#!/usr/bin/env python3
"""Reconstruct all bounded integer inputs to the torsion-detection proof.

Python 3.10+; standard library only. No downloaded tables, floating-point
arithmetic, numerical rank decisions, or pre-existing certificate files are used.

Run from any directory:
    python /path/to/anc/verify_torsion_certificates.py

The default output directory is ``generated`` next to this script. Use
``--output-dir PATH`` to select another destination, or ``--verify-only`` to
perform the complete reconstruction without writing files. Any failed check
exits with a nonzero status, including when Python is run with ``-O``.

Convention: A[i][j] = <alpha_j, alpha_i^vee>, so the i-th simple reflection
acts by alpha_j -> alpha_j - A[i][j] alpha_i. Group matrices therefore act
on simple-root coordinate columns. All positions and indices in generated
JSON are one-based; group element IDs are internal and are not serialized.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from itertools import combinations
from math import gcd
from pathlib import Path
from time import perf_counter


class VerificationError(RuntimeError):
    """A required mathematical certificate check failed."""


def require(condition, message):
    if not condition:
        raise VerificationError(message)


CONFIGURATIONS = (
    {
        "type": "B3", "cartan": ((2, -1, 0), (-1, 2, -1), (0, -2, 2)),
        "order": 48, "max_length": 9,
        "all_gap_histogram": {1: 138, 2: 49, 3: 12},
        "tests": {3: {"cases": 12, "columns": {1: 9, 2: 2, 3: 1}, "gcds": {1: 12}}},
    },
    {
        "type": "C3", "cartan": ((2, -1, 0), (-1, 2, -2), (0, -1, 2)),
        "order": 48, "max_length": 9,
        "all_gap_histogram": {1: 138, 2: 49, 3: 12},
        "tests": {3: {"cases": 12, "columns": {1: 9, 2: 2, 3: 1}, "gcds": {1: 11, 2: 1}}},
    },
    {
        "type": "F4",
        "cartan": ((2, -1, 0, 0), (-1, 2, -1, 0), (0, -2, 2, -1), (0, 0, -1, 2)),
        "order": 1152, "max_length": 24,
        "all_gap_histogram": {1: 6168, 2: 3518, 3: 1676, 4: 567, 5: 210, 6: 101, 7: 24},
        "tests": {4: {"cases": 567, "columns": {1: 497, 2: 49, 3: 21}, "gcds": {1: 567}}},
    },
    {
        "type": "C2", "cartan": ((2, -2), (-1, 2)),
        "order": 8, "max_length": 4,
        "all_gap_histogram": {1: 12, 2: 3},
        "tests": {2: {"cases": 3, "columns": {1: 2, 2: 1}, "gcds": {1: 2, 2: 1}}},
    },
    {
        "type": "G2", "cartan": ((2, -1), (-3, 2)),
        "order": 12, "max_length": 6,
        "all_gap_histogram": {1: 20, 2: 7},
        "tests": {3: {"cases": 0, "columns": {}, "gcds": {}}},
    },
    {
        "type": "A3", "cartan": ((2, -1, 0), (-1, 2, -1), (0, -1, 2)),
        "order": 24, "max_length": 6,
        "all_gap_histogram": {1: 58, 2: 13, 3: 1},
        "tests": {
            2: {"cases": 13, "columns": {1: 13}, "gcds": {1: 13}},
            3: {"cases": 1, "columns": {1: 1}, "gcds": {1: 1}},
        },
    },
)


def multiply_matrices(a, b, rank):
    return tuple(
        sum(a[i * rank + k] * b[k * rank + j] for k in range(rank))
        for i in range(rank) for j in range(rank)
    )


def enumerate_group(config):
    """Breadth-first group closure; first-arrival words are shortest words."""
    cartan = config["cartan"]
    rank = len(cartan)
    identity = tuple(int(i == j) for i in range(rank) for j in range(rank))
    generators = []
    for i in range(rank):
        matrix = list(identity)
        for j in range(rank):
            matrix[i * rank + j] -= cartan[i][j]
        generators.append(tuple(matrix))
    matrices, words, lookup, edges = [identity], [()], {identity: 0}, []
    for matrix in matrices:
        word = words[lookup[matrix]]
        adjacent = []
        for i, generator in enumerate(generators):
            product = multiply_matrices(matrix, generator, rank)
            if product not in lookup:
                require(len(matrices) < config["order"], "Group exceeded the required order")
                lookup[product] = len(matrices)
                matrices.append(product)
                words.append(word + (i,))
            adjacent.append(lookup[product])
        edges.append(tuple(adjacent))
    require(len(matrices) == config["order"], "Wrong complete group order")
    require(max(map(len, words)) == config["max_length"], "Wrong maximum reduced length")
    for element, adjacent in enumerate(edges):
        for i, other in enumerate(adjacent):
            require(edges[other][i] == element, "A generator failed to be an involution")
            require(abs(len(words[element]) - len(words[other])) == 1,
                    "Simple-reflection length difference is not one")
    return {"rank": rank, "matrices": matrices, "words": words,
            "edges": edges, "lengths": list(map(len, words))}


def deletion_centres(group):
    """All (w, Dem(Q_w with j deleted)), including the gap-one cases."""
    centres = {}
    histogram = Counter()
    for w, word in enumerate(group["words"]):
        for omit in range(len(word)):
            current = 0
            for position, letter in enumerate(word):
                if position == omit:
                    continue
                following = group["edges"][current][letter]
                if group["lengths"][following] > group["lengths"][current]:
                    current = following
            centres.setdefault((w, current), []).append(omit)
    for w, u in centres:
        histogram[group["lengths"][w] - group["lengths"][u]] += 1
    return centres, histogram


def mask_data(group, word, omitted, columns):
    """Ordinary endpoint and literal boundary characters, without normalization."""
    omitted = set(omitted)
    rank, current = group["rank"], 0
    column_lookup = {position: index for index, position in enumerate(columns)}
    characters = [(0,) * rank for _ in columns]
    for position, letter in enumerate(word):
        if position in omitted:
            if position in column_lookup:
                matrix = group["matrices"][current]
                characters[column_lookup[position]] = tuple(
                    -matrix[a * rank + letter] for a in range(rank)
                )
        else:
            current = group["edges"][current][letter]
    return current, characters


def determinant(matrix):
    size = len(matrix)
    require(all(len(row) == size for row in matrix), "A minor is not square")
    if not size:
        return 1
    if size == 1:
        return matrix[0][0]
    if size == 2:
        return matrix[0][0] * matrix[1][1] - matrix[0][1] * matrix[1][0]
    return sum(
        (-1) ** j * matrix[0][j]
        * determinant([row[:j] + row[j + 1:] for row in matrix[1:]])
        for j in range(size)
    )


def extended_gcd(a, b):
    """Return nonnegative gcd g and integers x,y satisfying xa+yb=g."""
    old_r, r, old_s, s, old_t, t = a, b, 1, 0, 0, 1
    while r:
        quotient = old_r // r
        old_r, r = r, old_r - quotient * r
        old_s, s = s, old_s - quotient * s
        old_t, t = t, old_t - quotient * t
    if old_r < 0:
        old_r, old_s, old_t = -old_r, -old_s, -old_t
    require(old_s * a + old_t * b == old_r, "Extended Euclidean identity failed")
    return old_r, old_s, old_t


def minor_certificate(rows, column_count):
    """Full-column minors whose integral combination is the maximal-minor gcd.

    Once the gcd is one, remaining minors cannot change it. For a nonprimitive
    case, every full-column minor is examined. No smaller-column minor is used.
    """
    running_gcd, selected = 0, []
    for indices in combinations(range(len(rows)), column_count):
        value = determinant([list(rows[i]) for i in indices])
        next_gcd = gcd(running_gcd, abs(value))
        if next_gcd != running_gcd:
            check, left, right = extended_gcd(running_gcd, value)
            require(check == next_gcd, "Gcd mismatch")
            for minor in selected:
                minor["bezout_coefficient"] *= left
            selected.append({"row_indices": [i + 1 for i in indices],
                             "determinant": value, "bezout_coefficient": right})
            running_gcd = next_gcd
        if running_gcd == 1:
            break
    require(running_gcd > 0, "Raw matrix did not have full column rank")
    require(sum(m["bezout_coefficient"] * m["determinant"] for m in selected)
            == running_gcd, "Full-column minor Bezout identity failed")
    return running_gcd, selected


def reconstruct_gap(group, all_centres, gap):
    by_word = {}
    for (w, u), columns in all_centres.items():
        if group["lengths"][w] - group["lengths"][u] == gap:
            by_word.setdefault(w, {})[u] = columns
    records = []
    for w, centres in by_word.items():
        word = group["words"][w]
        all_columns = sorted({j for cols in centres.values() for j in cols})
        column_lookup = {j: k for k, j in enumerate(all_columns)}
        endpoint_masks = {u: [] for u in centres}
        # Every selected expression for u has length >= ell(u), and its length
        # has the parity of ell(u). The full reduced word has endpoint w, not u.
        for omission_count in range(gap % 2, gap + 1, 2):
            if omission_count == 0:
                continue
            for omitted in combinations(range(len(word)), omission_count):
                endpoint, characters = mask_data(group, word, omitted, all_columns)
                if endpoint in centres:
                    endpoint_masks[endpoint].append((omitted, characters))
        for u, columns in centres.items():
            masks = endpoint_masks[u]
            require(bool(masks), "Exact centre had no endpoint mask")
            reference_omitted, reference_characters = masks[0]
            positions = [column_lookup[j] for j in columns]
            rows, row_witnesses, seen = [], [], set()
            for omitted, characters in masks[1:]:
                for coordinate in range(group["rank"]):
                    row = tuple(characters[k][coordinate] - reference_characters[k][coordinate]
                                for k in positions)
                    # Removing duplicate or zero rows preserves the integral
                    # row lattice; no division or rational operation is used.
                    if any(row) and row not in seen:
                        seen.add(row)
                        rows.append(row)
                        row_witnesses.append({"omitted_positions": [j + 1 for j in omitted],
                                              "root_coordinate": coordinate + 1})
            lattice_gcd, minors = minor_certificate(rows, len(columns))
            record = {
                "word_w": [i + 1 for i in word],
                "word_u": [i + 1 for i in group["words"][u]],
                "dimension": gap,
                "exact_columns": [j + 1 for j in columns],
                "endpoint_mask_count": len(masks),
                "reference_omitted_positions": [j + 1 for j in reference_omitted],
                "raw_rows": [list(row) for row in rows],
                "row_witnesses": row_witnesses,
                "maximal_minor_gcd": lattice_gcd,
                "bezout_minors": minors,
            }
            verify_record(group, all_centres, w, u, record)
            records.append(record)
    require(len(records) == len({(w, u) for w, u in all_centres
                                 if group["lengths"][w] - group["lengths"][u] == gap}),
            "Certificate coverage omitted an exact-centre pair")
    return records


def verify_record(group, all_centres, w, u, record):
    """Check every stored witness against the independently generated objects."""
    word = tuple(i - 1 for i in record["word_w"])
    require(word == group["words"][w], "Wrong top word")
    require(tuple(i - 1 for i in record["word_u"]) == group["words"][u], "Wrong lower word")
    columns = [j - 1 for j in record["exact_columns"]]
    require(columns == all_centres[(w, u)], "Not the complete exact-column set")
    require(record["dimension"] == len(word) - len(group["words"][u]), "Wrong dimension")
    reference_omitted = [j - 1 for j in record["reference_omitted_positions"]]
    require(len(set(reference_omitted)) == len(reference_omitted)
            and all(0 <= j < len(word) for j in reference_omitted), "Illegal reference mask")
    endpoint, reference_characters = mask_data(group, word, reference_omitted, columns)
    require(endpoint == u, "Reference mask endpoint is wrong")
    rows = record["raw_rows"]
    require(len(rows) == len(record["row_witnesses"]), "Missing row witnesses")
    for row, witness in zip(rows, record["row_witnesses"]):
        omitted = [j - 1 for j in witness["omitted_positions"]]
        coordinate = witness["root_coordinate"] - 1
        require(0 <= coordinate < group["rank"], "Invalid root coordinate")
        require(len(set(omitted)) == len(omitted) and all(0 <= j < len(word) for j in omitted),
                "Illegal witness mask")
        endpoint, characters = mask_data(group, word, omitted, columns)
        require(endpoint == u, "Witness mask endpoint is wrong")
        reconstructed = [a[coordinate] - b[coordinate]
                         for a, b in zip(characters, reference_characters)]
        require(row == reconstructed, "Row is not its literal character difference")
        require(len(row) == len(columns), "Row does not use every column")
    identity = 0
    for minor in record["bezout_minors"]:
        indices = [i - 1 for i in minor["row_indices"]]
        require(len(indices) == len(columns) and len(set(indices)) == len(indices),
                "Minor does not use distinct rows and all columns")
        require(all(0 <= i < len(rows) for i in indices), "Minor row index out of range")
        value = determinant([rows[i] for i in indices])
        require(value == minor["determinant"], "Stored determinant is wrong")
        identity += minor["bezout_coefficient"] * value
    require(identity == record["maximal_minor_gcd"], "Stored Bezout identity failed")


def reconstruct_type(config):
    group = enumerate_group(config)
    centres, all_gaps = deletion_centres(group)
    require(dict(all_gaps) == config["all_gap_histogram"], "Wrong complete centre-gap histogram")
    output = {
        "schema_version": 1,
        "type": config["type"],
        "cartan_matrix": config["cartan"],
        "group_order": len(group["words"]),
        "maximum_length": max(group["lengths"]),
        "all_exact_centre_count": len(centres),
        "all_exact_centre_gap_histogram": dict(sorted(all_gaps.items())),
        "tests": [],
    }
    for gap, expected in config["tests"].items():
        records = reconstruct_gap(group, centres, gap)
        columns = Counter(len(record["exact_columns"]) for record in records)
        gcds = Counter(record["maximal_minor_gcd"] for record in records)
        require(len(records) == expected["cases"], "Wrong bounded-case count")
        require(dict(columns) == expected["columns"], "Wrong exact-column histogram")
        require(dict(gcds) == expected["gcds"], "Wrong integral-lattice gcd histogram")
        if config["type"] == "C3":
            exceptional = [r for r in records if r["maximal_minor_gcd"] != 1]
            require(len(exceptional) == 1 and exceptional[0]["word_w"] == [1, 2, 1, 3, 2, 1]
                    and exceptional[0]["word_u"] == [1, 2, 1], "Unexpected C3 exceptional pair")
        if config["type"] == "C2":
            exceptional = [r for r in records if r["maximal_minor_gcd"] != 1]
            require(len(exceptional) == 1 and exceptional[0]["word_w"] == [1, 2, 1]
                    and exceptional[0]["word_u"] == [1], "Unexpected C2 exceptional pair")
        summary = {
            "dimension": gap,
            "case_count": len(records),
            "column_histogram": dict(sorted(columns.items())),
            "maximal_minor_gcd_histogram": dict(sorted(gcds.items())),
            "stored_unique_nonzero_row_count": sum(len(r["raw_rows"]) for r in records),
            "stored_bezout_minor_count": sum(len(r["bezout_minors"]) for r in records),
        }
        output["tests"].append({"summary": summary, "records": records})
        print(f"PASS {config['type']} gap {gap}: {len(records)} pairs; "
              f"columns {dict(sorted(columns.items()))}; gcds {dict(sorted(gcds.items()))}")
    return output


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path,
                        default=Path(__file__).resolve().parent / "generated")
    parser.add_argument("--verify-only", action="store_true", help="Do not create or overwrite files")
    parser.add_argument("--check-stored", action="store_true",
                        help="Also require the supplied JSON files to match the reconstruction")
    args = parser.parse_args(argv)
    started = perf_counter()
    results = [reconstruct_type(config) for config in CONFIGURATIONS]
    summary = [{k: result[k] for k in ("type", "group_order", "maximum_length",
                                     "all_exact_centre_count", "all_exact_centre_gap_histogram")}
               | {"tests": [test["summary"] for test in result["tests"]]} for result in results]
    if args.check_stored:
        expected_files = [(f"{result['type']}_certificate.json", result) for result in results]
        expected_files.append(("summary.json", summary))
        for filename, expected in expected_files:
            path = args.output_dir / filename
            require(path.is_file(), f"Missing supplied certificate: {path}")
            try:
                stored = json.loads(path.read_text(encoding="utf-8"))
            except (OSError, ValueError) as exc:
                raise VerificationError(f"Cannot read supplied certificate {path}: {exc}") from exc
            normalized = json.loads(json.dumps(expected))
            require(stored == normalized, f"Supplied certificate differs from reconstruction: {path}")
        print(f"PASS stored certificates: {len(expected_files)} JSON files match the full reconstruction.")
    if not args.verify_only:
        args.output_dir.mkdir(parents=True, exist_ok=True)
        for result in results:
            destination = args.output_dir / f"{result['type']}_certificate.json"
            destination.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
        (args.output_dir / "summary.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")
        print(f"Certificate files written to {args.output_dir.resolve()}")
    print(f"ALL CHECKS PASSED ({perf_counter() - started:.3f} seconds).")
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except VerificationError as exc:
        print(f"VERIFICATION FAILED: {exc}", file=sys.stderr)
        sys.exit(1)
