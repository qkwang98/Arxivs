"""Bosonic-plethysm cluster seed and polyhedral model.

Public interface
----------------

    B, W, dt, H = bosonic_model(l, m)

``B`` is the extended exchange matrix, ``W`` is the variable-by-weight
matrix satisfying ``B @ W == 0``, ``dt`` is a certified reddening/DT
mutation sequence, and ``H`` cuts out the theta/g-vector cone in the
convention ``H @ g >= 0``.

Mutable variables come first in the rows of ``W`` and the columns of ``B``
and ``H``.  Python mutation indices are zero based.  See :func:`bosonic_model_data` for labels, symmetrizer, H-model
coordinates, face data, and independent certification metadata.

The H engine is exact.  It has a closed formula for every two-matrix model,
a built-in mutation computation for (l,m)=(3,4), and compact degree-zero
face reduction for odd matrix counts whenever the next even ambient model
is available.  Further optimized-seed words can be supplied through
``HOptions.optimizer_words``; every supplied word is checked to end in an optimized seed before use.
No unverified H matrix is returned.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from fractions import Fraction
from math import comb, gcd, lcm
import random
import time
import warnings
from typing import Dict, Iterable, List, Mapping, MutableMapping, Optional, Sequence, Tuple

import numpy as np

__version__ = "2.1.0"

__all__ = [
    "BosonicModelData",
    "DTSearchOptions",
    "HOptions",
    "HConstructionError",
    "ReddeningSearchError",
    "bosonic_model",
    "bosonic_model_data",
    "bosonic_seed",
    "verify_reddening",
]

Label = Tuple[object, ...]
Exponent = Tuple[int, ...]


class ReddeningSearchError(RuntimeError):
    """Raised when no certified reddening word is found in the search budget."""


class HConstructionError(RuntimeError):
    """Raised when the requested exact H construction is unavailable."""


@dataclass(frozen=True)
class DTSearchOptions:
    """Certified DT/reddening construction options.

    ``sequence`` may contain a previously known word.  It is checked against
    the principal matrix before being returned.  Python words are zero based
    unless ``sequence_one_based`` is true.
    """

    sequence: Optional[Sequence[int]] = None
    sequence_one_based: bool = False
    use_legacy_compiler: bool = True
    allow_reduction_search: bool = True
    seconds: float = 30.0
    beam_width: int = 128
    max_rounds: int = 200
    mutation_branch: int = 24
    deletion_branch: int = 12
    max_entry: int = 10**12
    seed: int = 0


@dataclass(frozen=True)
class HOptions:
    """Options for the exact cone computation.

    ``optimizer_words`` maps a frozen label such as ``"Delta[2]"`` or
    ``"z[4;1,2]"`` to a mutation word.  Words are zero based by default;
    set ``optimizer_words_one_based=True`` for MATLAB/paper-style words.

    Directly computed models retain the full Laurent-support inequality
    family.  For an odd matrix count, the successive-matrix face reduction
    removes only zero rows and exact duplicate restricted rows.
    """

    optimizer_words: Optional[Mapping[str, Sequence[int]]] = None
    optimizer_words_one_based: bool = False
    allow_certified_optimizer_search: bool = False
    optimizer_search_seconds: float = 30.0
    optimizer_search_restarts: int = 50
    optimizer_search_max_length: int = 120
    optimizer_search_seed: int = 0
    max_laurent_terms: int = 2_000_000
    use_face_ambient: bool = True
    ambient_l: Optional[int] = None
    ambient_m: Optional[int] = None


@dataclass(frozen=True)
class BosonicModelData:
    """Complete model output and certification metadata."""

    l: int
    m: int
    B: np.ndarray
    W: np.ndarray
    DT: Tuple[int, ...]
    H: np.ndarray
    mutable_labels: Tuple[str, ...]
    frozen_labels: Tuple[str, ...]
    all_labels: Tuple[str, ...]
    weight_column_labels: Tuple[str, ...]
    symmetrizer: np.ndarray
    relation_row_signs: np.ndarray
    dt_1based: Tuple[int, ...]
    dt_labels: Tuple[str, ...]
    dt_verified: bool
    dt_method: str
    H_coordinate_labels: Tuple[str, ...]
    H_weight_matrix: np.ndarray
    H_weight_column_labels: Tuple[str, ...]
    H_ambient_l: int
    H_ambient_m: int
    H_source_l: int
    H_source_m: int
    H_face_equations: np.ndarray
    H_face_labels: Tuple[str, ...]
    H_row_sources: Tuple[str, ...]
    H_verified: bool
    H_method: str
    cone_convention: str = "H @ g >= 0"
    compatibility_convention: str = "B @ W == 0"

    @property
    def weight_row_labels(self) -> Tuple[str, ...]:
        """Backward-compatible alias; these labels now index W columns."""
        return self.weight_column_labels

    @property
    def H_weight_row_labels(self) -> Tuple[str, ...]:
        """Backward-compatible alias; these labels index H_weight_matrix columns."""
        return self.H_weight_column_labels


# ---------------------------------------------------------------------------
# Labels, exchange matrix, and weights
# ---------------------------------------------------------------------------


def _require_parameters(l: int, m: int) -> Tuple[int, int]:
    if isinstance(l, bool) or not isinstance(l, (int, np.integer)) or int(l) < 2:
        raise ValueError("l must be an integer >= 2")
    if isinstance(m, bool) or not isinstance(m, (int, np.integer)) or int(m) < 2:
        raise ValueError("m must be an integer >= 2")
    return int(l), int(m)


def _canonical_z(l: int, n: int, i: int, j: int) -> Label:
    """Canonical representative of a chamber label in the seam quotient."""
    if n >= 4 and n % 2 == 0 and i == 0:
        return ("z", n - 1, i, j)
    if n >= 3 and n % 2 == 1 and i + j == l and j > 0:
        return ("z", n - 1, i, j)
    return ("z", n, i, j)


def _z_reference(l: int, n: int, i: int, j: int) -> Optional[Label]:
    if i == 0 and j == 0:
        return None
    if i == l and j == 0:
        return ("D", n)
    if n == 2 and i == 0 and j == l:
        return ("D", 1)
    if i < 0 or j < 0 or i + j < 1 or i + j > l or (i, j) in {(l, 0), (0, l)}:
        raise ValueError(f"invalid formal chamber label z[{n};{i},{j}]")
    return _canonical_z(l, n, i, j)


def _format_label(label: Label) -> str:
    if label[0] == "D":
        return f"Delta[{int(label[1])}]"
    return f"z[{int(label[1])};{int(label[2])},{int(label[3])}]"


def _mutable_labels(l: int, m: int) -> List[Label]:
    labels: List[Label] = []

    # Stage bases.
    for n in range(2, m + 1):
        for i in range(1, l):
            labels.append(_canonical_z(l, n, i, 0))

    # Second folded boundary of the first stage.
    for j in range(1, l):
        labels.append(_canonical_z(l, 2, 0, j))

    # Chamber interiors.
    for n in range(2, m + 1):
        for total in range(2, l):
            for i in range(1, total):
                labels.append(_canonical_z(l, n, i, total - i))

    # Even seams.
    for n in range(2, m):
        if n % 2 == 0:
            for i in range(1, l):
                labels.append(_canonical_z(l, n, i, l - i))

    # Odd seams.
    for n in range(3, m):
        if n % 2 == 1:
            for j in range(1, l):
                labels.append(_canonical_z(l, n, 0, j))

    expected = (m - 1) * (l - 1) * (l + 2) // 2
    if len(labels) != expected or len(set(labels)) != len(labels):
        raise RuntimeError("mutable-label enumeration failed")
    return labels


def _all_z_labels(l: int, m: int) -> set[Label]:
    labels: set[Label] = set()
    for n in range(2, m + 1):
        for total in range(1, l + 1):
            for i in range(total + 1):
                j = total - i
                if (i, j) in {(l, 0), (0, l)}:
                    continue
                labels.add(_canonical_z(l, n, i, j))
    return labels


def _frozen_labels(l: int, m: int, mutable: Sequence[Label]) -> List[Label]:
    frozen_z = _all_z_labels(l, m).difference(mutable)
    if m % 2:
        boundary = [_canonical_z(l, m, 0, j) for j in range(1, l)]
    else:
        boundary = [_canonical_z(l, m, i, l - i) for i in range(1, l)]
    if frozen_z != set(boundary):
        raise RuntimeError("frozen-label enumeration failed")
    return [("D", r) for r in range(1, m + 1)] + boundary


def _add_factor(monomial: MutableMapping[Label, int], label: Optional[Label], power: int = 1) -> None:
    if label is not None:
        monomial[label] = monomial.get(label, 0) + int(power)


def _raw_exchange_monomials(l: int, m: int, u: Label) -> Tuple[Dict[Label, int], Dict[Label, int]]:
    kind, n0, i0, j0 = u
    if kind != "z":
        raise ValueError("determinant vertices are frozen")
    n, i, j = int(n0), int(i0), int(j0)
    positive: Dict[Label, int] = {}
    negative: Dict[Label, int] = {}

    if j == 0:  # stage bases
        if i < l - 1:
            _add_factor(positive, _z_reference(l, n, i + 1, 0))
            _add_factor(positive, _z_reference(l, n, i - 1, 1), 2)
            _add_factor(negative, _z_reference(l, n, i - 1, 0))
            _add_factor(negative, _z_reference(l, n, i, 1), 2)
        elif n % 2 == 0:
            _add_factor(positive, ("D", n))
            _add_factor(positive, _z_reference(l, n, l - 2, 1), 2)
            _add_factor(negative, _z_reference(l, n, l - 2, 0))
            _add_factor(negative, _z_reference(l, n, l - 1, 1), 2)
        else:
            _add_factor(positive, _z_reference(l, n, l - 2, 1), 2)
            _add_factor(negative, ("D", n))
            _add_factor(negative, _z_reference(l, n, l - 2, 0))
            _add_factor(negative, _z_reference(l, n, l - 1, 1), 2)

    elif n == 2 and i == 0:  # first folded boundary
        _add_factor(positive, _z_reference(l, 2, 0, j - 1))
        _add_factor(positive, _z_reference(l, 2, 1, j), 2)
        _add_factor(negative, _z_reference(l, 2, 0, j + 1))
        _add_factor(negative, _z_reference(l, 2, 1, j - 1), 2)

    elif i > 0 and j > 0 and i + j < l:  # interiors
        _add_factor(positive, _z_reference(l, n, i, j - 1))
        _add_factor(positive, _z_reference(l, n, i + 1, j))
        _add_factor(positive, _z_reference(l, n, i - 1, j + 1))
        _add_factor(negative, _z_reference(l, n, i, j + 1))
        _add_factor(negative, _z_reference(l, n, i - 1, j))
        _add_factor(negative, _z_reference(l, n, i + 1, j - 1))

    elif n % 2 == 0 and n < m and i > 0 and j > 0 and i + j == l:  # even seams
        if i == l - 1 and j == 1:
            _add_factor(positive, ("D", n))
        _add_factor(positive, _z_reference(l, n, i - 1, j))
        _add_factor(positive, _z_reference(l, n + 1, i, j - 1))
        _add_factor(negative, _z_reference(l, n, i, j - 1))
        _add_factor(negative, _z_reference(l, n + 1, i - 1, j))

    elif n % 2 == 1 and n < m and i == 0 and 1 <= j <= l - 1:  # odd seams
        if j == l - 1:
            _add_factor(positive, ("D", n))
        _add_factor(positive, _z_reference(l, n, 1, j))
        _add_factor(positive, _z_reference(l, n + 1, 1, j - 1))
        _add_factor(negative, _z_reference(l, n, 1, j - 1))
        _add_factor(negative, _z_reference(l, n + 1, 1, j))
    else:
        raise RuntimeError(f"no exchange family contains {_format_label(u)}")

    return positive, negative


def _orient_exchange_rows(B_raw: np.ndarray, n_mutable: int) -> Tuple[np.ndarray, np.ndarray, np.ndarray]:
    A = B_raw[:, :n_mutable]
    row_signs = np.zeros(n_mutable, dtype=np.int64)
    for start in range(n_mutable):
        if row_signs[start]:
            continue
        row_signs[start] = 1
        stack = [start]
        while stack:
            i = stack.pop()
            for j in range(n_mutable):
                if i == j:
                    continue
                a, b = int(A[i, j]), int(A[j, i])
                if (a == 0) != (b == 0):
                    raise RuntimeError("nonreciprocal principal support")
                if a == 0:
                    continue
                proposed = (-1 if a * b > 0 else 1) * int(row_signs[i])
                if row_signs[j] == 0:
                    row_signs[j] = proposed
                    stack.append(j)
                elif row_signs[j] != proposed:
                    raise RuntimeError("inconsistent exchange-row orientations")

    B = B_raw * row_signs[:, None]

    d: List[Optional[Fraction]] = [None] * n_mutable
    for start in range(n_mutable):
        if d[start] is not None:
            continue
        d[start] = Fraction(1)
        stack = [start]
        while stack:
            i = stack.pop()
            for j in range(n_mutable):
                if B[i, j] == 0:
                    continue
                proposed = d[i] * Fraction(abs(int(B[i, j])), abs(int(B[j, i])))  # type: ignore[arg-type]
                if d[j] is None:
                    d[j] = proposed
                    stack.append(j)
                elif d[j] != proposed:
                    raise RuntimeError("inconsistent skew-symmetrizer ratios")

    common = 1
    for x in d:
        assert x is not None
        common = lcm(common, x.denominator)
    sym = [int(x * common) for x in d if x is not None]
    divisor = 0
    for x in sym:
        divisor = gcd(divisor, x)
    symmetrizer = np.asarray([x // divisor for x in sym], dtype=np.int64)
    skew = symmetrizer[:, None] * B[:, :n_mutable]
    if not np.array_equal(skew + skew.T, np.zeros_like(skew)):
        raise RuntimeError("principal matrix is not skew-symmetrizable")
    return B.astype(np.int64), row_signs, symmetrizer


def _omega(l: int, a: int) -> np.ndarray:
    result = np.zeros(l, dtype=np.int64)
    result[:a] = 1
    return result


def _weight_matrix(l: int, m: int, labels: Sequence[Label], order: str) -> Tuple[np.ndarray, Tuple[str, ...]]:
    """Initial weights with one row per seed variable.

    The paper order is ``epsilon[1],...,epsilon[l],delta[1],...,delta[m]``.
    The alternative order is retained for compatibility, but in either case
    the public convention is ``B @ W == 0``.
    """
    W0 = np.zeros((len(labels), l + m), dtype=np.int64)
    for r0, label in enumerate(labels):
        if label[0] == "D":
            r = int(label[1])
            W0[r0, :l] = 2
            W0[r0, l + r - 1] = l
            continue
        _, s0, i0, j0 = label
        stage, i, j = int(s0), int(i0), int(j0)
        q = (stage - 1) // 2 if j > 0 else 0
        W0[r0, :l] = _omega(l, i) + _omega(l, j) + _omega(l, i + j) + 2 * q
        if j == 0:
            W0[r0, l + stage - 1] += i
        else:
            for r in range(1, stage):
                W0[r0, l + r - 1] += j if r % 2 else l - j
            W0[r0, l + stage - 1] += i if stage % 2 == 0 else i + j

    epsilon_labels = [f"epsilon[{i}]" for i in range(1, l + 1)]
    delta_labels = [f"delta[{r}]" for r in range(1, m + 1)]
    if order == "epsilon-delta":
        return W0, tuple(epsilon_labels + delta_labels)
    if order == "delta-epsilon":
        return np.hstack([W0[:, l:], W0[:, :l]]), tuple(delta_labels + epsilon_labels)
    raise ValueError("weight_order must be 'delta-epsilon' or 'epsilon-delta'")


def _construct_matrices(l: int, m: int, weight_order: str) -> Tuple[np.ndarray, np.ndarray, List[Label], List[Label], np.ndarray, np.ndarray, Tuple[str, ...]]:
    mutable = _mutable_labels(l, m)
    frozen = _frozen_labels(l, m, mutable)
    labels = mutable + frozen
    index = {label: c for c, label in enumerate(labels)}
    B_raw = np.zeros((len(mutable), len(labels)), dtype=np.int64)
    for row, u in enumerate(mutable):
        positive, negative = _raw_exchange_monomials(l, m, u)
        for label, exponent in positive.items():
            B_raw[row, index[label]] += exponent
        for label, exponent in negative.items():
            B_raw[row, index[label]] -= exponent
    B, row_signs, symmetrizer = _orient_exchange_rows(B_raw, len(mutable))
    W, weight_labels = _weight_matrix(l, m, labels, weight_order)
    if np.any(B @ W):
        raise RuntimeError("weight-kernel check B @ W = 0 failed")
    expected_total = ((m - 1) * l * l + (m + 1) * l) // 2
    expected_mutable = (m - 1) * (l - 1) * (l + 2) // 2
    if B.shape != (expected_mutable, expected_total):
        raise RuntimeError("matrix-size check failed")
    return B, W, mutable, frozen, row_signs, symmetrizer, weight_labels


# ---------------------------------------------------------------------------
# Exact matrix mutation and reddening certification
# ---------------------------------------------------------------------------


def _mutate_matrix(M: np.ndarray, k: int) -> np.ndarray:
    """Exact Fomin--Zelevinsky mutation using Python integers."""
    if k < 0 or k >= M.shape[0] or k >= M.shape[1]:
        raise IndexError("mutation index out of range")
    A = np.asarray(M, dtype=object)
    column = A[:, k].copy()
    row = A[k, :].copy()
    result = A.copy()
    for i in range(A.shape[0]):
        if i == k:
            continue
        for j in range(A.shape[1]):
            if j == k:
                continue
            result[i, j] = A[i, j] + max(column[i], 0) * max(row[j], 0) - max(-column[i], 0) * max(-row[j], 0)
    result[k, :] = -A[k, :]
    result[:, k] = -A[:, k]
    return result


def verify_reddening(B_mutable: np.ndarray, sequence: Sequence[int]) -> bool:
    B_mutable = np.asarray(B_mutable)
    if B_mutable.ndim != 2 or B_mutable.shape[0] != B_mutable.shape[1]:
        raise ValueError("B_mutable must be square")
    n = B_mutable.shape[0]
    if any(isinstance(k, bool) or int(k) != k or not 0 <= int(k) < n for k in sequence):
        raise ValueError("invalid mutation index in sequence")
    framed = np.hstack([np.asarray(B_mutable, dtype=object), np.eye(n, dtype=object)])
    for k0 in sequence:
        framed = _mutate_matrix(framed, int(k0))
    C = framed[:, n:]
    return all(int(C[i, j]) <= 0 for i in range(n) for j in range(n))


def _exact_m2_reduction(l: int, principal: np.ndarray, mutable: Sequence[Label]) -> List[int]:
    """Construct the two-matrix reddening word from the triangular deletion."""
    A = np.asarray(principal, dtype=object).copy()
    active = list(range(len(mutable)))
    index = {label: i for i, label in enumerate(mutable)}
    history: List[Tuple[str, int, int]] = []

    def gid(i: int, j: int) -> int:
        return index[_canonical_z(l, 2, i, j)]

    def apply_word(word: Sequence[int]) -> None:
        nonlocal A
        for global_id in word:
            pos = active.index(global_id)
            A = _mutate_matrix(A, pos)
            history.append(("m", global_id, 0))

    def delete(global_id: int) -> None:
        nonlocal A
        pos = active.index(global_id)
        row = [int(A[pos, j]) for j in range(len(active)) if j != pos]
        if all(x >= 0 for x in row):
            sign = 1
        elif all(x <= 0 for x in row):
            sign = -1
        else:
            raise RuntimeError(f"prescribed m=2 deletion target {_format_label(mutable[global_id])} is not a source or sink")
        history.append(("d", global_id, sign))
        A = np.delete(np.delete(A, pos, axis=0), pos, axis=1)
        active.pop(pos)

    n = l - 1
    first: List[int] = []
    for q in range(n - 1, 0, -1):
        for u in range(q + 1):
            first.append(gid(1 + u, q - u))
    apply_word(first)
    delete(gid(1, 0))
    apply_word(list(reversed(first)))

    right = [gid(0, j) for j in range(n, 1, -1)]
    apply_word(right)
    delete(gid(0, 1))
    apply_word(list(reversed(right)))

    for k in range(2, n):
        prep: List[int] = []
        for q in range(n - k, 0, -1):
            for u in range(q + 1):
                prep.append(gid(k + u, q - u))
        apply_word(prep)
        delete(gid(k, 0))
        apply_word(list(reversed(prep)))

        for j in range(1, k + 1):
            target = gid(k - j, j)
            line = [gid(k - j, b) for b in range(j + n - k, j, -1)]
            apply_word(line)
            delete(target)
            apply_word(list(reversed(line)))

    # The remaining final layer is acyclic; delete available sources/sinks.
    while active:
        found = False
        for pos, global_id in enumerate(list(active)):
            row = [int(A[pos, j]) for j in range(len(active)) if j != pos]
            if all(x >= 0 for x in row) or all(x <= 0 for x in row):
                delete(global_id)
                found = True
                break
        if not found:
            raise RuntimeError("m=2 triangular reduction did not finish")

    sequence: List[int] = []
    for kind, vertex, sign in reversed(history):
        if kind == "m":
            sequence = [vertex] + sequence + [vertex]
        elif sign >= 0:
            sequence = [vertex] + sequence
        else:
            sequence = sequence + [vertex]
    if not verify_reddening(principal, sequence):
        raise RuntimeError("internal m=2 reddening certification failed")
    return sequence


_CERTIFIED_DT_CACHE_1BASED: Dict[Tuple[int, int], Tuple[int, ...]] = {
    (2, 3): (2, 4, 1, 4, 3, 4),
    (2, 4): (3, 6, 2, 6, 5, 1, 5, 4, 5, 6),
    (2, 5): (4, 2, 3, 7, 8, 6, 1, 5, 6, 2, 8, 3, 7, 5),
    (2, 6): (5, 4, 10, 8, 3, 1, 2, 6, 9, 8, 7, 6, 7, 1, 7, 2, 9, 2, 8, 9, 4, 10),
    (2, 7): (6, 10, 5, 1, 2, 3, 4, 7, 12, 10, 11, 2, 9, 8, 7, 8, 1, 8, 4, 12, 4, 11, 2, 11, 9, 3, 11, 10, 12),
    (3, 3): (4, 3, 4, 8, 4, 9, 7, 10, 2, 1, 9, 6, 8, 2, 7, 2, 8, 7, 6, 8, 10, 8, 6, 10, 9, 10, 8, 6, 8, 7, 2, 8, 5, 6, 9, 2, 10, 7, 9, 8, 4, 4),
    (3, 4): (5, 6, 5, 11, 5, 15, 10, 14, 3, 4, 3, 11, 10, 15, 3, 11, 15, 11, 14, 10, 11, 10, 13, 9, 12, 8, 13, 2, 1, 11, 8, 9, 11, 2, 11, 12, 13, 12, 2, 11, 12, 11, 2, 9, 11, 8, 9, 8, 11, 2, 13, 7, 8, 12, 9, 13, 11, 10, 11, 11, 15, 10, 11, 3, 3, 14, 10, 15, 11, 5, 5),
}


def _source_sink_positions(A: np.ndarray) -> List[Tuple[int, int]]:
    result: List[Tuple[int, int]] = []
    n = A.shape[0]
    for i in range(n):
        row = [int(A[i, j]) for j in range(n) if j != i]
        if all(x >= 0 for x in row):
            result.append((i, 1))
        elif all(x <= 0 for x in row):
            result.append((i, -1))
    return result


def _reconstruct_reduction_history(history: Sequence[Tuple[str, int, int]]) -> List[int]:
    sequence: List[int] = []
    for kind, vertex, sign in reversed(history):
        if kind == "m":
            sequence = [vertex] + sequence + [vertex]
        elif sign >= 0:
            sequence = [vertex] + sequence
        else:
            sequence = sequence + [vertex]
    return sequence


def _search_reddening_by_reduction(B0: np.ndarray, options: DTSearchOptions) -> List[int]:
    """Deterministic beam search for a source--sink reduction certificate."""
    n0 = B0.shape[0]
    start = (np.asarray(B0, dtype=object), tuple(range(n0)), tuple(), -1)
    states = [start]
    seen = {(tuple(range(n0)), tuple(int(x) for x in np.asarray(B0, dtype=object).flat))}
    deadline = time.monotonic() + max(0.1, float(options.seconds))
    rng = random.Random(options.seed)

    for _round in range(max(1, int(options.max_rounds))):
        if time.monotonic() >= deadline:
            break
        candidates = []
        for A, active, history, last_mut in states:
            if not active:
                seq = _reconstruct_reduction_history(history)
                if verify_reddening(B0, seq):
                    return seq
                continue

            ss = _source_sink_positions(A)
            if ss:
                # Branch over several deterministic deletion choices.
                choices = ss[: max(1, int(options.deletion_branch))]
                for pos, sign in choices:
                    gid = active[pos]
                    A2 = np.delete(np.delete(A, pos, axis=0), pos, axis=1)
                    active2 = active[:pos] + active[pos + 1 :]
                    hist2 = history + (("d", gid, sign),)
                    key = (active2, tuple(int(x) for x in A2.flat))
                    if key in seen:
                        continue
                    seen.add(key)
                    score = (len(active2), -len(_source_sink_positions(A2)), len(hist2), 0)
                    candidates.append((score, A2, active2, hist2, -1))
            else:
                local = []
                for pos, gid in enumerate(active):
                    if gid == last_mut:
                        continue
                    A2 = _mutate_matrix(A, pos)
                    max_abs = max((abs(int(x)) for x in A2.flat), default=0)
                    if max_abs > options.max_entry:
                        continue
                    active2 = active
                    hist2 = history + (("m", gid, 0),)
                    key = (active2, tuple(int(x) for x in A2.flat))
                    if key in seen:
                        continue
                    seen.add(key)
                    ss_count = len(_source_sink_positions(A2))
                    score = (len(active2), -ss_count, max_abs, len(hist2), gid)
                    local.append((score, A2, active2, hist2, gid))
                local.sort(key=lambda x: x[0])
                # Deterministic diversification among equal-quality moves.
                branch = local[: max(1, int(options.mutation_branch))]
                if len(local) > len(branch):
                    tail = local[len(branch) : min(len(local), 2 * len(branch))]
                    rng.shuffle(tail)
                    branch.extend(tail[: max(0, int(options.mutation_branch) // 4)])
                candidates.extend(branch)

        if not candidates:
            break
        candidates.sort(key=lambda x: x[0])
        states = [(A, active, hist, last) for _, A, active, hist, last in candidates[: max(1, int(options.beam_width))]]

    raise ReddeningSearchError(
        "no certified source--sink reduction was found; increase DTSearchOptions.seconds/beam_width"
    )


def _dt_sequence(l: int, m: int, B: np.ndarray, mutable: Sequence[Label], options: DTSearchOptions) -> Tuple[List[int], str]:
    principal = B[:, : len(mutable)]

    if options.sequence is not None:
        shift = 1 if options.sequence_one_based else 0
        sequence = [int(k) - shift for k in options.sequence]
        if not verify_reddening(principal, sequence):
            raise ReddeningSearchError("the user-supplied DT sequence failed certification")
        return sequence, "user-supplied certified DT word"

    if m == 2:
        return _exact_m2_reduction(l, principal, mutable), "exact triangular source--sink reduction"
    cached = _CERTIFIED_DT_CACHE_1BASED.get((l, m))
    if cached is not None:
        sequence = [x - 1 for x in cached]
        if not verify_reddening(principal, sequence):
            raise RuntimeError("built-in DT cache failed re-verification")
        return sequence, "built-in certified reduction word"

    # A drop-in upgrade may be placed next to the earlier bosonic_seed.py.
    # Reuse its all-parameter construction, but independently re-certify it.
    if options.use_legacy_compiler:
        try:
            import importlib
            legacy = importlib.import_module("bosonic_seed")
            if getattr(legacy, "__file__", None) != __file__:
                if hasattr(legacy, "bosonic_seed_data"):
                    old = legacy.bosonic_seed_data(l, m)
                    sequence = [int(k) for k in old.reddening_sequence]
                else:
                    old_B, _old_W, sequence = legacy.bosonic_seed(l, m)
                    sequence = [int(k) for k in sequence]
                    if np.asarray(old_B).shape != B.shape or not np.array_equal(np.asarray(old_B), B):
                        raise ReddeningSearchError("legacy B matrix does not match the current compiler")
                if verify_reddening(principal, sequence):
                    return sequence, "certified word supplied by the existing bosonic_seed package"
        except Exception:
            pass

    if not options.allow_reduction_search:
        raise ReddeningSearchError(
            f"no built-in DT word is stored for (l,m)=({l},{m}); "
            "supply DTSearchOptions.sequence or install the existing bosonic_seed compiler"
        )
    sequence = _search_reddening_by_reduction(principal, options)
    return sequence, "certified source--sink reduction search"


# ---------------------------------------------------------------------------
# H matrix: two-matrix closed formula and optimized-seed pullback
# ---------------------------------------------------------------------------


def _primitive_integral_row(values: Sequence[Fraction]) -> Tuple[int, ...]:
    denominator = 1
    for x in values:
        denominator = lcm(denominator, x.denominator)
    row = [int(x * denominator) for x in values]
    divisor = 0
    for x in row:
        divisor = gcd(divisor, abs(x))
    if divisor:
        row = [x // divisor for x in row]
    return tuple(row)


def _h_m2_full(l: int, labels: Sequence[Label]) -> Tuple[np.ndarray, Tuple[str, ...]]:
    """Full two-matrix inequality family, returned in ``H g >= 0`` convention."""
    index = {label: c for c, label in enumerate(labels)}
    rows: List[Tuple[int, ...]] = []
    sources: List[str] = []

    def unit(i: int, j: int) -> np.ndarray:
        label = _z_reference(l, 2, i, j)
        result = np.zeros(len(labels), dtype=np.int64)
        if label is not None:
            result[index[label]] = 1
        return result

    # Outer boundary path inequalities.
    for i in range(1, l):
        cumulative = np.zeros(len(labels), dtype=np.int64)
        frozen_label = _canonical_z(l, 2, i, l - i)
        for j in range(0, l + i):
            if 0 <= j < i:
                piece = unit(i - j, l - i)
            elif j == i:
                piece = 2 * unit(0, l - i)
            elif i < j < l:
                piece = unit(j - i, l - j)
            elif j == l:
                piece = 2 * unit(l - i, 0)
            else:
                piece = unit(l - i, j - l)
            cumulative = cumulative + piece
            rows.append(tuple(int(x) for x in cumulative))
            sources.append(_format_label(frozen_label))

    # Delta[2] diagonal path.  The final j=l term is zero; it is retained
    # deliberately in the full raw family.
    cumulative = np.zeros(len(labels), dtype=np.int64)
    for k in range(0, l + 1):
        cumulative = cumulative + unit(l - k, 0)
        rows.append(tuple(int(x) for x in cumulative))
        sources.append("Delta[2]")

    # Delta[1].
    rows.append(tuple(int(x) for x in unit(0, l)))
    sources.append("Delta[1]")
    return np.asarray(rows, dtype=np.int64), tuple(sources)


_H34_OPTIMIZER_WORDS_1BASED: Dict[str, Tuple[int, ...]] = {
    "Delta[1]": (12, 13, 15, 14, 10, 12, 9, 7, 8),
    "Delta[2]": (9, 12, 7, 4, 9, 15, 9, 11, 14, 4, 7, 12, 11, 15, 12, 7, 12, 13, 9, 10, 14, 1, 2),
    "Delta[3]": (14, 10, 15, 4, 3),
    "Delta[4]": (),
    "z[4;1,2]": (1, 4, 12, 1, 3, 12, 1, 6, 12, 3, 9, 6, 12, 7, 4, 1, 9, 7, 11, 13, 14, 10, 3, 5, 9, 11, 12, 14),
    "z[4;2,1]": (6, 15, 4, 10, 2, 8, 9, 12, 13, 11),
}


def _chiral_E(B: np.ndarray, symmetrizer: np.ndarray, n_mutable: int) -> np.ndarray:
    E = np.zeros((B.shape[1], n_mutable), dtype=object)
    E[:n_mutable, :] = -np.asarray(B[:, :n_mutable], dtype=object)
    E[n_mutable:, :] = (symmetrizer[:, None] * np.asarray(B[:, n_mutable:], dtype=object)).T
    return E


def _divide_by_one_plus_power(poly: Dict[Exponent, int], k: int, q: int, n_variables: int) -> Dict[Exponent, int]:
    if q == 0:
        return poly
    groups: Dict[Tuple[int, ...], Dict[int, int]] = {}
    for exponent, coefficient in poly.items():
        other = exponent[:k] + exponent[k + 1 :]
        bucket = groups.setdefault(other, {})
        bucket[exponent[k]] = bucket.get(exponent[k], 0) + coefficient

    output: Dict[Exponent, int] = {}
    for other, numerator in groups.items():
        low, high = min(numerator), max(numerator)
        quotient: Dict[int, int] = {}
        for degree in range(low, high + 1):
            value = numerator.get(degree, 0)
            for j in range(1, q + 1):
                value -= comb(q, j) * quotient.get(degree - j, 0)
            if value:
                quotient[degree] = value
        for degree in range(low, high + q + 1):
            reconstructed = sum(comb(q, j) * quotient.get(degree - j, 0) for j in range(q + 1))
            if reconstructed != numerator.get(degree, 0):
                raise HConstructionError("nonexact Laurent division during chiral pullback")
        for degree, coefficient in quotient.items():
            exponent = other[:k] + (degree,) + other[k:]
            output[exponent] = coefficient
    return output


def _pullback_boundary_monomial(
    B0: np.ndarray,
    symmetrizer: np.ndarray,
    word: Sequence[int],
    frozen_column: int,
    max_terms: int,
) -> Tuple[Dict[Exponent, int], np.ndarray]:
    n_mutable = B0.shape[0]
    n_variables = B0.shape[1]
    matrices = [np.asarray(B0, dtype=object).copy()]
    current = matrices[0]
    for k in word:
        current = _mutate_matrix(current, int(k))
        matrices.append(current)

    exponent = [0] * n_variables
    exponent[frozen_column] = 1
    polynomial: Dict[Exponent, int] = {tuple(exponent): 1}

    for t in range(len(word) - 1, -1, -1):
        k = int(word[t])
        B = matrices[t]
        column = _chiral_E(B, symmetrizer, n_mutable)[:, k]
        transformed = []
        common_denominator_power = 0
        for a, coefficient in polynomial.items():
            r = -sum(int(a[i]) * int(column[i]) for i in range(n_variables) if i != k)
            common_denominator_power = max(common_denominator_power, -r)
            b = list(a)
            b[k] = -a[k] + sum(int(a[i]) * max(int(column[i]), 0) for i in range(n_variables) if i != k)
            transformed.append((b, r, coefficient))

        numerator: Dict[Exponent, int] = {}
        for b, r, coefficient in transformed:
            power = r + common_denominator_power
            if power < 0:
                raise HConstructionError("internal Laurent denominator error")
            for j in range(power + 1):
                exponent2 = b.copy()
                exponent2[k] += j
                key = tuple(exponent2)
                numerator[key] = numerator.get(key, 0) + coefficient * comb(power, j)

        polynomial = _divide_by_one_plus_power(numerator, k, common_denominator_power, n_variables)
        if any(coefficient <= 0 for coefficient in polynomial.values()):
            raise HConstructionError("chiral pullback lost positivity")
        if len(polynomial) > max_terms:
            raise HConstructionError(
                f"boundary Laurent support exceeded max_laurent_terms={max_terms}"
            )
    return polynomial, matrices[-1]


def _optimizer_word_map(l: int, m: int, h_options: HOptions) -> Dict[str, Tuple[int, ...]]:
    result: Dict[str, Tuple[int, ...]] = {}
    if (l, m) == (3, 4):
        result.update({key: tuple(x - 1 for x in word) for key, word in _H34_OPTIMIZER_WORDS_1BASED.items()})
    if h_options.optimizer_words is not None:
        for key, word in h_options.optimizer_words.items():
            seq = tuple(int(x) - (1 if h_options.optimizer_words_one_based else 0) for x in word)
            result[str(key)] = seq
    return result


def _optimizer_energy(M: np.ndarray, frozen_column: int) -> Tuple[int, int, int, int, int]:
    c = [int(x) for x in M[:, frozen_column]]
    negatives = [i for i, x in enumerate(c) if x < 0]
    if not negatives:
        return (0, 0, 0, sum(abs(x) for x in c), max((abs(int(x)) for x in M.flat), default=0))
    best_post = None
    for k in negatives:
        M2 = _mutate_matrix(M, k)
        c2 = [int(x) for x in M2[:, frozen_column]]
        value = (sum(x < 0 for x in c2), sum(max(-x, 0) for x in c2))
        best_post = value if best_post is None or value < best_post else best_post
    assert best_post is not None
    return (
        len(negatives),
        sum(max(-x, 0) for x in c),
        100 * best_post[0] + best_post[1],
        sum(abs(x) for x in c),
        max((abs(int(x)) for x in M.flat), default=0),
    )


def _certified_optimizer_search(
    B0: np.ndarray,
    frozen_column: int,
    seconds: float,
    restarts: int,
    max_length: int,
    seed: int,
) -> Tuple[int, ...]:
    """A deterministic-seeded exact search; every returned word is certified."""
    n = B0.shape[0]
    rng = random.Random(seed)
    deadline = time.monotonic() + max(0.1, seconds)
    best_word: Optional[Tuple[int, ...]] = None
    best_energy = _optimizer_energy(B0, frozen_column)

    for restart in range(max(1, restarts)):
        if time.monotonic() >= deadline:
            break
        M = np.asarray(B0, dtype=object).copy()
        word: List[int] = []
        last = -1
        visited = {tuple(int(x) for x in M.flat)}
        temperature = 8.0
        for _ in range(max_length):
            energy = _optimizer_energy(M, frozen_column)
            if energy[0] == 0:
                column = [int(x) for x in M[:, frozen_column]]
                if all(x >= 0 for x in column):
                    return tuple(word)
            if energy < best_energy:
                best_energy = energy
                best_word = tuple(word)

            moves = []
            for k in range(n):
                if k == last:
                    continue
                M2 = _mutate_matrix(M, k)
                max_abs = max((abs(int(x)) for x in M2.flat), default=0)
                if max_abs > 10**12:
                    continue
                key = tuple(int(x) for x in M2.flat)
                if key in visited:
                    continue
                moves.append((_optimizer_energy(M2, frozen_column), k, M2, key))
            if not moves:
                break
            moves.sort(key=lambda item: (item[0], item[1]))
            top = moves[: min(12, len(moves))]
            if rng.random() < 0.8:
                base = top[0][0]
                # Rank-based deterministic-seeded diversification; avoids floating overflow.
                weights = [1.0 / (1.0 + rank / max(temperature, 0.2)) for rank in range(len(top))]
                chosen = rng.choices(top, weights=weights, k=1)[0]
            else:
                chosen = rng.choice(moves[: min(32, len(moves))])
            _, k, M, key = chosen
            word.append(k)
            last = k
            visited.add(key)
            temperature *= 0.97

    detail = f" best partial energy={best_energy}, length={0 if best_word is None else len(best_word)}"
    raise HConstructionError("no certified optimized seed was found in the H search budget;" + detail)


def _h_from_optimized_words(
    l: int,
    m: int,
    B: np.ndarray,
    mutable: Sequence[Label],
    frozen: Sequence[Label],
    symmetrizer: np.ndarray,
    h_options: HOptions,
) -> Tuple[np.ndarray, Tuple[str, ...], Dict[str, Tuple[int, ...]], str]:
    labels = list(mutable) + list(frozen)
    n_mutable = len(mutable)
    words = _optimizer_word_map(l, m, h_options)
    used_words: Dict[str, Tuple[int, ...]] = {}
    rows: List[Tuple[int, ...]] = []
    row_sources: List[str] = []

    for f_index, frozen_label in enumerate(frozen):
        name = _format_label(frozen_label)
        word = words.get(name)
        frozen_column = n_mutable + f_index
        if word is None and h_options.allow_certified_optimizer_search:
            word = _certified_optimizer_search(
                B,
                frozen_column,
                h_options.optimizer_search_seconds,
                h_options.optimizer_search_restarts,
                h_options.optimizer_search_max_length,
                h_options.optimizer_search_seed + f_index,
            )
        if word is None:
            raise HConstructionError(
                f"no optimizing word is available for {name} in (l,m)=({l},{m}); "
                "supply HOptions.optimizer_words or enable the certified optimizer search"
            )
        if any(k < 0 or k >= n_mutable for k in word):
            raise HConstructionError(f"optimizer word for {name} contains an invalid mutation index")

        polynomial, terminal = _pullback_boundary_monomial(
            B, symmetrizer, word, frozen_column, h_options.max_laurent_terms
        )
        terminal_column = [int(x) for x in terminal[:, frozen_column]]
        if any(x < 0 for x in terminal_column):
            raise HConstructionError(
                f"optimizer word for {name} did not end in a nonnegative frozen column"
            )
        used_words[name] = tuple(word)

        exponent_support = list(polynomial.keys())
        for exponent in exponent_support:
            linear_form = [
                Fraction(int(exponent[i]), int(symmetrizer[i])) if i < n_mutable else Fraction(int(exponent[i]), 1)
                for i in range(len(labels))
            ]
            paper_positive = _primitive_integral_row(linear_form)
            rows.append(tuple(paper_positive))  # convention H g >= 0
            row_sources.append(name)

    H = np.asarray(rows, dtype=np.int64)
    method = "optimized-seed chiral pullback; full positive Laurent supports"
    return H, tuple(row_sources), used_words, method


def _direct_h_for_seed(
    l: int,
    m: int,
    weight_order: str,
    h_options: HOptions,
) -> Tuple[np.ndarray, Tuple[str, ...], np.ndarray, Tuple[str, ...], Tuple[str, ...], str]:
    """Construct H in the native seed coordinates, or fail loudly."""
    B, W, mutable, frozen, _, sym, weight_labels = _construct_matrices(l, m, weight_order)
    labels = mutable + frozen
    label_text = tuple(_format_label(x) for x in labels)
    if m == 2:
        H, sources = _h_m2_full(l, labels)
        return H, label_text, W, weight_labels, sources, "closed two-matrix path formula"

    words = _optimizer_word_map(l, m, h_options)
    frozen_names = {_format_label(f) for f in frozen}
    if frozen_names.issubset(words) or h_options.allow_certified_optimizer_search:
        H, sources, _, method = _h_from_optimized_words(l, m, B, mutable, frozen, sym, h_options)
        return H, label_text, W, weight_labels, sources, method
    missing = sorted(frozen_names.difference(words))
    detail = missing[0] if missing else "an optimizer word"
    raise HConstructionError(
        f"no exact native H construction is available for (l,m)=({l},{m}); "
        f"missing {detail}. Supply HOptions.optimizer_words."
    )


def _compact_matrix_face(
    H: np.ndarray,
    coordinate_labels: Sequence[str],
    ambient_weight_matrix: np.ndarray,
    ambient_weight_labels: Sequence[str],
    row_sources: Sequence[str],
    l: int,
    m: int,
    ambient_m: int,
    weight_order: str,
) -> Tuple[np.ndarray, Tuple[str, ...], np.ndarray, Tuple[str, ...], Tuple[str, ...]]:
    """Restrict an ambient model to the degree-zero ``m``-matrix face.

    For fixed rank ``l``, the seed variables of ``Sigma_{l,m}`` are exactly
    the ambient seed variables of degree zero in
    ``delta[m+1],...,delta[ambient_m]``.  The face construction therefore
    identifies the smaller g-lattice with this coordinate sublattice.  The
    inherited inequalities are obtained by selecting those columns.  Zero
    rows and exact duplicate rows are removed; no further polyhedral
    redundancy test is performed.

    The degree-zero characterization is checked from the ambient weight
    matrix before any columns are discarded.
    """
    if ambient_m <= m:
        raise HConstructionError("matrix-face reduction requires ambient_m > m")

    _B, W_target, mutable_target, frozen_target, _signs, _sym, weight_labels_target = _construct_matrices(
        l, m, weight_order
    )
    target_labels = tuple(_format_label(x) for x in mutable_target + frozen_target)
    index = {label: c for c, label in enumerate(coordinate_labels)}
    missing = [label for label in target_labels if label not in index]
    if missing:
        raise HConstructionError(
            "matrix-face coordinate reduction failed; ambient model is missing "
            + missing[0]
        )

    discarded_weight_columns: List[int] = []
    for r in range(m + 1, ambient_m + 1):
        name = f"delta[{r}]"
        try:
            discarded_weight_columns.append(tuple(ambient_weight_labels).index(name))
        except ValueError as exc:
            raise HConstructionError(
                f"matrix-face coordinate reduction is missing ambient weight {name}"
            ) from exc
    ambient_weight_matrix = np.asarray(ambient_weight_matrix, dtype=np.int64)
    zero_degree_labels = {
        str(coordinate_labels[i])
        for i in range(len(coordinate_labels))
        if all(int(ambient_weight_matrix[i, c]) == 0 for c in discarded_weight_columns)
    }
    if zero_degree_labels != set(target_labels):
        extra = sorted(zero_degree_labels.difference(target_labels))
        absent = sorted(set(target_labels).difference(zero_degree_labels))
        detail = extra[0] if extra else absent[0]
        raise HConstructionError(
            "matrix-face coordinate reduction failed the zero-degree label check at "
            + detail
        )

    columns = [index[label] for label in target_labels]

    source_weight_index = {name: c for c, name in enumerate(ambient_weight_labels)}
    try:
        retained_weight_columns = [source_weight_index[name] for name in weight_labels_target]
    except KeyError as exc:
        raise HConstructionError(
            f"matrix-face reduction is missing retained weight {exc.args[0]}"
        ) from exc
    restricted_W = np.asarray(
        ambient_weight_matrix[np.ix_(columns, retained_weight_columns)], dtype=np.int64
    )
    if not np.array_equal(restricted_W, W_target):
        raise HConstructionError(
            "matrix-face reduction failed the exact restricted-weight check"
        )

    restricted = np.asarray(H[:, columns], dtype=np.int64)

    rows: List[Tuple[int, ...]] = []
    provenance: List[List[str]] = []
    seen: Dict[Tuple[int, ...], int] = {}
    for row, source in zip(restricted, row_sources):
        key = tuple(int(x) for x in row)
        if not any(key):
            continue
        position = seen.get(key)
        if position is None:
            seen[key] = len(rows)
            rows.append(key)
            provenance.append([str(source)])
        elif str(source) not in provenance[position]:
            provenance[position].append(str(source))

    H_reduced = (
        np.asarray(rows, dtype=np.int64)
        if rows
        else np.zeros((0, len(target_labels)), dtype=np.int64)
    )
    sources_reduced = tuple(" | ".join(items) for items in provenance)
    return H_reduced, target_labels, W_target, weight_labels_target, sources_reduced


def _h_direct_or_face(
    l: int,
    m: int,
    weight_order: str,
    h_options: HOptions,
) -> Tuple[
    np.ndarray,
    Tuple[str, ...],
    np.ndarray,
    Tuple[str, ...],
    int,
    int,
    int,
    int,
    np.ndarray,
    Tuple[str, ...],
    Tuple[str, ...],
    str,
]:
    """Return H and the exact coordinate system in which it acts.

    Native H is preferred for even matrix counts.  For odd ``m`` the model is
    obtained from an even ambient cone and the matrix-number face is reduced
    to the smaller coordinate system.  Any remaining rank face is kept
    explicit through paired equality rows.
    """
    # The paper derives odd matrix counts from the next even model.  Respect
    # that convention even if the caller happens to provide native odd-m
    # optimizer words.  Setting use_face_ambient=False remains an expert
    # escape hatch for a deliberately native construction.
    force_matrix_face = bool(m % 2 == 1 and h_options.use_face_ambient)

    native_failure: Optional[HConstructionError] = None
    if not force_matrix_face:
        try:
            H, labels, W, weight_labels, sources, method = _direct_h_for_seed(
                l, m, weight_order, h_options
            )
            return (
                H,
                labels,
                W,
                weight_labels,
                l,
                m,
                l,
                m,
                np.zeros((0, len(labels)), dtype=np.int64),
                tuple(),
                sources,
                method,
            )
        except HConstructionError as exc:
            native_failure = exc
            if not h_options.use_face_ambient:
                raise
    else:
        native_failure = HConstructionError(
            "odd matrix counts are constructed by the successive-matrix face reduction"
        )

    ambient_m = int(h_options.ambient_m) if h_options.ambient_m is not None else (m if m % 2 == 0 else m + 1)
    if ambient_m < m:
        raise HConstructionError("ambient_m must dominate the requested matrix count")
    if force_matrix_face and (ambient_m <= m or ambient_m % 2 != 0):
        raise HConstructionError(
            "an odd-m model requires a strictly larger even ambient_m for the face reduction"
        )

    if h_options.ambient_l is not None:
        ambient_l_candidates = [int(h_options.ambient_l)]
    else:
        # The successive-matrix face keeps the rank fixed.  Try that model
        # first; only then use the older odd-rank fallback when l is even.
        ambient_l_candidates = [l] + ([l + 1] if l % 2 == 0 else [])

    source_error: Optional[HConstructionError] = None
    source_data = None
    ambient_l = l
    for candidate_l in ambient_l_candidates:
        if candidate_l < l:
            raise HConstructionError("ambient_l must dominate the requested rank")
        if candidate_l == l and ambient_m == m:
            continue
        try:
            source_data = _direct_h_for_seed(candidate_l, ambient_m, weight_order, h_options)
            ambient_l = candidate_l
            break
        except HConstructionError as exc:
            source_error = exc

    if source_data is None:
        if source_error is not None:
            raise source_error
        assert native_failure is not None
        raise native_failure

    H0, labels0, W0, weight_labels0, sources0, method0 = source_data

    source_l, source_m = ambient_l, ambient_m
    coordinate_l, coordinate_m = ambient_l, ambient_m

    # For odd target m, absorb the degree-zero matrix face into the coordinate
    # system itself.  This is the requested H reduction: select the variables
    # of Sigma_{coordinate_l,m}, delete zero rows, and merge exact duplicates.
    if m % 2 == 1 and ambient_m > m:
        H0, labels0, W0, weight_labels0, sources0 = _compact_matrix_face(
            H0,
            labels0,
            W0,
            weight_labels0,
            sources0,
            ambient_l,
            m,
            ambient_m,
            weight_order,
        )
        coordinate_m = m
        method0 += (
            f"; compact degree-zero matrix-face reduction "
            f"({ambient_l},{ambient_m})->({ambient_l},{m})"
        )

    face_rows: List[np.ndarray] = []
    face_labels: List[str] = []
    for s in range(l + 1, coordinate_l + 1):
        name = f"epsilon[{s}]"
        c = weight_labels0.index(name)
        vector = W0[:, c].astype(np.int64)
        face_rows.extend([vector, -vector])
        face_labels.extend([f"{name}=0", f"{name}=0"])
    for r in range(m + 1, coordinate_m + 1):
        name = f"delta[{r}]"
        c = weight_labels0.index(name)
        vector = W0[:, c].astype(np.int64)
        face_rows.extend([vector, -vector])
        face_labels.extend([f"{name}=0", f"{name}=0"])
    face = np.asarray(face_rows, dtype=np.int64) if face_rows else np.zeros((0, len(labels0)), dtype=np.int64)
    H = np.vstack([H0, face])
    sources = tuple(sources0) + tuple(face_labels)
    method = method0
    if face_labels:
        method += f"; explicit zero-weight face in coordinates ({coordinate_l},{coordinate_m})"
    return (
        H,
        labels0,
        W0,
        weight_labels0,
        coordinate_l,
        coordinate_m,
        source_l,
        source_m,
        face,
        tuple(face_labels),
        sources,
        method,
    )


# ---------------------------------------------------------------------------
# Public API
# ---------------------------------------------------------------------------


def bosonic_model_data(
    l: int,
    m: int,
    *,
    weight_order: str = "epsilon-delta",
    dt_options: Optional[DTSearchOptions] = None,
    h_options: Optional[HOptions] = None,
) -> BosonicModelData:
    """Return the full Bosonic-plethysm seed and cone data.

    The direct seed matrices ``B`` and ``W`` always correspond to the input
    ``(l,m)``.  For odd ``m``, the degree-zero face of the next even model is
    reduced to the ``m``-matrix coordinate system.  Thus ``H`` has native
    columns whenever no rank enlargement is needed.  ``H_source_l`` and
    ``H_source_m`` record the direct model from which a reduction was made;
    a remaining rank face is recorded by ``H_face_equations``.  In every
    coordinate system, rows
    of the weight matrix and columns of ``H`` have the same variable order.
    """
    l, m = _require_parameters(l, m)
    dt_options = dt_options if dt_options is not None else DTSearchOptions()
    h_options = h_options if h_options is not None else HOptions()

    B, W, mutable, frozen, row_signs, symmetrizer, weight_labels = _construct_matrices(l, m, weight_order)
    dt, dt_method = _dt_sequence(l, m, B, mutable, dt_options)
    dt_verified = verify_reddening(B[:, : len(mutable)], dt)
    if not dt_verified:
        raise RuntimeError("internal DT certification failed")

    (
        H,
        H_labels,
        H_W,
        H_weight_labels,
        H_ambient_l,
        H_ambient_m,
        H_source_l,
        H_source_m,
        face_rows,
        face_labels,
        H_sources,
        H_method,
    ) = _h_direct_or_face(l, m, weight_order, h_options)
    if H.ndim != 2 or H.shape[1] != len(H_labels):
        raise RuntimeError("H dimension/label mismatch")
    if H_W.shape[0] != len(H_labels) or H_W.shape[1] != len(H_weight_labels):
        raise RuntimeError("H weight-matrix dimension/label mismatch")
    H_verified = bool(np.issubdtype(H.dtype, np.integer))

    mutable_text = tuple(_format_label(x) for x in mutable)
    frozen_text = tuple(_format_label(x) for x in frozen)
    return BosonicModelData(
        l=l,
        m=m,
        B=B,
        W=W,
        DT=tuple(int(k) for k in dt),
        H=H,
        mutable_labels=mutable_text,
        frozen_labels=frozen_text,
        all_labels=mutable_text + frozen_text,
        weight_column_labels=weight_labels,
        symmetrizer=symmetrizer,
        relation_row_signs=row_signs,
        dt_1based=tuple(int(k) + 1 for k in dt),
        dt_labels=tuple(mutable_text[int(k)] for k in dt),
        dt_verified=True,
        dt_method=dt_method,
        H_coordinate_labels=H_labels,
        H_weight_matrix=H_W,
        H_weight_column_labels=H_weight_labels,
        H_ambient_l=H_ambient_l,
        H_ambient_m=H_ambient_m,
        H_source_l=H_source_l,
        H_source_m=H_source_m,
        H_face_equations=face_rows,
        H_face_labels=face_labels,
        H_row_sources=H_sources,
        H_verified=H_verified,
        H_method=H_method,
    )


def bosonic_model(
    l: int,
    m: int,
    *,
    weight_order: str = "epsilon-delta",
    dt_options: Optional[DTSearchOptions] = None,
    h_options: Optional[HOptions] = None,
) -> Tuple[np.ndarray, np.ndarray, List[int], np.ndarray]:
    """Return ``(B, W, DT, H)``.

    Python DT indices are zero based.  The cone convention is ``H @ g >= 0``.
    Use :func:`bosonic_model_data` whenever H may be an ambient face model,
    or when labels and certification metadata are needed.
    """
    data = bosonic_model_data(
        l,
        m,
        weight_order=weight_order,
        dt_options=dt_options,
        h_options=h_options,
    )
    if (data.H_ambient_l, data.H_ambient_m) != (data.l, data.m):
        warnings.warn(
            "H still contains an explicit rank-face coordinate enlargement; "
            "call bosonic_model_data() and use H_coordinate_labels, "
            "H_weight_matrix, and H_face_equations",
            RuntimeWarning,
            stacklevel=2,
        )
    return data.B, data.W, list(data.DT), data.H


# Backward-compatible seed-only wrapper.
def bosonic_seed(
    l: int,
    m: int,
    *,
    weight_order: str = "epsilon-delta",
    dt_options: Optional[DTSearchOptions] = None,
) -> Tuple[np.ndarray, np.ndarray, List[int]]:
    """Return the legacy ``(B,W,DT)`` interface, without constructing H.

    Here ``W`` keeps the earlier weight-by-variable orientation, so the
    compatibility identity is ``B @ W.T == 0``.  The upgraded
    :func:`bosonic_model` interface instead returns variable-by-weight ``W``
    with the literal identity ``B @ W == 0``.
    """
    l, m = _require_parameters(l, m)
    options = dt_options if dt_options is not None else DTSearchOptions()
    B, W_new, mutable, _, _, _, _ = _construct_matrices(l, m, weight_order)
    dt, _ = _dt_sequence(l, m, B, mutable, options)
    return B, W_new.T.copy(), dt


if __name__ == "__main__":
    demo = bosonic_model_data(3, 4)
    print("B shape:", demo.B.shape)
    print("W shape:", demo.W.shape, "and B@W=0:", not np.any(demo.B @ demo.W))
    print("DT length:", len(demo.DT), "verified:", demo.dt_verified)
    print("H shape:", demo.H.shape, demo.cone_convention)
    print("H method:", demo.H_method)
