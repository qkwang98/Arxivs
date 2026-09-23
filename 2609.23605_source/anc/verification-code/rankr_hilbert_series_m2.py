# Changelog (reverse chronological):
# 2026-08-06 - Claude: added proper_only filtering to
#   m2_rank1_hilbert_sequences/all_hilbert_series, per Jan's clarification
#   of what "filtering" meant. Jan's terms: a "proper" Hilbert function /
#   Hilbert function of a "non-trivial quotient" is one with f_1 == n (no
#   minimal generator of degree <= 1 in I) -- exactly the condition an
#   abstract simplicial complex on n vertices must satisfy (every singleton
#   {i} present), giving a genuine bijection to f-vectors of simplicial
#   complexes on n vertices, as opposed to the plain surjection onto all
#   achievable H_{E/I} (any I, including degree-<=1-generated ones). This
#   is exactly the "every generator survives, f_1(Delta_i)=n" restriction
#   already used in ../artefacts/right-angle-simplices-notes.md's rank-r
#   section (independently arrived at there for a different reason -- to
#   match \angle(a) excluding the origin vertex); see that file's new
#   "Definition (Jan, 2026-08-06)" for the full writeup. Extrapolates to
#   rank r as: every generator/summand's own ideal I_i must independently
#   be proper (H_{E/I_i}(1) = n for every i).
# 2026-08-06 - Claude: created, at Jan's request. Enumerates ALL Hilbert
#   sequences achievable by F/M, F = free E-module of rank r with generator
#   degrees d_1=0 <= d_2 <= ... <= d_r, M any graded submodule -- the exact
#   discrete set, not just the convex hull already computed in
#   rank2_hilbert_translation_check.sage/rankr_hilbert_translation_check.sage.
#   Calls Amata-Crupi's actual Macaulay2 package (ExteriorIdeals'
#   allHilbertSequences, for the rank-1 building block) rather than
#   reimplementing Kruskal-Katona locally, per Jan's explicit ask, then
#   combines r independently-chosen rank-1 sequences in Python via the
#   exact sumset identity proved this session (see
#   ../artefacts/right-angle-simplices-notes.md's "Rank-r Hilbert functions
#   of graded E-modules" section): H_{F/M}(j) = sum_i H_{E/I_i}(j-d_i).
#   Cross-verifies the combined list against ExteriorModules'
#   isHilbertSequence(hs,F) oracle. Along the way, found and worked around
#   two real Macaulay2-package bugs (both packages' isHilbertSequence fail
#   on a leading negative entry -- one wrongly returns true, the other
#   crashes) -- see ../LOGBOOK.md's 2026-08-06 20:43 entry and ../TODO.md.
#   Plain Python (subprocess + ast only, no Sage needed) so it runs under
#   `python3` or `sage -python` equally.

import ast
import subprocess
import tempfile
import os
from itertools import product


def _run_m2(script):
    with tempfile.NamedTemporaryFile(mode="w", suffix=".m2", delete=False) as f:
        f.write(script)
        path = f.name
    try:
        out = subprocess.run(["M2", "--script", path], capture_output=True, text=True, timeout=180)
    finally:
        os.unlink(path)
    if out.returncode != 0:
        raise RuntimeError(f"M2 failed:\n{out.stderr}")
    return out.stdout


def _parse_m2_list(text):
    # M2 prints lists as {1, 2, {3, 4}} (braces, not brackets) and booleans
    # lowercase (true/false, not Python's True/False).
    line = text.strip().splitlines()[-1]
    line = line.replace("{", "(").replace("}", ")")
    line = line.replace("true", "True").replace("false", "False")
    return ast.literal_eval(line)


def is_proper(seq, n):
    """
    Jan's definition (2026-08-06): a Hilbert sequence (1, f_1, ..., f_n) of
    E/I is "proper" (his other names: "Hilbert function of a non-trivial
    quotient") iff f_1 == n, i.e. I has no minimal generator of degree
    <= 1 -- equivalently, iff it is the f-vector of an actual simplicial
    complex on the FULL vertex set [n] (every singleton {i} present, as
    required by the definition of "simplicial complex on n vertices").
    Sequences with f_1 < n are still genuine Hilbert functions, just of
    "trivial" quotients in this sense (some vertex missing entirely).
    """
    return seq[1] == n


def m2_rank1_hilbert_sequences(n, proper_only=False):
    """
    All Hilbert sequences (1, f_1, ..., f_n) of E/I, I ranging over ALL
    graded ideals of E = wedge(V_n) -- via Amata-Crupi's own
    allHilbertSequences(E), ExteriorIdeals.m2. Includes the all-zero
    sequence (I = E) unless proper_only=True (see is_proper -- the
    all-zero sequence has f_1=0 != n, so it is never proper).

    Always filters out any sequence containing a negative entry -- not a
    "different convention", a real bug workaround: allHilbertSequences(E)
    is confirmed (n=2..5) to always emit exactly one bogus trailing entry
    (-1, 0, ..., 0), since isHilbertSequence(List,Ring) never checks for a
    negative leading entry. See ../LOGBOOK.md's 2026-08-06 20:43 entry.

    proper_only=True additionally keeps only the sequences with f_1 == n
    (Jan's "proper" Hilbert functions -- see is_proper) -- e.g. for n=3,
    this narrows allHilbertSequences' 11 raw entries down to the 5 that are
    actual f-vectors of simplicial complexes on all 3 vertices:
    {1,3,3,1}, {1,3,3,0}, {1,3,2,0}, {1,3,1,0}, {1,3,0,0}.
    """
    script = f'''
needsPackage "ExteriorIdeals"
E = QQ[x_1..x_{n}, SkewCommutative=>true]
print toString allHilbertSequences E
'''
    raw = [tuple(seq) for seq in _parse_m2_list(_run_m2(script))]
    dropped = [seq for seq in raw if any(v < 0 for v in seq)]
    if dropped:
        print(f"m2_rank1_hilbert_sequences({n}): dropped {len(dropped)} bogus negative-entry "
              f"sequence(s) from Macaulay2's own output (known bug): {dropped}")
    result = [seq for seq in raw if all(v >= 0 for v in seq)]
    if proper_only:
        result = [seq for seq in result if is_proper(seq, n)]
    return result


def combine_rank_r(rank1_sequences, degs):
    """
    All Hilbert sequences of F/M, F = direct sum of E-copies shifted by
    degs (degs[0] must be 0, WLOG), M = any monomial submodule -- i.e. the
    full sumset of len(degs) independently-shifted copies of
    rank1_sequences, per the exact identity H_{F/M}(j) = sum_i
    H_{E/I_i}(j - d_i). Returns a sorted list of distinct tuples, each of
    length n + max(degs) + 1 (degrees 0..N), including the all-zero vector.
    """
    assert degs[0] == 0, "degs[0] == 0 is this project's WLOG normalization"
    n = len(rank1_sequences[0]) - 1
    N = n + max(degs)
    results = set()
    for choice in product(rank1_sequences, repeat=len(degs)):
        h = [0] * (N + 1)
        for d, seq in zip(degs, choice):
            for k, val in enumerate(seq):
                h[d + k] += val
        results.add(tuple(h))
    return sorted(results)


def m2_verify_hilbert_sequences(n, degs, sequences):
    """
    Cross-checks each sequence against ExteriorModules' own
    isHilbertSequence(hs, F) oracle, F = E^(-degs) (M2's sign convention:
    a generator of degree d is E^{-d}). One M2 session for the whole batch.
    Sequences with a negative entry are skipped (never valid, and would
    crash isHilbertSequence(List,Module) rather than return false -- the
    second bug in ../LOGBOOK.md's 2026-08-06 20:43 entry).
    """
    safe = [s for s in sequences if all(v >= 0 for v in s)]
    if len(safe) != len(sequences):
        print(f"m2_verify_hilbert_sequences: skipping {len(sequences)-len(safe)} "
              f"negative-entry candidate(s) (would crash the M2 oracle, never valid anyway).")
    degs_m2 = ", ".join(str(-d) for d in degs)
    seqs_m2 = ", ".join("{" + ", ".join(map(str, hs)) + "}" for hs in safe)
    script = f'''
needsPackage "ExteriorModules"
E = QQ[x_1..x_{n}, SkewCommutative=>true]
F = E^{{{degs_m2}}}
seqs = {{{seqs_m2}}}
print toString apply(seqs, hs -> isHilbertSequence(hs, F))
'''
    verdicts = _parse_m2_list(_run_m2(script))
    return dict(zip(safe, verdicts))


def all_hilbert_series(n, degs, verify=True, proper_only=False):
    """
    Top-level procedure: input n, degs = (d_1=0, d_2, ..., d_r); output the
    exact list of all Hilbert sequences of F/M (F free E-module of rank
    r=len(degs) with those generator degrees, M any graded submodule),
    including the all-zero sequence (unless proper_only=True). Calls
    Macaulay2's ExteriorIdeals package for the rank-1 building block (per
    Jan's request, rather than a local Kruskal-Katona reimplementation),
    combines in Python via the proved exact sumset identity, and (if
    verify=True) cross-checks every resulting sequence against
    ExteriorModules' own isHilbertSequence(hs,F).

    proper_only=True extrapolates Jan's rank-1 "proper Hilbert function"
    definition (is_proper: f_1 == n) to rank r by requiring EVERY
    generator/summand's own ideal I_i to independently be proper -- i.e.
    only proper rank-1 sequences are used as building blocks for each of
    the r independently-chosen summands.
    """
    rank1 = m2_rank1_hilbert_sequences(n, proper_only=proper_only)
    combined = combine_rank_r(rank1, degs)
    if verify:
        verdicts = m2_verify_hilbert_sequences(n, degs, combined)
        bad = [hs for hs, ok in verdicts.items() if not ok]
        if bad:
            print(f"all_hilbert_series({n}, {degs}): {len(bad)} sequence(s) REJECTED by "
                  f"Macaulay2's own isHilbertSequence -- investigate: {bad}")
        else:
            print(f"all_hilbert_series({n}, {degs}): all {len(combined)} sequences confirmed "
                  f"by Macaulay2's isHilbertSequence(hs, F).")
    return combined


if __name__ == "__main__":
    for hs in all_hilbert_series(3, (0, 1)):
        print(hs)
