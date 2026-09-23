# 2026-08-02 — Snellman-Moreno-Socías Conjecture 6.2, n=7 d=3: verification + binomial-basis rewrite

Code: `../code/snellman-morenosocias_n7d3_verify.m2` (Macaulay2),
`../code/snellman-morenosocias_binomial.py`. Cheap to recompute (seconds) — brief result log, not
a data archive. Full narrative/derivation, including the notational-bug finding: `../LOGBOOK/`.

## Conjectured value (Conjecture 6.2, read as giving q_{n,3}(t), the quotient's series)

n=7, d=3 (n=4·1+3 case): q_{7,3}(t) = 1 + 7t + 21t² + 34t³ + 28t⁴ (zero above degree 4).

## Macaulay2 check

Exterior algebra on 7 skew-commuting generators, char 31991 (matching the paper's own choice),
quotient by a random cubic, `hilbertFunction` degree by degree, 5 independent random seeds:

```
seed 1: {1, 7, 21, 34, 28, 0, 0, 0}  match: true
seed 2: {1, 7, 21, 34, 28, 0, 0, 0}  match: true
seed 3: {1, 7, 21, 34, 28, 0, 0, 0}  match: true
seed 4: {1, 7, 21, 34, 28, 0, 0, 0}  match: true
seed 5: {1, 7, 21, 34, 28, 0, 0, 0}  match: true
```

**PASS**, exact match every time — Conjecture 6.2 holds for this case (n=7,d=3), even though the
general Snellman–Moreno-Socías conjecture is known to be disproved (Lundqvist & Nicklasson 2018).

## Base-binomial (binomial-basis) coordinates

Using a = kozlov_vector(7) = (7,21,35,35,21,7,1) and (q_1,...,q_7) = (7,21,34,28,0,0,0):

```
y = (0, 1/35, 6/35, 4/5, 0, 0, 0)
sum(y) = 1 = q_1/a_1  ✓ (consistency check)
```

## Bottom line

Conjecture 6.2 confirmed computationally for n=7,d=3 — but only once read as giving q_{n,3}(t)
(the quotient's series), not p_{n,3}(t) (the ideal's, its literal label in the paper). See
`exterior-convex/LOGBOOK/` for why this is a genuine bug in the paper, not the harmless "Hilbert series of I"
convention.
