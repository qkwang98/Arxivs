"""Exact independent checks of the fixed-arity simplex constants.

The ordered-gap substitution on the ordered simplex gives the positive
complete homogeneous polynomial h_(i-1)(1,1/2,...,1/r).  Compare it with
the alternating inclusion-exclusion expression used in the paper.
These finite identities are consistency checks, not a proof of asymptotics.
"""
from fractions import Fraction
from math import comb, factorial
from pathlib import Path
import json


def positive_sum(r, k):
    values = [Fraction(1)] + [Fraction(0)] * k
    for j in range(1, r + 1):
        for degree in range(1, k + 1):
            values[degree] += values[degree - 1] / j
    return values[k]


rows = []
for r in range(2, 9):
    for i in range(1, 9):
        k = i - 1
        positive = positive_sum(r, k)
        alternating = sum((Fraction((-1)**(j+1)*comb(r, j), j**k)
                           for j in range(1, r+1)), Fraction(0))
        assert positive == alternating and positive > 0
        relation = positive / (factorial(r) * factorial(r+i-1))
        variable = Fraction(1, factorial(r-1)*factorial(i-1)*(r+i-1))
        if r == 2:
            assert relation == (1-Fraction(1, 2**i))/factorial(i+1)
            assert variable == Fraction(i, factorial(i+1))
        if i == 1:
            assert relation == Fraction(1, factorial(r)**2)
        rows.append({"arity": r, "homological_degree": i,
                     "relation_constant": str(relation),
                     "variable_constant": str(variable)})

result = {"status": "PASS", "exact_constant_pairs": len(rows),
          "method": "Two exact rational formulas; no floating point",
          "constants": rows,
          "scope": "Consistency checks; the asymptotic argument is in the paper"}
Path(__file__).with_suffix(".json").write_text(json.dumps(result, indent=2)+"\n",
                                             encoding="utf-8")
print("PASS: 56 exact fixed-arity/fixed-degree constants")
