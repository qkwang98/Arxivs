#!/usr/bin/env python3
"""Finite transcription checks for Section 7; not a proof of its all-parameter theorem."""
from math import comb


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def length_d(word):
    """Count positive roots e_i-e_j, e_i+e_j sent to negative roots."""
    total = 0
    for i in range(len(word)):
        for j in range(i + 1, len(word)):
            for sign in (-1, 1):
                vector = {abs(word[i]): 1 if word[i] > 0 else -1,
                          abs(word[j]): sign * (1 if word[j] > 0 else -1)}
                total += vector[min(vector)] < 0
    return total


def choose(n, k):
    return comb(n, k) if n >= k >= 0 else 0


def main():
    representatives = 0
    for r in range(3, 13):
        for k in range(3, r + 1):
            n, p = r + 2, r - k + 2
            w = [p] + list(range(p + 2, r + 1)) + [-n, -(n - 1)]
            w += list(range(1, p)) + [p + 1]
            require(sorted(map(abs, w)) == list(range(1, n + 1)), "Not a signed permutation")
            require(sum(x < 0 for x in w) % 2 == 0, "Wrong signed parity")
            length = length_d(w)
            require(length == k * p, f"Length failure for {(r, k)}")
            descents = []
            for j in range(n):
                v = w.copy()
                if j < n - 1:
                    v[j], v[j + 1] = v[j + 1], v[j]
                else:
                    v[-2], v[-1] = -v[-1], -v[-2]
                if length_d(v) < length:
                    descents.append(j + 1)
            require(descents == [k], f"Descent failure for {(r, k)}")
            representatives += 1
    coefficients = 0
    for k in range(3, 13):
        for d in range(16):
            section_dimension = (d + 1) * (choose(d + 2 * k - 1, 2 * k - 1)
                                          - choose(d + 2 * k - 3, 2 * k - 1))
            numerator_dimension = (choose(d + 2 * k - 1, 2 * k - 1)
                                   + 2 * k * choose(d + 2 * k - 2, 2 * k - 1)
                                   + (2 * k - 3) * choose(d + 2 * k - 3, 2 * k - 1))
            require(section_dimension == numerator_dimension,
                    f"Hilbert coefficient failure for {(k, d)}")
            coefficients += 1
    print(f"PASS type D: {representatives} signed representatives and {coefficients} Hilbert coefficients.")
    print("The arbitrary-parameter identities are proved geometrically in Section 7.")


if __name__ == "__main__":
    main()
