COMPUTATIONAL SUPPLEMENT
Additive Relations and Betti Growth in Goldbach Rings
Michael Nelson
9 November 2026

RUNNING THE SIX PYTHON CHECKS

  python verify.py

Invoke this from the supplement directory or use the full path to verify.py.
Python 3.10 or later and its standard library suffice. Do not use -O or -OO:
assertions are part of the checks, and the runner rejects optimized execution.
No external data, network access, Sage, SymPy, or Singular is needed for these
six checks. The prime-pair check uses an exhaustive sieve through 20,000,000.

MANIFEST.json records SHA256 hashes of all immutable sources, input data,
the expected prime-pair summary, this README, and the runner. The runner
checks the hashes before and after execution. It does not modify these
inputs. All generated logs and reports are placed under reports/, which is
excluded from the manifest. Unchanged copies of the five original Python
checkers run under reports/replay/ because two write relative to their own
source path. An overall successful run exits with code 0 and prints
OVERALL PASS. reports/verification.json records the outcome of every check.

The five earlier Python checkers, their illustrated-strand input, and the
three Singular scripts are byte-for-byte copies from the joint supplement
of the combined manuscript and its two companion papers. This focused
package does not require that larger supplement or the topological paper.
The new prime-pair checker reproduces the finite arithmetic depth check.

CHECKS AND MATHEMATICAL SCOPE

1. computations/linear-constants-check.py
   Checks 56 arity/homological-degree pairs using exact rational arithmetic.
   Compares inclusion-exclusion constants with the positive ordered-gap
   expression and checks the binary simplifications and i=1 case.
   This is a finite consistency check, not a proof of the asymptotic theorem.

2. computations/illustrated-strands-check.py
   Input: illustrated-strands-data.json.
   Reconstructs the displayed polynomial boundaries; checks weights,
   minimality, consecutive products zero, and exactness by integral unit
   pivots. Checks all 12 nonempty cubic strands through weight 31, and the
   illustrated strands (18,2), (42,2), (23,3), (31,3), and (34,4).
   Verifies the five oriented faces of the square-pyramid three-cell.
   These are strand-local checks, not a global cellular resolution claim.

3. computations/koszul33-check.py
   Reconstructs the eleven product-star edges and four face cycles in
   bidegree (33,3), checks the coefficient/exterior-index swaps, and uses
   a determinant of absolute value one to verify the integral basis.

4. computations/goldbach-cutoff132-single-colon.py
   Reconstructs binary-move components through prime 131. For
   f=x127^6-x107*x131^5, the endpoints of x3*f lie in distinct components
   of sizes 211 and 322. Verifies a path with multiplier x3^2 and a path
   with one x3 after adjoining 137. The filename uses the older cutoff
   label 132; in the paper's inclusive convention the first support
   containing 131 is A_131. The support and calculation are identical.

5. computations/dual-koszul-cocycles-check.py
   Reconstructs the quadratic and cubic binary-move components at every
   odd-prime prefix from last prime 11 through last prime 101. Checks all
   2299 cubic identities over these 22 supports, the signed differential,
   and an integral coefficient detector taking the cocycle to 1 and every
   incoming column to 0. Also verifies the separate cutoff-8 example.
   With A_m={odd primes <=m}, the 22 supports cover 11<=m<=102.
   Historical output labels use last-prime+1; this does not change support.
   These finite checks do not prove the infinite dual-cocycle conjecture.

6. computations/prime-pair-depth-check.py
   Input: prime-pair-depth-expected.json (never overwritten).
   Independently constructs an Eratosthenes sieve and, for each odd prime p,
   scans primes q>=5 in increasing order to find r=p+3-q prime, with q<=r.
   Repeated summands are allowed. Verifies q,r<=p-2, so the pair lies in
   the same prime prefix. Trial division independently crosschecks the
   sieve through 10,000. At the default bound it compares the entire
   deterministic summary with the recorded expected JSON.

   Expected bound: 20,000,000 inclusive.
   Odd primes tested: 1,270,606; largest prime: 19,999,999.
   The only exceptions are 3 and 5, so all 1,270,604 primes p>=7 pass.
   The largest least first summand is 691, first attained at
   (p,q,r)=(7,499,939,691,7,499,251).
   SHA256 of the ordered little-endian uint32 witness triples:
   9dcd43df6307b892e7b87c69bba0f7a38b75e99eac440d8c0946a23c19398e10

   Standalone commands:
     python computations/prime-pair-depth-check.py
     python computations/prime-pair-depth-check.py --limit 100000 --output reports/small-pair-check.json
   The smaller command recomputes that range; the recorded full summary
   is compared only when --limit is 20000000.

DEPTH CONSEQUENCES AND LIMITS

The finite prime-pair check, together with the fixed-anchor proposition
proved in the manuscript, gives depth G^{<m}<=2 over every field for every
integer 3<=m<=20,000,000. For m>=6 the exceptional set is {3,5}; the
smaller nonempty supports are polynomial rings in one or two variables.
The notation G^{<m} specifies all pair relations on the inclusive support
A_m, rather than a strict inequality on prime labels.

This is an upper bound, not a computation that the depth equals two.
Exact depth may be 0, 1, or 2. The computation gives no conclusion beyond
its finite range. It complements the paper's separate theorem that the
same bound holds for all sufficiently large variable cutoffs, whose
numerical onset is not specified. Combining the two statements does not
settle any unverified gap between them.

The prime-pair condition is sufficient; it is not claimed necessary for
the depth bound. For the relation-weight cutoff G^{<=m}, a witness for p
has weight p+3 and may be omitted near m. The manuscript then gives the
weaker bound depth<=2+u_m<=4 in this finite range for m>=6, where u_m counts
primes in (m-3,m]. This check does not establish depth<=2 for that family.

THREE SEPARATE SINGULAR CHECKS

From the supplement directory, run:
  Singular -q computations/goldbach-cutoff42-primary.sing
  Singular -q computations/goldbach-cutoff42-tor-check.sing
  Singular -q computations/goldbach-single-colon-prefixes.sing

These scripts were developed with Singular 4.4.1p5 and use its standard
libraries primdec.lib and elim.lib. They regenerate the relevant ideals;
no saved matrix or ideal input is required. The Python runner verifies
their source hashes but DOES NOT run Singular or recheck these claims.
Capture stdout separately if saved execution logs are desired.

The first script checks toric elimination, the primary decomposition,
and variable colon ideals on the supports through 41 and through 29,
over Q and F_2. The second checks regular sequences, socles, and the
regularity bound on the support through 41, giving depths 2,1,0 for
G, its toric quotient, and G/(x3), respectively. The third tests all
31 nonempty odd-prime prefixes through 131 over Q. It checks the
single-colon equalities at earlier prefixes, the second-colon equality
at 131, and the colon of the exceptional binomial. The manuscript gives
the field-independence argument for binomial membership assertions;
hash agreement alone is not a mathematical verification.

The general asymptotic, interpolation, stabilization, and eventual-depth
proofs are in the manuscript. No torsion, Massey-product, residue-field,
or ternary-prime-operation calculations are needed for this package.
