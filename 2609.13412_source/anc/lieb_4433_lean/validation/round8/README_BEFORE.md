# Order-fourteen bridge: partial Lean formalization

**Status: incomplete. This project does not yet prove the ordinary-immanant
bridge for all complex Hermitian positive-semidefinite matrices.** It contains
compiled proofs of the direct contraction mechanism, the complete finite
twenty-row certificate calculation, the Gram/tensor identities, and the exact
normalization. The missing step is the representation-theoretic identification
of the computed tableau traces with the actual ordinary symmetric-group
witnesses. This is a substantive proof obligation, not an additional historical
Pate theorem that may be imported under the requested scope.

In particular, there is no closed theorem here asserting

\[
59512d_{4433}(A)\le4035d_{653}(A)+6725d_{644}(A)
 +39759d_{554}(A)+23636d_{5333}(A).
\]

`LiebBridge.Bridge4433` is a **definition of the desired proposition**, not a
proof of it. The theorem `pdc4433_of_bridge_and_four_pate` has that bridge as an
explicit extra hypothesis. It must not be described as the requested result
conditional only on four Pate theorems.

## What is proved

### Direct analytic positivity

`Bridge/Contraction.lean` proves, for arbitrary finite complex arrays,

\[
\langle a\otimes b,F(a\otimes b)\rangle
 =\sum_o\left|\sum_l\overline{b_l}a_{o,l}\right|^2.
\]

This is an equality in the complex numbers; taking the real part gives
nonnegativity. Local filters need not preserve the decomposability of the
individual factors inside either side of the cut.

The principal theorem is `LiebBridge.projectedSwapWitness_nonneg`. It proves
positivity of the exact localized operator `Q B P F B Q` on every split tensor,
using actual matrices and Kronecker products. Its explicit assumptions are

\[
P^\dagger=P,\quad P^2=P,\quad Q^\dagger=Q,\quad B^\dagger=B.
\]

The proof derives the identity
`Q B P F B Q = (P B Q)† F (P B Q)` and then applies the sum of squares.
Commutation of `P` with the swap follows from its actual support on the
untouched block. There is no assumed witness-positivity statement and no
partial-transpose theory.

`Bridge/TensorWitness.lean` proves exact coordinate regrouping, preservation of
the inner product, and factorization of an ordinary pure tensor across the
required cut. It provides the site equivalences `12+1+1 = 14` and `10+2+2 = 14`.
Its local matrices remain parameters; they have not yet been identified with
the specific ordinary-character projectors of the certificate.

### Full complex PSD Gram domain

`Bridge/TensorGram.lean` defines coordinate tensors, the actual symmetric-group
action, pure tensors, their complex inner product, and Gram matrices. It proves
unitarity of the action and the exact Gram monomial identity, with the inverse
permutation convention fixed explicitly.

`exists_gram_of_posSemidef` uses mathlib's theorem
`Matrix.posSemidef_iff_eq_transpose_mul_self` to realize every complex Hermitian
PSD matrix as a Gram matrix. This includes singular matrices and the zero
matrix. No fixed rank, positive-definiteness, real-entry, or genericity
assumption is used.

`Bridge/Immanant.lean` defines the immanant for a **supplied character function**
and the permanent, constructs the tensor representation and character-weighted
operator, and proves

\[
\langle v,P_\chi v\rangle
 =\frac{\mathrm{degree}}{|S_I|}\,d_\chi(\operatorname{Gram}(v)).
\]

It also proves reality on Hermitian matrices for real inversion-invariant
characters. It does not construct the ordinary irreducible character family.

### Exact finite certificate

The entry point is `Bridge/Certificate.lean`, namespace
`LiebBridge.Certificate`. The checked computation uses rational/integer
arithmetic and `decide +kernel`, not floating point or `native_decide`.

The following are proved:

- The partition enumerator is complete, sound, duplicate-free, and has exactly
  135 elements: positive nonincreasing lists summing to fourteen.
- All twenty rational tableau trace rows agree with the supplied sparse
  coefficient rows on every partition of fourteen.
- All twenty rational weights are strictly positive.
- Row metadata has the required sizes, valid partitions, containment,
  `k = 1` or `k = 2`, and sign `+1` or `-1`.
- Every enumerated tableau has the required length; each basis has no
  duplicates; every adjacent axial denominator used is nonzero.
- Sparse keys are distinct valid partitions and stored entries are nonzero.
- The weighted stored coefficient identity holds for every list of natural
  numbers, so cancellation is not limited to the five surviving partitions.
- The weighted computed identity holds for every partition of fourteen.
- The surviving linear form is exactly

  \[
  4035d_{653}+6725d_{644}+39759d_{554}+23636d_{5333}-59512d_{4433}.
  \]

The five numerical hook quotients are checked to be
`12012, 15015, 9009, 6006, 15015`. **Their identification with actual irreducible
character degrees is not yet proved.** That requires the missing representation
construction and hook-length dimension theorem, or an equivalent dimension
argument. The sum of squared hook quotients and each row's hook-degree
cancellation are additional exact consistency identities, not substitutes for
that dimension theorem.

`bridge_of_witness_nonnegative` is an arithmetic implication for an arbitrary
function on shapes. Its twenty witness-positivity assumptions are explicit;
this theorem is not the matrix bridge.

### Generic character algebra

`Bridge/CentralAveraging.lean` proves central averaging and character expansion
from explicit class-function, orthogonality, and spanning hypotheses.

`Bridge/CharacterProjector.lean` proves multiplication/convolution compatibility,
centrality, Hermiticity, idempotence, and PSD of the relevant operator formulas
from explicit representation and coefficient identities. In particular, the
ordinary character **convolution identity** is a hypothesis; pointwise character
orthogonality alone is not substituted for it.

`Bridge/ProjectorConvention.lean` proves that the matrix and tensor operator
definitions agree under explicit inverse invariance of the character. This
accounts for the formulas using `χ(g)` and `χ(g⁻¹)`.

These are proved general lemmas. Their hypotheses have not yet been instantiated
for the required ordinary characters and embedded symmetric subgroups.

### Exact convex normalization and the four historical interfaces

`Bridge/Normalization.lean` proves equivalence of the unnormalized bridge with

\[
\bar d_{4433}\le
\frac{20175}{238048}\bar d_{653}
+\frac{20175}{238048}\bar d_{644}
+\frac{79518}{238048}\bar d_{554}
+\frac{118180}{238048}\bar d_{5333}.
\]

All four coefficients are proved strictly positive and their sum is exactly
one. The arithmetic transfer of the four upper bounds to the target is proved.

`Bridge/PateInterfaces.lean` exposes four separately named propositions:

- `LiebBridge.Pate653`
- `LiebBridge.Pate644`
- `LiebBridge.Pate554`
- `LiebBridge.Pate5333`

Each quantifies over every `Matrix (Fin 14) (Fin 14) ℂ` satisfying mathlib's
`PosSemidef` predicate and states the indicated normalized immanant bound by
the permanent. The ordinary character family is still an explicit parameter.
The historical proofs are not formalized, and none of these propositions is
declared as a global axiom. In a completed application they would be supplied
as precisely the four permitted historical theorem arguments.

## Exact remaining proof obligation

The missing central identification is

\[
\operatorname{Tr}\rho_\nu(W_j)
 = f^{\eta_j}\,\mathrm{computedCoeff}(j,\nu),
\]

for the actual ordinary symmetric-group representations and the actual
central-projector witnesses. It requires:

1. Construction/identification of the ordinary character family, including
   completeness, convolution, reality, inverse invariance, and its degrees.
2. Identification of the embedded subgroup projectors with the local matrices
   used by the contraction theorem.
3. The relevant branching/multiplicity statement, the intermediate-shape
   projection, and the specified seminormal action on the skew-tableau space.
4. Idempotence and the needed commutations for the cyclic trace reduction,
   including the pair-sign projector.
5. Instantiation of the central averaging and Gram lemmas to derive all twenty
   actual immanant witness inequalities.

This is a finite representation-theoretic identity independent of `A`, but it
has not been proved here. Checking the rational table, verifying Coxeter
relations for unrelated matrices, or assuming the twenty witness inequalities
would not close it. No such assumption is hidden in a purported completed
bridge theorem.

See `INDEPENDENT_FORMALIZATION_AUDIT.md` for the separate adversarial review and
`CERTIFICATE_STATUS.md` for the finite-computation boundary.

## Build and reproduce

The project pins:

- Lean `leanprover/lean4:v4.19.0`
- mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`
- transitive dependencies in `lake-manifest.json`

From the extracted project directory, with Git and elan installed:

```sh
elan toolchain install leanprover/lean4:v4.19.0
lake exe cache get
lake build
python3 scripts/check_axioms.py
python3 scripts/check_generated.py
```

The first dependency/cache download requires internet access. Do not update
the dependency revisions when reproducing this version. `lake build` rebuilds
the project proofs; the certificate uses kernel reduction and may take longer
than a native numerical check.

`scripts/check_generated.py` regenerates the two generated Lean files in an
isolated temporary directory and compares them byte-for-byte with the delivered
files. The Python generators are not trusted by Lean: they only emit literals
and theorem statements that the Lean source checks exactly. The handwritten
algorithm, enumeration proof, contraction proof, and universal arithmetic
identity are separate from the generators.

`Audit.lean` prints the dependencies of the key proved statements. No project
axiom, `sorry`, `admit`, or native-evaluation trust axiom is used. The standard
foundational axioms appearing in the audit are `propext`, `Classical.choice`,
and `Quot.sound`. Visible hypotheses of generic lemmas are not axioms and
remain mathematical obligations at every application.

`validation/BUILD_STATUS.md` records what was actually tested on the available
machine, including the distinction between an isolated source rebuild and a
fresh internet dependency installation.

## Specification provenance

The mathematical source files are preserved under `specification/`:

- `FINAL_PROOF.md` and `exact_certificate/certificate.json` came from the
  supplied `lieb_pdc_4433_independent_review_packet.zip`.
- `INDEPENDENT_AUDIT.md` is the recovered final response from the separate
  task titled **Audit permanental dominance proof**, identified through the
  user's reference to **Lieb permanental dominance**.

These are mathematical specifications and review evidence, not additional Lean
axioms or instructions overriding the requested scope.
