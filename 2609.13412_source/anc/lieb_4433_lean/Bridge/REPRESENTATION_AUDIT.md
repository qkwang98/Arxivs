# Representation-theory dependency audit

Audited local mathlib revision: `c44e0c8ee63ca166450922a373c7409c5d26b00b`,
using Lean 4.19.0.

Available reusable foundations include:

- `FDRep.character`, `FDRep.char_one`, `FDRep.char_conj`,
  `FDRep.char_iso`, and `FDRep.char_orthonormal` in
  `Mathlib/RepresentationTheory/Character.lean`.
- `FDRep.finrank_hom_simple_simple` (Schur's lemma) in
  `Mathlib/RepresentationTheory/FDRep.lean`.
- `GroupAlgebra.average`, `Representation.averageMap`, and
  `Representation.isProj_averageMap` in
  `Mathlib/RepresentationTheory/Invariants.lean`.
- Maschke semisimplicity in `Mathlib/RepresentationTheory/Maschke.lean`.
- Finite permutation groups and cycle types, finite group algebras,
  Coxeter groups, matrix traces and trace invariance under conjugation.
- Young diagrams and semistandard tableaux in
  `Mathlib/Combinatorics/Young/YoungDiagram.lean` and
  `Mathlib/Combinatorics/Young/SemistandardTableau.lean`.

A search across this complete local mathlib tree found no implementation of
Specht modules, Young symmetrizers, Young's orthogonal or seminormal
representations, symmetric-group branching, Schur-Weyl duality,
Jucys-Murphy operators, the hook-length formula, or Murnaghan-Nakayama.
The existing semistandard-tableau file supplies the basic tableau data
structure and elementary ordering properties; it does not construct the
ordinary irreducible representations used in the supplied proof.

The substantive missing connection is therefore the identification

`trace(rho_nu(Q B P swap B Q)) = f_eta * smallTableauTrace(eta, mu, sign, nu)`.

Checking the twenty small rational matrix traces proves arithmetic about
the specified matrices. It does not by itself prove this identity for the
ordinary irreducible characters of `Equiv.Perm (Fin 14)`. To close it one
must construct the relevant representations and prove the branching and
matrix-action facts, or give an alternative group-algebra proof connecting
the same coefficient rows to the genuine character projectors.

`CentralAveraging.lean` isolates an independently provable portion of that
connection: conjugation averaging, preservation of pairing with class
functions, finite Fourier reconstruction from explicit orthogonality and
spanning hypotheses, and positivity of the resulting character-weighted
form. Its character hypotheses are explicit theorem arguments, not global
axioms or disguised instances of the desired bridge. Their specialization
to the complete ordinary-character family remains a separate obligation.

`Normalization.lean` is completely independent of these representation
facts. It proves the precise arithmetic equivalence of the unnormalized
bridge and the normalized convex inequality, and the conditional transfer
of PDC from the four named partitions.

`CharacterProjector.lean` proves that coefficient convolution is represented
by operator multiplication, that class coefficients give central operators,
and that inverse/star-compatible convolution idempotents give Hermitian PSD
projectors. Its character specialization requires the explicit convolution
identity `sum_g chi(g) chi(g^-1 k) = |G| / degree * chi(k)`. Pointwise
character-table orthogonality alone is not substituted for this identity.

`ProjectorConvention.lean` resolves the inversion convention explicitly:
under `chi(g^-1) = chi(g)`, the coordinate matrix of the tensor operator in
`Immanant.lean` equals the matrix projector in `CharacterProjector.lean`.
No identification of an arbitrary supplied function with an ordinary
irreducible character is implicit in this equality.

A compressed finite proof remains a possible future route, with an exact
boundary. The 135-by-135 character-table orthogonality check is finite and
plausible, as is class-function completeness using permutation cycle types.
To derive projectors, one still needs a proof that the supplied functions
are genuine characters or independently justified class-algebra product
counts. Defining those product counts from the same character table and
then using them to establish its character convolution would be circular.
One possible alternative to a full Specht construction is to realize the
Jacobi-Trudi functions as integral virtual combinations of genuine Young
permutation representations, then use semisimplicity and orthogonality to
prove irreducibility. This would address character realization but would
still leave the stated skew-tableau branching/trace identity to prove.
