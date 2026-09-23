# Round-two audit: ordinary Young representation and branching realization

Date: 2026-09-11. This is a new, read-only mathematical/interface audit. Established Lean modules have not been edited. The sole new objective is to prove the actual ordinary Young-representation/branching trace identity; further arithmetic checks alone do not meet that objective.

**Latest independently verified boundary.** The requested ordinary Young-representation/branching trace identity is now independently compiled and axiom-audited: `WitnessTrace.trace_witness_eq_computedCoeff` proves the actual sandwich trace equals the actual prefix dimension times the unchanged evaluator for every certified witness and every partition of fourteen. Its only inputs are the witness, membership in the twenty rows, the partition list, and the semantic partition-of-fourteen proof. No representation, irreducibility, branching, matrix-identification, trace, or positivity premise remains. The actual character family also spans all real class functions on `S14`. The separate use of this trace in the full PSD/immanant conclusion still requires instantiating the concrete tensor localization and expectation/coefficient assembly; this audit does not silently identify the trace endpoint with the entire PDC theorem. The detailed construction reviews below record the completed interfaces and their earlier intermediate boundaries.

## 1. Required endpoint and fixed conventions

For each certificate row `w=(k,eta,mu,sign,...)` and each ordinary partition `nu` of fourteen, the required identity is

\[
\operatorname{Tr}\rho_\nu(QBP\tau_k BQ)
=\dim(V^\eta)\,\mathrm{computedCoeff}(w,\nu).
\]

The left side must use an actual representation of `Equiv.Perm (Fin 14)`, the actual ordinary partition label, and the actual central projectors for the embedded groups. The right side is the existing rational evaluator from `CertificateAlgorithm.lean`; it must not be replaced by a newly defined trace expression without proving equality to that evaluator.

Already fixed and audited conventions:

- Tensor position permutations form a left action, and a pure-tensor expectation of `U_sigma` is the Gram monomial with `sigma^-1`.
- The ordinary immanant uses the monomial with `sigma`. The explicit inverse-character convention lemma accounts for this difference.
- Boxes are zero-indexed. Content is column minus row. For the adjacent generator on labels `i,i+1`, the axial gap is `content(i+1)-content(i)`.
- A seminormal matrix column is the source tableau. Its diagonal entry is `1/d`; its entry at the swapped target tableau is `1+1/d`.
- The evaluator reverses a matrix word before sequential application. Thus `[1,0,2,1]` implements `S2 S1 S3 S2`, and `[2,1,0,2,1]` implements `S3 S2 S1 S3 S2`.
- The prefix selector is on the left in the trace. Filtering the initial tableau is correct because only closed paths contribute.
- The factor `dim(V^eta)` is not a normalization convention. It comes from a genuine tensor/multiplicity decomposition and has to be proved.

## 2. Minimal substantive lemma at each interface

| Construction | Smallest mathematical lemma that turns it into progress | What is insufficient |
|---|---|---|
| Growth/tableau model | A bijection between the defined growth tableaux and the existing valid box-list tableaux, respecting contents, adjacent swaps, and prefix shape | A second tableau data type with similar names |
| Local generator algebra | Involution, distant commutation, and adjacent braid for the actual truncated seminormal action | Nonzero denominators or a generic theorem assuming those relations |
| Coxeter-to-permutation extension | A representation of the actual `Equiv.Perm (Fin n)` sending its adjacent swaps to the proved generators | A representation of an abstract Coxeter group whose identification with `S_n` is still a hypothesis |
| Ordinary irreducibility and labels | Simplicity and pairwise inequivalence for the tableau representations, with canonical Young growth/content labels | Coxeter relations, correct matrix dimensions, or a complete family with arbitrarily assigned partition names |
| Branching | The prefix/tail basis bijection and intertwining of the embedded smaller symmetric-group action with the prefix action | An equality of dimensions alone |
| Central prefix projectors | Actual central character projectors act as the indicator of the required prefix shape | Declaring the diagonal prefix indicator to be the character projector |
| Tail action | Each adjacent permutation supported on the final boxes acts trivially on the prefix basis and by the existing skew seminormal action on the tail | An abstract multiplicity-space trace assumption |
| Existing evaluator semantics | The path evaluator equals the trace of the explicitly defined rational matrices, including list multiplicities and word order | Recomputing the same rational table or defining the trace to equal the evaluator |
| Final trace factor | Trace of `Id_(StdTab eta) tensor localWord` is `card(StdTab eta)` times the local trace, with the actual prefix/projector decomposition | Omitting the prefix dimension or identifying it with a hook quotient by name |

## 3. Economical construction route

A full general hook-length theorem, Schur--Weyl theory, or Robinson--Schensted correspondence is not logically necessary for this finite target. A possible economical route is the following.

### A. Derive the ordinary tableau representations

Start with genuine standard growth tableaux and establish the seminormal Coxeter relations. The local combinatorial input needs more than the existing denominator checks:

1. For consecutive labels, a nonstandard adjacent swap means their boxes lie in the same row or column; the axial gap is then respectively `+1` or `-1`.
2. A standard adjacent swap has gap different from `0,+1,-1`, so the two off-diagonal transition coefficients needed for irreducibility are nonzero.
3. The contents of three consecutive labels are pairwise distinct. In a braid calculation this prevents a zero denominator of the form `d_i+d_(i+1)`.
4. Distant adjacent swaps affect disjoint pairs and preserve the corresponding contents and admissibility conditions.

Once the actual `S_n` action is constructed, the Jucys--Murphy recurrence

\[
X_1=0,\qquad X_{i+1}=S_i X_i S_i+S_i
\]

can prove that `X_i` is diagonal, with eigenvalue equal to the content of the box containing label `i`. This identifies these diagonal operators with actual group-algebra elements; merely defining diagonal content operators would not provide that identification.

Distinct addable boxes of a Young shape have distinct contents, so a complete content sequence determines its growth tableau. Polynomial interpolation in the commuting `X_i` then provides the individual coordinate projections. An invariant subspace containing a nonzero vector contains one tableau basis vector; connectivity of the standard-tableau graph under admissible adjacent swaps, together with nonzero transition coefficients, gives the whole basis. This proves irreducibility over the complex numbers directly. Disjoint joint content spectra for different final shapes prove inequivalence.

The joint-spectrum argument avoids incorrectly inferring absolute irreducibility over `C` from irreducibility over `Q`. It also gives a concrete, canonical Young label, rather than an arbitrary indexing of a family of irreducibles. The row representation must send each adjacent swap to `+1`, and the column representation to `-1`, fixing the possible sign/conjugate convention.

### B. Obtain finite dimensions and completeness without a general hook theorem

A prefix/tail tableau bijection yields the usual cardinal recurrence by removing the final corner. Once the recurrence is proved for actual tableau cardinalities, exact computation through order fourteen can establish the required counts. The sum of squared actual dimensions, together with irreducibility and inequivalence, can establish completeness through the regular representation and Maschke theory.

For the witness positivity, the `eta` dimension only needs to be strictly positive after the trace identity: a constructed standard tableau supplies nonemptiness. Its numerical hook quotient is unnecessary. The final normalization uses five numerical constants whose arithmetic is already checked. With the historical hypotheses stated literally as in the existing `PateInterfaces`, no theorem identifying those constants with actual dimensions is logically necessary to prove the requested literal inequality. Such an identification is needed only for a separate claim that they equal character values at the identity, or if the historical inputs were instead formulated using unspecified actual degrees. The existing hook-quotient checks do not by themselves prove that additional identification.

### C. Prove branching with the same basis, then evaluate the trace

The central combinatorial equivalence is

\[
\mathrm{StdTab}(\nu)\simeq
\coprod_{\lambda\vdash m}
\mathrm{StdTab}(\lambda)\times\mathrm{SkewTab}(\lambda,\nu).
\]

The embedded `S_m` generators act only on the first factor. Irreducibility and the genuine character-projector identities then show that `P_eta` selects exactly the prefix shape `eta`. Applying the same statement at `m=n-k` shows that `Q_mu` is exactly the intermediate-prefix selector.

On the selected `eta` block, adjacent permutations supported on the final `2k` labels fix the prefix tableau and act by the skew seminormal matrices. This produces `card(StdTab eta)` genuinely identical copies. The trace factor now follows from a standard finite trace-of-identity-tensor calculation.

For the sandwich-to-short-word trace reduction, remember that the analytic contraction theorem intentionally assumed less: it only needed Hermitian `Q,B`. The trace reduction additionally uses `Q^2=Q`, `B^2=B`, and the relevant commutations. These must be provided by the actual projector/permutation construction.

## 4. Rational versus orthogonal Young forms

The existing evaluator uses a rational seminormal basis. Those generator matrices are generally not Hermitian for the standard coordinate inner product. It would be incorrect to use ordinary matrix transpose as the adjoint of this basis representation without proving a weighted invariant inner product or changing basis.

There is no need to do that for this trace task. A rational seminormal representation can be extended to `C`, and its traces may be computed in that basis. The positivity theorem is applied separately in the genuine unitary tensor representation, where the central character projectors are Hermitian. An isomorphism of irreducible representations or the corresponding genuine character equality connects the two. This keeps square roots and an explicit orthogonalization out of the finite trace calculation.

The trace is basis-independent; the concrete action and ordinary representation label are not optional.

## 5. Initial review of the new evaluator-semantics module

The first inspected version of `Bridge/Young/TraceSemantics.lean` has the correct source-column/target-row convention. Its finite basis is the subtype of `tabs.toFinset`. Its `mass` function sums all paths reaching a tableau, so duplicate intermediate states represent distinct contributions and are correctly retained.

The `Supported` invariant and the step/flatMap lemmas are the right substantive mechanism: all intermediate states stay in the actual basis. The matrix entry handles a swapped target only when that target is present in the basis; this matches the existing list evaluator.

The eventual equality with `traceWord` must require `tabs.Nodup`. The evaluator's outer list sum counts repeated input tableaux, whereas a matrix trace on `tabs.toFinset` counts each basis vector once. The existing certificate safety theorem supplies this hypothesis for the actual data. It must not disappear in a purported theorem for arbitrary lists.

This semantics theorem, once complete, closes the computational-interface gap. It does not prove that the matrices are the actual ordinary multiplicity action; that is the branching construction in Section 3.

## 6. Rejection criteria during this round

The following would leave the user's sole objective unresolved:

- A theorem whose new hypothesis is the desired trace realization, witness inequality, or central-projector/tableau identification.
- Defining “ordinary character” to be an arbitrary supplied shape-indexed class function without constructing the corresponding standard irreducible representation and fixing its label.
- Proving only a Coxeter-group representation and assuming the map to the actual symmetric group is an isomorphism.
- Using character-table orthogonality or the squared-degree sum before establishing that the functions are genuine irreducible characters.
- Declaring the hook quotient to be the representation dimension without a dimension argument.
- Replacing the path evaluator by a trace definition without proving their equality.
- Treating rational seminormal generators as orthogonal matrices in the standard coordinate metric.
- Obtaining the prefix/multiplicity decomposition only as an uninstantiated structure field whose content is the missing branching theorem.

Generic intermediate lemmas with such explicit hypotheses can be useful construction tools. They count toward the objective only when the hypotheses are subsequently discharged for the actual tableau/S_n model.

## Initial assessment (before the subsequent construction checks)

The authoritative paper proof supplies a mathematically coherent route. The previous analytic witness positivity, exact certificate, and convention checks remain intact. In this round the critical work is ordinary representation construction, prefix-compatible branching, and the actual trace identification. The new evaluator-semantics work has the correct initial interface, but no completion of the full ordinary trace identity is certified by this initial round-two audit.

## 7. Live construction review

### Evaluator semantics: interface completed

The subsequently inspected `TraceSemantics.lean` contains `traceWord_eq_matrixTrace` and `computedCoeff_eq_matrixTrace`. Their mathematical statements close the evaluator-to-concrete-matrix-trace interface identified above. The input basis is explicitly duplicate-free, the selected initial tableau gives the diagonal selector on the left, and `runWord` applies the rightmost factor first. In the two-contraction case, the matrix has precisely the scalar `1/2` and the sign-weighted prefix `S3`. No irreducible representation, positive semidefiniteness, or ordinary-character identity is assumed or claimed by these statements.

The finite path-mass proof correctly sums repeated intermediate paths. Replacing intermediate states by a set would have been wrong; the inspected implementation does not do so. The subtype of `tabs.toFinset` is only used for matrix coordinates and the final distinct basis sum.

### Tableau geometry and the total swap

`TableauGeometry.lean` defines a genuine standard tableau by a bijective numbering that is strictly increasing in the product order on Young-diagram cells. This is the correct row-and-column condition. The proofs of neighboring comparable consecutive cells, axial gap `+1` or `-1` in that case, and distinct contents for labels at distance at most two have the required mathematical strength. In particular, the equal-content argument constructs two distinct intervening cells, rather than silently assuming the two labels lie on one row or column.

`TableauSwap.lean` correctly swaps neighboring values when their cells are incomparable. Its `adjacentSwap` is total, fixing a tableau when the ordinary adjacent swap is forbidden. This is a useful combinatorial involution, but it is **not** itself the seminormal generator: in a forbidden column case the linear generator is multiplication by `-1`. Any generator built from the total swap must retain the separate diagonal coefficient and suppress the forbidden off-diagonal contribution. An unguarded expression involving `1+1/d` times the fixed tableau would be wrong in the forbidden row case, where `d=1`.

### Coxeter presentation and index convention

The inspected `CoxeterExtension.lean` normal-form argument works in an arbitrary monoid with explicitly stated square, distant, and braid relations. Its preliminary type-A map sends the abstract simple generators to the actual adjacent permutations and proves those images. This does not yet certify an isomorphism until injectivity and surjectivity are proved.

The convention is explicit: `Relations n` has `n` generators and presents the permutations of `n+1` positions. The fourteen-position application therefore uses thirteen generators. A correct cardinality or abstract group isomorphism would not by itself fix this generator correspondence; the final extension theorem must preserve the already proved adjacent images.

### Trace shortening and the multiplicity factor

For the actual projectors, cyclicity gives

\[
\operatorname{Tr}(QBP\tau BQ)
=\operatorname{Tr}(PQB\tau).
\]

The reduction uses projector idempotence and the relevant disjoint-support commutation, including `Q B = B Q`. Those are additional representation facts, not consequences of the deliberately weaker hypotheses of the analytic contraction lemma. On the `eta` prefix block, the resulting trace is

\[
\dim(V^\eta)\operatorname{Tr}(D_\mu B\tau).
\]

There is no factor of `dim(V^mu)` or `dim(V^nu)`. The zero-based word `[1,0,2,1]` is the product of adjacent permutations giving `(0 2)(1 3)` on the final four positions, as required. The trace factor is positive because the actual `eta` representation is nonzero; its exact numerical hook quotient is unnecessary at this cancellation step.

### A direct check fixing the Jucys--Murphy sign

The rational coefficient convention is compatible with content, rather than negative content. Let consecutive labels occupy cells of contents `x,y`, put `d=y-x`, and order an allowed two-tableau block as `(t, swapped t)`. Its actual source-column generator matrix is

\[
S=\begin{pmatrix}
1/d&1-1/d\\
1+1/d&-1/d
\end{pmatrix}.
\]

For `d` nonzero, direct multiplication gives `S^2=I` and

\[
S\begin{pmatrix}x&0\\0&y\end{pmatrix}S+S
=\begin{pmatrix}y&0\\0&x\end{pmatrix}.
\]

For a forbidden swap, `d=+1` or `-1`, and the one-dimensional calculation is `x+1/d=x+d=y`. Thus the proposed Jucys--Murphy recurrence has exactly the desired diagonal contents in both cases. This checks a potentially consequential normalization before the ordinary-label argument; it does not substitute for the actual group-action or irreducibility proofs.

### Independent Lean verification so far

An independent invocation of Lean on `Bridge/Young/TraceSemantics.lean` completed successfully. The new geometry and presentation files are under active construction; their mathematical interfaces have been reviewed above, but this audit does not infer completed compilation or finished representation realization from intermediate source alone.

## 8. Completed symmetric-group extension and a precise local truncation route

The subsequently completed `CoxeterExtension.lean` has independently passed source review and Lean compilation. `toPerm_eq_one_imp` proves the presentation map has trivial kernel by induction: write a kernel element as a smaller-rank element times a descending string; evaluate its permutation at the string's lowest point; the embedded smaller group fixes the final point, forcing the string to be empty; apply the induction hypothesis. Surjectivity follows from generation by the actual adjacent permutations.

Consequently `presentationEquiv` is a proved isomorphism with the genuine finite symmetric group, respecting each adjacent generator. `existsUnique_extension` takes exactly the square, distant-commutation, and braid relations, and yields the unique homomorphism from `Equiv.Perm (Fin (n+1))` with the specified adjacent images. There is no residual presentation hypothesis. This interface is now closed; the local seminormal relations still have to be supplied by the tableau construction.

The inspected `LocalBraid.lean` uses the six orders `abc,bac,acb,cab,bca,cba`. Both swap arrays, both gap arrays, and the source-column coefficients agree with that ordering. Its ambient braid statement for pairwise distinct rational contents has the correct mathematical scope. It deliberately does not assert that an arbitrary coordinate restriction preserves the braid relation.

A precise way to transfer the ambient relation is the following subquotient argument. Fix three consecutive labels and allow all six orders of their cells, leaving other labels unchanged.

1. The span of column-increasing orders is invariant. A swap leaving that set crosses two consecutive cells of a column in the forbidden direction; its axial gap is `-1`, so the outgoing coefficient `1+1/d` is zero.
2. Within that invariant space, the span of orders violating a row condition is invariant. A swap that could repair the final row violation reverses a horizontal neighboring pair; again its axial gap is `-1` and the coefficient is zero.
3. The quotient therefore has precisely the standard-order coordinates, with the desired truncated coefficients. Its generators inherit the ambient relations.

For this local argument, any two of the three cells cannot be strictly southeast of one another: the two grid neighbors between such cells would force two distinct intervening labels. Thus all relevant induced comparisons are row or column comparisons. Inequalities with outside labels are preserved because those labels lie outside the fixed three-label interval. These facts identify the quotient coordinates with actual standard tableaux.

This is a proposed rigorous transfer mechanism, not a claim that its Lean implementation is already complete. It can also be expressed using simultaneous block-triangular matrices: column-increasing coordinates are invariant, and row-violating coordinates inside them are invariant. Coordinate restriction to the quotient then preserves products. The standard coordinates alone are generally not an invariant subspace, since a forbidden row exit has `d=+1` and coefficient `2`.

At this point the evaluator semantics and genuine symmetric-group presentation interfaces are independently certified. They do not yet establish the actual Young generators' full relations, irreducibility, branching projectors, or the required ordinary trace identity.

## 9. Further independently compiled building blocks

`Seminormal.lean` now defines the genuine rational linear generator on `StandardTableau d → Q`. Its row-coordinate off-diagonal coefficient is `1-1/axial(row)`, which is exactly `1+1/axial(source)` at the swapped source because swapping reverses the gap. The forbidden branch is explicitly zero. `generator_square` handles both the allowed two-tableau case and the forbidden `+1`/`-1` cases. An independent Lean invocation completed successfully.

Independent Lean invocations also completed successfully for `LocalBraid.lean` and `TriangularCompression.lean`. The latter implements the proposed two-step invariant flag by concrete matrix zero entries, proves closure under multiplication, and proves that compression preserves products and braid relations over an arbitrary semiring. The directions of the zero-entry conditions have been audited against target rows and source columns. There is no unproved assertion that a principal submatrix of arbitrary braid matrices still satisfies braid.

The remaining application of this local mechanism can be reduced to immediate grid edges. Let `C` and `R` mean that the six-order filling respects vertical and horizontal neighboring-cell constraints. An adjacent value swap reverses only its swapped pair's relative order. Therefore a newly violated column edge or a repaired row edge forces source axial gap `-1`, annihilating the corresponding transition. Standardness follows from all immediate row and column edges increasing; edges involving a label outside the three-label interval retain their order automatically. This version avoids a case classification of all possible local posets.

The exact remaining distinction is unchanged: a checked ambient braid, a checked compression theorem, and a checked actual generator involution are construction ingredients. The actual generator's braid and distant commutation must still be derived, followed by genuine representation irreducibility/labels, prefix-compatible branching, and the central-projector trace realization.

## 10. Actual prefix basis and the concrete flags

`BranchingBasis.lean` has independently passed mathematical review and Lean compilation. Its `prefixEquiv` constructs the two restrictions and their inverse:

\[
\{t:\mathrm{StdTab}(\nu):\text{first }|\eta|\text{ cells}=\eta\}
\simeq \mathrm{StdTab}(\eta)\times\mathrm{SkewStdTab}(\eta,\nu).
\]

The skew label is the original label minus `eta.card`, with a proved lower bound making natural subtraction legitimate. In the inverse construction, the lower-set property of the initial Young diagram excludes a comparable pair pointing from an outer cell back into the prefix. Empty and full prefixes are covered by the same construction. `prefix_card` is therefore a cardinality statement about actual bases, not an assumed branching multiplicity. The next substantive interface is intertwining the actual smaller-group and tail generators through this basis equivalence.

`NumberingFlags.lean` has also independently passed compilation. It proves that immediate row/column inequalities characterize standard numberings, using grid paths. Its `column_exit_gap` and `row_reentry_gap` prove the exact `-1` gap needed for the flag zero entries. The latter is valid without an extra column condition; no positivity or representation hypothesis is hidden in either statement.

The inspected `AmbientBraid.lean` correctly distinguishes full numbering matrices from actual standard tableaux. Its intended braid identity is columnwise, requiring three distinct source contents. A global braid identity on all numberings would be false in the presence of equal-content collisions. To obtain the standard-tableau braid from the full numbering matrices, rewrite products with `compress_mul` and apply the columnwise result to each retained standard source; do not apply `compress_braid` with an unproved global ambient identity.

The proposed orbit-inclusion transfer can work without a separate orbit-injectivity theorem: establish `M_i O = O S_i`, use the six-dimensional braid, and select the column of `O` that is the original numbering's delta vector. This is a genuine intertwining argument, not an assumption that all ambient numberings carry a representation.

## 11. Concrete compressed braid now checked

The completed `AmbientBraid.lean` has independently passed source audit and Lean compilation. It implements the orbit-inclusion transfer described above and proves `numberingMatrix_braid_column`. The six actual numberings, the local gap arrays, and both intertwining directions agree with the source-column convention.

Its `compressed_braid` theorem is about the genuine subtype of numberings satisfying both row and column flags. Its only index assumptions say that the three labels are consecutive. All three content inequalities are derived from actual standard-tableau geometry. Products are transferred through `compress_mul` before the retained source column is selected, so the proof does not assume the unavailable global ambient braid.

This closes the difficult local braid calculation on the standard-numbering model. Identifying this subtype with the `StandardTableau` structure and matching its compressed matrices to the separately defined row-form generator are still explicit integration steps. They are concrete coordinate equivalences, whereas irreducibility, ordinary labels, prefix-generator intertwining, and the central-projector trace identity remain substantive representation-theoretic obligations. No full ordinary trace identity is claimed by this audit at this stage.

## 12. Actual rational Young action now checked

`StandardCompression.lean`, `YoungRepresentation.lean`, and the updated `Seminormal.lean` have independently passed source audit and Lean compilation. The flag subtype is now explicitly identified with `StandardTableau`; the compressed matrix is proved equal to the actual row-form operator's coordinate matrix. This proof converts source and target gaps by sign reversal and explicitly rules out a fixed allowed swap. It preserves the existing evaluator's `1+1/d` source coefficient exactly.

The actual row-form generators now satisfy square, distant commutation, and braid relations. `YoungRepresentation.representation` constructs a homomorphism from the actual permutation group on `n+1` positions when `d.card=n+1`. Its prescribed adjacent action and uniqueness are proved. The indexing is correct: a generator index `i` acts on tableau labels `i,i+1`, and the fourteen-position application uses `n=13`. There is no trace, character, irreducibility, or abstract-presentation premise in this construction.

The updated seminormal file also proves the actual operator recurrence

\[
S_iD_iS_i+S_i=D_{i+1}.
\]

Together with the zero first-content operator, this can derive all diagonal invariance from generator invariance. An explicit sum-of-transpositions definition of Jucys--Murphy elements is unnecessary for this use: the recurrence itself realizes each diagonal as a universal polynomial in actual generators. Intertwiners preserve these diagonals for the same reason.

The new generic `DiagonalIrreducibility.lean` has been reviewed mathematically: finite interpolation yields coordinate projections, nonzero directed coefficients propagate coordinate vectors, and a nonempty basis is explicit in its simple-module conclusion. Its hypotheses are actual endomorphism identities and coefficient connectivity. The Young application must still discharge those hypotheses, and the argument must be instantiated over `C`; a rational irreducibility result alone would not justify absolute irreducibility.

The current remaining chain is therefore smaller but still substantive: actual tableau graph connectivity and nonzero transition coefficients, content separation across distinct shapes, complex irreducibility, intertwining of prefix/tail actions through the proved basis split, the dictionary to existing skew box lists, and identification of the actual central projectors. The required ordinary trace identity has not yet been certified.

## 13. Actual complex irreducibility now checked

The subsequently completed `YoungIrreducibility.lean` and corrected `ScalarExtension.lean` independently compile. `complex_isSimpleModule` is a theorem about the actual complex symmetric-group representation on the genuine standard-tableau basis. Every premise of the generic criterion is discharged: the basis is nonempty by the constructed linear-extension tableau, the initial content operator is zero, the actual recurrence supplies content invariance, content sequences separate tableaux, and the proved adjacent-swap connectivity is realized by nonzero coefficients of the actual representation. The edge index is correctly recovered from consecutive tableau labels and the cardinal equality `d.card=n+1`.

This is a direct complex irreducibility proof, not an inference from rational irreducibility. More generally the same constructed action is proved irreducible over every characteristic-zero field. No unresolved simplicity or ordinary-character premise appears in the actual endpoint.

`TableauExistence.lean` and `CrossShapeSeparation.lean` also independently compile. The latter proves that equal aligned content sequences force equality of the Young shapes and tableaux, and that distinct equal-size shapes retain distinct sequences after casting to a characteristic-zero field. The passage from these separated spectra to inequivalence of actual representations is an additional intertwining step.

`BranchingAction.lean` independently compiles and now includes `generator_extendByZero`. Thus the prefix block is an actual invariant support for the smaller adjacent generators, and `prefixEquiv_intertwines` carries their action to the genuine inner tableau operator with fixed skew coordinate. This goes beyond a mere cardinality split. Extending this to the embedded smaller group, proving the tail action, and identifying the character projectors remain to be connected to the trace calculation.

Independent axiom inspection of the actual representation, generator braid, recurrence-based general simplicity criterion, prefix basis equivalence, and evaluator trace theorem returned only `propext`, `Classical.choice`, and `Quot.sound`.

Independent axiom inspection of the actual `YoungIrreducibility.complex_isSimpleModule` endpoint subsequently returned the same three standard axioms.

For the next projector step, Schur's lemma plus character orthogonality can prove the normalized central character sum acts as identity on its own simple representation and zero on a distinct simple representation. The shifted convolution identity needed by the existing analytic projector module then follows directly from the self-projector identity: reindex by inversion, multiply by the represented element `k`, and take trace. This does not require a prior completeness theorem for the entire Young family.

## 14. Projector normalization and the exact list dictionary

The inspected `CentralProjectorAction.lean` has the correct mathematical normalization. It uses the actual inverse character and `finrank(V)/|G|`, derives scalar action by Schur's lemma, and computes the scalar's trace using character orthogonality. In the isomorphic case it explicitly transports actual dimension through the isomorphism; in the nonisomorphic case it cancels the proved nonzero actual dimension of the target. No hook quotient or diagonal-selector identity is assumed. The generic theorem still has to be instantiated on the actual Young modules and their prefix restrictions.

The inspected `YoungInequivalence.lean` derives preservation of the content operators from the actual group-action intertwining condition. Cross-shape separation then annihilates every matrix coefficient of an intertwiner. Excluding an invertible intertwiner uses the genuinely nonzero coordinate module. This fixes the shape distinction through the construction itself, independently of any assumed character table.

The new exact filter dictionary in `CertificateTableaux.lean` has the required mathematical mechanism. Its neighbor checks imply full monotonicity only after proving order-convexity of the skew support; arbitrary supports would not suffice. It identifies the unchanged `skewBoxes` support with the actual difference of `ofRowLens` diagrams, proves generic duplicate-freeness of both skew boxes and the enumerated tableaux, and characterizes membership in the existing enumerator by an increasing inverse numbering.

One remaining normalization obligation in that dictionary is substantive enough to state explicitly: `ofRowLens` is not injective on arbitrary sorted lists with trailing zeros, whereas `prefixShape` removes zero rows. Equality of actual diagrams must therefore be converted to equality of certificate shape lists using their positive-part/canonical-shape hypotheses. The existing certificate metadata supplies those hypotheses for the twenty rows. Sortedness alone is insufficient for that conversion.

The degree distinction should not create unnecessary work: in the literal requested inequality and the four already explicit numerical `PateInterfaces`, the outer irreducible degree cancels from central averaging, and the positive prefix degree cancels from each witness inequality. A numerical hook-length theorem is therefore not an additional logical prerequisite for that literal conclusion. It would be required only if a further theorem explicitly identifies the normalization constants with actual character degrees. Actual cardinalities may still be useful for a chosen completeness proof of the Young family, which is a different obligation.

## 15. Actual categorical characters and the list/numbering inverse

`YoungFDRep.lean` now independently compiles. It supplies the missing categorical interface, rather than assuming categorical simplicity: it proves the necessary fullness and monomorphism preservation of the finite-dimensional forgetful functor, transports the actual simple group-algebra module through the representation/module equivalence, and reflects simplicity back to `FDRep`. Categorical isomorphism of two constructed modules is equivalent to equality of their Young diagrams by the proved intertwiner obstruction. The resulting character orthogonality theorem is therefore about the actual constructed characters, with a genuine shape delta and no simplicity or orthogonality premise left to supply.

The completed `CentralProjectorAction.lean` independently compiles, including `character_convolution`. The convolution follows from the actual self-projector identity, multiplication by the represented group element, trace linearity, and inversion reindexing. Its normalization is `|G|/dim(V)` on the convolution side and `dim(V)/|G|` in the projector. The result does not assume completeness of the family of Young modules. The unused-section-variable warnings do not affect the theorem statements or proofs.

The inspected `CertificateSkewEquiv.lean` constructs explicit inverse maps between the existing enumerated box lists and the genuine skew standard numberings. The forward map composes the support equivalence, the inverse list numbering, and a proved cardinality cast. The backward map lists the inverse numbering in label order. Both inverse laws, the exact `getD` entry equality, and the content equality are proved. Sortedness and `contains=true` suffice for this support-level equivalence; they do not yet justify equality of literal canonical prefix shape lists.

The next projector application must respect one remaining representation distinction: a skew multiplicity space is generally reducible, and its first content operator need not be zero or scalar. The straight-shape irreducibility proof cannot be reused on that space. The `mu` projector should instead be identified using the straight-shape decomposition at the full intermediate prefix size, then restricted to the selected `eta` block. That procedure yields the prefix selector without an unjustified irreducibility hypothesis on the skew action.

Independent compilation subsequently passed for `CertificateSkewEquiv.lean` and `PrefixDecomposition.lean`. The latter proves every standard tableau has a unique actual Young prefix diagram of every admissible size; it closes coverage without assuming an enumerated list of possible prefix shapes. A fixed-tail injection of that prefix module can be used to identify the central projector on each source basis vector, using the genuine simple-module selector theorem.

For final coverage over all 135 outer shapes, the `contains=false` case must also be represented: the certificate list is empty, and the actual prefix projector must be zero. Converting noncontainment to absence of the actual Young prefix requires the reverse direction from diagram inclusion to list containment. For arbitrary sorted lists that direction fails because of trailing zeros. Positive canonical row lists, supplied by the actual certificate metadata, resolve precisely this issue.

Independent axiom inspection of `YoungFDRep.char_orthonormal`, `CentralProjectorAction.projector_eq`, `CentralProjectorAction.character_convolution`, and `CertificateSkewEquiv.certificateEquiv` returned only `propext`, `Classical.choice`, and `Quot.sound`.

## 16. Exact tail swaps and the cyclic trace reduction

`CertificateSkewAction.lean` independently compiles. It proves that the executable `swapAdjacent` on the unchanged box list is exactly composition of the inverse numbering with the corresponding finite-index swap. The test for the swapped list to pass `standard` is equivalent to incomparability of the two consecutive cells. This handles every untouched coordinate as well as both swapped positions, so it does not merely check a few small tableau cases. The actual full-tableau tail action and intermediate-prefix selector still have to be carried through this dictionary.

`WitnessTraceReduction.lean` independently compiles. The sandwich trace reduces to `trace(Q B P F)` using only `Q²=Q`, `B²=B`, and `BQ=QB`. No commutation of the pair-swap `F` with the intermediate projector is assumed. The same module proves that the trace of an identity tensor a local matrix is the actual prefix basis cardinality times the local trace. Instantiating these identities still requires the real representation/projector factors; the generic formulas alone do not establish the desired twenty trace identities.

The completed `PrefixRepresentation.lean` independently compiles after its owner corrected the singleton helper's dependent-type elaboration. It extends the prefix-generator theorem to the actual embedded symmetric group using the proved symmetric-system induction. Its embedding fixes labels outside the prefix, its cardinal casts preserve the actual adjacent indices, and its scalar-extension theorem gives exact complex basis coefficients with a fixed skew coordinate. Source review found no normalization or coverage defect.

The completed `PrefixProjector.lean` independently compiles after its owner resolved the reported local elaboration obligations. It uses this full-group basis formula to reduce the actual embedded central character sum to the genuine simple-module projector. Its final selector theorem chooses each source tableau's actual `initialDiagram`, so it covers the full ambient basis without assuming the requested `eta` is contained in `nu`. No diagonal-selector, branching-character, or skew-irreducibility premise is used to establish the endpoint.

## 17. Actual prefix projectors and canonical selectors now checked

Independent compilation passed `PrefixProjector.lean`, `TensorYoungProjectors.lean`, and `CertificatePrefixShape.lean`. The first now proves the required actual ordinary character-projector identification on the full standard-tableau module. The tensor module instantiates the established projector formula with the actual Young character and actual tableau dimension; permutation-matrix multiplication and conjugate-transpose identities are proved in the same coordinate convention as `TensorGram`. Thus its positivity, Hermitian, and idempotence conclusions are about the actual tensor-model character projectors, rather than matrices whose character identities remain assumptions.

The canonical selector dictionary now also handles both cautions raised in this audit. `prefixShape_eq_iff_initialDiagram` identifies literal certificate prefix-shape equality with equality of the actual intermediate Young diagram, using explicit positivity of the canonical `eta` and `mu` row lists. `contains_iff_diagram_le` supplies the converse needed for the complementary noncontainment case, using explicit positivity of the `eta` rows. Its list length argument tests the missing first-column cell, so trailing-zero ambiguity is not silently ignored.

The updated `swapAdjacent_mem_tableaux_iff` identifies membership of the executable swapped list in the unchanged enumerator with standardness of the actual skew numbering. It proves the required support permutation as well as the monotonicity test. No incomplete search or list-order assumption is used.

Independent axiom inspection of `PrefixProjector.projector_eq_initialSelector` and all three actual tensor-projector endpoints returned only `propext`, `Classical.choice`, and `Quot.sound`. The exact remaining trace obligation is the tail-action intertwining and its assembly with the already proved selector dictionary and cyclic/multiplicity trace formulas. The complete twenty-row ordinary trace identity is not yet asserted by this audit.

## 18. Actual suffix coefficients now checked

The final `SuffixAction.lean` independently compiles. It proves the actual suffix adjacent permutation acts by the evaluator's exact seminormal matrix on the skew factor and by the identity on the inner standard-tableau factor. The tail index is `eta.card+i`, and the proof that it is an actual ambient adjacent-generator index uses the strict upper bound on `j=i+1`; there is no off-by-one cast assumption.

The stronger `generator_basis` theorem controls every ambient target, including those outside the selected prefix block. It therefore proves invariance needed for products and rules out hidden excursions through unrepresented coordinates. `generator_glued_basis` has the exact inner-tableau Kronecker delta. `representation_glued_basis` transports these coefficients to the actual representation over any characteristic-zero field, including `C`.

The source-to-target conversion is explicit. A swap reverses the axial gap, so the row-form coefficient `1-1/d_target` equals the evaluator's `1+1/d_source`. A valid target equal to the swapped source implies the actual skew swap is allowed. The proof also rules out a fixed allowed swap, so diagonal and off-diagonal contributions are not inadvertently merged. There is no skew irreducibility or zero initial-content hypothesis.

Independent axiom inspection of `SuffixAction.representation_glued_basis`, `SuffixAction.generator_basis`, `CertificatePrefixShape.prefixShape_eq_iff_initialDiagram`, and `CertificatePrefixShape.contains_iff_diagram_le` returned only the three standard axioms. The remaining integration is now composition into the exact two certificate words, assembly with the actual prefix selectors, and the full twenty-row trace statement, including zero blocks.

`DiagramCardinality.lean` independently compiles and proves diagram cardinality equals the sum of the input row lengths by a disjoint row/shifted-tail induction. This is a structural set-cardinality theorem, not a numerical recomputation. The inspected `WitnessShapes.lean` extracts shape sizes, positive canonical rows, containment, and signs directly from the already certified metadata, then forms actual diagrams and proves the needed size and inclusion statements. Its hypotheses are membership in the established twenty rows and the semantic partition-of-fourteen predicate.

During trace assembly, cyclicity must not be applied pointwise to local diagonals. Although `trace(F Q B)=trace(Q B F)`, generally `(F B)ss` need not equal `(B F)ss`. Either retain the evaluator's order `Q B F` by moving only the compatible prefix projector, or use cyclicity at the level of the full local trace. No commutation of `Q` with the pair-swap is justified.

## 19. Economical remaining tensor transport after the actual trace identity

This section is a read-only analysis of the smallest analytic integration; these are proposed remaining lemmas, not assertions that their Lean implementations already exist.

Let `J=((O ⊕ L) ⊕ L)`, let `psi : J ≃ Fin 14` be the already defined `split14one` or `split14two`, and let `C=((O→D)×(L→D))×(L→D)`. Compose precomposition by `psi` with `blockCoordinates` to obtain an exact configuration equivalence `e : (Fin 14→D) ≃ C`. For vectors use `R x(c)=x(e.symm c)`; for matrices use `M'=Matrix.reindexAlgEquiv ℂ ℂ e M`. Mathlib already supplies the algebra equivalence, and `Matrix.submatrix_mulVec_equiv` supplies the multiplication-by-vector transport. `Equiv.sum_comp` proves inner-product preservation. Thus products, sums, scalar multiples, adjoints, and expectations can be transported without introducing an abstract tensor-product or group-algebra model.

Only four permutation localization identities are needed after this reindexing:

1. A permutation supported on `O` becomes `outsideLift` of its local tensor permutation matrix.
2. A permutation supported on `O ⊕ L` becomes `leftLift` of its tensor permutation matrix after the two-block coordinate regrouping.
3. A permutation supported on `R` becomes `rightLift` of its local tensor permutation matrix.
4. The actual pair-swap becomes `pairSwapMatrix`.

Each identity follows entrywise from the existing formula `tensorPermMatrix g a b = if a ∘ g = b then 1 else 0`, by splitting the coordinate function into its sum components. This direction matches the existing left-action convention. The position permutation carried from `J` to `Fin 14` is `psi ∘ g ∘ psi⁻¹`; the configuration pullback reverses none of the matrix-word products. The existing prefix embedding must be proved equal to this supported permutation, rather than inferred from matching names.

Linearity then transports the actual central character sums, retaining the same actual degree and subgroup factorial. Take the local `P` to be the actual `eta` tensor projector. Take `Q` to be the actual `mu` tensor projector reindexed into the first two configuration factors. For `k=1`, take `B=1`; for `k=2`, take `B=(1+epsilon U_(01))/2` on the final two positions. The actual transposition is self-inverse and unitary, so `B` is Hermitian; `epsilon=±1` additionally proves `B²=B` for trace reduction. Matrix reindexing preserves the already proved Hermitian and idempotence identities of `P` and `Q`.

The exact operator equality after reindexing is then the existing `projectedSwapWitness P Q B`. Applying `pureTensor_projectedSwap_nonneg`, plus pure-tensor and inner-product transport, proves nonnegative expectation of the actual witness on every pure tensor. This uses only the already discharged facts `Pᴴ=P`, `P²=P`, `Qᴴ=Q`, and `Bᴴ=B`. The analytic theorem needs no commutation of `P` with `Q`, no positive-semidefiniteness assertion about the full witness, and no invariant inner product on the rational Young-coordinate matrices. In particular, none of the desired witness positivity is assumed in the transport.

The two actual permutation-word identities remain small finite-position equalities: for `k=1` the word is `(12 13)`; for `k=2`, `[1,0,2,1]` on positions `10,11,12,13` is `(10 12)(11 13)`, and `[2,1,0,2,1]` is `(12 13)` times that swap. These may be proved by extensionality on the fourteen positions; there is no reason to enumerate the group or tensor basis.

To connect this to the already proved central-averaging module, broad group-algebra development is also unnecessary. Define real coefficient functions on `S14`: push each subgroup's actual real character coefficient forward by its embedding, take the identity/transposition combination for `B`, and the delta function at the pair-swap. Compose the six factors with the existing finite convolution. `CharacterProjector.weightedOperator_mul` proves its realization is the actual `Q B P tau B Q` in every representation. `weightedOperator_trace` then turns the actual Young trace identity into the required character pairing. This is a finite-sum calculation with explicit coefficients, not a new representation-theory premise.

Finally, conjugation preserves the required pure-tensor testing condition by `tensorPerm_pureTensor`: applying any position permutation merely permutes the vector factors. Expectation transport therefore supplies every conjugated nonnegativity premise in `CentralAveraging.character_weighted_pairings_nonneg`. The separate class-function spanning obligation can use the actual orthogonal Young characters and the conjugacy-class count; neither this Fourier step nor the operator transport should be replaced by an assumed ordinary-immanant bridge.

## 20. Actual word transport, selected traces, and completeness now checked

Independent compilation passed the final `SuffixWord.lean`, `SelectedTrace.lean`, `PrefixProjectorAlgebra.lean`, and corrected `PrefixTrace.lean`. `SuffixWord` composes actual adjacent permutations by the same ordered list product as the unchanged evaluator. The matrix transport is a proved ring homomorphism through the genuine basis equivalence; multiplicativity is not assumed for an arbitrary coordinate restriction. Full vector intertwining proves products preserve the prefix block. Its specialized `certificate_representation_word_matrix` supplies the concrete list-to-numbering equivalence and encoding law, leaving no basis-identification hypothesis at that endpoint.

`SelectedTrace.trace_two_projectors` combines the actual two central prefix projectors with the exact intermediate-list selector. The relation between their sizes is explicitly `m+1+k=q+1`. Its remaining `hdiag` premise concerns the diagonal of a supplied tail operator; the actual word theorem now supplies that information for the prescribed words. This is a local operator interface, not an ordinary-immanant or witness-positivity premise. `PrefixProjectorAlgebra` proves commutation for nested actual prefix projectors and for actual transpositions supported outside a prefix. It does not assert the unavailable commutation of the intermediate projector with the pair-swap.

Independent compilation also passed the completed `YoungCharacterCompleteness.lean`. The structural chain is exact: the genuine full cycle partition, including fixed-point parts equal to one, injects conjugacy classes into the established exhaustive canonical shape list; the actual 135 Young characters are orthogonal; descending them to the conjugacy quotient gives a linearly independent family in a space of dimension at most 135; dimension equality makes them a basis. Canonical row-list recovery proves that equality of the actual diagrams is equality of the shape indices. No hook-length formula or character-table identification is a premise.

The quotient orientation and real normalization have been checked explicitly. `IsConj` uses `a*g*a⁻¹`; the older `IsClassFunction` convention is `a⁻¹*g*a`, handled by substituting `a⁻¹`. Actual character inversion invariance and rational-to-real scalar extension convert the complex orthogonality identity to `sum_g chi_p(g) chi_q(g) = |S14| delta_pq`. The old central-averaging character assumptions are all discharged by this actual family.

Independent axiom inspection of `SuffixWord.certificate_representation_word_matrix`, `SuffixWord.word_intertwines`, `YoungCharacterCompleteness.character14_span`, `character14_centralCoefficient_expansion`, and `character14_weighted_pairings_nonneg` returned only `propext`, `Classical.choice`, and `Quot.sound`.

The final scope check remains essential: `SuffixWord.permutationWord` is parameterized by the outer diagram and its cardinality proof. The concrete word-equals-pair-swap identities must show that every outer module evaluates the same actual permutation of fourteen positions. A family of shape-dependent group elements, even with individually correct traces, would not define the single witness coefficient function needed for central averaging. After this identification, the remaining ordinary trace assembly can use the already proved selected trace, signed word sum, cyclic reduction, and noncontainment-zero facts.

## 21. Requested actual ordinary trace endpoint independently verified

The completed `WitnessTrace.lean` independently compiles. Its main theorem has exactly the following scope:

```
∀ (w : Certificate.Witness) (hw : w ∈ Certificate.rows)
  (p : Certificate.Shape) (hp : Certificate.IsPartition14 p),
  LinearMap.trace ℂ (WitnessOperators.Space p hp)
    (WitnessOperators.witness w hw p hp)
  = (YoungProjectors.degree (WitnessShapes.etaDiagram w hw) : ℂ)
      * (Certificate.computedCoeff w p : ℂ)
```

The left side is the actual `Q B P F B Q` sandwich in the constructed ordinary Young representation of `S14`. The prefix operators are actual inverse-character sums with their actual degree/subgroup-cardinality normalization. `F` and the right transposition are fixed literal permutations of fourteen positions, independent of the outer partition. The right side is the unchanged original rational evaluator, cast to `C`, with the actual inner-tableau dimension as its only multiplicity.

The two branches cover the full domain. In the containment case, the proved metadata supplies `k=1` or `k=2`; the exact word identifications feed the already checked selected-word trace. The two-contraction branch has precisely `f_eta/2` times the unsigned word trace plus the original sign times the signed word trace. In the noncontainment case, the actual prefix projector and the unchanged evaluator both vanish. There is no positivity assumption, numerical trace assumption, assumed branching rule, or uninstantiated basis equivalence.

Independent `#print axioms` on `LiebBridge.Young.WitnessTrace.trace_witness_eq_computedCoeff` returned only `propext`, `Classical.choice`, and `Quot.sound`. Independent inspection of the elaborated theorem type confirmed that the four displayed inputs are its entire hypothesis list. The warnings from redundant trace-reassociation tactics are nonmathematical linter warnings.

`WitnessCoefficients.lean` also independently compiles. It defines one real coefficient function on `S14`, independent of the outer partition, by the six convolutions in the order `Q B P F B Q`. Prefix weights use inverse actual real characters and actual degree divided by the smaller symmetric-group cardinality. The right filter has the exact sign and factor `1/2`. `endEvaluation_witnessCoeff` evaluates that same coefficient function to the actual sandwich in every Young module, and `trace_witness_eq_pairing` identifies its ordinary-character pairing with the actual trace, with no extra degree or group-cardinality factor.

`TensorLocalization.lean` independently compiles the four supported-permutation localization identities and exact vector/matrix/expectation transport. Its `pureTensor_nonneg_of_transport` correctly retains a concrete matrix-equality input: that equality still has to be instantiated for the actual witness coefficients, with the actual local character projectors and fixed pair-swap. Thus the newly closed ordinary trace identification must be distinguished from completion of the entire analytic/immanant theorem. The latter also needs the coefficient/Gram-expectation link and application of the existing exact arithmetic and four historical Pate inputs.
