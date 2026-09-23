# Independent adversarial audit of the Lean formalization

Audit date: 2026-09-11. Toolchain: Lean 4.19.0, local mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`.

**Verdict: substantial analytic and finite computational components have been formalized, but the unconditional order-fourteen ordinary-immanant bridge has not been proved in Lean.** The remaining issue is the representation-theoretic realization that connects the finite tableau evaluator to the actual symmetric-group witness operators and ordinary irreducible characters. This audit must not be cited as an “all complete” formalization verdict.

This is a source and theorem-boundary audit by the separate audit agent. The contraction module was also built independently and its key theorem axioms inspected. Other agents continued updating their modules while this audit was prepared; the final whole-project build and final axiom inventory should be used to establish the delivered build status.

## 1. Analytic contraction and PSD coverage

`Contraction.lean` proves the exact finite complex identity

`<a tensor b, swap (a tensor b)> = sum_o star(c_o) * c_o`,

where `c_o = sum_l star(b_l) * a_(o,l)`. Conjugation is on the first inner-product argument. This is a sum of squared absolute values, without a missing dimension factor.

The main theorem `LiebBridge.projectedSwapWitness_nonneg` concerns an actual matrix `Q B P swap B Q`, with all three local extensions defined by Kronecker products. Its hypotheses are `Pᴴ=P`, `P*P=P`, `Qᴴ=Q`, and `Bᴴ=B`. The proof explicitly derives

`Q B P swap B Q = (P B Q)ᴴ swap (P B Q)`

and the factorization of the local filter across the relevant bipartition. It proves the required expectation inequality; witness positivity is not a hypothesis. The first-side array after filtering is arbitrary, so no unjustified assumption that `Q` preserves full decomposability is made. The proof is stronger than required: commutation of `P` with `Q` is unnecessary here. Support on `O` supplies the actual commutation of `P` with the pair swap.

`lake build Bridge.Contraction` succeeded. The inspected axioms of the core contraction identity, generic sandwich positivity, sandwich algebra, and concrete witness theorem are precisely `[propext, Classical.choice, Quot.sound]`; there is no `sorryAx` or custom axiom in these declarations.

`TensorGram.lean` defines genuine coordinate tensors, their pure tensors, tensor-factor permutations, and the complex Gram matrix. Its Gram realization theorem invokes mathlib's PSD factorization `A = Bᴴ * B` and takes the columns of `B`. Singular matrices, zero vectors, arbitrary complex phases, and zero diagonal entries are covered. No invertibility, rank reduction, or normalization of matrix entries is introduced.

`TensorWitness.lean` explicitly regroups the coordinates using a finite equivalence and proves preservation of the coordinate inner product and factorization of a pure tensor across the required bipartition. The `12+1+1` and `10+2+2` site sets are explicitly equivalent to `Fin 14`. Its local matrices remain parameters: the module does not yet identify them with the prescribed central symmetric-group projectors.

## 2. Permutation, inverse, and character conventions

The conventions in `TensorGram.lean` and `Immanant.lean` are mutually consistent:

- `tensorPerm σ x` is `c ↦ x (c ∘ σ)`, giving a left representation.
- On pure factors it sends `v_i` to `v_(σ⁻¹ i)`.
- Its expectation is therefore `prod_i A_(i,σ⁻¹ i)`.
- `complexImmanant χ A` uses the conventional `sum_σ χ(σ) prod_i A_(i,σ i)`.
- `characterOperator` uses `χ(σ⁻¹)`. Reindexing the finite sum by inversion yields exactly `degree / |S_I|` times `complexImmanant χ A`.

The Gram-operator identity does not assume positivity or an irreducible character. That generality is legitimate, and its documentation correctly states the limitation. The real-valued immanant is defined as the real part; the separate theorem `complexImmanant_star` proves reality under Hermiticity and a real inversion-invariant supplied character. No claim that an arbitrary supplied function is an ordinary character is made.

One interface distinction must remain explicit: `CharacterProjector.characterCoefficient` uses `χ(g)`, whereas `Immanant.characterOperator` uses `χ(g⁻¹)`. These agree for the ordinary real symmetric-group characters, but the generic definitions are not identical. A concrete application needs an inversion-invariance theorem or must supply the inverse character to one interface. This is not a detected error in either generic theorem, but silently equating them would be an error.

## 3. Finite certificate data and evaluator

An independent read-only parser compared `CertificateData.lean` with `specification/exact_certificate/certificate.json`: all twenty row parameters, signs, rational weights, and stored coefficients match exactly.

The evaluator conventions match the mathematical specification:

- Boxes are zero-indexed and content is column minus row.
- The axial denominator is next-box content minus current-box content.
- Adjacent generators are zero-indexed.
- `traceWord` reverses the supplied word before acting on a column state, which implements the displayed matrix word right to left.
- The two `k=2` words `[1,0,2,1]` and `[2,1,0,2,1]` are respectively `S2 S1 S3 S2` and `S3 S2 S1 S3 S2`.
- The initial tableau is selected by the intermediate shape. Since only diagonal return paths contribute to the trace, this agrees with placing the intermediate-shape projector on the left of the matrix word.
- The `k=2` sign term is divided by two, matching the symmetric/alternating pair projector.

`CertificateChecks.lean` checks the numerical evaluator against every stored row on the enumerated list using `decide +kernel`. `CertificateEnumeration.lean` proves both soundness and completeness of that list for positive nonincreasing partitions of fourteen, as well as absence of duplicates. This closes a real finite-coverage issue: checking a list of length 135 alone would not have proved that every partition was checked.

The rational evaluator is total, including division by zero and out-of-range list lookup. This does not invalidate any theorem about that evaluator, but semantic identification with a seminormal matrix additionally requires valid tableau lengths and nonzero axial differences. Finite metadata checks of all actual rows/tableaux would be useful safeguards; they do not substitute for the representation theorem.

`hookDegree` correctly computes the factorial divided by the hook product, and the five displayed numeric values are checked. However, `degree_4433` and the corresponding four declarations currently prove values of this arithmetic function. They do **not** prove that those numbers are dimensions or identity-character values of constructed ordinary irreducible representations. The hook-length dimension theorem remains part of the representation boundary.

`Certificate.lean` proves the exact rational/real weighted identity for an arbitrary function on shapes. Its theorem `bridge_of_witness_nonnegative` explicitly assumes all twenty witness inequalities. That is a valid arithmetic implication, and its documentation correctly identifies its scope. It must not be presented as the unconditional PSD bridge: supplying those assumptions for actual immanants is the substantive missing connection.

## 4. Generic representation-theory modules

`CentralAveraging.lean` establishes centralization and the character-weighted expansion from explicit hypotheses of conjugation invariance, orthogonality, and spanning for a supplied real character family. It also proves preservation of nonnegative conjugate pairings. The signs and cardinality factors in this generic expansion are consistent with `1/|G|` averaging. The character hypotheses and conjugate-positivity hypothesis remain visible theorem arguments; no hidden bridge axiom was found.

`CharacterProjector.lean` proves that inverse-compatible convolution idempotents give Hermitian idempotent, hence PSD, operators under a unitary matrix representation. The actual character convolution formula is explicitly a premise. This is stronger than merely assuming pointwise character orthogonality, and the source correctly distinguishes the two. Instantiation with the ordinary subgroup characters remains to be proved.

`Normalization.lean` proves the exact numerical equivalence of the unnormalized bridge with the convex normalized inequality and the transfer from precisely four lower PDC assumptions. It does not assert that the arbitrary shape-indexed function is an immanant or that the bridge has been obtained. The degree balance and convex weights are numerically correct. An eventual PDC theorem still needs the named quantities identified with ordinary immanants and the four external Pate results supplied in the stated complex PSD domain.

## 5. Exact remaining blocker

The central missing realization is, for every row `w` and ordinary partition `ν`,

`Tr(ρ_ν(W_w)) = f_η * computedCoeff w ν`,

where `W_w` is the concrete tensor/group-algebra operator built from the actual central projectors and pair swap. At present, the ordinary representations `ρ_ν` and their identification with the small tableau model have not been supplied.

Closing this requires a proof, rather than a renamed hypothesis, of the following linked facts (or an alternative actual group-algebra derivation):

1. The supplied shape-indexed characters are the complete ordinary irreducible character family of `S14`, with the required reality, inverse invariance, orthogonality, and class-function spanning.
2. The projectors for the indicated embedded smaller symmetric groups have the actual normalized character formulas and are identified with the local matrices in `TensorWitness`.
3. Restriction to the `η`-isotype gives `f_η` identical multiplicity copies, the intermediate `μ` projector selects exactly the asserted tableau paths, and the adjacent permutations act by the specified seminormal matrices.
4. The pair-swap word and pair-sign projector have those same actions, with the asserted multiplication orientation. The idempotence of `Q` and `B` and their required commutations must be supplied for the cyclic-trace reduction; these assumptions are not needed by the stronger analytic contraction theorem and therefore cannot be inferred from its hypotheses.
5. The central averaging and Gram identities are instantiated with these concrete characters and operators, yielding each actual immanant inequality from the already-proved analytic expectation inequality.

Verifying Coxeter relations for some small rational matrices alone would not settle items 1–3: it would not identify their ordinary-character labels, establish the correct branching multiplicities, or prove completeness. Likewise, naming the hook quotient `degree` does not prove its representation dimension.

The scalar factor `f_η` is positive and can eventually be divided out, but it cannot be omitted before proving the trace realization. The `f_ν` in the central projection and the `1/14!` normalization must also cancel through the genuine character expansion, not through an unproved naming convention.

## 6. Additional concrete steps that can be closed independently

The following are bounded useful additions, while keeping the principal blocker explicit:

- Check all actual row shape/size/sign metadata and nonzero axial denominators in the kernel.
- State the aggregate computed coefficient identity for every `IsPartition14`, combining the evaluator checks with partition completeness.
- Prove the explicit inversion-invariant identification between the two character-operator interfaces.
- Prove tensor permutation preservation of `tensorInner` by the coordinate equivalence `c ↦ c ∘ σ`, then use it with preservation of pure tensors to discharge geometric conjugate positivity once the local witness is instantiated.

These additions strengthen the verified boundary; none alone establishes the ordinary `S14` trace realization.

**Permitted final status:** the universal local witness positivity, exact finite coefficient calculations, partition coverage, Gram realization, and conditional arithmetic/character lemmas are formalized to their displayed hypotheses. **Not permitted:** claiming a complete Lean proof of the unconditional `(4,4,3,3)` bridge, or disguising the twenty required immanant inequalities as assumptions of the requested top theorem.

## Final addendum: bounded interface gaps closed

The final source review, after the additions described below, supersedes the earlier recommendations in Sections 2, 3, and 6. The parent reports that the normal final `lake build` passed. The separately requested isolated source rebuild and complete theorem-axiom audit were still being run when this addendum was written; their actual results belong in `validation/BUILD_STATUS.md` and the delivered audit logs. This addendum does not claim that an unobserved fresh internet installation or an in-progress audit has completed.

The following previously identified bounded obligations are now addressed in the Lean source:

- `Certificate.witnessMetadataCheck` verifies the two allowed values of `k`, positive nonincreasing `η` and `μ` of the required sizes, containment, and the allowed signs.
- `Certificate.tableauSafetyCheck` checks the required tableau lengths, duplicate-free tableau bases, and nonzero adjacent axial differences on every enumerated basis for every row and every order-fourteen partition. The evaluator therefore has an explicit finite check guarding the earlier total-division/default-index concern on the actual certificate data.
- Sparse-entry partition validity, distinctness, and nonzero coefficients are checked. `storedCoeff_eq_zero_of_not_partition` establishes the intended support statement.
- `Certificate.aggregateComputedIdentity` proves the weighted computed coefficient identity for every `IsPartition14`, using the already-proved enumerator completeness and evaluator-to-stored-row identity.
- `TensorGram.tensorInner_perm` proves preservation of the actual coordinate inner product under tensor permutations; `tensorInner_perm_left` gives the corresponding inverse-adjoint identity.
- `ProjectorConvention.characterOperator_matrix_eq_characterProjector` explicitly proves agreement of the matrix and tensor operator conventions under the stated inversion-invariance hypothesis. The earlier `χ(g)` versus `χ(g⁻¹)` interface is no longer left as an unstated identification.
- The hook-square-sum and row hook-degree cancellation are checked as additional arithmetic consistency identities. Their documentation correctly says that these do not identify the hook quotients with representation dimensions.

I reviewed `PateInterfaces.lean`. It introduces four separately named propositions for the normalized `(6,5,3)`, `(6,4,4)`, `(5,5,4)`, and `(5,3,3,3)` bounds on every complex `14 × 14` PSD matrix. The character family is visibly a parameter. These are definitions of historical-theorem interfaces, not assertions that arbitrary supplied functions are ordinary characters, and none is introduced as a Lean axiom. The theorem `pdc4433_of_bridge_and_four_pate` correctly retains `Bridge4433 χ` as an explicit additional assumption. Thus it is a valid conditional arithmetic application, but not the requested theorem depending only on the four historical results.

I also reviewed the final README. It leads with an explicit incomplete status, identifies `Bridge4433` as a proposition definition rather than a proof, distinguishes the compiled analytic and finite computational components from ordinary representation realization, and warns against presenting the conditional transfer theorem as the completed result. No mathematical completeness overclaim was found. The final packaging should include the build-status file and audit logs referenced by that README.

**Final independent assessment:** the bounded computational, convention, and tensor-geometric gaps identified in the first audit have been closed. The decisive outstanding obligation remains the actual ordinary-character/degree and branching trace realization described in Section 5. In particular, neither `Tr(ρ_ν(W_j)) = f_η * computedCoeff(j,ν)` nor the identification of the checked hook quotients with the required ordinary degrees has been established for constructed ordinary representations in this project. There is still no unconditional Lean proof of the all-complex-PSD `(4,4,3,3)` bridge. The final deliverable may accurately claim a compiled, assumption-explicit partial formalization with the above analytic and finite components, and must retain this substantive limitation.
