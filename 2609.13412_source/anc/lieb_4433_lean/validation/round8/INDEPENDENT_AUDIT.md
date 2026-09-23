# Independent audit of the final ordinary-immanant integration

Date: 2026-09-11. This report concerns the current round-eight integration only. The audit is read-only with respect to every mathematical Lean source file; its only Lean addition is the inspection file `validation/round8/FinalAxiomAudit.lean`. Its scope is the actual tensor witness, the same real coefficient function used by the proved Young trace, complete Hermitian PSD coverage, and the final theorem assumptions and axiom inventory.

## Current verified mathematical boundary

The preserved endpoint `WitnessTrace.trace_witness_eq_computedCoeff` states the actual Young-module sandwich trace for every certified witness and every partition of fourteen. It has no character, branching, matrix-identification, or positivity premise. The coefficient construction evaluates one fixed real function on `S14` to that same sandwich in every outer Young module. The actual Young characters are already proved irreducible, pairwise inequivalent, and complete as class functions.

The round-seven dimension-transport blocker is now closed. Independent source compilation of the complete `TensorWitnessPositivity.lean` succeeds. Both concrete site decompositions instantiate the actual projectors and the explicit contraction theorem, giving the coefficient-defined witness's nonnegative expectation on every complex pure tensor. The built `FinalBridge` endpoints derive every PSD row inequality and the complete ordinary matrix bridge. Direct kernel-axiom inspection of those endpoints succeeds. The only external mathematical inputs of `pdc4433_of_four_pate` are the four separately named historical Pate statements for the internally constructed actual ordinary characters.

## Index transport and the local positivity mechanism

`TensorFiniteLocalization.splitSites a b` identifies the site blocks with the ordered indices `0,...,a-1`, `a,...,a+b-1`, and `a+b,...,a+2b-1`. Its prefix embeddings use the genuine `Fin.castLEEmb` inclusion and fix every complementary position. The `outside_prefix` and `left_prefix` theorems explicitly prove this identification, including the conjugation direction; it is not inferred from matching dimensions.

`localCoordinates` pulls a function on `Fin(a+b)` back to the sum of the first two site blocks. Both `localMatrix` and `regroupLeftMatrix` are actual matrix reindexing algebra equivalences. Thus their multiplication order is unchanged. The local `leftProjector` must be this reindexed actual Young tensor projector, transported across the stated equality `m+1=a+b`; a general matrix of the same dimension would not suffice.

The concrete permutation identities have the correct orientation:

- the `12+1+1` block swap is `(12 13)`;
- the `10+2+2` block swap is the fixed word `(11 12)(10 11)(12 13)(11 12)`, hence `(10 12)(11 13)`;
- the right-block transposition in the latter split is `(12 13)`.

These identities are extensional equalities of actual permutations on fourteen positions. They do not enumerate `S14` or the tensor basis.

The existing contraction theorem applies to the exact localized operator `Q B P swap B Q`. It requires `P` to be Hermitian and idempotent and `Q,B` to be Hermitian. It does not require `P` and `Q` to commute, does not assume positivity of the full witness, and does not use a Hilbert-space structure on the rational Young-coordinate representation. The proof is an explicit sum of squared contractions after a local filter. For `k=2`, the local right filter is exactly `(I+sign*U_(01))/2`; the real sign and self-inverse unitary transposition make it Hermitian. The two `B` factors and the eventual single trace factor `1/2` must be preserved by the integration.

## Coefficient and inverse conventions

`WitnessCoefficients.witnessCoeff` has no outer-partition argument. It is the convolution of six real functions in the order `Q B P F B Q`. Prefix coefficients use the inverse actual real character with normalization `actual degree / subgroup cardinality`. The same function is evaluated in both the tensor representation and every actual Young representation. No global-factorial normalization is substituted for a subgroup factorial.

`TensorPairing.evaluation_pairing` identifies its real operator expectation with the old real coefficient pairing. The tensor action is `U_g x(c)=x(c∘g)`, so the pure Gram monomial has index `g⁻¹`. `TensorPairing.character_pairing` explicitly reindexes by inversion and uses actual character inversion invariance; it does not silently replace that monomial by the one with index `g`.

`TensorPairing.moment_conjugate` has the correct direction:

\[
m_v(a g a^{-1})=m_{v\circ a}(g).
\]

Indeed, moving the outer permutation across the inner product applies `U_(a^-1)` to the pure tensor, whose factors are `v(a i)`. Thus every conjugated test required by the central-averaging theorem is another pure-tensor test of the same coefficient function.

There are two legitimate final assembly routes. One can use `realWitnessForm_nonneg` with `m=TensorPairing.moment v` and identify each actual character pairing by `character_pairing`. Alternatively, `ordinaryWitnessForm_nonneg` uses `realMonomial A(g)=Re(prod_i A_i,g(i))`; its equality with the tensor moment is not definitional and requires the explicit Hermitian conjugation/real-part identity. Merely rewriting these two functions as equal would skip an inverse-convention obligation.

`WitnessCoefficientPositivity.coefficient_pairing` already supplies the actual trace theorem internally. The final `realWitnessForm_nonneg` retains only the explicit conjugated-positivity hypothesis, to be discharged by the concrete tensor theorem. Its multiplication by the prefix degree is removed using the proved positive actual tableau cardinality. The historical helper with a trace argument is not evidence that the final endpoint retains such an assumption.

## Full PSD coverage and final theorem assumptions

The final bridge takes only `A : Matrix (Fin 14) (Fin 14) ℂ` and `A.PosSemidef`. The existing `exists_gram_of_posSemidef` factors every such matrix into fourteen complex Gram vectors in the same dimension. It assumes neither nonsingularity nor positive diagonal entries and does not reduce to real matrices or any rank stratum. The proved tensor positivity theorem applies to arbitrary vector factors, with no normalization or independence condition. These two facts together cover every Hermitian PSD matrix, including zero and singular matrices.

The complete ordinary bridge instantiates the internally defined actual `OrdinaryImmanants.character`. Inspection of the elaborated final theorem types confirms that no trace, branching, character, class-function-span, tensor-localization, Gram-factorization, or witness-positivity hypothesis remains. The normalized PDC theorem exposes exactly `Pate653`, `Pate644`, `Pate554`, and `Pate5333`, each instantiated with that same actual character family, besides the matrix and its PSD hypothesis. These four historical facts are theorem arguments; they have not been declared as Lean axioms or proved in this development.

The inspected kernel axiom inventory of both the final bridge and the normalized PDC endpoint is exactly `propext`, `Classical.choice`, and `Quot.sound`. The actual tensor positivity, Young trace identification, coefficient averaging, and Gram factorization endpoints have the same inventory. The certificate's finite metadata checks and some arithmetic checks use fewer axioms. No `sorryAx`, new project axiom, or native-evaluation trust axiom appears.

The formal conclusion uses the literal denominator `12012`, and the four supplied Pate statements use the literal denominators `15015`, `9009`, `6006`, and `15015`. The resulting convex weights are positive and sum to one. A separate theorem identifying every actual tableau cardinality with a hook quotient is not needed for this literal inequality: actual representation dimensions are used in the trace and character-projection formulas and cancel before the displayed numerical normalization. This development should not be represented as a proof of a general hook-length formula or of a separately stated `dim V4433 = 12012` theorem. That qualification does not weaken the explicit target inequality.

The immanants and permanent are represented by their real values. `OrdinaryImmanants.complexImmanant_real` proves that the ordinary complex immanant is fixed by conjugation on every Hermitian matrix; the same general immanant-reality theorem applies to the constant-one character defining the permanent. Thus taking real parts does not replace the requested Hermitian-matrix quantities with different ones.

## Independent checks completed during this round

Independent source compilation passed `TensorFiniteLocalization.lean`, `TensorPairing.lean`, and `WitnessCoefficientPositivity.lean`. Direct axiom inspection of the preserved actual witness trace, the unconditional coefficient pairing, the witness-form central-averaging implication, and the tensor evaluation/conjugation/character-pairing identities returned only `propext`, `Classical.choice`, and `Quot.sound`.

`FinalBridge.lean` passes source-level mathematical review. Its `classPairing_moment` uses actual character inversion invariance, including the non-partition zero fallback. `gram_witness_nonnegative` applies the same coefficient's concrete tensor expectation to all conjugated moments. `psd_witness_nonnegative` uses the existing Gram factorization directly, with no additional restrictions. `matrix_bridge` supplies all twenty row inequalities to the unchanged exact certificate. The final theorem fixes `OrdinaryImmanants.character` internally and names only the four Pate facts as external mathematical inputs. The compiled endpoints have passed the independent axiom and theorem-type inspection described above.

The repaired dimension transports pass mathematical source review and independent compilation. `cast_hermitian` proves preservation of an actual Hermitian matrix under equality of its finite index size; `leftProjector_hermitian` applies it to the two casts already present in the preserved definition. `left_prefixTensor` locally generalizes the total input dimension and its arbitrary coefficient function, applies the exact localization theorem after equality elimination, and reconciles the casts with `cast_cast`. This does not replace the projector, change its normalization, or introduce a character-identification premise.

The concrete cases pass mathematical source review and independent full-file compilation. The `k=1` case uses the actual twelve-site `eta` projector, the actual thirteen-site `mu` projector, and the identity right filter. The `k=2` case uses the actual ten-site and twelve-site projectors and exactly `(I+sign*rightSwap)/2`. Each `hM` transports all six factors in order and uses the proved fixed `S14` pair/right-swap identities. The resulting `concrete_witness_nonneg` statement concerns the coefficient-defined tensor witness itself and has no localization or positivity hypothesis; only witness-row membership and arbitrary finite complex vector factors remain. The sole source-compile warning is an unused section-variable warning in the private cast helper.

The frozen final `FinalBridge.lean`, including `computed_witness_nonnegative`, independently compiled with exit code zero and no output. The build log is `validation/round8/final_bridge_independent_build.log`. The new all-partition API replaces each computed coefficient by the same certified stored coefficient and applies the proved sparse/full-sum identity; it does not change the witness form or restrict the set of partitions.

`validation/round8/FinalAxiomAudit.lean` independently compiled with exit code zero. Its complete output is saved in `validation/round8/final_axiom_audit.log`. It checks the types of all eight public final theorems and inspects thirty-two theorem axiom inventories, including actual tensor positivity, the actual Young witness trace, central coefficient pairing, all-partition certificate arithmetic, contraction, normalization, full PSD Gram coverage, and ordinary-immanant reality. Every inventory is a subset of the standard three axioms listed above. The file also prints the definitions of the four Pate interfaces, making their shapes, denominators, and complete PSD domains explicit.

This is an independent compilation of the completed source files against the available compiled dependency closure and a direct audit of the final compiled theorem bodies. The root agent's separate isolated source rebuild and complete project-theorem inventory are stronger reproducibility checks and are recorded separately; this report does not count them as independently rerun here.

## Final audit conclusion

The previous missing ordinary representation/branching/trace identity and the subsequent concrete tensor-localization blocker are both closed. The complete bridge and every computed witness inequality hold on the full complex Hermitian PSD cone. The formal dominance transfer has no remaining new mathematical obligation: it requires exactly the four historical Pate results that the task permits as prior facts. Their proofs remain outside this Lean development. There is no remaining assumption of the target PDC, the bridge, witness positivity, or an equivalent-strength replacement of those statements.
