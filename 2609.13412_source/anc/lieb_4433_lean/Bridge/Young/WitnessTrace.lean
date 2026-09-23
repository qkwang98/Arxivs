import Bridge.Young.WitnessOperators
import Bridge.Young.SelectedWordTrace

/-! Actual sandwich witness traces, with no coefficient or branching premise.
The word formulas use the same fixed S14 permutations in every Young module. -/

noncomputable section
namespace LiebBridge.Young.WitnessTrace
open scoped BigOperators Classical
open Certificate WitnessShapes WitnessOperators PrefixProjector PrefixProjectorAlgebra
  CertificateSkewEquiv SuffixWord

/-- Cyclic reduction for finite-dimensional endomorphisms, preserving the
relative order of the intermediate projector and the pair swap. -/
theorem sandwich_trace {V : Type*} [AddCommGroup V] [Module ℂ V]
    (P Q B F : Module.End ℂ V) (hQ : Q*Q=Q) (hB : B*B=B) (hBQ : B*Q=Q*B) :
    LinearMap.trace ℂ V (Q*B*P*F*B*Q) = LinearMap.trace ℂ V (Q*B*P*F) := by
  calc
    _ = LinearMap.trace ℂ V ((Q*B*P*F)*(B*Q)) := by congr 1 <;> noncomm_ring
    _ = LinearMap.trace ℂ V ((B*Q)*(Q*B*P*F)) := LinearMap.trace_mul_comm ℂ _ _
    _ = LinearMap.trace ℂ V (B*(Q*Q)*B*P*F) := by congr 1 <;> noncomm_ring
    _ = LinearMap.trace ℂ V (B*Q*B*P*F) := by rw [hQ]
    _ = LinearMap.trace ℂ V (Q*(B*B)*P*F) := by rw [hBQ]; congr 1 <;> noncomm_ring
    _ = _ := by rw [hB]

variable (w : Witness) (hw : w ∈ rows) (p : Shape) (hp : IsPartition14 p)

theorem witness_trace_reduced :
    LinearMap.trace ℂ (Space p hp) (witness w hw p hp) =
      LinearMap.trace ℂ (Space p hp)
        (etaP w hw p hp * (muQ w hw p hp * rightB w p hp * pairF w p hp)) := by
  rw [witness, sandwich_trace _ _ _ _ (muQ_idempotent w hw p hp)
    (rightB_idempotent w hw p hp) (muQ_commute_rightB w hw p hp).eq.symm]
  congr 1
  have hPB := (etaP_commute_rightB w hw p hp).eq
  have hPQ := (etaP_commute_muQ w hw p hp).eq
  calc
    _ = muQ w hw p hp * (rightB w p hp * etaP w hw p hp) * pairF w p hp := by
      noncomm_ring
    _ = muQ w hw p hp * (etaP w hw p hp * rightB w p hp) * pairF w p hp := by rw [hPB]
    _ = (muQ w hw p hp * etaP w hw p hp) * rightB w p hp * pairF w p hp := by
      noncomm_ring
    _ = _ := by rw [← hPQ]; noncomm_ring

/-- If eta does not fit inside nu, both the actual trace and the finite
coefficient vanish. This supplies the entire complementary set of partitions. -/
theorem trace_eq_of_not_contains (hc : contains p w.eta ≠ true) :
    LinearMap.trace ℂ (Space p hp) (witness w hw p hp) =
      (YoungProjectors.degree (etaDiagram w hw) : ℂ) * (computedCoeff w p : ℂ) := by
  have hnot : ¬ etaDiagram w hw ≤ partitionDiagram p hp := by
    intro h
    exact hc ((etaDiagram_le_partitionDiagram_iff w hw p hp).mp h)
  have hP : etaP w hw p hp = 0 :=
    PrefixTrace.projector_eq_zero_of_not_le _ _ _ hnot
  rw [witness_trace_reduced, hP, zero_mul, map_zero]
  simp [computedCoeff, traceWord, tableaux, hc]

/-- A certificate word denotes the literal fixed suffix permutation, since
its offset is the actual cardinality of eta. -/
theorem permutationLetter_fixed {eta nu : YoungDiagram} {r : ℕ}
    (h : eta ≤ nu) (hν : nu.card = 14) (htail : nu.card-eta.card=r+1)
    (i : Fin r) (a b : Fin 14)
    (ha : a.val=eta.card+i.val) (hb : b.val=eta.card+i.val+1) :
    permutationLetter h hν htail i = Equiv.swap a b := by
  unfold permutationLetter
  congr 1 <;> apply Fin.ext
  · simpa [SuffixAction.adjacentIndex, leftIndex] using ha.symm
  · simpa [SuffixAction.adjacentIndex, leftIndex] using hb.symm

theorem trace_word {r : ℕ} (hc : contains p w.eta = true)
    (htail : (partitionDiagram p hp).card-(etaDiagram w hw).card=r+1)
    (word : List (Fin r)) :
    LinearMap.trace ℂ (Space p hp)
      (etaP w hw p hp * (muQ w hw p hp * rep p hp
        (permutationWord (diagram_le_of_contains w.eta p (metadata w hw).eta_sorted hp.2.1 hc)
          (partitionDiagram_card p hp) htail word))) =
      (YoungProjectors.degree (etaDiagram w hw) : ℂ) *
        (traceWord w.eta p w.mu w.k (word.map Fin.val) : ℂ) := by
  exact SelectedWordTrace.trace_projectors_word
    (metadata w hw).eta_sorted hp.2.1 (metadata w hw).mu_sorted
    (metadata w hw).eta_positive (metadata w hw).mu_positive hc
    (m := 13-2*w.k) (q := 13-w.k)
    (by have := etaDiagram_card_add w hw; have := k_le_two w hw; change (etaDiagram w hw).card = _; omega)
    (partitionDiagram_card p hp)
    (by have := muDiagram_card_add w hw; have := k_le_two w hw; change (muDiagram w hw).card = _; omega)
    (by omega) (by omega) (by have := k_le_two w hw; omega) htail word

theorem word_one_permutation (hc : contains p w.eta = true) (hk : w.k=1)
    (htail : (partitionDiagram p hp).card-(etaDiagram w hw).card=1+1) :
    permutationWord (diagram_le_of_contains w.eta p (metadata w hw).eta_sorted hp.2.1 hc)
      (partitionDiagram_card p hp) htail ([0] : List (Fin 1)) = swap12 := by
  have h0 := permutationLetter_fixed
    (diagram_le_of_contains w.eta p (metadata w hw).eta_sorted hp.2.1 hc)
    (partitionDiagram_card p hp) htail (0 : Fin 1) 12 13
    (by change 12=(etaDiagram w hw).card+0; simp [hk])
    (by change 13=(etaDiagram w hw).card+0+1; simp [hk])
  simpa only [permutationWord, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, swap12] using h0

theorem word_two_permutations (hc : contains p w.eta = true) (hk : w.k=2)
    (htail : (partitionDiagram p hp).card-(etaDiagram w hw).card=3+1) :
    permutationWord (diagram_le_of_contains w.eta p (metadata w hw).eta_sorted hp.2.1 hc)
      (partitionDiagram_card p hp) htail ([1,0,2,1] : List (Fin 3)) = swapPairs ∧
    permutationWord (diagram_le_of_contains w.eta p (metadata w hw).eta_sorted hp.2.1 hc)
      (partitionDiagram_card p hp) htail ([2,1,0,2,1] : List (Fin 3)) = swap12*swapPairs := by
  have h0 := permutationLetter_fixed
    (diagram_le_of_contains w.eta p (metadata w hw).eta_sorted hp.2.1 hc)
    (partitionDiagram_card p hp) htail (0 : Fin 3) 10 11
    (by change 10=(etaDiagram w hw).card+0; simp [hk])
    (by change 11=(etaDiagram w hw).card+0+1; simp [hk])
  have h1 := permutationLetter_fixed
    (diagram_le_of_contains w.eta p (metadata w hw).eta_sorted hp.2.1 hc)
    (partitionDiagram_card p hp) htail (1 : Fin 3) 11 12
    (by change 11=(etaDiagram w hw).card+1; simp [hk])
    (by change 12=(etaDiagram w hw).card+1+1; simp [hk])
  have h2 := permutationLetter_fixed
    (diagram_le_of_contains w.eta p (metadata w hw).eta_sorted hp.2.1 hc)
    (partitionDiagram_card p hp) htail (2 : Fin 3) 12 13
    (by change 12=(etaDiagram w hw).card+2; simp [hk])
    (by change 13=(etaDiagram w hw).card+2+1; simp [hk])
  simp only [permutationWord, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one, h0, h1, h2, swap12, swapPairs, mul_assoc, and_self]

theorem witness_trace_two (hk : w.k=2) :
    LinearMap.trace ℂ (Space p hp) (witness w hw p hp) =
      (1/2 : ℂ) * (LinearMap.trace ℂ (Space p hp)
          (etaP w hw p hp * (muQ w hw p hp * rep p hp swapPairs)) +
        (w.sign : ℂ) * LinearMap.trace ℂ (Space p hp)
          (etaP w hw p hp * (muQ w hw p hp * rep p hp (swap12*swapPairs)))) := by
  rw [witness_trace_reduced]
  simp only [rightB, pairF, hk, if_pos, if_neg (show ¬ (2:ℕ)=1 by omega),
    map_mul, mul_smul_comm, smul_mul_assoc, mul_add, add_mul, one_mul, mul_one,
    mul_assoc, map_add, map_smul, smul_eq_mul]

/-- The missing representation-theoretic identification, for all twenty
witnesses and every partition of fourteen. The left side is the trace of
Q B P F B Q formed from actual Young representations and character projectors;
the right side is the unchanged exact certificate evaluator. -/
theorem trace_witness_eq_computedCoeff :
    LinearMap.trace ℂ (Space p hp) (witness w hw p hp) =
      (YoungProjectors.degree (etaDiagram w hw) : ℂ) * (computedCoeff w p : ℂ) := by
  by_cases hc : contains p w.eta = true
  · rcases (metadata w hw).k_cases with hk | hk
    · have htail : (partitionDiagram p hp).card-(etaDiagram w hw).card=1+1 := by
        simp [hk]
      have ht := trace_word w hw p hp hc htail ([0] : List (Fin 1))
      rw [word_one_permutation w hw p hp hc hk htail] at ht
      rw [witness_trace_reduced]
      simpa only [rightB, pairF, hk, if_neg (show ¬ (1:ℕ)=2 by omega), if_pos,
        mul_one, computedCoeff, List.map_cons, List.map_nil, Fin.val_zero] using ht
    · have htail : (partitionDiagram p hp).card-(etaDiagram w hw).card=3+1 := by
        simp [hk]
      have ht := trace_word w hw p hp hc htail ([1,0,2,1] : List (Fin 3))
      have ht' := trace_word w hw p hp hc htail ([2,1,0,2,1] : List (Fin 3))
      obtain ⟨hF,hBF⟩ := word_two_permutations w hw p hp hc hk htail
      rw [hF] at ht
      rw [hBF] at ht'
      rw [witness_trace_two w hw p hp hk, ht, ht']
      simp only [hk]
      change (1/2 : ℂ) *
        ((YoungProjectors.degree (etaDiagram w hw) : ℂ) *
            (traceWord w.eta p w.mu 2 [1,0,2,1] : ℂ) +
          (w.sign : ℂ) * ((YoungProjectors.degree (etaDiagram w hw) : ℂ) *
            (traceWord w.eta p w.mu 2 [2,1,0,2,1] : ℂ))) = _
      simp only [computedCoeff, hk, if_neg (show ¬ (2:ℕ)=1 by omega), if_pos,
        Rat.cast_div, Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
      ring
  · exact trace_eq_of_not_contains w hw p hp hc

end LiebBridge.Young.WitnessTrace
