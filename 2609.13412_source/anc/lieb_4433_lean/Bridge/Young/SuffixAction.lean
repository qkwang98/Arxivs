import Bridge.Young.PrefixRepresentation
import Bridge.Young.CertificateSkewAction
import Bridge.Young.TraceSemantics
import Bridge.Young.SeminormalEdges

/-! The actual suffix generators under the genuine tableau basis split,
and their exact agreement with the certificate's column-source convention. -/

noncomputable section
namespace LiebBridge.Young.SuffixAction

open BranchingBasis BranchingAction StandardTableau
open CertificateSkewEquiv CertificateSkewAction
open scoped BigOperators Classical

variable {eta nu : YoungDiagram}

def tailIndex (h : eta ≤ nu) (i : Fin (nu.card - eta.card)) : Fin nu.card :=
  ⟨eta.card + i.val, by have := card_le h; omega⟩

@[simp] theorem tailIndex_val (h : eta ≤ nu) (i : Fin (nu.card - eta.card)) :
    (tailIndex h i).val = eta.card + i.val := rfl

theorem tailIndex_injective (h : eta ≤ nu) : Function.Injective (tailIndex h) := by
  intro i j hij
  apply Fin.ext
  have := congrArg Fin.val hij
  simpa only [tailIndex_val, Nat.add_left_cancel_iff] using this

theorem tailIndex_consecutive (h : eta ≤ nu) (i j : Fin (nu.card - eta.card))
    (hij : j.val = i.val+1) : (tailIndex h j).val = (tailIndex h i).val+1 := by
  simp only [tailIndex_val, hij, Nat.add_assoc]

theorem outer_number_embed (h : eta ≤ nu) (t : PrefixTableau eta nu)
    (b : SkewCell eta nu) :
    tailIndex h ((outerTableau h t).number b) = t.val.number b.val := by
  apply Fin.ext
  rw [tailIndex_val, outerTableau_number_val]
  have := outer_label_ge t b
  omega

theorem outer_entry_embed (h : eta ≤ nu) (t : PrefixTableau eta nu)
    (i : Fin (nu.card - eta.card)) :
    ((outerTableau h t).number.symm i).val = t.val.entry (tailIndex h i) := by
  apply t.val.number.injective
  rw [← outer_number_embed, Equiv.apply_symm_apply, number_entry]

theorem outer_entry_val (h : eta ≤ nu) (t : PrefixTableau eta nu)
    (i : Fin (nu.card - eta.card)) :
    ((outerTableau h t).number.symm i).val.val = (t.val.entry (tailIndex h i)).val :=
  congrArg Subtype.val (outer_entry_embed h t i)

theorem outer_entry_le_iff (h : eta ≤ nu) (t : PrefixTableau eta nu)
    (i j : Fin (nu.card - eta.card)) :
    (outerTableau h t).number.symm i ≤ (outerTableau h t).number.symm j ↔
      t.val.entry (tailIndex h i) ≤ t.val.entry (tailIndex h j) := by
  change ((outerTableau h t).number.symm i).val ≤
    ((outerTableau h t).number.symm j).val ↔ _
  rw [outer_entry_embed, outer_entry_embed]

def skewContent (t : SkewStandardTableau eta nu) (i : Fin (nu.card - eta.card)) : ℚ :=
  (boxContent (t.number.symm i).val.val : ℤ)

def skewAxial (t : SkewStandardTableau eta nu) (i j : Fin (nu.card - eta.card)) : ℚ :=
  skewContent t j - skewContent t i

theorem axial_suffix (h : eta ≤ nu) (t : PrefixTableau eta nu)
    (i j : Fin (nu.card - eta.card)) :
    t.val.axial (tailIndex h i) (tailIndex h j) = skewAxial (outerTableau h t) i j := by
  simp only [axial, rationalContent, skewAxial, skewContent, outer_entry_val]

theorem hasPrefix_adjacentSwap_iff (h : eta ≤ nu) (t : StandardTableau nu)
    (i j : Fin (nu.card - eta.card)) (hij : j.val = i.val+1) :
    HasPrefix eta (t.adjacentSwap (tailIndex h i) (tailIndex h j)
      (tailIndex_consecutive h i j hij)) ↔ HasPrefix eta t := by
  by_cases hs : ¬ t.entry (tailIndex h i) ≤ t.entry (tailIndex h j)
  · rw [adjacentSwap_of_allowed _ _ _ _ hs]
    have he (b : Cell nu) :
        ((t.swapAllowed (tailIndex h i) (tailIndex h j)
          (tailIndex_consecutive h i j hij) hs).number b).val < eta.card ↔
          (t.number b).val < eta.card := by
      simp only [swapAllowed_number, Equiv.trans_apply, Equiv.swap_apply_def]
      split_ifs with hi hj
      · have hv := congrArg Fin.val hi
        simp only [tailIndex_val] at hv ⊢
        omega
      · have hv := congrArg Fin.val hj
        simp only [tailIndex_val] at hv ⊢
        omega
      · rfl
    simp only [HasPrefix, he]
  · rw [adjacentSwap_of_forbidden _ _ _ _ (not_not.mp hs)]

def suffixSwap (h : eta ≤ nu) (t : PrefixTableau eta nu)
    (i j : Fin (nu.card - eta.card)) (hij : j.val = i.val+1) : PrefixTableau eta nu :=
  ⟨t.val.adjacentSwap (tailIndex h i) (tailIndex h j) (tailIndex_consecutive h i j hij),
    (hasPrefix_adjacentSwap_iff h t.val i j hij).mpr t.property⟩

theorem innerTableau_suffixSwap (h : eta ≤ nu) (t : PrefixTableau eta nu)
    (i j : Fin (nu.card - eta.card)) (hij : j.val = i.val+1) :
    innerTableau h (suffixSwap h t i j hij) = innerTableau h t := by
  apply StandardTableau.ext
  apply Equiv.ext
  intro b
  apply Fin.ext
  rw [innerTableau_number_val, innerTableau_number_val]
  by_cases hs : ¬ t.val.entry (tailIndex h i) ≤ t.val.entry (tailIndex h j)
  · have hb : (t.val.number (innerCell h b)).val < eta.card :=
      (t.property (innerCell h b)).mpr b.property
    have hi : t.val.number (innerCell h b) ≠ tailIndex h i := by
      intro he
      have := congrArg Fin.val he
      simp only [tailIndex_val] at this
      omega
    have hj : t.val.number (innerCell h b) ≠ tailIndex h j := by
      intro he
      have := congrArg Fin.val he
      simp only [tailIndex_val] at this
      omega
    change ((t.val.adjacentSwap (tailIndex h i) (tailIndex h j) _).number (innerCell h b)).val = _
    rw [adjacentSwap_of_allowed _ _ _ _ hs]
    simp [swapAllowed_number, Equiv.swap_apply_of_ne_of_ne hi hj]
  · change ((t.val.adjacentSwap (tailIndex h i) (tailIndex h j) _).number (innerCell h b)).val = _
    rw [adjacentSwap_of_forbidden _ _ _ _ (not_not.mp hs)]

theorem outerTableau_suffixSwap (h : eta ≤ nu) (t : PrefixTableau eta nu)
    (i j : Fin (nu.card - eta.card)) (hij : j.val = i.val+1)
    (hs : ¬ (outerTableau h t).number.symm i ≤ (outerTableau h t).number.symm j) :
    outerTableau h (suffixSwap h t i j hij) =
      swappedTableau (outerTableau h t) i j ((swap_numbering_strictMono_iff _ i j hij).mpr hs) := by
  have hs' : ¬ t.val.entry (tailIndex h i) ≤ t.val.entry (tailIndex h j) :=
    fun hh => hs ((outer_entry_le_iff h t i j).mpr hh)
  apply CertificateSkewEquiv.skew_ext
  apply Equiv.ext
  intro b
  apply tailIndex_injective h
  rw [outer_number_embed]
  change (t.val.adjacentSwap (tailIndex h i) (tailIndex h j) _).number b.val =
    tailIndex h (Equiv.swap i j ((outerTableau h t).number b))
  rw [adjacentSwap_of_allowed _ _ _ _ hs']
  simp only [swapAllowed_number, Equiv.trans_apply]
  rw [← outer_number_embed]
  exact (Function.Injective.map_swap (tailIndex_injective h) i j
    ((outerTableau h t).number b)).symm

theorem suffixSwap_of_forbidden (h : eta ≤ nu) (t : PrefixTableau eta nu)
    (i j : Fin (nu.card - eta.card)) (hij : j.val = i.val+1)
    (hs : (outerTableau h t).number.symm i ≤ (outerTableau h t).number.symm j) :
    suffixSwap h t i j hij = t := by
  apply Subtype.ext
  exact adjacentSwap_of_forbidden _ _ _ _ ((outer_entry_le_iff h t i j).mp hs)

/-- The skew row-form operator uses the already constructed genuine skew swap. -/
def skewGenerator (i j : Fin (nu.card - eta.card)) (hij : j.val = i.val+1) :
    Module.End ℚ (SkewStandardTableau eta nu → ℚ) where
  toFun v t := (skewAxial t i j)⁻¹ * v t +
    if hs : ¬ t.number.symm i ≤ t.number.symm j then
      (1 - (skewAxial t i j)⁻¹) *
        v (swappedTableau t i j ((swap_numbering_strictMono_iff t i j hij).mpr hs))
    else 0
  map_add' v w := by
    funext t
    simp only [Pi.add_apply]
    split_ifs <;> ring
  map_smul' c v := by
    funext t
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

def suffixAction (h : eta ≤ nu) (i j : Fin (nu.card - eta.card))
    (hij : j.val = i.val+1) (v : PrefixTableau eta nu → ℚ) (t : PrefixTableau eta nu) : ℚ :=
  generator (tailIndex h i) (tailIndex h j) (tailIndex_consecutive h i j hij)
    (extendByZero v) t.val

theorem generator_extendByZero (h : eta ≤ nu) (i j : Fin (nu.card - eta.card))
    (hij : j.val = i.val+1) (v : PrefixTableau eta nu → ℚ) :
    generator (tailIndex h i) (tailIndex h j) (tailIndex_consecutive h i j hij)
      (extendByZero v) = extendByZero (suffixAction h i j hij v) := by
  funext t
  by_cases hp : HasPrefix eta t
  · simp only [extendByZero, dif_pos hp]
    rfl
  · have hp' : ¬ HasPrefix eta
        (t.adjacentSwap (tailIndex h i) (tailIndex h j) (tailIndex_consecutive h i j hij)) :=
      fun hh => hp ((hasPrefix_adjacentSwap_iff h t i j hij).mp hh)
    simp [generator_apply, extendByZero, hp, hp']

def splitAction (i j : Fin (nu.card - eta.card)) (hij : j.val = i.val+1)
    (f : StandardTableau eta × SkewStandardTableau eta nu → ℚ)
    (p : StandardTableau eta × SkewStandardTableau eta nu) : ℚ :=
  skewGenerator i j hij (fun b => f (p.1,b)) p.2

/-- Under the genuine prefix split, a suffix generator fixes the inner
standard tableau and acts by the rational skew seminormal operator. -/
theorem prefixEquiv_intertwines (h : eta ≤ nu) (i j : Fin (nu.card - eta.card))
    (hij : j.val = i.val+1) (f : StandardTableau eta × SkewStandardTableau eta nu → ℚ) :
    suffixAction h i j hij (f ∘ prefixEquiv h) = splitAction i j hij f ∘ prefixEquiv h := by
  funext t
  have hp := (hasPrefix_adjacentSwap_iff h t.val i j hij).mpr t.property
  simp only [suffixAction, generator_apply, extendByZero, dif_pos t.property, dif_pos hp,
    Function.comp_apply, splitAction]
  change (t.val.axial (tailIndex h i) (tailIndex h j))⁻¹ * f (prefixEquiv h t) +
    (if ¬ t.val.entry (tailIndex h i) ≤ t.val.entry (tailIndex h j) then
      (1 - (t.val.axial (tailIndex h i) (tailIndex h j))⁻¹) *
        f (prefixEquiv h (suffixSwap h t i j hij)) else 0) = _
  rw [axial_suffix]
  by_cases hs : ¬ (outerTableau h t).number.symm i ≤ (outerTableau h t).number.symm j
  · have hs' := mt (outer_entry_le_iff h t i j).mpr hs
    simp only [if_pos hs', skewGenerator, LinearMap.coe_mk, AddHom.coe_mk,
      dif_pos hs, prefixEquiv, Equiv.coe_fn_mk,
      innerTableau_suffixSwap, outerTableau_suffixSwap h t i j hij hs]
  · have hs' : ¬ ¬ t.val.entry (tailIndex h i) ≤ t.val.entry (tailIndex h j) :=
      not_not.mpr ((outer_entry_le_iff h t i j).mp (not_not.mp hs))
    simp only [if_neg hs', skewGenerator, LinearMap.coe_mk, AddHom.coe_mk,
      dif_neg hs, prefixEquiv, Equiv.coe_fn_mk]

theorem encode_injective (h : eta ≤ nu) :
    Function.Injective (encode : SkewStandardTableau eta nu → LiebBridge.Certificate.Tableau) := by
  intro S T he
  exact (geometricEquiv h).symm.injective (Subtype.ext he)

theorem skewAxial_eq_axialGap (t : SkewStandardTableau eta nu)
    (i j : Fin (nu.card - eta.card)) (hij : j.val = i.val+1) :
    skewAxial t i j = TraceSemantics.axialGap (encode t) i.val := by
  rw [TraceSemantics.axialGap, ← hij, encode_getD, encode_getD]
  simp only [skewAxial, skewContent, Int.cast_sub]
  rfl

theorem swappedTableau_allowed (t : SkewStandardTableau eta nu)
    (i j : Fin (nu.card - eta.card)) (hij : j.val = i.val+1)
    (hs : StrictMono (t.number.trans (Equiv.swap i j))) :
    ¬ (swappedTableau t i j hs).number.symm i ≤ (swappedTableau t i j hs).number.symm j := by
  intro hh
  change t.number.symm (Equiv.swap i j i) ≤ t.number.symm (Equiv.swap i j j) at hh
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right] at hh
  have he := t.increasing.monotone hh
  simp only [Equiv.apply_symm_apply] at he
  have hv : j.val ≤ i.val := he
  omega

theorem swappedTableau_twice (t : SkewStandardTableau eta nu)
    (i j : Fin (nu.card - eta.card))
    (hs : StrictMono (t.number.trans (Equiv.swap i j)))
    (hs' : StrictMono ((swappedTableau t i j hs).number.trans (Equiv.swap i j))) :
    swappedTableau (swappedTableau t i j hs) i j hs' = t := by
  apply CertificateSkewEquiv.skew_ext
  apply Equiv.ext
  intro b
  simp [swappedTableau]

theorem swappedTableau_ne (t : SkewStandardTableau eta nu)
    (i j : Fin (nu.card - eta.card)) (hij : j.val = i.val+1)
    (hs : StrictMono (t.number.trans (Equiv.swap i j))) :
    swappedTableau t i j hs ≠ t := by
  intro he
  have hh := congrArg (fun T : SkewStandardTableau eta nu => T.number (t.number.symm i)) he
  simp only [swappedTableau, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.swap_apply_left] at hh
  have hv := congrArg Fin.val hh
  omega

theorem skewAxial_swappedTableau (t : SkewStandardTableau eta nu)
    (i j : Fin (nu.card - eta.card))
    (hs : StrictMono (t.number.trans (Equiv.swap i j))) :
    skewAxial (swappedTableau t i j hs) i j = -skewAxial t i j := by
  change (boxContent (t.number.symm (Equiv.swap i j j)).val.val : ℚ) -
    (boxContent (t.number.symm (Equiv.swap i j i)).val.val : ℚ) = _
  simp only [Equiv.swap_apply_left, Equiv.swap_apply_right, skewAxial, skewContent]
  ring

theorem encode_eq_swap_iff (h : eta ≤ nu) (S T : SkewStandardTableau eta nu)
    (i j : Fin (nu.card - eta.card)) (hij : j.val = i.val+1) :
    encode T = LiebBridge.Certificate.swapAdjacent (encode S) i.val ↔
      ∃ hs : StrictMono (S.number.trans (Equiv.swap i j)), T = swappedTableau S i j hs := by
  constructor
  · intro he
    have ha : ¬ S.number.symm i ≤ S.number.symm j := by
      apply (standard_swapAdjacent_iff S i j hij).mp
      rw [← he]
      exact encode_standard T
    let hs := (swap_numbering_strictMono_iff S i j hij).mpr ha
    refine ⟨hs, encode_injective h ?_⟩
    rw [he, encode_swappedTableau S i j hij hs]
  · rintro ⟨hs, rfl⟩
    exact encode_swappedTableau S i j hij hs

/-- The exact row-target/column-source coefficient used by the executable
trace evaluator. In particular the off-diagonal coefficient is
`1 + 1 / axialGap source`, with its source normalization proved explicitly. -/
theorem skewGenerator_basis (h : eta ≤ nu) (i j : Fin (nu.card - eta.card))
    (hij : j.val = i.val+1) (source target : SkewStandardTableau eta nu) :
    skewGenerator i j hij (Pi.single source 1) target =
      TraceSemantics.seminormalEntry i.val (encode target) (encode source) := by
  have hdiag : encode target = encode source ↔ target = source := (encode_injective h).eq_iff
  by_cases he : encode target = LiebBridge.Certificate.swapAdjacent (encode source) i.val
  · obtain ⟨hs, rfl⟩ := (encode_eq_swap_iff h source target i j hij).mp he
    have ha := swappedTableau_allowed source i j hij hs
    have hs' := (swap_numbering_strictMono_iff (swappedTableau source i j hs) i j hij).mpr ha
    have ht := swappedTableau_twice source i j hs hs'
    have hn := swappedTableau_ne source i j hij hs
    have hen : encode (swappedTableau source i j hs) ≠ encode source :=
      fun hh => hn (encode_injective h hh)
    simp only [skewGenerator, LinearMap.coe_mk, AddHom.coe_mk, dif_pos ha,
      Pi.single_apply, if_neg hn, ht, if_pos rfl, mul_zero, mul_one, zero_add,
      skewAxial_swappedTableau, inv_neg, sub_neg_eq_add,
      TraceSemantics.seminormalEntry, if_neg hen, if_pos he, zero_add,
      ← skewAxial_eq_axialGap source i j hij, one_div]
    simp
  · have hzero : (if hs : ¬ target.number.symm i ≤ target.number.symm j then
        (1 - (skewAxial target i j)⁻¹) *
          (Pi.single source (1 : ℚ) : SkewStandardTableau eta nu → ℚ)
            (swappedTableau target i j ((swap_numbering_strictMono_iff target i j hij).mpr hs))
        else 0) = 0 := by
      by_cases hs : ¬ target.number.symm i ≤ target.number.symm j
      · rw [dif_pos hs]
        let hst := (swap_numbering_strictMono_iff target i j hij).mpr hs
        have hn : swappedTableau target i j hst ≠ source := by
          intro hh
          have ha := swappedTableau_allowed target i j hij hst
          have hs' := (swap_numbering_strictMono_iff (swappedTableau target i j hst) i j hij).mpr ha
          have hx := encode_swappedTableau (swappedTableau target i j hst) i j hij hs'
          rw [swappedTableau_twice] at hx
          rw [hh] at hx
          exact he hx
        simp [Pi.single_apply, hn]
      · rw [dif_neg hs]
    change (skewAxial target i j)⁻¹ *
      (Pi.single source (1 : ℚ) : SkewStandardTableau eta nu → ℚ) target + _ = _
    rw [hzero]
    simp only [TraceSemantics.seminormalEntry, if_neg he, add_zero, hdiag,
      ← skewAxial_eq_axialGap source i j hij, one_div, Pi.single_apply]
    split_ifs with ht
    · subst target
      simp
    · simp

theorem splitAction_single (i j : Fin (nu.card - eta.card)) (hij : j.val = i.val+1)
    (a : StandardTableau eta) (s : SkewStandardTableau eta nu)
    (p : StandardTableau eta × SkewStandardTableau eta nu) :
    splitAction i j hij (Pi.single (a,s) 1) p =
      if p.1 = a then skewGenerator i j hij (Pi.single s 1) p.2 else 0 := by
  by_cases hp : p.1 = a
  · have hf : (fun b : SkewStandardTableau eta nu =>
        (Pi.single (a,s) (1 : ℚ) : (StandardTableau eta × SkewStandardTableau eta nu) → ℚ) (p.1,b)) =
        (Pi.single s 1 : SkewStandardTableau eta nu → ℚ) := by
      funext b
      simp [Pi.single_apply, hp]
    simp only [splitAction, hf, if_pos hp]
  · have hf : (fun b : SkewStandardTableau eta nu =>
        (Pi.single (a,s) (1 : ℚ) : (StandardTableau eta × SkewStandardTableau eta nu) → ℚ) (p.1,b)) = 0 := by
      funext b
      simp [Pi.single_apply, hp]
    simp only [splitAction, hf, map_zero, Pi.zero_apply, if_neg hp]

/-- The actual ambient suffix generator, directly on ambient basis vectors.
Every entry agrees with the evaluator after encoding the skew tableau. -/
theorem generator_basis (h : eta ≤ nu) (i j : Fin (nu.card - eta.card))
    (hij : j.val = i.val+1) (a : StandardTableau eta)
    (source : SkewStandardTableau eta nu) (t : StandardTableau nu) :
    generator (tailIndex h i) (tailIndex h j) (tailIndex_consecutive h i j hij)
        (Pi.single (glueTableau h a source).val 1) t =
      if ht : HasPrefix eta t then
        if innerTableau h ⟨t,ht⟩ = a then
          TraceSemantics.seminormalEntry i.val (encode (outerTableau h ⟨t,ht⟩)) (encode source)
        else 0
      else 0 := by
  have hh := congrFun (generator_extendByZero h i j hij
    ((Pi.single (a,source) 1) ∘ prefixEquiv h)) t
  rw [PrefixRepresentation.extendByZero_single, prefixEquiv_intertwines] at hh
  rw [hh]
  by_cases hp : HasPrefix eta t
  · simp only [extendByZero, dif_pos hp, Function.comp_apply]
    change splitAction i j hij (Pi.single (a,source) 1) (prefixEquiv h ⟨t,hp⟩) = _
    rw [splitAction_single, skewGenerator_basis h]
    rfl
  · simp only [extendByZero, dif_neg hp]

theorem generator_glued_basis (h : eta ≤ nu) (i j : Fin (nu.card - eta.card))
    (hij : j.val = i.val+1) (a b : StandardTableau eta)
    (source target : SkewStandardTableau eta nu) :
    generator (tailIndex h i) (tailIndex h j) (tailIndex_consecutive h i j hij)
        (Pi.single (glueTableau h a source).val 1) (glueTableau h b target).val =
      if b = a then TraceSemantics.seminormalEntry i.val (encode target) (encode source) else 0 := by
  rw [generator_basis h i j hij]
  simp only [dif_pos (glueTableau h b target).property]
  change (if innerTableau h (glueTableau h b target) = a then
      TraceSemantics.seminormalEntry i.val (encode (outerTableau h (glueTableau h b target)))
        (encode source) else 0) = _
  rw [innerTableau_glue, outerTableau_glue]

def adjacentIndex {n : ℕ} (h : eta ≤ nu) (hν : nu.card = n+1)
    (i j : Fin (nu.card - eta.card)) (hij : j.val = i.val+1) : Fin n :=
  ⟨eta.card+i.val, by have := (tailIndex h j).isLt; simp only [tailIndex_val] at this; omega⟩

/-- The ambient generator above is the representation of the actual adjacent
permutation on the corresponding suffix labels. -/
theorem representation_suffixAdjacent {n : ℕ} (h : eta ≤ nu) (hν : nu.card = n+1)
    (i j : Fin (nu.card - eta.card)) (hij : j.val = i.val+1) :
    YoungRepresentation.representation hν
        (Equiv.swap (adjacentIndex h hν i j hij).castSucc (adjacentIndex h hν i j hij).succ) =
      generator (tailIndex h i) (tailIndex h j) (tailIndex_consecutive h i j hij) := by
  rw [YoungRepresentation.representation_adjacent]
  have hj : YoungRepresentation.rightIndex hν (adjacentIndex h hν i j hij) = tailIndex h j := by
    apply Fin.ext
    simp only [YoungRepresentation.rightIndex_val, adjacentIndex, tailIndex_val]
    omega
  unfold YoungRepresentation.adjacentOperator
  simp only [hj]
  rfl

/-- Direct complex (or characteristic-zero field) version of the actual
suffix permutation coefficient. -/
theorem representation_glued_basis (K : Type*) [Field K] [CharZero K] {n : ℕ}
    (h : eta ≤ nu) (hν : nu.card = n+1)
    (i j : Fin (nu.card - eta.card)) (hij : j.val = i.val+1)
    (a b : StandardTableau eta) (source target : SkewStandardTableau eta nu) :
    ScalarExtension.representation K hν
        (Equiv.swap (adjacentIndex h hν i j hij).castSucc (adjacentIndex h hν i j hij).succ)
        (Pi.single (glueTableau h a source).val 1) (glueTableau h b target).val =
      if b = a then (TraceSemantics.seminormalEntry i.val (encode target) (encode source) : K)
      else 0 := by
  change ScalarExtension.extend K (YoungRepresentation.representation hν _)
    (Pi.single (glueTableau h a source).val 1) (glueTableau h b target).val = _
  rw [ScalarExtension.extend_basis_coefficient, representation_suffixAdjacent h hν i j hij,
    generator_glued_basis h i j hij]
  split_ifs <;> simp

end LiebBridge.Young.SuffixAction
