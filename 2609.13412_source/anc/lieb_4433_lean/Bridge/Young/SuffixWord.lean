import Bridge.Young.SuffixAction
import Mathlib.LinearAlgebra.Matrix.Reindex

/-! Actual suffix words, with the same ordered list product as the exact
certificate evaluator.  The action and matrix identification are proved by
multiplicativity from the verified single-generator identities. -/

noncomputable section
namespace LiebBridge.Young.SuffixWord

open BranchingBasis BranchingAction CertificateSkewEquiv SuffixAction StandardTableau
open scoped BigOperators Matrix Classical

variable {eta nu : YoungDiagram} {r n : ℕ}

def leftIndex (htail : nu.card - eta.card = r+1) (i : Fin r) :
    Fin (nu.card - eta.card) := ⟨i.val, by omega⟩

def rightIndex (htail : nu.card - eta.card = r+1) (i : Fin r) :
    Fin (nu.card - eta.card) := ⟨i.val+1, by omega⟩

def skewLetter (htail : nu.card - eta.card = r+1) (i : Fin r) :
    Module.End ℚ (SkewStandardTableau eta nu → ℚ) :=
  skewGenerator (leftIndex htail i) (rightIndex htail i) rfl

def ambientLetter (h : eta ≤ nu) (htail : nu.card - eta.card = r+1) (i : Fin r) :
    Module.End ℚ (StandardTableau nu → ℚ) :=
  generator (tailIndex h (leftIndex htail i)) (tailIndex h (rightIndex htail i))
    (tailIndex_consecutive h _ _ rfl)

def permutationLetter (h : eta ≤ nu) (hν : nu.card = n+1)
    (htail : nu.card - eta.card = r+1) (i : Fin r) : Equiv.Perm (Fin (n+1)) :=
  Equiv.swap (adjacentIndex h hν (leftIndex htail i) (rightIndex htail i) rfl).castSucc
    (adjacentIndex h hν (leftIndex htail i) (rightIndex htail i) rfl).succ

def skewWord (htail : nu.card - eta.card = r+1) (word : List (Fin r)) :
    Module.End ℚ (SkewStandardTableau eta nu → ℚ) :=
  (word.map (skewLetter htail)).prod

def ambientWord (h : eta ≤ nu) (htail : nu.card - eta.card = r+1) (word : List (Fin r)) :
    Module.End ℚ (StandardTableau nu → ℚ) :=
  (word.map (ambientLetter h htail)).prod

/-- The actual permutation product, in the evaluator's unchanged word order. -/
def permutationWord (h : eta ≤ nu) (hν : nu.card = n+1)
    (htail : nu.card - eta.card = r+1) (word : List (Fin r)) : Equiv.Perm (Fin (n+1)) :=
  (word.map (permutationLetter h hν htail)).prod

theorem representation_permutationLetter (h : eta ≤ nu) (hν : nu.card = n+1)
    (htail : nu.card - eta.card = r+1) (i : Fin r) :
    YoungRepresentation.representation hν (permutationLetter h hν htail i) =
      ambientLetter h htail i :=
  representation_suffixAdjacent h hν (leftIndex htail i) (rightIndex htail i) rfl

theorem representation_permutationWord (h : eta ≤ nu) (hν : nu.card = n+1)
    (htail : nu.card - eta.card = r+1) (word : List (Fin r)) :
    YoungRepresentation.representation hν (permutationWord h hν htail word) =
      ambientWord h htail word := by
  induction word with
  | nil => simp [permutationWord, ambientWord]
  | cons i word ih =>
    change YoungRepresentation.representation hν
      (permutationLetter h hν htail i * permutationWord h hν htail word) =
        ambientLetter h htail i * ambientWord h htail word
    rw [map_mul, representation_permutationLetter, ih]

/-- Act on each skew coordinate function separately, fixing its inner index. -/
def splitOperator (T : Module.End ℚ (SkewStandardTableau eta nu → ℚ)) :
    Module.End ℚ ((StandardTableau eta × SkewStandardTableau eta nu) → ℚ) where
  toFun f p := T (fun b => f (p.1,b)) p.2
  map_add' f g := by
    funext p
    exact congrFun (T.map_add (fun b => f (p.1,b)) (fun b => g (p.1,b))) p.2
  map_smul' c f := by
    funext p
    exact congrFun (T.map_smul c (fun b => f (p.1,b))) p.2

@[simp] theorem splitOperator_one :
    splitOperator (eta := eta) (nu := nu) 1 = 1 := rfl

theorem splitOperator_mul (S T : Module.End ℚ (SkewStandardTableau eta nu → ℚ)) :
    splitOperator (S*T) = splitOperator S * splitOperator T := rfl

/-- Full vector intertwining for arbitrary suffix words. This proves that
products never acquire hidden contributions from outside the prefix block. -/
theorem word_intertwines (h : eta ≤ nu) (htail : nu.card - eta.card = r+1)
    (word : List (Fin r)) (f : StandardTableau eta × SkewStandardTableau eta nu → ℚ) :
    ambientWord h htail word (extendByZero (f ∘ prefixEquiv h)) =
      extendByZero ((splitOperator (skewWord htail word) f) ∘ prefixEquiv h) := by
  induction word generalizing f with
  | nil => simp [ambientWord, skewWord]
  | cons i word ih =>
    change ambientLetter h htail i
      (ambientWord h htail word (extendByZero (f ∘ prefixEquiv h))) = _
    rw [ih]
    rw [ambientLetter,
      SuffixAction.generator_extendByZero h (leftIndex htail i) (rightIndex htail i) rfl,
      SuffixAction.prefixEquiv_intertwines h (leftIndex htail i) (rightIndex htail i) rfl]
    rfl

theorem splitOperator_single (T : Module.End ℚ (SkewStandardTableau eta nu → ℚ))
    (a : StandardTableau eta) (s : SkewStandardTableau eta nu)
    (p : StandardTableau eta × SkewStandardTableau eta nu) :
    splitOperator T (Pi.single (a,s) 1) p =
      if p.1 = a then T (Pi.single s 1) p.2 else 0 := by
  by_cases hp : p.1 = a
  · have hf : (fun b : SkewStandardTableau eta nu =>
        (Pi.single (a,s) (1 : ℚ) : (StandardTableau eta × SkewStandardTableau eta nu) → ℚ) (p.1,b)) =
        (Pi.single s 1 : SkewStandardTableau eta nu → ℚ) := by
      funext b
      simp [Pi.single_apply, hp]
    change T _ _ = _
    rw [hf, if_pos hp]
  · have hf : (fun b : SkewStandardTableau eta nu =>
        (Pi.single (a,s) (1 : ℚ) : (StandardTableau eta × SkewStandardTableau eta nu) → ℚ) (p.1,b)) = 0 := by
      funext b
      simp [Pi.single_apply, hp]
    change T _ _ = _
    rw [hf, map_zero, if_neg hp]
    rfl

theorem word_basis (h : eta ≤ nu) (htail : nu.card - eta.card = r+1)
    (word : List (Fin r)) (a : StandardTableau eta)
    (source : SkewStandardTableau eta nu) (t : StandardTableau nu) :
    ambientWord h htail word (Pi.single (glueTableau h a source).val 1) t =
      if ht : HasPrefix eta t then
        if innerTableau h ⟨t,ht⟩ = a then
          skewWord htail word (Pi.single source 1) (outerTableau h ⟨t,ht⟩)
        else 0
      else 0 := by
  have hh := congrFun (word_intertwines h htail word (Pi.single (a,source) 1)) t
  rw [PrefixRepresentation.extendByZero_single] at hh
  rw [hh]
  by_cases hp : HasPrefix eta t
  · simp only [extendByZero, dif_pos hp, Function.comp_apply]
    change splitOperator (skewWord htail word) (Pi.single (a,source) 1) (prefixEquiv h ⟨t,hp⟩) = _
    exact splitOperator_single _ a source (prefixEquiv h ⟨t,hp⟩)
  · simp only [extendByZero, dif_neg hp]

theorem word_glued_basis (h : eta ≤ nu) (htail : nu.card - eta.card = r+1)
    (word : List (Fin r)) (a b : StandardTableau eta)
    (source target : SkewStandardTableau eta nu) :
    ambientWord h htail word (Pi.single (glueTableau h a source).val 1)
        (glueTableau h b target).val =
      if b = a then skewWord htail word (Pi.single source 1) target else 0 := by
  rw [word_basis]
  simp only [dif_pos (glueTableau h b target).property]
  change (if innerTableau h (glueTableau h b target) = a then
      skewWord htail word (Pi.single source 1) (outerTableau h (glueTableau h b target)) else 0) = _
  rw [innerTableau_glue, outerTableau_glue]

section MatrixModel

local instance : Fintype (SkewStandardTableau eta nu) := Fintype.ofFinite _

/-- The coordinate matrix transported along an actual basis equivalence. -/
def matrixModel {tabs : List LiebBridge.Certificate.Tableau}
    (e : TraceSemantics.TableauBasis tabs ≃ SkewStandardTableau eta nu) :
    Module.End ℚ (SkewStandardTableau eta nu → ℚ) →+*
      Matrix (TraceSemantics.TableauBasis tabs) (TraceSemantics.TableauBasis tabs) ℚ :=
  (Matrix.reindexAlgEquiv ℚ ℚ e.symm).toRingHom.comp (LinearMap.toMatrixAlgEquiv').toRingHom

theorem matrixModel_apply {tabs : List LiebBridge.Certificate.Tableau}
    (e : TraceSemantics.TableauBasis tabs ≃ SkewStandardTableau eta nu)
    (T : Module.End ℚ (SkewStandardTableau eta nu → ℚ))
    (target source : TraceSemantics.TableauBasis tabs) :
    matrixModel e T target source = T (Pi.single (e source) 1) (e target) := by
  change LinearMap.toMatrixAlgEquiv' T (e target) (e source) = _
  rw [LinearMap.toMatrixAlgEquiv'_apply]
  have heq : (fun j' : SkewStandardTableau eta nu => if j' = e source then (1 : ℚ) else 0) =
      (Pi.single (e source) 1 : SkewStandardTableau eta nu → ℚ) := by
    funext j'
    simp [Pi.single_apply]
  rw [heq]

theorem matrixModel_skewLetter (h : eta ≤ nu) (htail : nu.card - eta.card = r+1)
    {tabs : List LiebBridge.Certificate.Tableau}
    (e : TraceSemantics.TableauBasis tabs ≃ SkewStandardTableau eta nu)
    (hencode : ∀ t, encode (e t) = t.val) (i : Fin r) :
    matrixModel e (skewLetter htail i) = TraceSemantics.seminormalMatrix tabs i.val := by
  ext target source
  rw [matrixModel_apply]
  change skewGenerator (leftIndex htail i) (rightIndex htail i) rfl _ _ = _
  rw [skewGenerator_basis h _ _ rfl, hencode, hencode]
  rfl

/-- The actual skew word matrix is exactly the evaluator's ordered product. -/
theorem matrixModel_skewWord (h : eta ≤ nu) (htail : nu.card - eta.card = r+1)
    {tabs : List LiebBridge.Certificate.Tableau}
    (e : TraceSemantics.TableauBasis tabs ≃ SkewStandardTableau eta nu)
    (hencode : ∀ t, encode (e t) = t.val) (word : List (Fin r)) :
    matrixModel e (skewWord htail word) =
      TraceSemantics.wordMatrix tabs (word.map Fin.val) := by
  induction word with
  | nil => simp [skewWord, TraceSemantics.wordMatrix]
  | cons i word ih =>
    change matrixModel e (skewLetter htail i * skewWord htail word) =
      TraceSemantics.seminormalMatrix tabs i.val * TraceSemantics.wordMatrix tabs (word.map Fin.val)
    rw [map_mul, matrixModel_skewLetter h htail e hencode, ih]

theorem skewWord_basis (h : eta ≤ nu) (htail : nu.card - eta.card = r+1)
    {tabs : List LiebBridge.Certificate.Tableau}
    (e : TraceSemantics.TableauBasis tabs ≃ SkewStandardTableau eta nu)
    (hencode : ∀ t, encode (e t) = t.val) (word : List (Fin r))
    (source target : TraceSemantics.TableauBasis tabs) :
    skewWord htail word (Pi.single (e source) 1) (e target) =
      TraceSemantics.wordMatrix tabs (word.map Fin.val) target source := by
  rw [← matrixModel_apply e, matrixModel_skewWord h htail e hencode]

end MatrixModel

/-- Full ambient support and coefficient statement after scalar extension. -/
theorem representation_word_basis (K : Type*) [Field K] [CharZero K]
    (h : eta ≤ nu) (hν : nu.card = n+1) (htail : nu.card - eta.card = r+1)
    (word : List (Fin r)) (a : StandardTableau eta)
    (source : SkewStandardTableau eta nu) (t : StandardTableau nu) :
    ScalarExtension.representation K hν (permutationWord h hν htail word)
        (Pi.single (glueTableau h a source).val 1) t =
      if ht : HasPrefix eta t then
        if innerTableau h ⟨t,ht⟩ = a then
          (skewWord htail word (Pi.single source 1) (outerTableau h ⟨t,ht⟩) : K)
        else 0
      else 0 := by
  change ScalarExtension.extend K (YoungRepresentation.representation hν _)
    (Pi.single (glueTableau h a source).val 1) t = _
  rw [ScalarExtension.extend_basis_coefficient, representation_permutationWord, word_basis]
  split_ifs <;> simp

/-- Actual representation of a suffix permutation word on every glued basis
vector, expressed by the exact evaluator word matrix through a proved basis
equivalence. The source and target order is unchanged. -/
theorem representation_word_matrix (K : Type*) [Field K] [CharZero K]
    (h : eta ≤ nu) (hν : nu.card = n+1) (htail : nu.card - eta.card = r+1)
    {tabs : List LiebBridge.Certificate.Tableau}
    (e : TraceSemantics.TableauBasis tabs ≃ SkewStandardTableau eta nu)
    (hencode : ∀ t, encode (e t) = t.val) (word : List (Fin r))
    (a b : StandardTableau eta) (source target : TraceSemantics.TableauBasis tabs) :
    ScalarExtension.representation K hν (permutationWord h hν htail word)
        (Pi.single (glueTableau h a (e source)).val 1) (glueTableau h b (e target)).val =
      if b = a then (TraceSemantics.wordMatrix tabs (word.map Fin.val) target source : K)
      else 0 := by
  change ScalarExtension.extend K (YoungRepresentation.representation hν _)
    (Pi.single (glueTableau h a (e source)).val 1) (glueTableau h b (e target)).val = _
  rw [ScalarExtension.extend_basis_coefficient, representation_permutationWord, word_glued_basis,
    skewWord_basis h htail e hencode]
  split_ifs <;> simp

/-- The unchanged certificate list, viewed as the finite matrix basis, is
equivalent to the actual geometric skew-tableau basis. -/
def certificateBasisEquiv (etaList nuList : LiebBridge.Certificate.Shape)
    (he : etaList.Sorted (· ≥ ·)) (hn : nuList.Sorted (· ≥ ·))
    (hc : LiebBridge.Certificate.contains nuList etaList = true) :
    TraceSemantics.TableauBasis (LiebBridge.Certificate.tableaux etaList nuList) ≃
      SkewStandardTableau (YoungDiagram.ofRowLens etaList he) (YoungDiagram.ofRowLens nuList hn) :=
  ({ toFun := fun t => ⟨t.val, List.mem_toFinset.mp t.property⟩
     invFun := fun t => ⟨t.val, List.mem_toFinset.mpr t.property⟩
     left_inv := fun _ => rfl
     right_inv := fun _ => rfl } :
    TraceSemantics.TableauBasis (LiebBridge.Certificate.tableaux etaList nuList) ≃
      {t : LiebBridge.Certificate.Tableau // t ∈ LiebBridge.Certificate.tableaux etaList nuList}).trans
    (certificateEquiv etaList nuList he hn hc)

theorem certificateBasisEquiv_encode (etaList nuList : LiebBridge.Certificate.Shape)
    (he : etaList.Sorted (· ≥ ·)) (hn : nuList.Sorted (· ≥ ·))
    (hc : LiebBridge.Certificate.contains nuList etaList = true)
    (t : TraceSemantics.TableauBasis (LiebBridge.Certificate.tableaux etaList nuList)) :
    encode (certificateBasisEquiv etaList nuList he hn hc t) = t.val :=
  encode_certificateEquiv etaList nuList he hn hc ⟨t.val, List.mem_toFinset.mp t.property⟩

/-- Specialized endpoint with the actual certificate tableau enumeration.
There are no uninstantiated matrix or basis-identification hypotheses. -/
theorem certificate_representation_word_matrix (K : Type*) [Field K] [CharZero K]
    (etaList nuList : LiebBridge.Certificate.Shape)
    (he : etaList.Sorted (· ≥ ·)) (hn : nuList.Sorted (· ≥ ·))
    (hc : LiebBridge.Certificate.contains nuList etaList = true)
    (hν : (YoungDiagram.ofRowLens nuList hn).card = n+1)
    (htail : (YoungDiagram.ofRowLens nuList hn).card -
      (YoungDiagram.ofRowLens etaList he).card = r+1)
    (word : List (Fin r)) (a b : StandardTableau (YoungDiagram.ofRowLens etaList he))
    (source target : TraceSemantics.TableauBasis (LiebBridge.Certificate.tableaux etaList nuList)) :
    ScalarExtension.representation K hν
        (permutationWord (diagram_le_of_contains etaList nuList he hn hc) hν htail word)
        (Pi.single (glueTableau (diagram_le_of_contains etaList nuList he hn hc) a
          (certificateBasisEquiv etaList nuList he hn hc source)).val 1)
        (glueTableau (diagram_le_of_contains etaList nuList he hn hc) b
          (certificateBasisEquiv etaList nuList he hn hc target)).val =
      if b = a then
        (TraceSemantics.wordMatrix (LiebBridge.Certificate.tableaux etaList nuList)
          (word.map Fin.val) target source : K)
      else 0 :=
  representation_word_matrix K (diagram_le_of_contains etaList nuList he hn hc) hν htail
    (certificateBasisEquiv etaList nuList he hn hc)
    (certificateBasisEquiv_encode etaList nuList he hn hc) word a b source target

end LiebBridge.Young.SuffixWord
