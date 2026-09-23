import Bridge.CertificateAlgorithm
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

/-! Structural semantics of the finite rational path evaluator. Nothing in this file
identifies these matrices with an ordinary irreducible representation. -/

namespace LiebBridge.Young.TraceSemantics
open LiebBridge.Certificate
open scoped BigOperators Matrix
set_option maxRecDepth 5000

abbrev TableauBasis (tabs : List Tableau) := ↥tabs.toFinset

/-- The axial content difference used by the existing evaluator. -/
def axialGap (t : Tableau) (i : Nat) : ℚ :=
  (content (t.getD (i + 1) (0, 0)) - content (t.getD i (0, 0)) : ℤ)

/-- Explicit column-source, row-target rational seminormal entry. -/
def seminormalEntry (i : Nat) (target source : Tableau) : ℚ :=
  (if target = source then 1 / axialGap source i else 0) +
    (if target = swapAdjacent source i then 1 + 1 / axialGap source i else 0)

def seminormalMatrix (tabs : List Tableau) (i : Nat) :
    Matrix (TableauBasis tabs) (TableauBasis tabs) ℚ :=
  fun target source => seminormalEntry i target.val source.val

def wordMatrix (tabs : List Tableau) (word : List Nat) :
    Matrix (TableauBasis tabs) (TableauBasis tabs) ℚ :=
  (word.map (seminormalMatrix tabs)).prod

def prefixSelector (tabs : List Tableau) (eta mu : Shape) (k : Nat) :
    Matrix (TableauBasis tabs) (TableauBasis tabs) ℚ :=
  Matrix.diagonal fun t => if prefixShape eta t.val k == mu then 1 else 0

def mass (states : List (Tableau × ℚ)) (target : Tableau) : ℚ :=
  (states.map fun s => if s.1 == target then s.2 else 0).sum

def stateVector (tabs : List Tableau) (states : List (Tableau × ℚ)) :
    TableauBasis tabs → ℚ := fun t => mass states t.val

def Supported (tabs : List Tableau) (states : List (Tableau × ℚ)) : Prop :=
  ∀ s ∈ states, s.1 ∈ tabs

lemma basis_mem {tabs : List Tableau} (t : TableauBasis tabs) : t.val ∈ tabs :=
  List.mem_toFinset.mp t.property

lemma mass_nil (target : Tableau) : mass [] target = 0 := by simp [mass]

lemma mass_cons (s : Tableau × ℚ) (ss : List (Tableau × ℚ)) (target : Tableau) :
    mass (s :: ss) target = (if s.1 = target then s.2 else 0) + mass ss target := by
  simp [mass]

lemma mass_append (ss tt : List (Tableau × ℚ)) (target : Tableau) :
    mass (ss ++ tt) target = mass ss target + mass tt target := by
  simp [mass, List.map_append, List.sum_append]

lemma supported_step {tabs : List Tableau} (i : Nat) (s : Tableau × ℚ)
    (hs : s.1 ∈ tabs) : Supported tabs (seminormalStep tabs i s) := by
  intro t ht
  simp only [seminormalStep, List.mem_append, List.mem_singleton] at ht
  rcases ht with ht | ht
  · simpa [ht] using hs
  · split_ifs at ht with h
    · have ht' := List.mem_singleton.mp ht
      rw [ht']
      exact List.contains_iff_mem.mp h
    · simp at ht

lemma supported_flatMap {tabs : List Tableau} (i : Nat)
    {states : List (Tableau × ℚ)} (hs : Supported tabs states) :
    Supported tabs (states.flatMap (seminormalStep tabs i)) := by
  intro t ht
  obtain ⟨s, hss, hst⟩ := List.mem_flatMap.mp ht
  exact supported_step i s (hs s hss) t hst

lemma mass_step {tabs : List Tableau} (i : Nat) (s : Tableau × ℚ)
    (target : TableauBasis tabs) :
    mass (seminormalStep tabs i s) target.val =
      seminormalEntry i target.val s.1 * s.2 := by
  have hmem := basis_mem target
  have hst : (s.1 = target.val) ↔ (target.val = s.1) := eq_comm
  have hvt : (swapAdjacent s.1 i = target.val) ↔ (target.val = swapAdjacent s.1 i) := eq_comm
  simp only [seminormalStep, mass, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  by_cases hv : swapAdjacent s.1 i ∈ tabs
  · simp [hv, seminormalEntry, axialGap, div_eq_mul_inv]
    simp only [hst, hvt]
    split_ifs <;> ring
  · have hne : target.val ≠ swapAdjacent s.1 i := by
      intro h
      exact hv (h ▸ hmem)
    simp [hv, seminormalEntry, axialGap, hne, div_eq_mul_inv]
    simp only [hst, hvt]
    split_ifs <;> ring

lemma basis_sum_mass {tabs : List Tableau} (f : Tableau → ℚ)
    (states : List (Tableau × ℚ)) (hs : Supported tabs states) :
    (∑ t : TableauBasis tabs, f t.val * mass states t.val) =
      (states.map fun s => f s.1 * s.2).sum := by
  classical
  induction states with
  | nil => simp [mass]
  | cons s ss ih =>
    have hsmem := hs s (by simp)
    have htail : Supported tabs ss := fun t ht => hs t (by simp [ht])
    have hi := ih htail
    let b : TableauBasis tabs := ⟨s.1, List.mem_toFinset.mpr hsmem⟩
    have hdelta : (∑ t : TableauBasis tabs, f t.val * (if s.1 = t.val then s.2 else 0)) =
        f s.1 * s.2 := by
      change (∑ t : TableauBasis tabs, f t.val * (if b.val = t.val then s.2 else 0)) = _
      simp only [← Subtype.ext_iff, mul_ite, mul_zero]
      simp [b]
    simp only [mass_cons, mul_add, Finset.sum_add_distrib,
      List.map_cons, List.sum_cons]
    rw [hdelta, hi]

lemma mass_flatMap {tabs : List Tableau} (i : Nat)
    (states : List (Tableau × ℚ)) (target : TableauBasis tabs) :
    mass (states.flatMap (seminormalStep tabs i)) target.val =
      (states.map fun s => seminormalEntry i target.val s.1 * s.2).sum := by
  induction states with
  | nil => simp [mass]
  | cons s ss ih =>
    simp only [List.flatMap_cons, mass_append, mass_step, List.map_cons, List.sum_cons]
    rw [ih]

lemma stateVector_step {tabs : List Tableau} (i : Nat)
    (states : List (Tableau × ℚ)) (hs : Supported tabs states) :
    stateVector tabs (states.flatMap (seminormalStep tabs i)) =
      (seminormalMatrix tabs i) *ᵥ stateVector tabs states := by
  funext target
  simp only [stateVector, Matrix.mulVec, dotProduct, seminormalMatrix]
  rw [mass_flatMap, basis_sum_mass _ states hs]

/-- Execute the rightmost generator first, retaining every path contribution. -/
def runWord (tabs : List Tableau) (word : List Nat)
    (states : List (Tableau × ℚ)) : List (Tableau × ℚ) :=
  word.foldr (fun i ss => ss.flatMap (seminormalStep tabs i)) states

lemma runWord_eq_reverse_foldl (tabs : List Tableau) (word : List Nat)
    (states : List (Tableau × ℚ)) :
    runWord tabs word states =
      word.reverse.foldl (fun ss i => ss.flatMap (seminormalStep tabs i)) states := by
  simp [runWord, List.foldl_reverse]

lemma supported_runWord {tabs : List Tableau} (word : List Nat)
    (states : List (Tableau × ℚ)) (hs : Supported tabs states) :
    Supported tabs (runWord tabs word states) := by
  induction word with
  | nil => simpa [runWord] using hs
  | cons i word ih =>
    exact supported_flatMap i ih

lemma stateVector_runWord {tabs : List Tableau} (word : List Nat)
    (states : List (Tableau × ℚ)) (hs : Supported tabs states) :
    stateVector tabs (runWord tabs word states) =
      wordMatrix tabs word *ᵥ stateVector tabs states := by
  induction word with
  | nil => simp [runWord, wordMatrix]
  | cons i word ih =>
    change stateVector tabs ((runWord tabs word states).flatMap (seminormalStep tabs i)) = _
    rw [stateVector_step i _ (supported_runWord word states hs), ih]
    simp [wordMatrix, Matrix.mulVec_mulVec]

lemma mass_runWord_return {tabs : List Tableau} (word : List Nat)
    (t : TableauBasis tabs) :
    mass (runWord tabs word [(t.val, 1)]) t.val = wordMatrix tabs word t t := by
  classical
  have hs : Supported tabs [(t.val, 1)] := by
    intro s hs
    simp only [List.mem_singleton] at hs
    simpa [hs] using basis_mem t
  change stateVector tabs (runWord tabs word [(t.val, 1)]) t = _
  rw [stateVector_runWord word _ hs]
  simp only [Matrix.mulVec, dotProduct, stateVector, mass,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    beq_iff_eq, mul_ite, mul_one, mul_zero, ← Subtype.ext_iff]
  simp

lemma list_sum_eq_basis_sum (tabs : List Tableau) (hn : tabs.Nodup) (f : Tableau → ℚ) :
    (tabs.map f).sum = ∑ t : TableauBasis tabs, f t.val := by
  rw [Finset.sum_coe_sort]
  exact (List.sum_toFinset f hn).symm

def pathTrace (tabs : List Tableau) (selector : Tableau → Bool) (word : List Nat) : ℚ :=
  (tabs.map fun t => if selector t then mass (runWord tabs word [(t, 1)]) t else 0).sum

lemma pathTrace_eq_matrixTrace (tabs : List Tableau) (hn : tabs.Nodup)
    (selector : Tableau → Bool) (word : List Nat) :
    pathTrace tabs selector word =
      Matrix.trace (Matrix.diagonal (fun t : TableauBasis tabs => if selector t.val then 1 else 0) *
        wordMatrix tabs word) := by
  classical
  unfold pathTrace
  rw [list_sum_eq_basis_sum tabs hn]
  simp only [Matrix.trace, Matrix.diagonal_mul]
  apply Finset.sum_congr rfl
  intro t ht
  rw [mass_runWord_return]
  split_ifs <;> simp_all

/-- The evaluator's list trace is an actual matrix trace, for any duplicate-free
skew-tableau basis. This theorem is independent of a representation-theoretic realization. -/
theorem traceWord_eq_matrixTrace (eta nu mu : Shape) (k : Nat) (word : List Nat)
    (hn : (tableaux eta nu).Nodup) :
    traceWord eta nu mu k word =
      Matrix.trace (prefixSelector (tableaux eta nu) eta mu k *
        wordMatrix (tableaux eta nu) word) := by
  have h := pathTrace_eq_matrixTrace (tableaux eta nu) hn
    (fun t => prefixShape eta t k == mu) word
  simpa [traceWord, pathTrace, runWord, List.foldl_reverse, mass, prefixSelector] using h

/-- Matrix whose trace is the one- or two-contraction coefficient calculated by
`Certificate.computedCoeff`. This definition makes no claim of PSD witness positivity. -/
def computedWitnessMatrix (w : Witness) (nu : Shape) :
    Matrix (TableauBasis (tableaux w.eta nu)) (TableauBasis (tableaux w.eta nu)) ℚ :=
  let tabs := tableaux w.eta nu
  if w.k = 1 then prefixSelector tabs w.eta w.mu 1 * wordMatrix tabs [0]
  else if w.k = 2 then
    (1 / 2 : ℚ) • (prefixSelector tabs w.eta w.mu 2 *
      (wordMatrix tabs [1, 0, 2, 1] + w.sign • wordMatrix tabs [2, 1, 0, 2, 1]))
  else 0

theorem computedCoeff_eq_matrixTrace (w : Witness) (nu : Shape)
    (hn : (tableaux w.eta nu).Nodup) :
    computedCoeff w nu = Matrix.trace (computedWitnessMatrix w nu) := by
  classical
  by_cases h1 : w.k = 1
  · simpa [computedCoeff, computedWitnessMatrix, h1] using
      traceWord_eq_matrixTrace w.eta nu w.mu 1 [0] hn
  · by_cases h2 : w.k = 2
    · simp only [computedCoeff, computedWitnessMatrix, if_neg h1, if_pos h2]
      rw [traceWord_eq_matrixTrace w.eta nu w.mu 2 [1, 0, 2, 1] hn,
        traceWord_eq_matrixTrace w.eta nu w.mu 2 [2, 1, 0, 2, 1] hn]
      simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_add, smul_eq_mul]
      ring
    · simp [computedCoeff, computedWitnessMatrix, h1, h2]

end LiebBridge.Young.TraceSemantics
