import Bridge.Young.NumberingFlags
import Bridge.Young.LocalBraid
import Bridge.Young.TriangularCompression

/-! The concrete rational matrices on all numberings preserve the two Young
diagram flags. The braid theorem below is columnwise: three contents in the
source column must be pairwise distinct. No global braid is asserted for all
numberings when equal contents occur. -/

noncomputable section
namespace LiebBridge.Young.AmbientBraid
open scoped BigOperators Matrix
attribute [local instance] Classical.propDecidable
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def numberingMatrix {d : YoungDiagram} (i j : Fin d.card) :
    Matrix (Numbering d) (Numbering d) ℚ := by
  classical
  exact fun target source =>
    (if target = source then 1 / numberingGap source i j else 0) +
      (if target = numberingSwap source i j then 1 + 1 / numberingGap source i j else 0)

theorem numberingMatrix_preservesFlag {d : YoungDiagram} (i j : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) :
    TriangularCompression.PreservesFlag ColumnIncreasing RowIncreasing (numberingMatrix i j) := by
  classical
  constructor
  · intro target source hc hbad
    have hne : target ≠ source := by intro h; exact hbad (h ▸ hc)
    by_cases hsw : target = numberingSwap source i j
    · have hg := column_exit_gap source i j hij hc (hsw ▸ hbad)
      simp only [numberingMatrix, if_neg hne, if_pos hsw, hg]
      norm_num
    · simp [numberingMatrix, hne, hsw]
  · intro target source htC htR hsC hsR
    have hne : target ≠ source := by intro h; exact hsR (h ▸ htR)
    by_cases hsw : target = numberingSwap source i j
    · have hg := row_reentry_gap source i j hij hsR (hsw ▸ htR)
      simp only [numberingMatrix, if_neg hne, if_pos hsw, hg]
      norm_num
    · simp [numberingMatrix, hne, hsw]

def numberingContent {d : YoungDiagram} (e : Numbering d) (i : Fin d.card) : ℚ :=
  boxContent (e.symm i).val

/-- The six orders `abc, bac, acb, cab, bca, cba`, realized as actual numberings. -/
def orbit {d : YoungDiagram} (e : Numbering d) (i j k : Fin d.card) : Fin 6 → Numbering d :=
  ![e, numberingSwap e i j, numberingSwap e j k,
    numberingSwap (numberingSwap e j k) i j,
    numberingSwap (numberingSwap e i j) j k,
    numberingSwap (numberingSwap (numberingSwap e j k) i j) j k]

theorem orbit_swap1 {d : YoungDiagram} (e : Numbering d) (i j k : Fin d.card)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (r : Fin 6) :
    numberingSwap (orbit e i j k r) i j = orbit e i j k (LocalBraid.swap1 r) := by
  fin_cases r <;> ext x <;>
    by_cases hi : e x = i <;> by_cases hj : e x = j <;> by_cases hk : e x = k <;>
    simp_all [orbit, LocalBraid.swap1, numberingSwap, Equiv.swap_apply_def,
      hij.symm, hik.symm, hjk.symm]

theorem orbit_swap2 {d : YoungDiagram} (e : Numbering d) (i j k : Fin d.card)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (r : Fin 6) :
    numberingSwap (orbit e i j k r) j k = orbit e i j k (LocalBraid.swap2 r) := by
  fin_cases r <;> ext x <;>
    by_cases hi : e x = i <;> by_cases hj : e x = j <;> by_cases hk : e x = k <;>
    simp_all [orbit, LocalBraid.swap2, numberingSwap, Equiv.swap_apply_def,
      hij.symm, hik.symm, hjk.symm]

theorem orbit_gap1 {d : YoungDiagram} (e : Numbering d) (i j k : Fin d.card)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (r : Fin 6) :
    numberingGap (orbit e i j k r) i j =
      LocalBraid.gap1 (numberingContent e i) (numberingContent e j) (numberingContent e k) r := by
  fin_cases r <;>
    simp [orbit, LocalBraid.gap1, numberingGap, numberingSwap, numberingContent,
      hij, hik, hjk, hij.symm, hik.symm, hjk.symm, Equiv.swap_apply_def]

theorem orbit_gap2 {d : YoungDiagram} (e : Numbering d) (i j k : Fin d.card)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (r : Fin 6) :
    numberingGap (orbit e i j k r) j k =
      LocalBraid.gap2 (numberingContent e i) (numberingContent e j) (numberingContent e k) r := by
  fin_cases r <;>
    simp [orbit, LocalBraid.gap2, numberingGap, numberingSwap, numberingContent,
      hij, hik, hjk, hij.symm, hik.symm, hjk.symm, Equiv.swap_apply_def]

def orbitInclusion {d : YoungDiagram} (e : Numbering d) (i j k : Fin d.card) :
    Matrix (Numbering d) (Fin 6) ℚ := by
  classical
  exact fun target r => if target = orbit e i j k r then 1 else 0

theorem mul_orbitInclusion {d : YoungDiagram} (e : Numbering d) (i j k : Fin d.card)
    (M : Matrix (Numbering d) (Numbering d) ℚ) (target : Numbering d) (r : Fin 6) :
    (M * orbitInclusion e i j k) target r = M target (orbit e i j k r) := by
  classical
  simp [Matrix.mul_apply, orbitInclusion]

theorem mul_adjacentMatrix {α : Type*} (E : Matrix α (Fin 6) ℚ)
    (swap : Fin 6 → Fin 6) (gap : Fin 6 → ℚ) (target : α) (r : Fin 6) :
    (E * LocalBraid.adjacentMatrix swap gap) target r =
      E target r * (1 / gap r) + E target (swap r) * (1 + 1 / gap r) := by
  simp [Matrix.mul_apply, LocalBraid.adjacentMatrix, mul_add,
    Finset.sum_add_distrib, mul_ite]

theorem intertwine1 {d : YoungDiagram} (e : Numbering d) (i j k : Fin d.card)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    numberingMatrix i j * orbitInclusion e i j k =
      orbitInclusion e i j k *
        LocalBraid.s1 (numberingContent e i) (numberingContent e j) (numberingContent e k) := by
  classical
  ext target r
  rw [mul_orbitInclusion]
  unfold LocalBraid.s1
  rw [mul_adjacentMatrix]
  simp only [numberingMatrix, orbitInclusion, orbit_gap1 e i j k hij hik hjk,
    orbit_swap1 e i j k hij hik hjk, ite_mul, one_mul, zero_mul]

theorem intertwine2 {d : YoungDiagram} (e : Numbering d) (i j k : Fin d.card)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    numberingMatrix j k * orbitInclusion e i j k =
      orbitInclusion e i j k *
        LocalBraid.s2 (numberingContent e i) (numberingContent e j) (numberingContent e k) := by
  classical
  ext target r
  rw [mul_orbitInclusion]
  unfold LocalBraid.s2
  rw [mul_adjacentMatrix]
  simp only [numberingMatrix, orbitInclusion, orbit_gap2 e i j k hij hik hjk,
    orbit_swap2 e i j k hij hik hjk, ite_mul, one_mul, zero_mul]

/-- The braid holds on a source column whose three local contents are distinct.
The proof intertwines the actual six numbering columns with the universal
six-order rational matrices. -/
theorem numberingMatrix_braid_column {d : YoungDiagram} (e : Numbering d)
    (i j k : Fin d.card) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hab : numberingContent e i ≠ numberingContent e j)
    (hac : numberingContent e i ≠ numberingContent e k)
    (hbc : numberingContent e j ≠ numberingContent e k) (target : Numbering d) :
    (numberingMatrix i j * numberingMatrix j k * numberingMatrix i j) target e =
      (numberingMatrix j k * numberingMatrix i j * numberingMatrix j k) target e := by
  classical
  let E := orbitInclusion e i j k
  let S1 := LocalBraid.s1 (numberingContent e i) (numberingContent e j) (numberingContent e k)
  let S2 := LocalBraid.s2 (numberingContent e i) (numberingContent e j) (numberingContent e k)
  have h1 : numberingMatrix i j * E = E * S1 := intertwine1 e i j k hij hik hjk
  have h2 : numberingMatrix j k * E = E * S2 := intertwine2 e i j k hij hik hjk
  have hb : S1 * S2 * S1 = S2 * S1 * S2 := LocalBraid.braid _ _ _ hab hac hbc
  have hleft : (numberingMatrix i j * numberingMatrix j k * numberingMatrix i j) * E =
      E * (S1 * S2 * S1) := by
    calc
      _ = numberingMatrix i j * (numberingMatrix j k * (numberingMatrix i j * E)) := by
        simp only [Matrix.mul_assoc]
      _ = numberingMatrix i j * (numberingMatrix j k * (E * S1)) := by rw [h1]
      _ = numberingMatrix i j * ((numberingMatrix j k * E) * S1) := by rw [Matrix.mul_assoc]
      _ = numberingMatrix i j * ((E * S2) * S1) := by rw [h2]
      _ = (numberingMatrix i j * E) * (S2 * S1) := by simp only [Matrix.mul_assoc]
      _ = (E * S1) * (S2 * S1) := by rw [h1]
      _ = E * (S1 * S2 * S1) := by simp only [Matrix.mul_assoc]
  have hright : (numberingMatrix j k * numberingMatrix i j * numberingMatrix j k) * E =
      E * (S2 * S1 * S2) := by
    calc
      _ = numberingMatrix j k * (numberingMatrix i j * (numberingMatrix j k * E)) := by
        simp only [Matrix.mul_assoc]
      _ = numberingMatrix j k * (numberingMatrix i j * (E * S2)) := by rw [h2]
      _ = numberingMatrix j k * ((numberingMatrix i j * E) * S2) := by rw [Matrix.mul_assoc]
      _ = numberingMatrix j k * ((E * S1) * S2) := by rw [h1]
      _ = (numberingMatrix j k * E) * (S1 * S2) := by simp only [Matrix.mul_assoc]
      _ = (E * S2) * (S1 * S2) := by rw [h2]
      _ = E * (S2 * S1 * S2) := by simp only [Matrix.mul_assoc]
  have hprod : (numberingMatrix i j * numberingMatrix j k * numberingMatrix i j) * E =
      (numberingMatrix j k * numberingMatrix i j * numberingMatrix j k) * E := by
    rw [hleft, hright, hb]
  have hentry := congrArg (fun M => M target (0 : Fin 6)) hprod
  simpa only [E, mul_orbitInclusion, orbit, Matrix.cons_val_zero] using hentry

theorem numberingContent_ne_of_strictMono {d : YoungDiagram} (e : Numbering d)
    (he : StrictMono e) (i j : Fin d.card) (hij : i < j)
    (hgap : (j : ℕ) ≤ (i : ℕ) + 2) : numberingContent e i ≠ numberingContent e j := by
  let t : StandardTableau d := ⟨e, he⟩
  have hz := t.content_ne_of_label_distance_le_two (t.entry i) (t.entry j)
    (by simpa using hij) (by simpa using hgap)
  intro h
  apply hz
  change (boxContent (e.symm i).val : ℚ) = (boxContent (e.symm j).val : ℚ) at h
  change boxContent (e.symm i).val = boxContent (e.symm j).val
  exact_mod_cast h

/-- The actual rational matrix restricted to the genuine standard-numbering
subquotient. Its basis is precisely the conjunction of the two local flags. -/
def compressedMatrix {d : YoungDiagram} (i j : Fin d.card) :
    Matrix (TriangularCompression.Retained (@ColumnIncreasing d) RowIncreasing)
      (TriangularCompression.Retained (@ColumnIncreasing d) RowIncreasing) ℚ :=
  TriangularCompression.compress ColumnIncreasing RowIncreasing (numberingMatrix i j)

/-- The concrete standard-numbering matrices satisfy the adjacent braid.
Flag preservation removes intermediate nonstandard numberings; genuine Young
diagram geometry discharges the only content-distinctness requirement. -/
theorem compressed_braid {d : YoungDiagram} (i j k : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) (hjk : (k : ℕ) = (j : ℕ) + 1) :
    compressedMatrix i j * compressedMatrix j k * compressedMatrix i j =
      compressedMatrix j k * compressedMatrix i j * compressedMatrix j k := by
  have h1 := numberingMatrix_preservesFlag i j hij
  have h2 := numberingMatrix_preservesFlag j k hjk
  unfold compressedMatrix
  rw [← TriangularCompression.compress_mul ColumnIncreasing RowIncreasing h1 h2,
    ← TriangularCompression.compress_mul ColumnIncreasing RowIncreasing h2 h1,
    ← TriangularCompression.compress_mul ColumnIncreasing RowIncreasing
      (TriangularCompression.preservesFlag_mul ColumnIncreasing RowIncreasing h1 h2) h1,
    ← TriangularCompression.compress_mul ColumnIncreasing RowIncreasing
      (TriangularCompression.preservesFlag_mul ColumnIncreasing RowIncreasing h2 h1) h2]
  ext target source
  change (numberingMatrix i j * numberingMatrix j k * numberingMatrix i j) target.val source.val =
    (numberingMatrix j k * numberingMatrix i j * numberingMatrix j k) target.val source.val
  have he : StrictMono source.val := (strictMono_iff_flags source.val).mpr source.property
  apply numberingMatrix_braid_column source.val i j k (by omega) (by omega) (by omega)
  · exact numberingContent_ne_of_strictMono source.val he i j (by omega) (by omega)
  · exact numberingContent_ne_of_strictMono source.val he i k (by omega) (by omega)
  · exact numberingContent_ne_of_strictMono source.val he j k (by omega) (by omega)

end LiebBridge.Young.AmbientBraid
