import Bridge.Young.ContentSeparation

/-!
# Content sequences separate different Young shapes

The prefix argument is carried out on actual grid cells of two possibly different diagrams.
When two equal-content cells are comparable, the lower-set property places the earlier cell
inside the other diagram, so the common-prefix hypothesis applies there.
-/

namespace LiebBridge.Young.CrossShapeSeparation

open StandardTableau

variable {eta nu : YoungDiagram}

theorem coordinates_comparable_of_content (a b : ℕ × ℕ)
    (h : boxContent a = boxContent b) : a ≤ b ∨ b ≤ a := by
  change (a.1 ≤ b.1 ∧ a.2 ≤ b.2) ∨ (b.1 ≤ a.1 ∧ b.2 ≤ a.2)
  unfold boxContent at h
  omega

/-- At the same prefix, equal next contents force equal next cells across different diagrams. -/
theorem entry_coordinates_eq_of_prefix (hcard : eta.card = nu.card)
    (t : StandardTableau eta) (u : StandardTableau nu) (i : Fin eta.card)
    (hp : ∀ j : Fin eta.card, j < i →
      (t.entry j).val = (u.entry (Fin.cast hcard j)).val)
    (hc : t.rationalContent i = u.rationalContent (Fin.cast hcard i)) :
    (t.entry i).val = (u.entry (Fin.cast hcard i)).val := by
  classical
  have hc' : boxContent (t.entry i).val = boxContent (u.entry (Fin.cast hcard i)).val := by
    unfold rationalContent at hc
    exact_mod_cast hc
  by_contra hn
  obtain h | h := coordinates_comparable_of_content _ _ hc'
  · have ha : (t.entry i).val ∈ nu.cells :=
      nu.isLowerSet h (u.entry (Fin.cast hcard i)).property
    let a : Cell nu := ⟨(t.entry i).val,ha⟩
    have hlt : a < u.entry (Fin.cast hcard i) :=
      lt_of_le_of_ne h (fun he => hn (congrArg Subtype.val he))
    have hk : u.number a < Fin.cast hcard i := by
      simpa only [number_entry] using u.number_lt _ _ hlt
    let k : Fin eta.card := Fin.cast hcard.symm (u.number a)
    have hki : k < i := by change (u.number a).val < i.val; exact hk
    have he : (t.entry k).val = (t.entry i).val := by
      rw [hp k hki]
      simp [k,a]
    have heq : k = i := t.number.symm.injective (Subtype.ext he)
    exact (ne_of_lt hki) heq
  · have hb : (u.entry (Fin.cast hcard i)).val ∈ eta.cells :=
      eta.isLowerSet h (t.entry i).property
    let b : Cell eta := ⟨(u.entry (Fin.cast hcard i)).val,hb⟩
    have hlt : b < t.entry i :=
      lt_of_le_of_ne h (fun he => hn (congrArg Subtype.val he).symm)
    have hk : t.number b < i := by simpa only [number_entry] using t.number_lt _ _ hlt
    have he : (u.entry (Fin.cast hcard (t.number b))).val =
        (u.entry (Fin.cast hcard i)).val := by
      rw [← hp (t.number b) hk, entry_number]
    have heq := u.number.symm.injective (Subtype.ext he)
    have hv := congrArg Fin.val heq
    simp only [Fin.coe_cast] at hv
    exact (ne_of_lt hk) (Fin.ext hv)

/-- Equal entire content sequences imply equality of every aligned numbered cell. -/
theorem entry_coordinates_eq_of_contents (hcard : eta.card = nu.card)
    (t : StandardTableau eta) (u : StandardTableau nu)
    (hc : ∀ i : Fin eta.card, t.rationalContent i = u.rationalContent (Fin.cast hcard i)) :
    ∀ i : Fin eta.card, (t.entry i).val = (u.entry (Fin.cast hcard i)).val := by
  have hprefix : ∀ n : ℕ, ∀ i : Fin eta.card, i.val < n →
      (t.entry i).val = (u.entry (Fin.cast hcard i)).val := by
    intro n
    induction n with
    | zero => intro i hi; omega
    | succ n ih =>
      intro i hi
      by_cases hn : i.val < n
      · exact ih i hn
      · exact entry_coordinates_eq_of_prefix hcard t u i (fun j hj => ih j (by omega)) (hc i)
  intro i
  exact hprefix eta.card i i.isLt

/-- The content sequence determines the Young shape as well as the tableau. -/
theorem shape_eq_of_contents (hcard : eta.card = nu.card)
    (t : StandardTableau eta) (u : StandardTableau nu)
    (hc : ∀ i : Fin eta.card, t.rationalContent i = u.rationalContent (Fin.cast hcard i)) :
    eta = nu := by
  have he := entry_coordinates_eq_of_contents hcard t u hc
  apply YoungDiagram.ext
  ext b
  constructor
  · intro hb
    have hh := he (t.number ⟨b,hb⟩)
    simp only [entry_number] at hh
    rw [hh]
    exact (u.entry (Fin.cast hcard (t.number ⟨b,hb⟩))).property
  · intro hb
    let j := u.number (⟨b,hb⟩ : Cell nu)
    have hh := he (Fin.cast hcard.symm j)
    have hv : (u.entry (Fin.cast hcard (Fin.cast hcard.symm j))).val = b := by simp [j]
    rw [hv] at hh
    rw [← hh]
    exact (t.entry (Fin.cast hcard.symm j)).property

/-- Full equality in the family of all standard tableaux, allowing different initial shapes. -/
theorem sigma_eq_of_contents (hcard : eta.card = nu.card)
    (t : StandardTableau eta) (u : StandardTableau nu)
    (hc : ∀ i : Fin eta.card, t.rationalContent i = u.rationalContent (Fin.cast hcard i)) :
    (⟨eta,t⟩ : Σ d : YoungDiagram, StandardTableau d) = ⟨nu,u⟩ := by
  have hs := shape_eq_of_contents hcard t u hc
  subst nu
  have ht : t = u := eq_of_rationalContent t u (by simpa using hc)
  subst u
  rfl

/-- Every pair of tableaux of distinct equally-sized shapes differs in some content coordinate. -/
theorem exists_content_ne (hcard : eta.card = nu.card) (hne : eta ≠ nu)
    (t : StandardTableau eta) (u : StandardTableau nu) :
    ∃ i : Fin eta.card, t.rationalContent i ≠ u.rationalContent (Fin.cast hcard i) := by
  classical
  by_contra! hh
  exact hne (shape_eq_of_contents hcard t u hh)

/-- The same cross-shape separation persists over every characteristic-zero field. -/
theorem exists_cast_content_ne {K : Type*} [Field K] [CharZero K]
    (hcard : eta.card = nu.card) (hne : eta ≠ nu)
    (t : StandardTableau eta) (u : StandardTableau nu) :
    ∃ i : Fin eta.card, (t.rationalContent i : K) ≠
      (u.rationalContent (Fin.cast hcard i) : K) := by
  obtain ⟨i,hi⟩ := exists_content_ne hcard hne t u
  refine ⟨i, ?_⟩
  exact_mod_cast hi

end LiebBridge.Young.CrossShapeSeparation
