import Bridge.Young.Seminormal

/-! Distinct standard tableaux have distinct content sequences. This is proved
from their actual increasing numberings, without dimension or character facts. -/

namespace LiebBridge.Young
namespace StandardTableau

variable {d : YoungDiagram}

theorem comparable_of_same_content (a b : Cell d)
    (h : boxContent a.1 = boxContent b.1) : a ≤ b ∨ b ≤ a := by
  change (a.1.1 ≤ b.1.1 ∧ a.1.2 ≤ b.1.2) ∨
    (b.1.1 ≤ a.1.1 ∧ b.1.2 ≤ a.1.2)
  unfold boxContent at h
  omega

/-- At a fixed prefix, the next content determines the next cell uniquely. -/
theorem entry_eq_of_prefix_and_content (t u : StandardTableau d) (i : Fin d.card)
    (hp : ∀ j : Fin d.card, j < i → t.entry j = u.entry j)
    (hc : t.rationalContent i = u.rationalContent i) : t.entry i = u.entry i := by
  classical
  have hc' : boxContent (t.entry i).1 = boxContent (u.entry i).1 := by
    unfold rationalContent at hc
    exact_mod_cast hc
  by_contra hn
  obtain h | h := comparable_of_same_content (t.entry i) (u.entry i) hc'
  · have hlt : t.entry i < u.entry i := lt_of_le_of_ne h hn
    have hk : u.number (t.entry i) < i := by
      simpa only [number_entry] using u.number_lt _ _ hlt
    have he := (hp (u.number (t.entry i)) hk).trans (u.entry_number (t.entry i))
    have hki : u.number (t.entry i) = i := t.number.symm.injective he
    omega
  · have hlt : u.entry i < t.entry i := lt_of_le_of_ne h (Ne.symm hn)
    have hk : t.number (u.entry i) < i := by
      simpa only [number_entry] using t.number_lt _ _ hlt
    have he := (hp (t.number (u.entry i)) hk).symm.trans (t.entry_number (u.entry i))
    have hki : t.number (u.entry i) = i := u.number.symm.injective he
    omega

/-- The joint eigenvalue tuple of the content diagonals separates the genuine
standard-tableau basis. -/
theorem eq_of_rationalContent (t u : StandardTableau d)
    (hc : ∀ i : Fin d.card, t.rationalContent i = u.rationalContent i) : t = u := by
  have hprefix : ∀ n : ℕ, ∀ i : Fin d.card, (i : ℕ) < n → t.entry i = u.entry i := by
    intro n
    induction n with
    | zero => intro i hi; omega
    | succ n ih =>
      intro i hi
      by_cases hn : (i : ℕ) < n
      · exact ih i hn
      · apply entry_eq_of_prefix_and_content t u i
        · intro j hj
          exact ih j (by omega)
        · exact hc i
  apply ext
  apply Equiv.ext
  intro b
  have he := hprefix d.card (t.number b) (t.number b).isLt
  have hu := congrArg u.number he
  simp only [entry_number, number_entry] at hu
  exact hu.symm

theorem exists_content_ne {t u : StandardTableau d} (htu : t ≠ u) :
    ∃ i : Fin d.card, t.rationalContent i ≠ u.rationalContent i := by
  classical
  by_contra h
  apply htu
  apply eq_of_rationalContent
  simpa only [not_exists, not_not] using h

end StandardTableau
end LiebBridge.Young
