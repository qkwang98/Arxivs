import Bridge.Young.TableauSwap
import Mathlib.Logic.Relation

/-! The graph of genuine standard tableaux under allowed adjacent swaps is
connected. The proof fixes an initial segment and moves the desired next cell
left one position at a time. Every swap is proved to preserve standardness. -/

namespace LiebBridge.Young.StandardTableau

variable {d : YoungDiagram}

def AllowedStep (t u : StandardTableau d) : Prop :=
  ∃ (i j : Fin d.card) (hij : (j : ℕ) = (i : ℕ) + 1),
    ¬ t.entry i ≤ t.entry j ∧ u = t.adjacentSwap i j hij

abbrev Reachable (t u : StandardTableau d) : Prop :=
  Relation.ReflTransGen AllowedStep t u

theorem number_ge_of_prefix (t u : StandardTableau d) (i : Fin d.card)
    (hp : ∀ k : Fin d.card, k < i → t.entry k = u.entry k) :
    i ≤ t.number (u.entry i) := by
  by_contra h
  have hj : t.number (u.entry i) < i := lt_of_not_ge h
  have he := (hp _ hj).symm.trans (t.entry_number (u.entry i))
  have hi : t.number (u.entry i) = i := u.number.symm.injective he
  omega

/-- Extend a matched prefix by one cell using only allowed swaps. -/
theorem match_next (t u : StandardTableau d) (i : Fin d.card)
    (hp : ∀ k : Fin d.card, k < i → t.entry k = u.entry k) :
    ∃ v : StandardTableau d, Reachable t v ∧
      ∀ k : Fin d.card, k ≤ i → v.entry k = u.entry k := by
  classical
  let j := t.number (u.entry i)
  have hge : i ≤ j := number_ge_of_prefix t u i hp
  by_cases hji : j = i
  · refine ⟨t, .refl, ?_⟩
    intro k hk
    rcases lt_or_eq_of_le hk with hk | hk
    · exact hp k hk
    · have h := t.entry_number (u.entry i)
      change t.entry j = u.entry i at h
      simpa only [hji, hk] using h
  · have hij : (i : ℕ) < j := by omega
    let p : Fin d.card := ⟨(j : ℕ) - 1, by omega⟩
    have hpj : (j : ℕ) = (p : ℕ) + 1 := by dsimp [p]; omega
    have hip : (i : ℕ) ≤ p := by omega
    have hjentry : t.entry j = u.entry i := t.entry_number (u.entry i)
    have hs : ¬ t.entry p ≤ t.entry j := by
      intro hab
      have hne : t.entry p ≠ t.entry j := by
        intro he
        have he' := t.number.symm.injective he
        omega
      have hlt := u.number_lt _ _ (lt_of_le_of_ne hab hne)
      rw [hjentry, number_entry] at hlt
      have he := (hp (u.number (t.entry p)) hlt).trans (u.entry_number (t.entry p))
      have hk : u.number (t.entry p) = p := t.number.symm.injective he
      omega
    let t' := t.adjacentSwap p j hpj
    have hprefix : ∀ k : Fin d.card, k < i → t'.entry k = u.entry k := by
      intro k hk
      change (t.adjacentSwap p j hpj).entry k = _
      rw [adjacentSwap_entry_other t p j hpj k (by intro h; subst k; omega)
        (by intro h; subst k; omega)]
      exact hp k hk
    have hnew : t'.number (u.entry i) = p := by
      change (t.adjacentSwap p j hpj).number (u.entry i) = p
      rw [adjacentSwap_of_allowed _ _ _ _ hs]
      change Equiv.swap p j j = p
      exact Equiv.swap_apply_right p j
    obtain ⟨v, hv, hvm⟩ := match_next t' u i hprefix
    exact ⟨v, .head ⟨p, j, hpj, hs, rfl⟩ hv, hvm⟩
termination_by (t.number (u.entry i) : ℕ)
decreasing_by
  change (t'.number (u.entry i) : ℕ) < (j : ℕ)
  rw [hnew]
  omega

/-- Any two standard tableaux of a fixed diagram are joined by allowed swaps. -/
theorem reachable (t u : StandardTableau d) : Reachable t u := by
  have hm : ∀ n : ℕ, n ≤ d.card → ∃ v : StandardTableau d,
      Reachable t v ∧ ∀ k : Fin d.card, (k : ℕ) < n → v.entry k = u.entry k := by
    intro n
    induction n with
    | zero => exact fun _ => ⟨t, .refl, by intro k hk; omega⟩
    | succ n ih =>
      intro hn
      obtain ⟨v, hv, hp⟩ := ih (by omega)
      let i : Fin d.card := ⟨n, by omega⟩
      obtain ⟨w, hw, hwp⟩ := match_next v u i hp
      refine ⟨w, hv.trans hw, ?_⟩
      intro k hk
      exact hwp k (by change (k : ℕ) ≤ n; omega)
  obtain ⟨v, hv, he⟩ := hm d.card le_rfl
  have hvu : v = u := by
    apply ext
    apply Equiv.ext
    intro b
    have h := congrArg u.number (he (v.number b) (v.number b).isLt)
    simp only [entry_number, number_entry] at h
    exact h.symm
  simpa only [hvu] using hv

end LiebBridge.Young.StandardTableau
