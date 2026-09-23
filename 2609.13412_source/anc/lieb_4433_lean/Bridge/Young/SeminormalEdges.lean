import Bridge.Young.Seminormal
import Bridge.Young.TableauConnectivity

/-! The edges in the standard-tableau graph carry nonzero coefficients in the
actual seminormal operators. This includes the source/target sign conversion. -/

namespace LiebBridge.Young.StandardTableau

variable {d : YoungDiagram}

noncomputable local instance : DecidableEq (StandardTableau d) := Classical.decEq _

theorem axial_ne_one_and_neg_one (t : StandardTableau d) (i j : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) (hs : ¬ t.entry i ≤ t.entry j) :
    t.axial i j ≠ 1 ∧ t.axial i j ≠ -1 := by
  have h := (t.consecutive_incomparable_iff (t.entry i) (t.entry j)
    (by simpa only [number_entry] using hij)).mp hs
  unfold axial rationalContent
  exact_mod_cast h

theorem adjacentSwap_ne (t : StandardTableau d) (i j : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) (hs : ¬ t.entry i ≤ t.entry j) :
    t.adjacentSwap i j hij ≠ t := by
  intro h
  have he := congrArg (fun v : StandardTableau d => v.entry i) h
  change (t.adjacentSwap i j hij).entry i = t.entry i at he
  rw [adjacentSwap_of_allowed _ _ _ _ hs, swapAllowed_entry,
    Equiv.swap_apply_left] at he
  have hh := t.number.symm.injective he
  omega

theorem generator_allowed_coefficient (t : StandardTableau d) (i j : Fin d.card)
    (hij : (j : ℕ) = (i : ℕ) + 1) (hs : ¬ t.entry i ≤ t.entry j) :
    generator i j hij (Pi.single t 1) (t.adjacentSwap i j hij) =
      1 + (t.axial i j)⁻¹ := by
  classical
  have hss := t.adjacentSwap_allowed i j hij hs
  have hn := t.adjacentSwap_ne i j hij hs
  simp only [generator_apply, if_pos hss, Pi.single_apply, if_neg hn,
    adjacentSwap_involutive i j hij t, if_pos rfl, mul_zero, mul_one, zero_add,
    axial_adjacentSwap _ _ _ _ hs, inv_neg, sub_neg_eq_add]
  simp

theorem generator_allowed_coefficient_ne_zero (t : StandardTableau d)
    (i j : Fin d.card) (hij : (j : ℕ) = (i : ℕ) + 1)
    (hs : ¬ t.entry i ≤ t.entry j) :
    generator i j hij (Pi.single t 1) (t.adjacentSwap i j hij) ≠ 0 := by
  rw [generator_allowed_coefficient _ _ _ _ hs]
  have hd := t.axial_ne_zero i j hij
  have hn := (t.axial_ne_one_and_neg_one i j hij hs).2
  intro h
  have he := congrArg (fun a : ℚ => a * t.axial i j) h
  simp only [add_mul, one_mul, inv_mul_cancel₀ hd, zero_mul] at he
  exact hn (by linarith only [he])

end LiebBridge.Young.StandardTableau
