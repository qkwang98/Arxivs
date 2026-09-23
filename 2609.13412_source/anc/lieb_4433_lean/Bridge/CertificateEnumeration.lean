import Bridge.CertificateAlgorithm

namespace LiebBridge.Certificate

def IsPartition14 (p : Shape) : Prop :=
  p.sum = 14 ∧ p.Pairwise (fun a b => b ≤ a) ∧ ∀ a ∈ p, 0 < a

theorem positive_length_le_sum (p : Shape) (hp : ∀ a ∈ p, 0 < a) :
    p.length ≤ p.sum := by
  induction p with
  | nil => simp
  | cons a p ih =>
    have ha := hp a (by simp)
    have ht : ∀ b ∈ p, 0 < b := fun b hb => hp b (by simp [hb])
    have hi := ih ht
    simp only [List.length_cons, List.sum_cons]
    omega

theorem entry_le_sum (p : Shape) (a : Nat) (ha : a ∈ p) : a ≤ p.sum := by
  induction p with
  | nil => simp at ha
  | cons b p ih =>
    simp only [List.mem_cons] at ha
    simp only [List.sum_cons]
    rcases ha with rfl | ha
    · omega
    · have hi := ih ha
      omega

theorem mem_partitionsAux_of_valid (fuel : Nat) (p : Shape) (cap : Nat)
    (hlen : p.length ≤ fuel)
    (hsort : p.Pairwise (fun a b => b ≤ a))
    (hpos : ∀ a ∈ p, 0 < a)
    (hcap : ∀ a ∈ p, a ≤ cap) :
    p ∈ partitionsAux fuel p.sum cap := by
  induction fuel generalizing p cap with
  | zero =>
    have hp : p = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    subst p
    simp [partitionsAux]
  | succ fuel ih =>
    cases p with
    | nil => simp [partitionsAux]
    | cons a p =>
      have ha : 0 < a := hpos a (by simp)
      have hacap : a ≤ cap := hcap a (by simp)
      have hnonzero : a + p.sum ≠ 0 := by omega
      have hlength : p.length ≤ fuel := by simpa using hlen
      have hsorttail := (List.pairwise_cons.mp hsort).2
      have hpostail : ∀ b ∈ p, 0 < b := fun b hb => hpos b (by simp [hb])
      have hcaptail : ∀ b ∈ p, b ≤ a := (List.pairwise_cons.mp hsort).1
      have hit := ih p a hlength hsorttail hpostail hcaptail
      have hminus : a - 1 + 1 = a := by omega
      simp only [List.sum_cons, partitionsAux, if_neg hnonzero, List.mem_flatMap]
      refine ⟨a - 1, ?_, ?_⟩
      · simp only [List.mem_reverse, List.mem_range]
        omega
      · have hsub : a + p.sum - (a - 1 + 1) = p.sum := by omega
        simp only [hminus, hsub]
        exact List.mem_map.mpr ⟨p, by simpa using hit, rfl⟩

theorem partitions14_complete (p : Shape) (hp : IsPartition14 p) :
    p ∈ partitions14 := by
  have hsum : p.sum = 14 := hp.1
  have hlen : p.length ≤ 14 := by
    have := positive_length_le_sum p hp.2.2
    omega
  have hcap : ∀ a ∈ p, a ≤ 14 := by
    intro a ha
    have := entry_le_sum p a ha
    omega
  have h := mem_partitionsAux_of_valid 14 p 14 hlen hp.2.1 hp.2.2 hcap
  simpa [partitions14, hp.1] using h

def isPartition14Check (p : Shape) : Bool :=
  decide (p.sum = 14) && decide (p.Pairwise (fun a b => b ≤ a)) &&
    p.all (fun a => decide (0 < a))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem partitions14_soundCheck :
    (partitions14.all isPartition14Check) = true := by decide +kernel

theorem partitions14_sound (p : Shape) (hp : p ∈ partitions14) : IsPartition14 p := by
  have h := List.all_eq_true.mp partitions14_soundCheck p hp
  simpa [isPartition14Check, IsPartition14, List.all_eq_true, and_assoc] using h

theorem mem_partitions14_iff (p : Shape) : p ∈ partitions14 ↔ IsPartition14 p :=
  ⟨partitions14_sound p, partitions14_complete p⟩

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem partitions14_nodup : partitions14.Nodup := by decide +kernel

end LiebBridge.Certificate
