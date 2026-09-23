import Bridge.Young.WitnessShapes
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Multiset.Sort

/-! The number of conjugacy classes of `S₁₄` is at most 135.
We use conjugacy classification by cycle partition only in its injective direction,
then the already established exhaustive certificate partition list. -/

noncomputable section
namespace LiebBridge.Young.ConjugacyBound
open LiebBridge.Certificate

abbrev Shape14 := {p : Shape // IsPartition14 p}
abbrev S14 := Equiv.Perm (Fin 14)

instance shape14Fintype : Fintype Shape14 :=
  Fintype.ofFinset partitions14.toFinset (fun p => by
    simpa only [List.mem_toFinset] using mem_partitions14_iff p)

theorem card_shape14 : Fintype.card Shape14 = 135 := by
  have h : Fintype.card Shape14 = partitions14.toFinset.card :=
    Fintype.card_ofFinset (p := {p | IsPartition14 p}) partitions14.toFinset (fun p => by
    simpa only [List.mem_toFinset] using mem_partitions14_iff p)
  rw [h, List.toFinset_card_of_nodup partitions14_nodup, partitions14_length]

def partitionShape (p : Nat.Partition 14) : Shape14 :=
  ⟨p.parts.sort (· ≥ ·), by
    refine ⟨?_, Multiset.sort_sorted _ _, ?_⟩
    · have hs := p.parts_sum
      rw [← Multiset.sort_eq (· ≥ ·) p.parts, Multiset.sum_coe] at hs
      exact hs
    · intro a ha
      exact p.parts_pos ((Multiset.mem_sort _).mp ha)⟩

theorem partitionShape_injective : Function.Injective partitionShape := by
  intro p q h
  apply Nat.Partition.ext
  have hh := congrArg (fun s : Shape14 => (s.val : Multiset ℕ)) h
  simpa only [partitionShape, Multiset.sort_eq] using hh

def permutationPartition (g : S14) : Nat.Partition 14 where
  parts := g.partition.parts
  parts_pos := g.partition.parts_pos
  parts_sum := by simpa only [Fintype.card_fin] using g.partition.parts_sum

theorem permutationPartition_eq_iff (g h : S14) :
    permutationPartition g = permutationPartition h ↔ IsConj g h := by
  rw [Equiv.Perm.partition_eq_of_isConj, Nat.Partition.ext_iff, Nat.Partition.ext_iff]
  rfl

def conjugacyShape : ConjClasses S14 → Shape14 :=
  Quotient.lift (fun g => partitionShape (permutationPartition g)) (by
    intro g h hconj
    exact congrArg partitionShape ((permutationPartition_eq_iff g h).mpr hconj))

theorem conjugacyShape_injective : Function.Injective conjugacyShape := by
  intro c d
  refine Quotient.inductionOn₂ c d ?_
  intro g h hgh
  apply Quotient.sound
  exact (permutationPartition_eq_iff g h).mp (partitionShape_injective hgh)

theorem card_conjClasses_le : Nat.card (ConjClasses S14) ≤ 135 := by
  have h := Nat.card_le_card_of_injective conjugacyShape conjugacyShape_injective
  simpa only [Nat.card_eq_fintype_card, card_shape14] using h

end LiebBridge.Young.ConjugacyBound
