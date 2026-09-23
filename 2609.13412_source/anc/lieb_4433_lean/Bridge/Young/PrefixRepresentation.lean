import Bridge.Young.BranchingAction
import Bridge.Young.ScalarExtension

/-! The full embedded prefix symmetric group acts on the inner tableau
coordinate and fixes the skew coordinate.  The proof extends the actual
adjacent-generator calculation by the proved presentation of the actual
symmetric group.  No representation branching statement is assumed. -/

noncomputable section
namespace LiebBridge.Young.PrefixRepresentation

open BranchingBasis BranchingAction StandardTableau YoungRepresentation
open scoped BigOperators Classical

variable {eta nu : YoungDiagram} {m n : ℕ}

/-- Permute the initial labels and fix every label outside the prefix. -/
def prefixEmbedding (hm : m + 1 ≤ n + 1) :
    Equiv.Perm (Fin (m+1)) →* Equiv.Perm (Fin (n+1)) :=
  Equiv.Perm.viaEmbeddingHom (Fin.castLEEmb hm)

theorem viaEmbeddingHom_swap {A B : Type*} [DecidableEq A] [DecidableEq B]
    (e : A ↪ B) (a b : A) :
    Equiv.Perm.viaEmbeddingHom e (Equiv.swap a b) = Equiv.swap (e a) (e b) := by
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ Set.range e
  · obtain ⟨y, rfl⟩ := hx
    rw [Equiv.Perm.viaEmbeddingHom_apply, Equiv.Perm.viaEmbedding_apply]
    exact Function.Injective.map_swap e.injective a b y
  · rw [Equiv.Perm.viaEmbeddingHom_apply,
      Equiv.Perm.viaEmbedding_apply_of_not_mem _ _ _ hx]
    symm
    apply Equiv.swap_apply_of_ne_of_ne
    · exact fun hh => hx ⟨a, hh.symm⟩
    · exact fun hh => hx ⟨b, hh.symm⟩

@[simp] theorem prefixEmbedding_swap (hm : m+1 ≤ n+1) (a b : Fin (m+1)) :
    prefixEmbedding hm (Equiv.swap a b) =
      Equiv.swap (Fin.castLE hm a) (Fin.castLE hm b) :=
  viaEmbeddingHom_swap (Fin.castLEEmb hm) a b

def ambientIndex (hm : m+1 ≤ n+1) (i : Fin m) : Fin n := ⟨i.val, by omega⟩

theorem prefixEmbedding_adjacent (hm : m+1 ≤ n+1) (i : Fin m) :
    prefixEmbedding hm (Equiv.swap i.castSucc i.succ) =
      Equiv.swap (ambientIndex hm i).castSucc (ambientIndex hm i).succ := by
  rw [prefixEmbedding_swap]
  rfl

theorem representation_prefixAdjacent (h : eta ≤ nu)
    (hη : eta.card = m+1) (hν : nu.card = n+1) (i : Fin m) :
    YoungRepresentation.representation hν
        (prefixEmbedding (by have := card_le h; omega) (Equiv.swap i.castSucc i.succ)) =
      generator (prefixIndex h (leftIndex hη i)) (prefixIndex h (rightIndex hη i)) rfl := by
  rw [prefixEmbedding_adjacent, YoungRepresentation.representation_adjacent]
  rfl

/-- Act on the inner coordinate, keeping the skew coordinate fixed. -/
def splitOperator {K : Type*} [Field K]
    (T : Module.End K (StandardTableau eta → K)) :
    Module.End K ((StandardTableau eta × SkewStandardTableau eta nu) → K) where
  toFun f p := T (fun a => f (a,p.2)) p.1
  map_add' f g := by
    funext p
    exact congrFun (T.map_add (fun a => f (a,p.2)) (fun a => g (a,p.2))) p.1
  map_smul' c f := by
    funext p
    exact congrFun (T.map_smul c (fun a => f (a,p.2))) p.1

@[simp] theorem splitOperator_apply {K : Type*} [Field K]
    (T : Module.End K (StandardTableau eta → K))
    (f : StandardTableau eta × SkewStandardTableau eta nu → K)
    (p : StandardTableau eta × SkewStandardTableau eta nu) :
    splitOperator T f p = T (fun a => f (a,p.2)) p.1 := rfl

@[simp] theorem splitOperator_one {K : Type*} [Field K] :
    splitOperator (nu := nu) (1 : Module.End K (StandardTableau eta → K)) = 1 := rfl

theorem splitOperator_mul {K : Type*} [Field K]
    (S T : Module.End K (StandardTableau eta → K)) :
    splitOperator (nu := nu) (S*T) = splitOperator S * splitOperator T := rfl

/-- The actual full prefix-group action in the combinatorial split coordinates. -/
theorem representation_intertwines (h : eta ≤ nu)
    (hη : eta.card = m+1) (hν : nu.card = n+1)
    (g : Equiv.Perm (Fin (m+1)))
    (f : StandardTableau eta × SkewStandardTableau eta nu → ℚ) :
    YoungRepresentation.representation hν
        (prefixEmbedding (by have := card_le h; omega) g)
        (extendByZero (f ∘ prefixEquiv h)) =
      extendByZero ((splitOperator (YoungRepresentation.representation hη g) f) ∘ prefixEquiv h) := by
  have key : ∀ g : Equiv.Perm (Fin (m+1)), ∀ f :
      StandardTableau eta × SkewStandardTableau eta nu → ℚ,
      YoungRepresentation.representation hν
          (prefixEmbedding (by have := card_le h; omega) g)
          (extendByZero (f ∘ prefixEquiv h)) =
        extendByZero ((splitOperator (YoungRepresentation.representation hη g) f) ∘ prefixEquiv h) := by
    intro g
    apply (Bridge.Young.CoxeterExtension.symmetricSystem m).simple_induction g
    · intro i f
      rw [Bridge.Young.CoxeterExtension.symmetricSystem_simple]
      simp only [Bridge.Young.CoxeterExtension.adjacent]
      rw [representation_prefixAdjacent h hη hν i, generator_extendByZero,
        prefixEquiv_intertwines, YoungRepresentation.representation_adjacent]
      rfl
    · intro f
      simp
    · intro g₁ g₂ h₁ h₂ f
      simp only [map_mul, Module.End.mul_apply, splitOperator_mul]
      rw [h₂, h₁]
  exact key g f

theorem prefixEquiv_eq_iff (h : eta ≤ nu) (t : PrefixTableau eta nu)
    (a : StandardTableau eta) (s : SkewStandardTableau eta nu) :
    prefixEquiv h t = (a,s) ↔ t.val = (glueTableau h a s).val := by
  have hg : prefixEquiv h (glueTableau h a s) = (a,s) := by
    simp [prefixEquiv]
  rw [← hg, (prefixEquiv h).injective.eq_iff]
  exact Subtype.ext_iff

/-- A single split basis vector extends to the corresponding genuine ambient
tableau basis vector, with coefficient exactly one. -/
theorem extendByZero_single (h : eta ≤ nu) (a : StandardTableau eta)
    (s : SkewStandardTableau eta nu) :
    extendByZero ((Pi.single (a,s) (1 : ℚ)) ∘ prefixEquiv h) =
      Pi.single (glueTableau h a s).val 1 := by
  funext t
  by_cases hp : HasPrefix eta t
  · by_cases ht : t = (glueTableau h a s).val
    · have he := (prefixEquiv_eq_iff h ⟨t,hp⟩ a s).mpr ht
      change (if ht' : HasPrefix eta t then
        (Pi.single (a,s) (1 : ℚ) : (StandardTableau eta × SkewStandardTableau eta nu) → ℚ)
          (prefixEquiv h ⟨t,ht'⟩) else (0 : ℚ)) =
        (Pi.single (glueTableau h a s).val 1 : StandardTableau nu → ℚ) t
      rw [dif_pos hp]
      change (Pi.single (a,s) (1 : ℚ) : (StandardTableau eta × SkewStandardTableau eta nu) → ℚ)
        (prefixEquiv h ⟨t,hp⟩) = _
      rw [he]
      rw [Pi.single_eq_same]
      exact (congrArg (Pi.single (glueTableau h a s).val (1 : ℚ) : StandardTableau nu → ℚ)
        ht).trans (Pi.single_eq_same _ _ ) |>.symm
    · have he : prefixEquiv h ⟨t,hp⟩ ≠ (a,s) :=
        fun he => ht ((prefixEquiv_eq_iff h ⟨t,hp⟩ a s).mp he)
      simp [extendByZero, hp, Pi.single_apply, ht, Ne.symm ht, he, Ne.symm he]
  · have ht : t ≠ (glueTableau h a s).val := by
      intro ht
      exact hp (ht ▸ (glueTableau h a s).property)
    simp [extendByZero, hp, Pi.single_apply, ht, ht.symm]

theorem splitOperator_single {K : Type*} [Field K]
    (T : Module.End K (StandardTableau eta → K)) (a : StandardTableau eta)
    (s : SkewStandardTableau eta nu) (p : StandardTableau eta × SkewStandardTableau eta nu) :
    splitOperator T (Pi.single (a,s) 1) p =
      if p.2 = s then T (Pi.single a 1) p.1 else 0 := by
  by_cases hs : p.2 = s
  · have hf : (fun b : StandardTableau eta =>
        (Pi.single (a,s) (1 : K) : (StandardTableau eta × SkewStandardTableau eta nu) → K) (b,p.2)) =
        (Pi.single a 1 : StandardTableau eta → K) := by
      funext b
      simp [Pi.single_apply, hs]
    simp only [splitOperator_apply, hf, if_pos hs]
  · have hf : (fun b : StandardTableau eta =>
        (Pi.single (a,s) (1 : K) : (StandardTableau eta × SkewStandardTableau eta nu) → K) (b,p.2)) = 0 := by
      funext b
      simp [Pi.single_apply, hs]
    simp only [splitOperator_apply, hf, map_zero, Pi.zero_apply, if_neg hs]

theorem rational_representation_basis (h : eta ≤ nu)
    (hη : eta.card = m+1) (hν : nu.card = n+1)
    (g : Equiv.Perm (Fin (m+1))) (a : StandardTableau eta)
    (s : SkewStandardTableau eta nu) (t : StandardTableau nu) :
    YoungRepresentation.representation hν
        (prefixEmbedding (by have := card_le h; omega) g)
        (Pi.single (glueTableau h a s).val 1) t =
      if ht : HasPrefix eta t then
        if outerTableau h ⟨t,ht⟩ = s then
          YoungRepresentation.representation hη g (Pi.single a 1) (innerTableau h ⟨t,ht⟩)
        else 0
      else 0 := by
  have hh := congrFun (representation_intertwines h hη hν g (Pi.single (a,s) 1)) t
  rw [extendByZero_single] at hh
  rw [hh]
  simp only [extendByZero]
  by_cases hp : HasPrefix eta t
  · simp only [dif_pos hp, Function.comp_apply]
    exact splitOperator_single _ a s (prefixEquiv h ⟨t,hp⟩)
  · simp only [dif_neg hp]

/-- Exact full-group branching coefficients after scalar extension. This is
the same inner representation, and the skew label is unchanged. -/
theorem representation_basis (K : Type*) [Field K] [CharZero K]
    (h : eta ≤ nu) (hη : eta.card = m+1) (hν : nu.card = n+1)
    (g : Equiv.Perm (Fin (m+1))) (a : StandardTableau eta)
    (s : SkewStandardTableau eta nu) (t : StandardTableau nu) :
    ScalarExtension.representation K hν
        (prefixEmbedding (by have := card_le h; omega) g)
        (Pi.single (glueTableau h a s).val 1) t =
      if ht : HasPrefix eta t then
        if outerTableau h ⟨t,ht⟩ = s then
          ScalarExtension.representation K hη g (Pi.single a 1) (innerTableau h ⟨t,ht⟩)
        else 0
      else 0 := by
  change ScalarExtension.extend K (YoungRepresentation.representation hν _)
    (Pi.single (glueTableau h a s).val 1) t = _
  rw [ScalarExtension.extend_basis_coefficient, rational_representation_basis]
  split_ifs with hp hs
  · exact (ScalarExtension.extend_basis_coefficient K
      (YoungRepresentation.representation hη g) a (innerTableau h ⟨t,hp⟩)).symm
  · exact map_zero (algebraMap ℚ K)
  · exact map_zero (algebraMap ℚ K)

end LiebBridge.Young.PrefixRepresentation
