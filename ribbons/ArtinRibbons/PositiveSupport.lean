import ArtinRibbons.PositiveEmbedding

/-!
# Support of the actual positive Artin elements

Homogeneous braid moves preserve the set of indices in a word. The resulting
support homomorphism on the actual positive presentation identifies the
selected positive submonoid after the proved faithful embedding. Consequently
both factors of a selected positive element remain selected.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Ribbon2

open OAI.HarmonicArtin

variable {I : Type*}

@[ext] private structure SupportValue (I : Type*) where
  carrier : Set I

private instance : CommMonoid (SupportValue I) where
  mul a b := ⟨a.carrier ∪ b.carrier⟩
  one := ⟨∅⟩
  mul_assoc a b c := by ext i; exact or_assoc
  one_mul a := by ext i; change (False ∨ i ∈ a.carrier) ↔ i ∈ a.carrier; tauto
  mul_one a := by ext i; change (i ∈ a.carrier ∨ False) ↔ i ∈ a.carrier; tauto
  mul_comm a b := by ext i; exact or_comm

private theorem supportValue_word (w : List I) (i : I) :
    i ∈ ((w.map (fun j => (⟨{j}⟩ : SupportValue I))).prod).carrier ↔ i ∈ w := by
  induction w with
  | nil => change False ↔ i ∈ ([] : List I); simp
  | cons j w ih =>
    change (i = j ∨ i ∈ ((w.map (fun j => (⟨{j}⟩ : SupportValue I))).prod).carrier) ↔ _
    rw [ih, List.mem_cons]

private theorem altList_support (i j k : I) (n : ℕ) (hn : 2 ≤ n) :
    k ∈ CoxeterExchange.altList i j n ↔ k = i ∨ k = j := by
  constructor
  · exact CoxeterExchange.mem_altList i j n k
  · intro h
    obtain ⟨l, rfl⟩ : ∃ l, n = l + 2 := ⟨n - 2, by omega⟩
    simp only [CoxeterExchange.altList_succ, List.mem_cons]
    exact h.elim Or.inl (fun h => Or.inr (Or.inl h))

variable (M : CoxeterMatrix I)

private theorem support_relations :
    ∀ a b : FreeMonoid I, positiveBraidRelations M a b →
      FreeMonoid.lift (fun i => (⟨{i}⟩ : SupportValue I)) a =
        FreeMonoid.lift (fun i => (⟨{i}⟩ : SupportValue I)) b := by
  rintro a b ⟨i, j, rfl, rfl⟩
  simp only [FreeMonoid.lift_ofList]
  ext k
  rw [supportValue_word, supportValue_word]
  by_cases hij : i = j
  · rw [hij]
  by_cases hn : M i j = 0
  · simp only [hn, CoxeterExchange.altList_zero]
  · have hge : 2 ≤ M i j := by have := M.off_diagonal i j hij; omega
    rw [altList_support i j k _ hge, altList_support j i k _ hge, or_comm]

private noncomputable def positiveSupportHom : PositiveArtin M →* SupportValue I :=
  PresentedMonoid.lift (fun i => ⟨{i}⟩) (support_relations M)

/-- The support is independent of a representative positive word. -/
noncomputable def positiveSupport (a : PositiveArtin M) : Set I :=
  (positiveSupportHom M a).carrier

@[simp] theorem positiveSupport_one : positiveSupport M 1 = ∅ := by
  unfold positiveSupport
  rw [map_one]
  rfl

@[simp] theorem positiveSupport_generator (i : I) :
    positiveSupport M (positiveGenerator M i) = {i} := rfl

@[simp] theorem positiveSupport_mul (a b : PositiveArtin M) :
    positiveSupport M (a * b) = positiveSupport M a ∪ positiveSupport M b := by
  unfold positiveSupport
  rw [map_mul]
  rfl

@[simp] theorem positiveSupport_word (w : List I) :
    positiveSupport M (wordPositive M w) = {i | i ∈ w} := by
  ext i
  induction w with
  | nil => simp [wordPositive]
  | cons j w ih =>
    change i ∈ positiveSupport M (positiveGenerator M j * wordPositive M w) ↔ _
    rw [positiveSupport_mul, Set.mem_union, positiveSupport_generator,
      Set.mem_singleton_iff, ih]
    exact List.mem_cons.symm

/-- The selected positive presentation submonoid. -/
def positiveParabolic (J : Set I) : Submonoid (PositiveArtin M) :=
  Submonoid.closure (positiveGenerator M '' J)

theorem mem_positiveParabolic_iff_support (J : Set I) (a : PositiveArtin M) :
    a ∈ positiveParabolic M J ↔ positiveSupport M a ⊆ J := by
  constructor
  · intro ha
    let N : Submonoid (PositiveArtin M) :=
      { carrier := {b | positiveSupport M b ⊆ J}
        one_mem' := by simp
        mul_mem' := by
          intro b c hb hc
          change positiveSupport M (b * c) ⊆ J
          rw [positiveSupport_mul]
          exact Set.union_subset hb hc }
    have hle : positiveParabolic M J ≤ N := by
      apply Submonoid.closure_le.mpr
      rintro _ ⟨i, hi, rfl⟩
      change positiveSupport M (positiveGenerator M i) ⊆ J
      simpa only [positiveSupport_generator, Set.singleton_subset_iff] using hi
    exact hle ha
  · intro ha
    obtain ⟨w, rfl⟩ := positive_word_surjective M a
    have hw : ∀ i ∈ w, i ∈ J := by rw [positiveSupport_word] at ha; exact ha
    clear ha
    induction w with
    | nil => exact Submonoid.one_mem _
    | cons i w ih =>
      change positiveGenerator M i * wordPositive M w ∈ _
      exact Submonoid.mul_mem _ (Submonoid.subset_closure ⟨i, hw i (by simp), rfl⟩)
        (ih (fun j hj => hw j (List.mem_cons_of_mem i hj)))

theorem positiveToParent_mem_iff_support [Finite M.Group] (J : Set I) (a : PositiveArtin M) :
    positiveToParent M a ∈ actualPositiveParabolic M J ↔ positiveSupport M a ⊆ J := by
  rw [← mem_positiveParabolic_iff_support M J a]
  constructor
  · intro ha
    rw [← map_positiveParabolic M J] at ha
    obtain ⟨b, hb, hba⟩ := ha
    rwa [positiveToParent_injective M hba] at hb
  · intro ha
    rw [← map_positiveParabolic M J]
    exact ⟨a, ha, rfl⟩

/-- Selected positive elements have selected positive factors on both sides. -/
theorem positive_factors_mem_actualPositiveParabolic [Finite M.Group] (J : Set I)
    (a b : PositiveArtin M)
    (h : positiveToParent M (a * b) ∈ actualPositiveParabolic M J) :
    positiveToParent M a ∈ actualPositiveParabolic M J ∧
      positiveToParent M b ∈ actualPositiveParabolic M J := by
  rw [positiveToParent_mem_iff_support, positiveSupport_mul, Set.union_subset_iff] at h
  exact ⟨(positiveToParent_mem_iff_support M J a).2 h.1,
    (positiveToParent_mem_iff_support M J b).2 h.2⟩

end ArtinNormalisers.Ribbon2
