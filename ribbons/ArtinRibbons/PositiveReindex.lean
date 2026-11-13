import ArtinRibbons.Positive

/-! # Generator-preserving maps and reindexing of the actual presentations -/

namespace ArtinNormalisers.Ribbon2

open OAI.HarmonicArtin OAI.HarmonicArtin.CoxeterExchange

variable {I K : Type*}

theorem map_altList (f : I → K) (i j : I) (n : ℕ) :
    (altList i j n).map f = altList (f i) (f j) n := by
  induction n generalizing i j with
  | zero => rfl
  | succ n ih => simp only [altList_succ, List.map_cons, ih]

theorem map_alternatingWord (f : I → K) (i j : I) (n : ℕ) :
    (CoxeterSystem.alternatingWord i j n).map f =
      CoxeterSystem.alternatingWord (f i) (f j) n := by
  induction n generalizing i j with
  | zero => rfl
  | succ n ih =>
    simp only [CoxeterSystem.alternatingWord_succ', List.map_cons, ih]
    split_ifs <;> rfl

/-- A label-preserving index map induces the corresponding map of positive
Artin presentations, without an injectivity or finiteness premise. -/
def positiveMap (M : CoxeterMatrix I) (N : CoxeterMatrix K) (f : I → K)
    (hf : ∀ i j, N (f i) (f j) = M i j) : PositiveArtin M →* PositiveArtin N :=
  PresentedMonoid.lift (fun i => positiveGenerator N (f i)) <| by
    rintro _ _ ⟨i, j, rfl, rfl⟩
    rw [FreeMonoid.lift_ofList, FreeMonoid.lift_ofList]
    have h := wordPositive_braid N (f i) (f j)
    simp only [wordPositive, hf i j] at h
    simpa only [← map_altList f i j (M i j), ← map_altList f j i (M i j),
      List.map_map, Function.comp_def] using h

@[simp] theorem positiveMap_generator (M : CoxeterMatrix I) (N : CoxeterMatrix K)
    (f : I → K) (hf) (i : I) :
    positiveMap M N f hf (positiveGenerator M i) = positiveGenerator N (f i) := rfl

@[simp] theorem positiveMap_word (M : CoxeterMatrix I) (N : CoxeterMatrix K)
    (f : I → K) (hf) (w : List I) :
    positiveMap M N f hf (wordPositive M w) = wordPositive N (w.map f) := by
  simp [wordPositive, map_list_prod, List.map_map, Function.comp_def]

/-- The same index map on the unchanged parent Artin-group presentations. -/
def parentArtinMap (M : CoxeterMatrix I) (N : CoxeterMatrix K) (f : I → K)
    (hf : ∀ i j, N (f i) (f j) = M i j) : Artin.Group M →* Artin.Group N :=
  TauCeti.ArtinGroup.lift M (fun i => Artin.generator N (f i)) <| by
    intro i j
    have h := TauCeti.ArtinGroup.prod_map_gen_braidWord N (f i) (f j)
    simp only [CoxeterSystem.braidWord, hf i j, hf j i] at h ⊢
    simpa only [Artin.generator, ← map_alternatingWord f i j (M i j),
      ← map_alternatingWord f j i (M j i), List.map_map, Function.comp_def] using h

@[simp] theorem parentArtinMap_generator (M : CoxeterMatrix I) (N : CoxeterMatrix K)
    (f : I → K) (hf) (i : I) :
    parentArtinMap M N f hf (Artin.generator M i) = Artin.generator N (f i) :=
  TauCeti.ArtinGroup.lift_gen M _ _ i

/-- The actual positive-to-parent map commutes with label-preserving maps. -/
theorem positiveToParent_map (M : CoxeterMatrix I) (N : CoxeterMatrix K)
    (f : I → K) (hf) :
    (positiveToParent N).comp (positiveMap M N f hf) =
      (parentArtinMap M N f hf).comp (positiveToParent M) := by
  apply PresentedMonoid.ext
  intro i
  change positiveToParent N (positiveMap M N f hf (positiveGenerator M i)) =
    parentArtinMap M N f hf (positiveToParent M (positiveGenerator M i))
  simp

theorem inverse_label_eq (M : CoxeterMatrix I) (N : CoxeterMatrix K) (e : I ≃ K)
    (he : ∀ i j, N (e i) (e j) = M i j) (i j : K) :
    M (e.symm i) (e.symm j) = N i j := by
  simpa using (he (e.symm i) (e.symm j)).symm

/-- An actual multiplicative equivalence of positive presentations along a
label-preserving equivalence of index types, possibly in different universes. -/
def positiveEquivOfLabels (M : CoxeterMatrix I) (N : CoxeterMatrix K) (e : I ≃ K)
    (he : ∀ i j, N (e i) (e j) = M i j) : PositiveArtin M ≃* PositiveArtin N :=
  MonoidHom.toMulEquiv (positiveMap M N e he)
    (positiveMap N M e.symm (inverse_label_eq M N e he))
    (by
      apply PresentedMonoid.ext
      intro i
      change positiveMap N M e.symm (inverse_label_eq M N e he)
        (positiveMap M N e he (positiveGenerator M i)) = positiveGenerator M i
      simp)
    (by
      apply PresentedMonoid.ext
      intro i
      change positiveMap M N e he
        (positiveMap N M e.symm (inverse_label_eq M N e he) (positiveGenerator N i)) =
          positiveGenerator N i
      simp)

@[simp] theorem positiveEquivOfLabels_generator (M : CoxeterMatrix I) (N : CoxeterMatrix K)
    (e : I ≃ K) (he) (i : I) :
    positiveEquivOfLabels M N e he (positiveGenerator M i) = positiveGenerator N (e i) := rfl

/-- Reindexing a Coxeter matrix reindexes the positive presentation by the
same equivalence and preserves the named generators. -/
def positiveReindexEquiv (M : CoxeterMatrix I) (e : I ≃ K) :
    PositiveArtin M ≃* PositiveArtin (M.reindex e) :=
  positiveEquivOfLabels M (M.reindex e) e (by
    intro i j
    simp [CoxeterMatrix.reindex_apply])

@[simp] theorem positiveReindexEquiv_generator (M : CoxeterMatrix I) (e : I ≃ K) (i : I) :
    positiveReindexEquiv M e (positiveGenerator M i) =
      positiveGenerator (M.reindex e) (e i) := rfl

/-- Injectivity of the actual positive presentation map transports through
an index equivalence and its explicitly proved commuting diagram. -/
theorem positiveToParent_injective_of_labels (M : CoxeterMatrix I) (N : CoxeterMatrix K)
    (e : I ≃ K) (he : ∀ i j, N (e i) (e j) = M i j)
    (hN : Function.Injective (positiveToParent N)) :
    Function.Injective (positiveToParent M) := by
  intro a b hab
  apply (positiveEquivOfLabels M N e he).injective
  change positiveMap M N e he a = positiveMap M N e he b
  apply hN
  change ((positiveToParent N).comp (positiveMap M N e he)) a =
    ((positiveToParent N).comp (positiveMap M N e he)) b
  rw [positiveToParent_map]
  exact congrArg (parentArtinMap M N e he) hab

end ArtinNormalisers.Ribbon2
