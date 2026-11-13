import ArtinRibbons.RibbonLcm

/-!
# Coxeter length additivity for atomic lcm relation words

Every elementary ribbon and every pair lcm is a simple positive lift. Thus
any atomic decomposition of an actual pair lcm has length-additive Coxeter
evaluation. This is the algebraic input for the later geometric geodesic
comparison; no wall-crossing or fundamental-groupoid comparison is assumed.
-/

namespace ArtinNormalisers.Ribbon2

open OAI.HarmonicArtin

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group]

theorem projection_positiveToParent (a : PositiveArtin M) :
    Artin.projection M (positiveToParent M a) = positiveToCoxeter M a := by
  obtain ⟨w, rfl⟩ := positive_word_surjective M a
  rw [positiveToParent_word, Artin.projection_wordProd, positiveToCoxeter_word]
  rfl

@[simp] theorem projection_parentSimpleLift (w : M.Group) :
    Artin.projection M (positiveToParent M (positiveSimpleLift M w)) = w := by
  rw [projection_positiveToParent, positiveToCoxeter_simpleLift]

theorem degree_eq_coxeterLength_of_simple {r : Artin.Group M}
    (h : ∃ w, r = positiveToParent M (positiveSimpleLift M w)) :
    degree M r = (M.toCoxeterSystem.length (Artin.projection M r) : ℤ) := by
  obtain ⟨w, rfl⟩ := h
  rw [degree_positiveToParent, positiveDegree_simpleLift, projection_parentSimpleLift]

theorem elementaryMu_degree_eq_coxeterLength (J : Set I) (a : I) :
    degree M (elementaryMu M J a) =
      (M.toCoxeterSystem.length (Artin.projection M (elementaryMu M J a)) : ℤ) :=
  degree_eq_coxeterLength_of_simple M
    ⟨_, parabolicDelta_ratio_eq_simpleLift M J (insert a J) (Set.subset_insert a J)⟩

namespace AtomicWord

variable {M}

/-- Sum of the Coxeter lengths of the actual traversed elementary labels. -/
noncomputable def coxeterWeight {X Y : RibbonObject M} : AtomicWord M X Y → ℕ
  | .nil _ => 0
  | @cons _ _ _ X _ a _ p =>
      M.toCoxeterSystem.length (Artin.projection M (elementaryMu M X.indices a)) +
        p.coxeterWeight

theorem degree_eval_eq_coxeterWeight {X Y : RibbonObject M} (p : AtomicWord M X Y) :
    degree M p.eval = (p.coxeterWeight : ℤ) := by
  induction p with
  | nil X => exact degree_one M
  | @cons X Y a ha p ih =>
    rw [eval_cons, degree_mul, elementaryMu_degree_eq_coxeterLength, ih]
    exact (Int.natCast_add _ _).symm

/-- A simple total evaluation has length equal to the sum of all elementary
Coxeter lengths. This applies to every atomic factorization, not just choices. -/
theorem coxeter_length_additive_of_simple {X Y : RibbonObject M} (p : AtomicWord M X Y)
    (h : ∃ w, p.eval = positiveToParent M (positiveSimpleLift M w)) :
    M.toCoxeterSystem.length (Artin.projection M p.eval) = p.coxeterWeight := by
  have he := (degree_eq_coxeterLength_of_simple M h).symm.trans
    (degree_eval_eq_coxeterWeight p)
  exact_mod_cast he

/-- Every actual pair-lcm relation word has length-additive Coxeter evaluation.
The geometric consequence that its gallery is geodesic belongs to landmark 3. -/
theorem pairLcm_coxeter_length_additive {X Y : RibbonObject M}
    (p : AtomicWord M X Y) (a b : I)
    (he : p.eval = pairRibbonLcm M X.indices a b) :
    M.toCoxeterSystem.length (Artin.projection M p.eval) = p.coxeterWeight := by
  apply coxeter_length_additive_of_simple p
  refine ⟨(parabolicLongest M X.indices)⁻¹ *
    parabolicLongest M (insert b (insert a X.indices)), ?_⟩
  rw [he]
  exact parabolicDelta_ratio_eq_simpleLift M X.indices
    (insert b (insert a X.indices)) (fun _ h => Set.mem_insert_of_mem b (Set.mem_insert_of_mem a h))

end AtomicWord

end ArtinNormalisers.Ribbon2
