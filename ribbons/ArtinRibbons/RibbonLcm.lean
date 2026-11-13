import ArtinRibbons.RibbonWords

/-! # The actual pairwise lcm of elementary positive ribbons

The common multiple is the actual fundamental-element ratio. Its universal
property is proved in the whole positive monoid, and its two initial
elementary factors extend to positive generated paths with the same target.
-/

namespace ArtinNormalisers.Ribbon2

open OAI.HarmonicArtin OAI.HarmonicArtin.CoxeterExchange

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group]

omit [Finite M.Group] in
private theorem selected_positive_univ (J : Set I) {p : Artin.Group M}
    (hp : p ∈ actualPositiveParabolic M J) : p ∈ actualPositiveParabolic M Set.univ :=
  Submonoid.closure_mono (Set.image_mono (Set.subset_univ J)) hp

/-- The actual left-lcm candidate in equations (5.8)--(5.9). -/
noncomputable def pairRibbonLcm (J : Set I) (a b : I) : Artin.Group M :=
  (parabolicDelta M J)⁻¹ * parabolicDelta M (insert b (insert a J))

private theorem source_subset_pair (J : Set I) (a b : I) :
    J ⊆ insert b (insert a J) :=
  (Set.subset_insert a J).trans (Set.subset_insert b _)

theorem pairRibbonLcm_positive (J : Set I) (a b : I) :
    pairRibbonLcm M J a b ∈ actualPositiveParabolic M Set.univ :=
  selected_positive_univ M _ (parabolicDelta_ratio_positive M J _ (source_subset_pair J a b))

theorem pairRibbonLcm_leftReduced (J : Set I) (a b : I) :
    IsLeftParabolicallyReduced M J (pairRibbonLcm M J a b) :=
  parabolicDelta_ratio_leftReduced M J _ (source_subset_pair J a b)

theorem pairRibbonLcm_isRibbon (J : Set I) (a b : I) :
    IsRibbon M ⟨J⟩ ⟨parabolicTwistImage M (insert b (insert a J)) J⟩
      (pairRibbonLcm M J a b) :=
  parabolicDelta_ratio_isRibbon M J _ (source_subset_pair J a b)

@[simp] theorem pairRibbonLcm_projection (J : Set I) (a b : I) :
    Artin.projection M (pairRibbonLcm M J a b) =
      (parabolicLongest M J)⁻¹ * parabolicLongest M (insert b (insert a J)) := by
  rw [pairRibbonLcm, map_mul, map_inv, projection_parabolicDelta, projection_parabolicDelta]

/-- Every nested fundamental ratio with `a` among the added indices has an
actual positive elementary `a`-prefix and an explicit positive quotient. -/
theorem parabolicDelta_ratio_elementary_prefix (J K : Set I) (hJK : J ⊆ K)
    (a : I) (haK : a ∈ K) :
    ∃ q ∈ actualPositiveParabolic M Set.univ,
      (parabolicDelta M J)⁻¹ * parabolicDelta M K = elementaryMu M J a * q := by
  have hJaK : insert a J ⊆ K := Set.insert_subset haK hJK
  refine ⟨(parabolicDelta M (insert a J))⁻¹ * parabolicDelta M K,
    selected_positive_univ M K (parabolicDelta_ratio_positive M _ _ hJaK), ?_⟩
  unfold elementaryMu
  group

/-- The ratio is the left-lcm of the two actual elementary ribbons in the
entire positive monoid; no lcm structure or completeness hypothesis is assumed. -/
theorem pairRibbonLcm_is_left_lcm (J : Set I) (a b : I) :
    (∃ q ∈ actualPositiveParabolic M Set.univ,
      pairRibbonLcm M J a b = elementaryMu M J a * q) ∧
    (∃ q ∈ actualPositiveParabolic M Set.univ,
      pairRibbonLcm M J a b = elementaryMu M J b * q) ∧
    ∀ p : Artin.Group M, p ∈ actualPositiveParabolic M Set.univ →
      (∃ q ∈ actualPositiveParabolic M Set.univ, p = elementaryMu M J a * q) →
      (∃ q ∈ actualPositiveParabolic M Set.univ, p = elementaryMu M J b * q) →
      ∃ q ∈ actualPositiveParabolic M Set.univ, p = pairRibbonLcm M J a b * q := by
  refine ⟨parabolicDelta_ratio_elementary_prefix M J _ (source_subset_pair J a b) a
      (Set.mem_insert_of_mem b (Set.mem_insert a J)),
    parabolicDelta_ratio_elementary_prefix M J _ (source_subset_pair J a b) b
      (Set.mem_insert b _), ?_⟩
  intro p hp hpa hpb
  have hδ : parabolicDelta M J ∈ actualPositiveParabolic M Set.univ :=
    selected_positive_univ M J (parabolicDelta_mem_positiveParabolic M J)
  have hJ : ∀ j ∈ J, ∃ q ∈ actualPositiveParabolic M Set.univ,
      parabolicDelta M J * p = Artin.generator M j * q := by
    intro j hj
    obtain ⟨q, hq, he⟩ := (generator_leftDivides_parabolicDelta_iff M J j).mpr hj
    exact ⟨q * p, (actualPositiveParabolic M Set.univ).mul_mem hq hp,
      by rw [he, mul_assoc]⟩
  have hadded : ∀ c : I,
      (∃ q ∈ actualPositiveParabolic M Set.univ, p = elementaryMu M J c * q) →
      ∃ q ∈ actualPositiveParabolic M Set.univ,
        parabolicDelta M J * p = Artin.generator M c * q := by
    intro c hc
    obtain ⟨q, hq, he⟩ := hc
    obtain ⟨r, hr, hd⟩ :=
      (generator_leftDivides_parabolicDelta_iff M (insert c J) c).mpr (Set.mem_insert c J)
    refine ⟨r * q, (actualPositiveParabolic M Set.univ).mul_mem hr hq, ?_⟩
    rw [he, elementaryMu]
    calc
      parabolicDelta M J * ((parabolicDelta M J)⁻¹ * parabolicDelta M (insert c J) * q) =
          parabolicDelta M (insert c J) * q := by group
      _ = Artin.generator M c * (r * q) := by rw [hd, mul_assoc]
  obtain ⟨q, hq, hqeq⟩ := parabolicDelta_left_lcm M (insert b (insert a J))
    (parabolicDelta M J * p) ((actualPositiveParabolic M Set.univ).mul_mem hδ hp) (by
      intro j hj
      rcases Set.mem_insert_iff.mp hj with hjb | hj
      · simpa only [hjb] using hadded b hpb
      · rcases Set.mem_insert_iff.mp hj with hja | hj
        · simpa only [hja] using hadded a hpa
        · exact hJ j hj)
  refine ⟨q, hq, ?_⟩
  unfold pairRibbonLcm
  calc
    p = (parabolicDelta M J)⁻¹ * (parabolicDelta M J * p) := by group
    _ = (parabolicDelta M J)⁻¹ * (parabolicDelta M (insert b (insert a J)) * q) := by rw [hqeq]
    _ = (parabolicDelta M J)⁻¹ * parabolicDelta M (insert b (insert a J)) * q := by group

/-- An elementary prefix of a positive left-reduced ribbon leaves a positive
left-reduced ribbon tail with the genuine intermediate endpoint. -/
theorem positive_ribbon_elementary_tail {X Y : RibbonObject M} {r : Artin.Group M}
    (_hrpos : r ∈ actualPositiveParabolic M Set.univ)
    (hrred : IsLeftParabolicallyReduced M X.indices r) (hrib : IsRibbon M X Y r)
    (a : I) (_ha : a ∉ X.indices)
    (hprefix : ∃ q ∈ actualPositiveParabolic M Set.univ,
      r = elementaryMu M X.indices a * q) :
    ∃ q : Artin.Group M,
      PositiveReducedArrow M ⟨parabolicTwistImage M (insert a X.indices) X.indices⟩ Y q ∧
      r = elementaryMu M X.indices a * q := by
  obtain ⟨q, hqpos, hfactor⟩ := hprefix
  let μ := elementaryMu M X.indices a
  let Z : RibbonObject M := ⟨parabolicTwistImage M (insert a X.indices) X.indices⟩
  have hμ : IsRibbon M X Z μ := elementaryMu_isRibbon M X.indices a
  have hμpos : μ ∈ actualPositiveParabolic M Set.univ :=
    selected_positive_univ M _ (elementaryMu_positive M X.indices a)
  have hqRibbon : IsRibbon M Z Y q := by
    have h := IsRibbon.mul M (IsRibbon.inv M hμ) hrib
    have he : μ⁻¹ * r = q := by rw [hfactor]; dsimp [μ]; group
    simpa only [he] using h
  have hqred : IsLeftParabolicallyReduced M Z.indices q := by
    intro j hj s hs he
    obtain ⟨i, hi, hrel⟩ := IsRibbon.generator_reverse M hμ hj
    apply hrred i hi (μ * s) ((actualPositiveParabolic M Set.univ).mul_mem hμpos hs)
    rw [← mul_assoc, hrel, mul_assoc, he]
    exact hfactor.symm
  exact ⟨q, positive_leftReduced_ribbon_generated M hqpos hqred hqRibbon, hfactor⟩

/-- Distinct outside labels yield two positive generated factorizations of
the actual same lcm, with first labels `a` and `b` and an actual common target.
The tails may be identity arrows. -/
theorem pairRibbonLcm_factorizations (J : Set I) (a b : I)
    (ha : a ∉ J) (hb : b ∉ J) (_hab : a ≠ b) :
    ∃ qa qb : Artin.Group M,
      PositiveReducedArrow M ⟨parabolicTwistImage M (insert a J) J⟩
        ⟨parabolicTwistImage M (insert b (insert a J)) J⟩ qa ∧
      PositiveReducedArrow M ⟨parabolicTwistImage M (insert b J) J⟩
        ⟨parabolicTwistImage M (insert b (insert a J)) J⟩ qb ∧
      pairRibbonLcm M J a b = elementaryMu M J a * qa ∧
      pairRibbonLcm M J a b = elementaryMu M J b * qb := by
  obtain ⟨hpa, hpb, -⟩ := pairRibbonLcm_is_left_lcm M J a b
  obtain ⟨qa, hqa, hea⟩ := positive_ribbon_elementary_tail M
    (pairRibbonLcm_positive M J a b) (pairRibbonLcm_leftReduced M J a b)
    (pairRibbonLcm_isRibbon M J a b) a ha hpa
  obtain ⟨qb, hqb, heb⟩ := positive_ribbon_elementary_tail M
    (pairRibbonLcm_positive M J a b) (pairRibbonLcm_leftReduced M J a b)
    (pairRibbonLcm_isRibbon M J a b) b hb hpb
  exact ⟨qa, qb, hqa, hqb, hea, heb⟩

/-- Two concrete decorated atomic paths of the same actual lcm, beginning
with the prescribed distinct outside labels. All intermediate objects and
labels remain part of the words. -/
theorem pairRibbonLcm_atomicWords (J : Set I) (a b : I)
    (ha : a ∉ J) (hb : b ∉ J) (hab : a ≠ b) :
    ∃ wa : AtomicWord M (atomicNext M (⟨J⟩ : RibbonObject M) a)
        ⟨parabolicTwistImage M (insert b (insert a J)) J⟩,
    ∃ wb : AtomicWord M (atomicNext M (⟨J⟩ : RibbonObject M) b)
        ⟨parabolicTwistImage M (insert b (insert a J)) J⟩,
      (AtomicWord.cons a ha wa).eval = pairRibbonLcm M J a b ∧
      (AtomicWord.cons b hb wb).eval = pairRibbonLcm M J a b := by
  obtain ⟨qa, qb, hqa, hqb, hea, heb⟩ := pairRibbonLcm_factorizations M J a b ha hb hab
  obtain ⟨wa, hwa⟩ := (positiveReducedArrow_iff_exists_atomicWord M).mp hqa
  obtain ⟨wb, hwb⟩ := (positiveReducedArrow_iff_exists_atomicWord M).mp hqb
  refine ⟨wa, wb, ?_, ?_⟩
  · change elementaryMu M J a * wa.eval = pairRibbonLcm M J a b
    rw [hwa]
    exact hea.symm
  · change elementaryMu M J b * wb.eval = pairRibbonLcm M J a b
    rw [hwb]
    exact heb.symm

/-- A nested fundamental ratio is the actual positive lift of its Coxeter
projection. This follows from the proved simple-prefix divisibility bridge. -/
theorem parabolicDelta_ratio_eq_simpleLift (J K : Set I) (hJK : J ⊆ K) :
    (parabolicDelta M J)⁻¹ * parabolicDelta M K =
      positiveToParent M (positiveSimpleLift M
        ((parabolicLongest M J)⁻¹ * parabolicLongest M K)) := by
  classical
  let := fundamental_finite_index M
  let := Fintype.ofFinite I
  have hp := positiveDelta_prefix_of_subset M J K hJK
  change PositivePrefix M (positiveSimpleLift M (parabolicLongest M J))
    (positiveSimpleLift M (parabolicLongest M K)) at hp
  have hweak := (positivePrefix_simple_iff M _ _).mp hp
  have hmul := positiveSimpleLift_mul M (parabolicLongest M J)
    ((parabolicLongest M J)⁻¹ * parabolicLongest M K)
    (by simpa only [mul_inv_cancel_left] using
      (show M.toCoxeterSystem.length (parabolicLongest M K) =
        M.toCoxeterSystem.length (parabolicLongest M J) +
          M.toCoxeterSystem.length ((parabolicLongest M J)⁻¹ * parabolicLongest M K)
        from hweak))
  rw [mul_inv_cancel_left] at hmul
  have h := congrArg (positiveToParent M) hmul
  rw [map_mul] at h
  have hJ : positiveToParent M (positiveSimpleLift M (parabolicLongest M J)) =
      parabolicDelta M J := positiveToParent_positiveDelta M J
  have hK : positiveToParent M (positiveSimpleLift M (parabolicLongest M K)) =
      parabolicDelta M K := positiveToParent_positiveDelta M K
  rw [hJ, hK] at h
  rw [h]
  group

private theorem simpleLift_actual_prefix_iff (u v : M.Group) :
    (∃ q ∈ actualPositiveParabolic M Set.univ,
      positiveToParent M (positiveSimpleLift M v) =
        positiveToParent M (positiveSimpleLift M u) * q) ↔
      WeakPrefix M.toCoxeterSystem u v := by
  classical
  let := fundamental_finite_index M
  let := Fintype.ofFinite I
  exact (positivePrefix_iff_parentQuotient M _ _).symm.trans
    (positivePrefix_simple_iff M u v)

/-- The Coxeter projection of the actual ribbon lcm is the weak-prefix join
of the projections of its two elementary prefixes, with the full universal
property. No lattice instance is assumed. -/
theorem pairRibbonLcm_weakPrefix_join (J : Set I) (a b : I) :
    let u := (parabolicLongest M J)⁻¹ * parabolicLongest M (insert a J)
    let v := (parabolicLongest M J)⁻¹ * parabolicLongest M (insert b J)
    let l := (parabolicLongest M J)⁻¹ * parabolicLongest M (insert b (insert a J))
    WeakPrefix M.toCoxeterSystem u l ∧ WeakPrefix M.toCoxeterSystem v l ∧
      ∀ w, WeakPrefix M.toCoxeterSystem u w → WeakPrefix M.toCoxeterSystem v w →
        WeakPrefix M.toCoxeterSystem l w := by
  dsimp only
  have ha := parabolicDelta_ratio_eq_simpleLift M J (insert a J) (Set.subset_insert a J)
  change elementaryMu M J a = _ at ha
  have hb := parabolicDelta_ratio_eq_simpleLift M J (insert b J) (Set.subset_insert b J)
  change elementaryMu M J b = _ at hb
  have hl := parabolicDelta_ratio_eq_simpleLift M J (insert b (insert a J))
    (source_subset_pair J a b)
  change pairRibbonLcm M J a b = _ at hl
  obtain ⟨hpa, hpb, hleast⟩ := pairRibbonLcm_is_left_lcm M J a b
  refine ⟨(simpleLift_actual_prefix_iff M _ _).mp ?_,
    (simpleLift_actual_prefix_iff M _ _).mp ?_, ?_⟩
  · rw [← hl, ← ha]
    exact hpa
  · rw [← hl, ← hb]
    exact hpb
  · intro w huw hvw
    apply (simpleLift_actual_prefix_iff M _ _).mp
    rw [← hl]
    apply hleast _ (positiveActualHom M (positiveSimpleLift M w)).property
    · have h := (simpleLift_actual_prefix_iff M _ _).mpr huw
      rwa [← ha] at h
    · have h := (simpleLift_actual_prefix_iff M _ _).mpr hvw
      rwa [← hb] at h

end ArtinNormalisers.Ribbon2
