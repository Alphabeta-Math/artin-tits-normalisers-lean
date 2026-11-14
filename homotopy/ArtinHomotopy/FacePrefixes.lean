import ArtinRibbons.RibbonLcm

/-!
# Maximal face prefixes of actual positive relative ribbons

The face prefix at `X` with added indices `T` is the actual ratio
`Δ_X⁻¹ Δ_(X ∪ T)`. Its positive-prefix universal property follows from the
accepted global atom-lcm theorem after multiplying by `Δ_X`. Removing it
leaves an actual positive generated ribbon with the correct endpoint.

This is the relative left-prefix analogue of OAI's
`positive_descent_fundamental` in `Harmonic/PositiveDescentSet.lean`, inspected
at SHA256 `867cd471727c93ef85bf274a38db99606cf3b308c015dd6f843571dd8b1021c8`.
That supplier is an ordinary positive **suffix** theorem and is not imported
or silently reversed here. The proof below generalizes the accepted
`positive_ribbon_elementary_tail` using its actual endpoint calculation.
No asphericity or topological comparison is asserted by this module.
-/

namespace ArtinNormalisers.Homotopy5

open ArtinNormalisers.Ribbon2

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group]

/-- Positive left divisibility in the actual Artin group, with a genuine
positive quotient. -/
def RibbonPrefix (a b : Artin.Group M) : Prop :=
  ∃ q ∈ actualPositiveParabolic M Set.univ, b = a * q

omit [Finite M.Group] in
theorem RibbonPrefix.trans {a b c : Artin.Group M}
    (hab : RibbonPrefix M a b) (hbc : RibbonPrefix M b c) : RibbonPrefix M a c := by
  obtain ⟨q, hq, hqa⟩ := hab
  obtain ⟨r, hr, hrb⟩ := hbc
  exact ⟨q * r, Submonoid.mul_mem _ hq hr, by rw [hrb, hqa, mul_assoc]⟩

omit [Finite M.Group] in
private theorem selected_positive_univ (J : Set I) {p : Artin.Group M}
    (hp : p ∈ actualPositiveParabolic M J) : p ∈ actualPositiveParabolic M Set.univ :=
  Submonoid.closure_mono (Set.image_mono (Set.subset_univ J)) hp

/-- The actual relative fundamental-element ratio for an arbitrary added set. -/
noncomputable def facePrefix (X : RibbonObject M) (T : Set I) : Artin.Group M :=
  (parabolicDelta M X.indices)⁻¹ * parabolicDelta M (X.indices ∪ T)

/-- The actual intermediate endpoint determined by longest-element opposition. -/
noncomputable def facePrefixTarget (X : RibbonObject M) (T : Set I) : RibbonObject M :=
  ⟨parabolicTwistImage M (X.indices ∪ T) X.indices⟩

theorem facePrefix_positive (X : RibbonObject M) (T : Set I) :
    facePrefix M X T ∈ actualPositiveParabolic M Set.univ :=
  selected_positive_univ M _ (parabolicDelta_ratio_positive M _ _ Set.subset_union_left)

theorem facePrefix_isRibbon (X : RibbonObject M) (T : Set I) :
    IsRibbon M X (facePrefixTarget M X T) (facePrefix M X T) :=
  parabolicDelta_ratio_isRibbon M _ _ Set.subset_union_left

theorem facePrefix_leftReduced (X : RibbonObject M) (T : Set I) :
    IsLeftParabolicallyReduced M X.indices (facePrefix M X T) :=
  parabolicDelta_ratio_leftReduced M _ _ Set.subset_union_left

theorem facePrefix_generated (X : RibbonObject M) (T : Set I) :
    PositiveReducedArrow M X (facePrefixTarget M X T) (facePrefix M X T) :=
  positive_leftReduced_ribbon_generated M (facePrefix_positive M X T)
    (facePrefix_leftReduced M X T) (facePrefix_isRibbon M X T)

theorem elementary_prefix_facePrefix (X : RibbonObject M) (T : Set I) {a : I}
    (ha : a ∈ T) : RibbonPrefix M (elementaryMu M X.indices a) (facePrefix M X T) :=
  parabolicDelta_ratio_elementary_prefix M X.indices (X.indices ∪ T)
    Set.subset_union_left a (Or.inr ha)

/-- The face ratio is the actual positive lcm of its elementary prefixes.
Indices already in `X` are harmless: their elementary ratios are identities. -/
theorem facePrefix_prefix_iff (X : RibbonObject M) (T : Set I)
    {p : Artin.Group M} (hp : p ∈ actualPositiveParabolic M Set.univ) :
    RibbonPrefix M (facePrefix M X T) p ↔
      ∀ a ∈ T, RibbonPrefix M (elementaryMu M X.indices a) p := by
  constructor
  · intro h a ha
    exact (elementary_prefix_facePrefix M X T ha).trans M h
  · intro hall
    have hδ : parabolicDelta M X.indices ∈ actualPositiveParabolic M Set.univ :=
      selected_positive_univ M _ (parabolicDelta_mem_positiveParabolic M X.indices)
    have hsource : ∀ j ∈ X.indices, ∃ q ∈ actualPositiveParabolic M Set.univ,
        parabolicDelta M X.indices * p = Artin.generator M j * q := by
      intro j hj
      obtain ⟨q, hq, heq⟩ := (generator_leftDivides_parabolicDelta_iff M X.indices j).2 hj
      exact ⟨q * p, Submonoid.mul_mem _ hq hp, by rw [heq, mul_assoc]⟩
    have hadded : ∀ a ∈ T, ∃ q ∈ actualPositiveParabolic M Set.univ,
        parabolicDelta M X.indices * p = Artin.generator M a * q := by
      intro a ha
      obtain ⟨q, hq, heq⟩ := hall a ha
      obtain ⟨r, hr, hdelta⟩ :=
        (generator_leftDivides_parabolicDelta_iff M (insert a X.indices) a).2
          (Set.mem_insert a X.indices)
      refine ⟨r * q, Submonoid.mul_mem _ hr hq, ?_⟩
      rw [heq, elementaryMu]
      calc
        parabolicDelta M X.indices *
            ((parabolicDelta M X.indices)⁻¹ * parabolicDelta M (insert a X.indices) * q) =
            parabolicDelta M (insert a X.indices) * q := by group
        _ = Artin.generator M a * (r * q) := by rw [hdelta, mul_assoc]
    obtain ⟨q, hq, heq⟩ := parabolicDelta_left_lcm M (X.indices ∪ T)
      (parabolicDelta M X.indices * p) (Submonoid.mul_mem _ hδ hp) (by
        intro j hj
        exact hj.elim (hsource j) (hadded j))
    refine ⟨q, hq, ?_⟩
    unfold facePrefix
    calc
      p = (parabolicDelta M X.indices)⁻¹ * (parabolicDelta M X.indices * p) := by group
      _ = (parabolicDelta M X.indices)⁻¹ * (parabolicDelta M (X.indices ∪ T) * q) := by rw [heq]
      _ = _ := by group

/-- Removing an actual positive face prefix leaves an actual positive reduced
ribbon with its genuine intermediate endpoint. -/
theorem positive_ribbon_face_tail {X Y : RibbonObject M} {p : Artin.Group M}
    (hp : PositiveReducedArrow M X Y p) (T : Set I)
    (hprefix : RibbonPrefix M (facePrefix M X T) p) :
    ∃ q : Artin.Group M, PositiveReducedArrow M (facePrefixTarget M X T) Y q ∧
      p = facePrefix M X T * q := by
  obtain ⟨q, hqpos, hfactor⟩ := hprefix
  let η := facePrefix M X T
  let Z := facePrefixTarget M X T
  have hη : IsRibbon M X Z η := facePrefix_isRibbon M X T
  have hηpos : η ∈ actualPositiveParabolic M Set.univ := facePrefix_positive M X T
  have hqRibbon : IsRibbon M Z Y q := by
    have h := IsRibbon.mul M (IsRibbon.inv M hη) hp.isRibbon
    have he : η⁻¹ * p = q := by rw [hfactor]; dsimp only [η]; group
    simpa only [he] using h
  have hqred : IsLeftParabolicallyReduced M Z.indices q := by
    intro j hj s hs he
    obtain ⟨i, hi, hrel⟩ := IsRibbon.generator_reverse M hη hj
    apply (hp.leftReduced M) i hi (η * s) (Submonoid.mul_mem _ hηpos hs)
    rw [← mul_assoc, hrel, mul_assoc, he]
    exact hfactor.symm
  exact ⟨q, positive_leftReduced_ribbon_generated M hqpos hqred hqRibbon, hfactor⟩

theorem positive_ribbon_face_tail_of_elementary_prefixes {X Y : RibbonObject M}
    {p : Artin.Group M} (hp : PositiveReducedArrow M X Y p) (T : Set I)
    (hall : ∀ a ∈ T, RibbonPrefix M (elementaryMu M X.indices a) p) :
    ∃ q : Artin.Group M, PositiveReducedArrow M (facePrefixTarget M X T) Y q ∧
      p = facePrefix M X T * q :=
  positive_ribbon_face_tail M hp T ((facePrefix_prefix_iff M X T hp.positive).2 hall)

/-- The outside atomic descents are actual elementary ribbon prefixes. -/
def outsideAtomDescents (X : RibbonObject M) (p : Artin.Group M) : Set I :=
  {a | a ∉ X.indices ∧ RibbonPrefix M (elementaryMu M X.indices a) p}

theorem outsideAtomDescents_facePrefix (X : RibbonObject M) (T : Set I) :
    outsideAtomDescents M X (facePrefix M X T) = T \ X.indices := by
  ext a
  constructor
  · rintro ⟨haX, q, hq, hprefix⟩
    have ha : a ∈ X.indices ∪ T := by
      obtain ⟨r, hr, hdelta⟩ :=
        (generator_leftDivides_parabolicDelta_iff M (insert a X.indices) a).2
          (Set.mem_insert a X.indices)
      apply (generator_leftDivides_parabolicDelta_iff M (X.indices ∪ T) a).1
      refine ⟨r * q, Submonoid.mul_mem _ hr hq, ?_⟩
      calc
        parabolicDelta M (X.indices ∪ T) =
            parabolicDelta M X.indices * facePrefix M X T := by unfold facePrefix; group
        _ = parabolicDelta M X.indices * (elementaryMu M X.indices a * q) := by rw [hprefix]
        _ = parabolicDelta M (insert a X.indices) * q := by unfold elementaryMu; group
        _ = Artin.generator M a * (r * q) := by rw [hdelta, mul_assoc]
    exact ⟨ha.resolve_left haX, haX⟩
  · rintro ⟨haT, haX⟩
    exact ⟨haX, elementary_prefix_facePrefix M X T haT⟩

theorem outsideAtomDescents_facePrefix_of_disjoint (X : RibbonObject M) (T : Set I)
    (hT : T ⊆ X.indicesᶜ) : outsideAtomDescents M X (facePrefix M X T) = T := by
  rw [outsideAtomDescents_facePrefix]
  ext a
  exact ⟨fun h => h.1, fun ha => ⟨ha, hT ha⟩⟩

theorem facePrefix_prefix_of_union_subset (X : RibbonObject M) (T U : Set I)
    (hTU : X.indices ∪ T ⊆ X.indices ∪ U) :
    RibbonPrefix M (facePrefix M X T) (facePrefix M X U) := by
  obtain ⟨q, hq, heq⟩ := parabolicDelta_prefix_of_subset M (X.indices ∪ T) (X.indices ∪ U) hTU
  refine ⟨q, selected_positive_univ M _ hq, ?_⟩
  unfold facePrefix
  rw [heq]
  group

/-- The actual maximal face type is the set of outside atomic descents. -/
def maximalFaceType (X : RibbonObject M) (p : Artin.Group M) : Set I :=
  outsideAtomDescents M X p

theorem maximalFaceType_subset_compl (X : RibbonObject M) (p : Artin.Group M) :
    maximalFaceType M X p ⊆ X.indicesᶜ := fun _ h => h.1

theorem maximalFacePrefix_prefix {X Y : RibbonObject M} {p : Artin.Group M}
    (hp : PositiveReducedArrow M X Y p) :
    RibbonPrefix M (facePrefix M X (maximalFaceType M X p)) p :=
  (facePrefix_prefix_iff M X _ hp.positive).2 (fun _ h => h.2)

/-- Every face prefix of `p` positively divides its maximal face prefix.
The conclusion compares actual Artin elements with actual positive quotients. -/
theorem maximalFacePrefix_greatest {X Y : RibbonObject M} {p : Artin.Group M}
    (hp : PositiveReducedArrow M X Y p) (T : Set I)
    (hT : RibbonPrefix M (facePrefix M X T) p) :
    RibbonPrefix M (facePrefix M X T) (facePrefix M X (maximalFaceType M X p)) := by
  have hall := (facePrefix_prefix_iff M X T hp.positive).1 hT
  apply facePrefix_prefix_of_union_subset M X T _
  intro a ha
  rcases ha with haX | haT
  · exact Or.inl haX
  · by_cases haX : a ∈ X.indices
    · exact Or.inl haX
    · exact Or.inr ⟨haX, hall a haT⟩

theorem maximalFacePrefix_tail {X Y : RibbonObject M} {p : Artin.Group M}
    (hp : PositiveReducedArrow M X Y p) :
    ∃ q : Artin.Group M,
      PositiveReducedArrow M (facePrefixTarget M X (maximalFaceType M X p)) Y q ∧
      p = facePrefix M X (maximalFaceType M X p) * q :=
  positive_ribbon_face_tail M hp _ (maximalFacePrefix_prefix M hp)

/-- Every nonidentity positive generated ribbon has an actual outside
elementary prefix. -/
theorem outsideAtomDescents_nonempty {X Y : RibbonObject M} {p : Artin.Group M}
    (hp : PositiveReducedArrow M X Y p) (hne : p ≠ 1) :
    (outsideAtomDescents M X p).Nonempty := by
  obtain ⟨w, hw⟩ := (positiveReducedArrow_iff_exists_atomicWord M).1 hp
  cases w with
  | nil X => exact False.elim (hne (by simpa only [AtomicWord.eval_nil] using hw.symm))
  | cons a ha w =>
    exact ⟨a, ha, w.eval, w.positive, by simpa only [AtomicWord.eval_cons] using hw.symm⟩

/-- The maximal face prefix has strictly positive actual degree whenever
there is a nontrivial positive ribbon to reduce. -/
theorem maximalFacePrefix_degree_pos {X Y : RibbonObject M} {p : Artin.Group M}
    (hp : PositiveReducedArrow M X Y p) (hne : p ≠ 1) :
    0 < degree M (facePrefix M X (maximalFaceType M X p)) := by
  obtain ⟨a, haX, ha⟩ := outsideAtomDescents_nonempty M hp hne
  have haD : a ∈ maximalFaceType M X p := ⟨haX, ha⟩
  obtain ⟨q, hq, heq⟩ := elementary_prefix_facePrefix M X _ haD
  have hdeg := congrArg (degree M) heq
  rw [degree_mul] at hdeg
  have hμ := elementaryMu_degree_pos M X.indices a haX
  have hqdeg := degree_nonneg_of_mem_actualPositiveParabolic M Set.univ hq
  omega

/-- Removing the maximal actual face prefix strictly decreases the degree.
This is the algebraic termination input for a descending-cell argument. -/
theorem maximalFacePrefix_tail_degree_lt {X Y : RibbonObject M} {p : Artin.Group M}
    (hp : PositiveReducedArrow M X Y p) (hne : p ≠ 1) :
    ∃ q : Artin.Group M,
      PositiveReducedArrow M (facePrefixTarget M X (maximalFaceType M X p)) Y q ∧
      p = facePrefix M X (maximalFaceType M X p) * q ∧ degree M q < degree M p := by
  obtain ⟨q, hq, heq⟩ := maximalFacePrefix_tail M hp
  refine ⟨q, hq, heq, ?_⟩
  have hdeg := congrArg (degree M) heq
  rw [degree_mul] at hdeg
  have hpos := maximalFacePrefix_degree_pos M hp hne
  omega

end ArtinNormalisers.Homotopy5
