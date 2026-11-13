import ArtinRibbons.ReducedRibbons
import ArtinRibbons.RibbonPositiveCalculus

/-! # Positive generation by the actual outside elementary ribbons

Every positive source-left-reduced ribbon factors into the actual outside
fundamental-element ratios. The induction removes a positive elementary
factor and strictly decreases the actual exponent-sum length. Conversely,
every generated positive path remains positive and source-left-reduced.
-/

namespace ArtinNormalisers.Ribbon2

open OAI.HarmonicArtin

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group]

omit [Finite M.Group] in
private theorem positive_univ_of_selected (J : Set I) {a : Artin.Group M}
    (ha : a ∈ actualPositiveParabolic M J) : a ∈ actualPositiveParabolic M Set.univ :=
  Submonoid.closure_mono (Set.image_mono (Set.subset_univ J)) ha

omit [Finite M.Group] in
theorem one_leftReduced (J : Set I) : IsLeftParabolicallyReduced M J 1 := by
  intro i _ s hs he
  have hd := congrArg (degree M) he
  rw [degree_mul, degree_generator, degree_one] at hd
  have hn := degree_nonneg_of_mem_actualPositiveParabolic M Set.univ hs
  omega

/-- A selected atom cannot left-divide a fundamental-element ratio. Such a
divisor would make `Δ_J σ_i` simple, contradicting maximal parabolic length.
The nestedness premise is retained for the positive-ratio interface. -/
theorem parabolicDelta_ratio_leftReduced (J K : Set I) (_hJK : J ⊆ K) :
    IsLeftParabolicallyReduced M J ((parabolicDelta M J)⁻¹ * parabolicDelta M K) := by
  classical
  let := fundamental_finite_index M
  let := Fintype.ofFinite I
  intro i hi q hq he
  rw [← positiveToParent_mrange_eq_actual] at hq
  obtain ⟨q, rfl⟩ := hq
  have hfactor : (positiveDelta M J * positiveGenerator M i) * q = positiveDelta M K := by
    apply positiveToParent_injective M
    rw [map_mul, map_mul, positiveToParent_positiveDelta, positiveToParent_generator,
      positiveToParent_positiveDelta]
    calc
      parabolicDelta M J * Artin.generator M i * positiveToParent M q =
          parabolicDelta M J * (Artin.generator M i * positiveToParent M q) := mul_assoc _ _ _
      _ = parabolicDelta M J * ((parabolicDelta M J)⁻¹ * parabolicDelta M K) := by rw [he]
      _ = parabolicDelta M K := by group
  have hs := (positive_simple_factors M (positiveDelta M J * positiveGenerator M i) q
    (parabolicLongest M K) hfactor).1
  have hd := congrArg (positiveDegree M) hs
  simp only [positiveDegree_mul, positiveDelta, positiveDegree_simpleLift,
    positiveDegree_generator, map_mul, positiveToCoxeter_simpleLift,
    positiveToCoxeter_generator] at hd
  have hw : parabolicLongest M J * M.toCoxeterSystem.simple i ∈ Artin.coxeterParabolic M J :=
    (Artin.coxeterParabolic M J).mul_mem (parabolicLongest_mem_parabolic M J)
      (Subgroup.subset_closure ⟨i, hi, rfl⟩)
  have hmax := parabolicLongest_max M J hw
  omega

theorem elementaryMu_leftReduced (J : Set I) (a : I) :
    IsLeftParabolicallyReduced M J (elementaryMu M J a) :=
  parabolicDelta_ratio_leftReduced M J (insert a J) (Set.subset_insert a J)

theorem elementaryMu_ne_one (J : Set I) (a : I) (ha : a ∉ J) : elementaryMu M J a ≠ 1 := by
  intro he
  have hd : parabolicDelta M (insert a J) = parabolicDelta M J := by
    calc
      parabolicDelta M (insert a J) = parabolicDelta M J * elementaryMu M J a := by
        unfold elementaryMu
        group
      _ = parabolicDelta M J := by rw [he, mul_one]
  obtain ⟨q, hq, hdiv⟩ := (generator_leftDivides_parabolicDelta_iff M (insert a J) a).mpr
    (Set.mem_insert a J)
  exact ha ((generator_leftDivides_parabolicDelta_iff M J a).mp ⟨q, hq, hd ▸ hdiv⟩)

theorem elementaryMu_degree_pos (J : Set I) (a : I) (ha : a ∉ J) :
    0 < degree M (elementaryMu M J a) := by
  have hp := positive_univ_of_selected M (insert a J) (elementaryMu_positive M J a)
  have hn := degree_nonneg_of_mem_actualPositiveParabolic M Set.univ hp
  have hz := (degree_eq_zero_iff_of_mem_actualPositiveParabolic M Set.univ hp).not.mpr
    (elementaryMu_ne_one M J a ha)
  omega

omit [Finite M.Group] in
private theorem isRibbon_one_objects_eq {X Y : RibbonObject M} (h : IsRibbon M X Y 1) : X = Y :=
  congrArg (fun J : Set I => (⟨J⟩ : RibbonObject M))
    (isRibbon_target_indices_unique M (isRibbon_one M X) h)

theorem PositiveReducedArrow.positive {X Y : RibbonObject M} {r : Artin.Group M}
    (h : PositiveReducedArrow M X Y r) : r ∈ actualPositiveParabolic M Set.univ := by
  induction h with
  | identity X => exact Submonoid.one_mem _
  | elementary a ha hr =>
    exact positive_univ_of_selected M _ (elementaryMu_positive M _ a)
  | comp hβ hγ ihβ ihγ => exact Submonoid.mul_mem _ ihβ ihγ

theorem PositiveReducedArrow.isRibbon {X Y : RibbonObject M} {r : Artin.Group M}
    (h : PositiveReducedArrow M X Y r) : IsRibbon M X Y r :=
  ReducedArrow.isRibbon M (PositiveReducedArrow.toReducedArrow M h)

theorem PositiveReducedArrow.leftReduced {X Y : RibbonObject M} {r : Artin.Group M}
    (h : PositiveReducedArrow M X Y r) : IsLeftParabolicallyReduced M X.indices r := by
  induction h with
  | identity X => exact one_leftReduced M X.indices
  | elementary a ha hr => exact elementaryMu_leftReduced M _ a
  | comp hβ hγ ihβ ihγ =>
    exact positive_ribbon_mul_leftReduced M hβ.positive ihβ hβ.isRibbon hγ.positive ihγ

/-- Positive source-left-reduced ribbons are generated by the actual outside
elementary labels. The identity case proves equality of its actual endpoints. -/
theorem positive_leftReduced_ribbon_generated {X Y : RibbonObject M} {r : Artin.Group M}
    (hpos : r ∈ actualPositiveParabolic M Set.univ)
    (hred : IsLeftParabolicallyReduced M X.indices r) (hrib : IsRibbon M X Y r) :
    PositiveReducedArrow M X Y r := by
  have core : ∀ n (X Y : RibbonObject M) (r : Artin.Group M), (degree M r).toNat = n →
      r ∈ actualPositiveParabolic M Set.univ → IsLeftParabolicallyReduced M X.indices r →
      IsRibbon M X Y r → PositiveReducedArrow M X Y r := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro X Y r hn hp hred hrib
      by_cases hr1 : r = 1
      · subst r
        have hXY := isRibbon_one_objects_eq M hrib
        subst Y
        exact .identity X
      have hrpos := hp
      rw [← positiveToParent_mrange_eq_actual] at hp
      obtain ⟨p, hp⟩ := hp
      have hp1 : p ≠ 1 := by
        intro he
        apply hr1
        rw [← hp, he, map_one]
      obtain ⟨a, hat⟩ := exists_positive_first M hp1
      obtain ⟨t, hpt⟩ := hat
      have hfirst : r = Artin.generator M a * positiveToParent M t := by
        rw [← hp, hpt, map_mul, positiveToParent_generator]
      have ha : a ∉ X.indices := by
        intro hai
        exact hred a hai (positiveToParent M t) (positiveActualHom M t).property hfirst.symm
      let μ := elementaryMu M X.indices a
      let Z : RibbonObject M := ⟨parabolicTwistImage M (insert a X.indices) X.indices⟩
      have hμ : IsRibbon M X Z μ := elementaryMu_isRibbon M X.indices a
      have hμpos : μ ∈ actualPositiveParabolic M Set.univ :=
        positive_univ_of_selected M _ (elementaryMu_positive M X.indices a)
      have hδX : parabolicDelta M X.indices ∈ actualPositiveParabolic M Set.univ :=
        positive_univ_of_selected M _ (parabolicDelta_mem_positiveParabolic M X.indices)
      have hδY : parabolicDelta M Y.indices ∈ actualPositiveParabolic M Set.univ :=
        positive_univ_of_selected M _ (parabolicDelta_mem_positiveParabolic M Y.indices)
      have hAtom : ∃ q ∈ actualPositiveParabolic M Set.univ,
          parabolicDelta M X.indices * r = Artin.generator M a * q := by
        refine ⟨positiveToParent M t * parabolicDelta M Y.indices,
          (actualPositiveParabolic M Set.univ).mul_mem (positiveActualHom M t).property hδY, ?_⟩
        rw [IsRibbon.parabolicDelta_mul M hrib, hfirst, mul_assoc]
      obtain ⟨c, hc, hproduct⟩ := parabolicDelta_insert_left_lcm M X.indices a
        (parabolicDelta M X.indices * r)
        ((actualPositiveParabolic M Set.univ).mul_mem hδX hrpos) ⟨r, hrpos, rfl⟩ hAtom
      have hfactor : r = μ * c := by
        calc
          r = (parabolicDelta M X.indices)⁻¹ * (parabolicDelta M X.indices * r) := by group
          _ = (parabolicDelta M X.indices)⁻¹ * (parabolicDelta M (insert a X.indices) * c) := by
            rw [hproduct]
          _ = μ * c := by dsimp [μ, elementaryMu]; group
      have hcRibbon : IsRibbon M Z Y c := by
        have h := IsRibbon.mul M (IsRibbon.inv M hμ) hrib
        have he : μ⁻¹ * r = c := by rw [hfactor]; group
        simpa only [he] using h
      have hcReduced : IsLeftParabolicallyReduced M Z.indices c := by
        intro j hj s hs he
        obtain ⟨i, hi, hrel⟩ := IsRibbon.generator_reverse M hμ hj
        apply hred i hi (μ * s) ((actualPositiveParabolic M Set.univ).mul_mem hμpos hs)
        rw [← mul_assoc, hrel, mul_assoc, he, ← hfactor]
      have hμdeg : 0 < degree M μ := elementaryMu_degree_pos M X.indices a ha
      have hcdeg := degree_nonneg_of_mem_actualPositiveParabolic M Set.univ hc
      have hrdeg := degree_nonneg_of_mem_actualPositiveParabolic M Set.univ hrpos
      have hdeg : degree M r = degree M μ + degree M c := by rw [hfactor, degree_mul]
      have hlt : (degree M c).toNat < n := by omega
      have hgenerated := ih _ hlt Z Y c rfl hc hcReduced hcRibbon
      have hstep : PositiveReducedArrow M X Z μ := .elementary a ha hμ
      simpa only [← hfactor] using PositiveReducedArrow.comp hstep hgenerated
  exact core _ X Y r rfl hpos hred hrib

theorem positiveReducedArrow_iff {X Y : RibbonObject M} {r : Artin.Group M} :
    PositiveReducedArrow M X Y r ↔ r ∈ actualPositiveParabolic M Set.univ ∧
      IsLeftParabolicallyReduced M X.indices r ∧ IsRibbon M X Y r := by
  constructor
  · intro h
    exact ⟨h.positive, h.leftReduced, h.isRibbon⟩
  · rintro ⟨hp, hred, hrib⟩
    exact positive_leftReduced_ribbon_generated M hp hred hrib

end ArtinNormalisers.Ribbon2
