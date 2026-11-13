import ArtinRibbons.RibbonPositiveCalculus
import ArtinRibbons.ReducedRibbons
import ArtinRibbons.PositiveRibbons

/-!
# Cofinal positive loops in the actual reduced ribbon groupoid

The loops are actual products of parabolic fundamental elements. Their
positive generation and cofinality will clear signed generated ribbon paths;
no normalizer decomposition or abstract cofinality premise is used.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Ribbon2

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group]

/-- Global longest opposition on the index set of a parabolic. -/
noncomputable def cofinalTarget (J : Set I) : Set I :=
  parabolicTwistImage M Set.univ J

theorem cofinalTarget_involutive (J : Set I) :
    cofinalTarget M (cofinalTarget M J) = J := by
  classical
  have ht : Function.Involutive (parabolicTwist M Set.univ) :=
    parabolicTwistIndex_involutive M Set.univ
  ext i
  constructor
  · rintro ⟨u, ⟨v, hv, hvu⟩, hui⟩
    have huv : u = parabolicTwist M Set.univ v := Subtype.ext hvu.symm
    rw [huv] at hui
    change ((parabolicTwist M Set.univ) ((parabolicTwist M Set.univ) v) : I) = i at hui
    rw [ht] at hui
    exact hui ▸ hv
  · intro hi
    refine ⟨parabolicTwist M Set.univ ⟨i, Set.mem_univ i⟩,
      ⟨⟨i, Set.mem_univ i⟩, hi, rfl⟩, ?_⟩
    exact congrArg Subtype.val (ht ⟨i, Set.mem_univ i⟩)

/-- The positive half-turn ratio from a parabolic to its global opposition. -/
noncomputable def cofinalDelta (J : Set I) : Artin.Group M :=
  (parabolicDelta M J)⁻¹ * parabolicDelta M Set.univ

/-- The actual cofinal loop, before any cofinality assertion. -/
noncomputable def cofinalLoop (J : Set I) : Artin.Group M :=
  ((parabolicDelta M J)⁻¹) ^ 2 * (parabolicDelta M Set.univ) ^ 2

theorem cofinalDelta_isRibbon (J : Set I) :
    IsRibbon M ⟨J⟩ ⟨cofinalTarget M J⟩ (cofinalDelta M J) :=
  parabolicDelta_ratio_isRibbon M J Set.univ (Set.subset_univ J)

theorem cofinalDelta_positive (J : Set I) :
    cofinalDelta M J ∈ actualPositiveParabolic M Set.univ :=
  parabolicDelta_ratio_positive M J Set.univ (Set.subset_univ J)

/-- The global fundamental square is central in the unchanged Artin group. -/
theorem globalDelta_square_commute (a : Artin.Group M) :
    Commute ((parabolicDelta M Set.univ) ^ 2) a := by
  have ha : a ∈ Subgroup.closure (Set.range (Artin.generator M)) := by
    rw [Artin.closure_range_generator M]
    exact Subgroup.mem_top a
  induction ha using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, rfl⟩ := hg
    let j := parabolicTwist M Set.univ ⟨i, Set.mem_univ i⟩
    have h₁ := parabolicTwist_relation M Set.univ ⟨i, Set.mem_univ i⟩
    have h₂ := parabolicTwist_relation M Set.univ j
    have hji : (parabolicTwist M Set.univ j : I) = i := by
      exact congrArg Subtype.val (parabolicTwistIndex_involutive M Set.univ
        ⟨i, Set.mem_univ i⟩)
    change parabolicDelta M Set.univ * Artin.generator M i =
      Artin.generator M j * parabolicDelta M Set.univ at h₁
    rw [hji] at h₂
    change (parabolicDelta M Set.univ) ^ 2 * Artin.generator M i =
      Artin.generator M i * (parabolicDelta M Set.univ) ^ 2
    calc
      _ = parabolicDelta M Set.univ *
          (parabolicDelta M Set.univ * Artin.generator M i) := by simp only [pow_two]; group
      _ = parabolicDelta M Set.univ *
          (Artin.generator M j * parabolicDelta M Set.univ) := by rw [h₁]
      _ = (parabolicDelta M Set.univ * Artin.generator M j) *
          parabolicDelta M Set.univ := by group
      _ = (Artin.generator M i * parabolicDelta M Set.univ) *
          parabolicDelta M Set.univ := by rw [h₂]
      _ = _ := by simp only [pow_two]; group
  | one => exact Commute.one_right _
  | mul a b ha hb hca hcb => exact hca.mul_right hcb
  | inv a ha hca => exact hca.inv_right

theorem cofinalDelta_mul_cofinalDelta (J : Set I) :
    cofinalDelta M J * cofinalDelta M (cofinalTarget M J) = cofinalLoop M J := by
  have h := IsRibbon.parabolicDelta_mul M (cofinalDelta_isRibbon M J)
  have hd : parabolicDelta M Set.univ =
      cofinalDelta M J * parabolicDelta M (cofinalTarget M J) := by
    simpa only [cofinalDelta, mul_inv_cancel_left] using h
  have hm : parabolicDelta M Set.univ *
      (parabolicDelta M (cofinalTarget M J))⁻¹ = cofinalDelta M J := by
    rw [hd]
    group
  unfold cofinalDelta cofinalLoop
  calc
    _ = (parabolicDelta M J)⁻¹ *
        (parabolicDelta M Set.univ * (parabolicDelta M (cofinalTarget M J))⁻¹) *
          parabolicDelta M Set.univ := by group
    _ = (parabolicDelta M J)⁻¹ * cofinalDelta M J * parabolicDelta M Set.univ := by rw [hm]
    _ = _ := by unfold cofinalDelta; simp only [pow_two]; group

/-- Actual ribbon transport makes these concrete loops natural. -/
theorem IsRibbon.cofinalLoop_mul {X Y : RibbonObject M} {r : Artin.Group M}
    (h : IsRibbon M X Y r) :
    r * cofinalLoop M Y.indices = cofinalLoop M X.indices * r := by
  have hc := IsRibbon.parabolicDelta_conjugate M h
  have hm : r * (parabolicDelta M Y.indices)⁻¹ =
      (parabolicDelta M X.indices)⁻¹ * r := by
    rw [← hc]
    group
  have hz := (globalDelta_square_commute M r).eq
  unfold cofinalLoop
  calc
    _ = (r * (parabolicDelta M Y.indices)⁻¹) *
        (parabolicDelta M Y.indices)⁻¹ * (parabolicDelta M Set.univ) ^ 2 := by group
    _ = ((parabolicDelta M X.indices)⁻¹ * r) *
        (parabolicDelta M Y.indices)⁻¹ * (parabolicDelta M Set.univ) ^ 2 := by rw [hm]
    _ = (parabolicDelta M X.indices)⁻¹ *
        (r * (parabolicDelta M Y.indices)⁻¹) * (parabolicDelta M Set.univ) ^ 2 := by group
    _ = (parabolicDelta M X.indices)⁻¹ *
        ((parabolicDelta M X.indices)⁻¹ * r) * (parabolicDelta M Set.univ) ^ 2 := by rw [hm]
    _ = ((parabolicDelta M X.indices)⁻¹)^2 *
        (r * (parabolicDelta M Set.univ)^2) := by group
    _ = _ := by rw [← hz]; group

theorem IsRibbon.cofinalLoop_pow_mul {X Y : RibbonObject M} {r : Artin.Group M}
    (h : IsRibbon M X Y r) (n : ℕ) :
    r * cofinalLoop M Y.indices ^ n = cofinalLoop M X.indices ^ n * r := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ← mul_assoc, ih, mul_assoc, IsRibbon.cofinalLoop_mul M h,
      ← mul_assoc, ← pow_succ]

theorem positive_cofinalDelta (J : Set I) :
    PositiveReducedArrow M ⟨J⟩ ⟨cofinalTarget M J⟩ (cofinalDelta M J) :=
  positive_leftReduced_ribbon_generated M (cofinalDelta_positive M J)
    (parabolicDelta_ratio_leftReduced M J Set.univ (Set.subset_univ J))
    (cofinalDelta_isRibbon M J)

theorem positive_cofinalLoop (X : RibbonObject M) :
    PositiveReducedArrow M X X (cofinalLoop M X.indices) := by
  have h₁ := positive_cofinalDelta M X.indices
  have h₂ := positive_cofinalDelta M (cofinalTarget M X.indices)
  rw [cofinalTarget_involutive] at h₂
  have h := PositiveReducedArrow.comp h₁ h₂
  rw [cofinalDelta_mul_cofinalDelta] at h
  exact h

theorem positive_cofinalLoop_pow (X : RibbonObject M) (n : ℕ) :
    PositiveReducedArrow M X X (cofinalLoop M X.indices ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using PositiveReducedArrow.identity (M := M) X
  | succ n ih =>
    simpa only [pow_succ] using PositiveReducedArrow.comp ih (positive_cofinalLoop M X)

/-- Each actual outside generator has a positive generated complement in
the concrete cofinal loop at its source. -/
theorem elementaryMu_positive_complement {X Y : RibbonObject M} (a : I)
    (ha : a ∉ X.indices) (hr : IsRibbon M X Y (elementaryMu M X.indices a)) :
    ∃ t : Artin.Group M, PositiveReducedArrow M Y X t ∧
      elementaryMu M X.indices a * t = cofinalLoop M X.indices := by
  obtain ⟨q, hq, hD⟩ := parabolicDelta_prefix_of_subset M (insert a X.indices)
    Set.univ (Set.subset_univ _)
  have hprod : elementaryMu M X.indices a * q = cofinalDelta M X.indices := by
    unfold elementaryMu cofinalDelta
    rw [hD]
    group
  have hqrib : IsRibbon M Y ⟨cofinalTarget M X.indices⟩ q := by
    have h := (IsRibbon.inv M hr).mul M (cofinalDelta_isRibbon M X.indices)
    have he : (elementaryMu M X.indices a)⁻¹ * cofinalDelta M X.indices = q := by
      rw [← hprod]
      group
    simpa only [he] using h
  have hμ : PositiveReducedArrow M X Y (elementaryMu M X.indices a) :=
    .elementary a ha hr
  have hqred : IsLeftParabolicallyReduced M Y.indices q := by
    intro j hj s hs he
    obtain ⟨i, hi, hrel⟩ := IsRibbon.generator_reverse M hr hj
    apply (parabolicDelta_ratio_leftReduced M X.indices Set.univ
      (Set.subset_univ X.indices)) i hi
      (elementaryMu M X.indices a * s)
      ((actualPositiveParabolic M Set.univ).mul_mem hμ.positive hs)
    change Artin.generator M i * (elementaryMu M X.indices a * s) = cofinalDelta M X.indices
    rw [← mul_assoc, hrel, mul_assoc, he, hprod]
  have hqgen := positive_leftReduced_ribbon_generated M hq hqred hqrib
  have hδ := positive_cofinalDelta M (cofinalTarget M X.indices)
  rw [cofinalTarget_involutive] at hδ
  refine ⟨q * cofinalDelta M (cofinalTarget M X.indices),
    PositiveReducedArrow.comp hqgen hδ, ?_⟩
  rw [← mul_assoc, hprod, cofinalDelta_mul_cofinalDelta]

/-- Every positive generated path divides a power of the concrete source
loop, with a positive generated complementary path. -/
theorem PositiveReducedArrow.positive_complement {X Y : RibbonObject M} {β : Artin.Group M}
    (h : PositiveReducedArrow M X Y β) :
    ∃ (n : ℕ) (q : Artin.Group M), PositiveReducedArrow M Y X q ∧
      β * q = cofinalLoop M X.indices ^ n := by
  induction h with
  | identity X =>
    exact ⟨0, 1, .identity X, by simp⟩
  | elementary a ha hr =>
    obtain ⟨q, hq, he⟩ := elementaryMu_positive_complement M a ha hr
    exact ⟨1, q, hq, by simpa only [pow_one] using he⟩
  | @comp X Y Z β γ hβ hγ ihβ ihγ =>
    obtain ⟨n, p, hp, hprodβ⟩ := ihβ
    obtain ⟨m, q, hq, hprodγ⟩ := ihγ
    refine ⟨m + n, q * p, .comp hq hp, ?_⟩
    calc
      (β * γ) * (q * p) = β * (γ * q) * p := by group
      _ = β * cofinalLoop M Y.indices ^ m * p := by rw [hprodγ]
      _ = (cofinalLoop M X.indices ^ m * β) * p := by
        rw [IsRibbon.cofinalLoop_pow_mul M hβ.isRibbon m]
      _ = cofinalLoop M X.indices ^ m * (β * p) := by group
      _ = cofinalLoop M X.indices ^ m * cofinalLoop M X.indices ^ n := by rw [hprodβ]
      _ = cofinalLoop M X.indices ^ (m + n) := (pow_add _ _ _).symm

/-- Every signed generated ribbon is a fraction of two actual positive
generated paths, with a canonical target-loop power as denominator. -/
theorem ReducedArrow.positive_fraction {X Y : RibbonObject M} {β : Artin.Group M}
    (h : ReducedArrow M X Y β) :
    ∃ (n : ℕ) (p : Artin.Group M), PositiveReducedArrow M X Y p ∧
      β = p * (cofinalLoop M Y.indices ^ n)⁻¹ := by
  induction h with
  | identity X =>
    exact ⟨0, 1, .identity X, by simp⟩
  | elementary a ha hr =>
    exact ⟨0, _, .elementary a ha hr, by simp⟩
  | @comp X Y Z β γ hβ hγ ihβ ihγ =>
    obtain ⟨n, p, hp, hprodβ⟩ := ihβ
    obtain ⟨m, q, hq, hprodγ⟩ := ihγ
    have hmove : (cofinalLoop M Y.indices ^ n)⁻¹ * q =
        q * (cofinalLoop M Z.indices ^ n)⁻¹ := by
      have hqn := IsRibbon.cofinalLoop_pow_mul M hq.isRibbon n
      calc
        _ = (cofinalLoop M Y.indices ^ n)⁻¹ *
            (q * cofinalLoop M Z.indices ^ n) * (cofinalLoop M Z.indices ^ n)⁻¹ := by group
        _ = (cofinalLoop M Y.indices ^ n)⁻¹ *
            (cofinalLoop M Y.indices ^ n * q) * (cofinalLoop M Z.indices ^ n)⁻¹ := by rw [hqn]
        _ = _ := by group
    refine ⟨m + n, p * q, .comp hp hq, ?_⟩
    rw [hprodβ, hprodγ]
    calc
      (p * (cofinalLoop M Y.indices ^ n)⁻¹) *
          (q * (cofinalLoop M Z.indices ^ m)⁻¹) =
        p * ((cofinalLoop M Y.indices ^ n)⁻¹ * q) *
          (cofinalLoop M Z.indices ^ m)⁻¹ := by group
      _ = p * (q * (cofinalLoop M Z.indices ^ n)⁻¹) *
          (cofinalLoop M Z.indices ^ m)⁻¹ := by rw [hmove]
      _ = (p * q) * (cofinalLoop M Z.indices ^ (m + n))⁻¹ := by
        simp only [pow_add, mul_inv_rev, mul_assoc]
  | @inverse X Y β h ih =>
    obtain ⟨n, p, hp, hprod⟩ := ih
    obtain ⟨m, q, hq, hcomp⟩ := PositiveReducedArrow.positive_complement M hp
    have hinv : p⁻¹ = q * (cofinalLoop M X.indices ^ m)⁻¹ := by
      calc
        p⁻¹ = p⁻¹ * (p * q) * (cofinalLoop M X.indices ^ m)⁻¹ := by rw [hcomp]; group
        _ = _ := by group
    refine ⟨m, q * cofinalLoop M X.indices ^ n,
      .comp hq (positive_cofinalLoop_pow M X n), ?_⟩
    rw [hprod, mul_inv_rev, inv_inv, hinv]
    have hqn := IsRibbon.cofinalLoop_pow_mul M hq.isRibbon n
    calc
      cofinalLoop M Y.indices ^ n * (q * (cofinalLoop M X.indices ^ m)⁻¹) =
        (cofinalLoop M Y.indices ^ n * q) * (cofinalLoop M X.indices ^ m)⁻¹ := by group
      _ = _ := by rw [← hqn]

end ArtinNormalisers.Ribbon2
