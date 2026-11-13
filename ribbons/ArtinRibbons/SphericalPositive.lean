import ArtinRibbons.PositiveEmbedding
import ArtinNormalisers.Theorem18.Geometry
import OAI.Topology.ArtinGroups.Harmonic.PositiveReverseHom
import OAI.Topology.ArtinGroups.Harmonic.PositiveDegreeSublevelFinite
import OAI.Topology.ArtinGroups.Harmonic.FiniteArtinPositiveLeft

/-! # Spherical positive cancellation, divisibility and fractions

Cancellation comes from the proved canonical embedding into the actual Artin
group. The generic positive-head and divisor theorems then apply globally,
without restricting the index universe or adding finite rank as a hypothesis.
-/

namespace ArtinNormalisers.Ribbon2

open OAI.HarmonicArtin OAI.HarmonicArtin.Geometric

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group]

/-- The actual positive presentation is cancellative because its canonical
homomorphism into the unchanged parent group is injective. -/
noncomputable instance positiveCancelMonoid : CancelMonoid (PositiveArtin M) :=
  Function.Injective.cancelMonoid (positiveToParent M) (positiveToParent_injective M)
    (positiveToParent M).map_one (positiveToParent M).map_mul (positiveToParent M).map_pow

theorem positive_cancel_left (a b c : PositiveArtin M) (h : a * b = a * c) : b = c :=
  mul_left_cancel h

theorem positive_cancel_right (a b c : PositiveArtin M) (h : b * a = c * a) : b = c :=
  mul_right_cancel h

theorem positive_head (a : PositiveArtin M) : HasPositiveHead M a := by
  classical
  have := Theorem18.finite_index M
  let := Fintype.ofFinite I
  obtain ⟨z, hz⟩ := exists_longest M.toCoxeterSystem
  exact positive_greedy_head M (positive_cancel_left M) z hz a

theorem positive_gcd_left (a b : PositiveArtin M) :
    ∃ g : PositiveArtin M, PositivePrefix M g a ∧ PositivePrefix M g b ∧
      ∀ e : PositiveArtin M, PositivePrefix M e a → PositivePrefix M e b →
        PositivePrefix M e g := by
  classical
  have := Theorem18.finite_index M
  let := Fintype.ofFinite I
  obtain ⟨z, hz⟩ := exists_longest M.toCoxeterSystem
  exact positive_greatest_common_left_divisor M (positive_cancel_left M) z hz a b

theorem positive_gcd_right (a b : PositiveArtin M) :
    ∃ g : PositiveArtin M, PositiveSuffix M g a ∧ PositiveSuffix M g b ∧
      ∀ e : PositiveArtin M, PositiveSuffix M e a → PositiveSuffix M e b →
        PositiveSuffix M e g := by
  classical
  have := Theorem18.finite_index M
  let := Fintype.ofFinite I
  obtain ⟨z, hz⟩ := exists_longest M.toCoxeterSystem
  exact positive_greatest_common_right_divisor M z hz (positive_cancel_left M) a b

/-- Every actual Artin element is a right fraction of positive elements,
transported through the generator-preserving presentation equivalence. -/
theorem positive_fraction (g : Artin.Group M) :
    ∃ a b : PositiveArtin M,
      g = positiveToParent M a * (positiveToParent M b)⁻¹ := by
  classical
  have := Theorem18.finite_index M
  let := Fintype.ofFinite I
  obtain ⟨u, v, h⟩ := finiteArtin_positive_fraction M ((presentationEquiv M).symm g)
  have he := congrArg (presentationEquiv M) h
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, presentationEquiv_word] at he
  exact ⟨wordPositive M u, wordPositive M v, by simpa only [positiveToParent_word] using he⟩

theorem positive_left_fraction (g : Artin.Group M) :
    ∃ a b : PositiveArtin M,
      g = (positiveToParent M a)⁻¹ * positiveToParent M b := by
  classical
  have := Theorem18.finite_index M
  let := Fintype.ofFinite I
  obtain ⟨u, v, h⟩ := finiteArtin_positive_left_fraction M ((presentationEquiv M).symm g)
  have he := congrArg (presentationEquiv M) h
  simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, presentationEquiv_word] at he
  exact ⟨wordPositive M u, wordPositive M v, by simpa only [positiveToParent_word] using he⟩

/-- Two positives have a common right multiple, obtained from actual group
fractions and reflected through the proved injective canonical map. -/
theorem positive_common_multiple_left (a b : PositiveArtin M) :
    ∃ c : PositiveArtin M, PositivePrefix M a c ∧ PositivePrefix M b c := by
  let f := positiveToParent M
  obtain ⟨x, y, hxy⟩ := positive_fraction M ((f a)⁻¹ * f b)
  have he : f (a * x) = f (b * y) := by
    rw [map_mul, map_mul]
    have hm := eq_mul_inv_iff_mul_eq.mp hxy
    rw [mul_assoc] at hm
    exact (inv_mul_eq_iff_eq_mul.mp hm).symm
  have hp := positiveToParent_injective M he
  exact ⟨a * x, ⟨x, rfl⟩, ⟨y, hp⟩⟩

theorem positive_common_multiple_right (a b : PositiveArtin M) :
    ∃ c : PositiveArtin M, PositiveSuffix M a c ∧ PositiveSuffix M b c := by
  let f := positiveToParent M
  obtain ⟨x, y, hxy⟩ := positive_left_fraction M (f a * (f b)⁻¹)
  change f a * (f b)⁻¹ = (f x)⁻¹ * f y at hxy
  have he : f (x * a) = f (y * b) := by
    rw [map_mul, map_mul]
    calc
      f x * f a = (f x * (f a * (f b)⁻¹)) * f b := by group
      _ = f y * f b := by rw [hxy]; group
  have hp := positiveToParent_injective M he
  exact ⟨x * a, ⟨x, rfl⟩, ⟨y, hp⟩⟩

theorem positive_lcm_left (a b : PositiveArtin M) :
    ∃ c : PositiveArtin M, PositivePrefix M a c ∧ PositivePrefix M b c ∧
      ∀ d : PositiveArtin M, PositivePrefix M a d → PositivePrefix M b d →
        PositivePrefix M c d :=
  positive_lcm_of_common_multiple M (positive_gcd_left M) a b
    (positive_common_multiple_left M a b)

/-- The suffix version of the source's minimal-degree/gcd argument. -/
theorem positive_lcm_right (a b : PositiveArtin M) :
    ∃ c : PositiveArtin M, PositiveSuffix M a c ∧ PositiveSuffix M b c ∧
      ∀ d : PositiveArtin M, PositiveSuffix M a d → PositiveSuffix M b d →
        PositiveSuffix M c d := by
  classical
  let P : ℕ → Prop := fun n => ∃ c : PositiveArtin M,
    PositiveSuffix M a c ∧ PositiveSuffix M b c ∧ positiveDegree M c = n
  have hex : ∃ n, P n := by
    obtain ⟨c, hac, hbc⟩ := positive_common_multiple_right M a b
    exact ⟨positiveDegree M c, c, hac, hbc, rfl⟩
  obtain ⟨c, hac, hbc, hc⟩ := Nat.find_spec hex
  refine ⟨c, hac, hbc, ?_⟩
  intro d had hbd
  obtain ⟨e, hec, hed, he⟩ := positive_gcd_right M c d
  have hae := he a hac had
  have hbe := he b hbc hbd
  have hmin : positiveDegree M c ≤ positiveDegree M e := by
    rw [hc]
    exact Nat.find_min' hex ⟨e, hae, hbe, rfl⟩
  have hedeg : positiveDegree M e ≤ positiveDegree M c := by
    obtain ⟨u, hu⟩ := hec
    rw [hu, positiveDegree_mul]
    omega
  have heq : e = c := by
    obtain ⟨u, hu⟩ := hec
    have hu0 : positiveDegree M u = 0 := by
      have hedeg' := Nat.le_antisymm hedeg hmin
      rw [hu, positiveDegree_mul] at hedeg'
      omega
    rw [(positiveDegree_zero_iff M u).mp hu0, one_mul] at hu
    exact hu.symm
  rwa [heq] at hed

/-- Left divisibility in the actual generated positive cone. -/
def ActualLeftDivides (a b : actualPositiveParabolic M Set.univ) : Prop :=
  ∃ c : actualPositiveParabolic M Set.univ, b = a * c

/-- Right divisibility in the actual generated positive cone. -/
def ActualRightDivides (a b : actualPositiveParabolic M Set.univ) : Prop :=
  ∃ c : actualPositiveParabolic M Set.univ, b = c * a

theorem positiveActualEquiv_leftDivides_iff (a b : PositiveArtin M) :
    ActualLeftDivides M (positiveActualEquiv M a) (positiveActualEquiv M b) ↔
      PositivePrefix M a b := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨d, rfl⟩ := (positiveActualEquiv M).surjective c
    exact ⟨d, (positiveActualEquiv M).injective (by simpa only [map_mul] using hc)⟩
  · rintro ⟨c, rfl⟩
    exact ⟨positiveActualEquiv M c, map_mul _ _ _⟩

theorem positiveActualEquiv_rightDivides_iff (a b : PositiveArtin M) :
    ActualRightDivides M (positiveActualEquiv M a) (positiveActualEquiv M b) ↔
      PositiveSuffix M a b := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨d, rfl⟩ := (positiveActualEquiv M).surjective c
    exact ⟨d, (positiveActualEquiv M).injective (by simpa only [map_mul] using hc)⟩
  · rintro ⟨c, rfl⟩
    exact ⟨positiveActualEquiv M c, map_mul _ _ _⟩

theorem actualPositive_gcd_left (a b : actualPositiveParabolic M Set.univ) :
    ∃ g : actualPositiveParabolic M Set.univ, ActualLeftDivides M g a ∧ ActualLeftDivides M g b ∧
      ∀ e, ActualLeftDivides M e a → ActualLeftDivides M e b → ActualLeftDivides M e g := by
  obtain ⟨a, rfl⟩ := (positiveActualEquiv M).surjective a
  obtain ⟨b, rfl⟩ := (positiveActualEquiv M).surjective b
  obtain ⟨g, hga, hgb, hg⟩ := positive_gcd_left M a b
  refine ⟨positiveActualEquiv M g, (positiveActualEquiv_leftDivides_iff M g a).mpr hga,
    (positiveActualEquiv_leftDivides_iff M g b).mpr hgb, ?_⟩
  intro e hea heb
  obtain ⟨e, rfl⟩ := (positiveActualEquiv M).surjective e
  exact (positiveActualEquiv_leftDivides_iff M e g).mpr (hg e
    ((positiveActualEquiv_leftDivides_iff M e a).mp hea)
    ((positiveActualEquiv_leftDivides_iff M e b).mp heb))

theorem actualPositive_gcd_right (a b : actualPositiveParabolic M Set.univ) :
    ∃ g : actualPositiveParabolic M Set.univ, ActualRightDivides M g a ∧ ActualRightDivides M g b ∧
      ∀ e, ActualRightDivides M e a → ActualRightDivides M e b → ActualRightDivides M e g := by
  obtain ⟨a, rfl⟩ := (positiveActualEquiv M).surjective a
  obtain ⟨b, rfl⟩ := (positiveActualEquiv M).surjective b
  obtain ⟨g, hga, hgb, hg⟩ := positive_gcd_right M a b
  refine ⟨positiveActualEquiv M g, (positiveActualEquiv_rightDivides_iff M g a).mpr hga,
    (positiveActualEquiv_rightDivides_iff M g b).mpr hgb, ?_⟩
  intro e hea heb
  obtain ⟨e, rfl⟩ := (positiveActualEquiv M).surjective e
  exact (positiveActualEquiv_rightDivides_iff M e g).mpr (hg e
    ((positiveActualEquiv_rightDivides_iff M e a).mp hea)
    ((positiveActualEquiv_rightDivides_iff M e b).mp heb))

theorem actualPositive_lcm_left (a b : actualPositiveParabolic M Set.univ) :
    ∃ c : actualPositiveParabolic M Set.univ, ActualLeftDivides M a c ∧ ActualLeftDivides M b c ∧
      ∀ d, ActualLeftDivides M a d → ActualLeftDivides M b d → ActualLeftDivides M c d := by
  obtain ⟨a, rfl⟩ := (positiveActualEquiv M).surjective a
  obtain ⟨b, rfl⟩ := (positiveActualEquiv M).surjective b
  obtain ⟨c, hac, hbc, hc⟩ := positive_lcm_left M a b
  refine ⟨positiveActualEquiv M c, (positiveActualEquiv_leftDivides_iff M a c).mpr hac,
    (positiveActualEquiv_leftDivides_iff M b c).mpr hbc, ?_⟩
  intro d had hbd
  obtain ⟨d, rfl⟩ := (positiveActualEquiv M).surjective d
  exact (positiveActualEquiv_leftDivides_iff M c d).mpr (hc d
    ((positiveActualEquiv_leftDivides_iff M a d).mp had)
    ((positiveActualEquiv_leftDivides_iff M b d).mp hbd))

theorem actualPositive_lcm_right (a b : actualPositiveParabolic M Set.univ) :
    ∃ c : actualPositiveParabolic M Set.univ, ActualRightDivides M a c ∧ ActualRightDivides M b c ∧
      ∀ d, ActualRightDivides M a d → ActualRightDivides M b d → ActualRightDivides M c d := by
  obtain ⟨a, rfl⟩ := (positiveActualEquiv M).surjective a
  obtain ⟨b, rfl⟩ := (positiveActualEquiv M).surjective b
  obtain ⟨c, hac, hbc, hc⟩ := positive_lcm_right M a b
  refine ⟨positiveActualEquiv M c, (positiveActualEquiv_rightDivides_iff M a c).mpr hac,
    (positiveActualEquiv_rightDivides_iff M b c).mpr hbc, ?_⟩
  intro d had hbd
  obtain ⟨d, rfl⟩ := (positiveActualEquiv M).surjective d
  exact (positiveActualEquiv_rightDivides_iff M c d).mpr (hc d
    ((positiveActualEquiv_rightDivides_iff M a d).mp had)
    ((positiveActualEquiv_rightDivides_iff M b d).mp hbd))

end ArtinNormalisers.Ribbon2
