import ArtinRibbons.Positive

/-!
# Removing positive parabolic factors from both ends

The middle element has minimum positive degree among actual decompositions
`p = a * r * b`. Moving any selected generator from the middle to an outside
factor would decrease that degree. This uses only the actual exponent sum;
no positive embedding, Garside lattice, or ribbon-normalizer splitting is assumed.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Ribbon2

variable {I : Type*} (M : CoxeterMatrix I) (J : Set I)

/-- No selected generator is a positive left divisor of this actual element. -/
def IsLeftParabolicallyReduced (r : Artin.Group M) : Prop :=
  ∀ i ∈ J, ∀ s ∈ actualPositiveParabolic M Set.univ, Artin.generator M i * s ≠ r

/-- No selected generator is a positive right divisor of this actual element. -/
def IsRightParabolicallyReduced (r : Artin.Group M) : Prop :=
  ∀ i ∈ J, ∀ s ∈ actualPositiveParabolic M Set.univ, s * Artin.generator M i ≠ r

/-- Strip actual positive parabolic factors on both sides, leaving an actual
positive element with no selected generator as a positive divisor on either end. -/
theorem exists_positive_parabolic_double_reduction (p : Artin.Group M)
    (hp : p ∈ actualPositiveParabolic M Set.univ) :
    ∃ a r b : Artin.Group M,
      a ∈ actualPositiveParabolic M J ∧
      r ∈ actualPositiveParabolic M Set.univ ∧
      b ∈ actualPositiveParabolic M J ∧
      p = a * r * b ∧
      IsLeftParabolicallyReduced M J r ∧ IsRightParabolicallyReduced M J r := by
  classical
  let P : ℕ → Prop := fun n => ∃ a r b : Artin.Group M,
    a ∈ actualPositiveParabolic M J ∧
    r ∈ actualPositiveParabolic M Set.univ ∧
    b ∈ actualPositiveParabolic M J ∧ p = a * r * b ∧ (degree M r).toNat = n
  have hex : ∃ n, P n := by
    refine ⟨(degree M p).toNat, 1, p, 1, (actualPositiveParabolic M J).one_mem,
      hp, (actualPositiveParabolic M J).one_mem, ?_, rfl⟩
    simp
  obtain ⟨a, r, b, ha, hr, hb, hprod, hdeg⟩ := Nat.find_spec hex
  refine ⟨a, r, b, ha, hr, hb, hprod, ?_, ?_⟩
  · intro i hi s hs heq
    have hnew : P (degree M s).toNat := by
      refine ⟨a * Artin.generator M i, s, b,
        (actualPositiveParabolic M J).mul_mem ha
          (generator_mem_actualPositiveParabolic M J hi), hs, hb, ?_, rfl⟩
      simpa only [← heq, mul_assoc] using hprod
    have hmin := Nat.find_min' hex hnew
    have hsdeg := degree_nonneg_of_mem_actualPositiveParabolic M Set.univ hs
    have hstep : degree M r = 1 + degree M s := by
      rw [← heq, degree_mul, degree_generator]
    omega
  · intro i hi s hs heq
    have hnew : P (degree M s).toNat := by
      refine ⟨a, s, Artin.generator M i * b, ha, hs,
        (actualPositiveParabolic M J).mul_mem
          (generator_mem_actualPositiveParabolic M J hi) hb, ?_, rfl⟩
      simpa only [← heq, mul_assoc] using hprod
    have hmin := Nat.find_min' hex hnew
    have hsdeg := degree_nonneg_of_mem_actualPositiveParabolic M Set.univ hs
    have hstep : degree M r = degree M s + 1 := by
      rw [← heq, degree_mul, degree_generator]
    omega

/-- Removing parabolic group factors from a normalizer element preserves
normalizer membership. The factors here need not be positive. -/
theorem middle_mem_normalizer_of_parabolic_factors {p a r b : Artin.Group M}
    (ha : a ∈ Artin.parabolic M J) (hb : b ∈ Artin.parabolic M J)
    (hp : p ∈ Subgroup.normalizer (Artin.parabolic M J : Set (Artin.Group M)))
    (hprod : p = a * r * b) :
    r ∈ Subgroup.normalizer (Artin.parabolic M J : Set (Artin.Group M)) := by
  have haN := (Artin.parabolic M J).le_normalizer ha
  have hbN := (Artin.parabolic M J).le_normalizer hb
  have hr : a⁻¹ * p * b⁻¹ = r := by
    rw [hprod]
    group
  rw [← hr]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ haN) hp)
    (Subgroup.inv_mem _ hbN)

/-- The positive double reduction of an actual normalizer element has an
actual middle normalizer element, with no Garside or splitting hypothesis. -/
theorem exists_positive_normalizer_double_reduction (p : Artin.Group M)
    (hp : p ∈ actualPositiveParabolic M Set.univ)
    (hpN : p ∈ Subgroup.normalizer (Artin.parabolic M J : Set (Artin.Group M))) :
    ∃ a r b : Artin.Group M,
      a ∈ actualPositiveParabolic M J ∧
      r ∈ actualPositiveParabolic M Set.univ ∧
      b ∈ actualPositiveParabolic M J ∧
      p = a * r * b ∧
      IsLeftParabolicallyReduced M J r ∧
      IsRightParabolicallyReduced M J r ∧
      r ∈ Subgroup.normalizer (Artin.parabolic M J : Set (Artin.Group M)) := by
  obtain ⟨a, r, b, ha, hr, hb, hprod, hleft, hright⟩ :=
    exists_positive_parabolic_double_reduction M J p hp
  exact ⟨a, r, b, ha, hr, hb, hprod, hleft, hright,
    middle_mem_normalizer_of_parabolic_factors M J
      (actualPositiveParabolic_le_parabolic M J ha)
      (actualPositiveParabolic_le_parabolic M J hb) hpN hprod⟩

end ArtinNormalisers.Ribbon2
