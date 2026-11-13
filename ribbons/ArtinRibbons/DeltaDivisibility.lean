import ArtinRibbons.Fundamental
import ArtinRibbons.SphericalPositive
import ArtinRibbons.PositiveSupport
import OAI.Topology.ArtinGroups.Harmonic.RestrictionHomRange

/-! # The actual parabolic fundamental element as a global positive lcm

The positive head and the longest-descent factor theorem identify the
fundamental element as the least common left multiple of its selected atoms
in the entire positive monoid. All conclusions are transported to the actual
parent Artin group through the proved canonical embedding.
-/

namespace ArtinNormalisers.Ribbon2

open OAI.HarmonicArtin OAI.HarmonicArtin.CoxeterExchange OAI.HarmonicArtin.Geometric

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group]

/-- Prefixes in the presented positive monoid are precisely positive right
quotients in the actual Artin group. -/
theorem positivePrefix_iff_parentQuotient (a b : PositiveArtin M) :
    PositivePrefix M a b ↔ ∃ q ∈ actualPositiveParabolic M Set.univ,
      positiveToParent M b = positiveToParent M a * q := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨positiveToParent M c, (positiveActualHom M c).property,
      by rw [hc, map_mul]⟩
  · rintro ⟨q, hq, he⟩
    rw [← positiveToParent_mrange_eq_actual] at hq
    obtain ⟨c, rfl⟩ := hq
    exact ⟨c, positiveToParent_injective M (by simpa only [map_mul] using he)⟩

theorem positiveSuffix_iff_parentQuotient (a b : PositiveArtin M) :
    PositiveSuffix M a b ↔ ∃ q ∈ actualPositiveParabolic M Set.univ,
      positiveToParent M b = q * positiveToParent M a := by
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨positiveToParent M c, (positiveActualHom M c).property,
      by rw [hc, map_mul]⟩
  · rintro ⟨q, hq, he⟩
    rw [← positiveToParent_mrange_eq_actual] at hq
    obtain ⟨c, rfl⟩ := hq
    exact ⟨c, positiveToParent_injective M (by simpa only [map_mul] using he)⟩

/-- The canonical presented positive lift of the actual parabolic longest
element. This is connected to `parabolicDelta`, rather than replacing it. -/
noncomputable def positiveDelta (J : Set I) : PositiveArtin M :=
  positiveSimpleLift M (parabolicLongest M J)

@[simp] theorem positiveToParent_positiveDelta (J : Set I) :
    positiveToParent M (positiveDelta M J) = parabolicDelta M J := by
  rw [positiveDelta, parabolicDelta_eq_globalPositiveLift]
  change positiveToParent M (wordPositive M (reducedExpression M (parabolicLongest M J))) =
    toParent M (wordArtin M (reducedExpression M (parabolicLongest M J)))
  rw [positiveToParent_word]
  exact (presentationEquiv_word M _).symm

omit [Finite M.Group] in
@[simp] theorem projection_positiveSimpleLift (w : M.Group) :
    Artin.projection M (positiveToParent M (positiveSimpleLift M w)) = w := by
  change Artin.projection M (positiveToParent M (wordPositive M (reducedExpression M w))) = w
  rw [positiveToParent_word, Artin.projection_wordProd]
  exact wordCoxeter_reducedExpression M w

omit [Finite M.Group] in
private theorem selected_of_simpleLift_mem (J : Set I) (w : M.Group)
    (hw : positiveToParent M (positiveSimpleLift M w) ∈ actualPositiveParabolic M J) :
    w ∈ Artin.coxeterParabolic M J := by
  have hpar := actualPositiveParabolic_le_parabolic M J hw
  have hm : Artin.projection M (positiveToParent M (positiveSimpleLift M w)) ∈
      (Artin.parabolic M J).map (Artin.projection M) := ⟨_, hpar, rfl⟩
  simpa only [Artin.map_parabolic, projection_positiveSimpleLift] using hm

/-- The selected Coxeter elements give exactly the simple left divisors. -/
theorem positiveSimpleLift_prefix_positiveDelta_iff (J : Set I) (w : M.Group) :
    PositivePrefix M (positiveSimpleLift M w) (positiveDelta M J) ↔
      w ∈ Artin.coxeterParabolic M J := by
  classical
  let := fundamental_finite_index M
  let := Fintype.ofFinite I
  constructor
  · rintro ⟨c, hc⟩
    apply selected_of_simpleLift_mem M J w
    apply (positive_factors_mem_actualPositiveParabolic M J _ c ?_).1
    rw [← hc, positiveToParent_positiveDelta]
    exact parabolicDelta_mem_positiveParabolic M J
  · intro hw
    exact (positivePrefix_simple_iff M _ _).mpr (parabolicLongest_left_length M J hw).symm

theorem positiveSimpleLift_suffix_positiveDelta_iff (J : Set I) (w : M.Group) :
    PositiveSuffix M (positiveSimpleLift M w) (positiveDelta M J) ↔
      w ∈ Artin.coxeterParabolic M J := by
  classical
  let := fundamental_finite_index M
  let := Fintype.ofFinite I
  constructor
  · rintro ⟨c, hc⟩
    apply selected_of_simpleLift_mem M J w
    apply (positive_factors_mem_actualPositiveParabolic M J c _ ?_).2
    rw [← hc, positiveToParent_positiveDelta]
    exact parabolicDelta_mem_positiveParabolic M J
  · intro hw
    let z := parabolicLongest M J
    have hzz : z * z = 1 := parabolicLongest_mul_self M J
    have hzi : z⁻¹ = z := by
      calc
        z⁻¹ = z⁻¹ * (z * z) := by rw [hzz, mul_one]
        _ = z := by group
    have hl := parabolicLongest_left_length M J ((Artin.coxeterParabolic M J).inv_mem hw)
    simp only [inv_inv, M.toCoxeterSystem.length_inv] at hl
    change M.toCoxeterSystem.length w + M.toCoxeterSystem.length (w * z) =
      M.toCoxeterSystem.length z at hl
    have hi : M.toCoxeterSystem.length (z * w⁻¹) =
        M.toCoxeterSystem.length (w * z) := by
      rw [← M.toCoxeterSystem.length_inv (z * w⁻¹)]
      simp only [mul_inv_rev, inv_inv, hzi]
    have hlen : M.toCoxeterSystem.length ((z * w⁻¹) * w) =
        M.toCoxeterSystem.length (z * w⁻¹) + M.toCoxeterSystem.length w := by
      rw [inv_mul_cancel_right, hi]
      exact (by omega : M.toCoxeterSystem.length z =
        M.toCoxeterSystem.length (w * z) + M.toCoxeterSystem.length w)
    exact ⟨positiveSimpleLift M (z * w⁻¹), by
      simpa only [inv_mul_cancel_right, positiveDelta, z] using
        positiveSimpleLift_mul M (z * w⁻¹) w hlen⟩

/-- All left divisors, not merely the atoms, are exactly the selected simple
positive lifts. -/
theorem positive_prefix_positiveDelta_iff (J : Set I) (p : PositiveArtin M) :
    PositivePrefix M p (positiveDelta M J) ↔
      ∃ w ∈ Artin.coxeterParabolic M J, p = positiveSimpleLift M w := by
  classical
  let := fundamental_finite_index M
  let := Fintype.ofFinite I
  constructor
  · intro hp
    obtain ⟨c, hc⟩ := hp
    have he := (positive_simple_factors M p c (parabolicLongest M J) hc.symm).1
    refine ⟨positiveToCoxeter M p, ?_, he⟩
    apply (positiveSimpleLift_prefix_positiveDelta_iff M J _).mp
    rw [← he]
    exact ⟨c, hc⟩
  · rintro ⟨w, hw, rfl⟩
    exact (positiveSimpleLift_prefix_positiveDelta_iff M J w).mpr hw

theorem positive_suffix_positiveDelta_iff (J : Set I) (p : PositiveArtin M) :
    PositiveSuffix M p (positiveDelta M J) ↔
      ∃ w ∈ Artin.coxeterParabolic M J, p = positiveSimpleLift M w := by
  classical
  let := fundamental_finite_index M
  let := Fintype.ofFinite I
  constructor
  · intro hp
    obtain ⟨c, hc⟩ := hp
    have he := (positive_simple_factors M c p (parabolicLongest M J) hc.symm).2
    refine ⟨positiveToCoxeter M p, ?_, he⟩
    apply (positiveSimpleLift_suffix_positiveDelta_iff M J _).mp
    rw [← he]
    exact ⟨c, hc⟩
  · rintro ⟨w, hw, rfl⟩
    exact (positiveSimpleLift_suffix_positiveDelta_iff M J w).mpr hw

private theorem longest_unique {K : Type*} [Fintype K] (N : CoxeterMatrix K)
    (q z : N.Group)
    (hq : ∀ w, N.toCoxeterSystem.length w ≤ N.toCoxeterSystem.length q)
    (hz : ∀ w, N.toCoxeterSystem.length w ≤ N.toCoxeterSystem.length z) : q = z := by
  classical
  have h := length_mul_of_all_descents N.toCoxeterSystem q
    (all_descents_of_longest N.toCoxeterSystem q hq) z
  have hqz : q * z = 1 := N.toCoxeterSystem.length_eq_zero_iff.mp (by
    have h1 := hq z
    have h2 := hz q
    omega)
  have hzz := longest_mul_self N.toCoxeterSystem z hz
  calc
    q = q * (z * z) := by rw [hzz, mul_one]
    _ = z := by rw [← mul_assoc, hqz, one_mul]

theorem positiveGenerator_prefix_positiveDelta_of_mem (J : Set I) {j : I} (hj : j ∈ J) :
    PositivePrefix M (positiveGenerator M j) (positiveDelta M J) := by
  classical
  let := fundamental_finite_index M
  let := Fintype.ofFinite I
  have hm : M.toCoxeterSystem.simple j ∈ Artin.coxeterParabolic M J :=
    Subgroup.subset_closure ⟨j, hj, rfl⟩
  have hl := parabolicLongest_left_length M J hm
  have hp : PositivePrefix M (positiveSimpleLift M (M.toCoxeterSystem.simple j))
      (positiveDelta M J) :=
    (positivePrefix_simple_iff M _ _).mpr hl.symm
  simpa only [positiveSimpleLift_simple] using hp

/-- Exactly the selected atoms left-divide the fundamental element. -/
theorem positiveGenerator_prefix_positiveDelta_iff (J : Set I) (j : I) :
    PositivePrefix M (positiveGenerator M j) (positiveDelta M J) ↔ j ∈ J := by
  constructor
  · rintro ⟨c, hc⟩
    have hm : positiveToParent M (positiveGenerator M j * c) ∈ actualPositiveParabolic M J := by
      rw [← hc, positiveToParent_positiveDelta]
      exact parabolicDelta_mem_positiveParabolic M J
    have ha := (positive_factors_mem_actualPositiveParabolic M J _ _ hm).1
    have hs := (positiveToParent_mem_iff_support M J (positiveGenerator M j)).mp ha
    simpa only [positiveSupport_generator, Set.singleton_subset_iff] using hs
  · exact positiveGenerator_prefix_positiveDelta_of_mem M J

theorem generator_leftDivides_parabolicDelta_iff (J : Set I) (j : I) :
    (∃ q ∈ actualPositiveParabolic M Set.univ,
      parabolicDelta M J = Artin.generator M j * q) ↔ j ∈ J := by
  simpa only [positiveToParent_positiveDelta, positiveToParent_generator] using
    (positivePrefix_iff_parentQuotient M (positiveGenerator M j) (positiveDelta M J)).symm.trans
      (positiveGenerator_prefix_positiveDelta_iff M J j)

theorem generator_rightDivides_parabolicDelta_of_mem (J : Set I) {j : I} (hj : j ∈ J) :
    ∃ q ∈ actualPositiveParabolic M Set.univ,
      parabolicDelta M J = q * Artin.generator M j := by
  obtain ⟨i, hperm⟩ := parabolicDelta_generator_permutation M J ⟨j, hj⟩
  obtain ⟨q, hq, he⟩ := (generator_leftDivides_parabolicDelta_iff M J i).mpr i.property
  refine ⟨q, hq, ?_⟩
  have hc : Artin.generator M i * (q * Artin.generator M j) =
      Artin.generator M i * parabolicDelta M J := by
    rw [← mul_assoc, ← he]
    exact hperm
  exact (mul_left_cancel hc).symm

/-- Exactly the selected atoms right-divide the same actual fundamental
element; no positive inverse of a Coxeter lift is substituted. -/
theorem positiveGenerator_suffix_positiveDelta_iff (J : Set I) (j : I) :
    PositiveSuffix M (positiveGenerator M j) (positiveDelta M J) ↔ j ∈ J := by
  constructor
  · rintro ⟨c, hc⟩
    have hm : positiveToParent M (c * positiveGenerator M j) ∈ actualPositiveParabolic M J := by
      rw [← hc, positiveToParent_positiveDelta]
      exact parabolicDelta_mem_positiveParabolic M J
    have ha := (positive_factors_mem_actualPositiveParabolic M J _ _ hm).2
    have hs := (positiveToParent_mem_iff_support M J (positiveGenerator M j)).mp ha
    simpa only [positiveSupport_generator, Set.singleton_subset_iff] using hs
  · intro hj
    apply (positiveSuffix_iff_parentQuotient M _ _).mpr
    simpa only [positiveToParent_positiveDelta, positiveToParent_generator] using
      generator_rightDivides_parabolicDelta_of_mem M J hj

theorem generator_rightDivides_parabolicDelta_iff (J : Set I) (j : I) :
    (∃ q ∈ actualPositiveParabolic M Set.univ,
      parabolicDelta M J = q * Artin.generator M j) ↔ j ∈ J := by
  simpa only [positiveToParent_positiveDelta, positiveToParent_generator] using
    (positiveSuffix_iff_parentQuotient M (positiveGenerator M j) (positiveDelta M J)).symm.trans
      (positiveGenerator_suffix_positiveDelta_iff M J j)

/-- The parabolic fundamental lift is the global positive left-lcm of all
selected atoms, not just an lcm computed inside the selected parabolic. -/
theorem positiveDelta_left_lcm (J : Set I) (p : PositiveArtin M)
    (hp : ∀ j ∈ J, PositivePrefix M (positiveGenerator M j) p) :
    PositivePrefix M (positiveDelta M J) p := by
  classical
  let := fundamental_finite_index M
  let := Fintype.ofFinite I
  obtain ⟨g, hgp, hg⟩ := positive_head M p
  have hdesc : ∀ j ∈ J,
      M.toCoxeterSystem.length (M.toCoxeterSystem.simple j * g) <
        M.toCoxeterSystem.length g := by
    intro j hj
    have hjp : PositivePrefix M (positiveSimpleLift M (M.toCoxeterSystem.simple j)) p := by
      simpa only [positiveSimpleLift_simple] using hp j hj
    have hw := (positivePrefix_simple_iff M _ _).mp (hg _ hjp)
    have hl := (weakPrefix_simple_iff M.toCoxeterSystem j g).mp hw
    omega
  obtain ⟨q, hq, hqg⟩ := positive_longest_descent_prefix M J g hdesc
  have heq : q = parabolicLongestRestricted M J :=
    longest_unique (restrictedMatrix M J) q (parabolicLongestRestricted M J) hq
      (parabolicLongestRestricted_max M J)
  rw [heq] at hqg
  exact positivePrefix_trans M hqg hgp

/-- The same global left-lcm statement, with actual elements and actual
positive quotients in the unchanged parent Artin group. -/
theorem parabolicDelta_left_lcm (J : Set I) (p : Artin.Group M)
    (hp : p ∈ actualPositiveParabolic M Set.univ)
    (h : ∀ j ∈ J, ∃ q ∈ actualPositiveParabolic M Set.univ,
      p = Artin.generator M j * q) :
    ∃ q ∈ actualPositiveParabolic M Set.univ, p = parabolicDelta M J * q := by
  rw [← positiveToParent_mrange_eq_actual] at hp
  obtain ⟨p, rfl⟩ := hp
  have hall : ∀ j ∈ J, PositivePrefix M (positiveGenerator M j) p := by
    intro j hj
    apply (positivePrefix_iff_parentQuotient M _ _).mpr
    simpa only [positiveToParent_generator] using h j hj
  simpa only [positiveToParent_positiveDelta] using
    (positivePrefix_iff_parentQuotient M _ _).mp (positiveDelta_left_lcm M J p hall)

theorem positiveDelta_prefix_of_subset (J K : Set I) (hJK : J ⊆ K) :
    PositivePrefix M (positiveDelta M J) (positiveDelta M K) :=
  positiveDelta_left_lcm M J _ (fun _ hj => positiveGenerator_prefix_positiveDelta_of_mem M K (hJK hj))

/-- The quotient can itself be chosen in the larger actual positive parabolic. -/
theorem parabolicDelta_prefix_of_subset (J K : Set I) (hJK : J ⊆ K) :
    ∃ q ∈ actualPositiveParabolic M K, parabolicDelta M K = parabolicDelta M J * q := by
  refine ⟨(parabolicDelta M J)⁻¹ * parabolicDelta M K,
    parabolicDelta_ratio_positive M J K hJK, ?_⟩
  group

theorem positiveDelta_insert_is_left_lcm (J : Set I) (a : I) :
    PositivePrefix M (positiveDelta M J) (positiveDelta M (insert a J)) ∧
    PositivePrefix M (positiveGenerator M a) (positiveDelta M (insert a J)) ∧
    ∀ p : PositiveArtin M, PositivePrefix M (positiveDelta M J) p →
      PositivePrefix M (positiveGenerator M a) p →
      PositivePrefix M (positiveDelta M (insert a J)) p := by
  refine ⟨positiveDelta_prefix_of_subset M J _ (Set.subset_insert a J),
    positiveGenerator_prefix_positiveDelta_of_mem M _ (Set.mem_insert a J), ?_⟩
  intro p hJ ha
  apply positiveDelta_left_lcm M _ p
  intro j hj
  rcases Set.mem_insert_iff.mp hj with rfl | hj
  · exact ha
  · exact positivePrefix_trans M (positiveGenerator_prefix_positiveDelta_of_mem M J hj) hJ

theorem parabolicDelta_insert_left_lcm (J : Set I) (a : I) (p : Artin.Group M)
    (hp : p ∈ actualPositiveParabolic M Set.univ)
    (hJ : ∃ q ∈ actualPositiveParabolic M Set.univ, p = parabolicDelta M J * q)
    (ha : ∃ q ∈ actualPositiveParabolic M Set.univ, p = Artin.generator M a * q) :
    ∃ q ∈ actualPositiveParabolic M Set.univ, p = parabolicDelta M (insert a J) * q := by
  apply parabolicDelta_left_lcm M _ p hp
  intro j hj
  rcases Set.mem_insert_iff.mp hj with rfl | hj
  · exact ha
  · obtain ⟨q, hq, hprod⟩ := hJ
    obtain ⟨r, hr, hd⟩ := (generator_leftDivides_parabolicDelta_iff M J j).mpr hj
    exact ⟨r * q, (actualPositiveParabolic M Set.univ).mul_mem hr hq,
      by rw [hprod, hd, mul_assoc]⟩

end ArtinNormalisers.Ribbon2
