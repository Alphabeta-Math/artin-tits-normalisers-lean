import ArtinRibbons.RibbonGroupoid
import ArtinRibbons.ParabolicReduction
import ArtinRibbons.PositiveSupport
import ArtinRibbons.SphericalPositive
import ArtinRibbons.DeltaDivisibility

/-!
# Positive calculus for actual ribbons

The positive-parabolic conjugation condition forces generator permutations.
Gcd/lcm calculus then controls divisors of reduced positive ribbons and
proves that their products remain reduced. All group elements and positive
divisibility witnesses use the actual Artin presentation.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Ribbon2

open OAI.HarmonicArtin

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group]

private theorem positive_degree_one_selected (J : Set I) {a : Artin.Group M}
    (ha : a ∈ actualPositiveParabolic M J) (hdeg : degree M a = 1) :
    ∃ j ∈ J, a = Artin.generator M j := by
  have hfull : a ∈ actualPositiveParabolic M Set.univ := by
    apply Submonoid.closure_mono (s := Artin.generator M '' J) ?_ ha
    exact Set.image_mono (Set.subset_univ J)
  rw [← positiveToParent_mrange_eq_actual M] at hfull
  obtain ⟨b, rfl⟩ := hfull
  obtain ⟨w, rfl⟩ := positive_word_surjective M b
  have hw : w.length = 1 := by
    rw [positiveToParent_word, degree_wordProd] at hdeg
    omega
  obtain ⟨j, rfl⟩ := List.length_eq_one_iff.1 hw
  refine ⟨j, ?_, rfl⟩
  exact (positiveToParent_mem_iff_support M J (positiveGenerator M j)).1 ha (by simp)

/-- Every source generator has an actual target-generator transport relation. -/
theorem IsRibbon.generator_forward {X Y : RibbonObject M} {r : Artin.Group M}
    (h : IsRibbon M X Y r) {i : I} (hi : i ∈ X.indices) :
    ∃ j ∈ Y.indices, Artin.generator M i * r = r * Artin.generator M j := by
  have hmem := (h (Artin.generator M i)).1
    (generator_mem_actualPositiveParabolic M X.indices hi)
  have hdeg : degree M (r⁻¹ * Artin.generator M i * r) = 1 := by
    rw [degree_mul, degree_mul, degree_inv, degree_generator]
    omega
  obtain ⟨j, hj, heq⟩ := positive_degree_one_selected M Y.indices hmem hdeg
  refine ⟨j, hj, ?_⟩
  calc
    Artin.generator M i * r = r * (r⁻¹ * Artin.generator M i * r) := by group
    _ = r * Artin.generator M j := by rw [heq]

/-- The reverse direction follows from the inverse ribbon, with the same
source and target convention as right-composed ribbon paths. -/
theorem IsRibbon.generator_reverse {X Y : RibbonObject M} {r : Artin.Group M}
    (h : IsRibbon M X Y r) {j : I} (hj : j ∈ Y.indices) :
    ∃ i ∈ X.indices, Artin.generator M i * r = r * Artin.generator M j := by
  obtain ⟨i, hi, heq⟩ := IsRibbon.generator_forward M (h.inv M) hj
  refine ⟨i, hi, ?_⟩
  have h' := congrArg (fun a => r * a * r) heq
  simpa [mul_assoc] using h'.symm

omit [Finite M.Group] in
private theorem positive_mem_univ (J : Set I) {a : Artin.Group M}
    (ha : a ∈ actualPositiveParabolic M J) : a ∈ actualPositiveParabolic M Set.univ :=
  Submonoid.closure_mono (Set.image_mono (Set.subset_univ J)) ha

/-- Support saturation for actual positive factors, transported through the
proved faithful positive presentation. -/
theorem actual_positive_factors_mem (J : Set I) {a b : Artin.Group M}
    (ha : a ∈ actualPositiveParabolic M Set.univ)
    (hb : b ∈ actualPositiveParabolic M Set.univ)
    (hab : a * b ∈ actualPositiveParabolic M J) :
    a ∈ actualPositiveParabolic M J ∧ b ∈ actualPositiveParabolic M J := by
  rw [← positiveToParent_mrange_eq_actual M] at ha hb
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  apply positive_factors_mem_actualPositiveParabolic M J a b
  simpa only [map_mul] using hab

private theorem delta_leftDivides_conjugate {X Y : RibbonObject M} {r : Artin.Group M}
    (h : IsRibbon M X Y r) :
    ∃ q ∈ actualPositiveParabolic M Set.univ,
      r⁻¹ * parabolicDelta M X.indices * r = parabolicDelta M Y.indices * q := by
  have hp := (h (parabolicDelta M X.indices)).1
    (parabolicDelta_mem_positiveParabolic M X.indices)
  apply parabolicDelta_left_lcm M Y.indices _ (positive_mem_univ M Y.indices hp)
  intro j hj
  obtain ⟨i, hi, hrel⟩ := IsRibbon.generator_reverse M h hj
  obtain ⟨q, hq, hdelta⟩ := (generator_leftDivides_parabolicDelta_iff M X.indices i).2 hi
  have hqi : q ∈ actualPositiveParabolic M X.indices :=
    (actual_positive_factors_mem M X.indices
      (positive_mem_univ M X.indices (generator_mem_actualPositiveParabolic M X.indices hi))
      hq (hdelta ▸ parabolicDelta_mem_positiveParabolic M X.indices)).2
  refine ⟨r⁻¹ * q * r, positive_mem_univ M Y.indices ((h q).1 hqi), ?_⟩
  have hgen : r⁻¹ * Artin.generator M i * r = Artin.generator M j := by
    rw [mul_assoc, hrel]
    simp
  calc
    r⁻¹ * parabolicDelta M X.indices * r =
        (r⁻¹ * Artin.generator M i * r) * (r⁻¹ * q * r) := by rw [hdelta]; group
    _ = Artin.generator M j * (r⁻¹ * q * r) := by rw [hgen]

/-- Every actual ribbon transports the fundamental element of its source
to that of its target. The proof compares internal positive lcm divisibility
in both directions, without assuming equal longest-root counts. -/
theorem IsRibbon.parabolicDelta_conjugate {X Y : RibbonObject M} {r : Artin.Group M}
    (h : IsRibbon M X Y r) :
    r⁻¹ * parabolicDelta M X.indices * r = parabolicDelta M Y.indices := by
  obtain ⟨a, ha, hforward⟩ := delta_leftDivides_conjugate M h
  obtain ⟨b, hb, hbackward⟩ := delta_leftDivides_conjugate M (h.inv M)
  have hda := congrArg (degree M) hforward
  have hdb := congrArg (degree M) hbackward
  simp only [degree_mul, degree_inv] at hda hdb
  have ha0 : degree M a = 0 := by
    have ha' := degree_nonneg_of_mem_actualPositiveParabolic M Set.univ ha
    have hb' := degree_nonneg_of_mem_actualPositiveParabolic M Set.univ hb
    omega
  have ha1 := (degree_eq_zero_iff_of_mem_actualPositiveParabolic M Set.univ ha).1 ha0
  simpa only [ha1, mul_one] using hforward

theorem IsRibbon.parabolicDelta_mul {X Y : RibbonObject M} {r : Artin.Group M}
    (h : IsRibbon M X Y r) :
    parabolicDelta M X.indices * r = r * parabolicDelta M Y.indices := by
  rw [← IsRibbon.parabolicDelta_conjugate M h]
  group

/-- The lcm of an atom and a positive reduced transporter is obtained by
transporting that atom across the ribbon. The statement gives its universal
property directly in the positive presentation. -/
theorem positive_atom_ribbon_lcm (J : Set I) (r : PositiveArtin M) (i j : I)
    (hi : i ∈ J) (hred : IsLeftParabolicallyReduced M J (positiveToParent M r))
    (hrel : positiveGenerator M i * r = r * positiveGenerator M j)
    (a : PositiveArtin M) (hia : PositivePrefix M (positiveGenerator M i) a)
    (hra : PositivePrefix M r a) : PositivePrefix M (r * positiveGenerator M j) a := by
  obtain ⟨l, hil, hrl, hl⟩ := positive_lcm_left M (positiveGenerator M i) r
  have hlbound := hl (r * positiveGenerator M j) ⟨r, hrel.symm⟩ ⟨positiveGenerator M j, rfl⟩
  obtain ⟨v, hv⟩ := hrl
  have hvj : PositivePrefix M v (positiveGenerator M j) :=
    (positivePrefix_mul_left_iff M (positive_cancel_left M) r v (positiveGenerator M j)).1
      (hv ▸ hlbound)
  have hvne : v ≠ 1 := by
    intro hv1
    have hlr : l = r := by rw [hv, hv1, mul_one]
    obtain ⟨c, hc⟩ := hil
    apply hred i hi (positiveToParent M c) (positiveActualHom M c).property
    have h := congrArg (positiveToParent M) (hlr.symm.trans hc)
    simpa only [map_mul, positiveToParent_generator] using h.symm
  have hdeg := positivePrefix_degree M hvj
  rw [positiveDegree_generator] at hdeg
  have hvdeg : positiveDegree M v = 1 := by
    have hn : positiveDegree M v ≠ 0 := mt (positiveDegree_zero_iff M v).1 hvne
    omega
  have hveq : v = positiveGenerator M j :=
    positivePrefix_eq_of_degree M hvj (by rw [hvdeg, positiveDegree_generator])
  have hleq : l = r * positiveGenerator M j := by rw [hv, hveq]
  simpa only [hleq] using hl a hia hra

/-- Multiplication of positive left-reduced ribbons preserves left reduction.
Only the first factor's transporter relation is needed for this divisor step. -/
theorem positive_ribbon_mul_leftReduced {X Y : RibbonObject M} {r s : Artin.Group M}
    (hr : r ∈ actualPositiveParabolic M Set.univ)
    (hred : IsLeftParabolicallyReduced M X.indices r)
    (hribbon : IsRibbon M X Y r)
    (hs : s ∈ actualPositiveParabolic M Set.univ)
    (hsred : IsLeftParabolicallyReduced M Y.indices s) :
    IsLeftParabolicallyReduced M X.indices (r * s) := by
  rw [← positiveToParent_mrange_eq_actual M] at hr hs
  obtain ⟨p, rfl⟩ := hr
  obtain ⟨q, rfl⟩ := hs
  intro i hi t ht heq
  rw [← positiveToParent_mrange_eq_actual M] at ht
  obtain ⟨u, rfl⟩ := ht
  obtain ⟨j, hj, hrel⟩ := IsRibbon.generator_forward M hribbon hi
  have hrelP : positiveGenerator M i * p = p * positiveGenerator M j := by
    apply positiveToParent_injective M
    simpa only [map_mul, positiveToParent_generator] using hrel
  have hprefix : PositivePrefix M (positiveGenerator M i) (p * q) := by
    refine ⟨u, positiveToParent_injective M ?_⟩
    simpa only [map_mul, positiveToParent_generator] using heq.symm
  have hlcm := positive_atom_ribbon_lcm M X.indices p i j hi hred hrelP (p * q)
    hprefix ⟨q, rfl⟩
  have hjq := (positivePrefix_mul_left_iff M (positive_cancel_left M)
    p (positiveGenerator M j) q).1 hlcm
  obtain ⟨v, hv⟩ := hjq
  apply hsred j hj (positiveToParent M v) (positiveActualHom M v).property
  have h := congrArg (positiveToParent M) hv
  simpa only [map_mul, positiveToParent_generator] using h.symm

end ArtinNormalisers.Ribbon2
