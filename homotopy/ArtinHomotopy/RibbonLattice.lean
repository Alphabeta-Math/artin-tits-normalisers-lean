import ArtinHomotopy.FacePrefixes
import ArtinRibbons.CofinalRibbons

/-!
# Actual left-lcms of arbitrary positive reduced ribbons

The ambient positive Artin lcm is closed under the ribbon condition: selected
source atoms transport across each prefix, hence across their lcm. The positive
quotients have exponent degree one and are actual atoms. The accepted
generator-conjugation theorem then supplies the actual target parabolic.

A concrete cofinal-loop power supplies a common positive reduced upper bound,
so the ambient lcm and its two tails are positive reduced generated ribbons.
All values remain in the existing Artin presentation. No lattice or ribbon
closure axiom is introduced. Inputs are the accepted M2 positive embedding,
ambient lcm, generator transport, cofinality and positive generation theorems.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Homotopy5

open Ribbon2 OAI.HarmonicArtin

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group]

/-- The actual ambient positive lcm, expressed using genuine group labels and
positive quotients rather than changing the underlying monoid. -/
theorem ambient_positive_left_lcm {p q : Artin.Group M}
    (hp : p ∈ actualPositiveParabolic M Set.univ)
    (hq : q ∈ actualPositiveParabolic M Set.univ) :
    ∃ l : Artin.Group M, l ∈ actualPositiveParabolic M Set.univ ∧
      RibbonPrefix M p l ∧ RibbonPrefix M q l ∧
      ∀ r, r ∈ actualPositiveParabolic M Set.univ →
        RibbonPrefix M p r → RibbonPrefix M q r → RibbonPrefix M l r := by
  obtain ⟨l, hpl, hql, hleast⟩ := actualPositive_lcm_left M ⟨p, hp⟩ ⟨q, hq⟩
  have unpack {a b : actualPositiveParabolic M Set.univ}
      (h : ActualLeftDivides M a b) : RibbonPrefix M a.val b.val := by
    obtain ⟨c, hc⟩ := h
    exact ⟨c.val, c.property, congrArg Subtype.val hc⟩
  refine ⟨l.val, l.property, unpack hpl, unpack hql, ?_⟩
  intro r hr hpr hqr
  apply unpack (hleast ⟨r, hr⟩ ?_ ?_)
  · obtain ⟨a, ha, hea⟩ := hpr
    exact ⟨⟨a, ha⟩, Subtype.ext hea⟩
  · obtain ⟨b, hb, heb⟩ := hqr
    exact ⟨⟨b, hb⟩, Subtype.ext heb⟩

omit [Finite M.Group] in
private theorem positive_degree_one_generator {a : Artin.Group M}
    (ha : a ∈ actualPositiveParabolic M Set.univ) (hdeg : degree M a = 1) :
    ∃ k : I, a = Artin.generator M k := by
  rw [← positiveToParent_mrange_eq_actual M] at ha
  obtain ⟨b, rfl⟩ := ha
  obtain ⟨w, rfl⟩ := Ribbon2.positive_word_surjective M b
  have hw : w.length = 1 := by
    rw [positiveToParent_word, degree_wordProd] at hdeg
    omega
  obtain ⟨k, rfl⟩ := List.length_eq_one_iff.mp hw
  exact ⟨k, rfl⟩

/-- An atom transported across a ribbon also transports across any positive
extension of that ribbon. -/
theorem ribbonPrefix_generator_mul {X Y : RibbonObject M} {p l : Artin.Group M}
    (hp : IsRibbon M X Y p) (hpl : RibbonPrefix M p l) {i : I} (hi : i ∈ X.indices) :
    RibbonPrefix M p (Artin.generator M i * l) := by
  obtain ⟨a, ha, hla⟩ := hpl
  obtain ⟨j, _, hrel⟩ := hp.generator_forward M hi
  refine ⟨Artin.generator M j * a, Submonoid.mul_mem _
    (generator_mem_actualPositiveParabolic M Set.univ (Set.mem_univ j)) ha, ?_⟩
  rw [hla, ← mul_assoc, hrel, mul_assoc]

/-- The endpoint is literally the set of atoms conjugated from the source. -/
def ribbonLcmTargetIndices (X : RibbonObject M) (l : Artin.Group M) : Set I :=
  {k | ∃ i ∈ X.indices, Artin.generator M i * l = l * Artin.generator M k}

/-- Any ambient positive lcm of two actual same-source ribbons is itself an
actual ribbon, with the explicit atom-transport endpoint. -/
theorem isRibbon_of_ambient_positive_left_lcm {X Y Z : RibbonObject M}
    {p q l : Artin.Group M} (hp : IsRibbon M X Y p) (hq : IsRibbon M X Z q)
    (hl : l ∈ actualPositiveParabolic M Set.univ)
    (hpl : RibbonPrefix M p l) (hql : RibbonPrefix M q l)
    (hleast : ∀ r, r ∈ actualPositiveParabolic M Set.univ →
      RibbonPrefix M p r → RibbonPrefix M q r → RibbonPrefix M l r) :
    IsRibbon M X ⟨ribbonLcmTargetIndices M X l⟩ l := by
  classical
  have hforward (i : X.indices) :
      ∃ k : I, l⁻¹ * Artin.generator M i * l = Artin.generator M k := by
    have hpos : Artin.generator M i * l ∈ actualPositiveParabolic M Set.univ :=
      Submonoid.mul_mem _ (generator_mem_actualPositiveParabolic M Set.univ (Set.mem_univ i)) hl
    obtain ⟨a, ha, hea⟩ := hleast _ hpos
      (ribbonPrefix_generator_mul M hp hpl i.property)
      (ribbonPrefix_generator_mul M hq hql i.property)
    have hd := congrArg (degree M) hea
    simp only [degree_mul, degree_generator] at hd
    obtain ⟨k, hak⟩ := positive_degree_one_generator M ha (by omega)
    refine ⟨k, ?_⟩
    calc
      l⁻¹ * Artin.generator M i * l = l⁻¹ * (Artin.generator M i * l) := by group
      _ = l⁻¹ * (l * a) := by rw [hea]
      _ = Artin.generator M k := by rw [inv_mul_cancel_left, hak]
  choose f hf using hforward
  have hrib := isRibbon_of_generator_conjugates M X.indices f l hf
  have htarget : Set.range f = ribbonLcmTargetIndices M X l := by
    ext k
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨i.val, i.property, ?_⟩
      calc
        Artin.generator M i * l = l * (l⁻¹ * Artin.generator M i * l) := by group
        _ = l * Artin.generator M (f i) := by rw [hf i]
    · rintro ⟨i, hi, hrel⟩
      have he : Artin.generator M k = Artin.generator M (f ⟨i, hi⟩) := by
        calc
          Artin.generator M k = l⁻¹ * (Artin.generator M i * l) := by rw [hrel]; group
          _ = Artin.generator M (f ⟨i, hi⟩) := by simpa only [mul_assoc] using hf ⟨i, hi⟩
      have hik : k = f ⟨i, hi⟩ := M.toCoxeterSystem.simple_injective
        (by simpa only [CoxeterMatrix.toCoxeterSystem_simple, Artin.projection_generator]
          using congrArg (Artin.projection M) he)
      exact ⟨⟨i, hi⟩, hik.symm⟩
  simpa only [htarget] using hrib

omit [Finite M.Group] in
/-- Positive prefixes inherit source left reduction from an actual upper bound. -/
theorem ribbonPrefix_leftReduced {X : RibbonObject M} {l r : Artin.Group M}
    (hr : IsLeftParabolicallyReduced M X.indices r) (hlr : RibbonPrefix M l r) :
    IsLeftParabolicallyReduced M X.indices l := by
  obtain ⟨b, hb, hrb⟩ := hlr
  intro i hi a ha hea
  apply hr i hi (a * b) (Submonoid.mul_mem _ ha hb)
  rw [← mul_assoc, hea]
  exact hrb.symm

/-- Removing any positive generated ribbon prefix leaves a positive generated
ribbon at its actual intermediate endpoint. -/
theorem positive_ribbon_prefix_tail {X Y Z : RibbonObject M} {p r : Artin.Group M}
    (hp : PositiveReducedArrow M X Y p) (hr : PositiveReducedArrow M X Z r)
    (hpr : RibbonPrefix M p r) :
    ∃ a : Artin.Group M, PositiveReducedArrow M Y Z a ∧ r = p * a := by
  obtain ⟨a, ha, hra⟩ := hpr
  have harib : IsRibbon M Y Z a := by
    have h := (hp.isRibbon.inv M).mul M hr.isRibbon
    have he : p⁻¹ * r = a := by rw [hra]; group
    simpa only [he] using h
  have hared : IsLeftParabolicallyReduced M Y.indices a := by
    intro j hj b hb he
    obtain ⟨i, hi, hrel⟩ := hp.isRibbon.generator_reverse M hj
    apply (hr.leftReduced M) i hi (p * b) (Submonoid.mul_mem _ hp.positive hb)
    rw [← mul_assoc, hrel, mul_assoc, he]
    exact hra.symm
  exact ⟨a, positive_leftReduced_ribbon_generated M ha hared harib, hra⟩

/-- A specific power of the actual cofinal loop is a common positive reduced
upper bound for any two positive generated ribbons with the same source. -/
theorem positive_reduced_ribbon_common_upper_bound {X Y Z : RibbonObject M}
    {p q : Artin.Group M} (hp : PositiveReducedArrow M X Y p)
    (hq : PositiveReducedArrow M X Z q) :
    ∃ r : Artin.Group M, PositiveReducedArrow M X X r ∧
      RibbonPrefix M p r ∧ RibbonPrefix M q r := by
  obtain ⟨n, a, ha, hpa⟩ := hp.positive_complement M
  obtain ⟨m, b, hb, hqb⟩ := hq.positive_complement M
  refine ⟨cofinalLoop M X.indices ^ (n + m), positive_cofinalLoop_pow M X (n + m), ?_, ?_⟩
  · refine ⟨a * cofinalLoop M X.indices ^ m,
      (PositiveReducedArrow.comp ha (positive_cofinalLoop_pow M X m)).positive, ?_⟩
    rw [← mul_assoc, hpa, ← pow_add]
  · refine ⟨b * cofinalLoop M X.indices ^ n,
      (PositiveReducedArrow.comp hb (positive_cofinalLoop_pow M X n)).positive, ?_⟩
    rw [← mul_assoc, hqb, ← pow_add, Nat.add_comm]

/-- Arbitrary same-source positive reduced ribbons have an actual left-lcm,
with actual positive generated tails and the ambient positive universal property.
No lattice structure or closure conclusion is supplied as a hypothesis. -/
theorem positive_reduced_ribbon_lcm_left {X Y Z : RibbonObject M} {p q : Artin.Group M}
    (hp : PositiveReducedArrow M X Y p) (hq : PositiveReducedArrow M X Z q) :
    ∃ (U : RibbonObject M) (l : Artin.Group M),
      PositiveReducedArrow M X U l ∧
      (∃ a : Artin.Group M, PositiveReducedArrow M Y U a ∧ l = p * a) ∧
      (∃ b : Artin.Group M, PositiveReducedArrow M Z U b ∧ l = q * b) ∧
      ∀ r, r ∈ actualPositiveParabolic M Set.univ →
        RibbonPrefix M p r → RibbonPrefix M q r → RibbonPrefix M l r := by
  obtain ⟨l, hlpos, hpl, hql, hleast⟩ := ambient_positive_left_lcm M hp.positive hq.positive
  let U : RibbonObject M := ⟨ribbonLcmTargetIndices M X l⟩
  have hlrib : IsRibbon M X U l :=
    isRibbon_of_ambient_positive_left_lcm M hp.isRibbon hq.isRibbon hlpos hpl hql hleast
  obtain ⟨r, hr, hpr, hqr⟩ := positive_reduced_ribbon_common_upper_bound M hp hq
  have hlred : IsLeftParabolicallyReduced M X.indices l :=
    ribbonPrefix_leftReduced M (hr.leftReduced M) (hleast r hr.positive hpr hqr)
  have hlgen := positive_leftReduced_ribbon_generated M hlpos hlred hlrib
  exact ⟨U, l, hlgen, positive_ribbon_prefix_tail M hp hlgen hpl,
    positive_ribbon_prefix_tail M hq hlgen hql, hleast⟩

/-- The least ambient prefix also factors every common positive ribbon upper
bound through a positive generated tail at the genuine lcm endpoint. -/
theorem positive_reduced_ribbon_lcm_left_with_tails {X Y Z : RibbonObject M}
    {p q : Artin.Group M} (hp : PositiveReducedArrow M X Y p)
    (hq : PositiveReducedArrow M X Z q) :
    ∃ (U : RibbonObject M) (l : Artin.Group M),
      PositiveReducedArrow M X U l ∧
      (∃ a : Artin.Group M, PositiveReducedArrow M Y U a ∧ l = p * a) ∧
      (∃ b : Artin.Group M, PositiveReducedArrow M Z U b ∧ l = q * b) ∧
      ∀ (V : RibbonObject M) (r : Artin.Group M), PositiveReducedArrow M X V r →
        RibbonPrefix M p r → RibbonPrefix M q r →
        ∃ t : Artin.Group M, PositiveReducedArrow M U V t ∧ r = l * t := by
  obtain ⟨U, l, hl, hp', hq', hleast⟩ := positive_reduced_ribbon_lcm_left M hp hq
  refine ⟨U, l, hl, hp', hq', ?_⟩
  intro V r hr hpr hqr
  exact positive_ribbon_prefix_tail M hl hr (hleast r hr.positive hpr hqr)

end ArtinNormalisers.Homotopy5
