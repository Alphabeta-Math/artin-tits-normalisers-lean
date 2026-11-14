import ArtinHomotopy.RibbonLattice

/-!
# Greatest common prefixes and greatest simple prefixes of actual ribbons

Common generated positive prefixes have bounded nonnegative exponent degree.
Choose one of greatest degree. The proved lcm of it with any other candidate
is again a common prefix; maximal degree forces the positive lcm quotient to
be one. This proves greatestness without finite divisor enumeration or an
assumption that an ambient gcd satisfies the ribbon condition.

Simple ribbons are actual generated arrows dividing the actual cofinal
half-turn. Their greatest-prefix theorem is the preceding gcd construction
specialized to that half-turn. No topological or asphericity claim is made.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Homotopy5

open Ribbon2

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group]

omit [Finite M.Group] in
/-- Positive left divisibility increases the actual exponent degree. -/
theorem ribbonPrefix_degree_le {a b : Artin.Group M} (hab : RibbonPrefix M a b) :
    degree M a ≤ degree M b := by
  obtain ⟨c, hc, rfl⟩ := hab
  rw [degree_mul]
  exact le_add_of_nonneg_right (degree_nonneg_of_mem_actualPositiveParabolic M Set.univ hc)

omit [Finite M.Group] in
/-- A positive quotient with no degree increase is one. -/
theorem ribbonPrefix_eq_of_degree_le {a b : Artin.Group M} (hab : RibbonPrefix M a b)
    (hdeg : degree M b ≤ degree M a) : a = b := by
  obtain ⟨c, hc, hbc⟩ := hab
  have hnonneg := degree_nonneg_of_mem_actualPositiveParabolic M Set.univ hc
  have hsum := congrArg (degree M) hbc
  rw [degree_mul] at hsum
  have hc0 : degree M c = 0 := by omega
  have hc1 := (degree_eq_zero_iff_of_mem_actualPositiveParabolic M Set.univ hc).mp hc0
  simpa only [hc1, mul_one] using hbc.symm

omit [Finite M.Group] in
theorem ribbonPrefix_antisymm {a b : Artin.Group M}
    (hab : RibbonPrefix M a b) (hba : RibbonPrefix M b a) : a = b :=
  ribbonPrefix_eq_of_degree_le M hab (ribbonPrefix_degree_le M hba)

/-- Greatest common actual generated positive prefix, retaining its genuine
intermediate endpoint. Only finite Coxeter type is assumed. -/
theorem positive_reduced_ribbon_gcd_left {X Y Z : RibbonObject M} {p q : Artin.Group M}
    (hp : PositiveReducedArrow M X Y p) (hq : PositiveReducedArrow M X Z q) :
    ∃ (U : RibbonObject M) (d : Artin.Group M),
      PositiveReducedArrow M X U d ∧ RibbonPrefix M d p ∧ RibbonPrefix M d q ∧
      ∀ (V : RibbonObject M) (e : Artin.Group M), PositiveReducedArrow M X V e →
        RibbonPrefix M e p → RibbonPrefix M e q → RibbonPrefix M e d := by
  classical
  let P : ℕ → Prop := fun n => ∃ (U : RibbonObject M) (d : Artin.Group M),
    PositiveReducedArrow M X U d ∧ RibbonPrefix M d p ∧ RibbonPrefix M d q ∧
      (degree M d).toNat = n
  have hzero : P 0 :=
    ⟨X, 1, .identity X, ⟨p, hp.positive, (one_mul p).symm⟩,
      ⟨q, hq.positive, (one_mul q).symm⟩, by rw [degree_one]; rfl⟩
  have hmax : P (Nat.findGreatest P (degree M p).toNat) :=
    Nat.findGreatest_spec (Nat.zero_le _) hzero
  obtain ⟨U, d, hd, hdp, hdq, hdegree⟩ := hmax
  refine ⟨U, d, hd, hdp, hdq, ?_⟩
  intro V e he hep heq
  obtain ⟨W, l, hl, ⟨a, ha, hla⟩, ⟨b, hb, hlb⟩, hleast⟩ :=
    positive_reduced_ribbon_lcm_left M hd he
  have hdl : RibbonPrefix M d l := ⟨a, ha.positive, hla⟩
  have hel : RibbonPrefix M e l := ⟨b, hb.positive, hlb⟩
  have hlp := hleast p hp.positive hdp hep
  have hlq := hleast q hq.positive hdq heq
  have hbound : (degree M l).toNat ≤ (degree M p).toNat := by
    have := ribbonPrefix_degree_le M hlp
    omega
  have hmaxl : (degree M l).toNat ≤ Nat.findGreatest P (degree M p).toNat :=
    Nat.le_findGreatest hbound ⟨W, l, hl, hlp, hlq, rfl⟩
  have hldeg : degree M l ≤ degree M d := by
    have := degree_nonneg_of_mem_actualPositiveParabolic M Set.univ hl.positive
    have := degree_nonneg_of_mem_actualPositiveParabolic M Set.univ hd.positive
    omega
  have hld : l = d := (ribbonPrefix_eq_of_degree_le M hdl hldeg).symm
  simpa only [hld] using hel

/-- The greatest common prefix has actual generated positive tails to both
original targets, and every other common prefix has a generated tail to it. -/
theorem positive_reduced_ribbon_gcd_left_with_tails {X Y Z : RibbonObject M}
    {p q : Artin.Group M} (hp : PositiveReducedArrow M X Y p)
    (hq : PositiveReducedArrow M X Z q) :
    ∃ (U : RibbonObject M) (d : Artin.Group M), PositiveReducedArrow M X U d ∧
      (∃ a : Artin.Group M, PositiveReducedArrow M U Y a ∧ p = d * a) ∧
      (∃ b : Artin.Group M, PositiveReducedArrow M U Z b ∧ q = d * b) ∧
      ∀ (V : RibbonObject M) (e : Artin.Group M), PositiveReducedArrow M X V e →
        RibbonPrefix M e p → RibbonPrefix M e q →
        ∃ t : Artin.Group M, PositiveReducedArrow M V U t ∧ d = e * t := by
  obtain ⟨U, d, hd, hdp, hdq, hgreatest⟩ := positive_reduced_ribbon_gcd_left M hp hq
  refine ⟨U, d, hd, positive_ribbon_prefix_tail M hd hp hdp,
    positive_ribbon_prefix_tail M hd hq hdq, ?_⟩
  intro V e he hep heq
  exact positive_ribbon_prefix_tail M he hd (hgreatest V e he hep heq)

/-- A simple ribbon is an actual positive generated arrow which positively
divides the actual source half-turn. This definition contains no maximality. -/
def SimpleRibbon (X Y : RibbonObject M) (s : Artin.Group M) : Prop :=
  PositiveReducedArrow M X Y s ∧ RibbonPrefix M s (cofinalDelta M X.indices)

/-- Greatest arbitrary simple ribbon prefix, rather than only a face prefix. -/
theorem greatest_simple_ribbon_prefix {X Y : RibbonObject M} {p : Artin.Group M}
    (hp : PositiveReducedArrow M X Y p) :
    ∃ (U : RibbonObject M) (d : Artin.Group M), SimpleRibbon M X U d ∧ RibbonPrefix M d p ∧
      ∀ (V : RibbonObject M) (e : Artin.Group M), SimpleRibbon M X V e →
        RibbonPrefix M e p → RibbonPrefix M e d := by
  have hδ : PositiveReducedArrow M X ⟨cofinalTarget M X.indices⟩
      (cofinalDelta M X.indices) := positive_cofinalDelta M X.indices
  obtain ⟨U, d, hd, hdp, hdδ, hgreatest⟩ := positive_reduced_ribbon_gcd_left M hp hδ
  exact ⟨U, d, ⟨hd, hdδ⟩, hdp, fun V e he hep => hgreatest V e he.1 hep he.2⟩

/-- A nonidentity positive generated ribbon has a nonidentity simple prefix.
Every outside atomic descent divides both it and the actual half-turn. -/
theorem greatest_simple_ribbon_prefix_ne_one {X Y : RibbonObject M} {p d : Artin.Group M}
    (hp : PositiveReducedArrow M X Y p) (hpne : p ≠ 1)
    (hgreatest : ∀ (V : RibbonObject M) (e : Artin.Group M), SimpleRibbon M X V e →
      RibbonPrefix M e p → RibbonPrefix M e d) : d ≠ 1 := by
  obtain ⟨a, haX, hap⟩ := outsideAtomDescents_nonempty M hp hpne
  have hμ : PositiveReducedArrow M X (atomicNext M X a) (elementaryMu M X.indices a) :=
    .elementary a haX (elementaryMu_isRibbon M X.indices a)
  have hμδ : RibbonPrefix M (elementaryMu M X.indices a) (cofinalDelta M X.indices) :=
    parabolicDelta_ratio_elementary_prefix M X.indices Set.univ (Set.subset_univ _) a
      (Set.mem_univ a)
  have hprefix := hgreatest _ _ ⟨hμ, hμδ⟩ hap
  have hdegree := ribbonPrefix_degree_le M hprefix
  have hpositive := elementaryMu_degree_pos M X.indices a haX
  intro hd1
  rw [hd1, degree_one] at hdegree
  omega

/-- The greatest simple head leaves an actual generated tail. For a
nonidentity input that head is nontrivial and the tail has smaller degree. -/
theorem greatest_simple_ribbon_prefix_with_tail {X Y : RibbonObject M} {p : Artin.Group M}
    (hp : PositiveReducedArrow M X Y p) :
    ∃ (U : RibbonObject M) (d a : Artin.Group M), SimpleRibbon M X U d ∧
      PositiveReducedArrow M U Y a ∧ p = d * a ∧
      (∀ (V : RibbonObject M) (e : Artin.Group M), SimpleRibbon M X V e →
        RibbonPrefix M e p → RibbonPrefix M e d) ∧
      (p ≠ 1 → d ≠ 1 ∧ degree M a < degree M p) := by
  obtain ⟨U, d, hd, hdp, hgreatest⟩ := greatest_simple_ribbon_prefix M hp
  obtain ⟨a, ha, hpa⟩ := positive_ribbon_prefix_tail M hd.1 hp hdp
  refine ⟨U, d, a, hd, ha, hpa, hgreatest, ?_⟩
  intro hpne
  have hdne := greatest_simple_ribbon_prefix_ne_one M hp hpne hgreatest
  have hdnonneg := degree_nonneg_of_mem_actualPositiveParabolic M Set.univ hd.1.positive
  have hddeg : degree M d ≠ 0 := by
    intro hz
    exact hdne ((degree_eq_zero_iff_of_mem_actualPositiveParabolic M Set.univ hd.1.positive).mp hz)
  have hsum := congrArg (degree M) hpa
  rw [degree_mul] at hsum
  exact ⟨hdne, by omega⟩

end ArtinNormalisers.Homotopy5
