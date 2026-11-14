import ArtinHomotopy.RibbonGcd
import ArtinChambers.RibbonDeckLabels

/-!
# The actual ordered incoming ribbon vertices

A vertex is an actual signed generated ribbon from a varying standard
parabolic into the fixed target. The order records a genuine positive
generated factor on the left. Exponent degree proves antisymmetry and gives
an integer height strictly increasing along strict order.

The chamber uses the actual inverse Coxeter projection as its transported
facet representative. Right multiplication by any actual target loop is an
order automorphism. Concrete cofinal loops clear every finite set of vertices
to actual positive generated ribbons. No topological conclusion or abstract
label-injectivity hypothesis is part of these definitions.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Deligne5

open Ribbon2 Homotopy5 Chamber3

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group]

/-- Signed incoming vertices in the actual generated ribbon groupoid. -/
structure IncomingVertex (B0 : RibbonObject M) where
  source : RibbonObject M
  value : Artin.Group M
  reduced : ReducedArrow M source B0 value

namespace IncomingVertex

variable {M} {B0 : RibbonObject M}

@[ext] theorem ext {u v : IncomingVertex M B0}
    (hs : u.source = v.source) (hv : u.value = v.value) : u = v := by
  cases u
  cases v
  cases hs
  cases hv
  rfl

/-- A fixed actual incoming label determines its source by genuine positive
parabolic conjugation, rather than by an injectivity field. -/
theorem source_eq_of_value_eq {u v : IncomingVertex M B0} (h : u.value = v.value) :
    u.source = v.source := by
  have hu := u.reduced.isRibbon.inv M
  have hv := v.reduced.isRibbon.inv M
  rw [h] at hu
  exact congrArg (fun J : Set I => (⟨J⟩ : RibbonObject M))
    (isRibbon_target_indices_unique M hu hv)

theorem ext_value {u v : IncomingVertex M B0} (h : u.value = v.value) : u = v :=
  ext (source_eq_of_value_eq h) h

/-- The unique actual factor from the first incoming label to the second. -/
def difference (u v : IncomingVertex M B0) : Artin.Group M := u.value * v.value⁻¹

theorem difference_reduced (u v : IncomingVertex M B0) :
    ReducedArrow M u.source v.source (difference u v) :=
  .comp u.reduced (.inverse v.reduced)

@[simp] theorem difference_self (u : IncomingVertex M B0) : difference u u = 1 :=
  mul_inv_cancel _

theorem difference_mul (u v w : IncomingVertex M B0) :
    difference u v * difference v w = difference u w := by
  unfold difference
  group

theorem difference_eq_one_iff (u v : IncomingVertex M B0) : difference u v = 1 ↔ u = v := by
  constructor
  · intro h
    exact ext_value (mul_inv_eq_one.mp h)
  · rintro rfl
    exact difference_self _

instance partialOrder : PartialOrder (IncomingVertex M B0) where
  le u v := PositiveReducedArrow M u.source v.source (difference u v)
  le_refl u := by
    rw [difference_self]
    exact .identity u.source
  le_trans u v w huv hvw := by
    have h := PositiveReducedArrow.comp huv hvw
    simpa only [difference_mul] using h
  le_antisymm u v huv hvu := by
    have hn := degree_nonneg_of_mem_actualPositiveParabolic M Set.univ huv.positive
    have hn' := degree_nonneg_of_mem_actualPositiveParabolic M Set.univ hvu.positive
    have hz : degree M (difference u v) = 0 := by
      simp only [difference, degree_mul, degree_inv] at hn hn' ⊢
      omega
    exact (difference_eq_one_iff u v).mp
      ((degree_eq_zero_iff_of_mem_actualPositiveParabolic M Set.univ huv.positive).mp hz)

theorem le_iff (u v : IncomingVertex M B0) :
    u ≤ v ↔ PositiveReducedArrow M u.source v.source (u.value * v.value⁻¹) := Iff.rfl

/-- Height increases when a positive factor is removed from an incoming label. -/
def height (u : IncomingVertex M B0) : ℤ := -degree M u.value

theorem height_monotone : Monotone (height : IncomingVertex M B0 → ℤ) := by
  intro u v huv
  have hn := degree_nonneg_of_mem_actualPositiveParabolic M Set.univ huv.positive
  simp only [difference, degree_mul, degree_inv] at hn
  dsimp only [height]
  omega

theorem height_strictMono : StrictMono (height : IncomingVertex M B0 → ℤ) := by
  intro u v huv
  have hn := degree_nonneg_of_mem_actualPositiveParabolic M Set.univ huv.le.positive
  have hne : difference u v ≠ 1 := by
    intro h
    exact huv.ne ((difference_eq_one_iff u v).mp h)
  have hz : degree M (difference u v) ≠ 0 := by
    intro h
    exact hne ((degree_eq_zero_iff_of_mem_actualPositiveParabolic M Set.univ huv.le.positive).mp h)
  simp only [difference, degree_mul, degree_inv] at hn hz
  dsimp only [height]
  omega

theorem height_lt {u v : IncomingVertex M B0} (h : u < v) : height u < height v :=
  height_strictMono h

/-- The inverse projection is the actual representative sending the source
parabolic to the fixed target parabolic. -/
noncomputable def rawFacetLabel (u : IncomingVertex M B0) : RawFacetLabel M B0.indices where
  indices := u.source.indices
  representative := (Artin.projection M u.value)⁻¹
  parabolic_conjugacy := conjugacy_symm M (isRibbon_projection_transporter M u.reduced.isRibbon)

/-- The actual restricted-arrangement chamber of an incoming vertex. -/
noncomputable def chamber (u : IncomingVertex M B0) : ActualChamber M B0.indices :=
  actualChamberOfRawLabel M B0.indices u.rawFacetLabel

@[simp] theorem chamber_indices (u : IncomingVertex M B0) :
    actualChamberIndices M B0.indices u.chamber = u.source.indices :=
  actualChamberIndices_rawLabel M B0.indices u.rawFacetLabel

/-- The corresponding literal source-index chamber fiber. -/
noncomputable def chamberFiber (u : IncomingVertex M B0) : ChamberFiber M B0.indices u.source :=
  ⟨u.chamber, u.chamber_indices⟩

/-- The incoming chamber definition agrees with actual signed fiber transport. -/
theorem fiberTarget_chamber (u v : IncomingVertex M B0) :
    (fiberTarget M B0.indices (Artin.projection M (difference u v))
      (isRibbon_projection_transporter M (difference_reduced u v).isRibbon) u.chamberFiber).val =
        v.chamber := by
  let w := Artin.projection M (difference u v)
  have hw := isRibbon_projection_transporter M (difference_reduced u v).isRibbon
  have hchosen : actualChamberOfRawLabel M B0.indices
      (chamberRawLabel M B0.indices u.chamber) =
        actualChamberOfRawLabel M B0.indices u.rawFacetLabel :=
    chamberRawLabel_chamber M B0.indices _
  have hreplace := rightTransportRawLabel_independent M B0.indices hchosen
    v.source.indices w
    (by simpa only [chamberRawLabel_indices, chamber_indices] using hw) hw
  change actualChamberOfRawLabel M B0.indices
    (fiberTargetLabel M B0.indices w hw u.chamberFiber) = v.chamber
  refine hreplace.trans ?_
  apply (actualChamberOfRawLabel_eq_iff M B0.indices _ v.rawFacetLabel).mpr
  refine ⟨rfl, ?_⟩
  change (((Artin.projection M u.value)⁻¹ * w)⁻¹ *
    (Artin.projection M v.value)⁻¹) ∈ Artin.coxeterParabolic M v.source.indices
  have he : (Artin.projection M u.value)⁻¹ * w = (Artin.projection M v.value)⁻¹ := by
    simp only [w, difference, map_mul, map_inv]
    group
  rw [he, inv_mul_cancel]
  exact Subgroup.one_mem _

/-- Right multiplication by a genuine target loop preserves all actual
incoming labels and sources. -/
def rightMul (b : Artin.Group M) (hb : ReducedArrow M B0 B0 b)
    (u : IncomingVertex M B0) : IncomingVertex M B0 :=
  ⟨u.source, u.value * b, .comp u.reduced hb⟩

@[simp] theorem rightMul_source (b : Artin.Group M) (hb : ReducedArrow M B0 B0 b)
    (u : IncomingVertex M B0) : (rightMul b hb u).source = u.source := rfl

@[simp] theorem rightMul_value (b : Artin.Group M) (hb : ReducedArrow M B0 B0 b)
    (u : IncomingVertex M B0) : (rightMul b hb u).value = u.value * b := rfl

/-- Every signed target loop acts by an actual order automorphism. -/
def rightMulOrderIso (b : Artin.Group M) (hb : ReducedArrow M B0 B0 b) :
    IncomingVertex M B0 ≃o IncomingVertex M B0 where
  toFun := rightMul b hb
  invFun := rightMul b⁻¹ (.inverse hb)
  left_inv u := ext_value (by simp only [rightMul_value]; group)
  right_inv u := ext_value (by simp only [rightMul_value]; group)
  map_rel_iff' := by
    intro u v
    change PositiveReducedArrow M u.source v.source
      ((u.value * b) * (v.value * b)⁻¹) ↔
        PositiveReducedArrow M u.source v.source (u.value * v.value⁻¹)
    have he : (u.value * b) * (v.value * b)⁻¹ = u.value * v.value⁻¹ := by group
    rw [he]

/-- Concrete cofinal right shifts, including their actual signed inverses. -/
noncomputable def cofinalShift (n : ℕ) : IncomingVertex M B0 ≃o IncomingVertex M B0 :=
  rightMulOrderIso (cofinalLoop M B0.indices ^ n)
    (positive_cofinalLoop_pow M B0 n).toReducedArrow

@[simp] theorem cofinalShift_source (n : ℕ) (u : IncomingVertex M B0) :
    (cofinalShift (M := M) (B0 := B0) n u).source = u.source := rfl

@[simp] theorem cofinalShift_value (n : ℕ) (u : IncomingVertex M B0) :
    (cofinalShift (M := M) (B0 := B0) n u).value = u.value * cofinalLoop M B0.indices ^ n := rfl

/-- Every signed incoming vertex becomes positive after sufficiently large
actual cofinal shifts; the conclusion retains positive ribbon generation. -/
theorem eventually_positive (u : IncomingVertex M B0) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m →
      PositiveReducedArrow M u.source B0 ((cofinalShift m u).value) := by
  obtain ⟨n, a, ha, hpa⟩ := u.reduced.positive_fraction M
  refine ⟨n, ?_⟩
  intro m hnm
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  have he : (cofinalShift (n + k) u).value = a * cofinalLoop M B0.indices ^ k := by
    rw [cofinalShift_value, hpa, pow_add]
    group
  rw [he]
  exact .comp ha (positive_cofinalLoop_pow M B0 k)

/-- Every finite family of actual signed incoming vertices can be cleared
simultaneously by the same concrete cofinal right shift. -/
theorem finite_eventually_positive (F : Finset (IncomingVertex M B0)) :
    ∃ n : ℕ, ∀ u ∈ F, ∀ m : ℕ, n ≤ m →
      PositiveReducedArrow M u.source B0 ((cofinalShift m u).value) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert u F _ ih =>
    obtain ⟨n, hn⟩ := u.eventually_positive
    obtain ⟨k, hk⟩ := ih
    refine ⟨max n k, ?_⟩
    intro v hv m hm
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hn m ((le_max_left _ _).trans hm)
    · exact hk v hv m ((le_max_right _ _).trans hm)

end IncomingVertex

end ArtinNormalisers.Deligne5
