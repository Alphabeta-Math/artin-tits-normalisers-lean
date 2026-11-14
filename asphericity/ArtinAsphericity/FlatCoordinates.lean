module

public import ArtinChambers.Dominant
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Actual complementary coordinates on the relative dual flat

Restricting simple-root evaluation to the indices outside `K` identifies the
actual relative flat with a real product space. Its inverse extends the
coordinates by zero on `K`, using the existing dual-coordinate equivalence
and its actual product topology. The continuous linear equivalence and
strict-orthant description work in arbitrary rank. Finite rank additionally
gives a genuine coordinate basis and finite dimension, including dimension
zero when every index lies in `K`.
-/

set_option autoImplicit false

@[expose] public section

namespace ArtinNormalisers.Asphericity5

open Theorem18 Chamber3 Module

variable {I : Type*}

/-- Extend complementary simple coordinates by zero on the selected indices. -/
noncomputable def flatCoordinateZeroExtension (K : Set I)
    (f : {i : I // i ∉ K} → ℝ) : I → ℝ := by
  classical
  exact fun i => if hi : i ∈ K then 0 else f ⟨i, hi⟩

theorem flatCoordinateZeroExtension_of_mem (K : Set I)
    (f : {i : I // i ∉ K} → ℝ) {i : I} (hi : i ∈ K) :
    flatCoordinateZeroExtension K f i = 0 := by
  classical
  simp [flatCoordinateZeroExtension, hi]

@[simp]
theorem flatCoordinateZeroExtension_apply (K : Set I)
    (f : {i : I // i ∉ K} → ℝ) (i : {i : I // i ∉ K}) :
    flatCoordinateZeroExtension K f i = f i := by
  classical
  simp [flatCoordinateZeroExtension, i.property]

theorem continuous_flatCoordinateZeroExtension (K : Set I) :
    Continuous (flatCoordinateZeroExtension K) := by
  classical
  apply continuous_pi
  intro i
  by_cases hi : i ∈ K
  · simpa only [flatCoordinateZeroExtension, dite_eq_left hi] using
      (continuous_const : Continuous (fun _ : ({i : I // i ∉ K} → ℝ) => (0 : ℝ)))
  · simpa only [flatCoordinateZeroExtension, dite_eq_right hi] using
      (continuous_apply (⟨i, hi⟩ : {i : I // i ∉ K}))

/-- The actual relative flat, with its inherited topology, has exactly the
complementary simple-root coordinates. No finiteness hypothesis is needed. -/
noncomputable def flatComplementCoordinates (K : Set I) :
    relativeSubspace K ≃L[ℝ] ({i : I // i ∉ K} → ℝ) where
  toLinearEquiv :=
    { toFun := fun φ i => φ.val (simpleRoot i)
      invFun := fun f => ⟨(dualCoordinates (I := I)).symm (flatCoordinateZeroExtension K f), by
        intro i hi
        change dualCoordinates ((dualCoordinates (I := I)).symm (flatCoordinateZeroExtension K f)) i = 0
        rw [LinearEquiv.apply_symm_apply]
        exact flatCoordinateZeroExtension_of_mem K f hi⟩
      left_inv := by
        intro φ
        classical
        apply Subtype.ext
        apply (dualCoordinates (I := I)).injective
        rw [LinearEquiv.apply_symm_apply]
        funext i
        change flatCoordinateZeroExtension K (fun j => φ.val (simpleRoot j)) i = φ.val (simpleRoot i)
        by_cases hi : i ∈ K
        · rw [flatCoordinateZeroExtension_of_mem K _ hi]
          exact (φ.property i hi).symm
        · simp [flatCoordinateZeroExtension, hi]
      right_inv := by
        intro f
        funext i
        change dualCoordinates ((dualCoordinates (I := I)).symm (flatCoordinateZeroExtension K f)) i = f i
        rw [LinearEquiv.apply_symm_apply, flatCoordinateZeroExtension_apply]
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  continuous_toFun := continuous_pi fun i =>
    (continuous_evaluation (simpleRoot (i : I))).comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (dualCoordinatesHomeomorph (I := I)).symm.continuous_toFun.comp
      (continuous_flatCoordinateZeroExtension K)

@[simp]
theorem flatComplementCoordinates_apply (K : Set I) (φ : relativeSubspace K)
    (i : {i : I // i ∉ K}) :
    flatComplementCoordinates K φ i = φ.val (simpleRoot i) := rfl

theorem flatComplementCoordinates_symm_apply_simpleRoot (K : Set I)
    (f : {i : I // i ∉ K} → ℝ) (i : I) :
    ((flatComplementCoordinates K).symm f).val (simpleRoot i) =
      flatCoordinateZeroExtension K f i := by
  change dualCoordinates ((dualCoordinates (I := I)).symm (flatCoordinateZeroExtension K f)) i = _
  exact congrArg (fun g : I → ℝ => g i) ((dualCoordinates (I := I)).apply_symm_apply _)

@[simp]
theorem flatComplementCoordinates_symm_apply (K : Set I)
    (f : {i : I // i ∉ K} → ℝ) (i : {i : I // i ∉ K}) :
    ((flatComplementCoordinates K).symm f).val (simpleRoot i) = f i := by
  rw [flatComplementCoordinates_symm_apply_simpleRoot, flatCoordinateZeroExtension_apply]

theorem flatComplementCoordinates_symm_of_mem (K : Set I)
    (f : {i : I // i ∉ K} → ℝ) {i : I} (hi : i ∈ K) :
    ((flatComplementCoordinates K).symm f).val (simpleRoot i) = 0 := by
  rw [flatComplementCoordinates_symm_apply_simpleRoot, flatCoordinateZeroExtension_of_mem K f hi]

/-- The actual standard facet inside its actual relative flat is exactly
the strict positive orthant in these complementary coordinates. -/
theorem mem_standardFacet_iff_flatComplementCoordinates_pos (M : CoxeterMatrix I)
    (K : Set I) (φ : relativeSubspace K) :
    φ.val ∈ standardFacet M K ↔ ∀ i : {i : I // i ∉ K}, 0 < flatComplementCoordinates K φ i := by
  constructor
  · intro hφ i
    exact hφ.2 i i.property
  · intro hφ
    exact ⟨φ.property, fun i hi => hφ ⟨i, hi⟩⟩

theorem flatComplementCoordinates_standardFacet (M : CoxeterMatrix I) (K : Set I) :
    flatComplementCoordinates K ''
        ((Subtype.val : relativeSubspace K → Dual I) ⁻¹' standardFacet M K) =
      {f : ({i : I // i ∉ K} → ℝ) | ∀ i, 0 < f i} := by
  ext f
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    exact (mem_standardFacet_iff_flatComplementCoordinates_pos M K φ).mp hφ
  · intro hf
    change ∀ i, 0 < f i at hf
    refine ⟨(flatComplementCoordinates K).symm f, ?_,
      (flatComplementCoordinates K).apply_symm_apply f⟩
    apply (mem_standardFacet_iff_flatComplementCoordinates_pos M K _).mpr
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hf

/-- In finite rank, the actual flat has a genuine basis indexed by the
unselected simple indices, rather than a merely spanning family. -/
noncomputable def flatComplementBasis [Finite I] (K : Set I) :
    Basis {i : I // i ∉ K} ℝ (relativeSubspace K) :=
  Basis.ofEquivFun (flatComplementCoordinates K).toLinearEquiv

@[simp]
theorem flatComplementBasis_repr [Finite I] (K : Set I) (φ : relativeSubspace K)
    (i : {i : I // i ∉ K}) :
    (flatComplementBasis K).repr φ i = φ.val (simpleRoot i) :=
  Basis.ofEquivFun_repr_apply (flatComplementCoordinates K).toLinearEquiv φ i

theorem finiteDimensional_relativeSubspace [Finite I] (K : Set I) :
    FiniteDimensional ℝ (relativeSubspace K) :=
  FiniteDimensional.of_injective (flatComplementCoordinates K).toLinearMap
    (flatComplementCoordinates K).injective

theorem finrank_relativeSubspace [Finite I] (K : Set I) :
    Module.finrank ℝ (relativeSubspace K) = Nat.card {i : I // i ∉ K} := by
  let := Fintype.ofFinite {i : I // i ∉ K}
  rw [(flatComplementCoordinates K).toLinearEquiv.finrank_eq, Module.finrank_pi]
  exact (Nat.card_eq_fintype_card).symm

end ArtinNormalisers.Asphericity5
