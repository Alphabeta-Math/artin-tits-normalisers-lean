import ArtinChambers.ActualComparison
import ArtinChambers.RibbonDeckLabels
import ArtinRibbons.RibbonGroupoid

/-!
# The actual standard ribbon vertex group and its multiplication conventions

The vertex is literally the image of the standard actual chamber under the
proved ribbon covering. First traversing a ribbon labelled `β`, then one
labelled `γ`, has Artin label `β * γ`. Mathlib's `End` multiplication reverses
categorical traversal, so ordinary ribbon labels identify with `Endᵐᵒᵖ`.
The equivalence with `End` itself therefore sends a label to its inverse.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Sequence4

open CategoryTheory Chamber3 Ribbon2

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- The actual image of the standard chamber under the actual ribbon cover. -/
noncomputable def standardComponentRibbonObject : AssociateReducedRibbonObject M J :=
  (componentRibbonFunctor M J).obj (intervalObject (standardActualChamber M J))

@[simp] theorem standardComponentRibbonObject_underlying :
    (standardComponentRibbonObject M J).obj = actualRibbonObject M ⟨J⟩ := by
  change actualRibbonObject M ⟨actualChamberIndices M J (standardActualChamber M J)⟩ = _
  rw [standardActualChamber_indices]

@[simp] theorem standardComponentRibbonObject_ribbonObject :
    (standardComponentRibbonObject M J).obj.val = (⟨J⟩ : RibbonObject M) := by
  rw [standardComponentRibbonObject_underlying]
  rfl

@[simp] theorem standardComponentRibbonObject_indices :
    (standardComponentRibbonObject M J).obj.val.indices = J := by
  rw [standardComponentRibbonObject_ribbonObject]

/-- The literal Artin label, forgetting only endomorphism/subcategory wrappers. -/
def componentEndValue (f : End (standardComponentRibbonObject M J)) : Artin.Group M :=
  f.asHom.hom.val.val

theorem componentEndValue_reduced (f : End (standardComponentRibbonObject M J)) :
    ReducedArrow M (⟨J⟩ : RibbonObject M) ⟨J⟩ (componentEndValue M J f) := by
  have hf := f.asHom.hom.property
  change ReducedArrow M (standardComponentRibbonObject M J).obj.val
    (standardComponentRibbonObject M J).obj.val (componentEndValue M J f) at hf
  simpa only [standardComponentRibbonObject_ribbonObject] using hf

theorem componentEndValue_injective : Function.Injective (componentEndValue M J) := by
  intro f g h
  apply End.ext
  apply ObjectProperty.hom_ext
  apply Subtype.ext
  exact Subtype.ext h

@[simp] theorem componentEndValue_one :
    componentEndValue M J 1 = 1 := rfl

/-- Endomorphism multiplication reverses categorical traversal. -/
@[simp] theorem componentEndValue_mul (f g : End (standardComponentRibbonObject M J)) :
    componentEndValue M J (f * g) = componentEndValue M J g * componentEndValue M J f := rfl

@[simp] theorem componentEndValue_inv (f : End (standardComponentRibbonObject M J)) :
    componentEndValue M J f⁻¹ = (componentEndValue M J f)⁻¹ := rfl

/-- An actual loop, with the same Artin label, as a categorical endomorphism. -/
noncomputable def componentEndOfLoop (r : reducedRibbonLoops M (⟨J⟩ : RibbonObject M)) :
    End (standardComponentRibbonObject M J) := by
  refine End.of (ObjectProperty.homMk ⟨⟨r.val, ?_⟩, ?_⟩)
  · change IsRibbon M (standardComponentRibbonObject M J).obj.val
      (standardComponentRibbonObject M J).obj.val r.val
    rw [standardComponentRibbonObject_ribbonObject]
    exact r.property.isRibbon
  · change ReducedArrow M (standardComponentRibbonObject M J).obj.val
      (standardComponentRibbonObject M J).obj.val r.val
    rw [standardComponentRibbonObject_ribbonObject]
    exact r.property

@[simp] theorem componentEndOfLoop_asHom_value
    (r : reducedRibbonLoops M (⟨J⟩ : RibbonObject M)) :
    (componentEndOfLoop M J r).asHom.hom.val.val = r.val := rfl

@[simp] theorem componentEndValue_ofLoop
    (r : reducedRibbonLoops M (⟨J⟩ : RibbonObject M)) :
    componentEndValue M J (componentEndOfLoop M J r) = r.val := rfl

@[simp] theorem componentEndOfLoop_one : componentEndOfLoop M J 1 = 1 := by
  apply componentEndValue_injective M J
  rfl

theorem componentEndOfLoop_mul (r s : reducedRibbonLoops M (⟨J⟩ : RibbonObject M)) :
    componentEndOfLoop M J (r * s) = componentEndOfLoop M J s * componentEndOfLoop M J r := by
  apply componentEndValue_injective M J
  rfl

@[simp] theorem componentEndOfLoop_inv
    (r : reducedRibbonLoops M (⟨J⟩ : RibbonObject M)) :
    componentEndOfLoop M J r⁻¹ = (componentEndOfLoop M J r)⁻¹ := by
  apply componentEndValue_injective M J
  rfl

/-- Positive-label convention: labels multiply in traversal order, hence the
opposite of categorical `End`. This includes every signed actual ribbon loop. -/
noncomputable def reducedLoopsEquivComponentEndOp :
    reducedRibbonLoops M (⟨J⟩ : RibbonObject M) ≃*
      (End (standardComponentRibbonObject M J))ᵐᵒᵖ where
  toFun r := MulOpposite.op (componentEndOfLoop M J r)
  invFun f := ⟨componentEndValue M J f.unop, componentEndValue_reduced M J f.unop⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := MulOpposite.unop_injective (componentEndValue_injective M J rfl)
  map_mul' r s := MulOpposite.unop_injective (componentEndOfLoop_mul M J r s)

@[simp] theorem reducedLoopsEquivComponentEndOp_asHom_value
    (r : reducedRibbonLoops M (⟨J⟩ : RibbonObject M)) :
    ((reducedLoopsEquivComponentEndOp M J r).unop).asHom.hom.val.val = r.val := rfl

@[simp] theorem reducedLoopsEquivComponentEndOp_symm_value
    (f : (End (standardComponentRibbonObject M J))ᵐᵒᵖ) :
    ((reducedLoopsEquivComponentEndOp M J).symm f).val = componentEndValue M J f.unop := rfl

/-- Ordinary categorical endomorphisms correspond to inverse Artin labels. -/
noncomputable def componentEndEquivReducedLoops :
    End (standardComponentRibbonObject M J) ≃*
      reducedRibbonLoops M (⟨J⟩ : RibbonObject M) :=
  (MulEquiv.inv' _).trans (reducedLoopsEquivComponentEndOp M J).symm

@[simp] theorem componentEndEquivReducedLoops_value
    (f : End (standardComponentRibbonObject M J)) :
    (componentEndEquivReducedLoops M J f).val = (componentEndValue M J f)⁻¹ := rfl

/-- The inverse-label map from the actual loop subgroup to categorical End. -/
noncomputable def reducedLoopsEquivComponentEnd :
    reducedRibbonLoops M (⟨J⟩ : RibbonObject M) ≃*
      End (standardComponentRibbonObject M J) :=
  (componentEndEquivReducedLoops M J).symm

@[simp] theorem reducedLoopsEquivComponentEnd_asHom_value
    (r : reducedRibbonLoops M (⟨J⟩ : RibbonObject M)) :
    (reducedLoopsEquivComponentEnd M J r).asHom.hom.val.val = r.val⁻¹ := rfl

end ArtinNormalisers.Sequence4
