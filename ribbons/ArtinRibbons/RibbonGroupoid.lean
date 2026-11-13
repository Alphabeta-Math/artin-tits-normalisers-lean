import ArtinRibbons.Positive
import ArtinNormalisers.Artin.ExactSequence
import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# The larger ribbon groupoid

The morphisms are actual elements of the parent Artin group, satisfying the
positive-parabolic conjugation condition of arXiv:2509.21915v3, Definition
5.1 (PDF p. 21). Composition is multiplication on the right: first `β`, then
`γ`, has label `β * γ`. The construction on all standard parabolics needs
no spherical hypothesis. Restricting to associates (Definition 2.7, PDF p. 5)
gives the objects of the article's larger ribbon groupoid.

This is not the reduced ribbon groupoid of Definition 5.5. Generation by its
elementary `μ` morphisms and the reduced-ribbon normalizer isomorphism are
separate obligations. In particular loops here form a subgroup of the Artin
group; their categorical endomorphism group is identified with its opposite
because categorical endomorphism multiplication reverses composition.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Ribbon2

open CategoryTheory

variable {I : Type*} (M : CoxeterMatrix I)

/-- A wrapper for a standard parabolic index set, carrying the ribbon
category structure without changing the category structure on plain sets. -/
structure RibbonObject (M : CoxeterMatrix I) where
  indices : Set I

/-- The defining condition on an actual Artin element. This is equivalent
to `A⁺_X β = β A⁺_Y`. -/
def IsRibbon (X Y : RibbonObject M) (β : Artin.Group M) : Prop :=
  ∀ a : Artin.Group M, a ∈ actualPositiveParabolic M X.indices ↔
    β⁻¹ * a * β ∈ actualPositiveParabolic M Y.indices

/-- The conjugation condition is exactly the positive coset equality used
in Definition 5.1. -/
theorem isRibbon_iff_positiveCosets_eq (X Y : RibbonObject M) (β : Artin.Group M) :
    IsRibbon M X Y β ↔
      (fun a : Artin.Group M => a * β) ''
          (actualPositiveParabolic M X.indices : Set (Artin.Group M)) =
        (fun a : Artin.Group M => β * a) ''
          (actualPositiveParabolic M Y.indices : Set (Artin.Group M)) := by
  constructor
  · intro h
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨β⁻¹ * a * β, (h a).mp ha, by simp [mul_assoc]⟩
    · rintro ⟨a, ha, rfl⟩
      refine ⟨β * a * β⁻¹, (h _).mpr ?_, by simp [mul_assoc]⟩
      simpa [mul_assoc] using ha
  · intro h a
    constructor
    · intro ha
      have hz : a * β ∈ (fun b : Artin.Group M => β * b) ''
          (actualPositiveParabolic M Y.indices : Set (Artin.Group M)) := by
        rw [← h]
        exact ⟨a, ha, rfl⟩
      obtain ⟨b, hb, hba⟩ := hz
      have heq : β⁻¹ * a * β = b := by
        calc
          β⁻¹ * a * β = β⁻¹ * (a * β) := mul_assoc _ _ _
          _ = β⁻¹ * (β * b) := congrArg (fun z => β⁻¹ * z) hba.symm
          _ = b := by simp
      rwa [heq]
    · intro ha
      have hz : a * β ∈ (fun b : Artin.Group M => b * β) ''
          (actualPositiveParabolic M X.indices : Set (Artin.Group M)) := by
        rw [h]
        exact ⟨β⁻¹ * a * β, ha, by simp [mul_assoc]⟩
      obtain ⟨b, hb, hba⟩ := hz
      have hba' : b = a := mul_right_cancel hba
      subst b
      exact hb

theorem isRibbon_one (X : RibbonObject M) : IsRibbon M X X 1 := by
  intro a
  simp

theorem IsRibbon.mul {X Y Z : RibbonObject M} {β γ : Artin.Group M}
    (hβ : IsRibbon M X Y β) (hγ : IsRibbon M Y Z γ) :
    IsRibbon M X Z (β * γ) := by
  intro a
  simpa only [mul_inv_rev, mul_assoc] using (hβ a).trans (hγ (β⁻¹ * a * β))

theorem IsRibbon.inv {X Y : RibbonObject M} {β : Artin.Group M}
    (hβ : IsRibbon M X Y β) : IsRibbon M Y X β⁻¹ := by
  intro a
  simpa [mul_assoc] using (hβ (β * a * β⁻¹)).symm

/-- Morphisms are actual Artin elements, with the positive conjugation
condition as a property rather than a chosen normalizer quotient label. -/
abbrev RibbonHom (X Y : RibbonObject M) :=
  {β : Artin.Group M // IsRibbon M X Y β}

instance ribbonGroupoid : Groupoid (RibbonObject M) where
  Hom X Y := RibbonHom M X Y
  id X := ⟨1, isRibbon_one M X⟩
  comp β γ := ⟨β.1 * γ.1, β.2.mul M γ.2⟩
  id_comp β := Subtype.ext (one_mul β.1)
  comp_id β := Subtype.ext (mul_one β.1)
  assoc β γ δ := Subtype.ext (mul_assoc β.1 γ.1 δ.1)
  inv β := ⟨β.1⁻¹, β.2.inv M⟩
  inv_comp β := Subtype.ext (inv_mul_cancel β.1)
  comp_inv β := Subtype.ext (mul_inv_cancel β.1)

@[simp]
theorem ribbon_comp_value {X Y Z : RibbonObject M} (β : X ⟶ Y) (γ : Y ⟶ Z) :
    (β ≫ γ).1 = β.1 * γ.1 := rfl

/-- Conjugation by a ribbon also transports the generated parabolic groups.
This uses the proved subgroup closure of the actual positive parabolic. -/
theorem IsRibbon.conjugates_parabolic {X Y : RibbonObject M} {β : Artin.Group M}
    (hβ : IsRibbon M X Y β) (a : Artin.Group M) :
    a ∈ Artin.parabolic M X.indices ↔ β⁻¹ * a * β ∈ Artin.parabolic M Y.indices := by
  have forward {U V : RibbonObject M} {b : Artin.Group M}
      (hb : IsRibbon M U V b) {c : Artin.Group M}
      (hc : c ∈ Artin.parabolic M U.indices) :
      b⁻¹ * c * b ∈ Artin.parabolic M V.indices := by
    have hle : Artin.parabolic M U.indices ≤
        (Artin.parabolic M V.indices).comap (MulAut.conj b⁻¹).toMonoidHom := by
      rw [← subgroupClosure_actualPositiveParabolic M U.indices]
      apply (Subgroup.closure_le _).2
      intro c hc
      change b⁻¹ * c * (b⁻¹)⁻¹ ∈ Artin.parabolic M V.indices
      simpa only [inv_inv, Subgroup.mem_toSubmonoid] using
        actualPositiveParabolic_le_parabolic M V.indices ((hb c).mp hc)
    have hmem := hle hc
    change b⁻¹ * c * (b⁻¹)⁻¹ ∈ Artin.parabolic M V.indices at hmem
    simpa only [inv_inv] using hmem
  constructor
  · exact forward hβ
  · intro ha
    simpa [mul_assoc] using forward (hβ.inv M) ha

/-- A ribbon conjugates the actual Coxeter parabolics by its canonical
projection, rather than by an independently chosen Coxeter element. -/
theorem IsRibbon.conjugates_coxeterParabolic {X Y : RibbonObject M}
    {β : Artin.Group M} (hβ : IsRibbon M X Y β) (w : M.Group) :
    w ∈ Artin.coxeterParabolic M X.indices ↔
      (Artin.projection M β)⁻¹ * w * Artin.projection M β ∈
        Artin.coxeterParabolic M Y.indices := by
  have forward {U V : RibbonObject M} {b : Artin.Group M}
      (hb : IsRibbon M U V b) {v : M.Group}
      (hv : v ∈ Artin.coxeterParabolic M U.indices) :
      (Artin.projection M b)⁻¹ * v * Artin.projection M b ∈
        Artin.coxeterParabolic M V.indices := by
    rw [← Artin.map_parabolic M U.indices] at hv
    obtain ⟨a, ha, hpa⟩ := Subgroup.mem_map.mp hv
    have hm : Artin.projection M (b⁻¹ * a * b) ∈
        (Artin.parabolic M V.indices).map (Artin.projection M) := Subgroup.mem_map.mpr
      ⟨b⁻¹ * a * b, (hb.conjugates_parabolic M a).mp ha, rfl⟩
    rw [Artin.map_parabolic M V.indices] at hm
    simpa only [map_mul, map_inv, hpa] using hm
  constructor
  · exact forward hβ
  · intro hw
    simpa [map_inv, mul_assoc] using forward (hβ.inv M) hw

/-- Associates in the sense of Definition 2.7: the actual standard Coxeter
parabolics are conjugate. The orientation of the witness is explicit. -/
def ParabolicAssociate (J K : Set I) : Prop :=
  ∃ w : M.Group, ∀ a : M.Group,
    a ∈ Artin.coxeterParabolic M J ↔ w⁻¹ * a * w ∈ Artin.coxeterParabolic M K

theorem IsRibbon.parabolicAssociate {X Y : RibbonObject M} {β : Artin.Group M}
    (hβ : IsRibbon M X Y β) : ParabolicAssociate M X.indices Y.indices :=
  ⟨Artin.projection M β, hβ.conjugates_coxeterParabolic M⟩

/-- The full subcategory on associates of a fixed `J`, which supplies the
object restriction of Definition 5.1 without changing its morphisms. -/
abbrev AssociateRibbonObject (J : Set I) :=
  (show ObjectProperty (RibbonObject M) from
    fun X => ParabolicAssociate M X.indices J).FullSubcategory

instance associateRibbonGroupoid (J : Set I) : Groupoid (AssociateRibbonObject M J) :=
  inferInstanceAs (Groupoid (InducedCategory (RibbonObject M)
    (fun X : AssociateRibbonObject M J => X.obj)))

/-- Loops form a literal subgroup of the actual Artin group, with its
ordinary multiplication. No quotient or reduced-ribbon generation is used. -/
def ribbonLoops (X : RibbonObject M) : Subgroup (Artin.Group M) where
  carrier := {β | IsRibbon M X X β}
  one_mem' := isRibbon_one M X
  mul_mem' hβ hγ := hβ.mul M hγ
  inv_mem' hβ := hβ.inv M

/-- The categorical endomorphism group uses the opposite multiplication
from the actual Artin labels. This is the explicit convention bridge. -/
def endEquivRibbonLoopsOpposite (X : RibbonObject M) :
    End X ≃* (ribbonLoops M X)ᵐᵒᵖ where
  toFun β := MulOpposite.op ⟨β.asHom.1, β.asHom.2⟩
  invFun β := End.of ⟨β.unop.1, β.unop.2⟩
  left_inv _β := End.ext rfl
  right_inv _β := MulOpposite.unop_injective rfl
  map_mul' _ _ := rfl

/-- A loop normalizes the actual generated Artin parabolic. -/
theorem ribbonLoop_mem_normalizer (X : RibbonObject M) (β : ribbonLoops M X) :
    (β : Artin.Group M) ∈
      Subgroup.normalizer (Artin.parabolic M X.indices : Set (Artin.Group M)) := by
  apply Subgroup.mem_normalizer_iff''.2
  exact β.2.conjugates_parabolic M

/-- Canonical inclusion of ribbon labels into the actual Artin normalizer. -/
def ribbonLoopsToNormalizer (X : RibbonObject M) :
    ribbonLoops M X →*
      Subgroup.normalizer (Artin.parabolic M X.indices : Set (Artin.Group M)) where
  toFun β := ⟨β, ribbonLoop_mem_normalizer M X β⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem ribbonLoopsToNormalizer_injective (X : RibbonObject M) :
    Function.Injective (ribbonLoopsToNormalizer M X) := by
  intro β γ h
  apply Subtype.ext
  exact congrArg (fun n : Subgroup.normalizer
    (Artin.parabolic M X.indices : Set (Artin.Group M)) => (n : Artin.Group M)) h

/-- The genuine projection from larger-ribbon loops to the actual
normalizer quotient. Surjectivity and injectivity are not asserted here. -/
def ribbonLoopsToNormalizerQuotient (X : RibbonObject M) :
    ribbonLoops M X →* Artin.normalizerQuotient M X.indices :=
  (QuotientGroup.mk' ((Artin.parabolic M X.indices).subgroupOf
    (Subgroup.normalizer (Artin.parabolic M X.indices : Set (Artin.Group M))))).comp
      (ribbonLoopsToNormalizer M X)

end ArtinNormalisers.Ribbon2
