module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.EqToHom

/-!
# The groupoid of indexed families of objects

An arrow consists of an equivalence of its indexing types together with an
actual coordinate morphism in the target groupoid. Indexing types, target
objects and target morphisms have independent universes. Empty families are
allowed. The construction contains no comparison or lifting assumptions.
-/

@[expose] public section

set_option autoImplicit false

namespace ArtinNormalisers.Chamber3

open CategoryTheory

universe w

/-- An arbitrary indexed family of actual objects of `D`. -/
structure FamilyGroupoid.{u, v} (D : Type v) where
  index : Type u
  obj : index → D

universe u v

namespace FamilyGroupoid

variable {D : Type v}

/-- Construct a family from its actual indexing type and object function. -/
def of (α : Type u) (f : α → D) : FamilyGroupoid.{u, v} D := ⟨α, f⟩

@[simp] theorem of_index (α : Type u) (f : α → D) : (of α f).index = α := rfl
@[simp] theorem of_obj (α : Type u) (f : α → D) (a : α) : (of α f).obj a = f a := rfl

variable [Groupoid.{w} D]

/-- The actual family arrows, with an equivalence on coordinates and an
actual target-groupoid morphism at every coordinate. -/
structure Hom (A B : FamilyGroupoid.{u, v} D) where
  equiv : A.index ≃ B.index
  hom : ∀ a, A.obj a ⟶ B.obj (equiv a)

namespace Hom

variable {A B C F : FamilyGroupoid.{u, v} D}

/-- Heterogeneous coordinate equality accounts for the codomain dependence
on the indexing equivalence. -/
@[ext] theorem ext {f g : Hom A B} (he : f.equiv = g.equiv)
    (hh : ∀ a, HEq (f.hom a) (g.hom a)) : f = g := by
  rcases f with ⟨ef, hf⟩
  rcases g with ⟨eg, hg⟩
  cases he
  have hfg : hf = hg := by
    funext a
    exact eq_of_heq (hh a)
  cases hfg
  rfl

def id (A : FamilyGroupoid.{u, v} D) : Hom A A :=
  ⟨Equiv.refl A.index, fun a => 𝟙 (A.obj a)⟩

def comp (f : Hom A B) (g : Hom B C) : Hom A C :=
  ⟨f.equiv.trans g.equiv, fun a => f.hom a ≫ g.hom (f.equiv a)⟩

/-- The inverse uses the actual inverse coordinate morphism. The preceding
`eqToHom` is the necessary transport along `e (e⁻¹ b) = b`. -/
noncomputable def inv (f : Hom A B) : Hom B A where
  equiv := f.equiv.symm
  hom b := eqToHom (congrArg B.obj (f.equiv.apply_symm_apply b).symm) ≫
    CategoryTheory.inv (f.hom (f.equiv.symm b))

theorem id_comp (f : Hom A B) : comp (id A) f = f := by
  apply ext (f := comp (id A) f) (g := f) (Equiv.refl_trans f.equiv)
  intro a
  change HEq ((𝟙 (A.obj a)) ≫ f.hom a) (f.hom a)
  simp

theorem comp_id (f : Hom A B) : comp f (id B) = f := by
  apply ext (f := comp f (id B)) (g := f) (Equiv.trans_refl f.equiv)
  intro a
  change HEq (f.hom a ≫ 𝟙 (B.obj (f.equiv a))) (f.hom a)
  simp

theorem assoc (f : Hom A B) (g : Hom B C) (h : Hom C F) :
    comp (comp f g) h = comp f (comp g h) := by
  apply ext (f := comp (comp f g) h) (g := comp f (comp g h)) rfl
  intro a
  change HEq ((f.hom a ≫ g.hom (f.equiv a)) ≫ h.hom (g.equiv (f.equiv a)))
    (f.hom a ≫ (g.hom (f.equiv a) ≫ h.hom (g.equiv (f.equiv a))))
  simp only [Category.assoc]
  rfl

theorem inv_comp (f : Hom A B) : comp (inv f) f = id B := by
  apply ext (Equiv.symm_trans_self f.equiv)
  intro b
  change HEq ((eqToHom (congrArg B.obj (f.equiv.apply_symm_apply b).symm) ≫
      CategoryTheory.inv (f.hom (f.equiv.symm b))) ≫ f.hom (f.equiv.symm b)) (𝟙 (B.obj b))
  rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  exact eqToHom_heq_id_dom _ _ _

theorem comp_inv (f : Hom A B) : comp f (inv f) = id A := by
  apply ext (Equiv.self_trans_symm f.equiv)
  intro a
  change HEq (f.hom a ≫
    (eqToHom (congrArg B.obj (f.equiv.apply_symm_apply (f.equiv a)).symm) ≫
      CategoryTheory.inv (f.hom (f.equiv.symm (f.equiv a))))) (𝟙 (A.obj a))
  have hn := eqToHom_naturality f.hom (f.equiv.symm_apply_apply a).symm
  rw [← Category.assoc, hn, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  exact eqToHom_heq_id_dom _ _ _

end Hom

/-- The genuine groupoid structure on all indexed families. -/
noncomputable instance groupoid : Groupoid.{max u w} (FamilyGroupoid.{u, v} D) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc
  inv := Hom.inv
  inv_comp := Hom.inv_comp
  comp_inv := Hom.comp_inv

variable {A B C : FamilyGroupoid.{u, v} D}

/-- Extract the actual indexing equivalence of a family arrow. -/
abbrev indexEquiv (f : A ⟶ B) : A.index ≃ B.index := f.equiv

/-- Extract the actual coordinate arrow, retaining its correct target. -/
abbrev coordinate (f : A ⟶ B) (a : A.index) : A.obj a ⟶ B.obj (indexEquiv f a) := f.hom a

@[simp] theorem id_equiv (A : FamilyGroupoid.{u, v} D) :
    (𝟙 A : A ⟶ A).equiv = Equiv.refl A.index := rfl

@[simp] theorem id_hom (A : FamilyGroupoid.{u, v} D) (a : A.index) :
    (𝟙 A : A ⟶ A).hom a = 𝟙 (A.obj a) := rfl

@[simp] theorem comp_equiv (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).equiv = f.equiv.trans g.equiv := rfl

@[simp] theorem comp_hom (f : A ⟶ B) (g : B ⟶ C) (a : A.index) :
    (f ≫ g).hom a = f.hom a ≫ g.hom (f.equiv a) := rfl

@[simp] theorem inv_equiv (f : A ⟶ B) :
    (CategoryTheory.inv f).equiv = f.equiv.symm := by
  rw [← Groupoid.inv_eq_inv f]
  rfl

@[simp] theorem groupoid_inv_hom (f : A ⟶ B) (b : B.index) :
    (Groupoid.inv f).hom b =
      eqToHom (congrArg B.obj (f.equiv.apply_symm_apply b).symm) ≫
        CategoryTheory.inv (f.hom (f.equiv.symm b)) := rfl

@[simp] theorem inv_hom (f : A ⟶ B) (b : B.index) :
    HEq ((CategoryTheory.inv f).hom b)
      (eqToHom (congrArg B.obj (f.equiv.apply_symm_apply b).symm) ≫
        CategoryTheory.inv (f.hom (f.equiv.symm b))) := by
  rw [← Groupoid.inv_eq_inv f]
  rfl

theorem equiv_eq_of_eq {f g : A ⟶ B} (h : f = g) : f.equiv = g.equiv := congrArg Hom.equiv h

theorem coordinate_heq_of_eq {f g : A ⟶ B} (h : f = g) (a : A.index) :
    HEq (f.hom a) (g.hom a) := by
  cases h
  rfl

end FamilyGroupoid
end ArtinNormalisers.Chamber3
