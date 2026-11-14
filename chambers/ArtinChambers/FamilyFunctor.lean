module

public import ArtinChambers.FamilyGroupoid

/-! # Applying a genuine functor to indexed families

The indexing types and equivalences are unchanged. Coordinate objects and
arrows are mapped by the supplied actual functor. No lifting premise is
part of this construction.
-/

@[expose] public section

namespace ArtinNormalisers.Chamber3.FamilyGroupoid

open CategoryTheory

universe u v v' w w'

variable {D : Type v} [Groupoid.{w} D] {C : Type v'} [Groupoid.{w'} C] (F : D ⥤ C)

def mapObject (A : FamilyGroupoid.{u, v} D) : FamilyGroupoid.{u, v'} C :=
  of A.index (fun a => F.obj (A.obj a))

def mapHom {A B : FamilyGroupoid.{u, v} D} (f : A ⟶ B) : mapObject F A ⟶ mapObject F B where
  equiv := f.equiv
  hom a := F.map (f.hom a)

/-- The functor on actual indexed-family groupoids induced by an actual functor. -/
def mapFunctor : FamilyGroupoid.{u, v} D ⥤ FamilyGroupoid.{u, v'} C where
  obj := mapObject F
  map := mapHom F
  map_id A := by
    apply Hom.ext (f := mapHom F (𝟙 A)) (g := 𝟙 (mapObject F A)) rfl
    intro a
    exact heq_of_eq (F.map_id (A.obj a))
  map_comp f g := by
    apply Hom.ext (f := mapHom F (f ≫ g)) (g := mapHom F f ≫ mapHom F g) rfl
    intro a
    exact heq_of_eq (F.map_comp (f.hom a) (g.hom (f.equiv a)))

@[simp] theorem mapFunctor_obj_index (A : FamilyGroupoid.{u, v} D) :
    ((mapFunctor F).obj A).index = A.index := rfl

@[simp] theorem mapFunctor_obj_obj (A : FamilyGroupoid.{u, v} D) (a : A.index) :
    ((mapFunctor F).obj A).obj a = F.obj (A.obj a) := rfl

@[simp] theorem mapFunctor_map_equiv {A B : FamilyGroupoid.{u, v} D} (f : A ⟶ B) :
    ((mapFunctor F).map f).equiv = f.equiv := rfl

@[simp] theorem mapFunctor_map_hom {A B : FamilyGroupoid.{u, v} D} (f : A ⟶ B) (a : A.index) :
    ((mapFunctor F).map f).hom a = F.map (f.hom a) := rfl

end ArtinNormalisers.Chamber3.FamilyGroupoid
