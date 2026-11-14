module

public import ArtinChambers.SignCells
public import Mathlib.CategoryTheory.Groupoid.FreeGroupoid

/-!
# The interval presentation on actual arrangement chambers

There is a positive generator for every ordered pair of actual chambers.
The only relations are the constant interval and composition through a
chamber lying between the endpoints in every hyperplane sign. In particular,
oppositely directed positive generators are not defined as inverses.

This file constructs the genuine groupoid presentation and proves its
universal property for arbitrary target groupoids. Its equivalence with the
adjacent-gallery presentation, and its comparison with the actual complement,
are separate theorems, not assumptions of this construction.
-/

@[expose] public section

namespace ArtinNormalisers.Chamber3

open CategoryTheory

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {H : Type*} {ℓ : H → E →L[ℝ] ℝ}

/-- The middle chamber respects every sign shared by the two endpoints. -/
def ChamberBetween (C D F : Chamber ℓ) : Prop :=
  ∀ h, C.signs h = F.signs h → D.signs h = C.signs h

theorem chamberBetween_left (C D : Chamber ℓ) : ChamberBetween C C D :=
  fun _ _ => rfl

theorem chamberBetween_right (C D : Chamber ℓ) : ChamberBetween C D D :=
  fun _ h => h.symm

theorem ChamberBetween.symm {C D F : Chamber ℓ} (h : ChamberBetween C D F) :
    ChamberBetween F D C := by
  intro k hk
  exact (h k hk.symm).trans hk.symm

/-- A wrapper keeps the complete generating quiver separate from all
category structures later carried by the actual chamber type. -/
@[ext] structure IntervalVertex (ℓ : H → E →L[ℝ] ℝ) where
  chamber : Chamber ℓ

instance intervalVertexQuiver : Quiver.{0} (IntervalVertex ℓ) where
  Hom _ _ := PUnit

/-- The free groupoid on one directed positive edge for each ordered pair. -/
abbrev FreeIntervalGroupoid (ℓ : H → E →L[ℝ] ℝ) :=
  Quiver.FreeGroupoid (IntervalVertex ℓ)

def freeIntervalObject (C : Chamber ℓ) : FreeIntervalGroupoid ℓ :=
  (Quiver.FreeGroupoid.of (IntervalVertex ℓ)).obj ⟨C⟩

def freeIntervalPositive (C D : Chamber ℓ) :
    freeIntervalObject C ⟶ freeIntervalObject D :=
  (Quiver.FreeGroupoid.of (IntervalVertex ℓ)).map
    (PUnit.unit : (⟨C⟩ : IntervalVertex ℓ) ⟶ ⟨D⟩)

/-- Only the geometric interval identities are primitive relations. -/
inductive IntervalRelation : HomRel (FreeIntervalGroupoid ℓ)
  | self (C : Chamber ℓ) : IntervalRelation (freeIntervalPositive C C) (𝟙 _)
  | between (C D F : Chamber ℓ) (h : ChamberBetween C D F) :
      IntervalRelation (freeIntervalPositive C F)
        (freeIntervalPositive C D ≫ freeIntervalPositive D F)

/-- The actual interval groupoid is a free-groupoid quotient by precisely
the displayed interval relations and their categorical congruence closure. -/
abbrev IntervalGroupoid (ℓ : H → E →L[ℝ] ℝ) :=
  CategoryTheory.Quotient (IntervalRelation (ℓ := ℓ))

def intervalObject (C : Chamber ℓ) : IntervalGroupoid ℓ :=
  (CategoryTheory.Quotient.functor (IntervalRelation (ℓ := ℓ))).obj (freeIntervalObject C)

def intervalPositive (C D : Chamber ℓ) : intervalObject C ⟶ intervalObject D :=
  (CategoryTheory.Quotient.functor (IntervalRelation (ℓ := ℓ))).map (freeIntervalPositive C D)

@[simp] theorem intervalPositive_self (C : Chamber ℓ) :
    intervalPositive C C = 𝟙 (intervalObject C) :=
  CategoryTheory.Quotient.sound _ (IntervalRelation.self C)

theorem intervalPositive_comp (C D F : Chamber ℓ) (h : ChamberBetween C D F) :
    intervalPositive C F = intervalPositive C D ≫ intervalPositive D F :=
  CategoryTheory.Quotient.sound _ (IntervalRelation.between C D F h)

/-- The underlying actual chamber, with no quotient of the object set. -/
def intervalChamber (X : IntervalGroupoid ℓ) : Chamber ℓ := X.as.as.chamber

@[simp] theorem intervalChamber_intervalObject (C : Chamber ℓ) :
    intervalChamber (intervalObject C) = C := rfl

@[simp] theorem intervalObject_intervalChamber (X : IntervalGroupoid ℓ) :
    intervalObject (intervalChamber X) = X := by
  cases X with
  | mk X => cases X with | mk X => cases X; rfl

universe u v

/-- Unconstrained data on the directed positive pair generators. -/
structure IntervalGeneratorData (ℓ : H → E →L[ℝ] ℝ) (T : Type u) [Groupoid.{v} T] where
  obj : Chamber ℓ → T
  positive : ∀ C D, obj C ⟶ obj D

namespace IntervalGeneratorData

variable {T : Type u} [Groupoid.{v} T] (A : IntervalGeneratorData ℓ T)

/-- Exactly the two families of primitive interval relations. -/
def RespectsIntervals : Prop :=
  (∀ C, A.positive C C = 𝟙 (A.obj C)) ∧
  ∀ C D F, ChamberBetween C D F →
    A.positive C F = A.positive C D ≫ A.positive D F

def prefunctor : IntervalVertex ℓ ⥤q T where
  obj X := A.obj X.chamber
  map {X Y} _ := A.positive X.chamber Y.chamber

def freeExtension : FreeIntervalGroupoid ℓ ⥤ T :=
  Quiver.FreeGroupoid.lift A.prefunctor

@[simp] theorem freeExtension_obj (C : Chamber ℓ) :
    A.freeExtension.obj (freeIntervalObject C) = A.obj C := rfl

@[simp] theorem freeExtension_positive (C D : Chamber ℓ) :
    A.freeExtension.map (freeIntervalPositive C D) = A.positive C D := by
  have h := Prefunctor.congr_hom (Quiver.FreeGroupoid.lift_spec A.prefunctor)
    (X := ⟨C⟩) (Y := ⟨D⟩)
    (PUnit.unit : (⟨C⟩ : IntervalVertex ℓ) ⟶ ⟨D⟩)
  exact h

def extensionFunctor (hA : A.RespectsIntervals) : IntervalGroupoid ℓ ⥤ T :=
  CategoryTheory.Quotient.lift _ A.freeExtension (by
    intro X Y f g h
    cases h with
    | self C =>
      rw [A.freeExtension.map_id, A.freeExtension_positive]
      exact hA.1 C
    | between C D F hb =>
      rw [A.freeExtension.map_comp, A.freeExtension_positive,
        A.freeExtension_positive, A.freeExtension_positive]
      exact hA.2 C D F hb)

@[simp] theorem extensionFunctor_obj (hA : A.RespectsIntervals) (C : Chamber ℓ) :
    (A.extensionFunctor hA).obj (intervalObject C) = A.obj C := rfl

@[simp] theorem extensionFunctor_positive (hA : A.RespectsIntervals) (C D : Chamber ℓ) :
    (A.extensionFunctor hA).map (intervalPositive C D) = A.positive C D :=
  A.freeExtension_positive C D

set_option backward.isDefEq.respectTransparency.types false in
/-- The positive generators determine genuine functors on the whole
presented groupoid, including inverses and all composite arrows. -/
theorem extensionFunctor_unique (hA : A.RespectsIntervals)
    (F : IntervalGroupoid ℓ ⥤ T)
    (hobj : F.obj = fun X => A.obj (intervalChamber X))
    (hpos : ∀ C D, HEq (F.map (intervalPositive C D)) (A.positive C D)) :
    F = A.extensionFunctor hA := by
  cases F with
  | mk fobj fmap fid fcomp =>
    dsimp only at hobj
    subst fobj
    let F : IntervalGroupoid ℓ ⥤ T :=
      { obj := fun X => A.obj (intervalChamber X)
        map := fmap
        map_id := fid
        map_comp := fcomp }
    change F = A.extensionFunctor hA
    have hpos' (C D : Chamber ℓ) :
        F.map (intervalPositive C D) = A.positive C D := eq_of_heq (hpos C D)
    apply Functor.hext (F := F) (G := A.extensionFunctor hA) (fun _ => rfl)
    intro X Y f
    apply heq_of_eq
    induction f using CategoryTheory.Quotient.induction with
    | h f =>
      induction f using Quiver.FreeGroupoid.hom_rec with
      | @of_map X Y e =>
        rcases X with ⟨C⟩
        rcases Y with ⟨D⟩
        have he : e = (PUnit.unit : (⟨C⟩ : IntervalVertex ℓ) ⟶ ⟨D⟩) := by
          exact @Subsingleton.elim PUnit inferInstance e PUnit.unit
        subst e
        exact (hpos' _ _).trans (A.extensionFunctor_positive hA _ _).symm
      | @inv_of_map X Y e =>
        rcases X with ⟨C⟩
        rcases Y with ⟨D⟩
        have he : e = (PUnit.unit : (⟨C⟩ : IntervalVertex ℓ) ⟶ ⟨D⟩) := by
          exact @Subsingleton.elim PUnit inferInstance e PUnit.unit
        subst e
        rw [(CategoryTheory.Quotient.functor (IntervalRelation (ℓ := ℓ))).map_inv]
        change F.map (inv (intervalPositive C D)) =
          (A.extensionFunctor hA).map (inv (intervalPositive C D))
        simp only [Functor.map_inv]
        simp only [hpos', A.extensionFunctor_positive]
        rfl
      | id X =>
        change F.map (𝟙 _) = (A.extensionFunctor hA).map (𝟙 _)
        exact (F.map_id _).trans ((A.extensionFunctor hA).map_id _).symm
      | comp f g hf hg =>
        simp only [Functor.map_comp]
        rw [hf, hg]
        rfl

/-- Universal extension from arbitrary groupoid-valued assignments satisfying
only the stated interval identities. No geometric comparison is a premise. -/
theorem exists_unique_extension (hA : A.RespectsIntervals) :
    ∃! F : IntervalGroupoid ℓ ⥤ T,
      F.obj = (fun X => A.obj (intervalChamber X)) ∧
      ∀ C D, HEq (F.map (intervalPositive C D)) (A.positive C D) := by
  refine ⟨A.extensionFunctor hA, ⟨rfl, ?_⟩, ?_⟩
  · intro C D
    exact heq_of_eq (A.extensionFunctor_positive hA C D)
  · intro F hF
    exact A.extensionFunctor_unique hA F hF.1 hF.2

end IntervalGeneratorData

end ArtinNormalisers.Chamber3
