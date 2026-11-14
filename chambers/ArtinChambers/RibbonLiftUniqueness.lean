import ArtinChambers.RibbonLifting
import ArtinChambers.GroupoidCover
import ArtinChambers.RibbonComponent
import ArtinChambers.RibbonLiftCompatibility

/-! # Recovery and unique outgoing lifting for the actual ribbon functor

The signed ribbon-family action has already been constructed from the
proved chosen-lcm relations. This file proves recovery on every signed
interval arrow and uses the separately proved value compatibility for the
actual outgoing covering statement.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ArtinNormalisers.Chamber3

open CategoryTheory Ribbon2

namespace FamilyRecovery

variable {D : Type*} [Groupoid D]
  {A B C : FamilyGroupoid D}

/-- One coordinate of a genuine family arrow recovers the specified actual
arrow, including its endpoint index. -/
def Recovers (f : A ⟶ B) (a : A.index) (b : B.index) (δ : A.obj a ⟶ B.obj b) : Prop :=
  f.equiv a = b ∧ HEq (f.hom a) δ

theorem identity (a : A.index) : Recovers (𝟙 A) a a (𝟙 (A.obj a)) := ⟨rfl, HEq.rfl⟩

theorem comp {f : A ⟶ B} {g : B ⟶ C} {a : A.index} {b : B.index} {c : C.index}
    {δ : A.obj a ⟶ B.obj b} {ε : B.obj b ⟶ C.obj c}
    (hf : Recovers f a b δ) (hg : Recovers g b c ε) :
    Recovers (f ≫ g) a c (δ ≫ ε) := by
  obtain ⟨he, hh⟩ := hf
  subst b
  obtain ⟨hge, hgh⟩ := hg
  subst c
  refine ⟨rfl, ?_⟩
  apply heq_of_eq
  change f.hom a ≫ g.hom (f.equiv a) = δ ≫ ε
  rw [eq_of_heq hh, eq_of_heq hgh]

private theorem inverse_heq_of_comp {X Y Z : D} (hZ : Z = X)
    {f : X ⟶ Y} {g : Y ⟶ Z} (h : HEq (f ≫ g) (𝟙 X)) : HEq g (inv f) := by
  subst Z
  exact heq_of_eq (IsIso.eq_inv_of_hom_inv_id (eq_of_heq h))

theorem inverse {f : A ⟶ B} {a : A.index} {b : B.index} {δ : A.obj a ⟶ B.obj b}
    (hf : Recovers f a b δ) : Recovers (inv f) b a (inv δ) := by
  obtain ⟨he, hh⟩ := hf
  subst b
  have hi : (inv f).equiv (f.equiv a) = a := by
    rw [FamilyGroupoid.inv_equiv]
    exact f.equiv.symm_apply_apply a
  refine ⟨hi, ?_⟩
  have hc := FamilyGroupoid.coordinate_heq_of_eq (IsIso.hom_inv_id f) a
  have hcomp : HEq (f.hom a ≫ (inv f).hom (f.equiv a)) (𝟙 (A.obj a)) := hc
  have hrec := inverse_heq_of_comp (congrArg A.obj hi) hcomp
  have hδ : f.hom a = δ := eq_of_heq hh
  exact hrec.trans (by rw [hδ])

end FamilyRecovery

open Theorem18

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- The actual source chamber as a coordinate of the family over its image. -/
noncomputable def distinguishedRibbonIndex
    (X : IntervalGroupoid (E := relativeSubspace J) (actualForms M J)) :
    ((intervalRibbonFunctor M J ⋙ ribbonLiftingFunctor M J).obj X).index :=
  ⟨intervalChamber X, rfl⟩

def IntervalLiftRecovers
    {X Y : IntervalGroupoid (E := relativeSubspace J) (actualForms M J)} (δ : X ⟶ Y) : Prop :=
  FamilyRecovery.Recovers ((intervalRibbonFunctor M J ⋙ ribbonLiftingFunctor M J).map δ)
    (distinguishedRibbonIndex M J X) (distinguishedRibbonIndex M J Y) δ

theorem intervalLiftRecovers_positive (C D : ActualChamber M J) :
    IntervalLiftRecovers M J (intervalPositive C D) := by
  constructor
  · apply Subtype.ext
    exact ribbonLiftInterval_endpoint M J C D
  · exact ribbonLiftInterval_arrow M J C D

private theorem intervalLiftRecovers_comp
    {X Y Z : IntervalGroupoid (E := relativeSubspace J) (actualForms M J)}
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IntervalLiftRecovers M J f) (hg : IntervalLiftRecovers M J g) :
    IntervalLiftRecovers M J (f ≫ g) := by
  change FamilyRecovery.Recovers
    ((intervalRibbonFunctor M J ⋙ ribbonLiftingFunctor M J).map (f ≫ g))
    (distinguishedRibbonIndex M J X) (distinguishedRibbonIndex M J Z) (f ≫ g)
  rw [CategoryTheory.Functor.map_comp]
  exact FamilyRecovery.comp
    (f := (intervalRibbonFunctor M J ⋙ ribbonLiftingFunctor M J).map f)
    (g := (intervalRibbonFunctor M J ⋙ ribbonLiftingFunctor M J).map g)
    (a := distinguishedRibbonIndex M J X) (b := distinguishedRibbonIndex M J Y)
    (c := distinguishedRibbonIndex M J Z) (δ := f) (ε := g) hf hg

/-- Recovery holds for every signed arrow of the actual interval groupoid,
not only the positive intervals used in its presentation. -/
theorem intervalLiftRecovers
    {X Y : IntervalGroupoid (E := relativeSubspace J) (actualForms M J)} (δ : X ⟶ Y) :
    IntervalLiftRecovers M J δ := by
  induction δ using CategoryTheory.Quotient.induction with
  | h f =>
    induction f using Quiver.FreeGroupoid.hom_rec with
    | @of_map X Y e =>
      rcases X with ⟨C⟩
      rcases Y with ⟨D⟩
      have he : e = (PUnit.unit :
          (⟨C⟩ : IntervalVertex (E := relativeSubspace J) (actualForms M J)) ⟶
          (⟨D⟩ : IntervalVertex (E := relativeSubspace J) (actualForms M J))) :=
        @Subsingleton.elim PUnit inferInstance e PUnit.unit
      subst e
      exact intervalLiftRecovers_positive M J C D
    | @inv_of_map X Y e =>
      rcases X with ⟨C⟩
      rcases Y with ⟨D⟩
      have he : e = (PUnit.unit :
          (⟨C⟩ : IntervalVertex (E := relativeSubspace J) (actualForms M J)) ⟶
          (⟨D⟩ : IntervalVertex (E := relativeSubspace J) (actualForms M J))) :=
        @Subsingleton.elim PUnit inferInstance e PUnit.unit
      subst e
      rw [(CategoryTheory.Quotient.functor
        (IntervalRelation (E := relativeSubspace J) (ℓ := actualForms M J))).map_inv]
      change FamilyRecovery.Recovers
        ((intervalRibbonFunctor M J ⋙ ribbonLiftingFunctor M J).map (inv (intervalPositive C D))) _ _ _
      rw [CategoryTheory.Functor.map_inv]
      exact FamilyRecovery.inverse (intervalLiftRecovers_positive M J C D)
    | id X =>
      change FamilyRecovery.Recovers
        ((intervalRibbonFunctor M J ⋙ ribbonLiftingFunctor M J).map (𝟙 _)) _ _ _
      rw [CategoryTheory.Functor.map_id]
      exact FamilyRecovery.identity _
    | @comp X Y Z f g hf hg =>
      let Q := CategoryTheory.Quotient.functor
        (IntervalRelation (E := relativeSubspace J) (ℓ := actualForms M J))
      exact intervalLiftRecovers_comp M J
        (X := Q.obj X) (Y := Q.obj Y) (Z := Q.obj Z)
        (f := Q.map f) (g := Q.map g) hf hg

theorem ribbonLiftInterval_endpoint_all
    {X Y : IntervalGroupoid (E := relativeSubspace J) (actualForms M J)} (δ : X ⟶ Y) :
    ribbonLiftEndpoint M J ((intervalRibbonFunctor M J).map δ) (distinguishedRibbonIndex M J X) =
      distinguishedRibbonIndex M J Y :=
  (intervalLiftRecovers M J δ).1

theorem ribbonLiftInterval_arrow_all
    {X Y : IntervalGroupoid (E := relativeSubspace J) (actualForms M J)} (δ : X ⟶ Y) :
    HEq (ribbonLiftArrow M J ((intervalRibbonFunctor M J).map δ) (distinguishedRibbonIndex M J X)) δ :=
  (intervalLiftRecovers M J δ).2

set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 2000000

/-- The constructed actual outgoing lift, retaining both the geometric
target chamber and its actual interval-groupoid arrow. -/
noncomputable def ribbonOutgoingLift
    (X : IntervalGroupoid (E := relativeSubspace J) (actualForms M J))
    (p : Outgoing (ActualReducedRibbonGroupoid M) ((intervalRibbonFunctor M J).obj X)) :
    Outgoing (IntervalGroupoid (E := relativeSubspace J) (actualForms M J)) X :=
  ⟨intervalObject (ribbonLiftEndpoint M J
      (X := (intervalRibbonFunctor M J).obj X) (Y := p.1) p.2 (distinguishedRibbonIndex M J X)).val,
    ribbonLiftArrow M J (X := (intervalRibbonFunctor M J).obj X) (Y := p.1)
      p.2 (distinguishedRibbonIndex M J X)⟩

/-- The outgoing map with its concrete source and target categories fixed. -/
noncomputable def ribbonOutgoingMap
    (X : IntervalGroupoid (E := relativeSubspace J) (actualForms M J)) :
    Outgoing (IntervalGroupoid (E := relativeSubspace J) (actualForms M J)) X →
      Outgoing (ActualReducedRibbonGroupoid M) ((intervalRibbonFunctor M J).obj X) :=
  fun p => ⟨(intervalRibbonFunctor M J).obj p.1, (intervalRibbonFunctor M J).map p.2⟩

/-- Every signed interval arrow is recovered exactly after mapping it to
the actual ribbon groupoid and applying the constructed lift. -/
theorem ribbonOutgoingLift_mapOutgoing
    (X : IntervalGroupoid (E := relativeSubspace J) (actualForms M J)) :
    Function.LeftInverse (ribbonOutgoingLift M J X) (ribbonOutgoingMap M J X) := by
  intro p
  obtain ⟨Y, δ⟩ := p
  unfold ribbonOutgoingLift ribbonOutgoingMap
  have ho : intervalObject (ribbonLiftEndpoint M J ((intervalRibbonFunctor M J).map δ)
      (distinguishedRibbonIndex M J X)).val = Y :=
    (congrArg (fun (C : ChamberFiber M J ((intervalRibbonFunctor M J).obj Y).val) => intervalObject C.val)
      (ribbonLiftInterval_endpoint_all M J δ)).trans (intervalObject_intervalChamber Y)
  exact Sigma.ext ho (ribbonLiftInterval_arrow_all M J δ)

/-- The separately proved actual ribbon-value compatibility supplies the
other inverse equation, including the literal target ribbon object. -/
theorem mapOutgoing_ribbonOutgoingLift
    (X : IntervalGroupoid (E := relativeSubspace J) (actualForms M J)) :
    Function.RightInverse (ribbonOutgoingLift M J X) (ribbonOutgoingMap M J X) := by
  intro p
  obtain ⟨Y, β⟩ := p
  unfold ribbonOutgoingLift ribbonOutgoingMap
  have ho : (intervalRibbonFunctor M J).obj
      (intervalObject (ribbonLiftEndpoint M J β (distinguishedRibbonIndex M J X)).val) = Y :=
    ribbonLiftSource_eq M J (ribbonLiftEndpoint M J β (distinguishedRibbonIndex M J X))
  exact Sigma.ext ho (ribbonLiftArrow_ribbon_heq M J β (distinguishedRibbonIndex M J X))

/-- The actual interval-to-ribbon functor has unique outgoing lifting.
Both inverse equations are proved above from its actual models. -/
theorem intervalRibbonFunctor_isCovering : IsCoveringFunctor (intervalRibbonFunctor M J) := by
  intro X
  change Function.Bijective (ribbonOutgoingMap M J X)
  constructor
  · exact Function.LeftInverse.injective (ribbonOutgoingLift_mapOutgoing M J X)
  · exact Function.RightInverse.surjective (mapOutgoing_ribbonOutgoingLift M J X)

/-- The same actual covering with its target restricted to the proved full
associate component. No arrows or objects are supplied by a covering axiom. -/
theorem componentRibbonFunctor_isCovering : IsCoveringFunctor (componentRibbonFunctor M J) := by
  let G := intervalRibbonFunctor M J
  let F := componentRibbonFunctor M J
  let incl := (reducedAssociateProperty M J).ι
  intro X
  constructor
  · intro p q hpq
    apply (intervalRibbonFunctor_isCovering M J X).injective
    exact congrArg (mapOutgoing incl (F.obj X)) hpq
  · rintro ⟨Y, β⟩
    let p : Outgoing (ActualReducedRibbonGroupoid M) (G.obj X) := ⟨Y.obj, β.hom⟩
    obtain ⟨q, hq⟩ := (intervalRibbonFunctor_isCovering M J X).surjective p
    have ho : F.obj q.1 = Y := by
      apply ObjectProperty.FullSubcategory.ext
      exact congrArg Sigma.fst hq
    subst Y
    have he : G.map q.2 = β.hom := eq_of_heq (Sigma.mk.inj hq).2
    have heF : F.map q.2 = β := ObjectProperty.hom_ext (reducedAssociateProperty M J) he
    exact ⟨q, Sigma.ext rfl (heq_of_eq heF)⟩

end ArtinNormalisers.Chamber3
