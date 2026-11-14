import ArtinChambers.RibbonLifting

/-!
# Projecting an actual lifted ribbon recovers its actual Artin label

Compare two genuine functors to families in the one-object groupoid of the
opposite Artin group. One maps the constructed coordinate lifts through the
actual ribbon functor. The other uses the same constructed index bijections
and the original Artin labels as constant coordinates. Their equality follows
from the proved signed ribbon universal property and the actual atomic formula.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ArtinNormalisers.Chamber3

open CategoryTheory Ribbon2

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- Actual ribbon labels, with the opposite correcting one-object composition. -/
noncomputable def ribbonValueFunctor : ActualReducedRibbonGroupoid M ⥤
    SingleObj (Artin.Group M)ᵐᵒᵖ where
  obj _ := SingleObj.star _
  map β := MulOpposite.op β.val.val
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The coordinate value of the actual interval-to-ribbon functor. -/
noncomputable def intervalRibbonValueFunctor := intervalRibbonFunctor M J ⋙ ribbonValueFunctor M

/-- Actual constructed signed lifts, followed by their actual Artin values. -/
noncomputable def liftedRibbonValueFunctor := ribbonLiftingFunctor M J ⋙
  FamilyGroupoid.mapFunctor (intervalRibbonValueFunctor M J)

/-- A genuine comparison functor with the constructed geometric index
bijections and the original ribbon's actual Artin value at each coordinate. -/
noncomputable def tautologicalRibbonValueFunctor : ActualReducedRibbonGroupoid M ⥤
    FamilyGroupoid (SingleObj (Artin.Group M)ᵐᵒᵖ) where
  obj := (liftedRibbonValueFunctor M J).obj
  map β :=
    { equiv := ((ribbonLiftingFunctor M J).map β).equiv
      hom _ := MulOpposite.op β.val.val }
  map_id X := by
    apply FamilyGroupoid.Hom.ext
    · change ((ribbonLiftingFunctor M J).map (𝟙 X)).equiv = Equiv.refl _
      exact FamilyGroupoid.equiv_eq_of_eq ((ribbonLiftingFunctor M J).map_id X)
    · intro C
      rfl
  map_comp β γ := by
    apply FamilyGroupoid.Hom.ext
    · change ((ribbonLiftingFunctor M J).map (β ≫ γ)).equiv =
        ((ribbonLiftingFunctor M J).map β).equiv.trans ((ribbonLiftingFunctor M J).map γ).equiv
      exact FamilyGroupoid.equiv_eq_of_eq ((ribbonLiftingFunctor M J).map_comp β γ)
    · intro C
      rfl

/-- Generator data induced by a genuine functor, without an extra semantic premise. -/
noncomputable def liftedRibbonValueData : RibbonGeneratorData M
    (FamilyGroupoid (SingleObj (Artin.Group M)ᵐᵒᵖ)) where
  obj X := (liftedRibbonValueFunctor M J).obj (actualRibbonObject M X)
  atom X a ha := (liftedRibbonValueFunctor M J).map (actualAtomicHom M X a ha)

theorem liftedRibbonValueData_word {X Y : RibbonObject M} (p : AtomicWord M X Y) :
    (liftedRibbonValueData M J).wordImage p =
      (liftedRibbonValueFunctor M J).map
        (actualReducedHom M p.toPositiveReducedArrow.toReducedArrow) := by
  induction p with
  | nil X => exact ((liftedRibbonValueFunctor M J).map_id (actualRibbonObject M X)).symm
  | @cons X Y a ha p ih =>
    rw [RibbonGeneratorData.wordImage_cons, ih]
    change (liftedRibbonValueFunctor M J).map (actualAtomicHom M X a ha) ≫
      (liftedRibbonValueFunctor M J).map
        (actualReducedHom M p.toPositiveReducedArrow.toReducedArrow) = _
    rw [← Functor.map_comp]
    rfl

theorem liftedRibbonValueData_respects : (liftedRibbonValueData M J).RespectsLcm := by
  intro X a b ha hb hab
  rw [liftedRibbonValueData_word, liftedRibbonValueData_word]
  congr 1
  apply Subtype.ext
  apply Subtype.ext
  exact (chosenLcmLeft_eval M X a b ha hb hab).trans
    (chosenLcmRight_eval M X a b ha hb hab).symm

/-- The value comparison agrees on every actual outside elementary ribbon. -/
theorem tautologicalRibbonValueFunctor_atom (X : RibbonObject M) (a : I) (ha : a ∉ X.indices) :
    (tautologicalRibbonValueFunctor M J).map (actualAtomicHom M X a ha) =
      (liftedRibbonValueFunctor M J).map (actualAtomicHom M X a ha) := by
  apply FamilyGroupoid.Hom.ext
  · rfl
  · intro C
    change HEq (MulOpposite.op (elementaryMu M X.indices a))
      ((intervalRibbonValueFunctor M J).map
        (((ribbonLiftingFunctor M J).map (actualAtomicHom M X a ha)).hom C))
    rw [ribbonLiftingFunctor_atom]
    apply heq_of_eq
    change MulOpposite.op (elementaryMu M X.indices a) =
      MulOpposite.op (((intervalRibbonFunctor M J).map
        (intervalPositive C.val
          (fiberTarget M J (Artin.projection M (elementaryMu M X.indices a))
            (isRibbon_projection_transporter M (elementaryMu_isRibbon M X.indices a)) C).val)).val.val)
    rw [intervalRibbonFunctor_positive, intervalRibbonPositive_value]
    congr 1
    rw [relativeTransport_fiberTarget M J _ _ (elementaryMu_projection_minimal M X.indices a)]
    exact elementaryMu_eq_transporterPositiveLift M X.indices a

/-- The already proved signed presentation forces compatibility for every
actual generated ribbon, including inverse and composite arrows. -/
theorem liftedRibbonValueFunctor_eq :
    liftedRibbonValueFunctor M J = tautologicalRibbonValueFunctor M J := by
  have hF := (liftedRibbonValueData M J).extensionFunctor_unique
    (liftedRibbonValueData_respects M J) (liftedRibbonValueFunctor M J)
    rfl (fun _ _ _ => HEq.rfl)
  have hT := (liftedRibbonValueData M J).extensionFunctor_unique
    (liftedRibbonValueData_respects M J) (tautologicalRibbonValueFunctor M J)
    rfl (fun X a ha => heq_of_eq (tautologicalRibbonValueFunctor_atom M J X a ha))
  exact hF.trans hT.symm

private theorem functor_map_heq {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (h : F = G) {X Y : C} (f : X ⟶ Y) : HEq (F.map f) (G.map f) := by
  subst G
  rfl

/-- The projected coordinate arrow has exactly the original actual Artin value. -/
theorem ribbonLiftArrow_ribbon_value {X Y : ActualReducedRibbonGroupoid M}
    (β : X ⟶ Y) (C : ChamberFiber M J X.val) :
    ((intervalRibbonFunctor M J).map (ribbonLiftArrow M J β C)).val.val = β.val.val := by
  have hm : (liftedRibbonValueFunctor M J).map β =
      (tautologicalRibbonValueFunctor M J).map β :=
    eq_of_heq (functor_map_heq (liftedRibbonValueFunctor_eq M J) β)
  have hc := FamilyGroupoid.coordinate_heq_of_eq hm C
  apply MulOpposite.op_injective
  exact eq_of_heq hc

theorem ribbonObject_of_fiber {X : ActualReducedRibbonGroupoid M}
    (C : ChamberFiber M J X.val) :
    actualRibbonObject M ⟨actualChamberIndices M J C.val⟩ = X := by
  rw [C.property]
  apply Subtype.ext
  cases X.val
  rfl

theorem ribbonLiftSource_eq {X : ActualReducedRibbonGroupoid M}
    (C : ChamberFiber M J X.val) :
    (intervalRibbonFunctor M J).obj (intervalObject C.val) = X :=
  (intervalRibbonFunctor_obj M J C.val).trans (ribbonObject_of_fiber M J C)

private theorem actualRibbonHom_heq_of_value {X Y X' Y' : ActualReducedRibbonGroupoid M}
    (hX : X = X') (hY : Y = Y') {f : X ⟶ Y} {g : X' ⟶ Y'}
    (h : f.val.val = g.val.val) : HEq f g := by
  subst X'
  subst Y'
  apply heq_of_eq
  apply Subtype.ext
  apply Subtype.ext
  exact h

/-- The compatibility as an actual arrow equality with endpoint transports
accounted for by heterogeneous equality. -/
theorem ribbonLiftArrow_ribbon_heq {X Y : ActualReducedRibbonGroupoid M}
    (β : X ⟶ Y) (C : ChamberFiber M J X.val) :
    HEq ((intervalRibbonFunctor M J).map (ribbonLiftArrow M J β C)) β := by
  apply actualRibbonHom_heq_of_value M
    (ribbonLiftSource_eq M J C)
    (ribbonLiftSource_eq M J (ribbonLiftEndpoint M J β C))
  exact ribbonLiftArrow_ribbon_value M J β C

private theorem cast_hom_eq_of_heq {D : Type*} [Category D] {A B A' B' : D}
    (hA : A = A') (hB : B = B') {f : A ⟶ B} {g : A' ⟶ B'} (h : HEq f g) :
    eqToHom hA.symm ≫ f ≫ eqToHom hB = g := by
  subst A'
  subst B'
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using eq_of_heq h

/-- Literal compatibility after the canonical source and target equality casts. -/
theorem ribbonLiftArrow_ribbon_cast {X Y : ActualReducedRibbonGroupoid M}
    (β : X ⟶ Y) (C : ChamberFiber M J X.val) :
    eqToHom (ribbonLiftSource_eq M J C).symm ≫
        (intervalRibbonFunctor M J).map (ribbonLiftArrow M J β C) ≫
        eqToHom (ribbonLiftSource_eq M J (ribbonLiftEndpoint M J β C)) = β :=
  cast_hom_eq_of_heq (ribbonLiftSource_eq M J C)
    (ribbonLiftSource_eq M J (ribbonLiftEndpoint M J β C)) (ribbonLiftArrow_ribbon_heq M J β C)

end ArtinNormalisers.Chamber3
