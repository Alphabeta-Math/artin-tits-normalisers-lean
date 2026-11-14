import ArtinChambers.RibbonLiftCompatibility
import ArtinRibbons.CoxeterProjection

/-!
# Actual signed Coxeter endpoint and deck labels

A second genuine value-family functor uses the explicit fiber equivalence
of the actual Coxeter projection. The signed universal property identifies
it with the constructed lift. At the actual standard chamber this gives
the existing normalizer-quotient projection as the exact loop endpoint label.
No based fundamental-group or exact-sequence comparison is asserted here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ArtinNormalisers.Chamber3

open CategoryTheory Ribbon2 Theorem18

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- Explicit Coxeter-projection index transport and original Artin values
form a genuine functor on all actual signed reduced ribbon arrows. -/
noncomputable def projectedRibbonValueFunctor : ActualReducedRibbonGroupoid M ⥤
    FamilyGroupoid (SingleObj (Artin.Group M)ᵐᵒᵖ) where
  obj := (liftedRibbonValueFunctor M J).obj
  map β :=
    { equiv := fiberEquiv M J (Artin.projection M β.val.val)
        (isRibbon_projection_transporter M β.val.property)
      hom _ := MulOpposite.op β.val.val }
  map_id X := by
    apply FamilyGroupoid.Hom.ext
    · apply Equiv.ext
      intro C
      change fiberTarget M J (Artin.projection M 1) _ C = C
      simpa only [map_one] using fiberTarget_one M J _ C
    · intro C
      rfl
  map_comp β γ := by
    apply FamilyGroupoid.Hom.ext
    · apply Equiv.ext
      intro C
      change fiberTarget M J (Artin.projection M (β.val.val * γ.val.val)) _ C =
        fiberTarget M J (Artin.projection M γ.val.val) _
          (fiberTarget M J (Artin.projection M β.val.val) _ C)
      symm
      simpa only [map_mul] using fiberTarget_comp M J
        (Artin.projection M β.val.val) (Artin.projection M γ.val.val)
        (isRibbon_projection_transporter M β.val.property)
        (isRibbon_projection_transporter M γ.val.property) C
    · intro C
      rfl

theorem projectedRibbonValueFunctor_atom (X : RibbonObject M) (a : I) (ha : a ∉ X.indices) :
    (projectedRibbonValueFunctor M J).map (actualAtomicHom M X a ha) =
      (liftedRibbonValueFunctor M J).map (actualAtomicHom M X a ha) := by
  calc
    _ = (tautologicalRibbonValueFunctor M J).map (actualAtomicHom M X a ha) := by
      apply FamilyGroupoid.Hom.ext
      · change fiberEquiv M J (Artin.projection M (elementaryMu M X.indices a)) _ =
          ((ribbonLiftingFunctor M J).map (actualAtomicHom M X a ha)).equiv
        rw [ribbonLiftingFunctor_atom]
        rfl
      · intro C
        rfl
    _ = _ := tautologicalRibbonValueFunctor_atom M J X a ha

/-- The all-signed presentation identifies the explicit projection-based
functor with the constructed lift-value functor. -/
theorem liftedRibbonValueFunctor_eq_projected :
    liftedRibbonValueFunctor M J = projectedRibbonValueFunctor M J := by
  have hF := (liftedRibbonValueData M J).extensionFunctor_unique
    (liftedRibbonValueData_respects M J) (liftedRibbonValueFunctor M J)
    rfl (fun _ _ _ => HEq.rfl)
  have hP := (liftedRibbonValueData M J).extensionFunctor_unique
    (liftedRibbonValueData_respects M J) (projectedRibbonValueFunctor M J)
    rfl (fun X a ha => heq_of_eq (projectedRibbonValueFunctor_atom M J X a ha))
  exact hF.trans hP.symm

private theorem functor_map_heq {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (h : F = G) {X Y : C} (f : X ⟶ Y) : HEq (F.map f) (G.map f) := by
  subst G
  rfl

/-- The index bijection of every signed actual ribbon lift is precisely
the equivalence induced by its actual Artin--Coxeter projection. -/
theorem ribbonLiftingFunctor_index_projection {X Y : ActualReducedRibbonGroupoid M}
    (β : X ⟶ Y) :
    ((ribbonLiftingFunctor M J).map β).equiv =
      fiberEquiv M J (Artin.projection M β.val.val)
        (isRibbon_projection_transporter M β.val.property) := by
  have hm : (liftedRibbonValueFunctor M J).map β =
      (projectedRibbonValueFunctor M J).map β :=
    eq_of_heq (functor_map_heq (liftedRibbonValueFunctor_eq_projected M J) β)
  exact FamilyGroupoid.equiv_eq_of_eq hm

/-- Exact signed endpoint transport, in the literal chamber-fiber subtype. -/
theorem ribbonLiftEndpoint_projection {X Y : ActualReducedRibbonGroupoid M}
    (β : X ⟶ Y) (C : ChamberFiber M J X.val) :
    ribbonLiftEndpoint M J β C =
      fiberTarget M J (Artin.projection M β.val.val)
        (isRibbon_projection_transporter M β.val.property) C :=
  congrArg (fun e => e C) (ribbonLiftingFunctor_index_projection M J β)

/-- The actual standard raw label `(1,J)`, with no normalizer choice. -/
noncomputable def standardRawFacetLabel : RawFacetLabel M J where
  indices := J
  representative := 1
  parabolic_conjugacy := by
    ext g
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
    simp

/-- The actual standard chamber in the existing relative arrangement. -/
noncomputable def standardActualChamber : ActualChamber M J :=
  actualChamberOfRawLabel M J (standardRawFacetLabel M J)

@[simp] theorem standardActualChamber_indices :
    actualChamberIndices M J (standardActualChamber M J) = J :=
  actualChamberIndices_rawLabel M J (standardRawFacetLabel M J)

noncomputable def standardActualChamberFiber : ChamberFiber M J (⟨J⟩ : RibbonObject M) :=
  ⟨standardActualChamber M J, standardActualChamber_indices M J⟩

/-- The lifted endpoint of an actual reduced ribbon loop is given by the
same existing Coxeter normalizer-quotient projection of its actual Artin label. -/
theorem ribbonLiftEndpoint_reducedLoop (r : reducedRibbonLoops M (⟨J⟩ : RibbonObject M)) :
    (ribbonLiftEndpoint M J (actualReducedHom M r.property) (standardActualChamberFiber M J)).val =
      reducedRibbonCoxeterProjection M ⟨J⟩ r • standardActualChamber M J := by
  rw [ribbonLiftEndpoint_projection]
  let L := standardRawFacetLabel M J
  let w : CoxeterNormalizer M J := reducedRibbonCoxeterNormalizerMap M ⟨J⟩ r
  have hw := isRibbon_projection_transporter M r.property.isRibbon
  have hchosen : actualChamberOfRawLabel M J
      (chamberRawLabel M J (standardActualChamber M J)) = actualChamberOfRawLabel M J L :=
    chamberRawLabel_chamber M J _
  have hreplace := rightTransportRawLabel_independent M J hchosen J (Artin.projection M r.val)
    (by simpa only [chamberRawLabel_indices, standardActualChamber_indices] using hw) hw
  change actualChamberOfRawLabel M J
      (fiberTargetLabel M J (Artin.projection M r.val) hw (standardActualChamberFiber M J)) =
    transportedChamber M J w (actualChamberOfRawLabel M J L)
  rw [transportedChamber_rawLabel]
  refine hreplace.trans ?_
  apply (actualChamberOfRawLabel_eq_iff M J _ _).mpr
  refine ⟨rfl, ?_⟩
  change ((1 : M.Group) * Artin.projection M r.val)⁻¹ * (w.val * 1) ∈
    Artin.coxeterParabolic M J
  have hwval : w.val = Artin.projection M r.val := rfl
  rw [hwval, one_mul, mul_one, inv_mul_cancel]
  exact Subgroup.one_mem _

/-- The same endpoint assertion directly for every actual signed loop arrow
at the original ribbon object `J`. -/
theorem ribbonLiftEndpoint_loopArrow
    (β : actualRibbonObject M (⟨J⟩ : RibbonObject M) ⟶ actualRibbonObject M ⟨J⟩) :
    (ribbonLiftEndpoint M J β (standardActualChamberFiber M J)).val =
      reducedRibbonCoxeterProjection M ⟨J⟩ ⟨β.val.val, β.property⟩ •
        standardActualChamber M J :=
  ribbonLiftEndpoint_reducedLoop M J ⟨β.val.val, β.property⟩

end ArtinNormalisers.Chamber3
