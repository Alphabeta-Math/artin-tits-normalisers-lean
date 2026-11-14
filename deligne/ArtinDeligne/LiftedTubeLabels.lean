import ArtinDeligne.LiftedTubes
import ArtinDeligne.IncomingOrder
import ArtinDeligne.SimpleTransport
import ArtinChambers.ActualComparison

/-!
# Actual path labels of the lifted chamber tubes

The universal-cover fiber consists of actual path-homotopy classes from the
fixed standard complement point. The actual fully faithful interval/complement
functor and the actual ribbon covering identify these with signed incoming
ribbon vertices. An outgoing path has the inverse of the incoming Artin label;
categorical composition, rather than an opposite fundamental-group convention,
controls all formulas here.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

noncomputable section

namespace ArtinNormalisers.Deligne5

open CategoryTheory Ribbon2 Homotopy5 Chamber3 Theorem18 Sequence4 Asphericity5

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group]

namespace IncomingVertex

/-- Transport only the fixed actual target object, preserving the actual label. -/
def rebaseEquiv {B C : RibbonObject M} (h : B = C) : IncomingVertex M B ≃ IncomingVertex M C where
  toFun u := ⟨u.source, u.value, h ▸ u.reduced⟩
  invFun u := ⟨u.source, u.value, h.symm ▸ u.reduced⟩
  left_inv _ := ext_value rfl
  right_inv _ := ext_value rfl

/-- Invert actual signed ribbons to give outgoing arrows in the pre-existing
actual reduced ribbon groupoid. No paths or vertex groups are replaced. -/
def outgoingEquiv (B : ActualReducedRibbonGroupoid M) :
    IncomingVertex M B.val ≃ Outgoing (ActualReducedRibbonGroupoid M) B where
  toFun u := ⟨actualRibbonObject M u.source,
    ⟨⟨u.value⁻¹, u.reduced.isRibbon.inv M⟩, .inverse u.reduced⟩⟩
  invFun p := ⟨p.1.val, p.2.val.val⁻¹, .inverse p.2.property⟩
  left_inv u := ext_value (inv_inv u.value)
  right_inv := by
    rintro ⟨⟨X, hX⟩, ⟨⟨p, hp⟩, hr⟩⟩
    dsimp only
    refine Sigma.ext (Subtype.ext rfl) ?_
    apply heq_of_eq
    apply Subtype.ext
    exact Subtype.ext (inv_inv p)

end IncomingVertex

variable (J : Set I)

@[simp] theorem tubeBasepoint_standard :
    tubeBasepoint M J (standardActualChamber M J) = standardComplementPoint M J := rfl

/-- The actual universal-cover index as its chamber and original path class. -/
def liftedTubePathEquiv : LiftedTubeIndex M J ≃
    Σ C : ActualChamber M J,
      Path.Homotopic.Quotient (standardComplementPoint M J) (tubeBasepoint M J C) where
  toFun A := ⟨A.chamber, liftedTubePathClass M J A⟩
  invFun p := ⟨p.1, (universalCoverFiberEquivPathClasses
    (standardComplementPoint M J) (tubeBasepoint M J p.1)).symm p.2⟩
  left_inv := by
    rintro ⟨C, e⟩
    change (⟨C, (universalCoverFiberEquivPathClasses _ _).symm
      ((universalCoverFiberEquivPathClasses _ _) e)⟩ : LiftedTubeIndex M J) = ⟨C, e⟩
    rw [Equiv.symm_apply_apply]
  right_inv := by
    rintro ⟨C, q⟩
    apply Sigma.ext rfl
    exact heq_of_eq ((universalCoverFiberEquivPathClasses _ _).apply_symm_apply q)

/-- Actual geometric path classes are actual interval arrows via the proved
fully faithful functor, at the literal canonical chamber basepoints. -/
def rootedPathIntervalEquiv :
    (Σ C : ActualChamber M J,
      Path.Homotopic.Quotient (standardComplementPoint M J) (tubeBasepoint M J C)) ≃
    Σ C : ActualChamber M J,
      intervalObject (standardActualChamber M J) ⟶ intervalObject C :=
  Equiv.sigmaCongrRight fun C =>
    ((actualIntervalComplementEquivalence M J).fullyFaithfulFunctor.homEquiv
      (X := intervalObject (standardActualChamber M J)) (Y := intervalObject C)).symm

def chamberIntervalObjectEquiv : ActualChamber M J ≃
    IntervalGroupoid (E := relativeSubspace J) (actualForms M J) where
  toFun := intervalObject
  invFun := intervalChamber
  left_inv := intervalChamber_intervalObject
  right_inv := intervalObject_intervalChamber

def rootedIntervalOutgoingEquiv :
    (Σ C : ActualChamber M J,
      intervalObject (standardActualChamber M J) ⟶ intervalObject C) ≃
    Outgoing (IntervalGroupoid (E := relativeSubspace J) (actualForms M J))
      (intervalObject (standardActualChamber M J)) :=
  Equiv.sigmaCongrLeft (chamberIntervalObjectEquiv M J)

theorem standardRibbonObject_indices :
    ((intervalRibbonFunctor M J).obj (intervalObject (standardActualChamber M J))).val =
      (⟨J⟩ : RibbonObject M) := by
  change (⟨actualChamberIndices M J (standardActualChamber M J)⟩ : RibbonObject M) = ⟨J⟩
  rw [standardActualChamber_indices]

/-- The actual unique outgoing lift identifies the fixed-root incoming labels. -/
def rootedRibbonIncomingEquiv :
    Outgoing (IntervalGroupoid (E := relativeSubspace J) (actualForms M J))
      (intervalObject (standardActualChamber M J)) ≃ IncomingVertex M (⟨J⟩ : RibbonObject M) :=
  (Chamber3.outgoingEquiv (intervalRibbonFunctor M J) (intervalRibbonFunctor_isCovering M J)
    (intervalObject (standardActualChamber M J))).trans
      ((IncomingVertex.outgoingEquiv M _).symm.trans
        (IncomingVertex.rebaseEquiv M (standardRibbonObject_indices M J)))

/-- Genuine open-sheet indices and actual signed incoming ribbon vertices. -/
def liftedTubeIndexEquivIncoming : LiftedTubeIndex M J ≃
    IncomingVertex M (⟨J⟩ : RibbonObject M) :=
  (((liftedTubePathEquiv M J).trans (rootedPathIntervalEquiv M J)).trans
    (rootedIntervalOutgoingEquiv M J)).trans (rootedRibbonIncomingEquiv M J)

/-- The actual interval arrow represented by an actual sheet's original path. -/
def liftedTubeIntervalArrow (A : LiftedTubeIndex M J) :
    intervalObject (standardActualChamber M J) ⟶ intervalObject A.chamber :=
  (actualIntervalComplementEquivalence M J).fullyFaithfulFunctor.preimage
    (liftedTubePathClass M J A)

@[simp] theorem map_liftedTubeIntervalArrow (A : LiftedTubeIndex M J) :
    (actualIntervalForward M J).map (liftedTubeIntervalArrow M J A) = liftedTubePathClass M J A :=
  (actualIntervalComplementEquivalence M J).fullyFaithfulFunctor.map_preimage _

@[simp] theorem rootedRibbonIncomingEquiv_value (C : ActualChamber M J)
    (δ : intervalObject (standardActualChamber M J) ⟶ intervalObject C) :
    (rootedRibbonIncomingEquiv M J ⟨intervalObject C, δ⟩).value =
      ((intervalRibbonFunctor M J).map δ).val.val⁻¹ := rfl

@[simp] theorem rootedRibbonIncomingEquiv_source (C : ActualChamber M J)
    (δ : intervalObject (standardActualChamber M J) ⟶ intervalObject C) :
    (rootedRibbonIncomingEquiv M J ⟨intervalObject C, δ⟩).source =
      (⟨actualChamberIndices M J C⟩ : RibbonObject M) := rfl

@[simp] theorem liftedTubeIndexEquivIncoming_value (A : LiftedTubeIndex M J) :
    (liftedTubeIndexEquivIncoming M J A).value =
      ((intervalRibbonFunctor M J).map (liftedTubeIntervalArrow M J A)).val.val⁻¹ := rfl

@[simp] theorem liftedTubeIndexEquivIncoming_source (A : LiftedTubeIndex M J) :
    (liftedTubeIndexEquivIncoming M J A).source =
      (⟨actualChamberIndices M J A.chamber⟩ : RibbonObject M) := rfl

private theorem incoming_chamber_of_interval_map (C : ActualChamber M J)
    (δ : intervalObject (standardActualChamber M J) ⟶ intervalObject C)
    (β : (intervalRibbonFunctor M J).obj (intervalObject (standardActualChamber M J)) ⟶
      (intervalRibbonFunctor M J).obj (intervalObject C))
    (hβ : (intervalRibbonFunctor M J).map δ = β)
    (u : IncomingVertex M (⟨J⟩ : RibbonObject M))
    (hus : u.source = (⟨actualChamberIndices M J C⟩ : RibbonObject M))
    (huv : u.value = β.val.val⁻¹) : u.chamber = C := by
  let w := Artin.projection M β.val.val
  have hrib : IsRibbon M ⟨actualChamberIndices M J (standardActualChamber M J)⟩
      ⟨actualChamberIndices M J C⟩ β.val.val := β.val.property
  have hw := isRibbon_projection_transporter M hrib
  have hwJ : (Artin.coxeterParabolic M (actualChamberIndices M J C)).map
      (MulAut.conj w).toMonoidHom = Artin.coxeterParabolic M J := by
    simpa only [standardActualChamber_indices] using hw
  have hchosen : actualChamberOfRawLabel M J
      (chamberRawLabel M J (standardActualChamber M J)) =
        actualChamberOfRawLabel M J (standardRawFacetLabel M J) :=
    chamberRawLabel_chamber M J _
  have hreplace := rightTransportRawLabel_independent M J hchosen
    (actualChamberIndices M J C) w
    (by simpa only [chamberRawLabel_indices] using hw)
    hwJ
  have hend := congrArg Subtype.val (ribbonLiftInterval_endpoint_all M J δ)
  rw [hβ, ribbonLiftEndpoint_projection] at hend
  change actualChamberOfRawLabel M J
    (fiberTargetLabel M J
      (X := ⟨actualChamberIndices M J (standardActualChamber M J)⟩)
      (Y := ⟨actualChamberIndices M J C⟩) w hw (distinguishedRibbonIndex M J
      (intervalObject (standardActualChamber M J)))) = C at hend
  have hlabel : u.rawFacetLabel =
      rightTransportRawLabel M J (standardRawFacetLabel M J)
        (actualChamberIndices M J C) w hwJ := by
    apply rawFacetLabel_ext M J
    · change u.source.indices = _
      rw [hus]
      rfl
    · change (Artin.projection M u.value)⁻¹ = 1 * w
      rw [huv, map_inv, inv_inv, one_mul]
  change actualChamberOfRawLabel M J u.rawFacetLabel = C
  rw [hlabel]
  exact hreplace.symm.trans hend

/-- The signed endpoint formula identifies the incoming vertex's actual
chamber with the original tube chamber. -/
theorem rootedRibbonIncomingEquiv_chamber (C : ActualChamber M J)
    (δ : intervalObject (standardActualChamber M J) ⟶ intervalObject C) :
    (rootedRibbonIncomingEquiv M J ⟨intervalObject C, δ⟩).chamber = C :=
  incoming_chamber_of_interval_map M J C δ ((intervalRibbonFunctor M J).map δ) rfl
    (rootedRibbonIncomingEquiv M J ⟨intervalObject C, δ⟩)
    (rootedRibbonIncomingEquiv_source M J C δ) (rootedRibbonIncomingEquiv_value M J C δ)

@[simp] theorem liftedTubeIndexEquivIncoming_chamber (A : LiftedTubeIndex M J) :
    (liftedTubeIndexEquivIncoming M J A).chamber = A.chamber :=
  rootedRibbonIncomingEquiv_chamber M J A.chamber (liftedTubeIntervalArrow M J A)

/-- The actual sheet index associated to an incoming vertex. -/
def incomingLiftedTubeIndex (u : IncomingVertex M (⟨J⟩ : RibbonObject M)) : LiftedTubeIndex M J :=
  (liftedTubeIndexEquivIncoming M J).symm u

@[simp] theorem incomingLiftedTubeIndex_chamber
    (u : IncomingVertex M (⟨J⟩ : RibbonObject M)) :
    (incomingLiftedTubeIndex M J u).chamber = u.chamber := by
  have h := liftedTubeIndexEquivIncoming_chamber M J (incomingLiftedTubeIndex M J u)
  simpa only [incomingLiftedTubeIndex, Equiv.apply_symm_apply] using h.symm

/-- These are the original open sheets, merely labelled by their actual ribbons. -/
def incomingLiftedTubeSheet (u : IncomingVertex M (⟨J⟩ : RibbonObject M)) :
    Set (ComplementUniversalCover M J) := liftedTubeSheet M J (incomingLiftedTubeIndex M J u)

theorem incomingLiftedTubeSheet_subset_projection_preimage
    (u : IncomingVertex M (⟨J⟩ : RibbonObject M)) :
    incomingLiftedTubeSheet M J u ⊆
      complementUniversalCoverProjection M J ⁻¹' actualTubeSet M J u.chamber := by
  simpa only [incomingLiftedTubeSheet, incomingLiftedTubeIndex_chamber] using
    liftedTubeSheet_subset_projection_preimage M J (incomingLiftedTubeIndex M J u)

/-- Actual universal-cover fiber transport by composition of the original
path classes. The endpoint is the specified actual canonical chamber point. -/
def transportLiftedTubeIndex (A : LiftedTubeIndex M J) (D : ActualChamber M J)
    (γ : Path.Homotopic.Quotient (tubeBasepoint M J A.chamber) (tubeBasepoint M J D)) :
    LiftedTubeIndex M J :=
  (liftedTubePathEquiv M J).symm ⟨D, (liftedTubePathClass M J A).trans γ⟩

/-- Equality of the actual transported fiber point is exactly the literal
path-composition equation, with no independently chosen path labels. -/
theorem transportLiftedTubeIndex_eq_iff (A B : LiftedTubeIndex M J)
    (γ : Path.Homotopic.Quotient (tubeBasepoint M J A.chamber) (tubeBasepoint M J B.chamber)) :
    transportLiftedTubeIndex M J A B.chamber γ = B ↔
      (liftedTubePathClass M J A).trans γ = liftedTubePathClass M J B := by
  constructor
  · intro h
    have he := congrArg (liftedTubePathEquiv M J) h
    rw [transportLiftedTubeIndex, Equiv.apply_symm_apply] at he
    exact eq_of_heq (Sigma.mk.inj he).2
  · intro h
    apply (liftedTubePathEquiv M J).injective
    rw [transportLiftedTubeIndex, Equiv.apply_symm_apply]
    exact Sigma.ext rfl (heq_of_eq h)

/-- The exact pair gauge, for every signed interval arrow. Outgoing paths
have inverse incoming labels, giving `p_A = label(δ) * p_B` in traversal order. -/
theorem liftedTubePathClass_comp_iff (A B : LiftedTubeIndex M J)
    (δ : intervalObject A.chamber ⟶ intervalObject B.chamber) :
    (show FundamentalGroupoid.mk (standardComplementPoint M J) ⟶
        FundamentalGroupoid.mk (tubeBasepoint M J B.chamber) from
      liftedTubePathClass M J A ≫ (actualIntervalForward M J).map δ) =
        liftedTubePathClass M J B ↔
      (liftedTubeIndexEquivIncoming M J A).value =
        ((intervalRibbonFunctor M J).map δ).val.val *
          (liftedTubeIndexEquivIncoming M J B).value := by
  rw [liftedTubeIndexEquivIncoming_value, liftedTubeIndexEquivIncoming_value]
  constructor
  · intro h
    have hδ : liftedTubeIntervalArrow M J A ≫ δ = liftedTubeIntervalArrow M J B := by
      apply (actualIntervalComplementEquivalence M J).fullyFaithfulFunctor.map_injective
      rw [actualIntervalComplementEquivalence_functor, Functor.map_comp,
        map_liftedTubeIntervalArrow, map_liftedTubeIntervalArrow]
      exact h
    have hv := congrArg (fun k : intervalObject (standardActualChamber M J) ⟶
      intervalObject B.chamber => ((intervalRibbonFunctor M J).map k).val.val) hδ
    rw [Functor.map_comp] at hv
    change ((intervalRibbonFunctor M J).map (liftedTubeIntervalArrow M J A)).val.val *
      ((intervalRibbonFunctor M J).map δ).val.val =
        ((intervalRibbonFunctor M J).map (liftedTubeIntervalArrow M J B)).val.val at hv
    rw [← hv]
    group
  · intro h
    have hv := congrArg Inv.inv h
    simp only [inv_inv, mul_inv_rev] at hv
    have hδ : liftedTubeIntervalArrow M J A ≫ δ = liftedTubeIntervalArrow M J B := by
      apply (intervalRibbonFunctor_isCovering M J).faithful.map_injective
      apply Subtype.ext
      apply Subtype.ext
      rw [Functor.map_comp]
      change ((intervalRibbonFunctor M J).map (liftedTubeIntervalArrow M J A)).val.val *
        ((intervalRibbonFunctor M J).map δ).val.val =
          ((intervalRibbonFunctor M J).map (liftedTubeIntervalArrow M J B)).val.val
      rw [hv]
      group
    rw [← map_liftedTubeIntervalArrow M J A, ← map_liftedTubeIntervalArrow M J B,
      ← Functor.map_comp, hδ]

/-- An actual simple positive incoming factor is precisely the canonical
positive chamber connector in the literal universal-cover path gauge. -/
theorem liftedTubePathClass_comp_positive (A B : LiftedTubeIndex M J)
    (hs : SimpleRibbon M (liftedTubeIndexEquivIncoming M J A).source
      (liftedTubeIndexEquivIncoming M J B).source
      ((liftedTubeIndexEquivIncoming M J A).difference (liftedTubeIndexEquivIncoming M J B))) :
    (show FundamentalGroupoid.mk (standardComplementPoint M J) ⟶
        FundamentalGroupoid.mk (tubeBasepoint M J B.chamber) from
      liftedTubePathClass M J A ≫
        (actualIntervalForward M J).map (intervalPositive A.chamber B.chamber)) =
      liftedTubePathClass M J B := by
  have hr := incoming_relativeTransport M hs
  rw [liftedTubeIndexEquivIncoming_chamber, liftedTubeIndexEquivIncoming_chamber] at hr
  have hv : ((intervalRibbonFunctor M J).map (intervalPositive A.chamber B.chamber)).val.val =
      (liftedTubeIndexEquivIncoming M J A).difference (liftedTubeIndexEquivIncoming M J B) := by
    rw [intervalRibbonFunctor_positive, intervalRibbonPositive_value, hr]
    exact (SimpleRibbon.eq_simpleLift M hs).symm
  apply (liftedTubePathClass_comp_iff M J A B (intervalPositive A.chamber B.chamber)).mpr
  rw [hv]
  dsimp only [IncomingVertex.difference]
  group

theorem transportLiftedTubeIndex_positive (A B : LiftedTubeIndex M J)
    (hs : SimpleRibbon M (liftedTubeIndexEquivIncoming M J A).source
      (liftedTubeIndexEquivIncoming M J B).source
      ((liftedTubeIndexEquivIncoming M J A).difference (liftedTubeIndexEquivIncoming M J B))) :
    transportLiftedTubeIndex M J A B.chamber
      ((actualIntervalForward M J).map (intervalPositive A.chamber B.chamber)) = B :=
  (transportLiftedTubeIndex_eq_iff M J A B _).mpr (liftedTubePathClass_comp_positive M J A B hs)

end ArtinNormalisers.Deligne5
