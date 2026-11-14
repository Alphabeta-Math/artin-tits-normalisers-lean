import ArtinSequences.AllBasepoints

/-!
# Positive traversal conventions on the actual fundamental groups

The source's multiplication in traversal order is implemented by the opposite
of mathlib's genuine fundamental group, not by a replacement path-group model.
Both comparison squares retain the same actual Coxeter quotient. The final
label formula transports the actual standard positive ribbon path along the
projection of the same actual upstairs basepoint path.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Sequence4

open Theorem18 Ribbon2

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- Pure comparison with the actual positive-traversal fundamental group. -/
noncomputable def positivePureEquiv (x : Complement M J) :
    Artin.pureNormalizerImage M J ≃* (FundamentalGroup (Complement M J) x)ᵐᵒᵖ :=
  (pureFundamentalGroupEquiv M J x).trans (MulEquiv.inv' _)

/-- Normalizer comparison with the actual positive-traversal fundamental group. -/
noncomputable def positiveNormalizerEquiv (x : Complement M J) :
    Artin.normalizerQuotient M J ≃*
      (FundamentalGroup (OrbitSpace M J) (orbitProjection M J x))ᵐᵒᵖ :=
  (normalizerFundamentalGroupEquiv M J x).trans (MulEquiv.inv' _)

@[simp] theorem positivePureEquiv_unop (x : Complement M J)
    (a : Artin.pureNormalizerImage M J) :
    (positivePureEquiv M J x a).unop = (pureFundamentalGroupEquiv M J x a)⁻¹ := rfl

@[simp] theorem positiveNormalizerEquiv_unop (x : Complement M J)
    (a : Artin.normalizerQuotient M J) :
    (positiveNormalizerEquiv M J x a).unop =
      (normalizerFundamentalGroupEquiv M J x a)⁻¹ := rfl

/-- The same actual covering map, on opposite fundamental groups. -/
noncomputable def positiveOrbitFundamentalGroupMap (x : Complement M J) :
    (FundamentalGroup (Complement M J) x)ᵐᵒᵖ →*
      (FundamentalGroup (OrbitSpace M J) (orbitProjection M J x))ᵐᵒᵖ :=
  (Landmark1.orbitFundamentalGroupMap M J x).op

omit [Finite M.Group] in
@[simp] theorem positiveOrbitFundamentalGroupMap_unop (x : Complement M J)
    (α : (FundamentalGroup (Complement M J) x)ᵐᵒᵖ) :
    (positiveOrbitFundamentalGroupMap M J x α).unop =
      Landmark1.orbitFundamentalGroupMap M J x α.unop := rfl

/-- Positive traversal endpoint monodromy to the same actual quotient. -/
noncomputable def positiveOrbitMonodromy (x : Complement M J) :
    (FundamentalGroup (OrbitSpace M J) (orbitProjection M J x))ᵐᵒᵖ →*
      Artin.coxeterNormalizerQuotient M J :=
  (normalizedOrbitMonodromy M J x).comp (oppositeInverseEquiv _).toMonoidHom

/-- On the same underlying positive path, the quotient label is exactly the
raw lifted endpoint label, with no inverse or quotient automorphism. -/
@[simp] theorem positiveOrbitMonodromy_op (x : Complement M J)
    (γ : FundamentalGroup (OrbitSpace M J) (orbitProjection M J x)) :
    positiveOrbitMonodromy M J x (MulOpposite.op γ) =
      (Landmark1.orbitMonodromy M J x γ).unop := by
  change normalizedOrbitMonodromy M J x γ⁻¹ = _
  rw [map_inv, normalizedOrbitMonodromy_apply, inv_inv]

@[simp] theorem positiveOrbitMonodromy_apply (x : Complement M J)
    (γ : (FundamentalGroup (OrbitSpace M J) (orbitProjection M J x))ᵐᵒᵖ) :
    positiveOrbitMonodromy M J x γ = (Landmark1.orbitMonodromy M J x γ.unop).unop :=
  positiveOrbitMonodromy_op M J x γ.unop

/-- The first actual positive-convention square at every basepoint. -/
theorem positivePureEquiv_inclusion (x : Complement M J) :
    (positiveOrbitFundamentalGroupMap M J x).comp (positivePureEquiv M J x).toMonoidHom =
      (positiveNormalizerEquiv M J x).toMonoidHom.comp
        (Artin.pureNormalizerInclusion M J) := by
  apply MonoidHom.ext
  intro a
  apply MulOpposite.unop_injective
  change Landmark1.orbitFundamentalGroupMap M J x
      (pureFundamentalGroupEquiv M J x a)⁻¹ =
    (normalizerFundamentalGroupEquiv M J x (Artin.pureNormalizerInclusion M J a))⁻¹
  rw [map_inv]
  exact congrArg Inv.inv (DFunLike.congr_fun (pureFundamentalGroupEquiv_inclusion M J x) a)

/-- The right actual positive-convention square has identity on the same Q. -/
theorem positiveNormalizerEquiv_monodromy (x : Complement M J) :
    (positiveOrbitMonodromy M J x).comp (positiveNormalizerEquiv M J x).toMonoidHom =
      Artin.normalizerQuotientMap M J := by
  apply MonoidHom.ext
  intro a
  change normalizedOrbitMonodromy M J x (normalizerFundamentalGroupEquiv M J x a)⁻¹⁻¹ = _
  rw [inv_inv]
  exact DFunLike.congr_fun (normalizerFundamentalGroupEquiv_monodromy M J x) a

/-- Short exactness of the actual positive-traversal geometric row. -/
theorem positiveOrbitFundamentalGroup_shortExact (x : Complement M J) :
    Function.Injective (positiveOrbitFundamentalGroupMap M J x) ∧
      (positiveOrbitFundamentalGroupMap M J x).range = (positiveOrbitMonodromy M J x).ker ∧
      Function.Surjective (positiveOrbitMonodromy M J x) := by
  obtain ⟨hinj, hrange, hsurj⟩ := Landmark1.orbitFundamentalGroup_shortExact M J x
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    apply MulOpposite.unop_injective
    exact hinj (congrArg MulOpposite.unop hab)
  · ext β
    have hmem : β ∈ (positiveOrbitFundamentalGroupMap M J x).range ↔
        β.unop ∈ (Landmark1.orbitFundamentalGroupMap M J x).range := by
      constructor
      · rintro ⟨α, hα⟩
        exact ⟨α.unop, congrArg MulOpposite.unop hα⟩
      · rintro ⟨α, hα⟩
        exact ⟨MulOpposite.op α, MulOpposite.unop_injective hα⟩
    rw [hmem, hrange]
    simp only [MonoidHom.mem_ker, positiveOrbitMonodromy_apply]
    exact ⟨fun h => congrArg MulOpposite.unop h,
      fun h => MulOpposite.unop_injective h⟩
  · intro q
    obtain ⟨γ, hγ⟩ := hsurj (MulOpposite.op q)
    refine ⟨MulOpposite.op γ, ?_⟩
    rw [positiveOrbitMonodromy_op, hγ]
    rfl

/-- The actual positive ribbon path comparison at every basepoint. Its
underlying path class is the standard positive Artin-labelled ribbon image,
transported along the projection of the same actual upstairs basepoint path. -/
theorem positiveNormalizerEquiv_label (x : Complement M J)
    (r : reducedRibbonLoops M (⟨J⟩ : RibbonObject M)) :
    (positiveNormalizerEquiv M J x (reducedRibbonNormalizerQuotientEquiv M ⟨J⟩ r)).unop =
      FundamentalGroup.fundamentalGroupMulEquivOfPath
        (projectedBasepointPath M J (standardBasepointPath M J x))
        (standardRibbonVertexEquiv M J (componentEndOfLoop M J r)) := by
  change (FundamentalGroup.fundamentalGroupMulEquivOfPath
    (projectedBasepointPath M J (standardBasepointPath M J x))
    (standardNormalizerEquiv M J (reducedRibbonNormalizerQuotientEquiv M ⟨J⟩ r)))⁻¹ = _
  rw [← map_inv]
  exact congrArg (FundamentalGroup.fundamentalGroupMulEquivOfPath
    (projectedBasepointPath M J (standardBasepointPath M J x)))
    (standardPositiveNormalizerEquiv_label M J r)

end ArtinNormalisers.Sequence4
