import ArtinSequences.RibbonVertex
import ArtinSequences.VertexComparison
import ArtinSequences.EndpointMonodromy
import ArtinRibbons.CoxeterProjection

/-!
# The actual normalizer comparison at the standard chamber point

The basepoint identification comes from the strictly commuting actual square.
The positive-label comparison lands in the opposite of mathlib's fundamental
group. The ordinary fundamental-group comparison consequently uses inverse
ribbon labels. Its compatibility with endpoint monodromy is proved separately.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Sequence4

open CategoryTheory Chamber3 Ribbon2 Theorem18

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- The actual real point in the standard restricted chamber. -/
noncomputable def standardComplementPoint : Complement M J :=
  actualChamberBasepoint M J (actualChamberPointFamily M J) (standardActualChamber M J)

/-- The actual bottom functor's basepoint equality is supplied by the strict
covering square, with no unrelated path or counit choice. -/
theorem standardRibbonImage_eq :
    (actualRibbonOrbitEquivalence M J).functor.obj (standardComponentRibbonObject M J) =
      FundamentalGroupoid.mk (orbitProjection M J (standardComplementPoint M J)) := by
  exact Functor.congr_obj (actualComparison_square M J)
    (intervalObject (standardActualChamber M J))

/-- The actual reduced ribbon vertex maps to the actual orbit-space fundamental
group at precisely the standard chamber image. -/
noncomputable def standardRibbonVertexEquiv :
    End (standardComponentRibbonObject M J) ≃*
      FundamentalGroup (OrbitSpace M J) (orbitProjection M J (standardComplementPoint M J)) :=
  basedEndEquiv (actualRibbonOrbitEquivalence M J).functor
    (actualRibbonOrbitEquivalence M J).fullyFaithfulFunctor
    (standardComponentRibbonObject M J) (standardRibbonImage_eq M J)

theorem standardRibbonVertexEquiv_asHom (e : End (standardComponentRibbonObject M J)) :
    (standardRibbonVertexEquiv M J e).asHom =
      eqToHom (standardRibbonImage_eq M J).symm ≫
        (actualRibbonOrbitEquivalence M J).functor.map e.asHom ≫
          eqToHom (standardRibbonImage_eq M J) := rfl

/-- Ordinary mathlib fundamental-group multiplication requires inverse labels. -/
noncomputable def standardReducedRibbonEquiv :
    reducedRibbonLoops M (⟨J⟩ : RibbonObject M) ≃*
      FundamentalGroup (OrbitSpace M J) (orbitProjection M J (standardComplementPoint M J)) :=
  (reducedLoopsEquivComponentEnd M J).trans (standardRibbonVertexEquiv M J)

/-- The actual M2 normalizer isomorphism followed by the actual M3 geometric
functor, including the explicit inverse-label convention. -/
noncomputable def standardNormalizerEquiv :
    Artin.normalizerQuotient M J ≃*
      FundamentalGroup (OrbitSpace M J) (orbitProjection M J (standardComplementPoint M J)) :=
  (reducedRibbonNormalizerQuotientEquiv M ⟨J⟩).symm.trans (standardReducedRibbonEquiv M J)

/-- In the positive traversal convention the target is explicitly opposite. -/
noncomputable def standardPositiveNormalizerEquiv :
    Artin.normalizerQuotient M J ≃*
      (FundamentalGroup (OrbitSpace M J)
        (orbitProjection M J (standardComplementPoint M J)))ᵐᵒᵖ :=
  (standardNormalizerEquiv M J).trans (MulEquiv.inv' _)

/-- The positive comparison carries the original, rather than inverse, actual
ribbon label through the specified bottom geometric functor. -/
theorem standardPositiveNormalizerEquiv_label
    (r : reducedRibbonLoops M (⟨J⟩ : RibbonObject M)) :
    (standardPositiveNormalizerEquiv M J (reducedRibbonNormalizerQuotientEquiv M ⟨J⟩ r)).unop =
      standardRibbonVertexEquiv M J (componentEndOfLoop M J r) := by
  change (standardNormalizerEquiv M J
    (reducedRibbonNormalizerQuotientEquiv M ⟨J⟩ r))⁻¹ = _
  change (standardReducedRibbonEquiv M J
    ((reducedRibbonNormalizerQuotientEquiv M ⟨J⟩).symm
      (reducedRibbonNormalizerQuotientEquiv M ⟨J⟩ r)))⁻¹ = _
  rw [MulEquiv.symm_apply_apply, ← map_inv]
  change standardRibbonVertexEquiv M J ((reducedLoopsEquivComponentEnd M J) r⁻¹) = _
  congr 1
  apply componentEndValue_injective M J
  simp only [componentEndValue, reducedLoopsEquivComponentEnd_asHom_value,
    Subgroup.coe_inv, inv_inv, componentEndOfLoop_asHom_value]

end ArtinNormalisers.Sequence4
