module

public import Mathlib.Topology.Homotopy.Lifting
public import Mathlib.Algebra.Group.Equiv.Opposite
public import ArtinLandmarks.Covering

/-!
# Actual lifted endpoints determine quotient-cover monodromy

The endpoint assertion is proved using mathlib's actual lifting monodromy,
not an abstract deck-label comparison. Inverse-opposite normalization is
explicit and leaves kernels unchanged.
-/

@[expose] public section

namespace ArtinNormalisers.Sequence4

open CategoryTheory

variable {E X Q : Type*} [TopologicalSpace E] [TopologicalSpace X]
  [Group Q] [MulAction Q E] {p : E → X}

/-- Any actual path class projecting to the specified based loop computes
its raw endpoint monodromy, with the literal quotient action at its endpoint. -/
theorem endpointMonodromy_eq_of_path_map_heq
    (hp : IsQuotientCoveringMap p Q) (e : E) (q : Q)
    (γ : Path.Homotopic.Quotient e (q • e)) (α : FundamentalGroup X (p e))
    (hmap : HEq
      ((FundamentalGroupoid.map ⟨p, hp.continuous⟩).map
        (show FundamentalGroupoid.mk e ⟶ FundamentalGroupoid.mk (q • e) from γ)) α.asHom) :
    hp.fundamentalGroupToMulOpposite ⟨e, rfl⟩ α = MulOpposite.op q := by
  have hclasses : HEq (γ.map ⟨p, hp.continuous⟩) α.asHom := hmap
  have hcast := Path.Homotopic.Quotient.cast_heq
    (γ := (α.asHom : Path.Homotopic.Quotient (p e) (p e))) rfl (hp.map_smul q)
  have heq : γ.map ⟨p, hp.continuous⟩ =
      Path.Homotopic.Quotient.cast (α.asHom : Path.Homotopic.Quotient (p e) (p e))
        rfl (hp.map_smul q) :=
    eq_of_heq (hclasses.trans hcast.symm)
  have hm := hp.isCoveringMap.monodromy_eq_of_map_eq
    (ex := ⟨e, rfl⟩) (ey := ⟨q • e, hp.map_smul q⟩) γ heq
  apply hp.fundamentalGroupToMulOpposite_apply_eq_iff.mpr
  exact congrArg Subtype.val hm.symm

/-- The same actual endpoint assertion with an arbitrary equality identifying
the chosen lift with the stated loop basepoint. -/
theorem endpointMonodromy_eq_of_path_map_heq_of_base
    (hp : IsQuotientCoveringMap p Q) (e : E) {x : X} (he : p e = x) (q : Q)
    (γ : Path.Homotopic.Quotient e (q • e)) (α : FundamentalGroup X x)
    (hmap : HEq
      ((FundamentalGroupoid.map ⟨p, hp.continuous⟩).map
        (show FundamentalGroupoid.mk e ⟶ FundamentalGroupoid.mk (q • e) from γ)) α.asHom) :
    hp.fundamentalGroupToMulOpposite ⟨e, he⟩ α = MulOpposite.op q := by
  subst x
  exact endpointMonodromy_eq_of_path_map_heq hp e q γ α hmap

/-- The endpoint can be supplied independently, together with its proved
equality to the quotient translate; no endpoint identification is assumed. -/
theorem endpointMonodromy_eq_of_path_map_heq_of_endpoint
    (hp : IsQuotientCoveringMap p Q) (e z : E) (q : Q) (hz : z = q • e)
    (γ : Path.Homotopic.Quotient e z) (α : FundamentalGroup X (p e))
    (hmap : HEq
      ((FundamentalGroupoid.map ⟨p, hp.continuous⟩).map
        (show FundamentalGroupoid.mk e ⟶ FundamentalGroupoid.mk z from γ)) α.asHom) :
    hp.fundamentalGroupToMulOpposite ⟨e, rfl⟩ α = MulOpposite.op q := by
  subst z
  exact endpointMonodromy_eq_of_path_map_heq hp e q γ α hmap

/-- Inversion converts the opposite group into the original group. -/
def oppositeInverseEquiv (Q : Type*) [Group Q] : Qᵐᵒᵖ ≃* Q :=
  (MulEquiv.inv' Q).symm

@[simp] theorem oppositeInverseEquiv_apply (q : Qᵐᵒᵖ) :
    oppositeInverseEquiv Q q = q.unop⁻¹ := rfl

@[simp] theorem oppositeInverseEquiv_op (q : Q) :
    oppositeInverseEquiv Q (MulOpposite.op q) = q⁻¹ := rfl

theorem ker_oppositeInverseEquiv_comp {G : Type*} [Group G] (f : G →* Qᵐᵒᵖ) :
    ((oppositeInverseEquiv Q).toMonoidHom.comp f).ker = f.ker := by
  ext g
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    EmbeddingLike.map_eq_one_iff]

/-- The normalized endpoint homomorphism for the actual quotient cover. -/
noncomputable def normalizedMonodromy (hp : IsQuotientCoveringMap p Q) (e : E) :
    FundamentalGroup X (p e) →* Q :=
  (oppositeInverseEquiv Q).toMonoidHom.comp (hp.fundamentalGroupToMulOpposite ⟨e, rfl⟩)

@[simp] theorem normalizedMonodromy_apply (hp : IsQuotientCoveringMap p Q) (e : E)
    (α : FundamentalGroup X (p e)) :
    normalizedMonodromy hp e α = (hp.fundamentalGroupToMulOpposite ⟨e, rfl⟩ α).unop⁻¹ := rfl

theorem normalizedMonodromy_ker (hp : IsQuotientCoveringMap p Q) (e : E) :
    (normalizedMonodromy hp e).ker = (hp.fundamentalGroupToMulOpposite ⟨e, rfl⟩).ker :=
  ker_oppositeInverseEquiv_comp _

theorem normalizedMonodromy_eq_of_path_map_heq
    (hp : IsQuotientCoveringMap p Q) (e : E) (q : Q)
    (γ : Path.Homotopic.Quotient e (q • e)) (α : FundamentalGroup X (p e))
    (hmap : HEq
      ((FundamentalGroupoid.map ⟨p, hp.continuous⟩).map
        (show FundamentalGroupoid.mk e ⟶ FundamentalGroupoid.mk (q • e) from γ)) α.asHom) :
    normalizedMonodromy hp e α = q⁻¹ := by
  rw [normalizedMonodromy_apply, endpointMonodromy_eq_of_path_map_heq hp e q γ α hmap]
  rfl

open Theorem18

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- The actual orbit-cover monodromy with the explicit inverse-opposite
normalization; it retains the original quotient and projection. -/
noncomputable def normalizedOrbitMonodromy (e : Complement M J) :
    FundamentalGroup (OrbitSpace M J) (orbitProjection M J e) →*
      Artin.coxeterNormalizerQuotient M J :=
  (oppositeInverseEquiv _).toMonoidHom.comp (Landmark1.orbitMonodromy M J e)

@[simp] theorem normalizedOrbitMonodromy_apply (e : Complement M J)
    (α : FundamentalGroup (OrbitSpace M J) (orbitProjection M J e)) :
    normalizedOrbitMonodromy M J e α = (Landmark1.orbitMonodromy M J e α).unop⁻¹ := rfl

theorem normalizedOrbitMonodromy_ker (e : Complement M J) :
    (normalizedOrbitMonodromy M J e).ker = (Landmark1.orbitMonodromy M J e).ker :=
  ker_oppositeInverseEquiv_comp _

end ArtinNormalisers.Sequence4
