module

public import ArtinChambers.GroupoidCover
public import ArtinLandmarks.Covering
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Actual topological covering maps induce fundamental-groupoid coverings

Lifting a path class supplies both its endpoint and its lifted arrow.
Monodromy recovers the endpoint of any lift, and injectivity on path
homotopy classes gives uniqueness once that endpoint is known. This proves
the outgoing-arrow covering condition for actual topological covering maps,
without connectedness or surjectivity assumptions.
-/

@[expose] public section

namespace ArtinNormalisers.Chamber3

open CategoryTheory

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

/-- A genuine covering map induces unique outgoing-arrow lifting on the
actual Mathlib fundamental groupoids, including uniqueness of the endpoint. -/
theorem isCoveringFunctor_fundamentalGroupoid_map {p : E → X} (hp : IsCoveringMap p) :
    IsCoveringFunctor (FundamentalGroupoid.map ⟨p, hp.continuous⟩) := by
  intro e
  constructor
  · rintro ⟨⟨y⟩, γ⟩ ⟨⟨z⟩, δ⟩ h
    have hyz : y = z := by
      have h' := congrArg (fun a : Outgoing (FundamentalGroupoid X)
          ((FundamentalGroupoid.map ⟨p, hp.continuous⟩).obj e) =>
        (hp.monodromy a.2 ⟨e.as, rfl⟩).val) h
      change (hp.monodromy (γ.map ⟨p, hp.continuous⟩) ⟨e.as, rfl⟩).val =
        (hp.monodromy (δ.map ⟨p, hp.continuous⟩) ⟨e.as, rfl⟩).val at h'
      simpa only [hp.monodromy_map] using h'
    subst z
    apply congrArg (fun a : e ⟶ FundamentalGroupoid.mk y =>
      (⟨FundamentalGroupoid.mk y, a⟩ : Outgoing (FundamentalGroupoid E) e))
    apply hp.injective_path_homotopic_map e.as y
    exact eq_of_heq (Sigma.mk.inj h).2
  · rintro ⟨⟨y⟩, γ⟩
    let ey := hp.monodromy γ ⟨e.as, rfl⟩
    refine ⟨⟨FundamentalGroupoid.mk ey.val, hp.liftPathQuotient γ ⟨e.as, rfl⟩⟩, ?_⟩
    have hey : p ey.val = y := ey.property
    apply Sigma.ext
    · exact congrArg (fun x : X => FundamentalGroupoid.mk x) hey
    · change HEq ((hp.liftPathQuotient γ ⟨e.as, rfl⟩).map ⟨p, hp.continuous⟩) γ
      rw [hp.map_liftPathQuotient]
      exact Path.Homotopic.Quotient.cast_heq rfl hey

variable {I : Type*} (M : CoxeterMatrix I) (J : Set I)

/-- The functor induced by the actual finite-type normalizer orbit covering. -/
noncomputable def orbitFundamentalGroupoidFunctor :
    FundamentalGroupoid (Theorem18.Complement M J) ⥤
      FundamentalGroupoid (Theorem18.OrbitSpace M J) :=
  FundamentalGroupoid.map ⟨Theorem18.orbitProjection M J,
    Theorem18.continuous_orbitProjection M J⟩

/-- Landmark 1's actual orbit covering satisfies the outgoing groupoid-cover
condition; no geometric/Artin groupoid comparison is assumed. -/
theorem isCoveringFunctor_orbitFundamentalGroupoidFunctor [Finite M.Group] :
    IsCoveringFunctor (orbitFundamentalGroupoidFunctor M J) :=
  isCoveringFunctor_fundamentalGroupoid_map (Landmark1.isCoveringMap_orbitProjection M J)

end ArtinNormalisers.Chamber3
