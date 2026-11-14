import ArtinDeligne.GarsideShifts
import ArtinAsphericity.DirectedCover

/-!
# Actual homotopy groups of the Garside weighted space

A cube together with its basepoint factors through one actual contractible
finite carrier. Injectivity of the unshifted inclusion identifies all lifted
boundary points with the same lifted basepoint. The contractible carrier's
based homotopy group is trivial, and its actual continuous inclusion maps
that equality back. This is not an argument from a free nullhomotopy of a cube.

The contractible-space homotopy-group theorem is the already accepted
`ArtinNormalisers.Asphericity5.homotopyGroup_subsingleton_of_contractible`,
whose TauCeti proof uses actual basepoint transport. No new supplier is used.
All conclusions concern this actual weighted model; a comparison with an
arrangement universal cover remains a separate mathematical requirement.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Deligne5

open Ribbon2 Homotopy5 Chamber3 OAI.HarmonicArtin Topology
open scoped unitInterval Topology.Homotopy

variable {S : Type*} (M : CoxeterMatrix S) [Finite M.Group] (B0 : RibbonObject M)

/-- The actual root vertex supplies a point, also for empty or full parabolics. -/
noncomputable def garsideRootPoint : GarsideWeights M B0 :=
  GarsideWeightsOn.include M B0 Set.univ
    (GarsideWeightsOn.vertex M B0 ⟨incomingRoot M B0, Set.mem_univ _⟩)

/-- Every actual based generalized loop is null in its genuine based homotopy
group. The separate basepoint summand also handles an empty cube index type. -/
theorem garside_genLoop_class_eq_const (N : Type*) [Finite N]
    (x : GarsideWeights M B0) (f : GenLoop N (GarsideWeights M B0) x) :
    (⟦f⟧ : HomotopyGroup N (GarsideWeights M B0) x) = ⟦GenLoop.const⟧ := by
  classical
  let f' : C(Unit ⊕ (I^N), GarsideWeights M B0) :=
    ⟨Sum.elim (fun _ => x) f, continuous_const.sumElim f.val.continuous⟩
  obtain ⟨n, B, _, _, _, hcontract, g, hg⟩ :=
    GarsideWeights.compact_map_contractible_carrier M B0 f'
  let Y := GarsideWeightsOn M B0 (B : Set (IncomingVertex M B0))
  let j : C(Y, GarsideWeights M B0) := unshiftedCarrierMap M B0 n B
  have hj : Function.Injective j := unshiftedCarrierMap_injective M B0 n B
  have hpoint (p : Unit ⊕ (I^N)) : j (g p) = f' p :=
    congrArg (fun F : C(Unit ⊕ (I^N), GarsideWeights M B0) => F p) hg
  let y : Y := g (Sum.inl Unit.unit)
  have hy : j y = x := hpoint (Sum.inl Unit.unit)
  let F : GenLoop N Y y :=
    ⟨⟨fun z => g (Sum.inr z), g.continuous.comp continuous_inr⟩, fun z hz => by
      apply hj
      exact (hpoint (Sum.inr z)).trans ((GenLoop.boundary f z hz).trans hy.symm)⟩
  let : ContractibleSpace Y := hcontract
  have hzero : (⟦F⟧ : HomotopyGroup N Y y) = ⟦GenLoop.const⟧ :=
    (Asphericity5.homotopyGroup_subsingleton_of_contractible N y).elim _ _
  have hmap : GenLoop.map j hy F = f := by
    apply GenLoop.ext
    intro z
    rw [GenLoop.map_apply]
    exact hpoint (Sum.inr z)
  have hm := congrArg (HomotopyGroup.map (N := N) j hy) hzero
  rw [HomotopyGroup.map_mk, HomotopyGroup.map_mk, hmap, GenLoop.map_const] at hm
  exact hm

/-- All finite-index homotopy groups of the actual Garside space vanish. -/
theorem garside_homotopyGroup_subsingleton (N : Type*) [Finite N]
    (x : GarsideWeights M B0) : Subsingleton (HomotopyGroup N (GarsideWeights M B0) x) := by
  refine ⟨fun a b => ?_⟩
  refine Quotient.inductionOn₂ a b fun f g => ?_
  exact (garside_genLoop_class_eq_const M B0 N x f).trans
    (garside_genLoop_class_eq_const M B0 N x g).symm

/-- Any two actual points lie in the image of one contractible finite carrier. -/
theorem garside_joined (x y : GarsideWeights M B0) : Joined x y := by
  let f : C(Bool, GarsideWeights M B0) :=
    ⟨fun b => if b then x else y, continuous_of_discreteTopology⟩
  obtain ⟨n, B, _, _, _, hcontract, g, hg⟩ :=
    GarsideWeights.compact_map_contractible_carrier M B0 f
  let Y := GarsideWeightsOn M B0 (B : Set (IncomingVertex M B0))
  let : ContractibleSpace Y := hcontract
  let j : C(Y, GarsideWeights M B0) := unshiftedCarrierMap M B0 n B
  have hx : j (g true) = x := congrArg (fun F : C(Bool, GarsideWeights M B0) => F true) hg
  have hy : j (g false) = y := congrArg (fun F : C(Bool, GarsideWeights M B0) => F false) hg
  rw [← hx, ← hy]
  exact (PathConnectedSpace.joined (g true) (g false)).map j.continuous

theorem garside_pathConnectedSpace : PathConnectedSpace (GarsideWeights M B0) :=
  ⟨⟨garsideRootPoint M B0⟩, garside_joined M B0⟩

/-- Asphericity of this actual weighted model, without asserting any comparison
with the original universal cover or the original Theorem 1.8 target. -/
theorem garside_isAspherical (x : GarsideWeights M B0) :
    TauCeti.IsAspherical (GarsideWeights M B0) x := by
  let : PathConnectedSpace (GarsideWeights M B0) := garside_pathConnectedSpace M B0
  exact TauCeti.IsAspherical.mk inferInstance
    (fun n => garside_homotopyGroup_subsingleton M B0 (Fin (n + 2)) x)

end ArtinNormalisers.Deligne5
