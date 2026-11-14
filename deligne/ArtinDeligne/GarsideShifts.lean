import ArtinDeligne.GarsideFolds
import ArtinDeligneVendor.Topology.ArtinGroups.Realizations.WeightHomeomorph

/-!
# Cofinal shifts and compact contractible carriers

Common target multiplication cancels in every incoming difference, so the
actual simple-chain condition is preserved. Compact maps can be shifted into
a finite positive head-closed carrier, which contracts by the proved folds.
Unshifting its actual inclusion gives a continuous injective factorization.
This concerns the actual Garside weighted space, without any comparison with
an arrangement universal cover. Proofs use the accepted finite-carrier and
weight-homeomorphism APIs; no additional external proof source is used.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Deligne5

open Ribbon2 Homotopy5 Chamber3 OAI.HarmonicArtin Topology

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (B0 : RibbonObject M)

theorem IncomingVertex.cofinalShift_difference (n : ℕ) (u v : IncomingVertex M B0) :
    (IncomingVertex.cofinalShift (M := M) (B0 := B0) n u).difference (IncomingVertex.cofinalShift (M := M) (B0 := B0) n v) =
      u.difference v := by
  simp only [IncomingVertex.difference, IncomingVertex.cofinalShift_value]
  group

/-- These particular cofinal loops have trivial actual Coxeter projection. -/
theorem projection_cofinalLoop (J : Set I) :
    Artin.projection M (cofinalLoop M J) = 1 := by
  have hJ : Artin.projection M (parabolicDelta M J) ^ 2 = 1 := by
    rw [projection_parabolicDelta, pow_two, parabolicLongest_mul_self]
  have hS : Artin.projection M (parabolicDelta M Set.univ) ^ 2 = 1 := by
    rw [projection_parabolicDelta, pow_two, parabolicLongest_mul_self]
  simp only [cofinalLoop, map_mul, map_pow, map_inv, inv_pow, hJ, hS, inv_one, one_mul]

/-- The actual chamber is preserved by cofinal shifts, because their Coxeter
projection is one. No invariance under an arbitrary loop is asserted. -/
theorem IncomingVertex.cofinalShift_chamber (n : ℕ) (u : IncomingVertex M B0) :
    (IncomingVertex.cofinalShift n u).chamber = u.chamber := by
  apply congrArg (actualChamberOfRawLabel M B0.indices)
  apply rawFacetLabel_ext M B0.indices
  · rfl
  · change (Artin.projection M (u.value * cofinalLoop M B0.indices ^ n))⁻¹ =
      (Artin.projection M u.value)⁻¹
    simp only [map_mul, map_pow, projection_cofinalLoop, one_pow, mul_one]

/-- The literal simple support condition is invariant under a common cofinal
shift. This does not assert chamber invariance for arbitrary target loops. -/
theorem garsideWeightsSet_shift_iff (n : ℕ) (w : OrderWeights (IncomingVertex M B0)) :
    weightMap (IncomingVertex.cofinalShift (M := M) (B0 := B0) n : IncomingVertex M B0 →o IncomingVertex M B0) w
      ∈ garsideWeightsSet M B0 ↔ w ∈ garsideWeightsSet M B0 := by
  classical
  let e := IncomingVertex.cofinalShift (M := M) (B0 := B0) n
  have hs := weightMap_support_embedding (e : IncomingVertex M B0 →o IncomingVertex M B0)
    e.injective w
  constructor
  · intro h u hu v hv huv
    have hu' : e u ∈ (weightMap (e : IncomingVertex M B0 →o IncomingVertex M B0) w).weights.support := by
      rw [hs]
      exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
    have hv' : e v ∈ (weightMap (e : IncomingVertex M B0 →o IncomingVertex M B0) w).weights.support := by
      rw [hs]
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    simpa only [e, IncomingVertex.cofinalShift_source,
      IncomingVertex.cofinalShift_difference] using h (e u) hu' (e v) hv' (e.monotone huv)
  · intro h u hu v hv huv
    rw [hs] at hu hv
    obtain ⟨u₀, hu₀, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨v₀, hv₀, rfl⟩ := Finset.mem_image.mp hv
    change SimpleRibbon M (e u₀).source (e v₀).source ((e u₀).difference (e v₀))
    simpa only [e, IncomingVertex.cofinalShift_source,
      IncomingVertex.cofinalShift_difference] using h u₀ hu₀ v₀ hv₀ (e.le_iff_le.mp huv)

/-- The cofinal order automorphism restricted to the genuine simple weighted
subspace, with its actual inherited topology. -/
noncomputable def cofinalWeightsShift (n : ℕ) : GarsideWeights M B0 ≃ₜ GarsideWeights M B0 :=
  (weightHomeomorph (IncomingVertex.cofinalShift (M := M) (B0 := B0) n)).subtype
    (fun w => (garsideWeightsSet_shift_iff M B0 n w).symm)

@[simp] theorem cofinalWeightsShift_val (n : ℕ) (w : GarsideWeights M B0) :
    (cofinalWeightsShift M B0 n w).val =
      weightMap (IncomingVertex.cofinalShift (M := M) (B0 := B0) n : IncomingVertex M B0 →o IncomingVertex M B0) w.val :=
  rfl

theorem GarsideWeightsOn.include_injective (A : Set (IncomingVertex M B0)) :
    Function.Injective (GarsideWeightsOn.include M B0 A) := by
  intro u v h
  apply Subtype.ext
  exact weightMap_injective (weightInclusion A) Subtype.val_injective
    (congrArg Subtype.val h)

/-- The actual finite carrier inclusion followed by the inverse common shift. -/
noncomputable def unshiftedCarrierMap (n : ℕ) (A : Set (IncomingVertex M B0)) :
    C(GarsideWeightsOn M B0 A, GarsideWeights M B0) :=
  ⟨fun w => (cofinalWeightsShift M B0 n).symm (GarsideWeightsOn.include M B0 A w),
    (cofinalWeightsShift M B0 n).symm.continuous.comp
      (GarsideWeightsOn.continuous_include M B0 A)⟩

theorem unshiftedCarrierMap_injective (n : ℕ) (A : Set (IncomingVertex M B0)) :
    Function.Injective (unshiftedCarrierMap M B0 n A) :=
  (cofinalWeightsShift M B0 n).symm.injective.comp
    (GarsideWeightsOn.include_injective M B0 A)

/-- Every compact map factors through an actual finite positive head-closed
contractible carrier and its unshifted inclusion. -/
theorem GarsideWeights.compact_map_contractible_carrier
    {X : Type*} [TopologicalSpace X] [CompactSpace X] (f : C(X, GarsideWeights M B0)) :
    ∃ (n : ℕ) (B : Finset (IncomingVertex M B0)),
      incomingRoot M B0 ∈ B ∧
      (∀ u ∈ B, IncomingVertex.IsPositive M B0 u) ∧
      (∀ u ∈ B, headStep M B0 u ∈ B) ∧
      ContractibleSpace (GarsideWeightsOn M B0 (B : Set (IncomingVertex M B0))) ∧
      ∃ g : C(X, GarsideWeightsOn M B0 (B : Set (IncomingVertex M B0))),
        (unshiftedCarrierMap M B0 n B).comp g = f := by
  classical
  obtain ⟨A, hA, a, ha⟩ := GarsideWeights.compact_map_finite_carrier M B0 f
  have hfA (x : X) (u : IncomingVertex M B0) (hu : u ∈ (f x).val.weights.support) : u ∈ A := by
    have he := congrArg (fun F : C(X, GarsideWeights M B0) => (F x).val) ha
    change weightMap (weightInclusion A) (a x).val = (f x).val at he
    rw [← he, weightMap_support_embedding (weightInclusion A) Subtype.val_injective] at hu
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hu
    exact v.property
  obtain ⟨n, hn⟩ := IncomingVertex.finite_eventually_positive hA.toFinset
  let e := IncomingVertex.cofinalShift (M := M) (B0 := B0) n
  let C := hA.toFinset.image e
  have hC : ∀ u ∈ C, IncomingVertex.IsPositive M B0 u := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact hn v hv n le_rfl
  obtain ⟨B, hCB, hrB, hpos, hclosed⟩ := exists_finite_positive_head_closed M B0 C hC
  have hcontract : ContractibleSpace (GarsideWeightsOn M B0 (B : Set (IncomingVertex M B0))) :=
    contractibleSpace_finite_positive_head_closed M B0
      (fun u => hpos u.val u.property) (fun u => hclosed u.val u.property)
      ⟨incomingRoot M B0, hrB⟩ rfl
  let sf : C(X, GarsideWeights M B0) :=
    ⟨fun x => cofinalWeightsShift M B0 n (f x),
      (cofinalWeightsShift M B0 n).continuous.comp f.continuous⟩
  have hs (x : X) : ∀ u ∈ (sf x).val.weights.support,
      u ∈ (B : Set (IncomingVertex M B0)) := by
    intro u hu
    change u ∈ (weightMap (e : IncomingVertex M B0 →o IncomingVertex M B0) (f x).val).weights.support at hu
    rw [weightMap_support_embedding _ e.injective] at hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    exact hCB (Finset.mem_image.mpr ⟨v, hA.mem_toFinset.mpr (hfA x v hv), rfl⟩)
  let g : C(X, GarsideWeightsOn M B0 (B : Set (IncomingVertex M B0))) :=
    ⟨fun x => GarsideWeights.restrict M B0 B (sf x) (hs x),
      GarsideWeights.continuous_restrict_finite M B0 B B.finite_toSet sf hs⟩
  refine ⟨n, B, hrB, hpos, hclosed, hcontract, g, ?_⟩
  apply ContinuousMap.ext
  intro x
  change (cofinalWeightsShift M B0 n).symm
    (GarsideWeightsOn.include M B0 B (GarsideWeights.restrict M B0 B (sf x) (hs x))) = f x
  rw [GarsideWeights.include_restrict]
  exact (cofinalWeightsShift M B0 n).symm_apply_apply (f x)

end ArtinNormalisers.Deligne5
