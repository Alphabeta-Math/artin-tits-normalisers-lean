module

public import ArtinLandmarks.RegularStabilizer
public import ArtinNormalisers.Theorem18.ArrangementTopology
public import ArtinNormalisers.Theorem18.CoveringSequence
public import Mathlib.Topology.Covering.Quotient

/-!
# Landmark 1: the actual relative normalizer quotient covering

A real linear combination of the coordinates of a complement point avoids
every retained hyperplane. The real regular stabilizer theorem therefore
identifies its full Coxeter pair stabilizer with the standard parabolic.
The actual normalizer quotient action is free, and its actual orbit map is a
quotient covering. Its genuine fundamental groups consequently form the
covering short exact sequence, with raw endpoint monodromy in the opposite
group. No Artin/fundamental-group comparison or asphericity is asserted.
-/

@[expose] public section

namespace ArtinNormalisers.Landmark1

open Theorem18

variable {I : Type*} (M : CoxeterMatrix I) (J : Set I)

/-- Coefficients of a real linear combination evaluated at a root. -/
noncomputable def coefficientEvaluation
    (p : relativeSubspace J × relativeSubspace J) (r : Vector I) :
    (ℝ × ℝ) →ₗ[ℝ] ℝ :=
  (p.1.val r) • LinearMap.fst ℝ ℝ ℝ + (p.2.val r) • LinearMap.snd ℝ ℝ ℝ

/-- An actual complement point has a real regular linear combination of its
two coordinates. No chamber point or positive dimension is assumed. -/
theorem exists_regular_linearCombination [Finite M.Group] (p : Complement M J) :
    ∃ a b : ℝ, realRelativeRegular M J (a • p.val.1 + b • p.val.2) := by
  classical
  let := (retainedRoots_finite M J).fintype
  let f : retainedRoots M J → (ℝ × ℝ) →ₗ[ℝ] ℝ :=
    fun r => coefficientEvaluation J p.val r.val
  have hf : ∀ r, ∃ c, f r c ≠ 0 := by
    intro r
    by_cases hx : p.val.1.val r.val = 0
    · refine ⟨(0, 1), ?_⟩
      have hy : p.val.2.val r.val ≠ 0 := fun hy => p.property r.val r.property ⟨hx, hy⟩
      simpa [f, coefficientEvaluation] using hy
    · exact ⟨(1, 0), by simpa [f, coefficientEvaluation] using hx⟩
  obtain ⟨c, hc⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f hf
  refine ⟨c.1, c.2, fun r hr => ?_⟩
  simpa [f, coefficientEvaluation, mul_comm] using hc ⟨r, hr⟩

/-- The full ambient Coxeter stabilizer of both coordinates of an actual
complement point is exactly the generated parabolic. -/
theorem complement_pair_stabilizer_iff [Finite M.Group]
    (p : Complement M J) (g : M.Group) :
    (dualAction M g p.val.1.val = p.val.1.val ∧
      dualAction M g p.val.2.val = p.val.2.val) ↔
      g ∈ Artin.coxeterParabolic M J := by
  constructor
  · rintro ⟨hx, hy⟩
    obtain ⟨a, b, hab⟩ := exists_regular_linearCombination M J p
    apply (realRelativeRegular_fixed_iff M J _ hab g).1
    change dualAction M g (a • p.val.1.val + b • p.val.2.val) = _
    rw [map_add, map_smul, map_smul, hx, hy]
    rfl
  · intro hg
    exact ⟨(mem_relativeSubspace_iff_fixed M J _).1 p.val.1.property g hg,
      (mem_relativeSubspace_iff_fixed M J _).1 p.val.2.property g hg⟩

/-- The actual action of `N_W(W_J)/W_J` on the actual complex complement is free. -/
theorem quotientComplement_smul_fixed_iff [Finite M.Group]
    (q : Artin.coxeterNormalizerQuotient M J) (p : Complement M J) :
    q • p = p ↔ q = 1 := by
  constructor
  · intro hq
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective
      ((Artin.coxeterParabolic M J).subgroupOf (CoxeterNormalizer M J)) q
    have hx := congrArg (fun z : Complement M J => z.val.1.val) hq
    have hy := congrArg (fun z : Complement M J => z.val.2.val) hq
    change dualAction M w.val p.val.1.val = p.val.1.val at hx
    change dualAction M w.val p.val.2.val = p.val.2.val at hy
    exact (QuotientGroup.eq_one_iff w).2
      ((complement_pair_stabilizer_iff M J p w.val).1 ⟨hx, hy⟩)
  · rintro rfl
    exact one_smul _ _

instance quotientComplementIsCancelSMul [Finite M.Group] :
    IsCancelSMul (Artin.coxeterNormalizerQuotient M J) (Complement M J) :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr fun q p hq =>
    (quotientComplement_smul_fixed_iff M J q p).1 hq

instance complementT2Space : T2Space (Complement M J) :=
  inferInstanceAs (T2Space ↥(complementSet M J))

/-- The actual finite-type complement is locally compact in its specified topology. -/
noncomputable instance complementLocallyCompactSpace [Finite M.Group] :
    LocallyCompactSpace (Complement M J) := by
  have := finite_index M
  have : LocallyCompactSpace (Dual I) :=
    dualCoordinatesHomeomorph.isClosedEmbedding.locallyCompactSpace
  have : LocallyCompactSpace (relativeSubspace J) :=
    (isClosed_relativeSubspace J).locallyCompactSpace
  exact (isOpen_complementSet M J).locallyCompactSpace

/-- The covering is the actual orbit map with its actual quotient topology. -/
theorem isQuotientCoveringMap_orbitProjection [Finite M.Group] :
    IsQuotientCoveringMap (orbitProjection M J) (Artin.coxeterNormalizerQuotient M J) := by
  have := properlyDiscontinuous_quotientComplementAction M J
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

theorem isCoveringMap_orbitProjection [Finite M.Group] :
    IsCoveringMap (orbitProjection M J) :=
  (isQuotientCoveringMap_orbitProjection M J).isCoveringMap

/-- The first homomorphism is induced by the actual continuous orbit map. -/
noncomputable def orbitFundamentalGroupMap (p : Complement M J) :
    FundamentalGroup (Complement M J) p →*
      FundamentalGroup (OrbitSpace M J) (orbitProjection M J p) :=
  FundamentalGroup.mapOfEq ⟨orbitProjection M J, continuous_orbitProjection M J⟩ rfl

/-- Raw endpoint monodromy of the actual covering; no inverse-label convention
or comparison with the Artin projection is silently imposed. -/
noncomputable def orbitMonodromy [Finite M.Group] (p : Complement M J) :
    FundamentalGroup (OrbitSpace M J) (orbitProjection M J p) →*
      (Artin.coxeterNormalizerQuotient M J)ᵐᵒᵖ :=
  (isQuotientCoveringMap_orbitProjection M J).fundamentalGroupToMulOpposite ⟨p, rfl⟩

/-- The geometric short exact sequence for the actual relative complement,
at every basepoint, now follows without assuming freeness or a covering. -/
theorem orbitFundamentalGroup_shortExact [Finite M.Group] (p : Complement M J) :
    Function.Injective (orbitFundamentalGroupMap M J p) ∧
      (orbitFundamentalGroupMap M J p).range = (orbitMonodromy M J p).ker ∧
      Function.Surjective (orbitMonodromy M J p) :=
  quotientCovering_fundamentalGroup_shortExact
    (isQuotientCoveringMap_orbitProjection M J) ⟨p, rfl⟩

end ArtinNormalisers.Landmark1
