module

public import ArtinChambers.SignCells
public import ArtinChambers.Tubes
public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Sets.OpenCover

/-!
# The actual chamber tubes cover the complexified complement

For a point `(x,y)` in the complement, all but finitely many parameters
make `y+t x` real regular. Its chamber has the same signs as `y` at every
hyperplane containing `x`, which is exactly the tube membership condition.
No density, properness or nondegeneracy premise is used.

The proof is local authoring using mathlib's finite-range and infinite-set
lemmas; no external GitHub proof is imported for this covering construction.
-/

@[expose] public section

namespace ArtinNormalisers.Chamber3

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {H : Type*} (ℓ : H → E →L[ℝ] ℝ)

/-- A complement point has a real regular linear combination of its real
and imaginary parts. Only finitely many scalar parameters are excluded. -/
theorem exists_regular_imag_add_smul_real [Finite H] (p : ComplexComplement ℓ) :
    ∃ t : ℝ, p.val.2 + t • p.val.1 ∈ regularSet ℓ := by
  classical
  let bad : H → ℝ := fun h => -(ℓ h p.val.2) / ℓ h p.val.1
  obtain ⟨t, ht⟩ := (Set.finite_range bad).exists_notMem
  refine ⟨t, fun h hzero => ?_⟩
  rw [map_add, map_smul, smul_eq_mul] at hzero
  by_cases hx : ℓ h p.val.1 = 0
  · apply p.property h
    exact ⟨hx, by simpa only [hx, mul_zero, add_zero] using hzero⟩
  · apply ht
    refine ⟨h, ?_⟩
    dsimp only [bad]
    apply (div_eq_iff hx).2
    linarith

/-- Every actual complement point belongs to the tube of a realized chamber. -/
theorem exists_mem_tubeSet [Finite H] (p : ComplexComplement ℓ) :
    ∃ C : Chamber ℓ, p ∈ tubeSet C := by
  obtain ⟨t, ht⟩ := exists_regular_imag_add_smul_real ℓ p
  let c := p.val.2 + t • p.val.1
  let C := chamberOfRegular ℓ c ht
  have hc : c ∈ C.region := mem_chamberOfRegular_region ℓ c ht
  refine ⟨C, fun h hx => ?_⟩
  have heval : ℓ h c = ℓ h p.val.2 := by
    dsimp only [c]
    rw [map_add, map_smul, hx, smul_zero, add_zero]
  have hsign := hc h
  change (if C.signs h then 0 < ℓ h c else ℓ h c < 0) at hsign
  change (if C.signs h then 0 < ℓ h p.val.2 else ℓ h p.val.2 < 0)
  rwa [heval] at hsign

/-- The tubes cover the literal real-pair complement with its given topology. -/
theorem iUnion_tubeSet [Finite H] :
    (⋃ C : Chamber ℓ, tubeSet C) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  exact Set.mem_iUnion.2 (exists_mem_tubeSet ℓ p)

/-- Covariance of actual tubes under a specified linear homeomorphism and
form permutation, with the corresponding chamber-sign transport. -/
theorem tubeSet_transport_iff (e : E ≃L[ℝ] E) (σ : H ≃ H)
    (hforms : ∀ h x, ℓ (σ h) (e x) = ℓ h x)
    {C D : Chamber ℓ} (hsigns : ∀ h, D.signs (σ h) = C.signs h)
    {p q : ComplexComplement ℓ}
    (hreal : q.val.1 = e p.val.1) (himag : q.val.2 = e p.val.2) :
    q ∈ tubeSet D ↔ p ∈ tubeSet C := by
  constructor
  · intro hq h hx
    have hz : ℓ (σ h) q.val.1 = 0 := by rw [hreal, hforms, hx]
    have hs := hq (σ h) hz
    change (if D.signs (σ h) then 0 < ℓ (σ h) q.val.2 else ℓ (σ h) q.val.2 < 0) at hs
    change (if C.signs h then 0 < ℓ h p.val.2 else ℓ h p.val.2 < 0)
    rwa [hsigns, himag, hforms] at hs
  · intro hp k hk
    let h := σ.symm k
    have hσ : σ h = k := σ.apply_symm_apply k
    have hx : ℓ h p.val.1 = 0 := by
      have hv := hforms h p.val.1
      rw [hσ, ← hreal, hk] at hv
      exact hv.symm
    have hs := hp h hx
    have hs' : D.signs k = C.signs h := by rw [← hσ, hsigns]
    have hy : ℓ k q.val.2 = ℓ h p.val.2 := by rw [← hσ, himag, hforms]
    change (if C.signs h then 0 < ℓ h p.val.2 else ℓ h p.val.2 < 0) at hs
    change (if D.signs k then 0 < ℓ k q.val.2 else ℓ k q.val.2 < 0)
    rw [hs', hy]
    exact hs

/-- A chamber tube as an actual open subset of the complement. -/
def chamberTubeOpen [Finite H] (C : Chamber ℓ) :
    TopologicalSpace.Opens (ComplexComplement ℓ) :=
  ⟨tubeSet C, isOpen_tubeSet C⟩

/-- The realized chambers index a genuine open cover of the complement. -/
theorem isOpenCover_chamberTube [Finite H] :
    TopologicalSpace.IsOpenCover (chamberTubeOpen ℓ) :=
  TopologicalSpace.IsOpenCover.of_sets (fun C : Chamber ℓ => isOpen_tubeSet C)
    (iUnion_tubeSet ℓ)

end ArtinNormalisers.Chamber3
