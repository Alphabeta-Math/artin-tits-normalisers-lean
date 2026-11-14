module

public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Finite real linear arrangements and their actual complexified complements

The parameter is a family of continuous real linear forms. All spaces below
have their inherited subspace topology. Chambers are nonempty strict sign
cells; their connected-component characterization is a theorem to prove.
No comparison with a fundamental groupoid is included in these definitions.
-/

@[expose] public section

namespace ArtinNormalisers.Chamber3

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {H : Type*}

/-- The real regular locus of the specified family of actual linear forms. -/
def regularSet (ℓ : H → E →L[ℝ] ℝ) : Set E :=
  {x | ∀ h, ℓ h x ≠ 0}

/-- A strict oriented halfspace of one actual form. -/
def signHalfSpace (f : E →L[ℝ] ℝ) (positive : Bool) : Set E :=
  {x | if positive then 0 < f x else f x < 0}

/-- A strict sign cell; inconsistent sign patterns have empty cell. -/
def signCell (ℓ : H → E →L[ℝ] ℝ) (s : H → Bool) : Set E :=
  {x | ∀ h, x ∈ signHalfSpace (ℓ h) (s h)}

/-- A realized chamber, represented by its nonempty geometric sign cell. -/
@[ext] structure Chamber (ℓ : H → E →L[ℝ] ℝ) where
  signs : H → Bool
  nonempty : (signCell ℓ signs).Nonempty

/-- The actual subset represented by a realized chamber. -/
def Chamber.region {ℓ : H → E →L[ℝ] ℝ} (C : Chamber ℓ) : Set E :=
  signCell ℓ C.signs

/-- The literal real-pair model of the complexified hyperplane complement. -/
def complexComplementSet (ℓ : H → E →L[ℝ] ℝ) : Set (E × E) :=
  {p | ∀ h, ¬(ℓ h p.1 = 0 ∧ ℓ h p.2 = 0)}

/-- The actual complement with its subspace topology. -/
abbrev ComplexComplement (ℓ : H → E →L[ℝ] ℝ) :=
  ↥(complexComplementSet ℓ)

/-- Van der Lek's chamber tube in the actual complement (article6.6). -/
def tubeSet {ℓ : H → E →L[ℝ] ℝ} (C : Chamber ℓ) : Set (ComplexComplement ℓ) :=
  {p | ∀ h, ℓ h p.val.1 = 0 → p.val.2 ∈ signHalfSpace (ℓ h) (C.signs h)}

end ArtinNormalisers.Chamber3
