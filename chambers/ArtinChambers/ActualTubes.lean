module

public import ArtinChambers.ActualArrangement

/-!
# Contractibility of the chamber tubes in the original complement

The identity-coordinate homeomorphism is restricted to the actual tube
subspaces. Contractibility transfers through this proved homeomorphism.
-/

@[expose] public section

namespace ArtinNormalisers.Chamber3

open Theorem18

variable {I : Type*} (M : CoxeterMatrix I) (J : Set I)

/-- The tube homeomorphism is the actual identity-coordinate complement
homeomorphism restricted to the corresponding subspaces. -/
noncomputable def actualTubeHomeomorph (C : ActualChamber M J) :
    ↥(actualTubeSet M J C) ≃ₜ ↥(tubeSet (E := relativeSubspace J) C) :=
  (actualComplementHomeomorph M J).subtype
    (p := fun p => p ∈ actualTubeSet M J C)
    (q := fun p => p ∈ tubeSet (E := relativeSubspace J) C)
    (fun _ => Iff.rfl)

/-- The article's actual tube is contractible. No finiteness assumption is
needed for this local assertion, including the full-parabolic point case. -/
noncomputable instance actualTubeContractible (C : ActualChamber M J) :
    ContractibleSpace ↥(actualTubeSet M J C) :=
  (actualTubeHomeomorph M J C).contractibleSpace

end ArtinNormalisers.Chamber3
