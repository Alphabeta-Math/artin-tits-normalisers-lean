module

public import ArtinChambers.ActualArrangement
public import ArtinChamberVendor.AlgebraicTopology.FundamentalGroupoid.Cech.Colimit
public import ArtinChamberVendor.AlgebraicTopology.FundamentalGroupoid.Cech.Map

/-!
# Actual chamber-tube van Kampen diagrams

The instantiated cocone has the actual complement's fundamental groupoid as
its vertex. The cover hypotheses are proved by the preceding explicit
construction. This does not yet identify the colimit with the ribbon or
Deligne presentation.
-/

@[expose] public section

namespace ArtinNormalisers.Chamber3

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped FundamentalGroupoid

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {H : Type*} [Finite H] (ℓ : H → E →L[ℝ] ℝ)

/-- The literal fundamental-groupoid cocone of the actual generic tubes. -/
noncomputable def tubeCechCocone :=
  TauCeti.FundamentalGroupoid.cechCocone
    (X := TopCat.of (ComplexComplement (E := E) ℓ)) (chamberTubeOpen ℓ)

/-- Actual open-cover van Kampen, with no local-connectivity premise assumed. -/
noncomputable def tubeCechIsColimit : IsColimit (tubeCechCocone ℓ) :=
  TauCeti.FundamentalGroupoid.isColimitCechCocone (isOpenCover_chamberTube ℓ)

section Actual

open Theorem18

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- The actual tube in the original article complement as an open subspace. -/
noncomputable def actualChamberTubeOpen (C : ActualChamber M J) :
    Opens (Complement M J) :=
  ⟨actualTubeSet M J C, isOpen_actualTubeSet M J C⟩

theorem iUnion_actualTubeSet :
    (⋃ C : ActualChamber M J, actualTubeSet M J C) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  exact Set.mem_iUnion.2 (exists_mem_actualTubeSet M J p)

theorem isOpenCover_actualChamberTube : IsOpenCover (actualChamberTubeOpen M J) :=
  IsOpenCover.of_sets (fun C => isOpen_actualTubeSet M J C) (iUnion_actualTubeSet M J)

/-- The Čech cocone's vertex is exactly the original complement's fundamental
 groupoid, rather than an abstract classifying-space substitute. -/
noncomputable def actualTubeCechCocone :=
  TauCeti.FundamentalGroupoid.cechCocone
    (X := TopCat.of (Complement M J)) (actualChamberTubeOpen M J)

/-- The canonical cocone of actual chamber tubes is a genuine colimit. -/
noncomputable def actualTubeCechIsColimit : IsColimit (actualTubeCechCocone M J) :=
  TauCeti.FundamentalGroupoid.isColimitCechCocone (isOpenCover_actualChamberTube M J)

end Actual

end ArtinNormalisers.Chamber3
