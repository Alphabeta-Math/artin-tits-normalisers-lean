module

public import ArtinChambers.ActualArrangement

/-!
# A finite convex open cover of the actual arrangement complement

For each form, choose one of four strict inequalities: positive or negative
real evaluation, or positive or negative imaginary evaluation. Their finite
intersections are actual convex open subsets of the ambient real product.
They cover the literal complexified complement. Every nonempty intersection
of a nonempty family of cover members is contractible with its actual
subspace topology. This good-cover construction alone asserts no asphericity.
The family may contain duplicate or zero forms; empty form families are allowed.
-/

@[expose] public section

namespace ArtinNormalisers.Asphericity5

open Chamber3

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {H : Type*}

/-- One of four genuine open halfspaces in the real-pair ambient space. -/
def coordinateHalfSpace (f : E →L[ℝ] ℝ) (k : Fin 4) : Set (E × E) :=
  if k = 0 then {p | 0 < f p.1}
  else if k = 1 then {p | f p.1 < 0}
  else if k = 2 then {p | 0 < f p.2}
  else {p | f p.2 < 0}

theorem isOpen_coordinateHalfSpace (f : E →L[ℝ] ℝ) (k : Fin 4) :
    IsOpen (coordinateHalfSpace f k) := by
  unfold coordinateHalfSpace
  split_ifs
  · exact isOpen_lt continuous_const (f.continuous.comp continuous_fst)
  · exact isOpen_lt (f.continuous.comp continuous_fst) continuous_const
  · exact isOpen_lt continuous_const (f.continuous.comp continuous_snd)
  · exact isOpen_lt (f.continuous.comp continuous_snd) continuous_const

theorem convex_coordinateHalfSpace (f : E →L[ℝ] ℝ) (k : Fin 4) :
    Convex ℝ (coordinateHalfSpace f k) := by
  unfold coordinateHalfSpace
  split_ifs
  · exact (convex_signHalfSpace f true).linear_preimage (LinearMap.fst ℝ E E)
  · exact (convex_signHalfSpace f false).linear_preimage (LinearMap.fst ℝ E E)
  · exact (convex_signHalfSpace f true).linear_preimage (LinearMap.snd ℝ E E)
  · exact (convex_signHalfSpace f false).linear_preimage (LinearMap.snd ℝ E E)

/-- The literal convex region specified by one four-way choice per form. -/
def convexCell (ℓ : H → E →L[ℝ] ℝ) (σ : H → Fin 4) : Set (E × E) :=
  ⋂ h, coordinateHalfSpace (ℓ h) (σ h)

theorem convex_convexCell (ℓ : H → E →L[ℝ] ℝ) (σ : H → Fin 4) :
    Convex ℝ (convexCell ℓ σ) :=
  convex_iInter fun h => convex_coordinateHalfSpace (ℓ h) (σ h)

theorem isOpen_convexCell [Finite H] (ℓ : H → E →L[ℝ] ℝ) (σ : H → Fin 4) :
    IsOpen (convexCell ℓ σ) :=
  isOpen_iInter_of_finite fun h => isOpen_coordinateHalfSpace (ℓ h) (σ h)

theorem convexCell_subset_complexComplementSet (ℓ : H → E →L[ℝ] ℝ)
    (σ : H → Fin 4) : convexCell ℓ σ ⊆ complexComplementSet ℓ := by
  intro p hp h hz
  have hh := Set.mem_iInter.mp hp h
  unfold coordinateHalfSpace at hh
  split_ifs at hh <;> simp [hz.1, hz.2] at hh

/-- Each ambient convex region, as an actual subset of the complement. -/
def convexCoverSet (ℓ : H → E →L[ℝ] ℝ) (σ : H → Fin 4) :
    Set (ComplexComplement ℓ) := Subtype.val ⁻¹' convexCell ℓ σ

theorem isOpen_convexCoverSet [Finite H] (ℓ : H → E →L[ℝ] ℝ)
    (σ : H → Fin 4) : IsOpen (convexCoverSet ℓ σ) :=
  (isOpen_convexCell ℓ σ).preimage continuous_subtype_val

theorem exists_mem_convexCoverSet (ℓ : H → E →L[ℝ] ℝ) (p : ComplexComplement ℓ) :
    ∃ σ : H → Fin 4, p ∈ convexCoverSet ℓ σ := by
  classical
  let σ : H → Fin 4 := fun h =>
    if 0 < ℓ h p.val.1 then 0 else if ℓ h p.val.1 < 0 then 1
    else if 0 < ℓ h p.val.2 then 2 else 3
  refine ⟨σ, Set.mem_iInter.mpr fun h => ?_⟩
  by_cases hrp : 0 < ℓ h p.val.1
  · simp [coordinateHalfSpace, σ, hrp]
  · by_cases hrn : ℓ h p.val.1 < 0
    · simp [coordinateHalfSpace, σ, hrp, hrn]
    · by_cases hip : 0 < ℓ h p.val.2
      · simp [coordinateHalfSpace, σ, hrp, hrn, hip]
      · have hr : ℓ h p.val.1 = 0 :=
          le_antisymm (le_of_not_gt hrp) (le_of_not_gt hrn)
        have hi : ℓ h p.val.2 ≠ 0 := fun hz => p.property h ⟨hr, hz⟩
        have hin : ℓ h p.val.2 < 0 := lt_of_le_of_ne (le_of_not_gt hip) hi
        simp [coordinateHalfSpace, σ, hrp, hrn, hip, hin]

theorem iUnion_convexCoverSet (ℓ : H → E →L[ℝ] ℝ) :
    (⋃ σ : H → Fin 4, convexCoverSet ℓ σ) = Set.univ := by
  ext p
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact exists_mem_convexCoverSet ℓ p

/-- Intersections before restricting to the complement remain convex. -/
def ambientConvexCoverIntersection (ℓ : H → E →L[ℝ] ℝ)
    (F : Set (H → Fin 4)) : Set (E × E) := ⋂ σ ∈ F, convexCell ℓ σ

/-- Literal intersections of the actual cover subsets. -/
def convexCoverIntersection (ℓ : H → E →L[ℝ] ℝ)
    (F : Set (H → Fin 4)) : Set (ComplexComplement ℓ) :=
  ⋂ σ ∈ F, convexCoverSet ℓ σ

theorem mem_convexCoverIntersection_iff (ℓ : H → E →L[ℝ] ℝ)
    (F : Set (H → Fin 4)) (p : ComplexComplement ℓ) :
    p ∈ convexCoverIntersection ℓ F ↔ p.val ∈ ambientConvexCoverIntersection ℓ F := by
  simp only [convexCoverIntersection, ambientConvexCoverIntersection, convexCoverSet,
    Set.mem_iInter, Set.mem_preimage]

theorem convex_ambientConvexCoverIntersection (ℓ : H → E →L[ℝ] ℝ)
    (F : Set (H → Fin 4)) : Convex ℝ (ambientConvexCoverIntersection ℓ F) :=
  convex_iInter fun σ => convex_iInter fun _ => convex_convexCell ℓ σ

theorem ambientConvexCoverIntersection_subset_complement (ℓ : H → E →L[ℝ] ℝ)
    {F : Set (H → Fin 4)} (hF : F.Nonempty) :
    ambientConvexCoverIntersection ℓ F ⊆ complexComplementSet ℓ := by
  obtain ⟨σ, hσ⟩ := hF
  intro p hp
  exact convexCell_subset_complexComplementSet ℓ σ
    (Set.mem_iInter.mp (Set.mem_iInter.mp hp σ) hσ)

/-- Flattening the two actual subtypes preserves their subspace topologies.
A nonempty index family is needed: the empty intersection inside the
complement is the whole complement, which need not be contractible. -/
def convexCoverIntersectionHomeomorph (ℓ : H → E →L[ℝ] ℝ)
    (F : Set (H → Fin 4)) (hF : F.Nonempty) :
    convexCoverIntersection ℓ F ≃ₜ ambientConvexCoverIntersection ℓ F where
  toFun p := ⟨p.val.val, (mem_convexCoverIntersection_iff ℓ F p.val).mp p.property⟩
  invFun p := ⟨⟨p.val, ambientConvexCoverIntersection_subset_complement ℓ hF p.property⟩,
    (mem_convexCoverIntersection_iff ℓ F _).mpr p.property⟩
  left_inv _p := rfl
  right_inv _p := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

variable [ContinuousAdd E] [ContinuousSMul ℝ E]

theorem contractibleSpace_convexCoverIntersection (ℓ : H → E →L[ℝ] ℝ)
    (F : Set (H → Fin 4)) (hF : F.Nonempty)
    (hne : (convexCoverIntersection ℓ F).Nonempty) :
    ContractibleSpace (convexCoverIntersection ℓ F) := by
  have hraw : (ambientConvexCoverIntersection ℓ F).Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨p.val, (mem_convexCoverIntersection_iff ℓ F p).mp hp⟩
  exact (convexCoverIntersectionHomeomorph ℓ F hF).contractibleSpace_iff.mpr
    ((convex_ambientConvexCoverIntersection ℓ F).contractibleSpace hraw)

/-- The ordinary finite-overlap good-cover conclusion, without excluding
empty hyperplane families or requiring distinct forms. -/
theorem contractibleSpace_finset_convexCoverSet (ℓ : H → E →L[ℝ] ℝ)
    (s : Finset (H → Fin 4)) (hs : s.Nonempty)
    (hne : (⋂ σ ∈ s, convexCoverSet ℓ σ).Nonempty) :
    ContractibleSpace (⋂ σ ∈ s, convexCoverSet ℓ σ) :=
  contractibleSpace_convexCoverIntersection ℓ (s : Set (H → Fin 4)) hs hne

section Actual

variable {I : Type*}

/-- The finite four-way cover in the original relative complement. -/
noncomputable def actualConvexCoverSet (M : CoxeterMatrix I) (J : Set I)
    (σ : RelativeRoot M J → Fin 4) : Set (Theorem18.Complement M J) :=
  actualComplementHomeomorph M J ⁻¹'
    convexCoverSet (E := Theorem18.relativeSubspace J) (actualForms M J) σ

theorem isOpen_actualConvexCoverSet (M : CoxeterMatrix I) [Finite M.Group]
    (J : Set I) (σ : RelativeRoot M J → Fin 4) :
    IsOpen (actualConvexCoverSet M J σ) :=
  (isOpen_convexCoverSet (E := Theorem18.relativeSubspace J) (actualForms M J) σ).preimage
    (actualComplementHomeomorph M J).continuous

theorem exists_mem_actualConvexCoverSet (M : CoxeterMatrix I) (J : Set I)
    (p : Theorem18.Complement M J) :
    ∃ σ : RelativeRoot M J → Fin 4, p ∈ actualConvexCoverSet M J σ :=
  exists_mem_convexCoverSet (E := Theorem18.relativeSubspace J)
    (actualForms M J) (actualComplementHomeomorph M J p)

theorem iUnion_actualConvexCoverSet (M : CoxeterMatrix I) (J : Set I) :
    (⋃ σ : RelativeRoot M J → Fin 4, actualConvexCoverSet M J σ) = Set.univ := by
  ext p
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact exists_mem_actualConvexCoverSet M J p

/-- The actual index type is finite under the original finite-W hypothesis. -/
theorem finite_actualConvexCoverIndex (M : CoxeterMatrix I) [Finite M.Group]
    (J : Set I) : Finite (RelativeRoot M J → Fin 4) := inferInstance

noncomputable def actualConvexCoverIntersection (M : CoxeterMatrix I) (J : Set I)
    (F : Set (RelativeRoot M J → Fin 4)) : Set (Theorem18.Complement M J) :=
  ⋂ σ ∈ F, actualConvexCoverSet M J σ

noncomputable def actualConvexCoverIntersectionHomeomorph
    (M : CoxeterMatrix I) (J : Set I) (F : Set (RelativeRoot M J → Fin 4)) :
    actualConvexCoverIntersection M J F ≃ₜ
      convexCoverIntersection (E := Theorem18.relativeSubspace J) (actualForms M J) F :=
  (actualComplementHomeomorph M J).subtype (by
    intro p
    simp only [actualConvexCoverIntersection, actualConvexCoverSet,
      convexCoverIntersection, Set.mem_iInter, Set.mem_preimage])

set_option maxHeartbeats 2000000 in
theorem contractibleSpace_actualConvexCoverIntersection
    (M : CoxeterMatrix I) (J : Set I) (F : Set (RelativeRoot M J → Fin 4))
    (hF : F.Nonempty) (hne : (actualConvexCoverIntersection M J F).Nonempty) :
    ContractibleSpace (actualConvexCoverIntersection M J F) := by
  let e := actualConvexCoverIntersectionHomeomorph M J F
  have hne' : (convexCoverIntersection (E := Theorem18.relativeSubspace J)
      (actualForms M J) F).Nonempty := by
    obtain ⟨p, hp⟩ := hne
    exact ⟨(e ⟨p, hp⟩).val, (e ⟨p, hp⟩).property⟩
  exact e.contractibleSpace_iff.mpr
    (contractibleSpace_convexCoverIntersection (E := Theorem18.relativeSubspace J)
      (actualForms M J) F hF hne')

theorem contractibleSpace_finset_actualConvexCoverSet
    (M : CoxeterMatrix I) (J : Set I) (s : Finset (RelativeRoot M J → Fin 4))
    (hs : s.Nonempty) (hne : (⋂ σ ∈ s, actualConvexCoverSet M J σ).Nonempty) :
    ContractibleSpace (⋂ σ ∈ s, actualConvexCoverSet M J σ) := by
  apply contractibleSpace_actualConvexCoverIntersection M J
    (s : Set (RelativeRoot M J → Fin 4))
  · obtain ⟨σ, hσ⟩ := hs
    exact ⟨σ, hσ⟩
  · exact hne

end Actual

end ArtinNormalisers.Asphericity5
