module

public import ArtinDeligne.CanonicalCells

/-!
# Realized canonical cells and affine tube carriers

The cover index consists only of four-sign selectors realized by actual
points. Its cells retain the original complement topology. The affine
carrier statements use common canonical-cell incidence on active weights;
zero weights require no incidence or tube membership hypotheses.
-/

@[expose] public section

namespace ArtinNormalisers.Deligne5

open Chamber3 Asphericity5 Homotopy5
open scoped BigOperators Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {H : Type*} (ℓ : H → E →L[ℝ] ℝ)

noncomputable def canonicalSelector (p : ComplexComplement ℓ) : H → Fin 4 :=
  canonicalCellChoice ℓ p

/-- Only sign types realized by actual complement points are indices. -/
def CanonicalType := {σ : H → Fin 4 // ∃ p : ComplexComplement ℓ, canonicalSelector ℓ p = σ}

instance [Finite H] : Finite (CanonicalType ℓ) := inferInstanceAs (Finite (Subtype _))

noncomputable def canonicalCenter (σ : CanonicalType ℓ) : ComplexComplement ℓ :=
  Classical.choose σ.property

@[simp] theorem canonicalSelector_center (σ : CanonicalType ℓ) :
    canonicalSelector ℓ (canonicalCenter ℓ σ) = σ.val := Classical.choose_spec σ.property

noncomputable def canonicalTypeOfPoint (p : ComplexComplement ℓ) : CanonicalType ℓ :=
  ⟨canonicalSelector ℓ p, p, rfl⟩

noncomputable def canonicalTypeSet (σ : CanonicalType ℓ) : Set (ComplexComplement ℓ) :=
  canonicalCell ℓ (canonicalCenter ℓ σ)

theorem canonicalTypeSet_eq_convexCoverSet (σ : CanonicalType ℓ) :
    canonicalTypeSet ℓ σ = convexCoverSet ℓ σ.val := by
  change convexCoverSet ℓ (canonicalSelector ℓ (canonicalCenter ℓ σ)) = _
  rw [canonicalSelector_center]

@[simp] theorem canonicalCenter_mem (σ : CanonicalType ℓ) :
    canonicalCenter ℓ σ ∈ canonicalTypeSet ℓ σ := canonicalCell_self ℓ _

theorem canonicalTypeSet_nonempty (σ : CanonicalType ℓ) :
    (canonicalTypeSet ℓ σ).Nonempty := ⟨_, canonicalCenter_mem ℓ σ⟩

theorem isOpen_canonicalTypeSet [Finite H] (σ : CanonicalType ℓ) :
    IsOpen (canonicalTypeSet ℓ σ) := isOpen_canonicalCell ℓ _

theorem convex_canonicalTypeSet_ambient (σ : CanonicalType ℓ) :
    Convex ℝ (canonicalCellAmbient ℓ (canonicalCenter ℓ σ)) := convex_canonicalCellAmbient ℓ _

theorem mem_canonicalTypeOfPoint (p : ComplexComplement ℓ) :
    p ∈ canonicalTypeSet ℓ (canonicalTypeOfPoint ℓ p) := by
  rw [canonicalTypeSet_eq_convexCoverSet]
  exact canonicalCell_self ℓ p

theorem iUnion_canonicalTypeSet : (⋃ σ : CanonicalType ℓ, canonicalTypeSet ℓ σ) = Set.univ := by
  ext p
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨canonicalTypeOfPoint ℓ p, mem_canonicalTypeOfPoint ℓ p⟩

theorem contractibleSpace_canonicalTypeSet [ContinuousAdd E] [ContinuousSMul ℝ E]
    (σ : CanonicalType ℓ) : ContractibleSpace (canonicalTypeSet ℓ σ) := by
  have heq : canonicalTypeSet ℓ σ = convexCoverIntersection ℓ {σ.val} := by
    rw [canonicalTypeSet_eq_convexCoverSet]
    ext p
    simp [convexCoverIntersection]
  rw [heq]
  apply contractibleSpace_convexCoverIntersection ℓ {σ.val} (Set.singleton_nonempty _)
  rw [← heq]
  exact canonicalTypeSet_nonempty ℓ σ


theorem isPathConnected_canonicalTypeSet [ContinuousAdd E] [ContinuousSMul ℝ E]
    (σ : CanonicalType ℓ) : IsPathConnected (canonicalTypeSet ℓ σ) := by
  let := contractibleSpace_canonicalTypeSet ℓ σ
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

theorem isConnected_canonicalTypeSet [ContinuousAdd E] [ContinuousSMul ℝ E]
    (σ : CanonicalType ℓ) : IsConnected (canonicalTypeSet ℓ σ) :=
  (isPathConnected_canonicalTypeSet ℓ σ).isConnected

noncomputable def canonicalTypeChamber [Finite H] (σ : CanonicalType ℓ) : Chamber ℓ :=
  tubeLowerChamber ℓ (canonicalCenter ℓ σ)

theorem canonicalTypeSet_subset_tubeSet [Finite H] (σ : CanonicalType ℓ) :
    canonicalTypeSet ℓ σ ⊆ tubeSet (canonicalTypeChamber ℓ σ) := by
  intro p hp h hr
  have hcenter : ℓ h (canonicalCenter ℓ σ).val.1 = 0 := by
    by_contra hn
    exact signHalfSpace_nonzero (canonicalCell_real ℓ hp hn) hr
  change p.val.2 ∈ signHalfSpace (ℓ h) ((tubeLowerChamber ℓ (canonicalCenter ℓ σ)).signs h)
  rw [tubeLowerChamber_signs_imag ℓ _ hcenter]
  exact canonicalCell_imag ℓ hp hcenter

section AffineCarriers

variable {ι : Type*} [Fintype ι]

/-- Real cancellation at an overlap forces every active center onto that
real wall. This is stronger than cancellation in the ambient complement. -/
theorem active_center_real_eq_zero (c : ι → ComplexComplement ℓ) (p : ComplexComplement ℓ)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hp : ∀ i, w i ≠ 0 → p ∈ canonicalCell ℓ (c i))
    {h : H} (hz : ℓ h (centerCombination ℓ c w).1 = 0)
    (i : ι) (hi : w i ≠ 0) : ℓ h (c i).val.1 = 0 := by
  classical
  have hreal : ∑ i, w i * ℓ h (c i).val.1 = 0 := by
    simpa only [centerCombination, map_sum, map_smul, smul_eq_mul] using hz
  have hnonneg (j : ι) : 0 ≤ w j * (ℓ h (c j).val.1 * ℓ h p.val.1) := by
    by_cases hj : w j = 0
    · simp only [hj, zero_mul, le_refl]
    · exact mul_nonneg (hw j) (canonicalCell_real_product_nonneg ℓ (hp j hj) h)
  have hsumzero : ∑ j, w j * (ℓ h (c j).val.1 * ℓ h p.val.1) = 0 := by
    simp only [← mul_assoc, ← Finset.sum_mul, hreal, zero_mul]
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp hsumzero
  by_contra hn
  have hpos := mul_pos (lt_of_le_of_ne (hw i) (Ne.symm hi))
    (canonicalCell_real_product_pos ℓ (hp i hi) hn)
  exact (ne_of_gt hpos) (hterms i (Finset.mem_univ i))

/-- A convex combination of centers carried by one tube remains in that
tube whenever their active canonical cells have a common point. -/
theorem centerCombination_mem_tubeSet_of_active (c : ι → ComplexComplement ℓ)
    (p : ComplexComplement ℓ) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwone : ∑ i, w i = 1)
    (hp : ∀ i, w i ≠ 0 → p ∈ canonicalCell ℓ (c i)) (D : Chamber ℓ)
    (hD : ∀ i, w i ≠ 0 → c i ∈ tubeSet D) :
    (⟨centerCombination ℓ c w,
      centerCombination_mem_complement_of_active ℓ c p w hw hwone hp⟩ : ComplexComplement ℓ)
      ∈ tubeSet D := by
  classical
  intro h hz
  have hactive : ∃ i, 0 < w i := by
    by_contra hn
    have hall (i : ι) : w i = 0 := le_antisymm
      (le_of_not_gt (fun hi => hn ⟨i, hi⟩)) (hw i)
    have hzero : ∑ i, w i = 0 := by simp only [hall, Finset.sum_const_zero]
    linarith
  obtain ⟨j, hj⟩ := hactive
  have hsign (i : ι) (hi : w i ≠ 0) :
      (c i).val.2 ∈ signHalfSpace (ℓ h) (D.signs h) :=
    hD i hi h (active_center_real_eq_zero ℓ c p w hw hp hz i hi)
  have hsum : ℓ h (centerCombination ℓ c w).2 = ∑ i, w i * ℓ h (c i).val.2 := by
    simp only [centerCombination, map_sum, map_smul, smul_eq_mul]
  cases hs : D.signs h
  · change ℓ h (centerCombination ℓ c w).2 < 0
    rw [hsum]
    apply Finset.sum_neg' _ ⟨j, Finset.mem_univ j, mul_neg_of_pos_of_neg hj (by
      simpa [signHalfSpace, hs] using hsign j (ne_of_gt hj))⟩
    intro i _
    by_cases hi : w i = 0
    · simp only [hi, zero_mul, le_refl]
    · exact (mul_neg_of_pos_of_neg (lt_of_le_of_ne (hw i) (Ne.symm hi))
        (by simpa [signHalfSpace, hs] using hsign i hi)).le
  · change 0 < ℓ h (centerCombination ℓ c w).2
    rw [hsum]
    apply Finset.sum_pos' _ ⟨j, Finset.mem_univ j, mul_pos hj (by
      simpa [signHalfSpace, hs] using hsign j (ne_of_gt hj))⟩
    intro i _
    by_cases hi : w i = 0
    · simp only [hi, zero_mul, le_refl]
    · exact (mul_pos (lt_of_le_of_ne (hw i) (Ne.symm hi))
        (by simpa [signHalfSpace, hs] using hsign i hi)).le


/-- The entire affine return is carried by a common tube, including at
zero barycentric coordinates and either endpoint of the segment. -/
theorem lineMap_commonPoint_centerCombination_mem_tubeSet_of_active
    (c : ι → ComplexComplement ℓ) (p : ComplexComplement ℓ) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwone : ∑ i, w i = 1)
    (hp : ∀ i, w i ≠ 0 → p ∈ canonicalCell ℓ (c i)) (D : Chamber ℓ)
    (hpD : p ∈ tubeSet D) (hD : ∀ i, w i ≠ 0 → c i ∈ tubeSet D)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (⟨AffineMap.lineMap p.val (centerCombination ℓ c w) t,
      lineMap_commonPoint_centerCombination_mem_of_active ℓ c p w hw hwone hp ht⟩ :
      ComplexComplement ℓ) ∈ tubeSet D := by
  let v : Option ι → ℝ := fun o => o.elim (1 - t) (fun i => t * w i)
  have hv : ∀ o, 0 ≤ v o := by
    intro o
    cases o with
    | none => exact sub_nonneg.mpr ht.2
    | some i => exact mul_nonneg ht.1 (hw i)
  have hvone : ∑ o, v o = 1 := by
    simp only [v, Fintype.sum_option, Option.elim_none, Option.elim_some,
      ← Finset.mul_sum, hwone, mul_one]
    ring
  have hi (i : ι) (hi : v (some i) ≠ 0) : w i ≠ 0 := by
    intro hz
    apply hi
    change t * w i = 0
    rw [hz, mul_zero]
  have hcell : ∀ o : Option ι, v o ≠ 0 → p ∈ canonicalCell ℓ (o.elim p c) := by
    intro o ho
    cases o with
    | none => exact canonicalCell_self ℓ p
    | some i => exact hp i (hi i ho)
  have htube : ∀ o : Option ι, v o ≠ 0 → o.elim p c ∈ tubeSet D := by
    intro o ho
    cases o with
    | none => exact hpD
    | some i => exact hD i (hi i ho)
  have heq : AffineMap.lineMap p.val (centerCombination ℓ c w) t =
      centerCombination ℓ (fun o : Option ι => o.elim p c) v := by
    ext <;> simp only [centerCombination, v, Fintype.sum_option, Option.elim_none,
      Option.elim_some, AffineMap.lineMap_apply_module, Prod.fst_add, Prod.snd_add,
      Prod.smul_fst, Prod.smul_snd, mul_smul, Finset.smul_sum]
  have hout := centerCombination_mem_tubeSet_of_active ℓ
    (fun o : Option ι => o.elim p c) p v hv hvone hcell D htube
  have heq' : (⟨AffineMap.lineMap p.val (centerCombination ℓ c w) t,
      lineMap_commonPoint_centerCombination_mem_of_active ℓ c p w hw hwone hp ht⟩ :
      ComplexComplement ℓ) =
      ⟨centerCombination ℓ (fun o : Option ι => o.elim p c) v,
        centerCombination_mem_complement_of_active ℓ _ p v hv hvone hcell⟩ :=
    Subtype.ext heq
  rw [heq']
  exact hout


theorem centerCombinationPoint_mem_tubeSet (c : ι → ComplexComplement ℓ)
    (p : ComplexComplement ℓ) (hp : ∀ i, p ∈ canonicalCell ℓ (c i))
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hwone : ∑ i, w i = 1)
    (D : Chamber ℓ) (hD : ∀ i, w i ≠ 0 → c i ∈ tubeSet D) :
    centerCombinationPoint ℓ c p hp w hw hwone ∈ tubeSet D :=
  centerCombination_mem_tubeSet_of_active ℓ c p w hw hwone (fun i _ => hp i) D hD

theorem centerCombinationReturnPath_mem_tubeSet [ContinuousAdd E] [ContinuousSMul ℝ E]
    (c : ι → ComplexComplement ℓ) (p : ComplexComplement ℓ)
    (hp : ∀ i, p ∈ canonicalCell ℓ (c i)) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwone : ∑ i, w i = 1)
    (D : Chamber ℓ) (hpD : p ∈ tubeSet D)
    (hD : ∀ i, w i ≠ 0 → c i ∈ tubeSet D) (t : unitInterval) :
    centerCombinationReturnPath ℓ c p hp w hw hwone t ∈ tubeSet D :=
  lineMap_commonPoint_centerCombination_mem_tubeSet_of_active ℓ c p w hw hwone
    (fun i _ => hp i) D hpD hD t.property

end AffineCarriers


section Actual

variable {I : Type*}

abbrev actualCanonicalType (M : CoxeterMatrix I) (J : Set I) :=
  CanonicalType (E := Theorem18.relativeSubspace J) (actualForms M J)


theorem finite_actualCanonicalType (M : CoxeterMatrix I) [Finite M.Group] (J : Set I) :
    Finite (actualCanonicalType M J) := inferInstance

noncomputable def actualCanonicalCenter (M : CoxeterMatrix I) (J : Set I)
    (σ : actualCanonicalType M J) : Theorem18.Complement M J :=
  (actualComplementHomeomorph M J).symm (canonicalCenter (E := Theorem18.relativeSubspace J) (actualForms M J) σ)

noncomputable def actualCanonicalTypeSet (M : CoxeterMatrix I) (J : Set I)
    (σ : actualCanonicalType M J) : Set (Theorem18.Complement M J) :=
  actualComplementHomeomorph M J ⁻¹' canonicalTypeSet (E := Theorem18.relativeSubspace J) (actualForms M J) σ

@[simp] theorem actualCanonicalCenter_mem (M : CoxeterMatrix I) (J : Set I)
    (σ : actualCanonicalType M J) :
    actualCanonicalCenter M J σ ∈ actualCanonicalTypeSet M J σ := by
  change actualComplementHomeomorph M J
    ((actualComplementHomeomorph M J).symm (canonicalCenter
      (E := Theorem18.relativeSubspace J) (actualForms M J) σ)) ∈
        canonicalTypeSet (E := Theorem18.relativeSubspace J) (actualForms M J) σ
  rw [Homeomorph.apply_symm_apply]
  exact canonicalCenter_mem _ σ

theorem actualCanonicalTypeSet_nonempty (M : CoxeterMatrix I) (J : Set I)
    (σ : actualCanonicalType M J) : (actualCanonicalTypeSet M J σ).Nonempty :=
  ⟨_, actualCanonicalCenter_mem M J σ⟩

theorem isOpen_actualCanonicalTypeSet (M : CoxeterMatrix I) [Finite M.Group]
    (J : Set I) (σ : actualCanonicalType M J) : IsOpen (actualCanonicalTypeSet M J σ) :=
  (isOpen_canonicalTypeSet (E := Theorem18.relativeSubspace J) (actualForms M J) σ).preimage
    (actualComplementHomeomorph M J).continuous

noncomputable def actualCanonicalTypeSetHomeomorph (M : CoxeterMatrix I) (J : Set I)
    (σ : actualCanonicalType M J) : actualCanonicalTypeSet M J σ ≃ₜ
      canonicalTypeSet (E := Theorem18.relativeSubspace J) (actualForms M J) σ :=
  (actualComplementHomeomorph M J).subtype (fun _ => Iff.rfl)

theorem contractibleSpace_actualCanonicalTypeSet (M : CoxeterMatrix I) (J : Set I)
    (σ : actualCanonicalType M J) : ContractibleSpace (actualCanonicalTypeSet M J σ) :=
  (actualCanonicalTypeSetHomeomorph M J σ).contractibleSpace_iff.mpr
    (contractibleSpace_canonicalTypeSet (E := Theorem18.relativeSubspace J) (actualForms M J) σ)


theorem isPathConnected_actualCanonicalTypeSet (M : CoxeterMatrix I) (J : Set I)
    (σ : actualCanonicalType M J) : IsPathConnected (actualCanonicalTypeSet M J σ) := by
  let := contractibleSpace_actualCanonicalTypeSet M J σ
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

theorem isConnected_actualCanonicalTypeSet (M : CoxeterMatrix I) (J : Set I)
    (σ : actualCanonicalType M J) : IsConnected (actualCanonicalTypeSet M J σ) :=
  (isPathConnected_actualCanonicalTypeSet M J σ).isConnected

noncomputable def actualCanonicalTypeChamber (M : CoxeterMatrix I) [Finite M.Group]
    (J : Set I) (σ : actualCanonicalType M J) : ActualChamber M J :=
  canonicalTypeChamber (E := Theorem18.relativeSubspace J) (actualForms M J) σ

theorem actualCanonicalTypeSet_subset_actualTubeSet (M : CoxeterMatrix I) [Finite M.Group]
    (J : Set I) (σ : actualCanonicalType M J) :
    actualCanonicalTypeSet M J σ ⊆ actualTubeSet M J (actualCanonicalTypeChamber M J σ) := by
  intro p hp
  exact canonicalTypeSet_subset_tubeSet (E := Theorem18.relativeSubspace J) (actualForms M J) σ hp

theorem iUnion_actualCanonicalTypeSet (M : CoxeterMatrix I) (J : Set I) :
    (⋃ σ : actualCanonicalType M J, actualCanonicalTypeSet M J σ) = Set.univ := by
  ext p
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨canonicalTypeOfPoint (E := Theorem18.relativeSubspace J) (actualForms M J) (actualComplementHomeomorph M J p),
    mem_canonicalTypeOfPoint _ _⟩

end Actual

end ArtinNormalisers.Deligne5
