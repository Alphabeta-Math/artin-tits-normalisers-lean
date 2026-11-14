module

public import ArtinAsphericity.ConvexCover
public import ArtinHomotopy.TubeIntervals
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Module.BigOperators

/-!
# Canonical four-sign cells and their actual geometric carriers

A center uses its real sign whenever nonzero, and otherwise its imaginary
sign. Centers whose cells contain one common point have all their affine
convex combinations in the actual complexified complement. The phase-chamber
interval also gives whole-cell tube carriers. No join or nerve comparison is
assumed by these geometric statements.
-/

@[expose] public section

namespace ArtinNormalisers.Deligne5

open Chamber3 Asphericity5 Homotopy5
open scoped BigOperators Classical

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {H : Type*} (ℓ : H → E →L[ℝ] ℝ)

/-- Real signs have priority, except at a zero real evaluation. -/
noncomputable def canonicalCellChoice (c : ComplexComplement ℓ) : H → Fin 4 := fun h =>
  if ℓ h c.val.1 = 0 then (if 0 < ℓ h c.val.2 then 2 else 3)
  else if 0 < ℓ h c.val.1 then 0 else 1

noncomputable def canonicalCellAmbient (c : ComplexComplement ℓ) : Set (E × E) :=
  convexCell ℓ (canonicalCellChoice ℓ c)

/-- The actual canonical cover member, with its inherited complement topology. -/
noncomputable def canonicalCell (c : ComplexComplement ℓ) : Set (ComplexComplement ℓ) :=
  convexCoverSet ℓ (canonicalCellChoice ℓ c)

theorem canonicalCoordinate_mem_iff (c p : ComplexComplement ℓ) (h : H) :
    p.val ∈ coordinateHalfSpace (ℓ h) (canonicalCellChoice ℓ c h) ↔
      if ℓ h c.val.1 = 0 then
        p.val.2 ∈ signHalfSpace (ℓ h) (decide (0 < ℓ h c.val.2))
      else p.val.1 ∈ signHalfSpace (ℓ h) (decide (0 < ℓ h c.val.1)) := by
  classical
  by_cases hr : ℓ h c.val.1 = 0
  · by_cases hi : 0 < ℓ h c.val.2 <;>
      simp [canonicalCellChoice, coordinateHalfSpace, signHalfSpace, hr, hi]
  · by_cases hp : 0 < ℓ h c.val.1 <;>
      simp [canonicalCellChoice, coordinateHalfSpace, signHalfSpace, hr, hp]

theorem mem_canonicalCell_iff (c p : ComplexComplement ℓ) :
    p ∈ canonicalCell ℓ c ↔ ∀ h,
      if ℓ h c.val.1 = 0 then
        p.val.2 ∈ signHalfSpace (ℓ h) (decide (0 < ℓ h c.val.2))
      else p.val.1 ∈ signHalfSpace (ℓ h) (decide (0 < ℓ h c.val.1)) := by
  change p.val ∈ (⋂ h, coordinateHalfSpace (ℓ h) (canonicalCellChoice ℓ c h)) ↔ _
  simp only [Set.mem_iInter, canonicalCoordinate_mem_iff]

theorem canonicalCell_real {c p : ComplexComplement ℓ} (hp : p ∈ canonicalCell ℓ c)
    {h : H} (hr : ℓ h c.val.1 ≠ 0) :
    p.val.1 ∈ signHalfSpace (ℓ h) (decide (0 < ℓ h c.val.1)) := by
  simpa only [ite_eq_right hr] using (mem_canonicalCell_iff ℓ c p).mp hp h

theorem canonicalCell_imag {c p : ComplexComplement ℓ} (hp : p ∈ canonicalCell ℓ c)
    {h : H} (hr : ℓ h c.val.1 = 0) :
    p.val.2 ∈ signHalfSpace (ℓ h) (decide (0 < ℓ h c.val.2)) := by
  simpa only [ite_eq_left hr] using (mem_canonicalCell_iff ℓ c p).mp hp h

private theorem mem_own_halfspace (f : E →L[ℝ] ℝ) {x : E} (hx : f x ≠ 0) :
    x ∈ signHalfSpace f (decide (0 < f x)) := by
  by_cases hp : 0 < f x
  · simp [signHalfSpace, hp]
  · have hn : f x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hx
    simpa [signHalfSpace, hp] using hn

theorem canonicalCell_self (c : ComplexComplement ℓ) : c ∈ canonicalCell ℓ c := by
  apply (mem_canonicalCell_iff ℓ c c).mpr
  intro h
  by_cases hr : ℓ h c.val.1 = 0
  · rw [ite_eq_left hr]
    exact mem_own_halfspace (ℓ h) (fun hi => c.property h ⟨hr, hi⟩)
  · rw [ite_eq_right hr]
    exact mem_own_halfspace (ℓ h) hr

theorem isOpen_canonicalCell [Finite H] (c : ComplexComplement ℓ) : IsOpen (canonicalCell ℓ c) :=
  isOpen_convexCoverSet ℓ _

theorem convex_canonicalCellAmbient (c : ComplexComplement ℓ) : Convex ℝ (canonicalCellAmbient ℓ c) :=
  convex_convexCell ℓ _

theorem isOpen_canonicalCellAmbient [Finite H] (c : ComplexComplement ℓ) :
    IsOpen (canonicalCellAmbient ℓ c) := isOpen_convexCell ℓ _

theorem canonicalCellAmbient_subset_complement (c : ComplexComplement ℓ) :
    canonicalCellAmbient ℓ c ⊆ complexComplementSet ℓ := convexCell_subset_complexComplementSet ℓ _

theorem iUnion_canonicalCell : (⋃ c : ComplexComplement ℓ, canonicalCell ℓ c) = Set.univ := by
  ext p
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  exact ⟨p, canonicalCell_self ℓ p⟩

private theorem product_pos_of_halfspace (f : E →L[ℝ] ℝ) {x y : E}
    (hx : f x ≠ 0) (hy : y ∈ signHalfSpace f (decide (0 < f x))) : 0 < f x * f y := by
  by_cases hp : 0 < f x
  · exact mul_pos hp (by simpa [signHalfSpace, hp] using hy)
  · have hn : f x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hx
    exact mul_pos_of_neg_of_neg hn (by simpa [signHalfSpace, hp] using hy)

theorem canonicalCell_real_product_pos {c p : ComplexComplement ℓ}
    (hp : p ∈ canonicalCell ℓ c) {h : H} (hr : ℓ h c.val.1 ≠ 0) :
    0 < ℓ h c.val.1 * ℓ h p.val.1 :=
  product_pos_of_halfspace (ℓ h) hr (canonicalCell_real ℓ hp hr)

theorem canonicalCell_real_product_nonneg {c p : ComplexComplement ℓ}
    (hp : p ∈ canonicalCell ℓ c) (h : H) : 0 ≤ ℓ h c.val.1 * ℓ h p.val.1 := by
  by_cases hr : ℓ h c.val.1 = 0
  · simp only [hr, zero_mul, le_refl]
  · exact (canonicalCell_real_product_pos ℓ hp hr).le

theorem canonicalCell_imag_product_pos {c p : ComplexComplement ℓ}
    (hp : p ∈ canonicalCell ℓ c) {h : H} (hr : ℓ h c.val.1 = 0) :
    0 < ℓ h c.val.2 * ℓ h p.val.2 :=
  product_pos_of_halfspace (ℓ h) (fun hi => c.property h ⟨hr, hi⟩) (canonicalCell_imag ℓ hp hr)

section ConvexCombinations

variable {ι : Type*} [Fintype ι]

/-- Both literal real coordinates of an affine combination of actual centers. -/
def centerCombination (c : ι → ComplexComplement ℓ) (w : ι → ℝ) : E × E :=
  (∑ i, w i • (c i).val.1, ∑ i, w i • (c i).val.2)

/-- Common canonical-cell incidence prevents simultaneous vanishing under
every nonnegative affine combination, including zero coefficients. -/
theorem centerCombination_mem_complement_of_active (c : ι → ComplexComplement ℓ)
    (p : ComplexComplement ℓ) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwone : ∑ i, w i = 1)
    (hp : ∀ i, w i ≠ 0 → p ∈ canonicalCell ℓ (c i)) :
    centerCombination ℓ c w ∈ complexComplementSet ℓ := by
  classical
  intro h hz
  have hreal : ∑ i, w i * ℓ h (c i).val.1 = 0 := by
    simpa only [centerCombination, map_sum, map_smul, smul_eq_mul] using hz.1
  have hnonneg (i : ι) : 0 ≤ w i * (ℓ h (c i).val.1 * ℓ h p.val.1) := by
    by_cases hi : w i = 0
    · simp only [hi, zero_mul, le_refl]
    · exact mul_nonneg (hw i) (canonicalCell_real_product_nonneg ℓ (hp i hi) h)
  have hsumzero : ∑ i, w i * (ℓ h (c i).val.1 * ℓ h p.val.1) = 0 := by
    simp only [← mul_assoc, ← Finset.sum_mul, hreal, zero_mul]
  have hterms := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp hsumzero
  have active_zero (i : ι) (hi : w i ≠ 0) : ℓ h (c i).val.1 = 0 := by
    by_contra hn
    have hpos := mul_pos (lt_of_le_of_ne (hw i) (Ne.symm hi))
      (canonicalCell_real_product_pos ℓ (hp i hi) hn)
    exact (ne_of_gt hpos) (hterms i (Finset.mem_univ i))
  have hactive : ∃ i, 0 < w i := by
    by_contra hn
    have hall (i : ι) : w i = 0 := le_antisymm
      (le_of_not_gt (fun hi => hn ⟨i, hi⟩)) (hw i)
    have hzero : ∑ i, w i = 0 := by simp only [hall, Finset.sum_const_zero]
    linarith
  obtain ⟨j, hj⟩ := hactive
  have himnonneg (i : ι) : 0 ≤ w i * (ℓ h (c i).val.2 * ℓ h p.val.2) := by
    by_cases hi : w i = 0
    · simp only [hi, zero_mul, le_refl]
    · exact (mul_pos (lt_of_le_of_ne (hw i) (Ne.symm hi))
        (canonicalCell_imag_product_pos ℓ (hp i hi) (active_zero i hi))).le
  have himpos : 0 < ∑ i, w i * (ℓ h (c i).val.2 * ℓ h p.val.2) :=
    Finset.sum_pos' (fun i _ => himnonneg i)
      ⟨j, Finset.mem_univ j, mul_pos hj
        (canonicalCell_imag_product_pos ℓ (hp j (ne_of_gt hj)) (active_zero j (ne_of_gt hj)))⟩
  have himzero : ∑ i, w i * ℓ h (c i).val.2 = 0 := by
    simpa only [centerCombination, map_sum, map_smul, smul_eq_mul] using hz.2
  have hzprod : ∑ i, w i * (ℓ h (c i).val.2 * ℓ h p.val.2) = 0 := by
    simp only [← mul_assoc, ← Finset.sum_mul, himzero, zero_mul]
  exact (ne_of_gt himpos) hzprod

theorem centerCombination_mem_complement (c : ι → ComplexComplement ℓ) (p : ComplexComplement ℓ)
    (hp : ∀ i, p ∈ canonicalCell ℓ (c i)) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwone : ∑ i, w i = 1) :
    centerCombination ℓ c w ∈ complexComplementSet ℓ :=
  centerCombination_mem_complement_of_active ℓ c p w hw hwone (fun i _ => hp i)

/-- The common point itself can be added as an extra center. -/
theorem centerCombination_with_commonPoint_mem (c : ι → ComplexComplement ℓ)
    (p : ComplexComplement ℓ) (hp : ∀ i, p ∈ canonicalCell ℓ (c i))
    (w : Option ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hwone : ∑ i, w i = 1) :
    centerCombination ℓ (fun o : Option ι => o.elim p c) w ∈ complexComplementSet ℓ := by
  apply centerCombination_mem_complement ℓ _ p _ w hw hwone
  intro o
  cases o with
  | none => exact canonicalCell_self ℓ p
  | some i => exact hp i

/-- Straight affine return from the common point to any such barycenter
stays in the actual complexified complement. -/
theorem lineMap_commonPoint_centerCombination_mem_of_active (c : ι → ComplexComplement ℓ)
    (p : ComplexComplement ℓ)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hwone : ∑ i, w i = 1)
    (hp : ∀ i, w i ≠ 0 → p ∈ canonicalCell ℓ (c i))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AffineMap.lineMap p.val (centerCombination ℓ c w) t ∈ complexComplementSet ℓ := by
  let v : Option ι → ℝ := fun o => o.elim (1 - t) (fun i => t * w i)
  have hv : ∀ o, 0 ≤ v o := by
    intro o
    cases o with
    | none => exact sub_nonneg.mpr ht.2
    | some i => exact mul_nonneg ht.1 (hw i)
  have hvone : ∑ o, v o = 1 := by
    simp only [v, Fintype.sum_option, Option.elim_none, Option.elim_some, ← Finset.mul_sum, hwone, mul_one]
    ring
  have hmem : ∀ o : Option ι, v o ≠ 0 →
      p ∈ canonicalCell ℓ (o.elim p c) := by
    intro o ho
    cases o with
    | none => exact canonicalCell_self ℓ p
    | some i =>
      apply hp i
      intro hi
      apply ho
      change t * w i = 0
      rw [hi, mul_zero]
  have h := centerCombination_mem_complement_of_active ℓ (fun o : Option ι => o.elim p c)
    p v hv hvone hmem
  convert h using 1
  ext <;> simp only [centerCombination, v, Fintype.sum_option, Option.elim_none, Option.elim_some,
    AffineMap.lineMap_apply_module, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    mul_smul, Finset.smul_sum]

theorem lineMap_commonPoint_centerCombination_mem (c : ι → ComplexComplement ℓ)
    (p : ComplexComplement ℓ) (hp : ∀ i, p ∈ canonicalCell ℓ (c i))
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hwone : ∑ i, w i = 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    AffineMap.lineMap p.val (centerCombination ℓ c w) t ∈ complexComplementSet ℓ :=
  lineMap_commonPoint_centerCombination_mem_of_active ℓ c p w hw hwone (fun i _ => hp i) ht

noncomputable def centerCombinationPoint (c : ι → ComplexComplement ℓ) (p : ComplexComplement ℓ)
    (hp : ∀ i, p ∈ canonicalCell ℓ (c i)) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwone : ∑ i, w i = 1) : ComplexComplement ℓ :=
  ⟨centerCombination ℓ c w, centerCombination_mem_complement ℓ c p hp w hw hwone⟩

/-- The actual straight return path, with actual complement endpoints and topology. -/
noncomputable def centerCombinationReturnPath [ContinuousAdd E] [ContinuousSMul ℝ E]
    (c : ι → ComplexComplement ℓ) (p : ComplexComplement ℓ)
    (hp : ∀ i, p ∈ canonicalCell ℓ (c i)) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwone : ∑ i, w i = 1) :
    Path p (centerCombinationPoint ℓ c p hp w hw hwone) where
  toFun t := ⟨AffineMap.lineMap p.val (centerCombination ℓ c w) (t : ℝ),
    lineMap_commonPoint_centerCombination_mem ℓ c p hp w hw hwone t.property⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  source' := by apply Subtype.ext; simp
  target' := by apply Subtype.ext; simp [centerCombinationPoint]

end ConvexCombinations

section ChamberCarriers

variable [Finite H]

/-- The upper phase chamber prioritizes nonzero imaginary signs, taking
the lower phase's real sign only where the imaginary evaluation vanishes. -/
noncomputable def phaseUpperChamber (p : ComplexComplement ℓ) : Chamber ℓ :=
  faceChamber ℓ p.val.2 (tubeLowerChamber ℓ p)

private theorem halfspace_sign (f : E →L[ℝ] ℝ) {x : E} {s : Bool}
    (hx : x ∈ signHalfSpace f s) : s = decide (0 < f x) := by
  cases s
  · have hn : f x < 0 := hx
    simp only [decide_eq_false (not_lt_of_ge hn.le)]
  · have hp : 0 < f x := hx
    simp only [decide_eq_true hp]

theorem tubeLowerChamber_signs_real (p : ComplexComplement ℓ) {h : H}
    (hr : ℓ h p.val.1 ≠ 0) : (tubeLowerChamber ℓ p).signs h = decide (0 < ℓ h p.val.1) :=
  faceChamber_signs_nonzero ℓ p.val.1 (tubeWitness ℓ p) hr

theorem tubeLowerChamber_signs_imag (p : ComplexComplement ℓ) {h : H}
    (hr : ℓ h p.val.1 = 0) : (tubeLowerChamber ℓ p).signs h = decide (0 < ℓ h p.val.2) := by
  rw [tubeLowerChamber, faceChamber_signs_zero ℓ p.val.1 (tubeWitness ℓ p) hr]
  exact halfspace_sign (ℓ h) (mem_tubeWitness ℓ p h hr)

theorem canonicalCell_lower_eq_lower {c p : ComplexComplement ℓ}
    (hp : p ∈ canonicalCell ℓ c) {h : H} (hr : ℓ h c.val.1 ≠ 0) :
    (tubeLowerChamber ℓ c).signs h = (tubeLowerChamber ℓ p).signs h := by
  have hm := canonicalCell_real ℓ hp hr
  rw [tubeLowerChamber_signs_real ℓ c hr,
    tubeLowerChamber_signs_real ℓ p (signHalfSpace_nonzero hm)]
  exact halfspace_sign (ℓ h) hm

theorem canonicalCell_lower_eq_upper {c p : ComplexComplement ℓ}
    (hp : p ∈ canonicalCell ℓ c) {h : H} (hr : ℓ h c.val.1 = 0) :
    (tubeLowerChamber ℓ c).signs h = (phaseUpperChamber ℓ p).signs h := by
  have hm := canonicalCell_imag ℓ hp hr
  rw [tubeLowerChamber_signs_imag ℓ c hr]
  change decide (0 < ℓ h c.val.2) = (faceChamber ℓ p.val.2 (tubeLowerChamber ℓ p)).signs h
  rw [faceChamber_signs_nonzero ℓ p.val.2 _ (signHalfSpace_nonzero hm)]
  exact halfspace_sign (ℓ h) hm

/-- Canonical-cell centers have their actual lower phase chamber in the
stated interval at every common point. -/
theorem canonicalCell_chamberBetween {c p : ComplexComplement ℓ}
    (hp : p ∈ canonicalCell ℓ c) :
    ChamberBetween (tubeLowerChamber ℓ p) (tubeLowerChamber ℓ c) (phaseUpperChamber ℓ p) := by
  intro h hshared
  by_cases hr : ℓ h c.val.1 = 0
  · exact (canonicalCell_lower_eq_upper ℓ hp hr).trans hshared.symm
  · exact canonicalCell_lower_eq_lower ℓ hp hr

private theorem bool_upper_interval {a c d : Bool} (h₁ : a = d → c = a)
    (h₂ : a = c → d = a) : d = c := by
  cases a <;> cases c <;> cases d <;> simp_all

/-- An upper bound of the center chamber in the phase interval carries the
whole actual canonical cell, not merely its chosen center or common point. -/
theorem canonicalCell_subset_tubeSet {c p : ComplexComplement ℓ}
    (hp : p ∈ canonicalCell ℓ c) (D : Chamber ℓ)
    (h₁ : ChamberBetween (tubeLowerChamber ℓ p) (tubeLowerChamber ℓ c) D)
    (h₂ : ChamberBetween (tubeLowerChamber ℓ p) D (phaseUpperChamber ℓ p)) :
    canonicalCell ℓ c ⊆ tubeSet D := by
  intro x hx h hxreal
  have hr : ℓ h c.val.1 = 0 := by
    by_contra hn
    exact signHalfSpace_nonzero (canonicalCell_real ℓ hx hn) hxreal
  have hcb := canonicalCell_lower_eq_upper ℓ hp hr
  have hd : D.signs h = (tubeLowerChamber ℓ c).signs h :=
    bool_upper_interval (h₁ h) (fun hac => h₂ h (hac.trans hcb))
  rw [hd, tubeLowerChamber_signs_imag ℓ c hr]
  exact canonicalCell_imag ℓ hx hr

end ChamberCarriers

end ArtinNormalisers.Deligne5
