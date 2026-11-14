module

public import ArtinChambers.Arrangement
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Sign-separated barycentric interpolation in the actual complement

Nonnegative barycentric weights may vanish. The scalar argument therefore
uses active signed coefficients, choosing the largest height among the
negative coefficients. After subtracting that height, all terms are
nonnegative and at least one positive term is strict.

The resulting centered real-pair interpolation is quadratic in its weights.
It stays in the actual complexified complement whenever opposite vertex
signs have strictly separated heights. No gallery separation theorem or
asphericity is assumed or asserted here. For incoming ribbon vertices, the
intended geometric height is **minus** the actual degree, so height increases
along a positive source-to-target arrow.

The scalar proof is local authoring from finite-sum positivity and finite
maxima in mathlib; no external GitHub proof of this construction is imported.
-/

@[expose] public section

namespace ArtinNormalisers.Deligne5

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

/-- Only heights across opposite signs must be strictly separated. Repeated
vertices of the same sign may have equal heights. -/
def NegativeBeforePositive (a d : ι → ℝ) : Prop :=
  ∀ i j, a i < 0 → 0 < a j → d i < d j

def PositiveBeforeNegative (a d : ι → ℝ) : Prop :=
  ∀ i j, 0 < a i → a j < 0 → d i < d j

def SignHeightSeparated (a d : ι → ℝ) : Prop :=
  NegativeBeforePositive a d ∨ PositiveBeforeNegative a d

private theorem exists_pos_and_neg_of_sum_zero (b : ι → ℝ)
    (hsum : ∑ i, b i = 0) (hne : ∃ i, b i ≠ 0) :
    (∃ i, 0 < b i) ∧ ∃ i, b i < 0 := by
  constructor
  · by_contra h
    have hnonpos (i : ι) : b i ≤ 0 := le_of_not_gt (fun hi => h ⟨i, hi⟩)
    have hz := (Finset.sum_eq_zero_iff_of_nonpos (fun i (_ : i ∈ Finset.univ) => hnonpos i)).1 hsum
    obtain ⟨i, hi⟩ := hne
    exact hi (hz i (Finset.mem_univ i))
  · by_contra h
    have hnonneg (i : ι) : 0 ≤ b i := le_of_not_gt (fun hi => h ⟨i, hi⟩)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) => hnonneg i)).1 hsum
    obtain ⟨i, hi⟩ := hne
    exact hi (hz i (Finset.mem_univ i))

/-- A zero total of nontrivial signed coefficients has strictly positive
height-weighted total when negative heights precede positive heights. -/
theorem sum_height_mul_pos (b d : ι → ℝ) (hsum : ∑ i, b i = 0)
    (hne : ∃ i, b i ≠ 0) (hsep : NegativeBeforePositive b d) :
    0 < ∑ i, d i * b i := by
  classical
  obtain ⟨⟨j, hj⟩, ⟨k₀, hk₀⟩⟩ := exists_pos_and_neg_of_sum_zero b hsum hne
  let N := Finset.univ.filter (fun i => b i < 0)
  have hN : N.Nonempty := ⟨k₀, by simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]; exact hk₀⟩
  obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image N d hN
  have hbk : b k < 0 := (Finset.mem_filter.1 hk).2
  have hnonneg (i : ι) : 0 ≤ (d i - d k) * b i := by
    by_cases hi : b i < 0
    · have hdi := hmax i (by simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]; exact hi)
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.2 hdi) hi.le
    · by_cases hip : 0 < b i
      · exact (mul_pos (sub_pos.2 (hsep k i hbk hip)) hip).le
      · have hiz : b i = 0 := le_antisymm (le_of_not_gt hip) (le_of_not_gt hi)
        rw [hiz, mul_zero]
  have hstrict : 0 < (d j - d k) * b j := mul_pos (sub_pos.2 (hsep k j hbk hj)) hj
  have hpositive : 0 < ∑ i, (d i - d k) * b i :=
    Finset.sum_pos' (fun i _ => hnonneg i) ⟨j, Finset.mem_univ j, hstrict⟩
  have hcenter : (∑ i, (d i - d k) * b i) = ∑ i, d i * b i := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_zero, sub_zero]
  rwa [hcenter] at hpositive

theorem sum_height_mul_neg (b d : ι → ℝ) (hsum : ∑ i, b i = 0)
    (hne : ∃ i, b i ≠ 0) (hsep : PositiveBeforeNegative b d) :
    (∑ i, d i * b i) < 0 := by
  have h := sum_height_mul_pos b (fun i => -d i) hsum hne (by
    intro i j hi hj
    exact neg_lt_neg (hsep j i hj hi))
  simpa only [neg_mul, Finset.sum_neg_distrib, neg_pos] using h

private theorem weighted_coefficients_nontrivial (w a : ι → ℝ)
    (hw : ∑ i, w i = 1) (ha : ∀ i, a i ≠ 0) : ∃ i, w i * a i ≠ 0 := by
  by_contra h
  have hz (i : ι) : w i = 0 := by
    by_contra hi
    exact h ⟨i, mul_ne_zero hi (ha i)⟩
  have hsum : ∑ i, w i = 0 := by simp only [hz, Finset.sum_const_zero]
  linarith

private theorem negative_of_weighted_negative (w a : ℝ) (hw : 0 ≤ w) (h : w * a < 0) : a < 0 := by
  by_contra hn
  have ha := le_of_not_gt hn
  have := mul_nonneg hw ha
  linarith

private theorem positive_of_weighted_positive (w a : ℝ) (hw : 0 ≤ w) (h : 0 < w * a) : 0 < a := by
  by_contra hn
  have ha := le_of_not_gt hn
  have := mul_nonpos_of_nonneg_of_nonpos hw ha
  linarith

theorem weighted_height_sum_pos (w a d : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hwone : ∑ i, w i = 1) (ha : ∀ i, a i ≠ 0)
    (hzero : ∑ i, w i * a i = 0) (hsep : NegativeBeforePositive a d) :
    0 < ∑ i, w i * d i * a i := by
  have h := sum_height_mul_pos (fun i => w i * a i) d hzero
    (weighted_coefficients_nontrivial w a hwone ha) (by
      intro i j hi hj
      exact hsep i j (negative_of_weighted_negative _ _ (hw i) hi)
        (positive_of_weighted_positive _ _ (hw j) hj))
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem weighted_height_sum_neg (w a d : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hwone : ∑ i, w i = 1) (ha : ∀ i, a i ≠ 0)
    (hzero : ∑ i, w i * a i = 0) (hsep : PositiveBeforeNegative a d) :
    (∑ i, w i * d i * a i) < 0 := by
  have h := sum_height_mul_neg (fun i => w i * a i) d hzero
    (weighted_coefficients_nontrivial w a hwone ha) (by
      intro i j hi hj
      exact hsep i j (positive_of_weighted_positive _ _ (hw i) hi)
        (negative_of_weighted_negative _ _ (hw j) hj))
  convert h using 1
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The scalar nonvanishing conclusion allows zero weights and either
orientation of strict opposite-sign height separation. -/
theorem weighted_height_sum_ne_zero (w a d : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hwone : ∑ i, w i = 1) (ha : ∀ i, a i ≠ 0)
    (hzero : ∑ i, w i * a i = 0) (hsep : SignHeightSeparated a d) :
    (∑ i, w i * d i * a i) ≠ 0 := by
  rcases hsep with hsep | hsep
  · exact ne_of_gt (weighted_height_sum_pos w a d hw hwone ha hzero hsep)
  · exact ne_of_lt (weighted_height_sum_neg w a d hw hwone ha hzero hsep)

section Vector

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

noncomputable def meanHeight (w d : ι → ℝ) : ℝ := ∑ i, w i * d i

noncomputable def realInterpolation (w : ι → ℝ) (c : ι → E) : E := ∑ i, w i • c i

noncomputable def imaginaryInterpolation (w d : ι → ℝ) (c : ι → E) : E :=
  ∑ i, (w i * (d i - meanHeight w d)) • c i

/-- The concrete centered quadratic interpolation in real and imaginary coordinates. -/
noncomputable def signInterpolation (w d : ι → ℝ) (c : ι → E) : E × E :=
  (realInterpolation w c, imaginaryInterpolation w d c)

theorem eval_realInterpolation (f : E →L[ℝ] ℝ) (w : ι → ℝ) (c : ι → E) :
    f (realInterpolation w c) = ∑ i, w i * f (c i) := by
  simp only [realInterpolation, map_sum, map_smul, smul_eq_mul]

theorem eval_imaginaryInterpolation (f : E →L[ℝ] ℝ) (w d : ι → ℝ) (c : ι → E) :
    f (imaginaryInterpolation w d c) =
      (∑ i, w i * d i * f (c i)) - meanHeight w d * ∑ i, w i * f (c i) := by
  simp only [imaginaryInterpolation, map_sum, map_smul, smul_eq_mul]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The concrete quadratic formula lands in the literal complement of the
specified continuous real forms, under proved scalar sign-height hypotheses. -/
theorem signInterpolation_mem_complexComplement {H : Type*} (ℓ : H → E →L[ℝ] ℝ)
    (w d : ι → ℝ) (c : ι → E) (hw : ∀ i, 0 ≤ w i) (hwone : ∑ i, w i = 1)
    (hc : ∀ i, c i ∈ Chamber3.regularSet ℓ)
    (hsep : ∀ h, SignHeightSeparated (fun i => ℓ h (c i)) d) :
    signInterpolation w d c ∈ Chamber3.complexComplementSet ℓ := by
  intro h hzero
  have hx : ∑ i, w i * ℓ h (c i) = 0 := by
    simpa only [signInterpolation, eval_realInterpolation] using hzero.1
  have hy : (∑ i, w i * d i * ℓ h (c i)) = 0 := by
    have he := eval_imaginaryInterpolation (ℓ h) w d c
    rw [hx, mul_zero, sub_zero] at he
    exact he ▸ hzero.2
  exact weighted_height_sum_ne_zero w (fun i => ℓ h (c i)) d hw hwone
    (fun i => hc i h) hx (hsep h) hy

theorem meanHeight_translate (w d : ι → ℝ) (t : ℝ) (hwone : ∑ i, w i = 1) :
    meanHeight w (fun i => d i + t) = meanHeight w d + t := by
  simp only [meanHeight, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hwone, one_mul]

omit [TopologicalSpace E] in
/-- Heights are absolute up to a common translation; no choice of a
simplex-specific recentering enters the formula. -/
theorem signInterpolation_height_translate (w d : ι → ℝ) (c : ι → E) (t : ℝ)
    (hwone : ∑ i, w i = 1) :
    signInterpolation w (fun i => d i + t) c = signInterpolation w d c := by
  apply Prod.ext
  · rfl
  change imaginaryInterpolation w (fun i => d i + t) c = imaginaryInterpolation w d c
  unfold imaginaryInterpolation
  rw [meanHeight_translate w d t hwone]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  ring

noncomputable def vertexWeight (k : ι) : ι → ℝ := by
  classical
  exact fun i => if i = k then 1 else 0

@[simp] theorem meanHeight_vertexWeight (k : ι) (d : ι → ℝ) :
    meanHeight (vertexWeight k) d = d k := by
  classical
  simp [meanHeight, vertexWeight]

omit [TopologicalSpace E] in
/-- At a vertex the imaginary part is zero and the real part is the actual
specified chamber point. -/
@[simp] theorem signInterpolation_vertexWeight (k : ι) (d : ι → ℝ) (c : ι → E) :
    signInterpolation (vertexWeight k) d c = (c k, 0) := by
  classical
  simp [signInterpolation, realInterpolation, imaginaryInterpolation, vertexWeight,
    meanHeight_vertexWeight]

section Aggregation

variable {κ : Type*} [Fintype κ]

/-- Combine the weights of equal labeled vertices, retaining zero-weight
labels. This is the ordinary face and degeneracy aggregation. -/
noncomputable def aggregateWeights (f : ι → κ) (w : ι → ℝ) : κ → ℝ := by
  classical
  exact fun k => ∑ i ∈ Finset.univ.filter (fun i => f i = k), w i

omit [Fintype κ] in
theorem aggregateWeights_nonneg (f : ι → κ) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (k : κ) :
    0 ≤ aggregateWeights f w k := by
  classical
  exact Finset.sum_nonneg (fun i _ => hw i)

theorem sum_aggregateWeights (f : ι → κ) (w : ι → ℝ) :
    (∑ k, aggregateWeights f w k) = ∑ i, w i := by
  classical
  exact Finset.sum_fiberwise Finset.univ f w

omit [TopologicalSpace E] in
theorem realInterpolation_aggregate (f : ι → κ) (w : ι → ℝ) (c : κ → E) :
    realInterpolation (aggregateWeights f w) c = realInterpolation w (fun i => c (f i)) := by
  classical
  unfold realInterpolation aggregateWeights
  calc
    (∑ k, (∑ i ∈ Finset.univ.filter (fun i => f i = k), w i) • c k) =
        ∑ k, ∑ i ∈ Finset.univ.filter (fun i => f i = k), w i • c (f i) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.1 hi).2]
    _ = ∑ i, w i • c (f i) := Finset.sum_fiberwise Finset.univ f _

theorem meanHeight_aggregate (f : ι → κ) (w : ι → ℝ) (d : κ → ℝ) :
    meanHeight (aggregateWeights f w) d = meanHeight w (fun i => d (f i)) := by
  simpa only [meanHeight, realInterpolation, smul_eq_mul] using
    realInterpolation_aggregate (E := ℝ) f w d

omit [TopologicalSpace E] in
theorem imaginaryInterpolation_aggregate (f : ι → κ) (w : ι → ℝ) (d : κ → ℝ) (c : κ → E) :
    imaginaryInterpolation (aggregateWeights f w) d c =
      imaginaryInterpolation w (fun i => d (f i)) (fun i => c (f i)) := by
  unfold imaginaryInterpolation
  rw [meanHeight_aggregate]
  have h := realInterpolation_aggregate f w
    (fun k => (d k - meanHeight w (fun i => d (f i))) • c k)
  simpa only [realInterpolation, smul_smul] using h

omit [TopologicalSpace E] in
/-- Repeating a labeled vertex and then aggregating its weights leaves the
actual quadratic interpolation unchanged, including on boundary faces. -/
theorem signInterpolation_aggregate (f : ι → κ) (w : ι → ℝ) (d : κ → ℝ) (c : κ → E) :
    signInterpolation (aggregateWeights f w) d c =
      signInterpolation w (fun i => d (f i)) (fun i => c (f i)) := by
  apply Prod.ext
  · exact realInterpolation_aggregate f w c
  · exact imaginaryInterpolation_aggregate f w d c

end Aggregation

section Continuity

variable [ContinuousAdd E] [ContinuousSMul ℝ E]

theorem continuous_meanHeight (d : ι → ℝ) : Continuous (fun w : ι → ℝ => meanHeight w d) := by
  apply continuous_finsetSum
  intro i hi
  exact (continuous_apply i).mul continuous_const

theorem continuous_realInterpolation (c : ι → E) :
    Continuous (fun w : ι → ℝ => realInterpolation w c) := by
  apply continuous_finsetSum
  intro i hi
  exact (continuous_apply i).smul continuous_const

theorem continuous_imaginaryInterpolation (d : ι → ℝ) (c : ι → E) :
    Continuous (fun w : ι → ℝ => imaginaryInterpolation w d c) := by
  apply continuous_finsetSum
  intro i hi
  exact ((continuous_apply i).mul (continuous_const.sub (continuous_meanHeight d))).smul continuous_const

theorem continuous_signInterpolation (d : ι → ℝ) (c : ι → E) :
    Continuous (fun w : ι → ℝ => signInterpolation w d c) :=
  (continuous_realInterpolation c).prodMk (continuous_imaginaryInterpolation d c)

end Continuity

end Vector

end ArtinNormalisers.Deligne5
