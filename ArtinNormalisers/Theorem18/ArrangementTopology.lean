module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Algebra.Module.Submodule.Union
public import ArtinNormalisers.Theorem18.Geometry

/-!
# Path connectedness of finite real arrangement complexifications

The complement is the actual subset of real pairs on which no selected linear
functional vanishes in both coordinates. Complex affine lines reduce paths to
the complement of finitely many points of the complex parameter plane.
No fundamental-group or asphericity assertion is assumed or proved here.
-/

set_option autoImplicit false

@[expose] public section

namespace ArtinNormalisers.Theorem18

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Evaluation of a real pair as a complex number. -/
def pairEvaluation (f : E →ₗ[ℝ] ℝ) (p : E × E) : ℂ := ⟨f p.1, f p.2⟩

/-- The actual real-pair complement of a family of complexified kernels. -/
def pairComplement {ι : Type*} (f : ι → E →ₗ[ℝ] ℝ) : Set (E × E) :=
  {p | ∀ a, pairEvaluation (f a) p ≠ 0}

@[simp]
theorem mem_pairComplement_iff {ι : Type*} (f : ι → E →ₗ[ℝ] ℝ) (p : E × E) :
    p ∈ pairComplement f ↔ ∀ a, ¬(f a p.1 = 0 ∧ f a p.2 = 0) := by
  simp [pairComplement, pairEvaluation, Complex.ext_iff]

/-- The complex affine line through two real pairs, in real coordinates. -/
def pairAffineLine (p q : E × E) (z : ℂ) : E × E :=
  (p.1 + z.re • (q.1 - p.1) + z.im • (-(q.2 - p.2)),
   p.2 + z.im • (q.1 - p.1) + z.re • (q.2 - p.2))

@[simp]
theorem pairAffineLine_zero (p q : E × E) : pairAffineLine p q 0 = p := by
  simp [pairAffineLine]

@[simp]
theorem pairAffineLine_one (p q : E × E) : pairAffineLine p q 1 = q := by
  simp [pairAffineLine]

theorem pairEvaluation_affineLine (f : E →ₗ[ℝ] ℝ) (p q : E × E) (z : ℂ) :
    pairEvaluation f (pairAffineLine p q z) =
      pairEvaluation f p + z * (pairEvaluation f q - pairEvaluation f p) := by
  apply Complex.ext <;>
    simp [pairEvaluation, pairAffineLine, Complex.mul_re, Complex.mul_im] <;> ring

section Paths

variable [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]

theorem continuous_pairAffineLine (p q : E × E) : Continuous (pairAffineLine p q) := by
  unfold pairAffineLine
  exact ((continuous_const.add (Complex.continuous_re.smul continuous_const)).add
    (Complex.continuous_im.smul continuous_const)).prodMk
    ((continuous_const.add (Complex.continuous_im.smul continuous_const)).add
      (Complex.continuous_re.smul continuous_const))

/-- Any two existing points of a finite real arrangement complement can be
joined inside that actual complement. Properness is needed only for existence. -/
theorem joinedIn_pairComplement {ι : Type*} [Finite ι] (f : ι → E →ₗ[ℝ] ℝ)
    {p q : E × E} (hp : p ∈ pairComplement f) (hq : q ∈ pairComplement f) :
    JoinedIn (pairComplement f) p q := by
  let bad : Set ℂ := {z | ∃ a, pairEvaluation (f a) (pairAffineLine p q z) = 0}
  have hfinite : bad.Finite := by
    have he : bad = ⋃ a, {z | pairEvaluation (f a) (pairAffineLine p q z) = 0} := by
      ext z
      simp [bad]
    rw [he]
    apply Set.finite_iUnion
    intro a
    apply Set.Subsingleton.finite
    intro z hz z' hz'
    change pairEvaluation (f a) (pairAffineLine p q z) = 0 at hz
    change pairEvaluation (f a) (pairAffineLine p q z') = 0 at hz'
    rw [pairEvaluation_affineLine] at hz hz'
    have hdelta : pairEvaluation (f a) q - pairEvaluation (f a) p ≠ 0 := by
      intro heq
      rw [heq, mul_zero, add_zero] at hz
      exact hp a hz
    exact mul_right_cancel₀ hdelta (add_left_cancel (hz.trans hz'.symm))
  have hpath : IsPathConnected badᶜ :=
    hfinite.countable.isPathConnected_compl_of_one_lt_rank (by
      rw [Complex.rank_real_complex]
      norm_num)
  have hzero : (0 : ℂ) ∈ badᶜ := by
    rintro ⟨a, ha⟩
    exact hp a (by simpa using ha)
  have hone : (1 : ℂ) ∈ badᶜ := by
    rintro ⟨a, ha⟩
    exact hq a (by simpa using ha)
  have hmap := (hpath.joinedIn 0 hzero 1 hone).map
    (continuous_pairAffineLine p q).continuousOn
  have hsub : pairAffineLine p q '' badᶜ ⊆ pairComplement f := by
    rintro _ ⟨z, hz, rfl⟩ a ha
    exact hz ⟨a, ha⟩
  simpa using hmap.mono hsub

omit [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E] in
/-- A finite family of proper kernels has a nonempty real-pair complement. -/
theorem pairComplement_nonempty {ι : Type*} [Finite ι] (f : ι → E →ₗ[ℝ] ℝ)
    (hf : ∀ a, ∃ x, f a x ≠ 0) : (pairComplement f).Nonempty := by
  obtain ⟨x, hx⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists f hf
  refine ⟨(x, 0), ?_⟩
  rw [mem_pairComplement_iff]
  intro a ha
  exact hx a ha.1

/-- The actual pair complexification complement of finitely many proper real
linear hyperplanes is path connected, including the empty arrangement. -/
theorem isPathConnected_pairComplement {ι : Type*} [Finite ι]
    (f : ι → E →ₗ[ℝ] ℝ) (hf : ∀ a, ∃ x, f a x ≠ 0) :
    IsPathConnected (pairComplement f) := by
  rw [isPathConnected_iff]
  exact ⟨pairComplement_nonempty f hf, fun _ hp _ hq => joinedIn_pairComplement f hp hq⟩

end Paths

section RelativeArrangement

variable {I : Type*}

/-- The nonzero functional defining an actual retained restricted root hyperplane. -/
noncomputable def retainedEvaluation (M : CoxeterMatrix I) (J : Set I) (r : retainedRoots M J) :
    relativeSubspace J →ₗ[ℝ] ℝ :=
  (Module.Dual.eval ℝ (Vector I) r.val).comp (relativeSubspace J).subtype

/-- The generic pair complement agrees with the source's actual relative complement. -/
theorem pairComplement_retainedEvaluation (M : CoxeterMatrix I) (J : Set I) :
    pairComplement (retainedEvaluation M J) = complementSet M J := by
  ext p
  rw [mem_pairComplement_iff]
  change (∀ r : retainedRoots M J, ¬(p.1.val r.val = 0 ∧ p.2.val r.val = 0)) ↔
    ∀ r ∈ retainedRoots M J, ¬(p.1.val r = 0 ∧ p.2.val r = 0)
  exact ⟨fun h r hr => h ⟨r, hr⟩, fun h r => h r.val r.property⟩

/-- The actual finite-type relative complexified complement is nonempty. -/
theorem complementSet_nonempty (M : CoxeterMatrix I) [Finite M.Group] (J : Set I) :
    (complementSet M J).Nonempty := by
  let := (retainedRoots_finite M J).fintype
  rw [← pairComplement_retainedEvaluation]
  exact pairComplement_nonempty (E := relativeSubspace J)
    (retainedEvaluation M J) (fun r => r.property.2)

/-- Paths exist in the actual relative complement, not just in a combinatorial model. -/
theorem isPathConnected_complementSet (M : CoxeterMatrix I) [Finite M.Group] (J : Set I) :
    IsPathConnected (complementSet M J) := by
  let := (retainedRoots_finite M J).fintype
  rw [← pairComplement_retainedEvaluation]
  exact isPathConnected_pairComplement (E := relativeSubspace J)
    (retainedEvaluation M J) (fun r => r.property.2)

instance complementPathConnectedSpace (M : CoxeterMatrix I) [Finite M.Group] (J : Set I) :
    PathConnectedSpace (Complement M J) :=
  (isPathConnected_iff_pathConnectedSpace).mp (isPathConnected_complementSet M J)

end RelativeArrangement

end ArtinNormalisers.Theorem18
