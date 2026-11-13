module

public import TauCeti.GroupTheory.Coxeter.Geometric.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Topology.Homeomorph.TransferInstance

/-!
# The actual relative reflection complement

The source's finite-type space is defined directly as a subspace of two copies
of the relative subspace of the standard dual representation. Only roots whose
evaluation is nonzero on that subspace contribute a removed hyperplane.
No assertion about fundamental groups or asphericity is made here.
-/

@[expose] public section

namespace ArtinNormalisers.Theorem18

variable {I : Type*}

/-- The free real vector space of the standard geometric representation. -/
abbrev Vector (I : Type*) := I →₀ ℝ

/-- The actual algebraic dual of the standard geometric representation. -/
abbrev Dual (I : Type*) := Module.Dual ℝ (Vector I)

/-- The standard simple root. -/
noncomputable def simpleRoot (i : I) : Vector I := Finsupp.single i 1

/-- The coordinate identification uses the actual dual basis. -/
noncomputable def dualCoordinates : Dual I ≃ₗ[ℝ] (I → ℝ) where
  toFun φ i := φ (simpleRoot i)
  invFun a := Finsupp.linearCombination ℝ a
  left_inv φ := by
    apply Finsupp.lhom_ext
    intro i a
    rw [Finsupp.linearCombination_single]
    change a * φ (simpleRoot i) = φ (Finsupp.single i a)
    rw [← Finsupp.smul_single_one i a, map_smul, smul_eq_mul]
    rfl
  right_inv a := by
    funext i
    simp [simpleRoot, Finsupp.linearCombination_single]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Pointwise dual coordinates give the usual real coordinate topology in
finite rank, and a specified topology without a finite-rank assumption. -/
noncomputable instance dualTopologicalSpace : TopologicalSpace (Dual I) :=
  TopologicalSpace.induced (dualCoordinates (I := I)) inferInstance

/-- The dual-coordinate identification is a homeomorphism, so the topology
above is the ordinary product-coordinate topology, not a discrete topology. -/
noncomputable def dualCoordinatesHomeomorph : Dual I ≃ₜ (I → ℝ) :=
  (dualCoordinates (I := I)).toEquiv.toHomeomorphOfIsInducing ⟨rfl⟩

instance dualContinuousAdd : ContinuousAdd (Dual I) :=
  continuousAdd_induced (dualCoordinates (I := I)).toLinearMap

instance dualContinuousSMul : ContinuousSMul ℝ (Dual I) :=
  continuousSMul_induced (dualCoordinates (I := I)).toLinearMap

instance dualContinuousNeg : ContinuousNeg (Dual I) :=
  ContinuousNeg.of_continuousConstSMul ℝ (Dual I)

instance dualTopologicalAddGroup : IsTopologicalAddGroup (Dual I) where

instance dualT2Space : T2Space (Dual I) := dualCoordinatesHomeomorph.symm.t2Space

/-- Evaluation at every vector is continuous for this dual topology. -/
theorem continuous_evaluation (v : Vector I) : Continuous (fun φ : Dual I => φ v) := by
  induction v using Finsupp.induction_linear with
  | zero => simpa only [map_zero] using (continuous_const : Continuous (fun _ : Dual I => (0 : ℝ)))
  | add u v hu hv =>
    simpa only [map_add, Function.comp_def] using
      continuous_add.comp (hu.prodMk hv)
  | single i a =>
    have hc : Continuous (fun φ : Dual I => φ (simpleRoot i)) :=
      (continuous_apply i).comp dualCoordinatesHomeomorph.continuous_toFun
    simpa only [← Finsupp.smul_single_one i a, map_smul, smul_eq_mul, simpleRoot] using
      hc.const_mul a

/-- The source's relative dual subspace `Θ_J`. -/
def relativeSubspace (J : Set I) : Submodule ℝ (Dual I) where
  carrier := {φ | ∀ j ∈ J, φ (simpleRoot j) = 0}
  zero_mem' := by simp
  add_mem' := by intro φ ψ hφ hψ j hj; simp [hφ j hj, hψ j hj]
  smul_mem' := by intro c φ hφ j hj; simp [hφ j hj]

@[simp]
theorem mem_relativeSubspace (J : Set I) (φ : Dual I) :
    φ ∈ relativeSubspace J ↔ ∀ j ∈ J, φ (simpleRoot j) = 0 := Iff.rfl

theorem isClosed_relativeSubspace (J : Set I) :
    IsClosed (relativeSubspace J : Set (Dual I)) := by
  have he : (relativeSubspace J : Set (Dual I)) =
      ⋂ j ∈ J, {φ : Dual I | φ (simpleRoot j) = 0} := by
    ext φ
    simp
  rw [he]
  exact isClosed_biInter fun j _ => isClosed_eq (continuous_evaluation (simpleRoot j)) continuous_const

/-- Roots are the actual orbit of the simple roots in the standard representation. -/
noncomputable def root (M : CoxeterMatrix I) (w : M.Group) (i : I) : Vector I :=
  M.toCoxeterSystem.geometricRepresentation w (simpleRoot i)

@[simp]
theorem root_one (M : CoxeterMatrix I) (i : I) : root M 1 i = simpleRoot i := by
  simp [root]

theorem root_ne_zero (M : CoxeterMatrix I) (w : M.Group) (i : I) : root M w i ≠ 0 := by
  intro h
  have he : M.toCoxeterSystem.geometricRepresentation w (simpleRoot i) =
      M.toCoxeterSystem.geometricRepresentation w 0 := by simpa [root] using h
  have hz := (Representation.apply_bijective M.toCoxeterSystem.geometricRepresentation w).injective he
  have := congrArg (fun v : Vector I => v i) hz
  simp [simpleRoot] at this

/-- The actual (possibly repeated, when indexed by group elements) root set. -/
def roots (M : CoxeterMatrix I) : Set (Vector I) := {r | ∃ w i, root M w i = r}

/-- Keep exactly those roots whose evaluation is not identically zero on `Θ_J`. -/
def retainedRoots (M : CoxeterMatrix I) (J : Set I) : Set (Vector I) :=
  {r | r ∈ roots M ∧ ∃ φ : relativeSubspace J, φ.val r ≠ 0}

/-- The restricted root hyperplane as an actual linear subspace of `Θ_J`. -/
noncomputable def restrictedHyperplane (J : Set I) (r : Vector I) :
    Submodule ℝ (relativeSubspace J) :=
  (Module.Dual.eval ℝ (Vector I) r |>.comp (relativeSubspace J).subtype).ker

@[simp]
theorem mem_restrictedHyperplane (J : Set I) (r : Vector I) (φ : relativeSubspace J) :
    φ ∈ restrictedHyperplane J r ↔ φ.val r = 0 := Iff.rfl

theorem retainedRoots_iff (M : CoxeterMatrix I) (J : Set I) (r : Vector I) :
    r ∈ retainedRoots M J ↔ r ∈ roots M ∧ restrictedHyperplane J r ≠ ⊤ := by
  classical
  constructor
  · rintro ⟨hr, φ, hφ⟩
    refine ⟨hr, fun htop => ?_⟩
    have hm : φ ∈ restrictedHyperplane J r := htop.symm ▸ Submodule.mem_top
    exact hφ hm
  · rintro ⟨hr, hproper⟩
    refine ⟨hr, ?_⟩
    by_contra hn
    push Not at hn
    apply hproper
    apply top_unique
    intro φ _
    exact hn φ

/-- The distinct proper restricted hyperplanes. Taking an image automatically
identifies roots which define the same restricted hyperplane. -/
noncomputable def restrictedArrangement (M : CoxeterMatrix I) (J : Set I) :
    Set (Submodule ℝ (relativeSubspace J)) :=
  restrictedHyperplane J '' retainedRoots M J

theorem restrictedArrangement_proper (M : CoxeterMatrix I) (J : Set I)
    {H : Submodule ℝ (relativeSubspace J)} (hH : H ∈ restrictedArrangement M J) : H ≠ ⊤ := by
  obtain ⟨r, hr, rfl⟩ := hH
  exact ((retainedRoots_iff M J r).mp hr).2

theorem simpleRoot_not_retained_of_mem (M : CoxeterMatrix I) (J : Set I)
    {j : I} (hj : j ∈ J) : simpleRoot j ∉ retainedRoots M J := by
  rintro ⟨_, φ, hφ⟩
  exact hφ (φ.property j hj)

theorem simpleRoot_retained_of_not_mem (M : CoxeterMatrix I) (J : Set I)
    {i : I} (hi : i ∉ J) : simpleRoot i ∈ retainedRoots M J := by
  classical
  refine ⟨⟨1, i, root_one M i⟩, ⟨Finsupp.lapply i, ?_⟩, ?_⟩
  · intro j hj
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    simp [simpleRoot, hji]
  · simp [simpleRoot]

@[simp]
theorem relativeSubspace_empty : relativeSubspace (∅ : Set I) = ⊤ := by
  ext φ
  simp

@[simp]
theorem relativeSubspace_univ : relativeSubspace (Set.univ : Set I) = ⊥ := by
  apply le_antisymm
  · intro φ hφ
    rw [Submodule.mem_bot]
    apply (dualCoordinates (I := I)).injective
    funext i
    exact hφ i (Set.mem_univ i)
  · exact bot_le

@[simp]
theorem retainedRoots_univ (M : CoxeterMatrix I) : retainedRoots M Set.univ = ∅ := by
  ext r
  simp only [retainedRoots, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
  intro _
  rintro ⟨φ, hφ⟩
  have hz : φ.val = 0 := by
    apply (dualCoordinates (I := I)).injective
    funext i
    exact φ.property i (Set.mem_univ i)
  exact hφ (by simp [hz])

@[simp]
theorem retainedRoots_empty (M : CoxeterMatrix I) : retainedRoots M ∅ = roots M := by
  classical
  ext r
  constructor
  · exact fun h => h.1
  · intro hr
    obtain ⟨w, i, rfl⟩ := hr
    have hn := root_ne_zero M w i
    have hex : ∃ j, root M w i j ≠ 0 := by
      by_contra h
      push Not at h
      exact hn (Finsupp.ext h)
    obtain ⟨j, hj⟩ := hex
    exact ⟨⟨w, i, rfl⟩, ⟨Finsupp.lapply j, by simp⟩, hj⟩

/-- The finite-type complexified complement, expressed as actual real and
imaginary coordinates. Both evaluations must vanish for a point to be removed. -/
def complementSet (M : CoxeterMatrix I) (J : Set I) :
    Set (relativeSubspace J × relativeSubspace J) :=
  {p | ∀ r ∈ retainedRoots M J, ¬(p.1.val r = 0 ∧ p.2.val r = 0)}

/-- The actual complement, carrying its inherited product/subspace topology. -/
def Complement (M : CoxeterMatrix I) (J : Set I) := ↥(complementSet M J)

instance complementTopologicalSpace (M : CoxeterMatrix I) (J : Set I) :
    TopologicalSpace (Complement M J) := inferInstanceAs (TopologicalSpace ↥(complementSet M J))

/-- The root-indexed definition is exactly the complement of the union of
`H × H` over the distinct proper restricted hyperplanes. -/
theorem mem_complementSet_iff_arrangement (M : CoxeterMatrix I) (J : Set I)
    (p : relativeSubspace J × relativeSubspace J) :
    p ∈ complementSet M J ↔
      ∀ H ∈ restrictedArrangement M J, ¬(p.1 ∈ H ∧ p.2 ∈ H) := by
  simp [restrictedArrangement, complementSet]

@[simp]
theorem complementSet_univ (M : CoxeterMatrix I) : complementSet M Set.univ = Set.univ := by
  simp [complementSet]

/-- The full-parabolic complement has exactly one point, including in rank zero. -/
noncomputable instance complementUnivUnique (M : CoxeterMatrix I) : Unique (Complement M Set.univ) where
  default := ⟨(0, 0), by simp⟩
  uniq p := by
    apply Subtype.ext
    apply Prod.ext <;> apply Subtype.ext <;>
      apply (dualCoordinates (I := I)).injective <;> funext i
    · exact p.val.1.property i (Set.mem_univ i)
    · exact p.val.2.property i (Set.mem_univ i)

/-- Finite Coxeter group already implies finite index type; this does not add
finite rank as an independent hypothesis. -/
theorem finite_index (M : CoxeterMatrix I) [Finite M.Group] : Finite I :=
  Finite.of_injective M.simple M.toCoxeterSystem.simple_injective

theorem roots_finite (M : CoxeterMatrix I) [Finite M.Group] : (roots M).Finite := by
  have := finite_index M
  have he : roots M = Set.range (fun p : M.Group × I => root M p.1 p.2) := by
    ext r
    simp [roots, Prod.exists]
  rw [he]
  exact Set.finite_range _

theorem retainedRoots_finite (M : CoxeterMatrix I) [Finite M.Group] (J : Set I) :
    (retainedRoots M J).Finite := (roots_finite M).subset (fun _ h => h.1)

/-- In finite Coxeter type the source complement is an open subset of the
relative real-pair vector space. -/
theorem isOpen_complementSet (M : CoxeterMatrix I) [Finite M.Group] (J : Set I) :
    IsOpen (complementSet M J) := by
  have he : complementSet M J =
      ⋂ r ∈ retainedRoots M J,
        {p : relativeSubspace J × relativeSubspace J |
          ¬(p.1.val r = 0 ∧ p.2.val r = 0)} := by
    ext p
    simp [complementSet]
  rw [he]
  apply (retainedRoots_finite M J).isOpen_biInter
  intro r _
  have h1 : Continuous (fun p : relativeSubspace J × relativeSubspace J => p.1.val r) :=
    (continuous_evaluation r).comp (continuous_subtype_val.comp continuous_fst)
  have h2 : Continuous (fun p : relativeSubspace J × relativeSubspace J => p.2.val r) :=
    (continuous_evaluation r).comp (continuous_subtype_val.comp continuous_snd)
  exact ((isClosed_eq h1 continuous_const).inter
    (isClosed_eq h2 continuous_const)).isOpen_compl

end ArtinNormalisers.Theorem18
