module

public import ArtinAsphericity.FlatCoordinates
public import ArtinChambers.ChamberLabels
public import Mathlib.Geometry.Convex.Cone.Simplicial
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Actual restricted Coxeter chambers are simplicial regions

Each actual chamber is carried onto a strict finite positive orthant by an
actual continuous linear equivalence. Its closure is the pointed cone generated
by a finite basis, and is simplicial in mathlib's `PointedCone.IsSimplicial`
sense. This proves geometric simpliciality only, not complement asphericity.
-/

@[expose] public section

namespace ArtinNormalisers.Asphericity5

open Theorem18 Chamber3 Module

/-- The strict positive orthant, including its vacuous rank-zero case. -/
def positiveOrthant (ι : Type*) : Set (ι → ℝ) := {a | ∀ i, 0 < a i}

/-- The nonnegative orthant. -/
def nonnegativeOrthant (ι : Type*) : Set (ι → ℝ) := {a | ∀ i, 0 ≤ a i}

theorem closure_positiveOrthant (ι : Type*) :
    closure (positiveOrthant ι) = nonnegativeOrthant ι := by
  have he : positiveOrthant ι = Set.pi Set.univ (fun _ : ι => Set.Ioi (0 : ℝ)) := by
    ext a
    simp [positiveOrthant]
  rw [he, closure_pi_set]
  ext a
  simp [nonnegativeOrthant]
  rfl

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- A genuine geometric simplicial region: a continuous linear change of
coordinates identifies it with a finite-dimensional strict positive orthant. -/
def IsSimplicialRegion (S : Set E) : Prop :=
  ∃ (n : ℕ) (e : E ≃L[ℝ] (Fin n → ℝ)), S = e ⁻¹' positiveOrthant (Fin n)

theorem IsSimplicialRegion.exists_orthant_equiv {S : Set E} (hS : IsSimplicialRegion S) :
    ∃ (n : ℕ) (e : E ≃L[ℝ] (Fin n → ℝ)), e '' S = positiveOrthant (Fin n) := by
  obtain ⟨n, e, he⟩ := hS
  refine ⟨n, e, ?_⟩
  rw [he]
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro ha
    exact ⟨e.symm a, by simpa only [Set.mem_preimage, ContinuousLinearEquiv.apply_symm_apply] using ha,
      e.apply_symm_apply a⟩

omit [TopologicalSpace E] in
theorem mem_hull_basis_iff {ι : Type*} [Fintype ι] (b : Basis ι ℝ E) (x : E) :
    x ∈ PointedCone.hull ℝ (Set.range b) ↔ ∀ i, 0 ≤ b.repr x i := by
  classical
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      intro i
      simp only [Basis.repr_self, Finsupp.single_apply]
      split_ifs <;> norm_num
    | zero => simp
    | add y z hy hz ihy ihz =>
      intro i
      simpa only [map_add, Finsupp.add_apply] using add_nonneg (ihy i) (ihz i)
    | smul a y hy ih =>
      intro i
      change 0 ≤ b.repr ((a : ℝ) • y) i
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact mul_nonneg a.property (ih i)
  · intro hx
    rw [← b.sum_repr x]
    apply Submodule.sum_mem
    intro i _
    exact (PointedCone.hull ℝ (Set.range b)).smul_mem (hx i)
      (PointedCone.subset_hull ⟨i, rfl⟩)

/-- The orthant condition gives an actual finite basis, whose conic hull
is exactly the chamber closure, including dimension zero. -/
theorem IsSimplicialRegion.exists_basis_and_closure {S : Set E} (hS : IsSimplicialRegion S) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℝ E),
      S = {x | ∀ i, 0 < b.repr x i} ∧
      closure S = (PointedCone.hull ℝ (Set.range b) : Set E) ∧
      (PointedCone.hull ℝ (Set.range b)).IsSimplicial := by
  obtain ⟨n, e, he⟩ := hS
  let b := Basis.ofEquivFun e.toLinearEquiv
  refine ⟨n, b, ?_, ?_, ?_⟩
  · rw [he]
    rfl
  · have hc : e ⁻¹' closure (positiveOrthant (Fin n)) =
        closure (e ⁻¹' positiveOrthant (Fin n)) := e.toHomeomorph.preimage_closure _
    rw [he, ← hc, closure_positiveOrthant]
    ext x
    exact (mem_hull_basis_iff b x).symm
  · exact PointedCone.IsSimplicial.hull (Set.finite_range b) b.linearIndependent.linearIndepOn_id

theorem IsSimplicialRegion.exists_basis {S : Set E} (hS : IsSimplicialRegion S) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℝ E), S = {x | ∀ i, 0 < b.repr x i} := by
  obtain ⟨n, b, h, _⟩ := hS.exists_basis_and_closure
  exact ⟨n, b, h⟩

/-- Reindex an arbitrary finite coordinate type to `Fin`, without restricting
the universe of the original Coxeter indexing type. -/
noncomputable def finiteCoordinateEquiv (ι : Type*) [Finite ι] :
    (ι → ℝ) ≃L[ℝ] (Fin (Nat.card ι) → ℝ) where
  toLinearEquiv :=
    { toFun := fun a i => a ((Finite.equivFin ι).symm i)
      invFun := fun a i => a (Finite.equivFin ι i)
      left_inv := fun a => by funext i; simp only [Equiv.symm_apply_apply]
      right_inv := fun a => by funext i; simp only [Equiv.apply_symm_apply]
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  continuous_toFun := continuous_pi fun i => continuous_apply ((Finite.equivFin ι).symm i)
  continuous_invFun := continuous_pi fun i => continuous_apply (Finite.equivFin ι i)

theorem finiteCoordinateEquiv_pos_iff (ι : Type*) [Finite ι] (a : ι → ℝ) :
    finiteCoordinateEquiv ι a ∈ positiveOrthant (Fin (Nat.card ι)) ↔ a ∈ positiveOrthant ι := by
  change (∀ i, 0 < a ((Finite.equivFin ι).symm i)) ↔ ∀ i, 0 < a i
  constructor
  · intro h i
    simpa only [Equiv.symm_apply_apply] using h (Finite.equivFin ι i)
  · intro h i
    exact h _

variable {I : Type*} {M : CoxeterMatrix I} {J : Set I}

/-- Actual inverse facet transport followed by actual outside-simple-root
coordinates, using the existing topology on the relative dual flat. -/
noncomputable def rawFacetCoordinates (L : RawFacetLabel M J) :
    relativeSubspace J ≃L[ℝ] ({i : I // i ∉ L.indices} → ℝ) :=
  (facetFlatEquiv L).symm.trans (flatComplementCoordinates L.indices)

theorem mem_translatedFacet_iff_coordinates_pos (L : RawFacetLabel M J)
    (x : relativeSubspace J) :
    x ∈ translatedFacet L ↔ rawFacetCoordinates L x ∈ positiveOrthant {i : I // i ∉ L.indices} := by
  constructor
  · rintro ⟨φ, hφ, rfl⟩ i
    change 0 < flatComplementCoordinates L.indices ((facetFlatEquiv L).symm (facetFlatEquiv L φ)) i
    rw [ContinuousLinearEquiv.symm_apply_apply, flatComplementCoordinates_apply]
    exact hφ.2 i i.property
  · intro h
    refine ⟨(facetFlatEquiv L).symm x, ?_, (facetFlatEquiv L).apply_symm_apply x⟩
    refine ⟨((facetFlatEquiv L).symm x).property, ?_⟩
    intro i hi
    have hh := h ⟨i, hi⟩
    simpa only [rawFacetCoordinates, ContinuousLinearEquiv.trans_apply,
      flatComplementCoordinates_apply] using hh

theorem translatedFacet_isSimplicialRegion [Finite I] (L : RawFacetLabel M J) :
    IsSimplicialRegion (translatedFacet L) := by
  let ι := {i : I // i ∉ L.indices}
  refine ⟨Nat.card ι, (rawFacetCoordinates L).trans (finiteCoordinateEquiv ι), ?_⟩
  ext x
  exact (mem_translatedFacet_iff_coordinates_pos L x).trans
    (finiteCoordinateEquiv_pos_iff ι (rawFacetCoordinates L x)).symm

variable (M) [Finite M.Group] (J)

/-- Every chamber of the actual restricted root arrangement is a geometric
simplicial region, for every spherical Coxeter type and every parabolic set. -/
theorem actualChamber_isSimplicialRegion (C : ActualChamber M J) :
    IsSimplicialRegion C.region := by
  let : Finite I := finite_index M
  obtain ⟨L, rfl⟩ := actualChamberOfRawLabel_surjective M J C
  rw [actualChamberOfRawLabel_region]
  exact translatedFacet_isSimplicialRegion L

theorem actualChamber_orthant_equiv (C : ActualChamber M J) :
    ∃ (n : ℕ) (e : relativeSubspace J ≃L[ℝ] (Fin n → ℝ)),
      e '' C.region = positiveOrthant (Fin n) :=
  (actualChamber_isSimplicialRegion M J C).exists_orthant_equiv

/-- Actual finite-basis generation of every actual chamber and its closure. -/
theorem actualChamber_basis_and_closure (C : ActualChamber M J) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℝ (relativeSubspace J)),
      C.region = {x | ∀ i, 0 < b.repr x i} ∧
      closure C.region = (PointedCone.hull ℝ (Set.range b) : Set (relativeSubspace J)) ∧
      (PointedCone.hull ℝ (Set.range b)).IsSimplicial :=
  (actualChamber_isSimplicialRegion M J C).exists_basis_and_closure

theorem actualChamber_closure_isSimplicialCone (C : ActualChamber M J) :
    ∃ K : PointedCone ℝ (relativeSubspace J),
      (K : Set (relativeSubspace J)) = closure C.region ∧ K.IsSimplicial := by
  obtain ⟨_, b, _, hclosure, hsimp⟩ := actualChamber_basis_and_closure M J C
  exact ⟨PointedCone.hull ℝ (Set.range b), hclosure.symm, hsimp⟩

end ArtinNormalisers.Asphericity5
