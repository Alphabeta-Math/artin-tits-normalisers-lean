module

public import ArtinNormalisers.Theorem18.Geometry
public import ArtinNormalisers.Artin.ExactSequence

/-!
# The natural relative normalizer action

The contragredient of the actual geometric representation fixes the relative
flat pointwise under the standard parabolic. Its normalizer therefore
preserves that flat and its restricted root arrangement. The action descends
through the actual normalizer quotient. These are geometric foundations;
they do not assert freeness, a covering theorem or Theorem 1.8.
-/

@[expose] public section

namespace ArtinNormalisers.Theorem18

variable {I : Type*} (M : CoxeterMatrix I) (J : Set I)

/-- The standard contragredient representation, with inverse in its argument. -/
noncomputable def dualAction : Representation ℝ M.Group (Dual I) :=
  M.toCoxeterSystem.geometricRepresentation.dual

@[simp] theorem dualAction_apply (w : M.Group) (φ : Dual I) (v : Vector I) :
    dualAction M w φ v = φ (M.toCoxeterSystem.geometricRepresentation w⁻¹ v) := rfl

theorem dualAction_simple_fixed_iff (i : I) (φ : Dual I) :
    dualAction M (M.simple i) φ = φ ↔ φ (simpleRoot i) = 0 := by
  have hsimple : M.toCoxeterSystem.simple i = M.simple i := by
    rw [CoxeterMatrix.toCoxeterSystem_simple]
  have heval (v : Vector I) :
      dualAction M (M.simple i) φ v =
        φ v - (2 * M.geometricForm (simpleRoot i) v) * φ (simpleRoot i) := by
    rw [dualAction_apply, ← hsimple, M.toCoxeterSystem.inv_simple,
      M.toCoxeterSystem.geometricRepresentation_simple,
      M.geometricReflection_apply, map_sub, map_smul]
    rfl
  constructor
  · intro h
    have hv := congrArg (fun f : Dual I => f (simpleRoot i)) h
    have hform : M.geometricForm (simpleRoot i) (simpleRoot i) = 1 :=
      M.geometricForm_single_self i
    rw [heval, hform] at hv
    linarith
  · intro h
    apply LinearMap.ext
    intro v
    rw [heval, h, mul_zero, sub_zero]

/-- The relative flat is precisely the fixed space of the generated parabolic. -/
theorem mem_relativeSubspace_iff_fixed (φ : Dual I) :
    φ ∈ relativeSubspace J ↔
      ∀ w ∈ Artin.coxeterParabolic M J, dualAction M w φ = φ := by
  constructor
  · intro hφ
    have hclosed : Artin.coxeterParabolic M J ≤
        { carrier := {w | dualAction M w φ = φ}
          one_mem' := by simp
          mul_mem' := by
            intro a b ha hb
            simp only [Set.mem_ofPred_eq] at *
            rw [map_mul, mul_apply_eq_comp, hb, ha]
          inv_mem' := by
            intro a ha
            simp only [Set.mem_ofPred_eq] at *
            have h := congrArg (fun f => dualAction M a⁻¹ f) ha
            simpa only [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel,
              map_one, one_apply_eq_self] using h.symm } := by
      change Subgroup.closure (M.simple '' J) ≤ _
      apply (Subgroup.closure_le _).2
      rintro _ ⟨i, hi, rfl⟩
      exact (dualAction_simple_fixed_iff M i φ).2 (hφ i hi)
    exact fun w hw => hclosed hw
  · intro h i hi
    apply (dualAction_simple_fixed_iff M i φ).1
    exact h _ (Subgroup.subset_closure ⟨i, hi, rfl⟩)

/-- Conjugation, rather than a root classification, proves flat preservation. -/
theorem dualAction_mem_relativeSubspace
    {w : M.Group}
    (hw : w ∈ Subgroup.normalizer (Artin.coxeterParabolic M J : Set M.Group))
    {φ : Dual I} (hφ : φ ∈ relativeSubspace J) :
    dualAction M w φ ∈ relativeSubspace J := by
  apply (mem_relativeSubspace_iff_fixed M J _).2
  intro u hu
  have hc := (Subgroup.mem_normalizer_iff''.mp hw u).mp hu
  have hf := (mem_relativeSubspace_iff_fixed M J φ).1 hφ _ hc
  calc
    dualAction M u (dualAction M w φ) =
        dualAction M w (dualAction M (w⁻¹ * u * w) φ) := by
      simp only [← mul_apply_eq_comp, ← map_mul]
      congr 2
      group
    _ = dualAction M w φ := by rw [hf]

abbrev CoxeterNormalizer :=
  Subgroup.normalizer (Artin.coxeterParabolic M J : Set M.Group)

/-- Restriction of the actual contragredient representation to the flat. -/
noncomputable def normalizerRepresentation :
    Representation ℝ (CoxeterNormalizer M J) (relativeSubspace J) where
  toFun w :=
    { toFun φ := ⟨dualAction M w φ, dualAction_mem_relativeSubspace M J w.property φ.property⟩
      map_add' φ ψ := Subtype.ext (map_add (dualAction M w) φ.val ψ.val)
      map_smul' c φ := Subtype.ext (map_smul (dualAction M w) c φ.val) }
  map_one' := by
    apply LinearMap.ext
    intro φ
    apply Subtype.ext
    change dualAction M 1 φ.val = φ.val
    rw [map_one, one_apply_eq_self]
  map_mul' w z := by
    apply LinearMap.ext
    intro φ
    apply Subtype.ext
    change dualAction M (w.val * z.val) φ.val =
      dualAction M w.val (dualAction M z.val φ.val)
    rw [map_mul, mul_apply_eq_comp]

/-- The standard parabolic acts trivially on the relative flat. -/
theorem parabolic_le_normalizerRepresentation_ker :
    (Artin.coxeterParabolic M J).subgroupOf (CoxeterNormalizer M J) ≤
      (normalizerRepresentation M J).ker := by
  intro w hw
  apply MonoidHom.mem_ker.mpr
  apply LinearMap.ext
  intro φ
  apply Subtype.ext
  exact (mem_relativeSubspace_iff_fixed M J φ.val).1 φ.property w.val hw

/-- The resulting representation of the actual quotient `N_W(W_J)/W_J`. -/
noncomputable def quotientRepresentation :
    Representation ℝ (Artin.coxeterNormalizerQuotient M J) (relativeSubspace J) :=
  QuotientGroup.lift _ (normalizerRepresentation M J)
    (parabolic_le_normalizerRepresentation_ker M J)

@[simp] theorem quotientRepresentation_mk (w : CoxeterNormalizer M J)
    (φ : relativeSubspace J) :
    quotientRepresentation M J
      (QuotientGroup.mk' ((Artin.coxeterParabolic M J).subgroupOf
        (CoxeterNormalizer M J)) w) φ = normalizerRepresentation M J w φ := rfl

@[simp] theorem normalizerRepresentation_apply_val
    (w : CoxeterNormalizer M J) (φ : relativeSubspace J) :
    (normalizerRepresentation M J w φ).val = dualAction M w.val φ.val := rfl

/-- The primal and contragredient actions preserve their evaluation pairing. -/
theorem dualAction_pairing (w : M.Group) (φ : Dual I) (r : Vector I) :
    dualAction M w φ (M.toCoxeterSystem.geometricRepresentation w r) = φ r := by
  rw [dualAction_apply, ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel,
    map_one, one_apply_eq_self]

theorem geometricAction_mem_roots (w : M.Group) {r : Vector I} (hr : r ∈ roots M) :
    M.toCoxeterSystem.geometricRepresentation w r ∈ roots M := by
  obtain ⟨a, i, rfl⟩ := hr
  refine ⟨w * a, i, ?_⟩
  simp only [root, map_mul, mul_apply_eq_comp]

/-- The retained root condition, including omission of hyperplanes containing
the whole relative flat, is preserved by the normalizer. -/
theorem geometricAction_mem_retainedRoots (w : CoxeterNormalizer M J)
    {r : Vector I} (hr : r ∈ retainedRoots M J) :
    M.toCoxeterSystem.geometricRepresentation w.val r ∈ retainedRoots M J := by
  obtain ⟨hr, φ, hφ⟩ := hr
  refine ⟨geometricAction_mem_roots M w.val hr,
    normalizerRepresentation M J w φ, ?_⟩
  simpa only [normalizerRepresentation_apply_val, dualAction_pairing] using hφ

/-- The diagonal normalizer action preserves the actual real-pair complement. -/
theorem normalizer_preserves_complement (w : CoxeterNormalizer M J)
    {p : relativeSubspace J × relativeSubspace J} (hp : p ∈ complementSet M J) :
    (normalizerRepresentation M J w p.1, normalizerRepresentation M J w p.2) ∈
      complementSet M J := by
  intro r hr hz
  apply hp _ (geometricAction_mem_retainedRoots M J w⁻¹ hr)
  simpa only [Prod.fst, Prod.snd, normalizerRepresentation_apply_val, dualAction_apply,
    Subgroup.coe_inv] using hz

/-- The actual normalizer action as permutations of the complement. -/
noncomputable def normalizerComplementAction :
    CoxeterNormalizer M J →* Equiv.Perm (Complement M J) where
  toFun w :=
    { toFun p := ⟨(normalizerRepresentation M J w p.val.1,
          normalizerRepresentation M J w p.val.2),
        normalizer_preserves_complement M J w p.property⟩
      invFun p := ⟨(normalizerRepresentation M J w⁻¹ p.val.1,
          normalizerRepresentation M J w⁻¹ p.val.2),
        normalizer_preserves_complement M J w⁻¹ p.property⟩
      left_inv p := by
        apply Subtype.ext
        apply Prod.ext <;>
          simp only [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel,
            map_one, one_apply_eq_self]
      right_inv p := by
        apply Subtype.ext
        apply Prod.ext <;>
          simp only [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel,
            map_one, one_apply_eq_self] }
  map_one' := by
    apply Equiv.ext
    intro p
    apply Subtype.ext
    change (normalizerRepresentation M J 1 p.val.1,
      normalizerRepresentation M J 1 p.val.2) = p.val
    rw [map_one]
    rfl
  map_mul' w z := by
    apply Equiv.ext
    intro p
    apply Subtype.ext
    change (normalizerRepresentation M J (w * z) p.val.1,
      normalizerRepresentation M J (w * z) p.val.2) =
      (normalizerRepresentation M J w (normalizerRepresentation M J z p.val.1),
       normalizerRepresentation M J w (normalizerRepresentation M J z p.val.2))
    rw [map_mul]
    rfl

theorem parabolic_le_normalizerComplementAction_ker :
    (Artin.coxeterParabolic M J).subgroupOf (CoxeterNormalizer M J) ≤
      (normalizerComplementAction M J).ker := by
  intro w hw
  have h := parabolic_le_normalizerRepresentation_ker M J hw
  change normalizerRepresentation M J w = 1 at h
  apply MonoidHom.mem_ker.mpr
  apply Equiv.ext
  intro p
  apply Subtype.ext
  change (normalizerRepresentation M J w p.val.1,
    normalizerRepresentation M J w p.val.2) = p.val
  rw [h]
  rfl

/-- The natural action on the actual complement descends to `N_W(W_J)/W_J`. -/
noncomputable def quotientComplementAction :
    Artin.coxeterNormalizerQuotient M J →* Equiv.Perm (Complement M J) :=
  QuotientGroup.lift _ (normalizerComplementAction M J)
    (parabolic_le_normalizerComplementAction_ker M J)

/-- The canonical quotient action, usable by orbit-quotient constructions. -/
noncomputable instance quotientComplementMulAction :
    MulAction (Artin.coxeterNormalizerQuotient M J) (Complement M J) :=
  MulAction.compHom _ (quotientComplementAction M J)

@[simp] theorem quotient_smul_eq (q : Artin.coxeterNormalizerQuotient M J)
    (p : Complement M J) : q • p = quotientComplementAction M J q p := rfl

@[simp] theorem quotientComplementAction_mk (w : CoxeterNormalizer M J)
    (p : Complement M J) :
    quotientComplementAction M J
      (QuotientGroup.mk' ((Artin.coxeterParabolic M J).subgroupOf
        (CoxeterNormalizer M J)) w) p = normalizerComplementAction M J w p := rfl

/-- Coordinate topology makes every actual dual action map continuous. -/
theorem continuous_dualAction (w : M.Group) : Continuous (dualAction M w) := by
  apply dualCoordinatesHomeomorph.comp_continuous_iff.mp
  apply continuous_pi
  intro i
  change Continuous (fun φ : Dual I =>
    φ (M.toCoxeterSystem.geometricRepresentation w⁻¹ (simpleRoot i)))
  exact continuous_evaluation _

theorem continuous_normalizerRepresentation (w : CoxeterNormalizer M J) :
    Continuous (normalizerRepresentation M J w) :=
  ((continuous_dualAction M w.val).comp continuous_subtype_val).subtype_mk _

theorem continuous_normalizerComplementAction (w : CoxeterNormalizer M J) :
    Continuous (normalizerComplementAction M J w) := by
  have h := ((continuous_normalizerRepresentation M J w).comp continuous_fst).prodMk
    ((continuous_normalizerRepresentation M J w).comp continuous_snd)
  exact (h.comp continuous_subtype_val).subtype_mk _

/-- Every element of the actual quotient acts continuously on the complement;
its inverse is continuous by the same theorem applied to the inverse element. -/
theorem continuous_quotientComplementAction (q : Artin.coxeterNormalizerQuotient M J) :
    Continuous (quotientComplementAction M J q) := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective
    ((Artin.coxeterParabolic M J).subgroupOf (CoxeterNormalizer M J)) q
  exact continuous_normalizerComplementAction M J w

instance quotientComplementContinuousConstSMul :
    ContinuousConstSMul (Artin.coxeterNormalizerQuotient M J) (Complement M J) :=
  ⟨continuous_quotientComplementAction M J⟩

/-- The source's actual topological orbit space `X_J / N(W,J)`. -/
def OrbitSpace :=
  Quotient (MulAction.orbitRel (Artin.coxeterNormalizerQuotient M J) (Complement M J))

noncomputable instance orbitSpaceTopologicalSpace : TopologicalSpace (OrbitSpace M J) :=
  inferInstanceAs (TopologicalSpace
    (Quotient (MulAction.orbitRel (Artin.coxeterNormalizerQuotient M J) (Complement M J))))

/-- The actual orbit map; the target carries precisely its quotient topology. -/
noncomputable def orbitProjection : Complement M J → OrbitSpace M J :=
  Quotient.mk (MulAction.orbitRel (Artin.coxeterNormalizerQuotient M J) (Complement M J))

theorem continuous_orbitProjection : Continuous (orbitProjection M J) :=
  continuous_quot_mk

theorem isOpenQuotientMap_orbitProjection : IsOpenQuotientMap (orbitProjection M J) :=
  MulAction.isOpenQuotientMap_quotientMk

/-- In spherical type, finiteness itself gives proper discontinuity in
mathlib's compact-intersection sense. This does not establish freeness. -/
theorem properlyDiscontinuous_quotientComplementAction [Finite M.Group] :
    ProperlyDiscontinuousSMul (Artin.coxeterNormalizerQuotient M J) (Complement M J) :=
  inferInstance

end ArtinNormalisers.Theorem18
