import ArtinDeligne.GarsideShifts

/-!
# Finite actual simple-chain carriers below any incoming vertex

Changing target along an actual signed incoming ribbon preserves its source
and every pairwise ribbon difference. It therefore gives actual order and
weighted-subspace isomorphisms, with no claim that an arbitrary target loop
fixes chambers. Relative head removal stays below its chosen target and uses
the nonnegative relative degree, not a global cofinal-loop degree.

A finite starting family must already lie in the required predicate Q;
upward closure inside the target downset then preserves Q during finite head
closure. Contractibility is derived from the proved positive head folds.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Deligne5

open Ribbon2 Homotopy5 Chamber3 OAI.HarmonicArtin Topology

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group]
variable {B0 : RibbonObject M}

/-- Retarget every genuine signed incoming arrow along the inverse of `u`. -/
def incomingRetarget (u : IncomingVertex M B0) :
    IncomingVertex M B0 ≃o IncomingVertex M u.source where
  toFun v := ⟨v.source, v.value * u.value⁻¹, .comp v.reduced (.inverse u.reduced)⟩
  invFun w := ⟨w.source, w.value * u.value, .comp w.reduced u.reduced⟩
  left_inv v := IncomingVertex.ext_value (by change (v.value * u.value⁻¹) * u.value = v.value; group)
  right_inv w := IncomingVertex.ext_value (by change (w.value * u.value) * u.value⁻¹ = w.value; group)
  map_rel_iff' := by
    intro v w
    change PositiveReducedArrow M v.source w.source
      ((v.value * u.value⁻¹) * (w.value * u.value⁻¹)⁻¹) ↔
        PositiveReducedArrow M v.source w.source (v.value * w.value⁻¹)
    have he : (v.value * u.value⁻¹) * (w.value * u.value⁻¹)⁻¹ = v.value * w.value⁻¹ := by group
    rw [he]

@[simp] theorem incomingRetarget_source (u v : IncomingVertex M B0) :
    (incomingRetarget M u v).source = v.source := rfl

@[simp] theorem incomingRetarget_value (u v : IncomingVertex M B0) :
    (incomingRetarget M u v).value = v.value * u.value⁻¹ := rfl

@[simp] theorem incomingRetarget_difference (u v w : IncomingVertex M B0) :
    (incomingRetarget M u v).difference (incomingRetarget M u w) = v.difference w := by
  simp only [IncomingVertex.difference, incomingRetarget_value]
  group

@[simp] theorem incomingRetarget_self (u : IncomingVertex M B0) :
    incomingRetarget M u u = incomingRoot M u.source := by
  apply IncomingVertex.ext_value
  exact mul_inv_cancel _

@[simp] theorem incomingRetarget_symm_root (u : IncomingVertex M B0) :
    (incomingRetarget M u).symm (incomingRoot M u.source) = u := by
  rw [← incomingRetarget_self M u, OrderIso.symm_apply_apply]

/-- The downset condition is precisely actual positive generation after retargeting. -/
theorem incomingRetarget_positive_iff (u v : IncomingVertex M B0) :
    IncomingVertex.IsPositive M u.source (incomingRetarget M u v) ↔ v ≤ u := Iff.rfl

/-- The actual principal downset is the genuine positive incoming subposet. -/
def incomingDownsetPositiveOrderIso (u : IncomingVertex M B0) :
    {v : IncomingVertex M B0 // v ≤ u} ≃o
      {w : IncomingVertex M u.source // IncomingVertex.IsPositive M u.source w} where
  toFun v := ⟨incomingRetarget M u v.val, (incomingRetarget_positive_iff M u v.val).2 v.property⟩
  invFun w := ⟨(incomingRetarget M u).symm w.val,
    (incomingRetarget_positive_iff M u _).1 (by simpa using w.property)⟩
  left_inv v := Subtype.ext ((incomingRetarget M u).symm_apply_apply v.val)
  right_inv w := Subtype.ext ((incomingRetarget M u).apply_symm_apply w.val)
  map_rel_iff' := by
    intro v w
    exact (incomingRetarget M u).le_iff_le

/-- Retarget an arbitrary literal vertex subset onto its actual image. -/
noncomputable def incomingRetargetOn (u : IncomingVertex M B0)
    (A : Set (IncomingVertex M B0)) : A ≃o (incomingRetarget M u '' A) where
  toFun v := ⟨incomingRetarget M u v.val, ⟨v.val, v.property, rfl⟩⟩
  invFun w := ⟨(incomingRetarget M u).symm w.val, by
    obtain ⟨v, hv, he⟩ := w.property
    rw [← he, OrderIso.symm_apply_apply]
    exact hv⟩
  left_inv v := Subtype.ext ((incomingRetarget M u).symm_apply_apply v.val)
  right_inv w := Subtype.ext ((incomingRetarget M u).apply_symm_apply w.val)
  map_rel_iff' := by
    intro v w
    exact (incomingRetarget M u).le_iff_le

@[simp] theorem incomingRetargetOn_val (u : IncomingVertex M B0)
    (A : Set (IncomingVertex M B0)) (v : A) :
    (incomingRetargetOn M u A v).val = incomingRetarget M u v.val := rfl

/-- Pairwise simple support is preserved on actual subset realizations. -/
theorem garsideWeightsOn_retarget_iff (u : IncomingVertex M B0)
    (A : Set (IncomingVertex M B0)) (w : OrderWeights A) :
    weightMap (incomingRetargetOn M u A : A →o (incomingRetarget M u '' A)) w
      ∈ garsideWeightsOnSet M u.source (incomingRetarget M u '' A) ↔
        w ∈ garsideWeightsOnSet M B0 A := by
  classical
  let : DecidableEq A := Classical.decEq _
  let : DecidableEq (incomingRetarget M u '' A) := Classical.decEq _
  let e := incomingRetargetOn M u A
  have hs := weightMap_support_embedding (e : A →o (incomingRetarget M u '' A)) e.injective w
  constructor
  · intro h a ha b hb hab
    have ha' : e a ∈ (weightMap (e : A →o (incomingRetarget M u '' A)) w).weights.support := by
      rw [hs]
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    have hb' : e b ∈ (weightMap (e : A →o (incomingRetarget M u '' A)) w).weights.support := by
      rw [hs]
      exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
    simpa only [e, incomingRetargetOn_val, incomingRetarget_source,
      incomingRetarget_difference] using h (e a) ha' (e b) hb' (e.monotone hab)
  · intro h a ha b hb hab
    rw [hs] at ha hb
    obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.mp hb
    change SimpleRibbon M a₀.val.source b₀.val.source
      ((incomingRetarget M u a₀.val).difference (incomingRetarget M u b₀.val))
    rw [incomingRetarget_difference]
    exact h a₀ ha₀ b₀ hb₀ (e.le_iff_le.mp hab)

/-- The actual weak weighted-subspace topology transports without changing
weights or the ribbon simple-support condition. -/
noncomputable def relativeGarsideWeightsHomeomorph (u : IncomingVertex M B0)
    (A : Set (IncomingVertex M B0)) :
    GarsideWeightsOn M B0 A ≃ₜ
      GarsideWeightsOn M u.source (incomingRetarget M u '' A) :=
  (weightHomeomorph (incomingRetargetOn M u A)).subtype
    (fun w => (garsideWeightsOn_retarget_iff M u A w).symm)

private theorem incoming_le_root_iff {C : RibbonObject M} (w : IncomingVertex M C) :
    w ≤ incomingRoot M C ↔ IncomingVertex.IsPositive M C w := by
  change PositiveReducedArrow M w.source C (w.value * (1 : Artin.Group M)⁻¹) ↔
    PositiveReducedArrow M w.source C w.value
  simp only [inv_one, mul_one]

private theorem positive_le_headStep {C : RibbonObject M} (w : IncomingVertex M C)
    (hw : IncomingVertex.IsPositive M C w) : w ≤ headStep M C w := by
  classical
  by_cases hne : w.value ≠ 1
  · rw [headStep_eq M C w hw hne]
    exact (positiveHeadTail_spec M C w hw).2.1
  · rw [headStep_eq_self_of_value_eq_one M C w (not_ne_iff.mp hne)]

/-- Actual head removal toward any chosen incoming target; outside its
principal downset the operation is the identity. -/
noncomputable def relativeHeadStep (u v : IncomingVertex M B0) : IncomingVertex M B0 := by
  classical
  exact if v ≤ u then (incomingRetarget M u).symm
    (headStep M u.source (incomingRetarget M u v)) else v

theorem incomingRetarget_relativeHeadStep (u v : IncomingVertex M B0) (hv : v ≤ u) :
    incomingRetarget M u (relativeHeadStep M u v) =
      headStep M u.source (incomingRetarget M u v) := by
  classical
  simp only [relativeHeadStep, ite_eq_left hv, OrderIso.apply_symm_apply]

theorem relativeHeadStep_self (u : IncomingVertex M B0) : relativeHeadStep M u u = u := by
  apply (incomingRetarget M u).injective
  rw [incomingRetarget_relativeHeadStep M u u le_rfl, incomingRetarget_self]
  exact headStep_eq_self_of_value_eq_one M u.source (incomingRoot M u.source) rfl

theorem relativeHeadStep_eq_of_not_le (u v : IncomingVertex M B0) (hv : ¬v ≤ u) :
    relativeHeadStep M u v = v := by
  classical
  simp only [relativeHeadStep, ite_eq_right hv]

/-- Every relative head lies in the actual order interval from its vertex to `u`. -/
theorem relativeHeadStep_interval (u v : IncomingVertex M B0) (hv : v ≤ u) :
    v ≤ relativeHeadStep M u v ∧ relativeHeadStep M u v ≤ u := by
  have hpos := (incomingRetarget_positive_iff M u v).2 hv
  constructor
  · apply (incomingRetarget M u).le_iff_le.mp
    rw [incomingRetarget_relativeHeadStep M u v hv]
    exact positive_le_headStep M _ hpos
  · apply (incomingRetarget M u).le_iff_le.mp
    rw [incomingRetarget_relativeHeadStep M u v hv, incomingRetarget_self]
    exact (incoming_le_root_iff M _).2 (headStep_positive M u.source _ hpos)

/-- Strict head termination uses the actual ribbon degree, with no assumption
on the global degree of the chosen target. -/
theorem relativeHeadStep_degree_lt (u v : IncomingVertex M B0) (hv : v ≤ u) (hne : v ≠ u) :
    degree M (relativeHeadStep M u v).value < degree M v.value := by
  have hpos := (incomingRetarget_positive_iff M u v).2 hv
  have hval : (incomingRetarget M u v).value ≠ 1 := by
    intro he
    apply hne
    exact IncomingVertex.ext_value (mul_inv_eq_one.mp he)
  have hlt := headStep_degree_lt M u.source (incomingRetarget M u v) hpos hval
  rw [← incomingRetarget_relativeHeadStep M u v hv] at hlt
  simp only [incomingRetarget_value, degree_mul, degree_inv] at hlt
  omega

/-- Natural termination height above the chosen incoming target. -/
def relativeHeadMeasure (u v : IncomingVertex M B0) : ℕ :=
  (degree M v.value - degree M u.value).toNat

theorem relativeHeadStep_measure_lt (u v : IncomingVertex M B0) (hv : v ≤ u) (hne : v ≠ u) :
    relativeHeadMeasure M u (relativeHeadStep M u v) < relativeHeadMeasure M u v := by
  have hlt := relativeHeadStep_degree_lt M u v hv hne
  have hb := (relativeHeadStep_interval M u v hv).2
  have hn := degree_nonneg_of_mem_actualPositiveParabolic M Set.univ hb.positive
  simp only [IncomingVertex.difference, degree_mul, degree_inv] at hn
  unfold relativeHeadMeasure
  omega

theorem relativeHeadStep_terminates (u v : IncomingVertex M B0) :
    relativeHeadStep M u v = v ∨
      relativeHeadMeasure M u (relativeHeadStep M u v) < relativeHeadMeasure M u v := by
  classical
  by_cases hv : v ≤ u
  · by_cases he : v = u
    · subst v
      exact Or.inl (relativeHeadStep_self M u)
    · exact Or.inr (relativeHeadStep_measure_lt M u v hv he)
  · exact Or.inl (relativeHeadStep_eq_of_not_le M u v hv)

/-- Every finite carrier below `u`, containing `u` and closed under its actual
relative heads, contracts by transporting the already proved positive folds. -/
theorem contractibleSpace_finite_relative_head_closed (u : IncomingVertex M B0)
    (B : Finset (IncomingVertex M B0))
    (hbelow : ∀ v ∈ B, v ≤ u) (hu : u ∈ B)
    (hclosed : ∀ v ∈ B, relativeHeadStep M u v ∈ B) :
    ContractibleSpace (GarsideWeightsOn M B0 (B : Set (IncomingVertex M B0))) := by
  classical
  let C : Set (IncomingVertex M u.source) := incomingRetarget M u '' (B : Set (IncomingVertex M B0))
  have hC : C.Finite := B.finite_toSet.image (incomingRetarget M u)
  let : Fintype C := hC.fintype
  have hpos (w : C) : IncomingVertex.IsPositive M u.source w.val := by
    obtain ⟨v, hv, he⟩ := w.property
    rw [← he]
    exact (incomingRetarget_positive_iff M u v).2 (hbelow v hv)
  have hhead (w : C) : headStep M u.source w.val ∈ C := by
    obtain ⟨v, hv, he⟩ := w.property
    refine ⟨relativeHeadStep M u v, hclosed v hv, ?_⟩
    simpa only [he] using incomingRetarget_relativeHeadStep M u v (hbelow v hv)
  let root : C := ⟨incomingRoot M u.source, ⟨u, hu, incomingRetarget_self M u⟩⟩
  have hcontract : ContractibleSpace (GarsideWeightsOn M u.source C) :=
    contractibleSpace_finite_positive_head_closed M u.source hpos hhead root rfl
  exact (relativeGarsideWeightsHomeomorph M u (B : Set (IncomingVertex M B0))).contractibleSpace_iff.mpr
    hcontract

/-- Finite boundary data already satisfying `Q` have a finite contractible
relative-head enlargement in `↓u ∩ Q`. Upward closure is required only within
that actual downset. Neither contraction nor any positive global target
height is assumed. -/
theorem exists_finite_contractible_relative_enlargement (u : IncomingVertex M B0)
    (A : Finset (IncomingVertex M B0)) (Q : IncomingVertex M B0 → Prop)
    (hA_below : ∀ v ∈ A, v ≤ u) (hAQ : ∀ v ∈ A, Q v) (hQu : Q u)
    (hQ : ∀ v w, v ≤ w → w ≤ u → Q v → Q w) :
    ∃ B : Finset (IncomingVertex M B0), A ⊆ B ∧ u ∈ B ∧
      (∀ v ∈ B, v ≤ u ∧ Q v) ∧
      (∀ v ∈ B, relativeHeadStep M u v ∈ B) ∧
      ContractibleSpace (GarsideWeightsOn M B0 (B : Set (IncomingVertex M B0))) := by
  classical
  have invariant (v : IncomingVertex M B0) (hv : v ≤ u ∧ Q v) :
      relativeHeadStep M u v ≤ u ∧ Q (relativeHeadStep M u v) := by
    have hb := relativeHeadStep_interval M u v hv.1
    exact ⟨hb.2, hQ v (relativeHeadStep M u v) hb.1 hb.2 hv.2⟩
  obtain ⟨B, hAB, hBQ, hclosed⟩ := exists_finite_closed_ancestry
    (relativeHeadStep M u) (relativeHeadMeasure M u) (fun v => v ≤ u ∧ Q v)
    (relativeHeadStep_terminates M u) invariant (insert u A) (by
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact ⟨le_rfl, hQu⟩
      · exact ⟨hA_below v hv, hAQ v hv⟩)
  have huB : u ∈ B := hAB (Finset.mem_insert_self _ _)
  exact ⟨B, (Finset.subset_insert _ _).trans hAB, huB, hBQ, hclosed,
    contractibleSpace_finite_relative_head_closed M u B (fun v hv => (hBQ v hv).1) huB hclosed⟩

end ArtinNormalisers.Deligne5
