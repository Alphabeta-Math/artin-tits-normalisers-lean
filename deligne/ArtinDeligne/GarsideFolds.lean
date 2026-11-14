import ArtinDeligne.GarsideWeights

/-!
# Finite barycentric deletion in the actual simple-chain space

Mass is transferred from a vertex to its proved head-removal cone vertex.
The coordinate formulas preserve nonnegativity, total weight, genuine chain
support and simplicity. All maps carry the inherited weighted-realization
topology. Finite iteration is the route to nullhomotopies; no contraction
or higher-topology conclusion is assumed as data.
-/

set_option autoImplicit false
namespace ArtinNormalisers.Deligne5
open OAI.HarmonicArtin Topology
open scoped BigOperators unitInterval

namespace FiniteWeightTransfer
attribute [local instance] Classical.decEq Classical.propDecidable
variable {P : Type*} [PartialOrder P] [Finite P]

noncomputable def movedWeights (p q : P) (t : unitInterval) (w : OrderWeights P) : P →₀ ℝ := by
  classical
  exact Finsupp.equivFunOnFinite.symm (fun i =>
    w.weights i + (if i = q then (t : ℝ) * w.weights p else 0) -
      (if i = p then (t : ℝ) * w.weights p else 0))

@[simp] theorem movedWeights_apply (p q : P) (t : unitInterval) (w : OrderWeights P) (i : P) :
    movedWeights p q t w i =
      w.weights i + (if i = q then (t : ℝ) * w.weights p else 0) -
        (if i = p then (t : ℝ) * w.weights p else 0) := rfl

theorem movedWeights_nonneg (p q : P) (t : unitInterval) (w : OrderWeights P) (i : P) :
    0 ≤ movedWeights p q t w i := by
  classical
  rw [movedWeights_apply]
  by_cases hp : i = p
  · subst i
    by_cases hq : p = q
    · simp only [hq, ↓reduceIte, add_sub_cancel_right]
      exact w.nonneg q
    · simp only [hq, ↓reduceIte, add_zero]
      have h := mul_nonneg (sub_nonneg.mpr t.property.2) (w.nonneg p)
      nlinarith
  · simp only [hp, ↓reduceIte, sub_zero]
    split_ifs
    · exact add_nonneg (w.nonneg i) (mul_nonneg t.property.1 (w.nonneg p))
    · simpa only [add_zero] using w.nonneg i

theorem movedWeights_total (p q : P) (t : unitInterval) (w : OrderWeights P) :
    (movedWeights p q t w).sum (fun _ a => a) = 1 := by
  classical
  let : Fintype P := Fintype.ofFinite P
  have hsum : (∑ i, w.weights i) = 1 := by
    rw [← Finsupp.sum_fintype w.weights (fun _ a => a) (by intro; rfl)]
    exact w.total
  rw [Finsupp.sum_fintype _ _ (by intro; rfl)]
  simp only [movedWeights_apply, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  linarith

theorem movedWeights_support (p q : P) (t : unitInterval) (w : OrderWeights P)
    {i : P} (hi : i ∈ (movedWeights p q t w).support) :
    i ∈ w.weights.support ∨ i = q := by
  classical
  by_cases hq : i = q
  · exact Or.inr hq
  · left
    by_contra hno
    have hw : w.weights i = 0 := Finsupp.notMem_support_iff.mp hno
    have hz : movedWeights p q t w i = 0 := by
      rw [movedWeights_apply]
      by_cases hp : i = p
      · subst i
        simp only [hw, mul_zero, ite_self, sub_zero, add_zero]
      · simp only [hw, hq, hp, ↓reduceIte, add_zero, sub_zero]
    exact (Finsupp.mem_support_iff.mp hi) hz



theorem movedWeights_zero (p q : P) (w : OrderWeights P) : movedWeights p q 0 w = w.weights := by
  classical
  ext i
  simp [movedWeights_apply]

theorem movedWeights_eq_of_notMem (p q : P) (t : unitInterval) (w : OrderWeights P)
    (hp : p ∉ w.weights.support) : movedWeights p q t w = w.weights := by
  classical
  have hz := Finsupp.notMem_support_iff.mp hp
  ext i
  simp only [movedWeights_apply, hz, mul_zero, ite_self, add_zero, sub_zero]

theorem movedWeights_one_source (p q : P) (hpq : p ≠ q) (w : OrderWeights P) :
    movedWeights p q 1 w p = 0 := by
  classical
  simp [movedWeights_apply, hpq]

noncomputable def moveOrderWeights (p q : P) (t : unitInterval) (w : OrderWeights P)
    (hcone : p ∈ w.weights.support → ∀ i ∈ w.weights.support, i ≤ q) : OrderWeights P where
  weights := movedWeights p q t w
  nonneg := movedWeights_nonneg p q t w
  total := movedWeights_total p q t w
  chain := by
    intro i hi j hj
    by_cases hp : p ∈ w.weights.support
    · rcases movedWeights_support p q t w hi with hiold | hiq
      · rcases movedWeights_support p q t w hj with hjold | hjq
        · exact w.chain i hiold j hjold
        · exact Or.inl (hjq.symm ▸ hcone hp i hiold)
      · rcases movedWeights_support p q t w hj with hjold | hjq
        · exact Or.inr (hiq.symm ▸ hcone hp j hjold)
        · exact Or.inl (le_of_eq (hiq.trans hjq.symm))
    · rw [movedWeights_eq_of_notMem p q t w hp] at hi hj
      exact w.chain i hi j hj

theorem continuous_moveOrderWeights {X : Type*} [TopologicalSpace X]
    (p q : P) (f : C(X, OrderWeights P))
    (hcone : ∀ x, p ∈ (f x).weights.support → ∀ i ∈ (f x).weights.support, i ≤ q) :
    Continuous (fun z : unitInterval × X => moveOrderWeights p q z.1 (f z.2) (hcone z.2)) := by
  apply (FiniteWeightCoordinates.continuous_iff_coordinates _).mpr
  intro i
  have hwi : Continuous (fun z : unitInterval × X => (f z.2).weights i) :=
    (weightEval_continuous i).comp (f.continuous.comp continuous_snd)
  have hwp : Continuous (fun z : unitInterval × X => (f z.2).weights p) :=
    (weightEval_continuous p).comp (f.continuous.comp continuous_snd)
  have ht : Continuous (fun z : unitInterval × X => (z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  change Continuous (fun z : unitInterval × X => movedWeights p q z.1 (f z.2) i)
  simp only [movedWeights_apply]
  split_ifs
  · exact (hwi.add (ht.mul hwp)).sub (ht.mul hwp)
  · exact (hwi.add (ht.mul hwp)).sub continuous_const
  · exact (hwi.add continuous_const).sub (ht.mul hwp)
  · exact (hwi.add continuous_const).sub continuous_const

end FiniteWeightTransfer

open Ribbon2 Homotopy5 Chamber3

variable {S : Type*} (M : CoxeterMatrix S) [Finite M.Group] (B0 : RibbonObject M)

/-- In a positive carrier, a maximal-degree active vertex is the minimum
of every active simple chain containing it. -/
theorem active_le_headStep {A : Set (IncomingVertex M B0)}
    (hpos : ∀ u : A, IncomingVertex.IsPositive M B0 u.val)
    (w : GarsideWeightsOn M B0 A) (p : A) (hp : p ∈ w.val.weights.support)
    (hmax : ∀ i ∈ w.val.weights.support, degree M i.val.value ≤ degree M p.val.value)
    (hne : p.val.value ≠ 1) (i : A) (hi : i ∈ w.val.weights.support) :
    i.val ≤ headStep M B0 p.val ∧
      SimpleRibbon M i.val.source (headStep M B0 p.val).source
        (i.val.difference (headStep M B0 p.val)) := by
  have hpi : p ≤ i := by
    rcases w.val.chain p hp i hi with hpi | hip
    · exact hpi
    · by_contra hnot
      have hlt : i.val < p.val := (lt_iff_le_not_ge).mpr ⟨hip, hnot⟩
      have hh := IncomingVertex.height_lt hlt
      have hb := hmax i hi
      dsimp only [IncomingVertex.height] at hh
      omega
  exact headStep_cone M B0 p.val (hpos p) hne i.val (hpos i) hpi
    (w.property p hp i hi hpi)

section Deletion

variable {A : Set (IncomingVertex M B0)} [Finite A]
  (hpos : ∀ u : A, IncomingVertex.IsPositive M B0 u.val)
  (p q : A) (hq : q.val = headStep M B0 p.val) (hne : p.val.value ≠ 1)
  {X : Type*} [TopologicalSpace X] (f : C(X, GarsideWeightsOn M B0 A))
  (hmax : ∀ x, ∀ i ∈ (f x).val.weights.support,
    degree M i.val.value ≤ degree M p.val.value)

omit [Finite A] in
include hpos hq hne hmax in
private theorem deletion_cone (x : X) (hp : p ∈ (f x).val.weights.support)
    (i : A) (hi : i ∈ (f x).val.weights.support) : i ≤ q := by
  have h := (active_le_headStep M B0 hpos (f x) p hp (hmax x) hne i hi).1
  change i.val ≤ q.val
  rwa [hq]

include hpos hq hne hmax in
/-- The genuine finite-coordinate weight transfer, now constrained to the
actual simple-chain subspace at every time. -/
noncomputable def deleteVertex (t : unitInterval) (x : X) : GarsideWeightsOn M B0 A := by
  classical
  let w := f x
  let w' := FiniteWeightTransfer.moveOrderWeights p q t w.val
    (deletion_cone M B0 hpos p q hq hne f hmax x)
  refine ⟨w', ?_⟩
  intro i hi j hj hij
  by_cases hp : p ∈ w.val.weights.support
  · have hsimple (k : A) (hk : k ∈ w.val.weights.support) :
        SimpleRibbon M k.val.source q.val.source (k.val.difference q.val) := by
      have h := (active_le_headStep M B0 hpos w p hp (hmax x) hne k hk).2
      rwa [← hq] at h
    rcases FiniteWeightTransfer.movedWeights_support p q t w.val hi with hiold | hiq
    · rcases FiniteWeightTransfer.movedWeights_support p q t w.val hj with hjold | hjq
      · exact w.property i hiold j hjold hij
      · subst j
        exact hsimple i hiold
    · subst i
      rcases FiniteWeightTransfer.movedWeights_support p q t w.val hj with hjold | hjq
      · have hjq' : j = q := le_antisymm
          (deletion_cone M B0 hpos p q hq hne f hmax x hp j hjold) hij
        subst j
        simpa only [IncomingVertex.difference_self] using simpleRibbon_one M q.val.source
      · subst j
        simpa only [IncomingVertex.difference_self] using simpleRibbon_one M q.val.source
  · have he := FiniteWeightTransfer.movedWeights_eq_of_notMem p q t w.val hp
    change i ∈ (FiniteWeightTransfer.movedWeights p q t w.val).support at hi
    change j ∈ (FiniteWeightTransfer.movedWeights p q t w.val).support at hj
    rw [he] at hi hj
    exact w.property i hi j hj hij

theorem continuous_deleteVertex :
    Continuous (fun z : unitInterval × X =>
      deleteVertex M B0 hpos p q hq hne f hmax z.1 z.2) := by
  have h := FiniteWeightTransfer.continuous_moveOrderWeights p q
    (⟨fun x => (f x).val, continuous_subtype_val.comp f.continuous⟩ : C(X, OrderWeights A))
    (deletion_cone M B0 hpos p q hq hne f hmax)
  exact h.subtype_mk _

theorem deleteVertex_zero (x : X) :
    deleteVertex M B0 hpos p q hq hne f hmax 0 x = f x := by
  apply Subtype.ext
  apply OrderWeights.ext
  exact FiniteWeightTransfer.movedWeights_zero p q (f x).val

theorem deleteVertex_one_source (x : X) :
    (deleteVertex M B0 hpos p q hq hne f hmax 1 x).val.weights p = 0 := by
  have hpq : p ≠ q := by
    intro he
    have hdeg := headStep_degree_lt M B0 p.val (hpos p) hne
    rw [← hq, ← he] at hdeg
    exact lt_irrefl _ hdeg
  exact FiniteWeightTransfer.movedWeights_one_source p q hpq (f x).val

set_option maxHeartbeats 2000000 in
/-- This is an actual homotopy of the given continuous map, not merely a
pointwise deletion or a combinatorial collapse claim. -/
noncomputable def deleteVertexHomotopy :
    f.Homotopy
      ⟨fun x => deleteVertex M B0 hpos p q hq hne f hmax 1 x,
        (continuous_deleteVertex M B0 hpos p q hq hne f hmax).comp
          (continuous_const.prodMk continuous_id)⟩ where
  toFun z := deleteVertex M B0 hpos p q hq hne f hmax z.1 z.2
  continuous_toFun := continuous_deleteVertex M B0 hpos p q hq hne f hmax
  map_zero_left := deleteVertex_zero M B0 hpos p q hq hne f hmax
  map_one_left _ := rfl

end Deletion


/-- A literal vertex point of the actual simple-chain weighted subspace. -/
noncomputable def GarsideWeightsOn.vertex {A : Set (IncomingVertex M B0)} (a : A) :
    GarsideWeightsOn M B0 A := by
  classical
  refine ⟨weightVertex a, ?_⟩
  intro i hi j hj _hij
  have hia : i = a := Finset.mem_singleton.mp (Finsupp.support_single_subset hi)
  have hja : j = a := Finset.mem_singleton.mp (Finsupp.support_single_subset hj)
  subst i
  subst j
  simpa only [IncomingVertex.difference_self] using simpleRibbon_one M a.val.source

private theorem eq_vertex_of_support_singleton {A : Set (IncomingVertex M B0)}
    (w : GarsideWeightsOn M B0 A) (r : A)
    (hs : ∀ i ∈ w.val.weights.support, i = r) : w = GarsideWeightsOn.vertex M B0 r := by
  classical
  have hr : r ∈ w.val.weights.support := by
    obtain ⟨i, hi⟩ := w.val.support_nonempty
    simpa only [hs i hi] using hi
  have he : w.val.weights.support = {r} :=
    Finset.eq_singleton_iff_unique_mem.mpr ⟨hr, hs⟩
  have ht := w.val.total
  change (∑ i ∈ w.val.weights.support, w.val.weights i) = 1 at ht
  rw [he, Finset.sum_singleton] at ht
  apply Subtype.ext
  exact weight_eq_vertex_of_one w.val r ht

set_option maxHeartbeats 4000000 in
/-- An actual finite head-closed positive carrier contracts by successive
maximal-degree deletions. The proof explicitly decreases the remaining
carrier cardinality and retains the continuous deletion homotopies. -/
theorem finite_positive_head_closed_homotopic_const
    {A : Set (IncomingVertex M B0)} [Finite A]
    (hpos : ∀ u : A, IncomingVertex.IsPositive M B0 u.val)
    (hclosed : ∀ u : A, headStep M B0 u.val ∈ A)
    (r : A) (hr : r.val = incomingRoot M B0)
    {X : Type*} [TopologicalSpace X] (f : C(X, GarsideWeightsOn M B0 A)) :
    f.Homotopic (ContinuousMap.const X (GarsideWeightsOn.vertex M B0 r)) := by
  classical
  let δ : A → A := fun u => ⟨headStep M B0 u.val, hclosed u⟩
  let ν : A → ℕ := fun u => (degree M u.val.value).toNat
  have hνzero (u : A) : ν u = 0 ↔ u = r := by
    constructor
    · intro hz
      have hn := degree_nonneg_of_mem_actualPositiveParabolic M Set.univ (hpos u).positive
      have hd : degree M u.val.value = 0 := by change (degree M u.val.value).toNat = 0 at hz; omega
      have hv := (degree_eq_zero_iff_of_mem_actualPositiveParabolic M Set.univ
        (hpos u).positive).mp hd
      apply Subtype.ext
      exact ((incoming_value_eq_one_iff M B0 u.val).mp hv).trans hr.symm
    · rintro rfl
      simp only [ν, hr, incomingRoot_value, degree_one, Int.toNat_zero]
  have hδ (u : A) : δ u = u ∨ ν (δ u) < ν u := by
    rcases headStep_measure M B0 u.val with he | hd
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr hd
  have hcore : ∀ n : ℕ, ∀ F : Finset A, F.card = n → r ∈ F →
      (∀ u ∈ F, δ u ∈ F) →
      ∀ g : C(X, GarsideWeightsOn M B0 A),
        (∀ x, ∀ u ∈ (g x).val.weights.support, u ∈ F) →
        g.Homotopic (ContinuousMap.const X (GarsideWeightsOn.vertex M B0 r)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro F hcard hrF hFclosed g hgF
      by_cases honly : ∀ u ∈ F, u = r
      · have heq : g = ContinuousMap.const X (GarsideWeightsOn.vertex M B0 r) := by
          apply ContinuousMap.ext
          intro x
          exact eq_vertex_of_support_singleton M B0 (g x) r (fun u hu => honly u (hgF x u hu))
        exact ⟨ContinuousMap.Homotopy.refl g |>.cast rfl heq⟩
      · push Not at honly
        obtain ⟨i, hiF, hir⟩ := honly
        obtain ⟨p, hpF, hmaxν⟩ := Finset.exists_max_image F ν ⟨r, hrF⟩
        have hνi : 0 < ν i := Nat.pos_of_ne_zero (fun hz => hir ((hνzero i).mp hz))
        have hνp : 0 < ν p := hνi.trans_le (hmaxν i hiF)
        have hpr : p ≠ r := fun he => (ne_of_gt hνp) ((hνzero p).mpr he)
        have hpne : p.val.value ≠ 1 := by
          intro he
          apply hpr
          apply Subtype.ext
          exact ((incoming_value_eq_one_iff M B0 p.val).mp he).trans hr.symm
        have hmaxdeg (u : A) (hu : u ∈ F) : degree M u.val.value ≤ degree M p.val.value := by
          have hb := hmaxν u hu
          have hu0 := degree_nonneg_of_mem_actualPositiveParabolic M Set.univ (hpos u).positive
          have hp0 := degree_nonneg_of_mem_actualPositiveParabolic M Set.univ (hpos p).positive
          change (degree M u.val.value).toNat ≤ (degree M p.val.value).toNat at hb
          omega
        have hmaxactive : ∀ x, ∀ u ∈ (g x).val.weights.support,
            degree M u.val.value ≤ degree M p.val.value :=
          fun x u hu => hmaxdeg u (hgF x u hu)
        let q : A := δ p
        have hq : q.val = headStep M B0 p.val := rfl
        let g' : C(X, GarsideWeightsOn M B0 A) :=
          ⟨fun x => deleteVertex M B0 hpos p q hq hpne g hmaxactive 1 x,
            (continuous_deleteVertex M B0 hpos p q hq hpne g hmaxactive).comp
              (continuous_const.prodMk continuous_id)⟩
        have hg' : ∀ x, ∀ u ∈ (g' x).val.weights.support, u ∈ F.erase p := by
          intro x u hu
          have hup : u ≠ p := by
            intro he
            subst u
            exact (Finsupp.mem_support_iff.mp hu)
              (deleteVertex_one_source M B0 hpos p q hq hpne g hmaxactive x)
          have huF : u ∈ F := by
            rcases FiniteWeightTransfer.movedWeights_support p q 1 (g x).val hu with huold | he
            · exact hgF x u huold
            · subst u
              exact hFclosed p hpF
          exact Finset.mem_erase.mpr ⟨hup, huF⟩
        have hrF' : r ∈ F.erase p := Finset.mem_erase.mpr ⟨Ne.symm hpr, hrF⟩
        have hFclosed' : ∀ u ∈ F.erase p, δ u ∈ F.erase p := by
          intro u hu
          obtain ⟨hup, huF⟩ := Finset.mem_erase.mp hu
          have hδup : δ u ≠ p := by
            intro he
            rcases hδ u with hfix | hdrop
            · exact hup (hfix.symm.trans he)
            · have hb := hmaxν u huF
              rw [he] at hdrop
              omega
          exact Finset.mem_erase.mpr ⟨hδup, hFclosed u huF⟩
        have hless : (F.erase p).card < n := by
          rw [← hcard]
          exact Finset.card_erase_lt_of_mem hpF
        have hrest := ih (F.erase p).card hless (F.erase p) rfl hrF' hFclosed' g' hg'
        exact (show g.Homotopic g' from
          ⟨deleteVertexHomotopy M B0 hpos p q hq hpne g hmaxactive⟩).trans hrest
  let : Fintype A := Fintype.ofFinite A
  exact hcore Finset.univ.card Finset.univ rfl (Finset.mem_univ r)
    (fun u _ => Finset.mem_univ (δ u)) f (fun _ u _ => Finset.mem_univ u)

/-- Contractibility here is a theorem about the actual finite weighted
subspace, derived from actual continuous vertex deletions. -/
theorem contractibleSpace_finite_positive_head_closed
    {A : Set (IncomingVertex M B0)} [Finite A]
    (hpos : ∀ u : A, IncomingVertex.IsPositive M B0 u.val)
    (hclosed : ∀ u : A, headStep M B0 u.val ∈ A)
    (r : A) (hr : r.val = incomingRoot M B0) :
    ContractibleSpace (GarsideWeightsOn M B0 A) := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  exact ⟨GarsideWeightsOn.vertex M B0 r,
    finite_positive_head_closed_homotopic_const M B0 hpos hclosed r hr
      (ContinuousMap.id (GarsideWeightsOn M B0 A))⟩


/-- The earlier finite-ancestry construction supplies all hypotheses of the
finite contraction, for each actual finite positive packet. -/
theorem exists_finite_contractible_positive_enlargement
    (A : Finset (IncomingVertex M B0))
    (hA : ∀ u ∈ A, IncomingVertex.IsPositive M B0 u) :
    ∃ B : Finset (IncomingVertex M B0), A ⊆ B ∧
      (∀ u ∈ B, IncomingVertex.IsPositive M B0 u) ∧
      ContractibleSpace (GarsideWeightsOn M B0 (B : Set (IncomingVertex M B0))) := by
  classical
  obtain ⟨B, hAB, hrB, hBpos, hBclosed⟩ := exists_finite_positive_head_closed M B0 A hA
  refine ⟨B, hAB, hBpos, ?_⟩
  let r : (B : Set (IncomingVertex M B0)) := ⟨incomingRoot M B0, hrB⟩
  exact contractibleSpace_finite_positive_head_closed M B0
    (fun u => hBpos u.val u.property)
    (fun u => hBclosed u.val u.property) r rfl

/-- Restrict an actual simple weighted chain to a containing vertex set. -/
noncomputable def GarsideWeights.restrict (A : Set (IncomingVertex M B0))
    (w : GarsideWeights M B0) (hw : ∀ u ∈ w.val.weights.support, u ∈ A) :
    GarsideWeightsOn M B0 A := by
  refine ⟨weightRestrict A w.val hw, ?_⟩
  intro u hu v hv huv
  have hu' : u.val ∈ w.val.weights.support := by
    rw [Finsupp.mem_support_iff] at hu ⊢
    exact hu
  have hv' : v.val ∈ w.val.weights.support := by
    rw [Finsupp.mem_support_iff] at hv ⊢
    exact hv
  exact w.property u.val hu' v.val hv' huv

theorem GarsideWeights.continuous_restrict_finite
    (A : Set (IncomingVertex M B0)) (hA : A.Finite)
    {X : Type*} [TopologicalSpace X] (f : C(X, GarsideWeights M B0))
    (hf : ∀ x, ∀ u ∈ (f x).val.weights.support, u ∈ A) :
    Continuous (fun x => GarsideWeights.restrict M B0 A (f x) (hf x)) := by
  have h := weightRestrict_continuous_finite A hA
    (⟨fun x => (f x).val, continuous_subtype_val.comp f.continuous⟩ :
      C(X, OrderWeights (IncomingVertex M B0))) hf
  exact h.subtype_mk _

theorem GarsideWeights.include_restrict (A : Set (IncomingVertex M B0))
    (w : GarsideWeights M B0) (hw : ∀ u ∈ w.val.weights.support, u ∈ A) :
    GarsideWeightsOn.include M B0 A (GarsideWeights.restrict M B0 A w hw) = w := by
  apply Subtype.ext
  exact weightRestrict_map A w.val hw

end ArtinNormalisers.Deligne5
