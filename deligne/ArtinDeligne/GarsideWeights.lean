import ArtinDeligne.SimpleTransport
import ArtinDeligne.FiniteAncestry
import ArtinDeligneVendor.Topology.ArtinGroups.Realizations.FiniteWeightsCompact

/-!
# Actual simple-chain weighted spaces and finite carriers

These spaces have the actual subspace topology inside the genuine weighted
order realization of incoming ribbon vertices. Supports are required to
have simple connecting arrows. This is a hereditary geometric simplicial
condition, not a contractibility field. Finite coordinate continuity and
compact finite-carrier factorization use the verified realization topology.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ArtinNormalisers.Deligne5

open Ribbon2 Homotopy5 Chamber3 OAI.HarmonicArtin Topology

namespace FiniteWeightCoordinates

variable {P : Type*} [PartialOrder P]

/-- The actual finite weighted realization embeds in its real coordinates. -/
theorem isClosedEmbedding_coordinates [Finite P] :
    IsClosedEmbedding (fun w : OrderWeights P => fun p => w.weights p) := by
  apply (continuous_pi weightEval_continuous).isClosedEmbedding
  intro u v h
  apply OrderWeights.ext
  exact DFunLike.ext' h

/-- No single-chain carrier assumption is needed in a finite vertex set. -/
theorem continuous_iff_coordinates [Finite P] {X : Type*} [TopologicalSpace X]
    (f : X → OrderWeights P) :
    Continuous f ↔ ∀ p, Continuous (fun x => (f x).weights p) := by
  constructor
  · intro h p
    exact (weightEval_continuous p).comp h
  · intro h
    exact (isClosedEmbedding_coordinates (P := P)).isEmbedding.isInducing.continuous_iff.mpr
      (continuous_pi h)

end FiniteWeightCoordinates

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (B0 : RibbonObject M)

/-- The actual simple-chain condition for the fixed incoming vertex poset. -/
def garsideWeightsSet : Set (OrderWeights (IncomingVertex M B0)) :=
  {w | ∀ u ∈ w.weights.support, ∀ v ∈ w.weights.support, u ≤ v →
    SimpleRibbon M u.source v.source (u.difference v)}

/-- The hereditary simple-chain subspace of the genuine incoming realization. -/
abbrev GarsideWeights := ↥(garsideWeightsSet M B0)

theorem GarsideWeights.simple (w : GarsideWeights M B0)
    {u v : IncomingVertex M B0} (hu : u ∈ w.val.weights.support)
    (hv : v ∈ w.val.weights.support) (huv : u ≤ v) :
    SimpleRibbon M u.source v.source (u.difference v) := w.property u hu v hv huv

/-- The same actual condition on a specified vertex subposet. -/
def garsideWeightsOnSet (A : Set (IncomingVertex M B0)) : Set (OrderWeights A) :=
  {w | ∀ u ∈ w.weights.support, ∀ v ∈ w.weights.support, u ≤ v →
    SimpleRibbon M u.val.source v.val.source (u.val.difference v.val)}

abbrev GarsideWeightsOn (A : Set (IncomingVertex M B0)) := ↥(garsideWeightsOnSet M B0 A)

/-- Actual support inclusion preserves the simple-chain condition. -/
noncomputable def GarsideWeightsOn.include (A : Set (IncomingVertex M B0))
    (w : GarsideWeightsOn M B0 A) : GarsideWeights M B0 := by
  classical
  refine ⟨weightMap (weightInclusion A) w.val, ?_⟩
  intro u hu v hv huv
  rw [weightMap_support_embedding (weightInclusion A) Subtype.val_injective] at hu hv
  obtain ⟨u', hu', rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨v', hv', rfl⟩ := Finset.mem_image.mp hv
  exact w.property u' hu' v' hv' huv

theorem GarsideWeightsOn.continuous_include (A : Set (IncomingVertex M B0)) :
    Continuous (GarsideWeightsOn.include M B0 A) :=
  ((weightMap_continuous (weightInclusion A)).comp continuous_subtype_val).subtype_mk _

/-- Compact actual simple-chain maps factor through a finite actual subposet.
The geometric simple-chain condition is retained by the factorization. -/
theorem GarsideWeights.compact_map_finite_carrier
    {X : Type*} [TopologicalSpace X] [CompactSpace X] (f : C(X, GarsideWeights M B0)) :
    ∃ (A : Set (IncomingVertex M B0)) (_ : A.Finite)
      (g : C(X, GarsideWeightsOn M B0 A)),
      (⟨GarsideWeightsOn.include M B0 A,
        GarsideWeightsOn.continuous_include M B0 A⟩ :
        C(GarsideWeightsOn M B0 A, GarsideWeights M B0)).comp g = f := by
  classical
  let f₀ : C(X, OrderWeights (IncomingVertex M B0)) :=
    ⟨fun x => (f x).val, continuous_subtype_val.comp f.continuous⟩
  obtain ⟨A, hA, g₀, hg⟩ := OAI.HarmonicArtin.compact_map_finite_carrier f₀
  have hpoint (x : X) : weightMap (weightInclusion A) (g₀ x) = (f x).val :=
    congrArg (fun F : C(X, OrderWeights (IncomingVertex M B0)) => F x) hg
  have hallowed (x : X) : g₀ x ∈ garsideWeightsOnSet M B0 A := by
    intro u hu v hv huv
    have hu' : u.val ∈ (f x).val.weights.support := by
      rw [← hpoint x, weightMap_support_embedding (weightInclusion A) Subtype.val_injective]
      exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
    have hv' : v.val ∈ (f x).val.weights.support := by
      rw [← hpoint x, weightMap_support_embedding (weightInclusion A) Subtype.val_injective]
      exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
    exact (f x).property u.val hu' v.val hv' huv
  let g : C(X, GarsideWeightsOn M B0 A) :=
    ⟨fun x => ⟨g₀ x, hallowed x⟩, g₀.continuous.subtype_mk _⟩
  refine ⟨A, hA, g, ?_⟩
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  exact hpoint x

/-- Positivity is actual generated positivity of the incoming label. -/
def IncomingVertex.IsPositive (u : IncomingVertex M B0) : Prop :=
  PositiveReducedArrow M u.source B0 u.value

/-- The genuine identity incoming vertex. -/
def incomingRoot : IncomingVertex M B0 := ⟨B0, 1, .identity B0⟩

@[simp] theorem incomingRoot_value : (incomingRoot M B0).value = 1 := rfl

theorem incoming_value_eq_one_iff (u : IncomingVertex M B0) :
    u.value = 1 ↔ u = incomingRoot M B0 := by
  constructor
  · intro h
    exact IncomingVertex.ext_value h
  · rintro rfl
    rfl

theorem incomingRoot_positive : IncomingVertex.IsPositive M B0 (incomingRoot M B0) :=
  .identity B0

/-- Removing a greatest simple head gives an actual positive cone vertex. -/
theorem exists_positive_headTail (u : IncomingVertex M B0)
    (hu : IncomingVertex.IsPositive M B0 u) :
    ∃ v : IncomingVertex M B0,
      IncomingVertex.IsPositive M B0 v ∧ u ≤ v ∧
      SimpleRibbon M u.source v.source (u.difference v) ∧
      (∀ q : IncomingVertex M B0, IncomingVertex.IsPositive M B0 q → u ≤ q →
        SimpleRibbon M u.source q.source (u.difference q) →
        q ≤ v ∧ SimpleRibbon M q.source v.source (q.difference v)) ∧
      (u.value ≠ 1 → degree M v.value < degree M u.value) := by
  obtain ⟨U, d, a, hd, ha, hpa, hgreat, hstrict⟩ :=
    greatest_simple_ribbon_prefix_with_tail M hu
  let v : IncomingVertex M B0 := ⟨U, a, ha.toReducedArrow⟩
  have hdiff : u.difference v = d := by
    dsimp only [IncomingVertex.difference, v]
    rw [hpa]
    group
  refine ⟨v, ha, ?_, ?_, ?_, ?_⟩
  · change PositiveReducedArrow M u.source U (u.difference v)
    rw [hdiff]
    exact hd.1
  · simpa only [hdiff] using hd
  · intro q hq huq hsq
    have hrp : RibbonPrefix M (u.difference q) u.value :=
      ⟨q.value, hq.positive, by dsimp only [IncomingVertex.difference]; group⟩
    have hrhead := hgreat q.source (u.difference q) hsq hrp
    obtain ⟨t, ht, hdt⟩ := positive_ribbon_prefix_tail M hsq.1 hd.1 hrhead
    have hqa : q.value = t * a := by
      calc
        q.value = (u.difference q)⁻¹ * u.value := by
          dsimp only [IncomingVertex.difference]
          group
        _ = t * a := by rw [hpa, hdt]; group
    have hqv : q.difference v = t := by
      dsimp only [IncomingVertex.difference, v]
      rw [hqa]
      group
    constructor
    · change PositiveReducedArrow M q.source U (q.difference v)
      rw [hqv]
      exact ht
    · rw [hqv]
      have hsimple : SimpleRibbon M u.source U (u.difference q * t) := by
        simpa only [← hdt] using hd
      exact SimpleRibbon.tail M hsimple hsq.1 ht
  · intro hne
    exact (hstrict hne).2

/-- A fixed, proved greatest-simple-head removal for every positive vertex. -/
noncomputable def positiveHeadTail (u : IncomingVertex M B0)
    (hu : IncomingVertex.IsPositive M B0 u) : IncomingVertex M B0 :=
  Classical.choose (exists_positive_headTail M B0 u hu)

theorem positiveHeadTail_spec (u : IncomingVertex M B0)
    (hu : IncomingVertex.IsPositive M B0 u) :
    IncomingVertex.IsPositive M B0 (positiveHeadTail M B0 u hu) ∧
      u ≤ positiveHeadTail M B0 u hu ∧
      SimpleRibbon M u.source (positiveHeadTail M B0 u hu).source
        (u.difference (positiveHeadTail M B0 u hu)) ∧
      (∀ q : IncomingVertex M B0, IncomingVertex.IsPositive M B0 q → u ≤ q →
        SimpleRibbon M u.source q.source (u.difference q) →
        q ≤ positiveHeadTail M B0 u hu ∧
          SimpleRibbon M q.source (positiveHeadTail M B0 u hu).source
            (q.difference (positiveHeadTail M B0 u hu))) ∧
      (u.value ≠ 1 → degree M (positiveHeadTail M B0 u hu).value < degree M u.value) :=
  Classical.choose_spec (exists_positive_headTail M B0 u hu)


/-- Total head removal fixes the identity and all nonpositive vertices. -/
noncomputable def headStep (u : IncomingVertex M B0) : IncomingVertex M B0 := by
  classical
  exact if h : IncomingVertex.IsPositive M B0 u ∧ u.value ≠ 1
    then positiveHeadTail M B0 u h.1 else u

theorem headStep_eq (u : IncomingVertex M B0)
    (hu : IncomingVertex.IsPositive M B0 u) (hne : u.value ≠ 1) :
    headStep M B0 u = positiveHeadTail M B0 u hu := by
  classical
  unfold headStep
  rw [dite_eq_left ⟨hu, hne⟩]

theorem headStep_eq_self_of_value_eq_one (u : IncomingVertex M B0) (hu : u.value = 1) :
    headStep M B0 u = u := by
  classical
  simp only [headStep, hu, ne_eq, not_true_eq_false, and_false, ↓reduceDIte]

theorem headStep_positive (u : IncomingVertex M B0)
    (hu : IncomingVertex.IsPositive M B0 u) :
    IncomingVertex.IsPositive M B0 (headStep M B0 u) := by
  classical
  by_cases hne : u.value ≠ 1
  · rw [headStep_eq M B0 u hu hne]
    exact (positiveHeadTail_spec M B0 u hu).1
  · rw [headStep_eq_self_of_value_eq_one M B0 u (not_ne_iff.mp hne)]
    exact hu

theorem headStep_degree_lt (u : IncomingVertex M B0)
    (hu : IncomingVertex.IsPositive M B0 u) (hne : u.value ≠ 1) :
    degree M (headStep M B0 u).value < degree M u.value := by
  rw [headStep_eq M B0 u hu hne]
  exact (positiveHeadTail_spec M B0 u hu).2.2.2.2 hne

theorem headStep_measure (u : IncomingVertex M B0) :
    headStep M B0 u = u ∨
      (degree M (headStep M B0 u).value).toNat < (degree M u.value).toNat := by
  classical
  by_cases hu : IncomingVertex.IsPositive M B0 u
  · by_cases hne : u.value ≠ 1
    · right
      have hlt := headStep_degree_lt M B0 u hu hne
      have hn := degree_nonneg_of_mem_actualPositiveParabolic M Set.univ
        (headStep_positive M B0 u hu).positive
      omega
    · exact Or.inl (headStep_eq_self_of_value_eq_one M B0 u (not_ne_iff.mp hne))
  · left
    simp only [headStep, hu, false_and, ↓reduceDIte]

/-- Finite positive carriers have genuine finite head-closed enlargements,
containing the actual identity vertex and no nonpositive vertices. -/
theorem exists_finite_positive_head_closed (A : Finset (IncomingVertex M B0))
    (hA : ∀ u ∈ A, IncomingVertex.IsPositive M B0 u) :
    ∃ B : Finset (IncomingVertex M B0), A ⊆ B ∧ incomingRoot M B0 ∈ B ∧
      (∀ u ∈ B, IncomingVertex.IsPositive M B0 u) ∧
      ∀ u ∈ B, headStep M B0 u ∈ B := by
  classical
  obtain ⟨B, hAB, hBpos, hBclosed⟩ := exists_finite_closed_ancestry
    (headStep M B0) (fun u => (degree M u.value).toNat)
    (IncomingVertex.IsPositive M B0) (headStep_measure M B0) (headStep_positive M B0)
    (insert (incomingRoot M B0) A) (by
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact incomingRoot_positive M B0
      · exact hA u hu)
  exact ⟨B, Finset.Subset.trans (Finset.subset_insert _ _) hAB,
    hAB (Finset.mem_insert_self _ _), hBpos, hBclosed⟩

/-- Every simple neighbor in a positive region can be joined to the actual
head-removal cone vertex. This is the finite vertex-deletion carrier law. -/
theorem headStep_cone (u : IncomingVertex M B0)
    (hu : IncomingVertex.IsPositive M B0 u) (hne : u.value ≠ 1)
    (q : IncomingVertex M B0) (hq : IncomingVertex.IsPositive M B0 q)
    (huq : u ≤ q) (hs : SimpleRibbon M u.source q.source (u.difference q)) :
    q ≤ headStep M B0 u ∧
      SimpleRibbon M q.source (headStep M B0 u).source (q.difference (headStep M B0 u)) := by
  rw [headStep_eq M B0 u hu hne]
  exact (positiveHeadTail_spec M B0 u hu).2.2.2.1 q hq huq hs

end ArtinNormalisers.Deligne5
