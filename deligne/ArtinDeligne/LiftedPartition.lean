import ArtinDeligne.LiftedCanonicalCover
import ArtinHomotopy.NerveComparison

/-!
# A genuine partition of unity on the actual lifted canonical cover

A finite partition on the original complement is split among its actual open,
disjoint sheets. The resulting function on a sheet is the original function
composed with endpoint projection, and is zero off that sheet. Closed supports
remain inside the lifted canonical cells. Local finiteness uses finite base
types and one possible sheet per base type near each point, without assuming
a metric, paracompactness or countability on the universal cover.

A targeted GitHub search `PartitionOfUnity covering language:Lean` (2026-11-14)
returned mathlib copies and unrelated fibration/manifold sources; pinned local
mathlib exposes no covering-partition constructor. The construction below is
local authoring using the already pinned mathlib partition/support APIs.
No additional supplier is imported or claimed.
-/

set_option autoImplicit false

noncomputable section

namespace ArtinNormalisers.Deligne5

open Set Function Filter Topology
open scoped Topology

namespace FiniteSheetPartition

variable {X Y S : Type*} [TopologicalSpace X] [TopologicalSpace Y] {F : S → Type*}
  (p : Y → X) (hp : Continuous p) (T : S → Set X)
  (W : ∀ s, F s → Set Y) (ho : ∀ s e, IsOpen (W s e))
  (hd : ∀ s, Pairwise fun e f => Disjoint (W s e) (W s f))
  (hc : ∀ s y, p y ∈ T s → ∃ e, y ∈ W s e)
  (ρ : PartitionOfUnity S X) (hT : ∀ s, tsupport (ρ s) ⊆ T s)

/-- The literal split weight; no partition identity is assumed. -/
def weight (i : Sigma F) (y : Y) : ℝ := by
  classical
  exact if y ∈ W i.1 i.2 then ρ i.1 (p y) else 0

/-- The closed localized base support, before constructing any continuous weight. -/
def supportPiece (i : Sigma F) : Set Y := W i.1 i.2 ∩ p ⁻¹' tsupport (ρ i.1)

include hd in
omit [TopologicalSpace Y] in
theorem sheet_eq_of_mem {s : S} {e f : F s} {y : Y}
    (he : y ∈ W s e) (hf : y ∈ W s f) : e = f := by
  by_contra h
  exact Set.disjoint_left.mp (hd s h) he hf

include hp ho hd hc hT in
theorem isClosed_supportPiece (i : Sigma F) : IsClosed (supportPiece p W ρ i) := by
  rw [← isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro y hy
  by_cases hs : p y ∈ tsupport (ρ i.1)
  · obtain ⟨e, he⟩ := hc i.1 y (hT i.1 hs)
    have hne : e ≠ i.2 := by
      intro h
      exact hy ⟨h ▸ he, hs⟩
    filter_upwards [(ho i.1 e).mem_nhds he] with z hz
    exact fun h => Set.disjoint_left.mp (hd i.1 hne) hz h.1
  · filter_upwards [((isClosed_tsupport (ρ i.1)).isOpen_compl.preimage hp).mem_nhds hs] with z hz
    exact fun h => hz h.2

omit [TopologicalSpace Y] in
theorem support_weight_subset (i : Sigma F) :
    Function.support (weight p W ρ i) ⊆ supportPiece p W ρ i := by
  classical
  intro y hy
  by_cases hs : y ∈ W i.1 i.2
  · refine ⟨hs, subset_tsupport (ρ i.1) ?_⟩
    simpa only [Function.mem_support, weight, ite_eq_left hs] using hy
  · simp only [Function.mem_support, weight, ite_eq_right hs, ne_eq, not_true_eq_false] at hy

include hp ho hd hc hT in
theorem tsupport_weight_subset (i : Sigma F) :
    tsupport (weight p W ρ i) ⊆ supportPiece p W ρ i :=
  closure_minimal (support_weight_subset p W ρ i) (isClosed_supportPiece p hp T W ho hd hc ρ hT i)

include hp ho hd hc hT in
theorem continuous_weight (i : Sigma F) : Continuous (weight p W ρ i) := by
  classical
  apply continuous_of_tsupport
  intro y hy
  have hs := (tsupport_weight_subset p hp T W ho hd hc ρ hT i hy).1
  apply ((ρ i.1).continuous.comp hp).continuousAt.congr_of_eventuallyEq
  filter_upwards [(ho i.1 i.2).mem_nhds hs] with z hz
  simp only [weight, ite_eq_left hz, Function.comp_def]

include hp ho hd hc hT in
theorem exists_local_unique (s : S) (y : Y) :
    ∃ N ∈ 𝓝 y, ∀ e f : F s,
      (supportPiece p W ρ ⟨s, e⟩ ∩ N).Nonempty →
      (supportPiece p W ρ ⟨s, f⟩ ∩ N).Nonempty → e = f := by
  by_cases hs : p y ∈ tsupport (ρ s)
  · obtain ⟨e, he⟩ := hc s y (hT s hs)
    refine ⟨W s e, (ho s e).mem_nhds he, ?_⟩
    rintro f g ⟨z, hz, hze⟩ ⟨w, hw, hwe⟩
    exact (sheet_eq_of_mem W hd hz.1 hze).trans (sheet_eq_of_mem W hd hw.1 hwe).symm
  · refine ⟨p ⁻¹' (tsupport (ρ s))ᶜ,
      ((isClosed_tsupport (ρ s)).isOpen_compl.preimage hp).mem_nhds hs, ?_⟩
    rintro e f ⟨z, hz, hzn⟩ _
    exact (hzn hz.2).elim

include hp ho hd hc hT in
theorem locallyFinite_supportPiece [Finite S] : LocallyFinite (supportPiece p W ρ) := by
  intro y
  choose N hN hu using exists_local_unique p hp T W ho hd hc ρ hT (y := y)
  refine ⟨⋂ s, N s, Filter.iInter_mem.mpr hN, ?_⟩
  apply Set.Finite.of_finite_image (f := Sigma.fst) (Set.toFinite _)
  rintro ⟨s, e⟩ he ⟨t, f⟩ hf hst
  dsimp at hst
  subst t
  have he' : (supportPiece p W ρ ⟨s, e⟩ ∩ N s).Nonempty :=
    he.mono (Set.inter_subset_inter_right _ (Set.iInter_subset N s))
  have hf' : (supportPiece p W ρ ⟨s, f⟩ ∩ N s).Nonempty :=
    hf.mono (Set.inter_subset_inter_right _ (Set.iInter_subset N s))
  exact congrArg (Sigma.mk s) (hu s e f he' hf')

include hp ho hd hc hT in
theorem locallyFinite_support_weight [Finite S] :
    LocallyFinite fun i => Function.support (weight p W ρ i) :=
  (locallyFinite_supportPiece p hp T W ho hd hc ρ hT).subset (support_weight_subset p W ρ)

include hd hc hT in
omit [TopologicalSpace Y] in
theorem sum_weight (y : Y) : (∑ᶠ i : Sigma F, weight p W ρ i y) = ∑ᶠ s, ρ s (p y) := by
  classical
  have hmap : Set.MapsTo Sigma.fst (Function.support fun i => weight p W ρ i y)
      (Function.support fun s => ρ s (p y)) := by
    intro i hi
    have hs := support_weight_subset p W ρ i hi
    simpa only [Function.mem_support, weight, ite_eq_left hs.1] using hi
  have hinj : Set.InjOn Sigma.fst (Function.support fun i => weight p W ρ i y) := by
    rintro ⟨s, e⟩ he ⟨t, f⟩ hf hst
    dsimp at hst
    subst t
    exact congrArg (Sigma.mk s) (sheet_eq_of_mem W hd
      (support_weight_subset p W ρ ⟨s, e⟩ he).1
      (support_weight_subset p W ρ ⟨s, f⟩ hf).1)
  have hsurj : Set.SurjOn Sigma.fst (Function.support fun i => weight p W ρ i y)
      (Function.support fun s => ρ s (p y)) := by
    intro s hs
    obtain ⟨e, he⟩ := hc s y (hT s (subset_tsupport (ρ s) hs))
    exact ⟨⟨s, e⟩, by simpa only [Function.mem_support, weight, ite_eq_left he] using hs, rfl⟩
  rw [← finsum_mem_support (fun i => weight p W ρ i y),
    ← finsum_mem_support (fun s => ρ s (p y))]
  apply finsum_mem_eq_of_bijOn Sigma.fst ⟨hmap, hinj, hsurj⟩
  intro i hi
  simp only [weight, ite_eq_left (support_weight_subset p W ρ i hi).1]

/-- The split functions form an actual partition on the total space. -/
def partition [Finite S] : PartitionOfUnity (Sigma F) Y where
  toFun i := ⟨weight p W ρ i, continuous_weight p hp T W ho hd hc ρ hT i⟩
  locallyFinite' := locallyFinite_support_weight p hp T W ho hd hc ρ hT
  nonneg' i y := by
    classical
    change 0 ≤ weight p W ρ i y
    unfold weight
    split_ifs
    · exact ρ.nonneg _ _
    · exact le_rfl
  sum_eq_one' y _ := (sum_weight p T W hd hc ρ hT y).trans (ρ.sum_eq_one (Set.mem_univ _))
  sum_le_one' y := (sum_weight p T W hd hc ρ hT y).trans_le (ρ.sum_le_one _)

/-- Closed supports are controlled, including at zero-valued boundary points. -/
theorem partition_tsupport_subset [Finite S] (i : Sigma F) :
    tsupport (partition p hp T W ho hd hc ρ hT i) ⊆ supportPiece p W ρ i :=
  tsupport_weight_subset p hp T W ho hd hc ρ hT i

end FiniteSheetPartition

/-- Reindex an already constructed partition through a genuine index equivalence. -/
def reindexPartitionOfUnity {X K L : Type*} [TopologicalSpace X]
    (e : K ≃ L) (ρ : PartitionOfUnity L X) : PartitionOfUnity K X where
  toFun k := ρ (e k)
  locallyFinite' := ρ.locallyFinite.comp_injective e.injective
  nonneg' k x := ρ.nonneg (e k) x
  sum_eq_one' x hx := by
    rw [finsum_comp (g := fun l => ρ l x) e e.bijective]
    exact ρ.sum_eq_one hx
  sum_le_one' x := by
    rw [finsum_comp (g := fun l => ρ l x) e e.bijective]
    exact ρ.sum_le_one x

open Theorem18 Chamber3 Asphericity5

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- The finite canonical cover has an ordinary base partition in the original topology. -/
theorem exists_canonicalBasePartition :
    ∃ ρ : PartitionOfUnity (actualCanonicalType M J) (Complement M J),
      ρ.IsSubordinate (actualCanonicalTypeSet M J) := by
  let : MetricSpace (Complement M J) := Homotopy5.complementMetricSpace M J
  apply PartitionOfUnity.exists_isSubordinate isClosed_univ (actualCanonicalTypeSet M J)
    (isOpen_actualCanonicalTypeSet M J)
  intro x _
  rw [iUnion_actualCanonicalTypeSet M J]
  exact Set.mem_univ x

def canonicalBasePartition : PartitionOfUnity (actualCanonicalType M J) (Complement M J) :=
  Classical.choose (exists_canonicalBasePartition M J)

theorem canonicalBasePartition_subordinate :
    (canonicalBasePartition M J).IsSubordinate (actualCanonicalTypeSet M J) :=
  Classical.choose_spec (exists_canonicalBasePartition M J)

abbrev CanonicalTubeFiber (σ : actualCanonicalType M J) :=
  {z : ComplementUniversalCover M J // complementUniversalCoverProjection M J z =
    tubeBasepoint M J (actualCanonicalTypeChamber M J σ)}

/-- Only repackage the actual fields; the underlying fiber points are unchanged. -/
def liftedCanonicalIndexEquivSigma :
    LiftedCanonicalIndex M J ≃ Sigma (CanonicalTubeFiber M J) where
  toFun A := ⟨A.base, A.fiberPoint⟩
  invFun i := ⟨i.1, i.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

def canonicalTubeSheet (σ : actualCanonicalType M J) (e : CanonicalTubeFiber M J σ) :
    Set (ComplementUniversalCover M J) :=
  liftedTubeSheet M J ⟨actualCanonicalTypeChamber M J σ, e⟩

theorem canonicalBasePartition_tsupport_tube (σ : actualCanonicalType M J) :
    tsupport (canonicalBasePartition M J σ) ⊆
      actualTubeSet M J (actualCanonicalTypeChamber M J σ) :=
  (canonicalBasePartition_subordinate M J σ).trans
    (actualCanonicalTypeSet_subset_actualTubeSet M J σ)

/-- The actual split partition before the harmless structure/Sigma reindexing. -/
def liftedCanonicalSigmaPartition :
    PartitionOfUnity (Sigma (CanonicalTubeFiber M J)) (ComplementUniversalCover M J) :=
  FiniteSheetPartition.partition (complementUniversalCoverProjection M J)
    (continuous_complementUniversalCoverProjection M J)
    (fun σ => actualTubeSet M J (actualCanonicalTypeChamber M J σ))
    (canonicalTubeSheet M J) (fun _σ e => isOpen_liftedTubeSheet M J ⟨_, e⟩)
    (fun _σ _ _ hne => disjoint_liftedTubeSheet_same_chamber M J _ hne)
    (fun _σ z hz => exists_mem_liftedTubeSheet_at_chamber M J _ z hz)
    (canonicalBasePartition M J) (canonicalBasePartition_tsupport_tube M J)

/-- An actual partition on the actual universal cover, indexed by its lifted canonical cells. -/
def actualLiftedCanonicalPartition :
    PartitionOfUnity (LiftedCanonicalIndex M J) (ComplementUniversalCover M J) :=
  reindexPartitionOfUnity (liftedCanonicalIndexEquivSigma M J) (liftedCanonicalSigmaPartition M J)

open scoped Classical in
/-- Literal split-weight formula: the base weight on its sheet, zero elsewhere. -/
theorem actualLiftedCanonicalPartition_apply (A : LiftedCanonicalIndex M J)
    (z : ComplementUniversalCover M J) :
    actualLiftedCanonicalPartition M J A z =
      if z ∈ liftedTubeSheet M J A.toLiftedTubeIndex
      then canonicalBasePartition M J A.base (complementUniversalCoverProjection M J z)
      else 0 := by
  classical
  rfl

/-- Closed support, including its boundary, lies in the specified lifted canonical open. -/
theorem actualLiftedCanonicalPartition_subordinate :
    (actualLiftedCanonicalPartition M J).IsSubordinate (liftedCanonicalSet M J) := by
  intro A z hz
  have hs := FiniteSheetPartition.partition_tsupport_subset
    (complementUniversalCoverProjection M J) (continuous_complementUniversalCoverProjection M J)
    (fun σ => actualTubeSet M J (actualCanonicalTypeChamber M J σ))
    (canonicalTubeSheet M J) (fun _σ e => isOpen_liftedTubeSheet M J ⟨_, e⟩)
    (fun _σ _ _ hne => disjoint_liftedTubeSheet_same_chamber M J _ hne)
    (fun _σ z hz => exists_mem_liftedTubeSheet_at_chamber M J _ z hz)
    (canonicalBasePartition M J) (canonicalBasePartition_tsupport_tube M J)
    ((liftedCanonicalIndexEquivSigma M J) A) hz
  exact ⟨hs.1, canonicalBasePartition_subordinate M J A.base hs.2⟩

end ArtinNormalisers.Deligne5
