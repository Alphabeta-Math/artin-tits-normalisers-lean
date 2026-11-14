import ArtinDeligneVendor.Topology.ArtinGroups.Realizations.FiniteWeightsCompact

/-!
# The actual weak topology of hereditary weighted subcomplexes

A hereditary predicate on finite vertex sets cuts out a closed subspace of
the genuine order realization. Its topology is determined by its admissible
finite chain simplices. This is proved from finite closed carrier faces in
each original chart, rather than assumed as a topology on a substitute space.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ArtinNormalisers.Deligne5

open OAI.HarmonicArtin Topology Convexity Simplicial CategoryTheory Opposite
attribute [local instance] Classical.decEq Classical.propDecidable

variable {P : Type*} [PartialOrder P]

/-- A finite-face predicate closed under taking subfaces. -/
def SupportHereditary (S : Finset P → Prop) : Prop :=
  ∀ ⦃A B : Finset P⦄, A ⊆ B → S B → S A

/-- The genuine subspace of the weighted order realization. -/
abbrev SubcomplexWeights (S : Finset P → Prop) :=
  {w : OrderWeights P // S w.weights.support}

/-- A fixed carrier condition in the original weighted realization. -/
def weightCarrierSet (F : Finset P) : Set (OrderWeights P) :=
  {w | w.weights.support ⊆ F}

theorem mem_weightCarrierSet_iff (F : Finset P) (w : OrderWeights P) :
    w ∈ weightCarrierSet F ↔ ∀ p, p ∉ F → w.weights p = 0 := by
  constructor
  · intro hw p hp
    exact Finsupp.notMem_support_iff.mp (fun h => hp (hw h))
  · intro hw p hp
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hp) (hw p hn)

theorem isClosed_weightCarrierSet (F : Finset P) : IsClosed (weightCarrierSet F) := by
  have he : weightCarrierSet F = ⋂ p, ⋂ (_ : p ∉ F), {w | w.weights p = 0} := by
    ext w
    simp only [mem_weightCarrierSet_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [he]
  exact isClosed_iInter fun p => isClosed_iInter fun _ =>
    isClosed_eq (weightEval_continuous p) continuous_const

/-- A bad finite support stays bad when all of its positive coordinates
remain positive. This proves actual closedness of the subcomplex. -/
theorem isClosed_subcomplexWeights (S : Finset P → Prop) (hS : SupportHereditary S) :
    IsClosed ({w | S w.weights.support} : Set (OrderWeights P)) := by
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro w hw
  let U : Set (OrderWeights P) := ⋂ p ∈ w.weights.support, {v | 0 < v.weights p}
  have hopen : IsOpen U := isOpen_biInter_finset fun p _ =>
    isOpen_lt continuous_const (weightEval_continuous p)
  have hwU : w ∈ U := by
    apply Set.mem_iInter.mpr
    intro p
    apply Set.mem_iInter.mpr
    intro hp
    exact lt_of_le_of_ne (w.nonneg p) (Ne.symm (Finsupp.mem_support_iff.mp hp))
  apply Filter.mem_of_superset (hopen.mem_nhds hwU)
  intro v hv
  change ¬S v.weights.support
  intro hSv
  apply hw
  apply hS ?_ hSv
  intro p hp
  have hpos := Set.mem_iInter.mp (Set.mem_iInter.mp hv p) hp
  exact Finsupp.mem_support_iff.mpr (ne_of_gt hpos)

theorem weightInclusion_support_subset (F : Finset P) (w : OrderWeights (F : Set P)) :
    (weightMap (weightInclusion (F : Set P)) w).weights.support ⊆ F := by
  rw [weightMap_support_embedding _ Subtype.val_injective]
  intro p hp
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hp
  exact q.property

/-- Any admissible finite vertex set includes continuously into the actual
hereditary subspace. It need not be a chain. -/
noncomputable def subcomplexFiniteInclusion (S : Finset P → Prop)
    (hS : SupportHereditary S) (F : Finset P) (hF : S F)
    (w : OrderWeights (F : Set P)) : SubcomplexWeights S :=
  ⟨weightMap (weightInclusion (F : Set P)) w,
    hS (weightInclusion_support_subset F w) hF⟩

theorem continuous_subcomplexFiniteInclusion (S : Finset P → Prop)
    (hS : SupportHereditary S) (F : Finset P) (hF : S F) :
    Continuous (subcomplexFiniteInclusion S hS F hF) :=
  (weightMap_continuous (weightInclusion (F : Set P))).subtype_mk _

/-- An admissible chain simplex with the actual inherited target topology. -/
noncomputable def subcomplexChart (S : Finset P → Prop) (hS : SupportHereditary S)
    {n : ℕ} (x : Fin (n + 1) →o P) (hx : S (Finset.univ.image x))
    (z : StdSimplex ℝ (Fin (n + 1))) : SubcomplexWeights S :=
  ⟨orderWeightsOfChain x z, hS (chainWeights_support x z) hx⟩

theorem continuous_subcomplexChart (S : Finset P → Prop) (hS : SupportHereditary S)
    {n : ℕ} (x : Fin (n + 1) →o P) (hx : S (Finset.univ.image x)) :
    Continuous (subcomplexChart S hS x hx) :=
  (chainWeightsChart_continuous x).subtype_mk _


/-- Carrier faces are closed in each original simplex chart. -/
def chainCarrierFace {n : ℕ} (x : Fin (n + 1) →o P) (F : Finset P) :
    Set (StdSimplex ℝ (Fin (n + 1))) :=
  {z | (orderWeightsOfChain x z).weights.support ⊆ F}

theorem isClosed_chainCarrierFace {n : ℕ} (x : Fin (n + 1) →o P) (F : Finset P) :
    IsClosed (chainCarrierFace x F) :=
  (isClosed_weightCarrierSet F).preimage (chainWeightsChart_continuous x)

/-- On a fixed finite carrier face the actual restriction is continuous. -/
noncomputable def chainCarrierRestriction {n : ℕ} (x : Fin (n + 1) →o P) (F : Finset P) :
    C(chainCarrierFace x F, OrderWeights (F : Set P)) := by
  let g : C(chainCarrierFace x F, OrderWeights P) :=
    ⟨fun z => orderWeightsOfChain x z.val,
      (chainWeightsChart_continuous x).comp continuous_subtype_val⟩
  exact ⟨fun z => weightRestrict (F : Set P) (g z) z.property,
    weightRestrict_continuous_finite (F : Set P) F.finite_toSet g (fun z => z.property)⟩

theorem chainCarrierRestriction_map {n : ℕ} (x : Fin (n + 1) →o P) (F : Finset P)
    (z : chainCarrierFace x F) :
    weightMap (weightInclusion (F : Set P)) (chainCarrierRestriction x F z) =
      orderWeightsOfChain x z.val :=
  weightRestrict_map (F : Set P) (orderWeightsOfChain x z.val) z.property

theorem chain_range_isChain {n : ℕ} (x : Fin (n + 1) →o P) :
    IsChain (· ≤ ·) (↑(Finset.univ.image x) : Set P) := by
  intro a ha b hb _hab
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hb
  exact (le_total i j).imp (fun h => x.monotone h) (fun h => x.monotone h)

theorem finiteChainOrder_range (F : Finset P) (hF : IsChain (· ≤ ·) (↑F : Set P))
    (hne : F.Nonempty) : Finset.univ.image (finiteChainOrder F hF hne) = F := by
  ext p
  constructor
  · intro hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    exact (finiteChainEnum F hF hne i).property
  · intro hp
    refine Finset.mem_image.mpr ⟨(finiteChainEnum F hF hne).symm ⟨p, hp⟩,
      Finset.mem_univ _, ?_⟩
    exact congrArg Subtype.val ((finiteChainEnum F hF hne).apply_symm_apply ⟨p, hp⟩)

/-- The ordinary finite-face coordinates are continuous; no global
coordinate-continuity criterion is being invoked for the weak realization. -/
theorem continuous_carrierSimplex {X : Type*} [TopologicalSpace X]
    (F : Finset P) (hF : IsChain (· ≤ ·) (↑F : Set P)) (hne : F.Nonempty)
    (g : C(X, OrderWeights P)) (hg : ∀ x, (g x).weights.support ⊆ F) :
    Continuous (fun x => carrierSimplex F hF hne (g x) (hg x)) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin (F.card - 1 + 1))).continuous_iff]
  change Continuous (fun x i => (g x).weights (finiteChainOrder F hF hne i))
  exact continuous_pi fun i => (weightEval_continuous _).comp g.continuous

set_option maxHeartbeats 1500000 in
/-- Closedness can be tested on all admissible finite faces. The proof is
a genuine finite closed-face gluing argument inside every original chart. -/
theorem isClosed_image_of_finite_face_preimages (S : Finset P → Prop)
    (hS : SupportHereditary S) (T : Set (SubcomplexWeights S))
    (hT : ∀ (F : Finset P), IsChain (· ≤ ·) (↑F : Set P) → F.Nonempty →
      ∀ hF : S F, IsClosed ((subcomplexFiniteInclusion S hS F hF) ⁻¹' T)) :
    IsClosed ((Subtype.val : SubcomplexWeights S → OrderWeights P) '' T) := by
  classical
  rw [orderWeights_isClosed_iff]
  intro n simplex
  let x := nerveChain simplex
  let L := Finset.univ.image x
  let Families := L.powerset.filter (fun F => F.Nonempty ∧ S F)
  let Piece (F : Finset P) : Set (StdSimplex ℝ (Fin (n.len + 1))) :=
    if hF : S F then
      Subtype.val '' ((chainCarrierRestriction x F) ⁻¹'
        ((subcomplexFiniteInclusion S hS F hF) ⁻¹' T))
    else ∅
  have hpiece (F : Finset P) (hFF : F ∈ Families) : IsClosed (Piece F) := by
    obtain ⟨hFL, hne, hSF⟩ := Finset.mem_filter.mp hFF
    have hsub : F ⊆ L := Finset.mem_powerset.mp hFL
    have hchain : IsChain (· ≤ ·) (↑F : Set P) :=
      fun a ha b hb hne => chain_range_isChain x (hsub ha) (hsub hb) hne
    dsimp only [Piece]
    rw [dite_eq_left hSF]
    exact (isClosed_chainCarrierFace x F).isClosedMap_subtype_val _
      ((hT F hchain hne hSF).preimage (chainCarrierRestriction x F).continuous)
  have he : (fun z => orderWeightsOfChain x z) ⁻¹'
        ((Subtype.val : SubcomplexWeights S → OrderWeights P) '' T) =
      ⋃ F ∈ Families, Piece F := by
    ext z
    constructor
    · rintro ⟨w, hwT, hwz⟩
      change w.val = orderWeightsOfChain x z at hwz
      let F := (orderWeightsOfChain x z).weights.support
      have hSF : S F := by
        change S (orderWeightsOfChain x z).weights.support
        rw [← hwz]
        exact w.property
      have hFF : F ∈ Families := Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr (chainWeights_support x z),
          (orderWeightsOfChain x z).support_nonempty, hSF⟩
      apply Set.mem_iUnion.mpr
      refine ⟨F, Set.mem_iUnion.mpr ⟨hFF, ?_⟩⟩
      dsimp only [Piece]
      rw [dite_eq_left hSF]
      let zF : chainCarrierFace x F := ⟨z, Finset.Subset.refl _⟩
      refine ⟨zF, ?_, rfl⟩
      have hpoint : subcomplexFiniteInclusion S hS F hSF (chainCarrierRestriction x F zF) = w := by
        apply Subtype.ext
        exact (chainCarrierRestriction_map x F zF).trans hwz.symm
      change subcomplexFiniteInclusion S hS F hSF (chainCarrierRestriction x F zF) ∈ T
      rwa [hpoint]
    · intro hz
      obtain ⟨F, hFz⟩ := Set.mem_iUnion.mp hz
      obtain ⟨hFF, hzF⟩ := Set.mem_iUnion.mp hFz
      have hSF : S F := (Finset.mem_filter.mp hFF).2.2
      dsimp only [Piece] at hzF
      rw [dite_eq_left hSF] at hzF
      obtain ⟨zF, hzFT, hzFz⟩ := hzF
      refine ⟨subcomplexFiniteInclusion S hS F hSF (chainCarrierRestriction x F zF), hzFT, ?_⟩
      exact (chainCarrierRestriction_map x F zF).trans
        (congrArg (orderWeightsOfChain x) hzFz)
  change IsClosed ((fun z => orderWeightsOfChain x z) ⁻¹' _)
  rw [he]
  exact isClosed_biUnion_finset hpiece

/-- Admissible simplex tests imply continuity on each admissible finite
chain face, by its canonical finite enumeration and actual coordinates. -/
theorem continuous_finite_face_of_charts (S : Finset P → Prop) (hS : SupportHereditary S)
    {Y : Type*} [TopologicalSpace Y] (f : SubcomplexWeights S → Y)
    (hc : ∀ (n : ℕ) (x : Fin (n + 1) →o P) (hx : S (Finset.univ.image x)),
      Continuous (fun z => f (subcomplexChart S hS x hx z)))
    (F : Finset P) (hF : IsChain (· ≤ ·) (↑F : Set P)) (hne : F.Nonempty) (hSF : S F) :
    Continuous (fun w : OrderWeights (F : Set P) => f (subcomplexFiniteInclusion S hS F hSF w)) := by
  classical
  let x := finiteChainOrder F hF hne
  have hx : S (Finset.univ.image x) := by rw [finiteChainOrder_range]; exact hSF
  let g : C(OrderWeights (F : Set P), OrderWeights P) :=
    weightMapContinuous (weightInclusion (F : Set P))
  have hg : ∀ w, (g w).weights.support ⊆ F := weightInclusion_support_subset F
  have ht := (hc (F.card - 1) x hx).comp (continuous_carrierSimplex F hF hne g hg)
  apply ht.congr
  intro w
  apply congrArg f
  apply Subtype.ext
  exact carrierSimplex_reconstruct F hF hne (g w) (hg w)

/-- The genuine final-continuity criterion for the inherited subspace. -/
theorem continuous_subcomplex_iff (S : Finset P → Prop) (hS : SupportHereditary S)
    {Y : Type*} [TopologicalSpace Y] (f : SubcomplexWeights S → Y) :
    Continuous f ↔ ∀ (n : ℕ) (x : Fin (n + 1) →o P) (hx : S (Finset.univ.image x)),
      Continuous (fun z => f (subcomplexChart S hS x hx z)) := by
  constructor
  · intro hf n x hx
    exact hf.comp (continuous_subcomplexChart S hS x hx)
  · intro hc
    apply continuous_iff_isClosed.mpr
    intro T hT
    have hclosed : IsClosed ((Subtype.val : SubcomplexWeights S → OrderWeights P) '' (f ⁻¹' T)) :=
      isClosed_image_of_finite_face_preimages S hS (f ⁻¹' T) (by
        intro F hF hne hSF
        exact hT.preimage (continuous_finite_face_of_charts S hS f hc F hF hne hSF))
    have hpre : IsClosed ((Subtype.val : SubcomplexWeights S → OrderWeights P) ⁻¹'
        ((Subtype.val : SubcomplexWeights S → OrderWeights P) '' (f ⁻¹' T))) :=
      hclosed.preimage continuous_subtype_val
    simpa only [Set.preimage_image_eq (f ⁻¹' T) Subtype.val_injective] using hpre

/-- Locally compact parameters may be included in every actual chart test. -/
theorem continuous_subcomplex_prod_iff (S : Finset P → Prop) (hS : SupportHereditary S)
    {Z Y : Type*} [TopologicalSpace Z] [LocallyCompactSpace Z] [TopologicalSpace Y]
    (f : Z × SubcomplexWeights S → Y) :
    Continuous f ↔ ∀ (n : ℕ) (x : Fin (n + 1) →o P) (hx : S (Finset.univ.image x)),
      Continuous (fun p : Z × StdSimplex ℝ (Fin (n + 1)) =>
        f (p.1, subcomplexChart S hS x hx p.2)) := by
  constructor
  · intro hf n x hx
    exact hf.comp (continuous_fst.prodMk
      ((continuous_subcomplexChart S hS x hx).comp continuous_snd))
  · intro hc
    have ht (w : SubcomplexWeights S) : Continuous (fun z => f (z, w)) := by
      let x := weightChain w.val
      have hx : S (Finset.univ.image x) := by
        have he : Finset.univ.image x = w.val.weights.support := by
          ext p
          constructor
          · intro hp
            obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
            exact (weightEnum w.val i).property
          · intro hp
            exact Finset.mem_image.mpr ⟨(weightEnum w.val).symm ⟨p, hp⟩, Finset.mem_univ _,
              congrArg Subtype.val ((weightEnum w.val).apply_symm_apply _)⟩
        rw [he]
        exact w.property
      have h : Continuous (fun z : Z =>
          f (z, subcomplexChart S hS x hx (weightSimplex w.val))) :=
        (hc (weightDim w.val) x hx).comp (continuous_id.prodMk continuous_const)
      have he : subcomplexChart S hS x hx (weightSimplex w.val) = w :=
        Subtype.ext (orderWeightsOfChain_canonical w.val)
      simpa only [he] using h
    let F : SubcomplexWeights S → C(Z, Y) := fun w => ⟨fun z => f (z, w), ht w⟩
    have hF : Continuous F := by
      apply (continuous_subcomplex_iff S hS F).mpr
      intro n x hx
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact (hc n x hx).comp continuous_swap
    exact (ContinuousMap.continuous_uncurry_of_continuous ⟨F, hF⟩).comp continuous_swap


/-- The canonical sorted simplex of one admissible finite chain. -/
noncomputable def subcomplexCanonicalChart (S : Finset P → Prop) (hS : SupportHereditary S)
    (F : Finset P) (hF : IsChain (· ≤ ·) (↑F : Set P)) (hne : F.Nonempty) (hSF : S F)
    (z : StdSimplex ℝ (Fin (F.card - 1 + 1))) : SubcomplexWeights S :=
  subcomplexChart S hS (finiteChainOrder F hF hne)
    (by rw [finiteChainOrder_range]; exact hSF) z

theorem continuous_subcomplexCanonicalChart (S : Finset P → Prop) (hS : SupportHereditary S)
    (F : Finset P) (hF : IsChain (· ≤ ·) (↑F : Set P)) (hne : F.Nonempty) (hSF : S F) :
    Continuous (subcomplexCanonicalChart S hS F hF hne hSF) :=
  continuous_subcomplexChart S hS (finiteChainOrder F hF hne)
    (by rw [finiteChainOrder_range]; exact hSF)

theorem continuous_finite_face_of_canonical (S : Finset P → Prop) (hS : SupportHereditary S)
    {Y : Type*} [TopologicalSpace Y] (f : SubcomplexWeights S → Y)
    (F : Finset P) (hF : IsChain (· ≤ ·) (↑F : Set P)) (hne : F.Nonempty) (hSF : S F)
    (hc : Continuous (fun z => f (subcomplexCanonicalChart S hS F hF hne hSF z))) :
    Continuous (fun w : OrderWeights (F : Set P) => f (subcomplexFiniteInclusion S hS F hSF w)) := by
  let g : C(OrderWeights (F : Set P), OrderWeights P) :=
    weightMapContinuous (weightInclusion (F : Set P))
  have hg : ∀ w, (g w).weights.support ⊆ F := weightInclusion_support_subset F
  have ht := hc.comp (continuous_carrierSimplex F hF hne g hg)
  apply ht.congr
  intro w
  apply congrArg f
  apply Subtype.ext
  exact carrierSimplex_reconstruct F hF hne (g w) (hg w)

/-- Canonical finite-chain charts alone determine the actual subspace
continuity; no separate nondegenerate/degenerate chart topology is assumed. -/
theorem continuous_subcomplex_iff_canonical (S : Finset P → Prop) (hS : SupportHereditary S)
    {Y : Type*} [TopologicalSpace Y] (f : SubcomplexWeights S → Y) :
    Continuous f ↔ ∀ (F : Finset P) (hF : IsChain (· ≤ ·) (↑F : Set P))
      (hne : F.Nonempty) (hSF : S F),
      Continuous (fun z => f (subcomplexCanonicalChart S hS F hF hne hSF z)) := by
  constructor
  · intro hf F hF hne hSF
    exact hf.comp (continuous_subcomplexCanonicalChart S hS F hF hne hSF)
  · intro hc
    apply continuous_iff_isClosed.mpr
    intro T hT
    have hclosed : IsClosed ((Subtype.val : SubcomplexWeights S → OrderWeights P) '' (f ⁻¹' T)) :=
      isClosed_image_of_finite_face_preimages S hS (f ⁻¹' T) (by
        intro F hF hne hSF
        exact hT.preimage (continuous_finite_face_of_canonical S hS f F hF hne hSF
          (hc F hF hne hSF)))
    have hpre : IsClosed ((Subtype.val : SubcomplexWeights S → OrderWeights P) ⁻¹'
        ((Subtype.val : SubcomplexWeights S → OrderWeights P) '' (f ⁻¹' T))) :=
      hclosed.preimage continuous_subtype_val
    simpa only [Set.preimage_image_eq (f ⁻¹' T) Subtype.val_injective] using hpre

theorem exists_subcomplexCanonicalChart (S : Finset P → Prop) (hS : SupportHereditary S)
    (w : SubcomplexWeights S) :
    ∃ (F : Finset P) (hF : IsChain (· ≤ ·) (↑F : Set P)) (hne : F.Nonempty) (hSF : S F)
      (z : StdSimplex ℝ (Fin (F.card - 1 + 1))),
      subcomplexCanonicalChart S hS F hF hne hSF z = w := by
  let F := w.val.weights.support
  have hF : IsChain (· ≤ ·) (↑F : Set P) := fun a ha b hb _ => w.val.chain a ha b hb
  have hne : F.Nonempty := w.val.support_nonempty
  refine ⟨F, hF, hne, w.property,
    carrierSimplex F hF hne w.val (Finset.Subset.refl _), ?_⟩
  apply Subtype.ext
  exact carrierSimplex_reconstruct F hF hne w.val (Finset.Subset.refl _)

/-- Canonical-chart continuity also determines actual homotopies and other
families parametrized by a locally compact space. -/
theorem continuous_subcomplex_prod_iff_canonical (S : Finset P → Prop)
    (hS : SupportHereditary S)
    {Z Y : Type*} [TopologicalSpace Z] [LocallyCompactSpace Z] [TopologicalSpace Y]
    (f : Z × SubcomplexWeights S → Y) :
    Continuous f ↔ ∀ (F : Finset P) (hF : IsChain (· ≤ ·) (↑F : Set P))
      (hne : F.Nonempty) (hSF : S F),
      Continuous (fun p : Z × StdSimplex ℝ (Fin (F.card - 1 + 1)) =>
        f (p.1, subcomplexCanonicalChart S hS F hF hne hSF p.2)) := by
  constructor
  · intro hf F hF hne hSF
    exact hf.comp (continuous_fst.prodMk
      ((continuous_subcomplexCanonicalChart S hS F hF hne hSF).comp continuous_snd))
  · intro hc
    have ht (w : SubcomplexWeights S) : Continuous (fun z => f (z, w)) := by
      obtain ⟨F, hF, hne, hSF, c, he⟩ := exists_subcomplexCanonicalChart S hS w
      have h : Continuous (fun z : Z => f (z, subcomplexCanonicalChart S hS F hF hne hSF c)) :=
        (hc F hF hne hSF).comp (continuous_id.prodMk continuous_const)
      simpa only [he] using h
    let G : SubcomplexWeights S → C(Z, Y) := fun w => ⟨fun z => f (z, w), ht w⟩
    have hG : Continuous G := by
      apply (continuous_subcomplex_iff_canonical S hS G).mpr
      intro F hF hne hSF
      apply ContinuousMap.continuous_of_continuous_uncurry
      exact (hc F hF hne hSF).comp continuous_swap
    exact (ContinuousMap.continuous_uncurry_of_continuous ⟨G, hG⟩).comp continuous_swap

end ArtinNormalisers.Deligne5
