import ArtinDeligne.HereditaryWeights
import ArtinDeligne.GarsideFolds
import ArtinDeligne.IncomingJoins

/-!
# The actual weak topology and interval carriers of Garside weights

The simple-chain condition is hereditary, so the already defined Garside
space has the proved admissible-chart finality and product finality of its
actual subspace topology. A simple interval carrier is an actual subspace
of this space. It is homeomorphic to the genuine order realization of that
interval, which has a top vertex and therefore contracts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ArtinNormalisers.Deligne5

open Ribbon2 Homotopy5 Chamber3 OAI.HarmonicArtin Topology Convexity
attribute [local instance] Classical.decEq Classical.propDecidable

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (B0 : RibbonObject M)

/-- The actual finite simple-chain predicate, with no topological fields. -/
def garsideSupportPredicate (F : Finset (IncomingVertex M B0)) : Prop :=
  ∀ u ∈ F, ∀ v ∈ F, u ≤ v → SimpleRibbon M u.source v.source (u.difference v)

theorem garsideSupportPredicate_hereditary : SupportHereditary (garsideSupportPredicate M B0) := by
  intro A B hAB hB u hu v hv huv
  exact hB u (hAB hu) v (hAB hv) huv

/-- This is an equality of the existing predicates and inherited spaces. -/
theorem garsideWeights_eq_subcomplex :
    GarsideWeights M B0 = SubcomplexWeights (garsideSupportPredicate M B0) := rfl

theorem isClosed_garsideWeightsSet : IsClosed (garsideWeightsSet M B0) :=
  isClosed_subcomplexWeights (garsideSupportPredicate M B0) (garsideSupportPredicate_hereditary M B0)

noncomputable def garsideChart {n : ℕ} (x : Fin (n + 1) →o IncomingVertex M B0)
    (hx : garsideSupportPredicate M B0 (Finset.univ.image x))
    (z : StdSimplex ℝ (Fin (n + 1))) : GarsideWeights M B0 :=
  subcomplexChart (garsideSupportPredicate M B0) (garsideSupportPredicate_hereditary M B0) x hx z

theorem continuous_garside_iff {Y : Type*} [TopologicalSpace Y] (f : GarsideWeights M B0 → Y) :
    Continuous f ↔ ∀ (n : ℕ) (x : Fin (n + 1) →o IncomingVertex M B0)
      (hx : garsideSupportPredicate M B0 (Finset.univ.image x)),
      Continuous (fun z => f (garsideChart M B0 x hx z)) :=
  continuous_subcomplex_iff (garsideSupportPredicate M B0) (garsideSupportPredicate_hereditary M B0) f

noncomputable def garsideCanonicalChart (F : Finset (IncomingVertex M B0))
    (hF : IsChain (· ≤ ·) (↑F : Set (IncomingVertex M B0))) (hne : F.Nonempty)
    (hSF : garsideSupportPredicate M B0 F) (z : StdSimplex ℝ (Fin (F.card - 1 + 1))) :
    GarsideWeights M B0 :=
  subcomplexCanonicalChart (garsideSupportPredicate M B0)
    (garsideSupportPredicate_hereditary M B0) F hF hne hSF z

theorem continuous_garside_iff_canonical {Y : Type*} [TopologicalSpace Y]
    (f : GarsideWeights M B0 → Y) :
    Continuous f ↔ ∀ (F : Finset (IncomingVertex M B0))
      (hF : IsChain (· ≤ ·) (↑F : Set (IncomingVertex M B0))) (hne : F.Nonempty)
      (hSF : garsideSupportPredicate M B0 F),
      Continuous (fun z => f (garsideCanonicalChart M B0 F hF hne hSF z)) :=
  continuous_subcomplex_iff_canonical (garsideSupportPredicate M B0)
    (garsideSupportPredicate_hereditary M B0) f

theorem continuous_garside_prod_iff_canonical
    {Z Y : Type*} [TopologicalSpace Z] [LocallyCompactSpace Z] [TopologicalSpace Y]
    (f : Z × GarsideWeights M B0 → Y) :
    Continuous f ↔ ∀ (F : Finset (IncomingVertex M B0))
      (hF : IsChain (· ≤ ·) (↑F : Set (IncomingVertex M B0))) (hne : F.Nonempty)
      (hSF : garsideSupportPredicate M B0 F),
      Continuous (fun p : Z × StdSimplex ℝ (Fin (F.card - 1 + 1)) =>
        f (p.1, garsideCanonicalChart M B0 F hF hne hSF p.2)) :=
  continuous_subcomplex_prod_iff_canonical (garsideSupportPredicate M B0)
    (garsideSupportPredicate_hereditary M B0) f

/-- Simple intervals have finitely many actual vertices: their projections
are injective because each actual difference is its canonical simple lift. -/
theorem finite_simple_interval {a b : IncomingVertex M B0}
    (hs : SimpleRibbon M a.source b.source (a.difference b)) : Finite (Set.Icc a b) := by
  let f : Set.Icc a b → M.Group := fun u => Artin.projection M (a.difference u.val)
  apply Finite.of_injective f
  intro u v huv
  have hu := IncomingVertex.simple_difference_of_interval hs le_rfl u.property.1 u.property.2
  have hv := IncomingVertex.simple_difference_of_interval hs le_rfl v.property.1 v.property.2
  have hd : a.difference u.val = a.difference v.val :=
    (SimpleRibbon.eq_simpleLift M hu).trans
      ((congrArg (transporterPositiveLift M) huv).trans (SimpleRibbon.eq_simpleLift M hv).symm)
  apply Subtype.ext
  apply IncomingVertex.ext_value
  exact inv_injective (mul_left_cancel hd)

/-- Every weighted chain of a simple interval already satisfies the actual
simple-chain condition. The homeomorphism uses its genuine subspace topology. -/
noncomputable def simpleIntervalWeightsHomeomorph {a b : IncomingVertex M B0}
    (hs : SimpleRibbon M a.source b.source (a.difference b)) :
    OrderWeights (Set.Icc a b) ≃ₜ GarsideWeightsOn M B0 (Set.Icc a b) where
  toFun w := ⟨w, fun u _hu v _hv huv =>
    IncomingVertex.simple_difference_of_interval hs u.property.1 huv v.property.2⟩
  invFun w := w.val
  left_inv _w := rfl
  right_inv _w := rfl
  continuous_toFun := continuous_id.subtype_mk _
  continuous_invFun := continuous_subtype_val

theorem contractibleSpace_simpleIntervalWeights {a b : IncomingVertex M B0}
    (hs : SimpleRibbon M a.source b.source (a.difference b)) :
    ContractibleSpace (GarsideWeightsOn M B0 (Set.Icc a b)) := by
  let topVertex : Set.Icc a b := ⟨b, hs.1, le_rfl⟩
  let : OrderTop (Set.Icc a b) := { top := topVertex, le_top := fun u => u.property.2 }
  have hOrd : ContractibleSpace (OrderWeights (Set.Icc a b)) :=
    nerveWeightsHomeomorph.contractibleSpace_iff.mp (nerve_orderTop_contractible (Set.Icc a b))
  exact (simpleIntervalWeightsHomeomorph M B0 hs).contractibleSpace_iff.mp hOrd

/-- The literal global subspace carried by one actual order interval. -/
def garsideIntervalCarrier (a b : IncomingVertex M B0) : Set (GarsideWeights M B0) :=
  {w | ∀ u ∈ w.val.weights.support, u ∈ Set.Icc a b}

theorem garsideIntervalCarrier_mono {a b c d : IncomingVertex M B0}
    (hca : c ≤ a) (hbd : b ≤ d) :
    garsideIntervalCarrier M B0 a b ⊆ garsideIntervalCarrier M B0 c d := by
  intro w hw u hu
  obtain ⟨hau, hub⟩ := hw u hu
  exact ⟨hca.trans hau, hub.trans hbd⟩

theorem isClosed_garsideIntervalCarrier (a b : IncomingVertex M B0) :
    IsClosed (garsideIntervalCarrier M B0 a b) := by
  have he : garsideIntervalCarrier M B0 a b =
      ⋂ u, ⋂ (_ : u ∉ Set.Icc a b), {w | w.val.weights u = 0} := by
    ext w
    simp only [garsideIntervalCarrier, Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro hw u hu
      exact Finsupp.notMem_support_iff.mp (fun h => hu (hw u h))
    · intro hw u hu
      by_contra hn
      exact (Finsupp.mem_support_iff.mp hu) (hw u hn)
  rw [he]
  exact isClosed_iInter fun u => isClosed_iInter fun _ =>
    isClosed_eq ((weightEval_continuous u).comp continuous_subtype_val) continuous_const

theorem range_garsideIntervalInclusion (a b : IncomingVertex M B0) :
    Set.range (GarsideWeightsOn.include M B0 (Set.Icc a b)) = garsideIntervalCarrier M B0 a b := by
  ext w
  constructor
  · rintro ⟨u, rfl⟩
    intro v hv
    change v ∈ (weightMap (weightInclusion (Set.Icc a b)) u.val).weights.support at hv
    rw [weightMap_support_embedding _ Subtype.val_injective] at hv
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    exact i.property
  · intro hw
    exact ⟨GarsideWeights.restrict M B0 (Set.Icc a b) w hw,
      GarsideWeights.include_restrict M B0 (Set.Icc a b) w hw⟩

theorem isClosedEmbedding_simpleIntervalInclusion {a b : IncomingVertex M B0}
    (hs : SimpleRibbon M a.source b.source (a.difference b)) :
    IsClosedEmbedding (GarsideWeightsOn.include M B0 (Set.Icc a b)) := by
  let : Finite (Set.Icc a b) := finite_simple_interval M B0 hs
  let : CompactSpace (GarsideWeightsOn M B0 (Set.Icc a b)) :=
    (simpleIntervalWeightsHomeomorph M B0 hs).compactSpace
  apply (GarsideWeightsOn.continuous_include M B0 (Set.Icc a b)).isClosedEmbedding
  intro u v huv
  apply Subtype.ext
  have h : weightMap (weightInclusion (Set.Icc a b)) u.val =
      weightMap (weightInclusion (Set.Icc a b)) v.val := congrArg Subtype.val huv
  exact weightMap_injective _ Subtype.val_injective h

/-- The actual finite interval inclusion is a closed embedding onto the
literal support-constrained carrier in the original Garside space. -/
noncomputable def simpleIntervalCarrierHomeomorph {a b : IncomingVertex M B0}
    (hs : SimpleRibbon M a.source b.source (a.difference b)) :
    GarsideWeightsOn M B0 (Set.Icc a b) ≃ₜ garsideIntervalCarrier M B0 a b :=
  (isClosedEmbedding_simpleIntervalInclusion M B0 hs).isEmbedding.toHomeomorph.trans
    (Homeomorph.setCongr (range_garsideIntervalInclusion M B0 a b))

theorem contractibleSpace_garsideIntervalCarrier {a b : IncomingVertex M B0}
    (hs : SimpleRibbon M a.source b.source (a.difference b)) :
    ContractibleSpace (garsideIntervalCarrier M B0 a b) :=
  (simpleIntervalCarrierHomeomorph M B0 hs).contractibleSpace_iff.mp
    (contractibleSpace_simpleIntervalWeights M B0 hs)


theorem continuous_garsideChart {n : ℕ} (x : Fin (n + 1) →o IncomingVertex M B0)
    (hx : garsideSupportPredicate M B0 (Finset.univ.image x)) :
    Continuous (garsideChart M B0 x hx) :=
  continuous_subcomplexChart (garsideSupportPredicate M B0)
    (garsideSupportPredicate_hereditary M B0) x hx

theorem continuous_garsideCanonicalChart (F : Finset (IncomingVertex M B0))
    (hF : IsChain (· ≤ ·) (↑F : Set (IncomingVertex M B0))) (hne : F.Nonempty)
    (hSF : garsideSupportPredicate M B0 F) :
    Continuous (garsideCanonicalChart M B0 F hF hne hSF) :=
  continuous_subcomplexCanonicalChart (garsideSupportPredicate M B0)
    (garsideSupportPredicate_hereditary M B0) F hF hne hSF

theorem continuous_garside_prod_iff
    {Z Y : Type*} [TopologicalSpace Z] [LocallyCompactSpace Z] [TopologicalSpace Y]
    (f : Z × GarsideWeights M B0 → Y) :
    Continuous f ↔ ∀ (n : ℕ) (x : Fin (n + 1) →o IncomingVertex M B0)
      (hx : garsideSupportPredicate M B0 (Finset.univ.image x)),
      Continuous (fun p : Z × StdSimplex ℝ (Fin (n + 1)) =>
        f (p.1, garsideChart M B0 x hx p.2)) :=
  continuous_subcomplex_prod_iff (garsideSupportPredicate M B0)
    (garsideSupportPredicate_hereditary M B0) f

theorem isClosedEmbedding_garsideWeights_val :
    IsClosedEmbedding (Subtype.val : GarsideWeights M B0 → OrderWeights (IncomingVertex M B0)) :=
  (isClosed_garsideWeightsSet M B0).isClosedEmbedding_subtypeVal

/-- The actual open star of a finite vertex set. -/
def garsideOpenStar (F : Finset (IncomingVertex M B0)) : Set (GarsideWeights M B0) :=
  {w | F ⊆ w.val.weights.support}

theorem isOpen_garsideOpenStar (F : Finset (IncomingVertex M B0)) :
    IsOpen (garsideOpenStar M B0 F) := by
  have he : garsideOpenStar M B0 F = ⋂ u ∈ F, {w | 0 < w.val.weights u} := by
    ext w
    simp only [garsideOpenStar, Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h u hu
      exact lt_of_le_of_ne (w.val.nonneg u) (Ne.symm (Finsupp.mem_support_iff.mp (h hu)))
    · intro h u hu
      exact Finsupp.mem_support_iff.mpr (ne_of_gt (h u hu))
  rw [he]
  exact isOpen_biInter_finset fun u _ =>
    isOpen_lt continuous_const ((weightEval_continuous u).comp continuous_subtype_val)


/-- Every nonempty admissible finite chain has actual simple interval bounds
chosen from the chain itself. No total order on all incoming vertices is used. -/
theorem exists_simple_interval_of_garsideSupport
    (F : Finset (IncomingVertex M B0))
    (hF : IsChain (· ≤ ·) (↑F : Set (IncomingVertex M B0))) (hne : F.Nonempty)
    (hSF : garsideSupportPredicate M B0 F) :
    ∃ a ∈ F, ∃ b ∈ F,
      (∀ u ∈ F, a ≤ u ∧ u ≤ b) ∧ SimpleRibbon M a.source b.source (a.difference b) := by
  let x := finiteChainOrder F hF hne
  let a := x 0
  let b := x (Fin.last (F.card - 1))
  have ha : a ∈ F := (finiteChainEnum F hF hne 0).property
  have hb : b ∈ F := (finiteChainEnum F hF hne (Fin.last (F.card - 1))).property
  have hbounds : ∀ u ∈ F, a ≤ u ∧ u ≤ b := by
    intro u hu
    let i := (finiteChainEnum F hF hne).symm ⟨u, hu⟩
    have hi : x i = u :=
      congrArg Subtype.val ((finiteChainEnum F hF hne).apply_symm_apply ⟨u, hu⟩)
    rw [← hi]
    exact ⟨x.monotone (Fin.zero_le i), x.monotone (Fin.le_last i)⟩
  exact ⟨a, ha, b, hb, hbounds, hSF a ha b hb (hbounds b hb).1⟩

/-- Conversely any finite packet inside an actual simple interval has the
hereditary simple-chain pair condition, including packets not totally ordered. -/
theorem garsideSupport_of_simple_interval
    (F : Finset (IncomingVertex M B0)) (a b : IncomingVertex M B0)
    (hs : SimpleRibbon M a.source b.source (a.difference b))
    (hF : ∀ u ∈ F, a ≤ u ∧ u ≤ b) : garsideSupportPredicate M B0 F := by
  intro u hu v hv huv
  exact IncomingVertex.simple_difference_of_interval hs (hF u hu).1 huv (hF v hv).2

end ArtinNormalisers.Deligne5
