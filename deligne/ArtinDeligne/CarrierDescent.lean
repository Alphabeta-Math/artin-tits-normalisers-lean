import ArtinDeligne.HereditaryWeights
import ArtinDeligne.AcyclicCarrierFamilies

/-!
# Descent of actual coherent simplex maps

Point values are evaluated on the literal finite support. Face compatibility
identifies this value with evaluation on every containing admissible face.
Continuity uses the proved hereditary-subspace final topology, rather than
assuming that coordinate continuity determines the infinite realization.
No new external proof source is used: the coherent family is constructed in
`AcyclicCarrierFamilies`, and finality is proved in `HereditaryWeights`.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Deligne5

open OAI.HarmonicArtin Convexity Topology
attribute [local instance] Classical.decEq Classical.propDecidable

variable {P Y : Type*} [PartialOrder P] [TopologicalSpace Y]

/-- Actual barycentric coordinates on any finite carrier containing the support. -/
noncomputable def weightFaceCoordinates (F : Finset P) (w : OrderWeights P)
    (hw : w.weights.support ⊆ F) : StdSimplex ℝ F :=
  ⟨Finsupp.equivFunOnFinite.symm (fun p => w.weights p.val), fun p => w.nonneg p.val, by
    rw [Finsupp.sum_fintype _ _ (by intro; rfl)]
    change (∑ p : F, w.weights p.val) = 1
    rw [Finset.sum_coe_sort, ← w.total]
    symm
    exact Finset.sum_subset hw (fun p _ hp => Finsupp.notMem_support_iff.mp hp)⟩

@[simp] theorem weightFaceCoordinates_apply (F : Finset P) (w : OrderWeights P)
    (hw : w.weights.support ⊆ F) (p : F) :
    (weightFaceCoordinates F w hw).weights p = w.weights p.val := rfl

/-- The corresponding ambient geometric simplex, used only for equality of
finite coordinates; it does not replace the actual weighted topology. -/
def orderWeightsSimplex (w : OrderWeights P) : StdSimplex ℝ P :=
  ⟨w.weights, w.nonneg, w.total⟩

theorem weightFaceCoordinates_map_val (F : Finset P) (w : OrderWeights P)
    (hw : w.weights.support ⊆ F) :
    (weightFaceCoordinates F w hw).map (fun p : F => p.val) = orderWeightsSimplex w := by
  ext p
  by_cases hp : p ∈ F
  · have he : p = (⟨p, hp⟩ : F).val := rfl
    rw [he, StdSimplex.map_apply_injective Subtype.val_injective]
    rfl
  · have hn : p ∉ Set.range (fun q : F => q.val) := by
      rintro ⟨q, rfl⟩
      exact hp q.property
    change Finsupp.mapDomain (fun q : F => q.val) (weightFaceCoordinates F w hw).weights p = w.weights p
    rw [Finsupp.mapDomain_of_notMem_range _ _ hn]
    exact (Finsupp.notMem_support_iff.mp (fun h => hp (hw h))).symm

/-- These coordinates commute with literal zero-coordinate face inclusions. -/
theorem weightFaceCoordinates_natural {A B : Finset P} (hAB : A ⊆ B)
    (w : OrderWeights P) (hA : w.weights.support ⊆ A) :
    (weightFaceCoordinates A w hA).map (carrierFaceInclusion hAB) =
      weightFaceCoordinates B w (hA.trans hAB) := by
  apply StdSimplex.simplex_map_injective (fun a b h => Subtype.ext h)
    (f := fun p : B => p.val)
  rw [StdSimplex.map_map]
  change (weightFaceCoordinates A w hA).map (fun p : A => p.val) = _
  rw [weightFaceCoordinates_map_val, weightFaceCoordinates_map_val]

theorem continuous_weightFaceCoordinates {X : Type*} [TopologicalSpace X]
    (F : Finset P) (f : C(X, OrderWeights P))
    (hf : ∀ x, (f x).weights.support ⊆ F) :
    Continuous (fun x => weightFaceCoordinates F (f x) (hf x)) := by
  rw [(StdSimplex.isEmbedding_toFun_comp_weights ℝ F).continuous_iff]
  exact continuous_pi (fun p => (weightEval_continuous p.val).comp f.continuous)

theorem orderWeights_support_isChain (w : OrderWeights P) :
    IsChain (· ≤ ·) (↑w.weights.support : Set P) :=
  fun a ha b hb _ => w.chain a ha b hb

namespace CarrierFamily

variable {D : FiniteCarrierData P Y} (family : CarrierFamily D)
variable (S : Finset P → Prop) (hS : SupportHereditary S)
  (had : ∀ F : Finset P, IsChain (· ≤ ·) (↑F : Set P) → S F → D.admissible F)

/-- Evaluation uses the actual support, which is always a nonempty chain. -/
noncomputable def descendFun (w : SubcomplexWeights S) : Y :=
  family.map w.val.weights.support w.val.support_nonempty
    (had _ (orderWeights_support_isChain w.val) w.property)
    (weightFaceCoordinates _ w.val (Finset.Subset.refl _))

/-- Any admissible containing face can be used, even if its admissibility is
given independently of the domain's hereditary predicate. -/
theorem descendFun_eq_of_admissible (w : SubcomplexWeights S) (F : Finset P)
    (hne : F.Nonempty) (hDF : D.admissible F) (hw : w.val.weights.support ⊆ F) :
    family.descendFun S had w =
      family.map F hne hDF (weightFaceCoordinates F w.val hw) := by
  symm
  have h := family.compatible w.val.support_nonempty hne
    (had _ (orderWeights_support_isChain w.val) w.property) hDF hw
    (weightFaceCoordinates _ w.val (Finset.Subset.refl _))
  rwa [weightFaceCoordinates_natural] at h

/-- Evaluation on any containing admissible finite chain gives the same
point, including points on all proper faces. -/
theorem descendFun_eq (w : SubcomplexWeights S) (F : Finset P)
    (hF : IsChain (· ≤ ·) (↑F : Set P)) (hne : F.Nonempty) (hSF : S F)
    (hw : w.val.weights.support ⊆ F) :
    family.descendFun S had w =
      family.map F hne (had F hF hSF) (weightFaceCoordinates F w.val hw) := by
  symm
  have h := family.compatible w.val.support_nonempty hne
    (had _ (orderWeights_support_isChain w.val) w.property) (had F hF hSF) hw
    (weightFaceCoordinates _ w.val (Finset.Subset.refl _))
  rwa [weightFaceCoordinates_natural] at h

theorem descendFun_carried (w : SubcomplexWeights S) (F : Finset P)
    (hF : IsChain (· ≤ ·) (↑F : Set P)) (hne : F.Nonempty) (hSF : S F)
    (hw : w.val.weights.support ⊆ F) : family.descendFun S had w ∈ D.carrier F := by
  rw [family.descendFun_eq S had w F hF hne hSF hw]
  exact family.carried _ _ _ _

include hS in
/-- Global continuity follows from genuine finite-chart finality on the
literal hereditary subspace. -/
theorem continuous_descendFun : Continuous (family.descendFun S had) := by
  apply (continuous_subcomplex_iff_canonical S hS _).mpr
  intro F hF hne hSF
  let c := subcomplexCanonicalChart S hS F hF hne hSF
  let f : C(StdSimplex ℝ (Fin (F.card - 1 + 1)), OrderWeights P) :=
    ⟨fun z => (c z).val,
      continuous_subtype_val.comp (continuous_subcomplexCanonicalChart S hS F hF hne hSF)⟩
  have hf (z) : (f z).weights.support ⊆ F := by
    change (orderWeightsOfChain (finiteChainOrder F hF hne) z).weights.support ⊆ F
    exact (chainWeights_support (finiteChainOrder F hF hne) z).trans
      (by rw [finiteChainOrder_range])
  have hc := (family.map F hne (had F hF hSF)).continuous.comp
    (continuous_weightFaceCoordinates F f hf)
  apply hc.congr
  intro z
  exact (family.descendFun_eq S had (c z) F hF hne hSF (hf z)).symm

/-- The actual continuous map descended from the coherent family. -/
noncomputable def descend : C(SubcomplexWeights S, Y) :=
  ⟨family.descendFun S had, family.continuous_descendFun S hS had⟩

theorem descend_carried (w : SubcomplexWeights S) (F : Finset P)
    (hF : IsChain (· ≤ ·) (↑F : Set P)) (hne : F.Nonempty) (hSF : S F)
    (hw : w.val.weights.support ⊆ F) : family.descend S hS had w ∈ D.carrier F :=
  family.descendFun_carried S had w F hF hne hSF hw

theorem descend_carried_of_admissible (w : SubcomplexWeights S) (F : Finset P)
    (hne : F.Nonempty) (hDF : D.admissible F) (hw : w.val.weights.support ⊆ F) :
    family.descend S hS had w ∈ D.carrier F := by
  change family.descendFun S had w ∈ D.carrier F
  rw [family.descendFun_eq_of_admissible S had w F hne hDF hw]
  exact family.carried _ _ _ _

end CarrierFamily

namespace CarrierHomotopy

variable {D : FiniteCarrierData P Y} {f₀ f₁ : CarrierFamily D}
  (H : CarrierHomotopy f₀ f₁)
variable (S : Finset P → Prop) (hS : SupportHereditary S)
  (had : ∀ F : Finset P, IsChain (· ≤ ·) (↑F : Set P) → S F → D.admissible F)

/-- The actual support selects the homotopy value, at every time. -/
noncomputable def descendFun (t : unitInterval) (w : SubcomplexWeights S) : Y :=
  H.hom w.val.weights.support w.val.support_nonempty
    (had _ (orderWeights_support_isChain w.val) w.property)
    (t, weightFaceCoordinates _ w.val (Finset.Subset.refl _))

theorem descendFun_eq_of_admissible (t : unitInterval) (w : SubcomplexWeights S)
    (F : Finset P) (hne : F.Nonempty) (hDF : D.admissible F)
    (hw : w.val.weights.support ⊆ F) :
    H.descendFun S had t w = H.hom F hne hDF (t, weightFaceCoordinates F w.val hw) := by
  symm
  have h := H.compatible w.val.support_nonempty hne
    (had _ (orderWeights_support_isChain w.val) w.property) hDF hw t
    (weightFaceCoordinates _ w.val (Finset.Subset.refl _))
  rwa [weightFaceCoordinates_natural] at h

theorem descendFun_eq (t : unitInterval) (w : SubcomplexWeights S) (F : Finset P)
    (hF : IsChain (· ≤ ·) (↑F : Set P)) (hne : F.Nonempty) (hSF : S F)
    (hw : w.val.weights.support ⊆ F) :
    H.descendFun S had t w =
      H.hom F hne (had F hF hSF) (t, weightFaceCoordinates F w.val hw) := by
  symm
  have h := H.compatible w.val.support_nonempty hne
    (had _ (orderWeights_support_isChain w.val) w.property) (had F hF hSF) hw t
    (weightFaceCoordinates _ w.val (Finset.Subset.refl _))
  rwa [weightFaceCoordinates_natural] at h

include hS in
theorem continuous_descendFun :
    Continuous (fun p : unitInterval × SubcomplexWeights S => H.descendFun S had p.1 p.2) := by
  apply (continuous_subcomplex_prod_iff_canonical S hS _).mpr
  intro F hF hne hSF
  let c := subcomplexCanonicalChart S hS F hF hne hSF
  let f : C(StdSimplex ℝ (Fin (F.card - 1 + 1)), OrderWeights P) :=
    ⟨fun z => (c z).val,
      continuous_subtype_val.comp (continuous_subcomplexCanonicalChart S hS F hF hne hSF)⟩
  have hf (z) : (f z).weights.support ⊆ F := by
    change (orderWeightsOfChain (finiteChainOrder F hF hne) z).weights.support ⊆ F
    exact (chainWeights_support (finiteChainOrder F hF hne) z).trans
      (by rw [finiteChainOrder_range])
  have hc := (H.hom F hne (had F hF hSF)).continuous.comp
    (continuous_fst.prodMk ((continuous_weightFaceCoordinates F f hf).comp continuous_snd))
  apply hc.congr
  intro p
  exact (H.descendFun_eq S had p.1 (c p.2) F hF hne hSF (hf p.2)).symm

/-- Descent retains both exact endpoint maps. Product continuity follows from
the proved locally compact parameter version of hereditary chart finality. -/
noncomputable def descend :
    ContinuousMap.Homotopy (f₀.descend S hS had) (f₁.descend S hS had) where
  toFun p := H.descendFun S had p.1 p.2
  continuous_toFun := H.continuous_descendFun S hS had
  map_zero_left _w := (H.hom _ _ _).apply_zero _
  map_one_left _w := (H.hom _ _ _).apply_one _

theorem descend_carried (t : unitInterval) (w : SubcomplexWeights S) (F : Finset P)
    (hF : IsChain (· ≤ ·) (↑F : Set P)) (hne : F.Nonempty) (hSF : S F)
    (hw : w.val.weights.support ⊆ F) : H.descend S hS had (t, w) ∈ D.carrier F := by
  change H.descendFun S had t w ∈ D.carrier F
  rw [H.descendFun_eq S had t w F hF hne hSF hw]
  exact H.carried _ _ _ _ _

theorem descend_carried_of_admissible (t : unitInterval) (w : SubcomplexWeights S)
    (F : Finset P) (hne : F.Nonempty) (hDF : D.admissible F)
    (hw : w.val.weights.support ⊆ F) : H.descend S hS had (t, w) ∈ D.carrier F := by
  change H.descendFun S had t w ∈ D.carrier F
  rw [H.descendFun_eq_of_admissible S had t w F hne hDF hw]
  exact H.carried _ _ _ _ _

end CarrierHomotopy

/-- A continuous map obtained directly from contractibility and monotonicity
data, through the proved all-dimensional coherent-family construction. -/
noncomputable def FiniteCarrierData.descendedMap (D : FiniteCarrierData P Y) :
    C(SubcomplexWeights D.admissible, Y) :=
  D.family.descend D.admissible (fun {_ _} hAB hB => D.hereditary hAB hB) (fun _ _ h => h)

/-- The constructed coherent homotopy descends to a genuine global homotopy;
there is no homotopy or extension supplied as an additional hypothesis. -/
noncomputable def CarrierFamily.descendedHomotopy {D : FiniteCarrierData P Y}
    (f₀ f₁ : CarrierFamily D) (S : Finset P → Prop) (hS : SupportHereditary S)
    (had : ∀ F : Finset P, IsChain (· ≤ ·) (↑F : Set P) → S F → D.admissible F) :
    ContinuousMap.Homotopy (f₀.descend S hS had) (f₁.descend S hS had) :=
  (f₀.homotopy f₁).descend S hS had

end ArtinNormalisers.Deligne5
