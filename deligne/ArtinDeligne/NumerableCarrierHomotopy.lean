import ArtinDeligne.NumerableWeights
import ArtinDeligne.AcyclicCarrierFamilies

/-!
# Numerable carrier homotopies in the original space

Finite simplex coordinates retain the original partition coefficients. A
coherent parameterized face family is evaluated on the positive support;
continuity uses one finite closed-support window near each original point.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ArtinNormalisers.Deligne5

open OAI.HarmonicArtin Topology Convexity
open Topology.NumerableConnectorCover
open scoped unitInterval
attribute [local instance] Classical.decEq Classical.propDecidable

universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v} [LinearOrder ι]

/-- The original common-intersection parameter space of a finite face. -/
def coverFaceParameter (W : ι → Set X) (F : Finset ι) : Set X :=
  {x | ∀ i ∈ F, x ∈ W i}

omit [TopologicalSpace X] [LinearOrder ι] in
theorem coverFaceParameter_antitone (W : ι → Set X) : Antitone (coverFaceParameter W) :=
  fun _ _ h _ hx i hi ↦ hx i (h hi)

/-- Ordinary simplex weights on a finite subset of a linearly ordered index set. -/
def numerableSimplexWeights (F : Finset ι) (z : StdSimplex ℝ F) : OrderWeights F where
  weights := z.weights
  nonneg := z.nonneg
  total := z.total
  chain := fun p _ q _ ↦ le_total p q

/-- The original finite-face chart into the common-intersection weight subspace. -/
noncomputable def numerableFaceChart (W : ι → Set X) (F : Finset ι)
    (hF : IsNerveFace W F) (z : StdSimplex ℝ F) : CoverWeights W :=
  ⟨weightMap (weightInclusion (F : Set ι)) (numerableSimplexWeights F z), by
    apply hF.mono
    rw [weightMap_support_embedding _ Subtype.val_injective]
    intro i hi
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    exact j.property⟩

omit [TopologicalSpace X] in
theorem numerableFaceChart_support_subset (W : ι → Set X) (F : Finset ι)
    (hF : IsNerveFace W F) (z : StdSimplex ℝ F) :
    (numerableFaceChart W F hF z).val.weights.support ⊆ F := by
  rw [numerableFaceChart, weightMap_support_embedding _ Subtype.val_injective]
  intro i hi
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
  exact j.property

omit [TopologicalSpace X] in
theorem numerableFaceChart_apply_mem (W : ι → Set X) (F : Finset ι)
    (hF : IsNerveFace W F) (z : StdSimplex ℝ F) (i : F) :
    (numerableFaceChart W F hF z).val.weights i.val = z.weights i :=
  weightMap_apply_embedding (weightInclusion (F : Set ι)) Subtype.val_injective _ i

omit [TopologicalSpace X] in
theorem numerableFaceChart_apply_not_mem (W : ι → Set X) (F : Finset ι)
    (hF : IsNerveFace W F) (z : StdSimplex ℝ F) {i : ι} (hi : i ∉ F) :
    (numerableFaceChart W F hF z).val.weights i = 0 :=
  Finsupp.notMem_support_iff.mp fun h ↦ hi (numerableFaceChart_support_subset W F hF z h)

omit [TopologicalSpace X] in
theorem continuous_numerableFaceChart (W : ι → Set X) (F : Finset ι)
    (hne : F.Nonempty) (hF : IsNerveFace W F) : Continuous (numerableFaceChart W F hF) := by
  apply Continuous.subtype_mk
  apply continuous_of_finite_chain_carrier _ F
    (fun a _ b _ _ ↦ le_total a b) hne
    (numerableFaceChart_support_subset W F hF)
  intro i
  by_cases hi : i ∈ F
  · simpa only [numerableFaceChart_apply_mem W F hF _ ⟨i, hi⟩] using
      (StdSimplex.continuous_weights_apply ℝ (⟨i, hi⟩ : F))
  · simpa only [numerableFaceChart_apply_not_mem W F hF _ hi] using
      (continuous_const : Continuous fun _ : StdSimplex ℝ F ↦ (0 : ℝ))

/-- The chart retains every original partition coefficient, also when its
finite support window is larger than the positive support. -/
theorem numerableFaceChart_finiteChart (W : ι → Set X) (ρ : PartitionOfUnity ι X)
    (hρ : ρ.IsSubordinate W) (F : Finset ι) (hF : IsNerveFace W F)
    (x : chartDomain ρ F) :
    numerableFaceChart W F hF (finiteChart ρ F x) = numerableCoverClassifier W ρ hρ x.val := by
  classical
  apply Subtype.ext
  apply OrderWeights.ext
  ext i
  change (numerableFaceChart W F hF (finiteChart ρ F x)).val.weights i =
    (partitionWeightsValue ρ x.val).weights i
  rw [partitionWeightsValue_apply]
  by_cases hi : i ∈ F
  · exact numerableFaceChart_apply_mem W F hF _ ⟨i, hi⟩
  · rw [numerableFaceChart_apply_not_mem W F hF _ hi]
    symm
    by_contra hn
    exact hi (x.property ((ρ.mem_finsupport x.val).mpr hn))

/-- The genuine zero-coordinate insertion between arbitrary finite faces. -/
def numerableFaceInclusion {A B : Finset ι} (h : A ⊆ B) : A → B :=
  fun a ↦ ⟨a.val, h a.property⟩

omit [TopologicalSpace X] in
theorem numerableFaceChart_map (W : ι → Set X) {A B : Finset ι}
    (hAB : A ⊆ B) (hA : IsNerveFace W A) (hB : IsNerveFace W B)
    (z : StdSimplex ℝ A) :
    numerableFaceChart W B hB (z.map (numerableFaceInclusion hAB)) =
      numerableFaceChart W A hA z := by
  apply Subtype.ext
  apply OrderWeights.ext
  change (z.map (numerableFaceInclusion hAB)).weights.mapDomain (Subtype.val : B → ι) =
    z.weights.mapDomain (Subtype.val : A → ι)
  rw [StdSimplex.weights_map, ← Finsupp.mapDomain_comp]
  rfl

/-- Larger faces have smaller common-intersection parameter spaces. -/
def coverFaceRestrict (W : ι → Set X) {A B : Finset ι} (h : A ⊆ B) :
    coverFaceParameter W B → coverFaceParameter W A :=
  fun x ↦ ⟨x.val, coverFaceParameter_antitone W h x.property⟩

omit [LinearOrder ι] in
theorem isOpen_coverFaceParameter (W : ι → Set X) (hW : ∀ i, IsOpen (W i))
    (F : Finset ι) : IsOpen (coverFaceParameter W F) := by
  have he : coverFaceParameter W F = ⋂ i ∈ F, W i := by
    ext x
    simp only [coverFaceParameter, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [he]
  exact isOpen_biInter_finset fun i _ ↦ hW i

omit [LinearOrder ι] in
/-- The actual point lies in every cover member of its positive support. -/
theorem partition_mem_coverFaceParameter (W : ι → Set X) (ρ : PartitionOfUnity ι X)
    (hρ : ρ.IsSubordinate W) (x : X) : x ∈ coverFaceParameter W (ρ.finsupport x) := by
  intro i hi
  exact hρ i ((ρ.mem_fintsupport_iff x i).mp ((ρ.finsupport_subset_fintsupport x) hi))

/-- Continuous finite-face tracks are intermediate gluing data. In the carrier
theorem they will be constructed by parameterized face induction. -/
abbrev NumerableFaceTracks (W : ι → Set X) :=
  ∀ (F : Finset ι), F.Nonempty → IsNerveFace W F →
    C(I × (coverFaceParameter W F × StdSimplex ℝ F), X)

def NumerableFaceTracks.Compatible (W : ι → Set X) (H : NumerableFaceTracks W) : Prop :=
  ∀ {A B : Finset ι} (hneA : A.Nonempty) (hneB : B.Nonempty)
    (hA : IsNerveFace W A) (hB : IsNerveFace W B) (hAB : A ⊆ B)
    (t : I) (x : coverFaceParameter W B) (z : StdSimplex ℝ A),
    H B hneB hB (t, (x, z.map (numerableFaceInclusion hAB))) =
      H A hneA hA (t, (coverFaceRestrict W hAB x, z))

/-- Evaluate on precisely the original positive partition support. -/
noncomputable def partitionTrackValue (W : ι → Set X) (ρ : PartitionOfUnity ι X)
    (hρ : ρ.IsSubordinate W) (H : NumerableFaceTracks W) (p : I × X) : X :=
  H (ρ.finsupport p.2) (partition_finsupport_nonempty ρ p.2)
    (partition_support_isNerveFace W ρ hρ p.2)
    (p.1, (⟨p.2, partition_mem_coverFaceParameter W ρ hρ p.2⟩,
      finiteChart ρ (ρ.finsupport p.2) ⟨p.2, Finset.Subset.refl _⟩))

/-- Exact face coherence permits any larger finite support window at the
same actual point, including the closed-support window. -/
theorem partitionTrackValue_eq_finite (W : ι → Set X) (ρ : PartitionOfUnity ι X)
    (hρ : ρ.IsSubordinate W) (H : NumerableFaceTracks W)
    (hH : NumerableFaceTracks.Compatible W H) (F : Finset ι) (hne : F.Nonempty)
    (hF : IsNerveFace W F) (t : I) (x : coverFaceParameter W F)
    (hx : ρ.finsupport x.val ⊆ F) :
    partitionTrackValue W ρ hρ H (t, x.val) =
      H F hne hF (t, (x, finiteChart ρ F ⟨x.val, hx⟩)) := by
  have h := hH (partition_finsupport_nonempty ρ x.val) hne
    (partition_support_isNerveFace W ρ hρ x.val) hF hx t x
    (finiteChart ρ (ρ.finsupport x.val) ⟨x.val, Finset.Subset.refl _⟩)
  change H F hne hF
    (t, (x, (finiteChart ρ (ρ.finsupport x.val) ⟨x.val, Finset.Subset.refl _⟩).map
      (finiteFaceInclusion hx))) = _ at h
  rw [finiteChart_map_inclusion] at h
  exact h.symm

/-- Local continuity comes from one finite closed-support chart and its
actual common-intersection parameter space. -/
theorem continuous_partitionTrackValue (W : ι → Set X) (hW : ∀ i, IsOpen (W i))
    (ρ : PartitionOfUnity ι X) (hρ : ρ.IsSubordinate W) (H : NumerableFaceTracks W)
    (hH : NumerableFaceTracks.Compatible W H) : Continuous (partitionTrackValue W ρ hρ H) := by
  classical
  rw [continuous_iff_continuousAt]
  intro p₀
  let F := ρ.fintsupport p₀.2
  have hne : F.Nonempty :=
    (partition_finsupport_nonempty ρ p₀.2).mono (ρ.finsupport_subset_fintsupport p₀.2)
  have hpF : p₀.2 ∈ coverFaceParameter W F := by
    intro i hi
    exact hρ i ((ρ.mem_fintsupport_iff p₀.2 i).mp hi)
  have hF : IsNerveFace W F := ⟨p₀.2, hpF⟩
  let V : Set X := coverFaceParameter W F ∩ chartDomain ρ F
  have hV : V ∈ 𝓝 p₀.2 :=
    Filter.inter_mem ((isOpen_coverFaceParameter W hW F).mem_nhds hpF)
      (chartDomain_mem_nhds ρ p₀.2)
  let U : Set (I × X) := Prod.snd ⁻¹' V
  have hU : U ∈ 𝓝 p₀ := continuous_snd.continuousAt.preimage_mem_nhds hV
  let g : U → I × (coverFaceParameter W F × StdSimplex ℝ F) := fun q ↦
    (q.val.1, (⟨q.val.2, q.property.1⟩,
      finiteChart ρ F ⟨q.val.2, q.property.2⟩))
  have hg : Continuous g := by
    refine (continuous_fst.comp continuous_subtype_val).prodMk ?_
    refine ((continuous_snd.comp continuous_subtype_val).subtype_mk _).prodMk ?_
    exact (finiteChart ρ F).continuous.comp
      ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  have hc : Continuous (U.domRestrict (partitionTrackValue W ρ hρ H)) := by
    apply ((H F hne hF).continuous.comp hg).congr
    intro q
    exact (partitionTrackValue_eq_finite W ρ hρ H hH F hne hF q.val.1
      ⟨q.val.2, q.property.1⟩ q.property.2).symm
  exact (continuousOn_iff_continuous_domRestrict.mpr hc).continuousAt hU

/-- Gluing already constructed coherent local tracks gives the genuine
global homotopy. The carrier theorem below constructs those tracks. -/
noncomputable def numerableFaceTracksHomotopy (W : ι → Set X)
    (hW : ∀ i, IsOpen (W i)) (ρ : PartitionOfUnity ι X) (hρ : ρ.IsSubordinate W)
    (r : C(CoverWeights W, X)) (H : NumerableFaceTracks W)
    (hH : NumerableFaceTracks.Compatible W H)
    (h₀ : ∀ F hne hF (x : coverFaceParameter W F) (z : StdSimplex ℝ F),
      H F hne hF (0, (x, z)) = r (numerableFaceChart W F hF z))
    (h₁ : ∀ F hne hF (x : coverFaceParameter W F) (z : StdSimplex ℝ F),
      H F hne hF (1, (x, z)) = x.val) :
    ContinuousMap.Homotopy (r.comp (numerableCoverClassifier W ρ hρ)) (ContinuousMap.id X) where
  toFun := partitionTrackValue W ρ hρ H
  continuous_toFun := continuous_partitionTrackValue W hW ρ hρ H hH
  map_zero_left x := by
    dsimp only [partitionTrackValue]
    rw [h₀]
    exact congrArg r (numerableFaceChart_finiteChart W ρ hρ (ρ.finsupport x)
      (partition_support_isNerveFace W ρ hρ x) ⟨x, Finset.Subset.refl _⟩)
  map_one_left x := by
    dsimp only [partitionTrackValue]
    exact h₁ _ _ _ _ _

/-- Monotone contractible carriers construct the actual numerable comparison
homotopy. The local face homotopies are produced by parameterized HEP and are
not input data. The original common-intersection spaces need not be contractible. -/
noncomputable def numerableCarrierHomotopy (W : ι → Set X)
    (hW : ∀ i, IsOpen (W i)) (ρ : PartitionOfUnity ι X) (hρ : ρ.IsSubordinate W)
    (C : Finset ι → Set X)
    (hC : ∀ F, F.Nonempty → IsNerveFace W F → ContractibleSpace (C F))
    (hmono : ∀ {A B}, A ⊆ B → A.Nonempty → IsNerveFace W B → C A ⊆ C B)
    (hinter : ∀ F, F.Nonempty → IsNerveFace W F → coverFaceParameter W F ⊆ C F)
    (r : C(CoverWeights W, X))
    (hr : ∀ F, F.Nonempty → IsNerveFace W F → ∀ w : CoverWeights W,
      w.val.weights.support ⊆ F → r w ∈ C F) :
    ContinuousMap.Homotopy (r.comp (numerableCoverClassifier W ρ hρ)) (ContinuousMap.id X) := by
  let D : FiniteCarrierData ι X :=
    { admissible := IsNerveFace W
      hereditary := fun h hF ↦ hF.mono h
      carrier := C
      contractible := hC
      monotone := hmono }
  let R := coverFaceParameter W
  let hR : Antitone R := coverFaceParameter_antitone W
  let f₀ : ParameterizedCarrierFamily D R hR :=
    { map := fun F hne hF ↦
        ⟨fun p ↦ r (numerableFaceChart W F hF p.2),
          r.continuous.comp ((continuous_numerableFaceChart W F hne hF).comp continuous_snd)⟩
      carried := fun F hne hF _x z ↦
        hr F hne hF _ (numerableFaceChart_support_subset W F hF z)
      compatible := fun _ _ ha hb hAB _ z ↦
        congrArg r (numerableFaceChart_map W hAB ha hb z) }
  let f₁ : ParameterizedCarrierFamily D R hR :=
    { map := fun _ _ _ ↦ ⟨fun p ↦ p.1.val, continuous_subtype_val.comp continuous_fst⟩
      carried := fun F hne hF x _ ↦ hinter F hne hF x.property
      compatible := fun _ _ _ _ _ _ _ ↦ rfl }
  let H := f₀.homotopy f₁
  refine numerableFaceTracksHomotopy W hW ρ hρ r
    (fun F hne hF ↦ (H.hom F hne hF).toContinuousMap) ?_ ?_ ?_
  · intro A B hA hB ha hb hAB t x z
    exact H.compatible hA hB ha hb hAB t x z
  · intro F hne hF x z
    exact (H.hom F hne hF).apply_zero (x, z)
  · intro F hne hF x z
    exact (H.hom F hne hF).apply_one (x, z)

end ArtinNormalisers.Deligne5
