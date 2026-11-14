import ArtinDeligneVendor.Topology.ArtinGroups.Realizations.FiniteWeightsCompact
import ArtinHomotopyVendor.Topology.Realization.POUNerveClassifier

/-!
# Original partition coefficients as genuine weak finite weights

Local finite closed support, rather than coordinatewise continuity alone,
proves continuity into the weak order-weight topology. The common-intersection
condition is proved from subordination. No comparison or asphericity is part
of the hypotheses or conclusion of this construction.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Deligne5

open OAI.HarmonicArtin Topology.NumerableConnectorCover Convexity
open scoped Topology

universe u v

variable {X : Type u} [TopologicalSpace X] {ι : Type v} [LinearOrder ι]

noncomputable def partitionChain (F : Finset ι) (hF : F.Nonempty) :
    Fin (finiteFaceDim F + 1) →o ι :=
  (F.orderEmbOfFin (finiteFace_card F hF)).toOrderHom

/-- The original finite partition chart, mapped into the genuine weight space. -/
noncomputable def finitePartitionWeights (ρ : PartitionOfUnity ι X)
    (F : Finset ι) (hF : F.Nonempty) (x : chartDomain ρ F) : OrderWeights ι :=
  orderWeightsOfChain (partitionChain F hF)
    ((finiteChart ρ F x).map (F.orderIsoOfFin (finiteFace_card F hF)).symm)

theorem finitePartitionWeights_apply (ρ : PartitionOfUnity ι X)
    (F : Finset ι) (hF : F.Nonempty) (x : chartDomain ρ F) (i : ι) :
    (finitePartitionWeights ρ F hF x).weights i = ρ i x.val := by
  classical
  change chainWeights (partitionChain F hF)
    ((finiteChart ρ F x).map (F.orderIsoOfFin (finiteFace_card F hF)).symm) i = _
  rw [chainWeights_apply]
  by_cases hi : i ∈ F
  · let e := F.orderIsoOfFin (finiteFace_card F hF)
    let j : F := ⟨i, hi⟩
    let k := e.symm j
    have hk : partitionChain F hF k = i :=
      congrArg Subtype.val (e.apply_symm_apply j)
    rw [Finset.sum_eq_single k]
    · rw [ite_eq_left hk, StdSimplex.weights_map]
      change Finsupp.mapDomain e.symm (finiteChart ρ F x).weights (e.symm j) = _
      rw [Finsupp.mapDomain_apply_of_injective e.symm.injective]
      rfl
    · intro l _ hl
      have hli : partitionChain F hF l ≠ i := by
        intro he
        apply hl
        exact (F.orderEmbOfFin (finiteFace_card F hF)).injective (he.trans hk.symm)
      exact ite_eq_right hli
    · intro hn
      exact False.elim (hn (Finset.mem_univ k))
  · have hρ : ρ i x.val = 0 := by
      by_contra hn
      exact hi (x.property ((ρ.mem_finsupport x.val).mpr hn))
    rw [hρ]
    apply Finset.sum_eq_zero
    intro k _
    have hk : partitionChain F hF k ≠ i := by
      intro he
      apply hi
      exact he ▸ F.orderEmbOfFin_mem (finiteFace_card F hF) k
    exact ite_eq_right hk

theorem continuous_finitePartitionWeights (ρ : PartitionOfUnity ι X)
    (F : Finset ι) (hF : F.Nonempty) : Continuous (finitePartitionWeights ρ F hF) :=
  (chainWeightsChart_continuous (partitionChain F hF)).comp
    ((StdSimplex.continuous_map ℝ (F.orderIsoOfFin (finiteFace_card F hF)).symm).comp
      (finiteChart ρ F).continuous)

/-- Pointwise weights use precisely the original positive partition support. -/
noncomputable def partitionWeightsValue (ρ : PartitionOfUnity ι X) (x : X) :
    OrderWeights ι :=
  finitePartitionWeights ρ (ρ.finsupport x) (partition_finsupport_nonempty ρ x)
    ⟨x, Finset.Subset.refl _⟩

@[simp] theorem partitionWeightsValue_apply (ρ : PartitionOfUnity ι X) (x : X) (i : ι) :
    (partitionWeightsValue ρ x).weights i = ρ i x :=
  finitePartitionWeights_apply ρ _ _ _ i

theorem partitionWeightsValue_eq_finite (ρ : PartitionOfUnity ι X)
    (F : Finset ι) (hF : F.Nonempty) (x : chartDomain ρ F) :
    partitionWeightsValue ρ x.val = finitePartitionWeights ρ F hF x := by
  apply OrderWeights.ext
  ext i
  rw [partitionWeightsValue_apply, finitePartitionWeights_apply]

theorem continuousOn_partitionWeightsValue (ρ : PartitionOfUnity ι X)
    (F : Finset ι) (hF : F.Nonempty) :
    ContinuousOn (partitionWeightsValue ρ) (chartDomain ρ F) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he : (chartDomain ρ F).domRestrict (partitionWeightsValue ρ) =
      finitePartitionWeights ρ F hF := by
    funext x
    exact partitionWeightsValue_eq_finite ρ F hF x
  rw [he]
  exact continuous_finitePartitionWeights ρ F hF

/-- A fixed finite closed-support window controls all nearby values. -/
theorem continuous_partitionWeightsValue (ρ : PartitionOfUnity ι X) :
    Continuous (partitionWeightsValue ρ) := by
  rw [continuous_iff_continuousAt]
  intro x
  have hs : (ρ.fintsupport x).Nonempty :=
    (partition_finsupport_nonempty ρ x).mono (ρ.finsupport_subset_fintsupport x)
  exact (continuousOn_partitionWeightsValue ρ _ hs).continuousAt (chartDomain_mem_nhds ρ x)

/-- Literal finite weights with a genuine common point of their cover members. -/
abbrev CoverWeights (W : ι → Set X) :=
  {w : OrderWeights ι // IsNerveFace W w.weights.support}

theorem partitionWeightsValue_support (ρ : PartitionOfUnity ι X) (x : X) :
    (partitionWeightsValue ρ x).weights.support = ρ.finsupport x := by
  ext i
  simp only [Finsupp.mem_support_iff, partitionWeightsValue_apply, ρ.mem_finsupport,
    Function.mem_support]

theorem partitionWeightsValue_isNerveFace (W : ι → Set X) (ρ : PartitionOfUnity ι X)
    (hρ : ρ.IsSubordinate W) (x : X) :
    IsNerveFace W (partitionWeightsValue ρ x).weights.support := by
  rw [partitionWeightsValue_support]
  exact partition_support_isNerveFace W ρ hρ x

/-- The original partition map into the common-intersection weight subspace. -/
noncomputable def numerableCoverClassifier (W : ι → Set X) (ρ : PartitionOfUnity ι X)
    (hρ : ρ.IsSubordinate W) : C(X, CoverWeights W) where
  toFun x := ⟨partitionWeightsValue ρ x, partitionWeightsValue_isNerveFace W ρ hρ x⟩
  continuous_toFun := (continuous_partitionWeightsValue ρ).subtype_mk _

end ArtinNormalisers.Deligne5
