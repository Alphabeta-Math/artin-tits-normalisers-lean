module

public import ArtinChambers.Arrangement
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Connected.Basic

/-!
# Sign cells and the connected chambers of a real linear arrangement

The proofs use mathlib's convex halfspaces and the constancy of the sign of
a continuous nonvanishing real function on a preconnected set. The forms may
repeat or be proportional; no hyperplane-separation counting is asserted.
-/

@[expose] public section

namespace ArtinNormalisers.Chamber3

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {H : Type*}

theorem isOpen_signHalfSpace (f : E →L[ℝ] ℝ) (s : Bool) :
    IsOpen (signHalfSpace f s) := by
  cases s
  · exact isOpen_lt f.continuous continuous_const
  · exact isOpen_lt continuous_const f.continuous

theorem convex_signHalfSpace (f : E →L[ℝ] ℝ) (s : Bool) :
    Convex ℝ (signHalfSpace f s) := by
  cases s
  · exact (convex_Iio (0 : ℝ)).linear_preimage f.toLinearMap
  · exact (convex_Ioi (0 : ℝ)).linear_preimage f.toLinearMap

theorem signHalfSpace_nonzero {f : E →L[ℝ] ℝ} {s : Bool} {x : E}
    (hx : x ∈ signHalfSpace f s) : f x ≠ 0 := by
  cases s
  · exact ne_of_lt hx
  · exact ne_of_gt hx

theorem signCell_eq_iInter (ℓ : H → E →L[ℝ] ℝ) (s : H → Bool) :
    signCell ℓ s = ⋂ h, signHalfSpace (ℓ h) (s h) := by
  ext x
  simp [signCell]

theorem isOpen_signCell [Finite H] (ℓ : H → E →L[ℝ] ℝ) (s : H → Bool) :
    IsOpen (signCell ℓ s) := by
  rw [signCell_eq_iInter]
  exact isOpen_iInter_of_finite fun h => isOpen_signHalfSpace (ℓ h) (s h)

theorem convex_signCell (ℓ : H → E →L[ℝ] ℝ) (s : H → Bool) :
    Convex ℝ (signCell ℓ s) := by
  rw [signCell_eq_iInter]
  exact convex_iInter fun h => convex_signHalfSpace (ℓ h) (s h)

theorem signCell_subset_regularSet (ℓ : H → E →L[ℝ] ℝ) (s : H → Bool) :
    signCell ℓ s ⊆ regularSet ℓ := by
  intro x hx h
  exact signHalfSpace_nonzero (hx h)

theorem signCell_signs_unique {ℓ : H → E →L[ℝ] ℝ} {s t : H → Bool} {x : E}
    (hs : x ∈ signCell ℓ s) (ht : x ∈ signCell ℓ t) : s = t := by
  funext h
  have hsh := hs h
  have hth := ht h
  cases hs' : s h <;> cases ht' : t h <;> try rfl
  · have hneg : ℓ h x < 0 := by simpa [signHalfSpace, hs'] using hsh
    have hpos : 0 < ℓ h x := by simpa [signHalfSpace, ht'] using hth
    exact False.elim (lt_asymm hneg hpos)
  · have hpos : 0 < ℓ h x := by simpa [signHalfSpace, hs'] using hsh
    have hneg : ℓ h x < 0 := by simpa [signHalfSpace, ht'] using hth
    exact False.elim (lt_asymm hpos hneg)

/-- The chamber containing a regular point, with its actual root signs. -/
noncomputable def chamberOfRegular (ℓ : H → E →L[ℝ] ℝ) (x : E)
    (hx : x ∈ regularSet ℓ) : Chamber ℓ := by
  classical
  refine ⟨fun h => decide (0 < ℓ h x), x, ?_⟩
  intro h
  by_cases hp : 0 < ℓ h x
  · simp [signHalfSpace, hp]
  · have hn : ℓ h x < 0 := lt_of_le_of_ne (le_of_not_gt hp) (hx h)
    simpa [signHalfSpace, hp] using hn

theorem mem_chamberOfRegular_region (ℓ : H → E →L[ℝ] ℝ) (x : E)
    (hx : x ∈ regularSet ℓ) : x ∈ (chamberOfRegular ℓ x hx).region := by
  classical
  intro h
  by_cases hp : 0 < ℓ h x
  · simp [chamberOfRegular, signHalfSpace, hp]
  · have hn : ℓ h x < 0 := lt_of_le_of_ne (le_of_not_gt hp) (hx h)
    simpa [chamberOfRegular, signHalfSpace, hp] using hn

namespace Chamber

variable {ℓ : H → E →L[ℝ] ℝ}

theorem region_nonempty (C : Chamber ℓ) : C.region.Nonempty := C.nonempty

theorem isOpen_region [Finite H] (C : Chamber ℓ) : IsOpen C.region :=
  isOpen_signCell ℓ C.signs

theorem convex_region (C : Chamber ℓ) : Convex ℝ C.region :=
  convex_signCell ℓ C.signs

theorem region_subset_regularSet (C : Chamber ℓ) : C.region ⊆ regularSet ℓ :=
  signCell_subset_regularSet ℓ C.signs

theorem eq_of_mem_region {C D : Chamber ℓ} {x : E}
    (hC : x ∈ C.region) (hD : x ∈ D.region) : C = D := by
  apply Chamber.ext
  exact signCell_signs_unique hC hD

theorem signs_eq_true_iff {C : Chamber ℓ} {x : E} (hx : x ∈ C.region) (h : H) :
    C.signs h = true ↔ 0 < ℓ h x := by
  have hh := hx h
  cases hs : C.signs h
  · have hn : ℓ h x < 0 := by simpa [signHalfSpace, hs] using hh
    simp [not_lt.mpr hn.le]
  · have hp : 0 < ℓ h x := by simpa [signHalfSpace, hs] using hh
    simp [hp]

theorem eq_chamberOfRegular {C : Chamber ℓ} {x : E} (hx : x ∈ C.region) :
    C = chamberOfRegular ℓ x (C.region_subset_regularSet hx) :=
  eq_of_mem_region hx (mem_chamberOfRegular_region ℓ x _)

section TopologicalVectorSpace

variable [ContinuousAdd E] [ContinuousSMul ℝ E]

theorem isPreconnected_region (C : Chamber ℓ) : IsPreconnected C.region :=
  C.convex_region.isPreconnected

theorem isPathConnected_region (C : Chamber ℓ) : IsPathConnected C.region :=
  C.convex_region.isPathConnected C.region_nonempty

/-- A chamber is exactly the connected component of each of its points in
the actual regular locus. This does not require a finite family of forms. -/
theorem region_eq_connectedComponentIn (C : Chamber ℓ) {x : E} (hx : x ∈ C.region) :
    C.region = connectedComponentIn (regularSet ℓ) x := by
  apply Set.Subset.antisymm
  · exact C.isPreconnected_region.subset_connectedComponentIn hx C.region_subset_regularSet
  · intro y hy h
    have hzero : ∀ z ∈ connectedComponentIn (regularSet ℓ) x, ℓ h z ≠ 0 :=
      fun z hz => connectedComponentIn_subset (regularSet ℓ) x hz h
    have hcont : ContinuousOn (ℓ h) (connectedComponentIn (regularSet ℓ) x) :=
      (ℓ h).continuous.continuousOn
    have hxcomp : x ∈ connectedComponentIn (regularSet ℓ) x :=
      mem_connectedComponentIn (C.region_subset_regularSet hx)
    have hxh := hx h
    cases hs : C.signs h
    · have hn : ℓ h x < 0 := by simpa [signHalfSpace, hs] using hxh
      have hyn := isPreconnected_connectedComponentIn.gt_of_ne hcont hzero
        ⟨x, hxcomp, hn⟩ hy
      simpa [signHalfSpace, hs] using hyn
    · have hp : 0 < ℓ h x := by simpa [signHalfSpace, hs] using hxh
      have hyp := isPreconnected_connectedComponentIn.lt_of_ne hcont hzero
        ⟨x, hxcomp, hp⟩ hy
      simpa [signHalfSpace, hs] using hyp

end TopologicalVectorSpace

end Chamber

theorem existsUnique_chamber_mem (ℓ : H → E →L[ℝ] ℝ) {x : E}
    (hx : x ∈ regularSet ℓ) : ∃! C : Chamber ℓ, x ∈ C.region := by
  refine ⟨chamberOfRegular ℓ x hx, mem_chamberOfRegular_region ℓ x hx, ?_⟩
  intro C hC
  exact Chamber.eq_of_mem_region hC (mem_chamberOfRegular_region ℓ x hx)

end ArtinNormalisers.Chamber3
