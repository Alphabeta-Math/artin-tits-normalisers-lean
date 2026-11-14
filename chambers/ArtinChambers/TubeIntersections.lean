module

public import ArtinChambers.SignCells

/-!
# Components of actual chamber-tube intersections

For a nonempty family of chambers, real signs on the forms where chamber
signs disagree determine the components of its actual tube intersection.
Every realized piece contracts by first moving the imaginary coordinate to
a point of one chosen chamber and then moving its real coordinate inside
the convex partial sign region. Repeated forms and empty form families are
allowed. The argument does not require the chamber family to be finite.
-/

@[expose] public section

namespace ArtinNormalisers.Chamber3

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {H : Type*} {ℓ : H → E →L[ℝ] ℝ}

/-- The literal intersection of a family of tubes in the actual complement. -/
def tubeIntersection (F : Set (Chamber ℓ)) : Set (ComplexComplement ℓ) :=
  {p | ∀ C ∈ F, p ∈ tubeSet C}

/-- A form on which the selected chamber signs are not all the same. -/
def tubeDisagreement (F : Set (Chamber ℓ)) (h : H) : Prop :=
  ∃ C ∈ F, ∃ D ∈ F, C.signs h ≠ D.signs h

/-- The actual real region specified only at the disagreeing forms. -/
def overlapRealRegion (F : Set (Chamber ℓ)) (ρ : H → Bool) : Set E :=
  {x | ∀ h, tubeDisagreement F h → x ∈ signHalfSpace (ℓ h) (ρ h)}

/-- A sign piece of the actual tube intersection, with its subspace topology. -/
def tubeIntersectionPiece (F : Set (Chamber ℓ)) (ρ : H → Bool) :
    Set (ComplexComplement ℓ) :=
  {p | p ∈ tubeIntersection F ∧ p.val.1 ∈ overlapRealRegion F ρ}

private theorem halfSpace_sign_unique {f : E →L[ℝ] ℝ} {s t : Bool} {y : E}
    (hs : y ∈ signHalfSpace f s) (ht : y ∈ signHalfSpace f t) : s = t := by
  cases s <;> cases t <;> try rfl
  · have hn : f y < 0 := hs
    have hp : 0 < f y := ht
    exact False.elim (lt_asymm hn hp)
  · have hp : 0 < f y := hs
    have hn : f y < 0 := ht
    exact False.elim (lt_asymm hn hp)

theorem tubeIntersection_real_ne_zero {F : Set (Chamber ℓ)}
    {p : ComplexComplement ℓ} (hp : p ∈ tubeIntersection F) {h : H}
    (hd : tubeDisagreement F h) : ℓ h p.val.1 ≠ 0 := by
  intro hz
  obtain ⟨C, hC, D, hD, hne⟩ := hd
  exact hne (halfSpace_sign_unique (hp C hC h hz) (hp D hD h hz))

theorem signs_eq_of_not_tubeDisagreement {F : Set (Chamber ℓ)} {h : H}
    (hd : ¬tubeDisagreement F h) {C D : Chamber ℓ} (hC : C ∈ F) (hD : D ∈ F) :
    C.signs h = D.signs h := by
  by_contra hne
  exact hd ⟨C, hC, D, hD, hne⟩

theorem convex_overlapRealRegion (F : Set (Chamber ℓ)) (ρ : H → Bool) :
    Convex ℝ (overlapRealRegion F ρ) := by
  have he : overlapRealRegion F ρ =
      ⋂ h, ⋂ (_ : tubeDisagreement F h), signHalfSpace (ℓ h) (ρ h) := by
    ext x
    simp [overlapRealRegion]
  rw [he]
  exact convex_iInter fun h => convex_iInter fun _ => convex_signHalfSpace (ℓ h) (ρ h)

theorem isOpen_overlapRealRegion [Finite H] (F : Set (Chamber ℓ)) (ρ : H → Bool) :
    IsOpen (overlapRealRegion F ρ) := by
  have he : overlapRealRegion F ρ =
      ⋂ h, ⋂ (_ : tubeDisagreement F h), signHalfSpace (ℓ h) (ρ h) := by
    ext x
    simp [overlapRealRegion]
  rw [he]
  exact isOpen_iInter_of_finite fun h =>
    isOpen_iInter_of_finite fun _ => isOpen_signHalfSpace (ℓ h) (ρ h)

theorem tubeIntersection_eq_iUnion_pieces (F : Set (Chamber ℓ)) :
    tubeIntersection F = ⋃ ρ : H → Bool, tubeIntersectionPiece F ρ := by
  classical
  ext p
  constructor
  · intro hp
    refine Set.mem_iUnion.mpr ⟨fun h => decide (0 < ℓ h p.val.1), hp, ?_⟩
    intro h hd
    have hn := tubeIntersection_real_ne_zero hp hd
    by_cases hpos : 0 < ℓ h p.val.1
    · simp [signHalfSpace, hpos]
    · have hneg : ℓ h p.val.1 < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hn
      simpa [signHalfSpace, hpos] using hneg
  · rintro hp
    obtain ⟨ρ, hρ⟩ := Set.mem_iUnion.mp hp
    exact hρ.1

namespace TubeIntersections

variable (F : Set (Chamber ℓ)) (ρ : H → Bool)
  (C0 : Chamber ℓ) (hC0 : C0 ∈ F) (c0 : E) (hc0 : c0 ∈ C0.region)

/-- A point satisfying the tube conditions, retained as a point of the
literal complement and the specified overlap piece. -/
def makePoint (x y : E) (hx : x ∈ overlapRealRegion F ρ)
    (hy : ∀ C ∈ F, ∀ h, ℓ h x = 0 → y ∈ signHalfSpace (ℓ h) (C.signs h)) :
    ↥(tubeIntersectionPiece F ρ) :=
  ⟨⟨(x, y), fun h hz => signHalfSpace_nonzero (hy C0 hC0 h hz.1) hz.2⟩, hy, hx⟩

include hC0 hc0 in
theorem chosenImaginary_condition {x : E} (hx : x ∈ overlapRealRegion F ρ) :
    ∀ C ∈ F, ∀ h, ℓ h x = 0 → c0 ∈ signHalfSpace (ℓ h) (C.signs h) := by
  intro C hC h hz
  by_cases hd : tubeDisagreement F h
  · exact False.elim (signHalfSpace_nonzero (hx h hd) hz)
  · rw [signs_eq_of_not_tubeDisagreement hd hC hC0]
    exact hc0 h

/-- The imaginary coordinate is the fixed chamber point, and the real
coordinate ranges over the actual convex partial-sign region. -/
def centerAt (x : E) (hx : x ∈ overlapRealRegion F ρ) :
    ↥(tubeIntersectionPiece F ρ) :=
  makePoint F ρ C0 hC0 x c0 hx (chosenImaginary_condition F ρ C0 hC0 c0 hc0 hx)

variable [ContinuousAdd E] [ContinuousSMul ℝ E]

def stageOneMap : C(↥(tubeIntersectionPiece F ρ), ↥(tubeIntersectionPiece F ρ)) where
  toFun p := centerAt F ρ C0 hC0 c0 hc0 p.val.val.1 p.property.2
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).prodMk
      continuous_const

def imaginaryHomotopy : ContinuousMap.Homotopy
    (ContinuousMap.id ↥(tubeIntersectionPiece F ρ)) (stageOneMap F ρ C0 hC0 c0 hc0) where
  toFun tp := makePoint F ρ C0 hC0 tp.2.val.val.1
    ((1 - (tp.1 : ℝ)) • tp.2.val.val.2 + (tp.1 : ℝ) • c0) tp.2.property.2 (by
      intro C hC h hz
      exact (convex_signHalfSpace (ℓ h) (C.signs h))
        (tp.2.property.1 C hC h hz)
        (chosenImaginary_condition F ρ C0 hC0 c0 hc0 tp.2.property.2 C hC h hz)
        (sub_nonneg.mpr tp.1.property.2) tp.1.property.1 (sub_add_cancel 1 (tp.1 : ℝ)))
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    fun_prop
  map_zero_left p := by
    apply Subtype.ext
    apply Subtype.ext
    simp [makePoint]
  map_one_left p := by
    apply Subtype.ext
    apply Subtype.ext
    simp [makePoint, stageOneMap, centerAt]

def realHomotopy (x0 : E) (hx0 : x0 ∈ overlapRealRegion F ρ) :
    ContinuousMap.Homotopy (stageOneMap F ρ C0 hC0 c0 hc0)
      (ContinuousMap.const _ (centerAt F ρ C0 hC0 c0 hc0 x0 hx0)) where
  toFun tp := centerAt F ρ C0 hC0 c0 hc0
    ((1 - (tp.1 : ℝ)) • tp.2.val.val.1 + (tp.1 : ℝ) • x0)
    ((convex_overlapRealRegion F ρ) tp.2.property.2 hx0
      (sub_nonneg.mpr tp.1.property.2) tp.1.property.1 (sub_add_cancel 1 (tp.1 : ℝ)))
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    fun_prop
  map_zero_left p := by
    apply Subtype.ext
    apply Subtype.ext
    simp [stageOneMap, centerAt, makePoint]
  map_one_left p := by
    apply Subtype.ext
    apply Subtype.ext
    simp [centerAt, makePoint]

end TubeIntersections

theorem tubeIntersectionPiece_nonempty_iff {F : Set (Chamber ℓ)}
    (hF : F.Nonempty) (ρ : H → Bool) :
    (tubeIntersectionPiece F ρ).Nonempty ↔ (overlapRealRegion F ρ).Nonempty := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.val.1, hp.2⟩
  · rintro ⟨x0, hx0⟩
    obtain ⟨C0, hC0⟩ := hF
    obtain ⟨c0, hc0⟩ := C0.nonempty
    exact ⟨_, (TubeIntersections.centerAt F ρ C0 hC0 c0 hc0 x0 hx0).property⟩

variable [ContinuousAdd E] [ContinuousSMul ℝ E]

/-- Every realized sign piece is genuinely contractible in its actual
subspace topology. No finite dimension or sphericality assumption is used. -/
theorem contractibleSpace_tubeIntersectionPiece {F : Set (Chamber ℓ)}
    (hF : F.Nonempty) {ρ : H → Bool} (hne : (tubeIntersectionPiece F ρ).Nonempty) :
    ContractibleSpace ↥(tubeIntersectionPiece F ρ) := by
  obtain ⟨C0, hC0⟩ := hF
  obtain ⟨c0, hc0⟩ := C0.nonempty
  obtain ⟨p, hp⟩ := hne
  apply (contractible_iff_id_nullhomotopic _).2
  exact ⟨TubeIntersections.centerAt F ρ C0 hC0 c0 hc0 p.val.1 hp.2,
    ⟨(TubeIntersections.imaginaryHomotopy F ρ C0 hC0 c0 hc0).trans
      (TubeIntersections.realHomotopy F ρ C0 hC0 c0 hc0 p.val.1 hp.2)⟩⟩

theorem isPathConnected_tubeIntersectionPiece {F : Set (Chamber ℓ)}
    (hF : F.Nonempty) {ρ : H → Bool} (hne : (tubeIntersectionPiece F ρ).Nonempty) :
    IsPathConnected (tubeIntersectionPiece F ρ) := by
  let := contractibleSpace_tubeIntersectionPiece hF hne
  exact isPathConnected_iff_pathConnectedSpace.mpr inferInstance

/-- These pieces are exactly the connected components in the actual tube
intersection, including when forms repeat or the form family is empty. -/
theorem tubeIntersectionPiece_eq_connectedComponentIn {F : Set (Chamber ℓ)}
    (hF : F.Nonempty) {ρ : H → Bool} {p : ComplexComplement ℓ}
    (hp : p ∈ tubeIntersectionPiece F ρ) :
    tubeIntersectionPiece F ρ = connectedComponentIn (tubeIntersection F) p := by
  apply Set.Subset.antisymm
  · have hpre := (isPathConnected_tubeIntersectionPiece hF ⟨p, hp⟩).isConnected.isPreconnected
    exact hpre.subset_connectedComponentIn hp (fun _ h => h.1)
  · intro q hq
    refine ⟨connectedComponentIn_subset (tubeIntersection F) p hq, ?_⟩
    intro h hd
    let f : ComplexComplement ℓ → ℝ := fun z => ℓ h z.val.1
    have hcont : ContinuousOn f (connectedComponentIn (tubeIntersection F) p) :=
      ((ℓ h).continuous.comp (continuous_fst.comp continuous_subtype_val)).continuousOn
    have hzero : ∀ z ∈ connectedComponentIn (tubeIntersection F) p, f z ≠ 0 :=
      fun z hz => tubeIntersection_real_ne_zero
        (connectedComponentIn_subset (tubeIntersection F) p hz) hd
    have hpc : p ∈ connectedComponentIn (tubeIntersection F) p := mem_connectedComponentIn hp.1
    have hph := hp.2 h hd
    cases hs : ρ h
    · have hn : f p < 0 := by simpa [f, signHalfSpace, hs] using hph
      have hqn := isPreconnected_connectedComponentIn.gt_of_ne hcont hzero ⟨p, hpc, hn⟩ hq
      simpa [f, signHalfSpace, hs] using hqn
    · have hn : 0 < f p := by simpa [f, signHalfSpace, hs] using hph
      have hqp := isPreconnected_connectedComponentIn.lt_of_ne hcont hzero ⟨p, hpc, hn⟩ hq
      simpa [f, signHalfSpace, hs] using hqp

/-- The same sign pieces are exactly the path components; this records
both directions needed to identify actual overlap path classes. -/
theorem tubeIntersectionPiece_eq_pathComponentIn {F : Set (Chamber ℓ)}
    (hF : F.Nonempty) {ρ : H → Bool} {p : ComplexComplement ℓ}
    (hp : p ∈ tubeIntersectionPiece F ρ) :
    tubeIntersectionPiece F ρ = pathComponentIn (tubeIntersection F) p := by
  apply Set.Subset.antisymm
  · have hpath := isPathConnected_tubeIntersectionPiece hF ⟨p, hp⟩
    exact hpath.subset_pathComponentIn hp (fun _ h => h.1)
  · rw [tubeIntersectionPiece_eq_connectedComponentIn hF hp]
    exact (isPathConnected_pathComponentIn hp.1).isConnected.isPreconnected
      |>.subset_connectedComponentIn (mem_pathComponentIn_self hp.1) pathComponentIn_subset

omit [ContinuousAdd E] [ContinuousSMul ℝ E] in
/-- Two sign pieces can overlap only if their signs agree on every
disagreeing form. Values of the sign functions elsewhere are immaterial. -/
theorem tubeIntersectionPiece_signs_eq {F : Set (Chamber ℓ)} {ρ σ : H → Bool}
    {p : ComplexComplement ℓ} (hρ : p ∈ tubeIntersectionPiece F ρ)
    (hσ : p ∈ tubeIntersectionPiece F σ) {h : H} (hd : tubeDisagreement F h) :
    ρ h = σ h :=
  halfSpace_sign_unique (hρ.2 h hd) (hσ.2 h hd)

omit [ContinuousAdd E] [ContinuousSMul ℝ E] in
theorem tubeIntersectionPiece_eq_of_signs_eq {F : Set (Chamber ℓ)} {ρ σ : H → Bool}
    (hs : ∀ h, tubeDisagreement F h → ρ h = σ h) :
    tubeIntersectionPiece F ρ = tubeIntersectionPiece F σ := by
  ext p
  constructor
  · intro hp
    refine ⟨hp.1, fun h hd => ?_⟩
    rw [← hs h hd]
    exact hp.2 h hd
  · intro hp
    refine ⟨hp.1, fun h hd => ?_⟩
    rw [hs h hd]
    exact hp.2 h hd

end ArtinNormalisers.Chamber3
