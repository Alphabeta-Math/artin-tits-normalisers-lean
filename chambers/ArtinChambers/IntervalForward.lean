module

public import ArtinChambers.IntervalGroupoid
public import ArtinChambers.Tubes
public import ArtinChambers.TubeIntersections
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

/-!
# From the interval presentation to the actual complement

Choose an actual real point of each chamber. The positive generator `C→D`
is the unique class joining their real basepoints inside the actual tube of
`D`. If `D` lies between `C` and `F`, the first two basepoints lie in one
actual component of the intersection of the tubes of `D` and `F`. This
proves the interval relation and yields a genuine functor. No equivalence,
faithfulness or adjacency presentation is assumed or asserted here.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false

namespace ArtinNormalisers.Chamber3

open CategoryTheory

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {H : Type*} {ℓ : H → E →L[ℝ] ℝ}

/-- An arbitrary family of actual chamber points, permitting later
equivariant choices without changing the geometric functor construction. -/
abbrev ChamberPointFamily (ℓ : H → E →L[ℝ] ℝ) := ∀ C : Chamber ℓ, ↥C.region

def chamberBasepoint (c : ChamberPointFamily ℓ) (C : Chamber ℓ) : ComplexComplement ℓ :=
  ⟨((c C).val, 0), fun h hz => signHalfSpace_nonzero ((c C).property h) hz.1⟩

theorem chamberBasepoint_mem_tubeSet (c : ChamberPointFamily ℓ) (C D : Chamber ℓ) :
    chamberBasepoint c C ∈ tubeSet D := by
  intro h hz
  exact False.elim (signHalfSpace_nonzero ((c C).property h) hz)

def chamberBasepointInTube (c : ChamberPointFamily ℓ) (C D : Chamber ℓ) : Tubes.Space D :=
  ⟨chamberBasepoint c C, chamberBasepoint_mem_tubeSet c C D⟩

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

namespace IntervalForward

/-- The unique local path class in a contractible actual tube. -/
noncomputable def localClass (D : Chamber ℓ) (p q : Tubes.Space D) :
    FundamentalGroupoid.mk p ⟶ FundamentalGroupoid.mk q :=
  Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath p q)

@[simp] theorem localClass_self (D : Chamber ℓ) (p : Tubes.Space D) :
    localClass D p p = 𝟙 (FundamentalGroupoid.mk p) :=
  @Subsingleton.elim (Path.Homotopic.Quotient p p) inferInstance _ _

theorem localClass_comp (D : Chamber ℓ) (p q r : Tubes.Space D) :
    localClass D p q ≫ localClass D q r = localClass D p r :=
  @Subsingleton.elim (Path.Homotopic.Quotient p r) inferInstance _ _

/-- A path class in the image of the actual tube inclusion. -/
noncomputable def classInTube (D : Chamber ℓ) {p q : ComplexComplement ℓ}
    (hp : p ∈ tubeSet D) (hq : q ∈ tubeSet D) :
    FundamentalGroupoid.mk p ⟶ FundamentalGroupoid.mk q :=
  (FundamentalGroupoid.map (ContinuousMap.subtypeVal (tubeSet D))).map
    (localClass D ⟨p, hp⟩ ⟨q, hq⟩)

@[simp] theorem classInTube_self (D : Chamber ℓ) {p : ComplexComplement ℓ}
    (hp : p ∈ tubeSet D) : classInTube D hp hp = 𝟙 (FundamentalGroupoid.mk p) := by
  rw [classInTube, localClass_self]
  exact (FundamentalGroupoid.map (ContinuousMap.subtypeVal (tubeSet D))).map_id _

theorem classInTube_comp (D : Chamber ℓ) {p q r : ComplexComplement ℓ}
    (hp : p ∈ tubeSet D) (hq : q ∈ tubeSet D) (hr : r ∈ tubeSet D) :
    classInTube D hp hq ≫ classInTube D hq hr = classInTube D hp hr := by
  dsimp only [classInTube]
  exact ((FundamentalGroupoid.map (ContinuousMap.subtypeVal (tubeSet D))).map_comp _ _).symm.trans
    (congrArg (fun f => (FundamentalGroupoid.map (ContinuousMap.subtypeVal (tubeSet D))).map f)
      (localClass_comp D ⟨p, hp⟩ ⟨q, hq⟩ ⟨r, hr⟩))

/-- The local class is the actual homotopy class of every path whose range
lies in the indicated tube; contractibility supplies independence of choice. -/
theorem classInTube_eq_path (D : Chamber ℓ) {p q : ComplexComplement ℓ}
    (hp : p ∈ tubeSet D) (hq : q ∈ tubeSet D) (γ : Path p q)
    (hγ : ∀ t, γ t ∈ tubeSet D) :
    classInTube D hp hq = Path.Homotopic.Quotient.mk γ := by
  let γD : Path (⟨p, hp⟩ : Tubes.Space D) ⟨q, hq⟩ :=
    { toFun t := ⟨γ t, hγ t⟩
      continuous_toFun := γ.continuous.subtype_mk _
      source' := Subtype.ext γ.source
      target' := Subtype.ext γ.target }
  have he : localClass D ⟨p, hp⟩ ⟨q, hq⟩ = Path.Homotopic.Quotient.mk γD :=
    @Subsingleton.elim (Path.Homotopic.Quotient (⟨p, hp⟩ : Tubes.Space D) ⟨q, hq⟩)
      inferInstance _ _
  rw [classInTube, he]
  change (Path.Homotopic.Quotient.mk γD).map (ContinuousMap.subtypeVal (tubeSet D)) = _
  rw [← Path.Homotopic.Quotient.mk_map]
  congr 1

variable (c : ChamberPointFamily ℓ)

/-- The positive geometric crossing for an ordered pair of chambers. -/
noncomputable def positiveClass (C D : Chamber ℓ) :
    FundamentalGroupoid.mk (chamberBasepoint c C) ⟶
      FundamentalGroupoid.mk (chamberBasepoint c D) :=
  classInTube D (chamberBasepoint_mem_tubeSet c C D) (chamberBasepoint_mem_tubeSet c D D)

@[simp] theorem positiveClass_self (C : Chamber ℓ) :
    positiveClass c C C = 𝟙 _ :=
  classInTube_self _ _

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
private theorem pairDisagreement_ne {C D : Chamber ℓ} {h : H}
    (hd : tubeDisagreement ({C, D} : Set (Chamber ℓ)) h) : C.signs h ≠ D.signs h := by
  intro he
  obtain ⟨A, hA, B, hB, hne⟩ := hd
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA hB
  rcases hA with rfl | rfl <;> rcases hB with rfl | rfl
  · exact hne rfl
  · exact hne he
  · exact hne he.symm
  · exact hne rfl

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
private theorem middle_sign_of_ne {C D F : Chamber ℓ}
    (hb : ChamberBetween C D F) {h : H} (hne : D.signs h ≠ F.signs h) :
    D.signs h = C.signs h := by
  have hh := hb h
  cases hc : C.signs h <;> cases hd : D.signs h <;> cases hf : F.signs h <;>
    simp_all

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
theorem basepoint_mem_intervalPiece (C D F : Chamber ℓ) (hb : ChamberBetween C D F) :
    chamberBasepoint c C ∈ tubeIntersectionPiece ({D, F} : Set (Chamber ℓ)) C.signs ∧
    chamberBasepoint c D ∈ tubeIntersectionPiece ({D, F} : Set (Chamber ℓ)) C.signs := by
  constructor
  · refine ⟨fun A _ => chamberBasepoint_mem_tubeSet c C A, fun h _ => ?_⟩
    exact (c C).property h
  · refine ⟨fun A _ => chamberBasepoint_mem_tubeSet c D A, fun h hd => ?_⟩
    rw [← middle_sign_of_ne hb (pairDisagreement_ne hd)]
    exact (c D).property h

/-- The interval relation holds for actual homotopy classes, using a path
in a genuine component of the intersection of the two target tubes. -/
theorem positiveClass_comp (C D F : Chamber ℓ) (hb : ChamberBetween C D F) :
    positiveClass c C F = positiveClass c C D ≫ positiveClass c D F := by
  obtain ⟨hC, hD⟩ := basepoint_mem_intervalPiece c C D F hb
  have hfamily : ({D, F} : Set (Chamber ℓ)).Nonempty := ⟨D, by simp⟩
  have hconn := isPathConnected_tubeIntersectionPiece hfamily ⟨_, hC⟩
  obtain ⟨γ, hγ⟩ := hconn.joinedIn _ hC _ hD
  have hγD : ∀ t, γ t ∈ tubeSet D := fun t => (hγ t).1 D (by simp)
  have hγF : ∀ t, γ t ∈ tubeSet F := fun t => (hγ t).1 F (by simp)
  have he : positiveClass c C D =
      classInTube F (chamberBasepoint_mem_tubeSet c C F)
        (chamberBasepoint_mem_tubeSet c D F) :=
    (classInTube_eq_path D _ _ γ hγD).trans (classInTube_eq_path F _ _ γ hγF).symm
  rw [he]
  exact (classInTube_comp F _ _ _).symm

/-- The target is the fundamental groupoid of the literal complement. -/
noncomputable def generatorData : IntervalGeneratorData ℓ (FundamentalGroupoid (ComplexComplement ℓ)) where
  obj C := FundamentalGroupoid.mk (chamberBasepoint c C)
  positive C D := positiveClass c C D

theorem generatorData_respects : (generatorData c).RespectsIntervals :=
  ⟨positiveClass_self c, positiveClass_comp c⟩

end IntervalForward

/-- The genuine functor on the interval groupoid, induced by actual paths
inside the chamber tubes and their proved interval relations. -/
noncomputable def intervalForward (c : ChamberPointFamily ℓ) :
    IntervalGroupoid ℓ ⥤ FundamentalGroupoid (ComplexComplement ℓ) :=
  (IntervalForward.generatorData c).extensionFunctor (IntervalForward.generatorData_respects c)

@[simp] theorem intervalForward_obj (c : ChamberPointFamily ℓ) (C : Chamber ℓ) :
    (intervalForward c).obj (intervalObject C) =
      FundamentalGroupoid.mk (chamberBasepoint c C) := rfl

@[simp] theorem intervalForward_positive (c : ChamberPointFamily ℓ) (C D : Chamber ℓ) :
    (intervalForward c).map (intervalPositive C D) = IntervalForward.positiveClass c C D :=
  (IntervalForward.generatorData c).extensionFunctor_positive _ C D

theorem intervalForward_positive_eq_path (c : ChamberPointFamily ℓ) (C D : Chamber ℓ)
    (γ : Path (chamberBasepoint c C) (chamberBasepoint c D))
    (hγ : ∀ t, γ t ∈ tubeSet D) :
    (intervalForward c).map (intervalPositive C D) = Path.Homotopic.Quotient.mk γ := by
  rw [intervalForward_positive]
  exact IntervalForward.classInTube_eq_path D _ _ γ hγ

end ArtinNormalisers.Chamber3
