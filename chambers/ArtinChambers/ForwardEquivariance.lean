module

public import ArtinChambers.ActualTubes
public import ArtinChambers.ChamberPoints
public import ArtinChambers.IntervalAction
public import ArtinChambers.IntervalForward
public import ArtinChambers.IntervalEquivalence

/-!
# The forward geometric functor and the actual quotient action

The interval functor is transported through the identity-coordinate
homeomorphism to the original relative complement. Positive arrows are actual
path classes in the target chamber's tube. Tube covariance proves their
equivariance when the chosen chamber points are equivariant.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace ArtinNormalisers.Chamber3

open CategoryTheory Theorem18

section FunctorExt

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {H : Type*} {ℓ : H → E →L[ℝ] ℝ}
  {T : Type*} [Groupoid T]

/-- Equality on objects and positive generators determines the full functor. -/
theorem intervalFunctor_ext (F G : IntervalGroupoid ℓ ⥤ T)
    (hobj : ∀ X, F.obj X = G.obj X)
    (hpos : ∀ C D, HEq (F.map (intervalPositive C D)) (G.map (intervalPositive C D))) :
    F = G := by
  let A : IntervalGeneratorData ℓ T :=
    { obj C := G.obj (intervalObject C)
      positive C D := G.map (intervalPositive C D) }
  have hA : A.RespectsIntervals := by
    constructor
    · intro C
      change G.map (intervalPositive C C) = 𝟙 _
      rw [intervalPositive_self, G.map_id]
    · intro C D K h
      change G.map (intervalPositive C K) =
        G.map (intervalPositive C D) ≫ G.map (intervalPositive D K)
      rw [intervalPositive_comp C D K h, G.map_comp]
  have hGobj : G.obj = fun X => A.obj (intervalChamber X) := by
    funext X
    dsimp only [A]
    rw [intervalObject_intervalChamber]
  have hFobj : F.obj = fun X => A.obj (intervalChamber X) :=
    (funext hobj).trans hGobj
  exact (A.extensionFunctor_unique hA F hFobj hpos).trans
    (A.extensionFunctor_unique hA G hGobj (fun _ _ => HEq.rfl)).symm

end FunctorExt

variable {I : Type*} (M : CoxeterMatrix I) (J : Set I)

/-- The actual real basepoint in the original complement. -/
noncomputable def actualChamberBasepoint
    (c : ChamberPointFamily (E := relativeSubspace J) (actualForms M J))
    (C : ActualChamber M J) : Complement M J :=
  (actualComplementHomeomorph M J).symm (chamberBasepoint c C)

theorem actualChamberBasepoint_mem_tube
    (c : ChamberPointFamily (E := relativeSubspace J) (actualForms M J))
    (C D : ActualChamber M J) :
    actualChamberBasepoint M J c C ∈ actualTubeSet M J D :=
  chamberBasepoint_mem_tubeSet c C D

/-- The existing forward functor, transported to the literal parent complement. -/
noncomputable def actualIntervalForwardOfPoints
    (c : ChamberPointFamily (E := relativeSubspace J) (actualForms M J)) :
    IntervalGroupoid (E := relativeSubspace J) (actualForms M J) ⥤
      FundamentalGroupoid (Complement M J) :=
  intervalForward c ⋙
    FundamentalGroupoid.map
      ⟨(actualComplementHomeomorph M J).symm, (actualComplementHomeomorph M J).symm.continuous⟩

@[simp] theorem actualIntervalForwardOfPoints_obj
    (c : ChamberPointFamily (E := relativeSubspace J) (actualForms M J))
    (C : ActualChamber M J) :
    (actualIntervalForwardOfPoints M J c).obj (intervalObject C) =
      FundamentalGroupoid.mk (actualChamberBasepoint M J c C) := rfl

/-- Every actual path in the indicated actual tube represents the positive arrow. -/
theorem actualIntervalForwardOfPoints_positive_eq_path
    (c : ChamberPointFamily (E := relativeSubspace J) (actualForms M J))
    (C D : ActualChamber M J)
    (γ : Path (actualChamberBasepoint M J c C) (actualChamberBasepoint M J c D))
    (hγ : ∀ t, γ t ∈ actualTubeSet M J D) :
    (actualIntervalForwardOfPoints M J c).map (intervalPositive C D) =
      Path.Homotopic.Quotient.mk γ := by
  change (FundamentalGroupoid.map
      ⟨(actualComplementHomeomorph M J).symm,
        (actualComplementHomeomorph M J).symm.continuous⟩).map
      ((intervalForward c).map (intervalPositive C D)) = _
  rw [intervalForward_positive_eq_path c C D
    (γ.map (actualComplementHomeomorph M J).continuous) hγ]
  change (Path.Homotopic.Quotient.mk
    (γ.map (actualComplementHomeomorph M J).continuous)).map _ = _
  rw [← Path.Homotopic.Quotient.mk_map]
  congr 1

/-- The actual quotient element as a continuous map of the original complement. -/
noncomputable def actualQuotientComplementMap (q : Artin.coxeterNormalizerQuotient M J) :
    C(Complement M J, Complement M J) :=
  ⟨fun p => q • p, continuous_const_smul q⟩

/-- Low-level coordinate equivariance gives equivariance of actual basepoints. -/
theorem actualChamberBasepoint_smul_of_coordinates
    (c : ChamberPointFamily (E := relativeSubspace J) (actualForms M J))
    (q : Artin.coxeterNormalizerQuotient M J)
    (hc : ∀ C, (c (q • C)).val = quotientRepresentation M J q (c C).val)
    (C : ActualChamber M J) :
    actualChamberBasepoint M J c (q • C) = q • actualChamberBasepoint M J c C := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective
    ((Artin.coxeterParabolic M J).subgroupOf (CoxeterNormalizer M J)) q
  apply Subtype.ext
  apply Prod.ext
  · exact hc C
  · change (0 : relativeSubspace J) = normalizerRepresentation M J w 0
    exact (map_zero _).symm

/-- Equivariant actual basepoints make the actual forward functor equivariant.
Only point covariance is a hypothesis; the arrow assertion is proved from paths. -/
theorem actualIntervalForwardOfPoints_equivariant
    (c : ChamberPointFamily (E := relativeSubspace J) (actualForms M J))
    (q : Artin.coxeterNormalizerQuotient M J)
    (hc : ∀ C, actualChamberBasepoint M J c (q • C) =
      q • actualChamberBasepoint M J c C) :
    intervalAction M J q ⋙ actualIntervalForwardOfPoints M J c =
      actualIntervalForwardOfPoints M J c ⋙
        FundamentalGroupoid.map (actualQuotientComplementMap M J q) := by
  apply intervalFunctor_ext
  · intro X
    rw [← intervalObject_intervalChamber X]
    change FundamentalGroupoid.mk (actualChamberBasepoint M J c (q • intervalChamber X)) =
      FundamentalGroupoid.mk (q • actualChamberBasepoint M J c (intervalChamber X))
    exact congrArg FundamentalGroupoid.mk (hc _)
  · intro C D
    let x : ↥(actualTubeSet M J D) :=
      ⟨actualChamberBasepoint M J c C, actualChamberBasepoint_mem_tube M J c C D⟩
    let y : ↥(actualTubeSet M J D) :=
      ⟨actualChamberBasepoint M J c D, actualChamberBasepoint_mem_tube M J c D D⟩
    let γ : Path (actualChamberBasepoint M J c C) (actualChamberBasepoint M J c D) :=
      (PathConnectedSpace.somePath x y).map continuous_subtype_val
    have hγ : ∀ t, γ t ∈ actualTubeSet M J D :=
      fun t => (PathConnectedSpace.somePath x y t).property
    let δ := (γ.map (actualQuotientComplementMap M J q).continuous).cast (hc C) (hc D)
    have hδ : ∀ t, δ t ∈ actualTubeSet M J (q • D) := by
      intro t
      exact (quotient_mem_actualTubeSet_iff M J q D (γ t)).2 (hγ t)
    change HEq ((actualIntervalForwardOfPoints M J c).map
      ((intervalAction M J q).map (intervalPositive C D)))
      ((FundamentalGroupoid.map (actualQuotientComplementMap M J q)).map
        ((actualIntervalForwardOfPoints M J c).map (intervalPositive C D)))
    rw [intervalAction_positive]
    change HEq ((actualIntervalForwardOfPoints M J c).map (intervalPositive (q • C) (q • D)))
      ((FundamentalGroupoid.map (actualQuotientComplementMap M J q)).map
        ((actualIntervalForwardOfPoints M J c).map (intervalPositive C D)))
    have hleft := actualIntervalForwardOfPoints_positive_eq_path M J c (q • C) (q • D) δ hδ
    have hright := congrArg
      (fun f : FundamentalGroupoid.mk (actualChamberBasepoint M J c C) ⟶
          FundamentalGroupoid.mk (actualChamberBasepoint M J c D) =>
        (FundamentalGroupoid.map (actualQuotientComplementMap M J q)).map f)
      (actualIntervalForwardOfPoints_positive_eq_path M J c C D γ hγ)
    have hpaths : HEq (Path.Homotopic.Quotient.mk δ)
        ((Path.Homotopic.Quotient.mk γ).map (actualQuotientComplementMap M J q)) := by
      rw [← Path.Homotopic.Quotient.mk_map]
      exact Path.Homotopic.hpath_hext (fun _ => rfl)
    exact (heq_of_eq hleft).trans (hpaths.trans (heq_of_eq hright).symm)

/-- It suffices to prove the actual coordinate covariance of the chamber points. -/
theorem actualIntervalForwardOfPoints_equivariant_of_coordinates
    (c : ChamberPointFamily (E := relativeSubspace J) (actualForms M J))
    (q : Artin.coxeterNormalizerQuotient M J)
    (hc : ∀ C, (c (q • C)).val = quotientRepresentation M J q (c C).val) :
    intervalAction M J q ⋙ actualIntervalForwardOfPoints M J c =
      actualIntervalForwardOfPoints M J c ⋙
        FundamentalGroupoid.map (actualQuotientComplementMap M J q) :=
  actualIntervalForwardOfPoints_equivariant M J c q
    (actualChamberBasepoint_smul_of_coordinates M J c q hc)

/-- The proved interval/complement equivalence transported to the original space. -/
noncomputable def actualIntervalComplementEquivalenceOfPoints [Finite M.Group]
    (c : ChamberPointFamily (E := relativeSubspace J) (actualForms M J)) :
    IntervalGroupoid (E := relativeSubspace J) (actualForms M J) ≌
      FundamentalGroupoid (Complement M J) :=
  (intervalComplementEquivalence c).trans
    (FundamentalGroupoidFunctor.equivOfHomotopyEquiv
      (actualComplementHomeomorph M J).symm.toHomotopyEquiv)

@[simp] theorem actualIntervalComplementEquivalenceOfPoints_functor [Finite M.Group]
    (c : ChamberPointFamily (E := relativeSubspace J) (actualForms M J)) :
    (actualIntervalComplementEquivalenceOfPoints M J c).functor =
      actualIntervalForwardOfPoints M J c := rfl

noncomputable instance actualIntervalForwardOfPoints_isEquivalence [Finite M.Group]
    (c : ChamberPointFamily (E := relativeSubspace J) (actualForms M J)) :
    (actualIntervalForwardOfPoints M J c).IsEquivalence :=
  (actualIntervalComplementEquivalenceOfPoints M J c).isEquivalence_functor

variable [Finite M.Group]

/-- The canonical actual interval-to-complement functor, with no point-choice premise. -/
noncomputable def actualIntervalForward :
    IntervalGroupoid (E := relativeSubspace J) (actualForms M J) ⥤
      FundamentalGroupoid (Complement M J) :=
  actualIntervalForwardOfPoints M J (actualChamberPointFamily M J)

@[simp] theorem actualIntervalForward_obj (C : ActualChamber M J) :
    (actualIntervalForward M J).obj (intervalObject C) =
      FundamentalGroupoid.mk
        (actualChamberBasepoint M J (actualChamberPointFamily M J) C) := rfl

/-- Strict equivariance is derived from the proved canonical point covariance
and actual path classes in covariant tubes. -/
theorem actualIntervalForward_equivariant (q : Artin.coxeterNormalizerQuotient M J) :
    intervalAction M J q ⋙ actualIntervalForward M J =
      actualIntervalForward M J ⋙
        FundamentalGroupoid.map (actualQuotientComplementMap M J q) :=
  actualIntervalForwardOfPoints_equivariant_of_coordinates M J (actualChamberPointFamily M J) q
    (actualChamberPointFamily_equivariant M J q)

/-- The canonical forward functor is the forward half of the actual-space equivalence. -/
noncomputable def actualIntervalComplementEquivalence :
    IntervalGroupoid (E := relativeSubspace J) (actualForms M J) ≌
      FundamentalGroupoid (Complement M J) :=
  actualIntervalComplementEquivalenceOfPoints M J (actualChamberPointFamily M J)

@[simp] theorem actualIntervalComplementEquivalence_functor :
    (actualIntervalComplementEquivalence M J).functor = actualIntervalForward M J := rfl

noncomputable instance actualIntervalForward_isEquivalence :
    (actualIntervalForward M J).IsEquivalence :=
  (actualIntervalComplementEquivalence M J).isEquivalence_functor

end ArtinNormalisers.Chamber3
