module

public import ArtinChambers.ForwardEquivariance
public import ArtinChambers.CoveringGroupoid

/-!
# The actual normalizer action and the orbit fundamental-groupoid map

The functors below come from the continuous action on the original relative
complement. Its actual orbit projection is invariant, surjective on points,
and has precisely the normalizer-quotient orbits as its object fibers.
No equivalence of quotient groupoids is assumed in these statements.
-/

@[expose] public section

namespace ArtinNormalisers.Chamber3

open CategoryTheory Theorem18

variable {I : Type*} (M : CoxeterMatrix I) (J : Set I)

/-- The actual continuous quotient action induces a functor on actual path classes. -/
noncomputable def actualSpaceAction (q : Artin.coxeterNormalizerQuotient M J) :
    FundamentalGroupoid (Complement M J) ⥤ FundamentalGroupoid (Complement M J) :=
  FundamentalGroupoid.map (actualQuotientComplementMap M J q)

@[simp] theorem actualSpaceAction_obj (q : Artin.coxeterNormalizerQuotient M J)
    (X : FundamentalGroupoid (Complement M J)) :
    (actualSpaceAction M J q).obj X = FundamentalGroupoid.mk (q • X.as) := rfl

@[simp] theorem actualSpaceAction_one : actualSpaceAction M J 1 = 𝟭 _ := by
  have hm : actualQuotientComplementMap M J 1 = ContinuousMap.id (Complement M J) := by
    ext p
    exact one_smul _ p
  unfold actualSpaceAction
  rw [hm, FundamentalGroupoid.map_id]

/-- A left action acts first by `r`, then by `q`, in categorical composition. -/
theorem actualSpaceAction_mul (q r : Artin.coxeterNormalizerQuotient M J) :
    actualSpaceAction M J (q * r) = actualSpaceAction M J r ⋙ actualSpaceAction M J q := by
  unfold actualSpaceAction
  rw [← FundamentalGroupoid.map_comp]
  congr 1
  ext p
  exact mul_smul q r p

/-- The actual orbit map is constant on each actual normalizer-quotient orbit. -/
@[simp] theorem orbitProjection_smul (q : Artin.coxeterNormalizerQuotient M J)
    (p : Complement M J) : orbitProjection M J (q • p) = orbitProjection M J p := by
  apply Quotient.sound
  exact MulAction.orbitRel_apply.2 (MulAction.mem_orbit_iff.2 ⟨q, rfl⟩)

/-- Strict invariance of the actual orbit functor on points and path classes. -/
theorem actualSpaceAction_comp_orbit (q : Artin.coxeterNormalizerQuotient M J) :
    actualSpaceAction M J q ⋙ orbitFundamentalGroupoidFunctor M J =
      orbitFundamentalGroupoidFunctor M J := by
  unfold actualSpaceAction orbitFundamentalGroupoidFunctor
  rw [← FundamentalGroupoid.map_comp]
  congr 1
  ext p
  exact orbitProjection_smul M J q p

/-- Every actual orbit-space point is the image of an actual complement point. -/
theorem orbitFundamentalGroupoidFunctor_obj_surjective :
    Function.Surjective (orbitFundamentalGroupoidFunctor M J).obj := by
  rintro ⟨y⟩
  obtain ⟨p, hp⟩ := Quotient.exists_rep y
  refine ⟨FundamentalGroupoid.mk p, ?_⟩
  exact congrArg (fun z : OrbitSpace M J => FundamentalGroupoid.mk z) hp

/-- Object fibers of the actual orbit functor are exactly actual action orbits. -/
theorem orbitFundamentalGroupoidFunctor_obj_eq_iff
    (X Y : FundamentalGroupoid (Complement M J)) :
    (orbitFundamentalGroupoidFunctor M J).obj X =
      (orbitFundamentalGroupoidFunctor M J).obj Y ↔
      ∃ q : Artin.coxeterNormalizerQuotient M J, (actualSpaceAction M J q).obj X = Y := by
  constructor
  · intro h
    have hp : orbitProjection M J X.as = orbitProjection M J Y.as :=
      congrArg FundamentalGroupoid.as h
    have hr : MulAction.orbitRel (Artin.coxeterNormalizerQuotient M J)
        (Complement M J) Y.as X.as := Quotient.exact hp.symm
    obtain ⟨q, hq⟩ := MulAction.mem_orbit_iff.1 (MulAction.orbitRel_apply.1 hr)
    refine ⟨q, ?_⟩
    change FundamentalGroupoid.mk (q • X.as) = Y
    rw [hq]
  · rintro ⟨q, hq⟩
    have hp : q • X.as = Y.as := congrArg FundamentalGroupoid.as hq
    change FundamentalGroupoid.mk (orbitProjection M J X.as) =
      FundamentalGroupoid.mk (orbitProjection M J Y.as)
    rw [← hp, orbitProjection_smul]

/-- Distinct realized chambers have distinct chosen actual real basepoints. -/
theorem actualIntervalForwardOfPoints_obj_injective
    (c : ChamberPointFamily (E := relativeSubspace J) (actualForms M J)) :
    Function.Injective (actualIntervalForwardOfPoints M J c).obj := by
  intro X Y h
  rw [← intervalObject_intervalChamber X, ← intervalObject_intervalChamber Y] at h ⊢
  have hp := congrArg (fun z : FundamentalGroupoid (Complement M J) => z.as.val.1) h
  change (c (intervalChamber X)).val = (c (intervalChamber Y)).val at hp
  apply congrArg intervalObject
  apply Chamber.eq_of_mem_region (c (intervalChamber X)).property
  rw [hp]
  exact (c (intervalChamber Y)).property

/-- In particular, the canonical actual geometric equivalence is object-injective. -/
theorem actualIntervalForward_obj_injective [Finite M.Group] :
    Function.Injective (actualIntervalForward M J).obj :=
  actualIntervalForwardOfPoints_obj_injective M J (actualChamberPointFamily M J)

end ArtinNormalisers.Chamber3
