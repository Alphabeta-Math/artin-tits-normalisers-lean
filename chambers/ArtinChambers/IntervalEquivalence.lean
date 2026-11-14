module

public import ArtinChambers.IntervalForward
public import ArtinChambers.FaceProjection
public import ArtinChambers.TubeCover
public import ArtinChambers.TubeDescent
public import ArtinChamberVendor.AlgebraicTopology.FundamentalGroupoid.CoverGeneration

/-!
# The interval groupoid and the actual complement's fundamental groupoid

Actual paths in tube overlaps realize the face-interval connectors. This
constructs both inverse natural isomorphisms between the geometric forward
functor and the independently proved tube descent. The resulting equivalence
uses only finite real arrangements and actual chamber-point choices; the
adjacent-gallery, equivariant ribbon and orbit-quotient comparisons remain
separate obligations.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace ArtinNormalisers.Chamber3

open CategoryTheory

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {H : Type*} {ℓ : H → E →L[ℝ] ℝ}

namespace IntervalEquivalence

set_option backward.isDefEq.respectTransparency false in
/-- Naturality on the primitive positive generators implies naturality on
every arrow of the genuinely presented interval groupoid. -/
noncomputable def natIsoOfPositive {T : Type*} [Groupoid T]
    (F G : IntervalGroupoid ℓ ⥤ T) (η : ∀ X, F.obj X ≅ G.obj X)
    (hpos : ∀ C D, F.map (intervalPositive C D) ≫ (η (intervalObject D)).hom =
      (η (intervalObject C)).hom ≫ G.map (intervalPositive C D)) : F ≅ G := by
  refine NatIso.ofComponents η ?_
  intro X Y f
  induction f using CategoryTheory.Quotient.induction with
  | h f =>
    induction f using Quiver.FreeGroupoid.hom_rec with
    | @of_map X Y e =>
      rcases X with ⟨C⟩
      rcases Y with ⟨D⟩
      have he : e = (PUnit.unit : (⟨C⟩ : IntervalVertex ℓ) ⟶ ⟨D⟩) :=
        @Subsingleton.elim PUnit inferInstance e PUnit.unit
      subst e
      exact hpos C D
    | @inv_of_map X Y e =>
      rcases X with ⟨C⟩
      rcases Y with ⟨D⟩
      have he : e = (PUnit.unit : (⟨C⟩ : IntervalVertex ℓ) ⟶ ⟨D⟩) :=
        @Subsingleton.elim PUnit inferInstance e PUnit.unit
      subst e
      rw [(CategoryTheory.Quotient.functor (IntervalRelation (ℓ := ℓ))).map_inv]
      change F.map (inv (intervalPositive C D)) ≫ (η (intervalObject C)).hom =
        (η (intervalObject D)).hom ≫ G.map (inv (intervalPositive C D))
      simp only [CategoryTheory.Functor.map_inv]
      have hh := congrArg
        (fun k => inv (F.map (intervalPositive C D)) ≫ k ≫ inv (G.map (intervalPositive C D)))
        (hpos C D)
      simpa [Category.assoc] using hh.symm
    | id X =>
      change F.map (𝟙 _) ≫ _ = _ ≫ G.map (𝟙 _)
      simp
    | comp f g hf hg =>
      simp only [CategoryTheory.Functor.map_comp, Category.assoc]
      rw [hg, ← Category.assoc, hf]
      simp only [Category.assoc]

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

theorem classInTube_inv (D : Chamber ℓ) {p q : ComplexComplement ℓ}
    (hp : p ∈ tubeSet D) (hq : q ∈ tubeSet D) :
    inv (IntervalForward.classInTube D hp hq) = IntervalForward.classInTube D hq hp := by
  symm
  exact IsIso.eq_inv_of_hom_inv_id
    ((IntervalForward.classInTube_comp D hp hq hp).trans (IntervalForward.classInTube_self D hp))

variable [Finite H] (c : ChamberPointFamily ℓ)

set_option backward.isDefEq.respectTransparency false in
/-- Actual tube images generate every path class, so naturality on those
images suffices for a natural isomorphism on the whole fundamental groupoid. -/
noncomputable def natIsoOfTubeLocals {T : Type*} [Groupoid T]
    (F G : FundamentalGroupoid (ComplexComplement ℓ) ⥤ T)
    (η : ∀ X, F.obj X ≅ G.obj X)
    (hloc : ∀ (C : Chamber ℓ) {p q : FundamentalGroupoid (Tubes.Space C)} (f : p ⟶ q),
      F.map ((FundamentalGroupoid.map (ContinuousMap.subtypeVal (tubeSet C))).map f) ≫
          (η ((FundamentalGroupoid.map (ContinuousMap.subtypeVal (tubeSet C))).obj q)).hom =
        (η ((FundamentalGroupoid.map (ContinuousMap.subtypeVal (tubeSet C))).obj p)).hom ≫
          G.map ((FundamentalGroupoid.map (ContinuousMap.subtypeVal (tubeSet C))).map f)) :
    F ≅ G := by
  let S : Subgroupoid (FundamentalGroupoid (ComplexComplement ℓ)) :=
    { arrows := fun x y => {f | F.map f ≫ (η y).hom = (η x).hom ≫ G.map f}
      inv := by
        intro x y f hf
        simp only [Set.mem_ofPred_eq, Groupoid.inv_eq_inv] at hf ⊢
        simp only [CategoryTheory.Functor.map_inv]
        have hh := congrArg (fun k => inv (F.map f) ≫ k ≫ inv (G.map f)) hf
        simpa [Category.assoc] using hh.symm
      mul := by
        intro x y z f hf g hg
        change F.map (f ≫ g) ≫ (η z).hom = (η x).hom ≫ G.map (f ≫ g)
        change F.map f ≫ (η y).hom = (η x).hom ≫ G.map f at hf
        change F.map g ≫ (η z).hom = (η y).hom ≫ G.map g at hg
        simp only [CategoryTheory.Functor.map_comp, Category.assoc]
        rw [hg, ← Category.assoc, hf]
        simp only [Category.assoc] }
  have hU : ∀ p : ComplexComplement ℓ, ∃ C : Chamber ℓ, tubeSet C ∈ nhds p := by
    intro p
    obtain ⟨C, hp⟩ := exists_mem_tubeSet ℓ p
    exact ⟨C, (isOpen_tubeSet C).mem_nhds hp⟩
  have hS : S = ⊤ := by
    rw [eq_top_iff, ← TauCeti.FundamentalGroupoid.iSup_im_map_subtypeVal_eq_top hU]
    refine iSup_le fun C => ?_
    rw [Subgroupoid.im, Subgroupoid.map_le_iff_le_comap]
    rintro ⟨p, q, f⟩ _
    exact hloc C f
  refine NatIso.ofComponents η ?_
  intro x y f
  have hf : f ∈ S.arrows x y := by rw [hS]; trivial
  exact hf

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
theorem face_basepoint_same_piece {p : ComplexComplement ℓ} {C D : Chamber ℓ}
    (hpC : p ∈ tubeSet C) (hpD : p ∈ tubeSet D) :
    let B := faceChamber ℓ p.val.1 C
    p ∈ tubeIntersectionPiece ({C, D} : Set (Chamber ℓ)) B.signs ∧
      chamberBasepoint c B ∈ tubeIntersectionPiece ({C, D} : Set (Chamber ℓ)) B.signs := by
  classical
  dsimp only
  have hpI : p ∈ tubeIntersection ({C, D} : Set (Chamber ℓ)) := by
    intro A hA
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with rfl | rfl
    · exact hpC
    · exact hpD
  constructor
  · refine ⟨hpI, fun h hd => ?_⟩
    have hn := tubeIntersection_real_ne_zero hpI hd
    rw [faceChamber_signs_nonzero ℓ p.val.1 C hn]
    by_cases hs : 0 < ℓ h p.val.1
    · simp [signHalfSpace, hs]
    · have hneg : ℓ h p.val.1 < 0 := lt_of_le_of_ne (le_of_not_gt hs) hn
      simpa [signHalfSpace, hs] using hneg
  · refine ⟨fun A _ => chamberBasepoint_mem_tubeSet c _ A, fun h _ => ?_⟩
    exact (c _).property h

/-- Actual overlap path classes agree with the image of the face connector.
The intermediate real point is connected to the given complex point inside
the literal overlap sign piece, whose contractibility was already proved. -/
theorem forward_faceIntervalConnector {p : ComplexComplement ℓ} {C D : Chamber ℓ}
    (hpC : p ∈ tubeSet C) (hpD : p ∈ tubeSet D) :
    (intervalForward c).map (faceIntervalConnector ℓ p.val.1 C D) =
      IntervalForward.classInTube C (chamberBasepoint_mem_tubeSet c C C) hpC ≫
        IntervalForward.classInTube D hpD (chamberBasepoint_mem_tubeSet c D D) := by
  let B := faceChamber ℓ p.val.1 C
  obtain ⟨hp, hB⟩ := face_basepoint_same_piece c hpC hpD
  have hfamily : ({C, D} : Set (Chamber ℓ)).Nonempty := ⟨C, by simp⟩
  have hconn := isPathConnected_tubeIntersectionPiece hfamily ⟨p, hp⟩
  obtain ⟨γ, hγ⟩ := hconn.joinedIn _ hB _ hp
  have hγC : ∀ t, γ t ∈ tubeSet C := fun t => (hγ t).1 C (by simp)
  have hγD : ∀ t, γ t ∈ tubeSet D := fun t => (hγ t).1 D (by simp)
  have hα :
      IntervalForward.classInTube C (chamberBasepoint_mem_tubeSet c B C) hpC =
        IntervalForward.classInTube D (chamberBasepoint_mem_tubeSet c B D) hpD :=
    (IntervalForward.classInTube_eq_path C _ _ γ hγC).trans
      (IntervalForward.classInTube_eq_path D _ _ γ hγD).symm
  have hC : IntervalForward.positiveClass c B C =
      IntervalForward.classInTube C (chamberBasepoint_mem_tubeSet c B C) hpC ≫
        IntervalForward.classInTube C hpC (chamberBasepoint_mem_tubeSet c C C) :=
    (IntervalForward.classInTube_comp C _ _ _).symm
  have hD : IntervalForward.positiveClass c B D =
      IntervalForward.classInTube C (chamberBasepoint_mem_tubeSet c B C) hpC ≫
        IntervalForward.classInTube D hpD (chamberBasepoint_mem_tubeSet c D D) := by
    rw [hα]
    exact (IntervalForward.classInTube_comp D _ _ _).symm
  change (intervalForward c).map (inv (intervalPositive B C) ≫ intervalPositive B D) = _
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_inv,
    intervalForward_positive]
  simp [hC, hD, classInTube_inv, Category.assoc]
  simp only [← Category.assoc, IntervalForward.classInTube_comp]

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
theorem faceChamber_basepoint (C D : Chamber ℓ) :
    faceChamber ℓ (chamberBasepoint c C).val.1 D = C := by
  change faceChamber ℓ (c C).val D = C
  rw [faceChamber_eq_chamberOfRegular ℓ (c C).val D
    (C.region_subset_regularSet (c C).property)]
  exact (Chamber.eq_chamberOfRegular (c C).property).symm

omit [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] in
theorem tubeGauge_basepoint (C D : Chamber ℓ) :
    tubeGauge ℓ D (chamberBasepoint c C) =
      inv (intervalPositive C (chosenCoverChamber ℓ (chamberBasepoint c C))) ≫
        intervalPositive C D := by
  unfold tubeGauge faceIntervalConnector
  exact congrArg
    (fun B : Chamber ℓ => inv (intervalPositive B (chosenCoverChamber ℓ (chamberBasepoint c C))) ≫
      intervalPositive B D)
    (faceChamber_basepoint c C (chosenCoverChamber ℓ (chamberBasepoint c C)))

theorem descent_classInTube (C : Chamber ℓ) {p q : ComplexComplement ℓ}
    (hp : p ∈ tubeSet C) (hq : q ∈ tubeSet C) :
    (descentFunctor ℓ).map (IntervalForward.classInTube C hp hq) =
      tubeGauge ℓ C p ≫ inv (tubeGauge ℓ C q) :=
  descentFunctor_map_local ℓ C (IntervalForward.localClass C ⟨p, hp⟩ ⟨q, hq⟩)

/-- The interval-side unit, proved on the positive pair generators and
extended to every signed arrow by the actual presentation. -/
noncomputable def unitIso :
    𝟭 (IntervalGroupoid ℓ) ≅ intervalForward c ⋙ descentFunctor ℓ :=
  natIsoOfPositive _ _
    (fun X => asIso (intervalPositive (intervalChamber X)
      (chosenCoverChamber ℓ (chamberBasepoint c (intervalChamber X))))) (by
        intro C D
        change intervalPositive C D ≫
            intervalPositive D (chosenCoverChamber ℓ (chamberBasepoint c D)) =
          intervalPositive C (chosenCoverChamber ℓ (chamberBasepoint c C)) ≫
            (descentFunctor ℓ).map ((intervalForward c).map (intervalPositive C D))
        have hC := tubeGauge_basepoint c C D
        have hD := tubeGauge_basepoint c D D
        have he := congrArg₂
          (fun (a : intervalObject (chosenCoverChamber ℓ (chamberBasepoint c C)) ⟶ intervalObject D)
            (b : intervalObject (chosenCoverChamber ℓ (chamberBasepoint c D)) ⟶ intervalObject D) =>
            intervalPositive C (chosenCoverChamber ℓ (chamberBasepoint c C)) ≫ (a ≫ inv b)) hC hD
        have hP : (descentFunctor ℓ).map ((intervalForward c).map (intervalPositive C D)) =
            tubeGauge ℓ D (chamberBasepoint c C) ≫ inv (tubeGauge ℓ D (chamberBasepoint c D)) :=
          (congrArg (fun f => (descentFunctor ℓ).map f) (intervalForward_positive c C D)).trans
            (descent_classInTube D _ _)
        have hs : intervalPositive C D ≫
            intervalPositive D (chosenCoverChamber ℓ (chamberBasepoint c D)) =
          intervalPositive C (chosenCoverChamber ℓ (chamberBasepoint c C)) ≫
            (tubeGauge ℓ D (chamberBasepoint c C) ≫ inv (tubeGauge ℓ D (chamberBasepoint c D))) := by
          simpa [Category.assoc] using he.symm
        exact hs.trans
          (congrArg (fun f => intervalPositive C (chosenCoverChamber ℓ (chamberBasepoint c C)) ≫ f)
            hP.symm))

omit [Finite H] in
theorem classInTube_eq_map (C : Chamber ℓ)
    {p q : FundamentalGroupoid (Tubes.Space C)} (f : p ⟶ q) :
    IntervalForward.classInTube C p.as.property q.as.property =
      (FundamentalGroupoid.map (ContinuousMap.subtypeVal (tubeSet C))).map f := by
  dsimp only [IntervalForward.classInTube]
  exact congrArg (fun k => (FundamentalGroupoid.map (ContinuousMap.subtypeVal (tubeSet C))).map k)
    (@Subsingleton.elim (Path.Homotopic.Quotient p.as q.as) inferInstance _ _)

/-- At a complement point, the counit is the actual path class from the
selected chamber basepoint to that point inside its selected tube. -/
noncomputable def counitComponent (p : FundamentalGroupoid (ComplexComplement ℓ)) :
    (descentFunctor ℓ ⋙ intervalForward c).obj p ≅ p :=
  asIso (IntervalForward.classInTube (chosenCoverChamber ℓ p.as)
    (chamberBasepoint_mem_tubeSet c _ _) (chosenCoverChamber_mem ℓ p.as))

theorem forward_tubeGauge {p : ComplexComplement ℓ} {C : Chamber ℓ}
    (hp : p ∈ tubeSet C) :
    (intervalForward c).map (tubeGauge ℓ C p) =
      (counitComponent c (FundamentalGroupoid.mk p)).hom ≫
        IntervalForward.classInTube C hp (chamberBasepoint_mem_tubeSet c C C) :=
  forward_faceIntervalConnector c (chosenCoverChamber_mem ℓ p) hp

/-- The complement-side counit, whose naturality is proved first inside
actual tubes and then on all path classes by the proved covering generation. -/
noncomputable def counitIso :
    descentFunctor ℓ ⋙ intervalForward c ≅ 𝟭 (FundamentalGroupoid (ComplexComplement ℓ)) :=
  natIsoOfTubeLocals _ _ (counitComponent c) (by
    intro C p q f
    change (intervalForward c).map
        ((descentFunctor ℓ).map
          ((FundamentalGroupoid.map (ContinuousMap.subtypeVal (tubeSet C))).map f)) ≫
          (counitComponent c (FundamentalGroupoid.mk q.as.val)).hom =
      (counitComponent c (FundamentalGroupoid.mk p.as.val)).hom ≫
        (FundamentalGroupoid.map (ContinuousMap.subtypeVal (tubeSet C))).map f
    rw [descentFunctor_map_local]
    simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_inv]
    simp [forward_tubeGauge c p.as.property, forward_tubeGauge c q.as.property,
      classInTube_inv, Category.assoc]
    exact (IntervalForward.classInTube_comp C _ _ _).trans (classInTube_eq_map C f))

end IntervalEquivalence

variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E] [Finite H]

/-- The interval presentation is genuinely equivalent to the fundamental
groupoid of the actual complexified arrangement complement. The inverse
is the previously proved tube descent; both inverse isomorphisms above are
constructed from actual overlap path classes. -/
noncomputable def intervalComplementEquivalence (c : ChamberPointFamily ℓ) :
    IntervalGroupoid ℓ ≌ FundamentalGroupoid (ComplexComplement ℓ) :=
  CategoryTheory.Equivalence.mk (intervalForward c) (descentFunctor ℓ)
    (IntervalEquivalence.unitIso c) (IntervalEquivalence.counitIso c)

@[simp] theorem intervalComplementEquivalence_functor (c : ChamberPointFamily ℓ) :
    (intervalComplementEquivalence c).functor = intervalForward c := rfl

@[simp] theorem intervalComplementEquivalence_inverse (c : ChamberPointFamily ℓ) :
    (intervalComplementEquivalence c).inverse = descentFunctor ℓ := rfl

end ArtinNormalisers.Chamber3
