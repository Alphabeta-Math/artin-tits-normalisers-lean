import ArtinChambers.ChamberTransport
import ArtinChambers.WeakIntervals
import ArtinChambers.FamilyGroupoid
import ArtinChambers.FamilyFunctor
import ArtinChambers.RibbonCover
import ArtinRibbons.RibbonUniversal
import ArtinRibbons.AtomicCoxeter

/-!
# Actual ribbon lifting through chamber families

The chamber fibers are the actual chambers with a specified standard-facet
index set. Their endpoint transport is induced by multiplication of actual
raw facet representatives by actual Coxeter parabolic transporters. No
groupoid covering or lifting uniqueness is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ArtinNormalisers.Chamber3

open CategoryTheory Ribbon2

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

/-- The literal fiber of the actual chamber index map; it can be empty. -/
abbrev ChamberFiber (X : RibbonObject M) :=
  {C : ActualChamber M J // actualChamberIndices M J C = X.indices}

omit [Finite M.Group] in
theorem rawFacetLabel_ext {L K : RawFacetLabel M J}
    (hi : L.indices = K.indices) (hr : L.representative = K.representative) : L = K := by
  cases L
  cases K
  cases hi
  cases hr
  rfl

/-- Right multiplication of a raw label by an actual parabolic transporter. -/
noncomputable def rightTransportRawLabel (L : RawFacetLabel M J) (K : Set I)
    (w : M.Group)
    (hw : (Artin.coxeterParabolic M K).map (MulAut.conj w).toMonoidHom =
      Artin.coxeterParabolic M L.indices) : RawFacetLabel M J where
  indices := K
  representative := L.representative * w
  parabolic_conjugacy := by
    have he : (MulAut.conj (L.representative * w)).toMonoidHom =
        (MulAut.conj L.representative).toMonoidHom.comp (MulAut.conj w).toMonoidHom := by
      apply MonoidHom.ext
      intro g
      change (L.representative * w) * g * (L.representative * w)⁻¹ =
        L.representative * (w * g * w⁻¹) * L.representative⁻¹
      group
    rw [he, ← Subgroup.map_map, hw, L.parabolic_conjugacy]

theorem rightTransportRawLabel_independent {L K : RawFacetLabel M J}
    (hLK : actualChamberOfRawLabel M J L = actualChamberOfRawLabel M J K)
    (T : Set I) (w : M.Group)
    (hL : (Artin.coxeterParabolic M T).map (MulAut.conj w).toMonoidHom =
      Artin.coxeterParabolic M L.indices)
    (hK : (Artin.coxeterParabolic M T).map (MulAut.conj w).toMonoidHom =
      Artin.coxeterParabolic M K.indices) :
    actualChamberOfRawLabel M J (rightTransportRawLabel M J L T w hL) =
      actualChamberOfRawLabel M J (rightTransportRawLabel M J K T w hK) := by
  obtain ⟨_, hc⟩ := (actualChamberOfRawLabel_eq_iff M J L K).mp hLK
  apply (actualChamberOfRawLabel_eq_iff M J _ _).mpr
  refine ⟨rfl, ?_⟩
  rw [← hL, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hc
  change (L.representative * w)⁻¹ * (K.representative * w) ∈ Artin.coxeterParabolic M T
  convert hc using 1
  group

omit [Finite M.Group] in
theorem transporter_comp {X Y Z : Set I} {u v : M.Group}
    (hu : (Artin.coxeterParabolic M Y).map (MulAut.conj u).toMonoidHom =
      Artin.coxeterParabolic M X)
    (hv : (Artin.coxeterParabolic M Z).map (MulAut.conj v).toMonoidHom =
      Artin.coxeterParabolic M Y) :
    (Artin.coxeterParabolic M Z).map (MulAut.conj (u * v)).toMonoidHom =
      Artin.coxeterParabolic M X := by
  have he : (MulAut.conj (u * v)).toMonoidHom =
      (MulAut.conj u).toMonoidHom.comp (MulAut.conj v).toMonoidHom := by
    apply MonoidHom.ext
    intro g
    change (u * v) * g * (u * v)⁻¹ = u * (v * g * v⁻¹) * u⁻¹
    group
  rw [he, ← Subgroup.map_map, hv, hu]

/-- An actual target raw label, from the proved source index equality. -/
noncomputable def fiberTargetLabel {X Y : RibbonObject M} (w : M.Group)
    (hw : (Artin.coxeterParabolic M Y.indices).map (MulAut.conj w).toMonoidHom =
      Artin.coxeterParabolic M X.indices) (C : ChamberFiber M J X) : RawFacetLabel M J :=
  rightTransportRawLabel M J (chamberRawLabel M J C.val) Y.indices w
    (by simpa only [chamberRawLabel_indices, C.property] using hw)

/-- Actual geometric endpoint transport on chamber fibers. -/
noncomputable def fiberTarget {X Y : RibbonObject M} (w : M.Group)
    (hw : (Artin.coxeterParabolic M Y.indices).map (MulAut.conj w).toMonoidHom =
      Artin.coxeterParabolic M X.indices) (C : ChamberFiber M J X) : ChamberFiber M J Y :=
  ⟨actualChamberOfRawLabel M J (fiberTargetLabel M J w hw C),
    actualChamberIndices_rawLabel M J _⟩

theorem fiberTarget_one {X : RibbonObject M}
    (h1 : (Artin.coxeterParabolic M X.indices).map (MulAut.conj (1 : M.Group)).toMonoidHom =
      Artin.coxeterParabolic M X.indices) (C : ChamberFiber M J X) :
    fiberTarget M J 1 h1 C = C := by
  apply Subtype.ext
  have he : fiberTargetLabel M J 1 h1 C = chamberRawLabel M J C.val := by
    apply rawFacetLabel_ext M J
    · exact C.property.symm
    · dsimp [fiberTargetLabel, rightTransportRawLabel]
      exact mul_one _
  change actualChamberOfRawLabel M J (fiberTargetLabel M J 1 h1 C) = C.val
  rw [he, chamberRawLabel_chamber]

theorem fiberTarget_comp {X Y Z : RibbonObject M} (u v : M.Group)
    (hu : (Artin.coxeterParabolic M Y.indices).map (MulAut.conj u).toMonoidHom =
      Artin.coxeterParabolic M X.indices)
    (hv : (Artin.coxeterParabolic M Z.indices).map (MulAut.conj v).toMonoidHom =
      Artin.coxeterParabolic M Y.indices) (C : ChamberFiber M J X) :
    fiberTarget M J v hv (fiberTarget M J u hu C) =
      fiberTarget M J (u * v) (transporter_comp M hu hv) C := by
  apply Subtype.ext
  let L := fiberTargetLabel M J u hu C
  have hchosen : actualChamberOfRawLabel M J
      (chamberRawLabel M J (fiberTarget M J u hu C).val) = actualChamberOfRawLabel M J L :=
    chamberRawLabel_chamber M J _
  have he := rightTransportRawLabel_independent M J hchosen Z.indices v
    (by simpa only [chamberRawLabel_indices, (fiberTarget M J u hu C).property] using hv) hv
  change actualChamberOfRawLabel M J (fiberTargetLabel M J v hv (fiberTarget M J u hu C)) = _
  refine he.trans ?_
  congr 1
  apply rawFacetLabel_ext M J
  · rfl
  · dsimp [L, fiberTargetLabel, rightTransportRawLabel]
    group

/-- The fiber index bijection of an actual Coxeter transporter, with inverse
given by its actual inverse and the proved reverse parabolic conjugacy. -/
noncomputable def fiberEquiv {X Y : RibbonObject M} (w : M.Group)
    (hw : (Artin.coxeterParabolic M Y.indices).map (MulAut.conj w).toMonoidHom =
      Artin.coxeterParabolic M X.indices) : ChamberFiber M J X ≃ ChamberFiber M J Y where
  toFun := fiberTarget M J w hw
  invFun := fiberTarget M J w⁻¹ (conjugacy_symm M hw)
  left_inv C := by
    rw [fiberTarget_comp]
    simpa only [mul_inv_cancel] using fiberTarget_one M J _ C
  right_inv C := by
    rw [fiberTarget_comp]
    simpa only [inv_mul_cancel] using fiberTarget_one M J _ C

theorem relativeTransport_fiberTarget {X Y : RibbonObject M} (w : M.Group)
    (hw : (Artin.coxeterParabolic M Y.indices).map (MulAut.conj w).toMonoidHom =
      Artin.coxeterParabolic M X.indices)
    (hmin : M.toCoxeterSystem.IsMinimalCosetRep Y.indices w) (C : ChamberFiber M J X) :
    relativeTransport M J C.val (fiberTarget M J w hw C).val = w := by
  let L := chamberRawLabel M J C.val
  change relativeTransport M J C.val (actualChamberOfRawLabel M J (fiberTargetLabel M J w hw C)) = w
  calc
    _ = relativeTransport M J (actualChamberOfRawLabel M J L)
        (actualChamberOfRawLabel M J (fiberTargetLabel M J w hw C)) := by
      rw [chamberRawLabel_chamber]
    _ = rawRelativeTransport M L (fiberTargetLabel M J w hw C) := relativeTransport_eq_raw M J _ _
    _ = M.toCoxeterSystem.minimalCosetRep Y.indices w := by
      change M.toCoxeterSystem.minimalCosetRep Y.indices
        (L.representative⁻¹ * (L.representative * w)) = _
      rw [inv_mul_cancel_left]
    _ = w := hmin.minimalCosetRep_eq _

open OAI.HarmonicArtin

/-- Actual positive factors of an actual simple positive lift are simple
positive lifts themselves. This uses the proved positive embedding. -/
theorem actual_simple_factors {a b : Artin.Group M} {d : M.Group}
    (ha : a ∈ actualPositiveParabolic M Set.univ)
    (hb : b ∈ actualPositiveParabolic M Set.univ)
    (hab : a * b = transporterPositiveLift M d) :
    a = transporterPositiveLift M (Artin.projection M a) ∧
      b = transporterPositiveLift M (Artin.projection M b) := by
  classical
  let := fundamental_finite_index M
  let := Fintype.ofFinite I
  rw [← positiveToParent_mrange_eq_actual] at ha hb
  obtain ⟨ap, hap⟩ := ha
  obtain ⟨bp, hbp⟩ := hb
  have he : ap * bp = positiveSimpleLift M d := by
    apply positiveToParent_injective M
    rw [map_mul, hap, hbp]
    exact hab
  obtain ⟨hA, hB⟩ := positive_simple_factors M ap bp d he
  have hprojA : positiveToCoxeter M ap = Artin.projection M a := by
    rw [← hap, projection_positiveToParent]
  have hprojB : positiveToCoxeter M bp = Artin.projection M b := by
    rw [← hbp, projection_positiveToParent]
  constructor
  · exact hap.symm.trans ((congrArg (positiveToParent M) hA).trans
      (congrArg (transporterPositiveLift M) hprojA))
  · exact hbp.symm.trans ((congrArg (positiveToParent M) hB).trans
      (congrArg (transporterPositiveLift M) hprojB))

theorem actual_simple_factors_length {a b : Artin.Group M} {d : M.Group}
    (ha : a ∈ actualPositiveParabolic M Set.univ)
    (hb : b ∈ actualPositiveParabolic M Set.univ)
    (hab : a * b = transporterPositiveLift M d) :
    M.toCoxeterSystem.length (Artin.projection M (a * b)) =
      M.toCoxeterSystem.length (Artin.projection M a) +
        M.toCoxeterSystem.length (Artin.projection M b) := by
  obtain ⟨hA, hB⟩ := actual_simple_factors M ha hb hab
  have hdeg := degree_mul M a b
  rw [degree_eq_coxeterLength_of_simple M ⟨d, hab⟩,
    degree_eq_coxeterLength_of_simple M ⟨_, hA⟩,
    degree_eq_coxeterLength_of_simple M ⟨_, hB⟩] at hdeg
  exact_mod_cast hdeg

theorem simple_reduced_projection_minimal {X Y : RibbonObject M} {β : Artin.Group M}
    (hβ : IsRibbon M X Y β) (hred : IsLeftParabolicallyReduced M X.indices β)
    (hs : β = transporterPositiveLift M (Artin.projection M β)) :
    M.toCoxeterSystem.IsMinimalCosetRep Y.indices (Artin.projection M β) := by
  have hinv : M.toCoxeterSystem.IsMinimalCosetRep X.indices (Artin.projection M β)⁻¹ := by
    apply transporterPositiveLift_inv_minimal_of_leftReduced M
    rw [← hs]
    exact hred
  have hproj := isRibbon_projection_transporter M hβ
  have hproj' : (M.toCoxeterSystem.parabolic Y.indices).map
      (MulAut.conj (Artin.projection M β)).toMonoidHom =
        M.toCoxeterSystem.parabolic X.indices := by
    simpa only [Artin.coxeterParabolic_eq] using hproj
  simpa only [inv_inv] using minimal_inv_of_parabolic_transporter M.toCoxeterSystem
    (inverse_parabolic_transporter M.toCoxeterSystem hproj') hinv

/-- Families are actual chamber fibers, including genuinely empty fibers
for objects not associated with the fixed ambient parabolic. -/
noncomputable def ribbonChamberFamily (X : RibbonObject M) :
    FamilyGroupoid (IntervalGroupoid (E := Theorem18.relativeSubspace J) (actualForms M J)) :=
  FamilyGroupoid.of (ChamberFiber M J X) (fun C => intervalObject C.val)

/-- A positive pair coordinate arrow over a genuine transporter bijection.
No multiplicativity is asserted without its geometric interval condition. -/
noncomputable def positiveFiberHom {X Y : RibbonObject M} (w : M.Group)
    (hw : (Artin.coxeterParabolic M Y.indices).map (MulAut.conj w).toMonoidHom =
      Artin.coxeterParabolic M X.indices) : ribbonChamberFamily M J X ⟶ ribbonChamberFamily M J Y where
  equiv := fiberEquiv M J w hw
  hom C := intervalPositive C.val (fiberTarget M J w hw C).val

noncomputable def atomicFiberHom (X : RibbonObject M) (a : I) (_ha : a ∉ X.indices) :
    ribbonChamberFamily M J X ⟶ ribbonChamberFamily M J (atomicNext M X a) :=
  positiveFiberHom M J (Artin.projection M (elementaryMu M X.indices a))
    (isRibbon_projection_transporter M (elementaryMu_isRibbon M X.indices a))

noncomputable def ribbonLiftingData :
    RibbonGeneratorData M (FamilyGroupoid (IntervalGroupoid (E := Theorem18.relativeSubspace J) (actualForms M J))) where
  obj := ribbonChamberFamily M J
  atom := atomicFiberHom M J

omit [Finite M.Group] in
private theorem intervalPositive_heq {C D C' D' : ActualChamber M J}
    (hC : C = C') (hD : D = D') : HEq (intervalPositive C D) (intervalPositive C' D') := by
  cases hC
  cases hD
  rfl

omit [Finite M.Group] in
private theorem intervalPositive_comp_heq {C D E E' : ActualChamber M J}
    (hE : E = E') :
    HEq (intervalPositive C D ≫ intervalPositive D E)
      (intervalPositive C D ≫ intervalPositive D E') := by
  cases hE
  rfl

theorem positiveFiberHom_one (X : RibbonObject M)
    (hw : (Artin.coxeterParabolic M X.indices).map (MulAut.conj (1 : M.Group)).toMonoidHom =
      Artin.coxeterParabolic M X.indices) :
    positiveFiberHom M J 1 hw = 𝟙 (ribbonChamberFamily M J X) := by
  apply FamilyGroupoid.Hom.ext
  · apply Equiv.ext
    intro C
    exact fiberTarget_one M J hw C
  · intro C
    change HEq (intervalPositive C.val (fiberTarget M J 1 hw C).val) (𝟙 (intervalObject C.val))
    exact (intervalPositive_heq M J rfl (congrArg Subtype.val (fiberTarget_one M J hw C))).trans
      (heq_of_eq (intervalPositive_self C.val))

theorem positiveFiberHom_comp {X Y Z : RibbonObject M} (u v : M.Group)
    (hu : (Artin.coxeterParabolic M Y.indices).map (MulAut.conj u).toMonoidHom =
      Artin.coxeterParabolic M X.indices)
    (hv : (Artin.coxeterParabolic M Z.indices).map (MulAut.conj v).toMonoidHom =
      Artin.coxeterParabolic M Y.indices)
    (hb : ∀ C : ChamberFiber M J X,
      ChamberBetween C.val (fiberTarget M J u hu C).val
        (fiberTarget M J (u * v) (transporter_comp M hu hv) C).val) :
    positiveFiberHom M J (u * v) (transporter_comp M hu hv) =
      positiveFiberHom M J u hu ≫ positiveFiberHom M J v hv := by
  apply FamilyGroupoid.Hom.ext
  · apply Equiv.ext
    intro C
    exact (fiberTarget_comp M J u v hu hv C).symm
  · intro C
    change HEq (intervalPositive C.val (fiberTarget M J (u * v) (transporter_comp M hu hv) C).val)
      (intervalPositive C.val (fiberTarget M J u hu C).val ≫
        intervalPositive (fiberTarget M J u hu C).val
          (fiberTarget M J v hv (fiberTarget M J u hu C)).val)
    exact (heq_of_eq (intervalPositive_comp _ _ _ (hb C))).trans
      (intervalPositive_comp_heq M J (congrArg Subtype.val (fiberTarget_comp M J u v hu hv C).symm))

/-- Each actual atomic word evaluating to a simple lift acts by one
positive interval arrow at every chamber in its actual source fiber. -/
theorem lifting_wordImage_of_simple {X Y : RibbonObject M} (p : AtomicWord M X Y)
    (hs : ∃ d : M.Group, p.eval = transporterPositiveLift M d) :
    (ribbonLiftingData M J).wordImage p =
      positiveFiberHom M J (Artin.projection M p.eval) (isRibbon_projection_transporter M p.isRibbon) := by
  induction p with
  | nil X =>
    symm
    exact positiveFiberHom_one M J X _
  | @cons X Y a ha p ih =>
    obtain ⟨d, hd⟩ := hs
    have hμpos : elementaryMu M X.indices a ∈ actualPositiveParabolic M Set.univ :=
      Submonoid.closure_mono (Set.image_mono (Set.subset_univ (insert a X.indices)))
        (elementaryMu_positive M X.indices a)
    have htotal : elementaryMu M X.indices a * p.eval = transporterPositiveLift M d := hd
    obtain ⟨hμ, hp⟩ := actual_simple_factors M hμpos p.positive htotal
    have hlen := actual_simple_factors_length M hμpos p.positive htotal
    have hcan : (AtomicWord.cons a ha p).eval =
        transporterPositiveLift M (Artin.projection M (AtomicWord.cons a ha p).eval) := by
      rw [hd, projection_transporterPositiveLift]
    have htotalmin := simple_reduced_projection_minimal M
      (AtomicWord.cons a ha p).isRibbon (AtomicWord.cons a ha p).leftReduced hcan
    have hμmin := elementaryMu_projection_minimal M X.indices a
    have hbet : ∀ C : ChamberFiber M J X,
        ChamberBetween C.val
          (fiberTarget M J (Artin.projection M (elementaryMu M X.indices a))
            (isRibbon_projection_transporter M (elementaryMu_isRibbon M X.indices a)) C).val
          (fiberTarget M J
            (Artin.projection M (elementaryMu M X.indices a) * Artin.projection M p.eval)
            (transporter_comp M
              (isRibbon_projection_transporter M (elementaryMu_isRibbon M X.indices a))
              (isRibbon_projection_transporter M p.isRibbon)) C).val := by
      intro C
      apply (chamberBetween_iff_relativeTransport_length M J _ _ _).mpr
      rw [relativeTransport_fiberTarget M J _ _ hμmin,
        relativeTransport_fiberTarget M J _ _ (by simpa only [AtomicWord.eval_cons, map_mul] using htotalmin)]
      simpa only [map_mul, inv_mul_cancel_left] using hlen
    rw [RibbonGeneratorData.wordImage_cons, ih ⟨_, hp⟩]
    symm
    change positiveFiberHom M J (Artin.projection M (elementaryMu M X.indices a * p.eval)) _ =
      positiveFiberHom M J (Artin.projection M (elementaryMu M X.indices a)) _ ≫
        positiveFiberHom M J (Artin.projection M p.eval) _
    simpa only [map_mul] using positiveFiberHom_comp M J
      (Artin.projection M (elementaryMu M X.indices a)) (Artin.projection M p.eval)
      (isRibbon_projection_transporter M (elementaryMu_isRibbon M X.indices a))
      (isRibbon_projection_transporter M p.isRibbon) hbet

/-- Only the fixed chosen pair-lcm relations are checked. Their two
actual simple total evaluations give the same lifted positive intervals. -/
theorem ribbonLiftingData_respects : (ribbonLiftingData M J).RespectsLcm := by
  intro X a b ha hb hab
  let p := AtomicWord.cons a ha (chosenLcmLeftTail M X a b ha hb hab)
  let q := AtomicWord.cons b hb (chosenLcmRightTail M X a b ha hb hab)
  have hp : p.eval = pairRibbonLcm M X.indices a b := by
    exact chosenLcmLeft_eval M X a b ha hb hab
  have hq : q.eval = pairRibbonLcm M X.indices a b := by
    exact chosenLcmRight_eval M X a b ha hb hab
  have hs : pairRibbonLcm M X.indices a b = transporterPositiveLift M
      ((parabolicLongest M X.indices)⁻¹ * parabolicLongest M (insert b (insert a X.indices))) :=
    parabolicDelta_ratio_eq_simpleLift M X.indices (insert b (insert a X.indices))
      (fun _ h => Set.mem_insert_of_mem b (Set.mem_insert_of_mem a h))
  change (ribbonLiftingData M J).wordImage p = (ribbonLiftingData M J).wordImage q
  rw [lifting_wordImage_of_simple M J p ⟨_, hp.trans hs⟩,
    lifting_wordImage_of_simple M J q ⟨_, hq.trans hs⟩]
  congr 1
  exact congrArg (Artin.projection M) (hp.trans hq.symm)

/-- The actual signed ribbon functor to the groupoid of actual chamber
families, constructed from the proved chosen-lcm relations. -/
noncomputable def ribbonLiftingFunctor : ActualReducedRibbonGroupoid M ⥤
    FamilyGroupoid (IntervalGroupoid (E := Theorem18.relativeSubspace J) (actualForms M J)) :=
  (ribbonLiftingData M J).extensionFunctor (ribbonLiftingData_respects M J)

@[simp] theorem ribbonLiftingFunctor_obj (X : ActualReducedRibbonGroupoid M) :
    (ribbonLiftingFunctor M J).obj X = ribbonChamberFamily M J X.val := rfl

theorem ribbonLiftingFunctor_atom (X : RibbonObject M) (a : I) (ha : a ∉ X.indices) :
    (ribbonLiftingFunctor M J).map (actualAtomicHom M X a ha) = atomicFiberHom M J X a ha :=
  (ribbonLiftingData M J).extensionFunctor_atom (ribbonLiftingData_respects M J) X a ha

theorem ribbonLiftingFunctor_word {X Y : RibbonObject M} (p : AtomicWord M X Y) :
    (ribbonLiftingFunctor M J).map (actualReducedHom M p.toPositiveReducedArrow.toReducedArrow) =
      (ribbonLiftingData M J).wordImage p :=
  (ribbonLiftingData M J).extensionFunctor_word (ribbonLiftingData_respects M J) p

/-- The endpoint and actual coordinate arrow of the constructed signed lift. -/
noncomputable def ribbonLiftEndpoint {X Y : ActualReducedRibbonGroupoid M} (β : X ⟶ Y)
    (C : ChamberFiber M J X.val) : ChamberFiber M J Y.val :=
  ((ribbonLiftingFunctor M J).map β).equiv C

noncomputable def ribbonLiftArrow {X Y : ActualReducedRibbonGroupoid M} (β : X ⟶ Y)
    (C : ChamberFiber M J X.val) :
    intervalObject C.val ⟶ intervalObject (ribbonLiftEndpoint M J β C).val :=
  ((ribbonLiftingFunctor M J).map β).hom C

theorem ribbonLiftingFunctor_positive_simple {X Y : RibbonObject M} {β : Artin.Group M}
    (hp : PositiveReducedArrow M X Y β)
    (hs : ∃ d : M.Group, β = transporterPositiveLift M d) :
    (ribbonLiftingFunctor M J).map (actualReducedHom M hp.toReducedArrow) =
      positiveFiberHom M J (Artin.projection M β) (isRibbon_projection_transporter M hp.isRibbon) := by
  let p := hp.atomicWord M
  have he : actualReducedHom M hp.toReducedArrow =
      actualReducedHom M p.toPositiveReducedArrow.toReducedArrow := by
    apply Subtype.ext
    apply Subtype.ext
    exact (hp.atomicWord_eval M).symm
  rw [he, ribbonLiftingFunctor_word]
  have hsimple : ∃ d : M.Group, p.eval = transporterPositiveLift M d := by
    simpa only [p, hp.atomicWord_eval M] using hs
  have h := lifting_wordImage_of_simple M J p hsimple
  simpa only [p, hp.atomicWord_eval M] using h

/-- Transport by the canonical relative element has precisely the actual
target chamber, not merely a chamber with the same index set. -/
theorem fiberTarget_relativeTransport (C D : ActualChamber M J) :
    (fiberTarget M J (X := ⟨actualChamberIndices M J C⟩) (Y := ⟨actualChamberIndices M J D⟩)
      (relativeTransport M J C D) (relativeTransport_conjugacy M J C D)
      (⟨C, rfl⟩ : ChamberFiber M J ⟨actualChamberIndices M J C⟩)).val = D := by
  let L := chamberRawLabel M J C
  let K := chamberRawLabel M J D
  have hlabel : fiberTargetLabel M J
      (X := ⟨actualChamberIndices M J C⟩) (Y := ⟨actualChamberIndices M J D⟩)
      (relativeTransport M J C D)
      (relativeTransport_conjugacy M J C D)
      (⟨C, rfl⟩ : ChamberFiber M J ⟨actualChamberIndices M J C⟩) =
        relativeTargetLabel M L K := by
    apply rawFacetLabel_ext M J
    · rfl
    · rfl
  change actualChamberOfRawLabel M J (fiberTargetLabel M J _ _ _) = D
  rw [hlabel]
  have he : actualChamberOfRawLabel M J (relativeTargetLabel M L K) =
      actualChamberOfRawLabel M J K :=
    (actualChamberOfRawLabel_eq_iff M J _ _).mpr
      ((translatedFacet_eq_iff _ _).mp (relativeTargetLabel_region M L K))
  exact he.trans (chamberRawLabel_chamber M J D)

/-- On every actual positive interval, the signed lifting functor gives
the corresponding actual relative-transporter family arrow. -/
theorem ribbonLiftingFunctor_intervalPositive (C D : ActualChamber M J) :
    (ribbonLiftingFunctor M J).map
      ((intervalRibbonFunctor M J).map (intervalPositive C D)) =
        positiveFiberHom M J (X := ⟨actualChamberIndices M J C⟩) (Y := ⟨actualChamberIndices M J D⟩)
          (relativeTransport M J C D) (relativeTransport_conjugacy M J C D) := by
  rw [intervalRibbonFunctor_positive]
  change (ribbonLiftingFunctor M J).map (actualReducedHom M
    (transporterPositiveLift_generated M (relativeTransport_conjugacy M J C D)
      (relativeTransport_minimal M J C D)).toReducedArrow) = _
  have h := ribbonLiftingFunctor_positive_simple M J
    (transporterPositiveLift_generated M (relativeTransport_conjugacy M J C D)
      (relativeTransport_minimal M J C D)) ⟨_, rfl⟩
  simpa only [projection_transporterPositiveLift] using h

theorem ribbonLiftInterval_endpoint (C D : ActualChamber M J) :
    (ribbonLiftEndpoint M J ((intervalRibbonFunctor M J).map (intervalPositive C D))
      (⟨C, rfl⟩ : ChamberFiber M J ⟨actualChamberIndices M J C⟩)).val = D := by
  have h := congrArg
    (fun (f : ribbonChamberFamily M J ⟨actualChamberIndices M J C⟩ ⟶
        ribbonChamberFamily M J ⟨actualChamberIndices M J D⟩) => (FamilyGroupoid.Hom.equiv f
      (⟨C, rfl⟩ : ChamberFiber M J ⟨actualChamberIndices M J C⟩)).val)
    (ribbonLiftingFunctor_intervalPositive M J C D)
  exact h.trans (fiberTarget_relativeTransport M J C D)

theorem ribbonLiftInterval_arrow (C D : ActualChamber M J) :
    HEq (ribbonLiftArrow M J ((intervalRibbonFunctor M J).map (intervalPositive C D))
      (⟨C, rfl⟩ : ChamberFiber M J ⟨actualChamberIndices M J C⟩)) (intervalPositive C D) := by
  have h := FamilyGroupoid.coordinate_heq_of_eq (ribbonLiftingFunctor_intervalPositive M J C D)
    (⟨C, rfl⟩ : ChamberFiber M J ⟨actualChamberIndices M J C⟩)
  exact h.trans (intervalPositive_heq M J rfl (fiberTarget_relativeTransport M J C D))

end ArtinNormalisers.Chamber3
