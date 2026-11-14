import ArtinSequences.StandardComparison

/-!
# The actual standard-basepoint monodromy square

An actual signed ribbon is lifted in the proved chamber covering. Its
geometric image is an actual path class in the original complement, and
the proved endpoint is the translate by the actual Coxeter quotient label.
The strictly commuting geometric square identifies its projection with
the standard vertex comparison. Covering monodromy therefore computes the
original label, with the inverse-opposite normalization kept explicit.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ArtinNormalisers.Sequence4

open CategoryTheory Chamber3 Ribbon2 Theorem18

private theorem functor_map_heq_of_eq {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (h : F = G) {X Y : C} (f : X ⟶ Y) : HEq (F.map f) (G.map f) := by
  subst G
  rfl

private theorem functor_map_heq {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {X Y X' Y' : C} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  subst X'
  subst Y'
  cases h
  rfl

private theorem hom_heq_eqToHom_conjugate {C : Type*} [Category C]
    {X Y : C} (h : X = Y) (f : X ⟶ X) : HEq f (eqToHom h.symm ≫ f ≫ eqToHom h) := by
  subst Y
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  rfl

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

private theorem componentHom_heq_of_value
    {X Y X' Y' : AssociateReducedRibbonObject M J} (hX : X = X') (hY : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (hv : f.hom.val.val = g.hom.val.val) : HEq f g := by
  subst X'
  subst Y'
  apply heq_of_eq
  apply ObjectProperty.hom_ext
  apply Subtype.ext
  exact Subtype.ext hv

/-- Positive traversal of the actual reduced loop has its original Coxeter
quotient label as raw endpoint monodromy, in the explicit opposite group. -/
theorem standardRibbonVertexEquiv_rawMonodromy
    (r : reducedRibbonLoops M (⟨J⟩ : RibbonObject M)) :
    Landmark1.orbitMonodromy M J (standardComplementPoint M J)
        (standardRibbonVertexEquiv M J (componentEndOfLoop M J r)) =
      MulOpposite.op (reducedRibbonCoxeterProjection M ⟨J⟩ r) := by
  let C0 := standardActualChamber M J
  let β := actualReducedHom M r.property
  let s := standardActualChamberFiber M J
  let D := (ribbonLiftEndpoint M J β s).val
  let δ := ribbonLiftArrow M J β s
  let e := componentEndOfLoop M J r
  let α := standardRibbonVertexEquiv M J e
  let q := reducedRibbonCoxeterProjection M ⟨J⟩ r
  let z := actualChamberBasepoint M J (actualChamberPointFamily M J) D
  let γ : Path.Homotopic.Quotient (standardComplementPoint M J) z :=
    (actualIntervalForward M J).map δ
  have htarget : (componentRibbonFunctor M J).obj (intervalObject D) =
      standardComponentRibbonObject M J := by
    apply ObjectProperty.FullSubcategory.ext
    exact (ribbonLiftSource_eq M J (ribbonLiftEndpoint M J β s)).trans
      (standardComponentRibbonObject_underlying M J).symm
  have hvalue : ((componentRibbonFunctor M J).map δ).hom.val.val = e.asHom.hom.val.val := by
    change ((intervalRibbonFunctor M J).map δ).val.val = r.val
    exact ribbonLiftArrow_ribbon_value M J β s
  have hβ : HEq ((componentRibbonFunctor M J).map δ) e.asHom :=
    componentHom_heq_of_value M J rfl htarget hvalue
  have hsq := functor_map_heq_of_eq (actualComparison_square M J) δ
  have hgeom : HEq ((orbitFundamentalGroupoidFunctor M J).map γ)
      ((actualRibbonOrbitEquivalence M J).functor.map e.asHom) :=
    hsq.symm.trans (functor_map_heq (actualRibbonOrbitEquivalence M J).functor rfl htarget hβ)
  have hloop : HEq ((actualRibbonOrbitEquivalence M J).functor.map e.asHom) α.asHom := by
    rw [standardRibbonVertexEquiv_asHom]
    exact hom_heq_eqToHom_conjugate (standardRibbonImage_eq M J) _
  have hz : z = q • standardComplementPoint M J := by
    have hD := ribbonLiftEndpoint_reducedLoop M J r
    change actualChamberBasepoint M J (actualChamberPointFamily M J) D = _
    rw [show D = q • C0 from hD]
    exact actualChamberBasepoint_smul_of_coordinates M J (actualChamberPointFamily M J) q
      (actualChamberPointFamily_equivariant M J q) C0
  exact endpointMonodromy_eq_of_path_map_heq_of_endpoint
    (Landmark1.isQuotientCoveringMap_orbitProjection M J)
    (standardComplementPoint M J) z q hz γ α (hgeom.trans hloop)

/-- The ordinary fundamental-group comparison uses the inverse ribbon
label, so its raw endpoint label is the inverse Coxeter quotient. -/
theorem standardReducedRibbonEquiv_rawMonodromy
    (r : reducedRibbonLoops M (⟨J⟩ : RibbonObject M)) :
    Landmark1.orbitMonodromy M J (standardComplementPoint M J)
        (standardReducedRibbonEquiv M J r) =
      MulOpposite.op ((reducedRibbonCoxeterProjection M ⟨J⟩ r)⁻¹) := by
  have he : reducedLoopsEquivComponentEnd M J r = componentEndOfLoop M J r⁻¹ := by
    apply componentEndValue_injective M J
    simp only [componentEndValue, reducedLoopsEquivComponentEnd_asHom_value,
      componentEndOfLoop_asHom_value, Subgroup.coe_inv]
  change Landmark1.orbitMonodromy M J (standardComplementPoint M J)
    (standardRibbonVertexEquiv M J (reducedLoopsEquivComponentEnd M J r)) = _
  rw [he, standardRibbonVertexEquiv_rawMonodromy, map_inv]

theorem standardReducedRibbonEquiv_monodromy
    (r : reducedRibbonLoops M (⟨J⟩ : RibbonObject M)) :
    normalizedOrbitMonodromy M J (standardComplementPoint M J)
        (standardReducedRibbonEquiv M J r) = reducedRibbonCoxeterProjection M ⟨J⟩ r := by
  rw [normalizedOrbitMonodromy_apply, standardReducedRibbonEquiv_rawMonodromy]
  exact inv_inv _

/-- The standard geometric comparison commutes with the original algebraic
normalizer-quotient projection, over the identity on that actual quotient. -/
theorem standardNormalizerEquiv_monodromy :
    (normalizedOrbitMonodromy M J (standardComplementPoint M J)).comp
        (standardNormalizerEquiv M J).toMonoidHom = Artin.normalizerQuotientMap M J := by
  apply MonoidHom.ext
  intro a
  obtain ⟨r, rfl⟩ := (reducedRibbonNormalizerQuotientEquiv M ⟨J⟩).surjective a
  change normalizedOrbitMonodromy M J (standardComplementPoint M J)
      (standardReducedRibbonEquiv M J
        ((reducedRibbonNormalizerQuotientEquiv M ⟨J⟩).symm
          (reducedRibbonNormalizerQuotientEquiv M ⟨J⟩ r))) = _
  rw [MulEquiv.symm_apply_apply, standardReducedRibbonEquiv_monodromy]
  exact (DFunLike.congr_fun (reducedRibbon_projection_compatible M ⟨J⟩) r).symm

/-- The raw form records the inverse-opposite convention without normalizing it. -/
theorem standardNormalizerEquiv_rawMonodromy (a : Artin.normalizerQuotient M J) :
    Landmark1.orbitMonodromy M J (standardComplementPoint M J) (standardNormalizerEquiv M J a) =
      MulOpposite.op ((Artin.normalizerQuotientMap M J a)⁻¹) := by
  obtain ⟨r, rfl⟩ := (reducedRibbonNormalizerQuotientEquiv M ⟨J⟩).surjective a
  change Landmark1.orbitMonodromy M J (standardComplementPoint M J)
      (standardReducedRibbonEquiv M J
        ((reducedRibbonNormalizerQuotientEquiv M ⟨J⟩).symm
          (reducedRibbonNormalizerQuotientEquiv M ⟨J⟩ r))) = _
  rw [MulEquiv.symm_apply_apply, standardReducedRibbonEquiv_rawMonodromy]
  congr 2
  exact (DFunLike.congr_fun (reducedRibbon_projection_compatible M ⟨J⟩) r).symm

end ArtinNormalisers.Sequence4
