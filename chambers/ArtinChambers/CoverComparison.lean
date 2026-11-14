module

public import ArtinChambers.CoverQuotient

/-!
# Comparing actual quotient covers through an equivariant equivalence

The invariant composite descends by the proved cover-descent theorem. Its
fullness, faithfulness and essential surjectivity are proved using actual
arrow lifts, object fibers, and the counit of the upstairs equivalence.
The upstairs equivalence is never treated as a strict isomorphism of objects.
-/

@[expose] public section

set_option autoImplicit false

namespace ArtinNormalisers.Chamber3

open CategoryTheory

universe uQ uC vC uD vD uX vX uY vY

variable {Q : Type uQ} [Group Q]
  {C : Type uC} [Groupoid.{vC} C] {D : Type uD} [Groupoid.{vD} D]
  {X : Type uX} [Groupoid.{vX} X] {Y : Type uY} [Groupoid.{vY} Y]
  {A : StrictGroupoidAction Q C} {A' : StrictGroupoidAction Q X}
  {F : C ⥤ D} {P : X ⥤ Y}

theorem comparison_invariant (U : CoverOrbitData A' P) (E : C ≌ X)
    (hE : ∀ q, A.functor q ⋙ E.functor = E.functor ⋙ A'.functor q) (q : Q) :
    A.functor q ⋙ (E.functor ⋙ P) = E.functor ⋙ P := by
  calc
    A.functor q ⋙ (E.functor ⋙ P) = (A.functor q ⋙ E.functor) ⋙ P := rfl
    _ = (E.functor ⋙ A'.functor q) ⋙ P := by rw [hE q]
    _ = E.functor ⋙ (A'.functor q ⋙ P) := rfl
    _ = E.functor ⋙ P := by rw [U.invariant q]

/-- The actual descended comparison functor. -/
noncomputable def comparisonFunctor (S : CoverOrbitData A F) (U : CoverOrbitData A' P)
    (E : C ≌ X) (hE : ∀ q, A.functor q ⋙ E.functor = E.functor ⋙ A'.functor q) : D ⥤ Y :=
  S.desc (E.functor ⋙ P) (comparison_invariant U E hE)

variable (S : CoverOrbitData A F) (U : CoverOrbitData A' P) (E : C ≌ X)
  (hE : ∀ q, A.functor q ⋙ E.functor = E.functor ⋙ A'.functor q)

/-- The comparison square commutes by strict functor equality. -/
theorem comparison_square : F ⋙ comparisonFunctor S U E hE = E.functor ⋙ P :=
  S.desc_fac (E.functor ⋙ P) (comparison_invariant U E hE)

private theorem outgoing_injective_of_faithful_obj_injective (L : C ⥤ X) [L.Faithful]
    (hobj : Function.Injective L.obj) (c : C) : Function.Injective (mapOutgoing L c) := by
  rintro ⟨y, f⟩ ⟨z, g⟩ h
  have hyz := hobj (Sigma.mk.inj h).1
  cases hyz
  have hfg := L.map_injective (eq_of_heq (Sigma.mk.inj h).2)
  cases hfg
  rfl

private theorem comparison_outgoing_injective_at
    (hobj : Function.Injective E.functor.obj) (c : C) :
    Function.Injective (mapOutgoing (comparisonFunctor S U E hE) (F.obj c)) := by
  have hcomp : Function.Injective (mapOutgoing (F ⋙ comparisonFunctor S U E hE) c) := by
    rw [comparison_square, mapOutgoing_comp]
    exact (U.covering (E.functor.obj c)).injective.comp
      (outgoing_injective_of_faithful_obj_injective E.functor hobj c)
  intro p q hpq
  obtain ⟨p', rfl⟩ := (S.covering c).surjective p
  obtain ⟨q', rfl⟩ := (S.covering c).surjective q
  exact congrArg (mapOutgoing F c) (hcomp hpq)

theorem comparisonFunctor_faithful (hobj : Function.Injective E.functor.obj) :
    (comparisonFunctor S U E hE).Faithful := by
  let B := comparisonFunctor S U E hE
  change B.Faithful
  constructor
  intro d e f g h
  obtain ⟨c, rfl⟩ := S.obj_surjective d
  have hs : mapOutgoing B (F.obj c) ⟨e, f⟩ = mapOutgoing B (F.obj c) ⟨e, g⟩ :=
    congrArg (fun k : B.obj (F.obj c) ⟶ B.obj e =>
      (⟨B.obj e, k⟩ : Outgoing Y (B.obj (F.obj c)))) h
  have ho := comparison_outgoing_injective_at S U E hE hobj c hs
  exact eq_of_heq (Sigma.mk.inj ho).2

/-- Fullness uses a literal outgoing lift downstairs and literal fiber
transitivity to bring its endpoint into the image of the upstairs equivalence. -/
theorem comparisonFunctor_full : (comparisonFunctor S U E hE).Full := by
  let B := comparisonFunctor S U E hE
  have sq : F ⋙ B = E.functor ⋙ P := comparison_square S U E hE
  change B.Full
  constructor
  intro d e γ
  obtain ⟨c, rfl⟩ := S.obj_surjective d
  obtain ⟨c', rfl⟩ := S.obj_surjective e
  let hc : B.obj (F.obj c) = P.obj (E.functor.obj c) := Functor.congr_obj sq c
  let hc' : B.obj (F.obj c') = P.obj (E.functor.obj c') := Functor.congr_obj sq c'
  let γ' : P.obj (E.functor.obj c) ⟶ P.obj (E.functor.obj c') :=
    eqToHom hc.symm ≫ γ ≫ eqToHom hc'
  obtain ⟨⟨z, φ⟩, hφ⟩ := (U.covering (E.functor.obj c)).surjective
    ⟨P.obj (E.functor.obj c'), γ'⟩
  have hz : P.obj z = P.obj (E.functor.obj c') := (Sigma.mk.inj hφ).1
  obtain ⟨q, hq⟩ := U.fiber_transitive (E.functor.obj c') z hz.symm
  have he : E.functor.obj ((A.functor q).obj c') = z :=
    (Functor.congr_obj (hE q) c').trans hq
  let δ : c ⟶ (A.functor q).obj c' := E.functor.preimage (φ ≫ eqToHom he.symm)
  have hδ : E.functor.map δ = φ ≫ eqToHom he.symm := E.functor.map_preimage _
  let ht : F.obj ((A.functor q).obj c') = F.obj c' := Functor.congr_obj (S.invariant q) c'
  let α : F.obj c ⟶ F.obj c' := F.map δ ≫ eqToHom ht
  refine ⟨α, eq_of_heq ?_⟩
  have hBcast : HEq (B.map α) (B.map (F.map δ)) := by
    dsimp only [α]
    rw [B.map_comp, eqToHom_map]
    exact comp_eqToHom_heq _ _
  have hsquare : HEq (B.map (F.map δ)) (P.map (E.functor.map δ)) :=
    Functor.hcongr_hom sq δ
  have hPcast : HEq (P.map (E.functor.map δ)) (P.map φ) := by
    rw [hδ, P.map_comp, eqToHom_map]
    exact comp_eqToHom_heq _ _
  have hγ : HEq γ' γ := by
    dsimp only [γ']
    exact (eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)
  exact hBcast.trans (hsquare.trans (hPcast.trans ((Sigma.mk.inj hφ).2.trans hγ)))

/-- Essential surjectivity uses the genuine counit isomorphism, not a
purported strict surjectivity of the upstairs equivalence on objects. -/
theorem comparisonFunctor_essSurj : (comparisonFunctor S U E hE).EssSurj := by
  let B := comparisonFunctor S U E hE
  have sq : F ⋙ B = E.functor ⋙ P := comparison_square S U E hE
  change B.EssSurj
  constructor
  intro y
  obtain ⟨x, rfl⟩ := U.obj_surjective y
  let c := E.inverse.obj x
  have hc : B.obj (F.obj c) = P.obj (E.functor.obj c) := Functor.congr_obj sq c
  exact ⟨F.obj c, ⟨eqToIso hc ≪≫ P.mapIso (E.counitIso.app x)⟩⟩

theorem comparisonFunctor_isEquivalence (hobj : Function.Injective E.functor.obj) :
    (comparisonFunctor S U E hE).IsEquivalence where
  faithful := comparisonFunctor_faithful S U E hE hobj
  full := comparisonFunctor_full S U E hE
  essSurj := comparisonFunctor_essSurj S U E hE

/-- The resulting actual equivalence of the two base groupoids. -/
noncomputable def comparisonEquivalence (hobj : Function.Injective E.functor.obj) : D ≌ Y := by
  letI := comparisonFunctor_isEquivalence S U E hE hobj
  exact (comparisonFunctor S U E hE).asEquivalence

@[simp] theorem comparisonEquivalence_functor (hobj : Function.Injective E.functor.obj) :
    (comparisonEquivalence S U E hE hobj).functor = comparisonFunctor S U E hE := rfl

theorem comparisonEquivalence_square (hobj : Function.Injective E.functor.obj) :
    F ⋙ (comparisonEquivalence S U E hE hobj).functor = E.functor ⋙ P :=
  comparison_square S U E hE

end ArtinNormalisers.Chamber3
