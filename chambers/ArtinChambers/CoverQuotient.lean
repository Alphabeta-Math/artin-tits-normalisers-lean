module

public import ArtinChambers.GroupoidCover
public import Mathlib.Algebra.Group.Defs
public import Mathlib.CategoryTheory.EqToHom

/-!
# Strict invariant descent along an orbit covering of groupoids

Unique outgoing-arrow lifting and transitivity on object fibers imply that
every strictly invariant functor descends uniquely. No quotient universal
property is included in the input data. Equality of image arrows is proved
from the actual covering bijections before the descended functor is built.
-/

@[expose] public section

set_option autoImplicit false

namespace ArtinNormalisers.Chamber3

open CategoryTheory

universe uQ uC vC uD vD uT vT

/-- A strict left group action, with the corresponding order of composition
of its actual action functors. These fields are action laws only. -/
structure StrictGroupoidAction (Q : Type uQ) [Group Q]
    (C : Type uC) [Groupoid.{vC} C] where
  functor : Q → C ⥤ C
  map_one : functor 1 = 𝟭 C
  map_mul : ∀ q r, functor (q * r) = functor r ⋙ functor q

variable {Q : Type uQ} [Group Q] {C : Type uC} [Groupoid.{vC} C]
  {D : Type uD} [Groupoid.{vD} D] {T : Type uT} [Groupoid.{vT} T]

/-- The low-level geometric/categorical properties of the proposed orbit
map. In particular, no existence of descended functors is a field. -/
structure CoverOrbitData (A : StrictGroupoidAction Q C) (F : C ⥤ D) : Prop where
  covering : IsCoveringFunctor F
  obj_surjective : Function.Surjective F.obj
  invariant : ∀ q, A.functor q ⋙ F = F
  fiber_transitive : ∀ X Y, F.obj X = F.obj Y → ∃ q, (A.functor q).obj X = Y

private theorem map_heq {X Y X' Y' : C} (H : C ⥤ T)
    (hX : X = X') (hY : Y = Y') {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) :
    HEq (H.map f) (H.map g) := by
  cases hX
  cases hY
  cases h
  rfl

private theorem id_heq {X Y : T} (h : X = Y) : HEq (𝟙 X) (𝟙 Y) := by
  cases h
  rfl

namespace CoverOrbitData

variable {A : StrictGroupoidAction Q C} {F : C ⥤ D}
  (S : CoverOrbitData A F) (H : C ⥤ T) (hH : ∀ q, A.functor q ⋙ H = H)

include S hH in
theorem obj_eq {X Y : C} (h : F.obj X = F.obj Y) : H.obj X = H.obj Y := by
  obtain ⟨q, hq⟩ := S.fiber_transitive X Y h
  have he := Functor.congr_obj (hH q) X
  change H.obj ((A.functor q).obj X) = H.obj X at he
  rw [hq] at he
  exact he.symm

include S hH in
/-- Image arrows of an invariant functor are independent of an outgoing
lift and of the representative object in the source fiber. -/
theorem map_eq {X Y X' Y' : C} {f : X ⟶ Y} {g : X' ⟶ Y'}
    (hX : F.obj X = F.obj X') (hY : F.obj Y = F.obj Y') (hf : HEq (F.map f) (F.map g)) :
    HEq (H.map f) (H.map g) := by
  obtain ⟨q, hq⟩ := S.fiber_transitive X X' hX
  let aq := A.functor q
  let f' : X' ⟶ aq.obj Y := eqToHom hq.symm ≫ aq.map f
  have htarget : F.obj (aq.obj Y) = F.obj Y' :=
    (Functor.congr_obj (S.invariant q) Y).trans hY
  have hFshift : HEq (F.map f') (F.map f) := by
    dsimp only [f']
    rw [F.map_comp, eqToHom_map]
    exact (eqToHom_comp_heq _ _).trans (Functor.hcongr_hom (S.invariant q) f)
  have ho : (⟨aq.obj Y, f'⟩ : Outgoing C X') = ⟨Y', g⟩ :=
    (S.covering X').injective (Sigma.ext htarget (hFshift.trans hf))
  have hHshift : HEq (H.map f') (H.map f) := by
    dsimp only [f']
    rw [H.map_comp, eqToHom_map]
    exact (eqToHom_comp_heq _ _).trans (Functor.hcongr_hom (hH q) f)
  have himage := map_heq H rfl (Sigma.mk.inj ho).1 (Sigma.mk.inj ho).2
  exact hHshift.symm.trans himage

/-- A representative is chosen only after actual surjectivity is supplied. -/
noncomputable def pick (d : D) : C := (S.obj_surjective d).choose

theorem pick_obj (d : D) : F.obj (S.pick d) = d := (S.obj_surjective d).choose_spec

noncomputable def descObj (d : D) : T := H.obj (S.pick d)

include hH in
theorem descObj_image (X : C) : S.descObj H (F.obj X) = H.obj X :=
  S.obj_eq H hH (S.pick_obj (F.obj X))

/-- The actual chosen outgoing lift of an arrow at a chosen representative. -/
noncomputable def pickedLift {d e : D} (f : d ⟶ e) : Outgoing C (S.pick d) :=
  liftOutgoing F S.covering (S.pick d) ⟨e, eqToHom (S.pick_obj d) ≫ f⟩

theorem pickedLift_target {d e : D} (f : d ⟶ e) : F.obj (S.pickedLift f).1 = e :=
  congrArg Sigma.fst (mapOutgoing_liftOutgoing F S.covering (S.pick d)
    ⟨e, eqToHom (S.pick_obj d) ≫ f⟩)

theorem pickedLift_map {d e : D} (f : d ⟶ e) : HEq (F.map (S.pickedLift f).2) f := by
  have he := mapOutgoing_liftOutgoing F S.covering (S.pick d)
    ⟨e, eqToHom (S.pick_obj d) ≫ f⟩
  exact (Sigma.mk.inj he).2.trans (eqToHom_comp_heq _ _)

noncomputable def descMap {d e : D} (f : d ⟶ e) : S.descObj H d ⟶ S.descObj H e :=
  H.map (S.pickedLift f).2 ≫
    eqToHom (S.obj_eq H hH ((S.pickedLift_target f).trans (S.pick_obj e).symm))

theorem descMap_lift {d e : D} (f : d ⟶ e) :
    HEq (S.descMap H hH f) (H.map (S.pickedLift f).2) :=
  comp_eqToHom_heq _ _

theorem descMap_image {X Y : C} (f : X ⟶ Y) :
    HEq (S.descMap H hH (F.map f)) (H.map f) :=
  (S.descMap_lift H hH (F.map f)).trans
    (S.map_eq H hH (S.pick_obj (F.obj X)) (S.pickedLift_target (F.map f))
      (S.pickedLift_map (F.map f)))

theorem descMap_id (d : D) : S.descMap H hH (𝟙 d) = 𝟙 (S.descObj H d) := by
  obtain ⟨X, rfl⟩ := S.obj_surjective d
  have hm := S.descMap_image H hH (𝟙 X)
  rw [F.map_id, H.map_id] at hm
  exact eq_of_heq (hm.trans (id_heq (S.descObj_image H hH X).symm))

theorem descMap_comp {d e z : D} (f : d ⟶ e) (g : e ⟶ z) :
    S.descMap H hH (f ≫ g) = S.descMap H hH f ≫ S.descMap H hH g := by
  obtain ⟨X, rfl⟩ := S.obj_surjective d
  obtain ⟨⟨Y, p⟩, hp⟩ := (S.covering X).surjective ⟨e, f⟩
  have hY := (Sigma.mk.inj hp).1
  cases hY
  have hf : F.map p = f := eq_of_heq (Sigma.mk.inj hp).2
  subst f
  obtain ⟨⟨Z, q⟩, hq⟩ := (S.covering Y).surjective ⟨z, g⟩
  have hZ := (Sigma.mk.inj hq).1
  cases hZ
  have hg : F.map q = g := eq_of_heq (Sigma.mk.inj hq).2
  subst g
  rw [← F.map_comp]
  have hfg := S.descMap_image H hH (p ≫ q)
  rw [H.map_comp] at hfg
  have hc : HEq (S.descMap H hH (F.map p) ≫ S.descMap H hH (F.map q))
      (H.map p ≫ H.map q) :=
    heq_comp (S.descObj_image H hH X) (S.descObj_image H hH Y) (S.descObj_image H hH Z)
      (S.descMap_image H hH p) (S.descMap_image H hH q)
  exact eq_of_heq (hfg.trans hc.symm)

/-- The descended actual functor, constructed by choosing outgoing lifts.
The preceding independence proof supplies its functor laws. -/
noncomputable def desc : D ⥤ T where
  obj := S.descObj H
  map := S.descMap H hH
  map_id := S.descMap_id H hH
  map_comp := S.descMap_comp H hH

theorem desc_fac : F ⋙ S.desc H hH = H := by
  apply Functor.hext (S.descObj_image H hH)
  intro X Y f
  exact S.descMap_image H hH f

end CoverOrbitData

/-- A surjective-on-objects covering detects strict equality of functors
after precomposition, by lifting every outgoing arrow. -/
theorem coveringFunctor_precomp_injective (F : C ⥤ D) (hF : IsCoveringFunctor F)
    (hsurj : Function.Surjective F.obj) :
    Function.Injective (fun G : D ⥤ T => F ⋙ G) := by
  intro G₁ G₂ h
  apply Functor.hext (fun d => by
    obtain ⟨X, rfl⟩ := hsurj d
    exact Functor.congr_obj h X)
  intro d e f
  obtain ⟨X, rfl⟩ := hsurj d
  obtain ⟨⟨Y, p⟩, hp⟩ := (hF X).surjective ⟨e, f⟩
  have hY := (Sigma.mk.inj hp).1
  cases hY
  have hf : F.map p = f := eq_of_heq (Sigma.mk.inj hp).2
  subst f
  exact Functor.hcongr_hom h p

/-- Every strictly invariant functor descends uniquely along the actual
covering with transitive object fibers. This is a proved quotient universal
property; it is not an assumption or a field of the action/cover data. -/
theorem coveringFunctor_descent_existsUnique
    (A : StrictGroupoidAction Q C) (F : C ⥤ D) (hcover : IsCoveringFunctor F)
    (hsurj : Function.Surjective F.obj) (hF : ∀ q, A.functor q ⋙ F = F)
    (htrans : ∀ X Y, F.obj X = F.obj Y → ∃ q, (A.functor q).obj X = Y)
    (H : C ⥤ T) (hH : ∀ q, A.functor q ⋙ H = H) :
    ∃! desc : D ⥤ T, F ⋙ desc = H := by
  let S : CoverOrbitData A F := ⟨hcover, hsurj, hF, htrans⟩
  refine ⟨S.desc H hH, S.desc_fac H hH, ?_⟩
  intro G hG
  exact coveringFunctor_precomp_injective F hcover hsurj (hG.trans (S.desc_fac H hH).symm)

end ArtinNormalisers.Chamber3
