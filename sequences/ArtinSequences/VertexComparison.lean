module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.Conj

/-!
# Based vertex-group comparison for genuine fully faithful functors

The fundamental group here is mathlib's actual `End (FundamentalGroupoid.mk x)`.
The comparison maps actual endomorphisms by the supplied actual functor and
transports their endpoints along the stated object equality. Fully faithful
functors give multiplicative equivalences by mathlib's proved endomorphism
equivalence. No geometric equivalence or normalizer comparison is assumed.

Multiplication in both endomorphism groups reverses categorical composition.
This file introduces no additional opposite-group identification.
-/

@[expose] public section

namespace ArtinNormalisers.Sequence4

open CategoryTheory

universe u v u' v' uX uY

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {X : Type uX} [TopologicalSpace X] {Y : Type uY} [TopologicalSpace Y]

/-- The based map of actual vertex groups, including literal endpoint transport. -/
noncomputable def basedEndHom (F : C ⥤ FundamentalGroupoid X) (c : C) {x : X}
    (h : F.obj c = FundamentalGroupoid.mk x) : End c →* FundamentalGroup X x :=
  (eqToIso h).conj.toMonoidHom.comp (F.mapEnd c)

/-- A genuine fully faithful functor gives an isomorphism with the actual
fundamental group at its specified image basepoint. -/
noncomputable def basedEndEquiv (F : C ⥤ FundamentalGroupoid X) (hF : F.FullyFaithful)
    (c : C) {x : X} (h : F.obj c = FundamentalGroupoid.mk x) :
    End c ≃* FundamentalGroup X x :=
  (hF.mulEquivEnd c).trans (eqToIso h).conj

@[simp] theorem basedEndHom_apply_asHom (F : C ⥤ FundamentalGroupoid X) (c : C) {x : X}
    (h : F.obj c = FundamentalGroupoid.mk x) (e : End c) :
    (basedEndHom F c h e).asHom =
      eqToHom h.symm ≫ F.map e.asHom ≫ eqToHom h := by
  rfl

@[simp] theorem basedEndEquiv_apply_asHom (F : C ⥤ FundamentalGroupoid X)
    (hF : F.FullyFaithful) (c : C) {x : X}
    (h : F.obj c = FundamentalGroupoid.mk x) (e : End c) :
    (basedEndEquiv F hF c h e).asHom =
      eqToHom h.symm ≫ F.map e.asHom ≫ eqToHom h := by
  rfl

@[simp] theorem basedEndEquiv_apply (F : C ⥤ FundamentalGroupoid X)
    (hF : F.FullyFaithful) (c : C) {x : X}
    (h : F.obj c = FundamentalGroupoid.mk x) (e : End c) :
    basedEndEquiv F hF c h e = basedEndHom F c h e := by
  rfl

theorem basedEndEquiv_toMonoidHom (F : C ⥤ FundamentalGroupoid X)
    (hF : F.FullyFaithful) (c : C) {x : X} (h : F.obj c = FundamentalGroupoid.mk x) :
    (basedEndEquiv F hF c h).toMonoidHom = basedEndHom F c h := by
  ext e
  rfl

/-- Functor composition acts on the actual endomorphism monoids in the
same order as ordinary composition of the resulting monoid homomorphisms. -/
theorem mapEnd_comp (F : C ⥤ D) (G : D ⥤ FundamentalGroupoid X) (c : C) :
    (F ⋙ G).mapEnd c = (G.mapEnd (F.obj c)).comp (F.mapEnd c) := by
  rfl

theorem basedEndHom_comp (F : C ⥤ D) (G : D ⥤ FundamentalGroupoid X)
    (c : C) {x : X} (h : G.obj (F.obj c) = FundamentalGroupoid.mk x) :
    basedEndHom (F ⋙ G) c h = (basedEndHom G (F.obj c) h).comp (F.mapEnd c) := by
  rfl

/-- A strict equality of the actual functors gives equality of their based
maps; proofs of the same object equality contribute no extra choice. -/
theorem basedEndHom_congr {F G : C ⥤ FundamentalGroupoid X} (hFG : F = G)
    (c : C) {x : X} (hF : F.obj c = FundamentalGroupoid.mk x)
    (hG : G.obj c = FundamentalGroupoid.mk x) :
    basedEndHom F c hF = basedEndHom G c hG := by
  subst G
  rfl

/-- Naturality with the actual fundamental-group map of a continuous map. -/
theorem basedEndHom_map (F : C ⥤ FundamentalGroupoid X) (c : C) {x : X}
    (h : F.obj c = FundamentalGroupoid.mk x) (f : C(X, Y)) :
    (FundamentalGroup.map f x).comp (basedEndHom F c h) =
      basedEndHom (F ⋙ FundamentalGroupoid.map f) c
        (congrArg (FundamentalGroupoid.map f).obj h) := by
  ext e
  change (FundamentalGroupoid.map f).map (basedEndHom F c h e).asHom =
    eqToHom (congrArg (FundamentalGroupoid.map f).obj h).symm ≫
      (FundamentalGroupoid.map f).map (F.map e.asHom) ≫
        eqToHom (congrArg (FundamentalGroupoid.map f).obj h)
  simp only [basedEndHom_apply_asHom, Functor.map_comp, eqToHom_map]

/-- A strict square of genuine groupoid functors induces the corresponding
strict square on based vertex groups, with the given object identifications. -/
theorem basedEndHom_square (F : C ⥤ FundamentalGroupoid X) (Q : C ⥤ D)
    (G : D ⥤ FundamentalGroupoid Y) (f : C(X, Y))
    (hsquare : F ⋙ FundamentalGroupoid.map f = Q ⋙ G)
    (c : C) {x : X} (hF : F.obj c = FundamentalGroupoid.mk x)
    (hG : G.obj (Q.obj c) = FundamentalGroupoid.mk (f x)) :
    (FundamentalGroup.map f x).comp (basedEndHom F c hF) =
      (basedEndHom G (Q.obj c) hG).comp (Q.mapEnd c) := by
  rw [basedEndHom_map]
  exact (basedEndHom_congr hsquare c _ hG).trans (basedEndHom_comp Q G c hG)

/-- The image of a vertex comparison transported along an actual path.
This uses mathlib's genuine change-of-basepoint equivalence. -/
noncomputable def pathBasedEndEquiv (F : C ⥤ FundamentalGroupoid X)
    (hF : F.FullyFaithful) (c : C) {x y : X}
    (h : F.obj c = FundamentalGroupoid.mk x) (p : Path x y) :
    End c ≃* FundamentalGroup X y :=
  (basedEndEquiv F hF c h).trans (FundamentalGroup.fundamentalGroupMulEquivOfPath p)

theorem pathBasedEndEquiv_apply_asHom (F : C ⥤ FundamentalGroupoid X)
    (hF : F.FullyFaithful) (c : C) {x y : X}
    (h : F.obj c = FundamentalGroupoid.mk x) (p : Path x y) (e : End c) :
    (pathBasedEndEquiv F hF c h p e).asHom =
      (Path.Homotopic.Quotient.mk p.symm) ≫
        (eqToHom h.symm ≫ F.map e.asHom ≫ eqToHom h) ≫ Path.Homotopic.Quotient.mk p := by
  rfl

/-- Change of basepoint commutes with the actual map of fundamental groups
under a continuous map, so compatible paths can transport a strict square. -/
theorem fundamentalGroup_map_changeBasepoint (f : C(X, Y)) {x x' : X} (p : Path x x')
    (g : FundamentalGroup X x) :
    FundamentalGroup.map f x' (FundamentalGroup.fundamentalGroupMulEquivOfPath p g) =
      FundamentalGroup.fundamentalGroupMulEquivOfPath (p.map f.continuous)
        (FundamentalGroup.map f x g) := by
  apply End.ext
  let α : FundamentalGroupoid.mk x ≅ FundamentalGroupoid.mk x' :=
    (Groupoid.isoEquivHom ..).symm (Path.Homotopic.Quotient.mk p)
  let β : FundamentalGroupoid.mk (f x) ≅ FundamentalGroupoid.mk (f x') :=
    (Groupoid.isoEquivHom ..).symm (Path.Homotopic.Quotient.mk (p.map f.continuous))
  have hiso : (FundamentalGroupoid.map f).mapIso α = β := by
    apply Iso.ext
    exact (Path.Homotopic.Quotient.mk_map p f).symm
  change (FundamentalGroupoid.map f).map (α.conj g).asHom =
    (β.conj ((FundamentalGroupoid.map f).mapEnd (FundamentalGroupoid.mk x) g)).asHom
  rw [← hiso]
  exact (FundamentalGroupoid.map f).map_conj α g

end ArtinNormalisers.Sequence4
