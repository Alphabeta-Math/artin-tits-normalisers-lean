module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Equivalence

/-!
# Covering functors as actual unique outgoing-arrow lifting

The total outgoing arrow map records both the target object and the
morphism. Bijectivity is precisely existence and uniqueness of an outgoing
lift. It is a property to prove for the concrete functors, not a hypothesis
asserting a geometric or ribbon equivalence.
-/

@[expose] public section

namespace ArtinNormalisers.Chamber3

open CategoryTheory

universe u v u' v' u'' v''

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {E : Type u''} [Category.{v''} E]

/-- All outgoing arrows, retaining their actual target objects. -/
abbrev Outgoing (C : Type u) [Category.{v} C] (X : C) := Σ Y : C, X ⟶ Y

/-- A functor acts on the complete outgoing-arrow set at its source. -/
def mapOutgoing (F : C ⥤ D) (X : C) : Outgoing C X → Outgoing D (F.obj X) :=
  fun p => ⟨F.obj p.1, F.map p.2⟩

/-- The unique-outgoing-lift condition of a groupoid covering. -/
def IsCoveringFunctor (F : C ⥤ D) : Prop :=
  ∀ X, Function.Bijective (mapOutgoing F X)

@[simp] theorem mapOutgoing_mk (F : C ⥤ D) (X Y : C) (f : X ⟶ Y) :
    mapOutgoing F X ⟨Y, f⟩ = ⟨F.obj Y, F.map f⟩ := rfl

@[simp] theorem mapOutgoing_comp (F : C ⥤ D) (G : D ⥤ E) (X : C) :
    mapOutgoing (F ⋙ G) X = mapOutgoing G (F.obj X) ∘ mapOutgoing F X := rfl

theorem isCoveringFunctor_id : IsCoveringFunctor (𝟭 C) := by
  intro X
  exact Function.bijective_id

theorem IsCoveringFunctor.comp {F : C ⥤ D} {G : D ⥤ E}
    (hF : IsCoveringFunctor F) (hG : IsCoveringFunctor G) :
    IsCoveringFunctor (F ⋙ G) := by
  intro X
  exact (hG (F.obj X)).comp (hF X)

/-- The genuine bijection used to lift both an endpoint and an arrow. -/
noncomputable def outgoingEquiv (F : C ⥤ D) (hF : IsCoveringFunctor F) (X : C) :
    Outgoing C X ≃ Outgoing D (F.obj X) := Equiv.ofBijective _ (hF X)

/-- The actual outgoing lift supplied by the proved bijection. -/
noncomputable def liftOutgoing (F : C ⥤ D) (hF : IsCoveringFunctor F) (X : C)
    (p : Outgoing D (F.obj X)) : Outgoing C X := (outgoingEquiv F hF X).symm p

@[simp] theorem mapOutgoing_liftOutgoing (F : C ⥤ D) (hF : IsCoveringFunctor F) (X : C)
    (p : Outgoing D (F.obj X)) : mapOutgoing F X (liftOutgoing F hF X p) = p :=
  (outgoingEquiv F hF X).apply_symm_apply p

@[simp] theorem liftOutgoing_mapOutgoing (F : C ⥤ D) (hF : IsCoveringFunctor F) (X : C)
    (p : Outgoing C X) : liftOutgoing F hF X (mapOutgoing F X p) = p :=
  (outgoingEquiv F hF X).symm_apply_apply p

/-- Every covering is faithful on each fixed-endpoint hom-set. -/
theorem IsCoveringFunctor.faithful {F : C ⥤ D} (hF : IsCoveringFunctor F) : F.Faithful := {
  map_injective := fun {X Y} {f g} h => by
    have hs : (⟨Y, f⟩ : Outgoing C X) = ⟨Y, g⟩ :=
      (hF X).injective (congrArg (fun k : F.obj X ⟶ F.obj Y =>
        (⟨F.obj Y, k⟩ : Outgoing D (F.obj X))) h)
    exact eq_of_heq (Sigma.mk.inj hs).2 }

end ArtinNormalisers.Chamber3
