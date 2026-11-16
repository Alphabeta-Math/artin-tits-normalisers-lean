import Mathlib
import ArtinDeligne
import Proofs.BrinkHowlettGroupoid
import Proofs.SimpleWallCrossings
import Proofs.ElementaryWallMorphism

noncomputable def StandardExpressions : (∀ {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) (I K : { L : Set S // ∃ g : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (CoxeterSystem.parabolic cs L) = CoxeterSystem.parabolic cs J }) (w : (BrinkHowlettGroupoid cs J).Hom I K), Type _) :=
(fun {S W} _inst {M} cs J I K w =>
  let Obj := { L : Set S // ∃ g : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (CoxeterSystem.parabolic cs L) = CoxeterSystem.parabolic cs J }
  let component : Set S → S → Set S := fun L a =>
    { b | b ∈ Set.insert a L ∧ Relation.ReflTransGen
      (fun i j : S => i ∈ Set.insert a L ∧ j ∈ Set.insert a L ∧ i ≠ j ∧ M i j ≠ 2) a b }
  let Atom := { p : Obj × S // p.2 ∉ p.1.val ∧ Finite (CoxeterSystem.parabolic cs (component p.1.val p.2)) }
  let crossing := fun e : Atom => SimpleWallCrossings S W M cs e.val.1.val e.val.2 e.property.1 e.property.2
  { es : List Atom //
    List.foldr
      (fun e tail L => L = e.val.1.val ∧ tail (crossing e).2.1)
      (fun L => L = K.val) es I.val ∧
    List.prod (List.map (fun e => (crossing e).1) es) = w.val ∧
    CoxeterSystem.length cs w.val =
      List.sum (List.map (fun e => CoxeterSystem.length cs (crossing e).1) es) })
