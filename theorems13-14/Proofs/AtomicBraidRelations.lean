import Mathlib
import ArtinDeligne
import Proofs.StandardExpressions
import Proofs.TwoGeneratorMinimal

set_option maxHeartbeats 2000000

noncomputable def AtomicBraidRelations : (∀ {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S),
  let Obj := { L : Set S // ∃ g : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (CoxeterSystem.parabolic cs L) = CoxeterSystem.parabolic cs J }
  let component : Set S → S → Set S := fun L a =>
    { b | b ∈ Set.insert a L ∧ Relation.ReflTransGen
      (fun i j : S => i ∈ Set.insert a L ∧ j ∈ Set.insert a L ∧ i ≠ j ∧ M i j ≠ 2) a b }
  let Atom := { p : Obj × S // p.2 ∉ p.1.val ∧ Finite (CoxeterSystem.parabolic cs (component p.1.val p.2)) }
  List Atom → List Atom → Prop) :=
(fun {S W} _inst {M} cs J =>
  let Obj := { L : Set S // ∃ g : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (CoxeterSystem.parabolic cs L) = CoxeterSystem.parabolic cs J }
  let component : Set S → S → Set S := fun L a =>
    { b | b ∈ Set.insert a L ∧ Relation.ReflTransGen
      (fun i j : S => i ∈ Set.insert a L ∧ j ∈ Set.insert a L ∧ i ≠ j ∧ M i j ≠ 2) a b }
  let Atom := { p : Obj × S // p.2 ∉ p.1.val ∧ Finite (CoxeterSystem.parabolic cs (component p.1.val p.2)) }
  let crossing := fun e : Atom => SimpleWallCrossings S W M cs e.val.1.val e.val.2 e.property.1 e.property.2
  let composable : List Atom → Set S → Set S → Prop := fun es L K =>
    List.foldr
      (fun e tail N => N = e.val.1.val ∧ tail (crossing e).2.1)
      (fun N => N = K) es L
  let parabolicRoots : Set S → Set (Finsupp S Real) := fun L =>
    { α | ∃ u : W, u ∈ CoxeterSystem.parabolic cs L ∧ ∃ i : S, i ∈ L ∧
      CoxeterSystem.geometricRepresentation cs u (Finsupp.single i (1 : Real)) = α }
  let braid : List Atom → List Atom → Prop := fun u v =>
    ∃ (L : Obj) (a b : S) (ha : a ∉ L.val) (hb : b ∉ L.val)
      (hab : a ≠ b)
      (hfin : Set.Finite (parabolicRoots (Set.insert a (Set.insert b L.val)) \ parabolicRoots L.val)),
      let h0 := TwoGeneratorMinimal cs J L a b ha hb hab hfin
      let hDa := Classical.choose h0
      let h1 := Classical.choose_spec h0
      let hDb := Classical.choose h1
      let h2 := Classical.choose_spec h1
      let K := Classical.choose h2
      let h3 := Classical.choose_spec h2
      let q := Classical.choose h3
      let h4 := Classical.choose_spec h3
      let ea := Classical.choose h4
      let eb := Classical.choose (Classical.choose_spec h4)
      (u = ea.val ∧ v = eb.val) ∨ (u = eb.val ∧ v = ea.val)
  fun es fs =>
    ∃ pre u v post : List Atom,
      braid u v ∧
      es = pre ++ u ++ post ∧
      fs = pre ++ v ++ post ∧
      ∃ L K : Obj, composable es L.val K.val ∧ composable fs L.val K.val)
