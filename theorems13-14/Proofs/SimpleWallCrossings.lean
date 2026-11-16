import Mathlib
import ArtinDeligne


noncomputable def SimpleWallCrossings : (∀ (S : Type _) (W : Type _) [Group W] (M : CoxeterMatrix S) (cs : CoxeterSystem M W) (I : Set S) (a : S) (_ha : a ∉ I), let D : Set S := {b | b ∈ Set.insert a I ∧ Relation.ReflTransGen (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b}; Finite (CoxeterSystem.parabolic cs D) → W × Set S × (W → W × Set S)) :=
(fun S W _inst M cs I a _ha =>
  let D : Set S := {b | b ∈ Set.insert a I ∧ Relation.ReflTransGen (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b}
  fun hD =>
    letI : Finite (CoxeterSystem.parabolic cs D) := hD
    let longest : (L : Set S) → L ⊆ D → W := fun L hL =>
      letI : Finite (CoxeterSystem.parabolic cs L) :=
        Finite.of_injective
          (fun w : CoxeterSystem.parabolic cs L => (⟨(w : W), (CoxeterSystem.parabolic_mono cs hL) w.property⟩ : CoxeterSystem.parabolic cs D))
          (fun _ _ h => Subtype.ext (congrArg (fun z : CoxeterSystem.parabolic cs D => (z : W)) h))
      (Classical.choose (Finite.exists_max (fun w : CoxeterSystem.parabolic cs L => CoxeterSystem.length cs (w : W)))).val
    let wD := longest D (fun _ h => h)
    let opposition : Equiv D D :=
      @Classical.epsilon (Equiv D D) ⟨Equiv.refl D⟩ (fun e => ∀ i : D, CoxeterSystem.geometricRepresentation cs wD (Finsupp.single (i : S) (1 : Real)) = -Finsupp.single (e i : S) (1 : Real))
    let aD : D := ⟨a, ⟨Set.mem_insert a I, Relation.ReflTransGen.refl⟩⟩
    let v := longest (D \ {a}) Set.sdiff_subset * wD
    let K : Set S := Set.insert a I \ {(opposition aD : S)}
    (v, K, fun x => (x * v, K)))
