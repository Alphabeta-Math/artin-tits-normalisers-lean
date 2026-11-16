import Mathlib
import ArtinDeligne
import Proofs.StandardExpressions
import Proofs.StandardFactorCount

theorem GeneratorsAndStandardLength : (∀ {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S),
  let Obj := { L : Set S // ∃ g : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (CoxeterSystem.parabolic cs L) = CoxeterSystem.parabolic cs J }
  let component : Set S → S → Set S := fun L a =>
    { b | b ∈ Set.insert a L ∧ Relation.ReflTransGen
      (fun i j : S => i ∈ Set.insert a L ∧ j ∈ Set.insert a L ∧ i ≠ j ∧ M i j ≠ 2) a b }
  let Atom := { p : Obj × S // p.2 ∉ p.1.val ∧ Finite (CoxeterSystem.parabolic cs (component p.1.val p.2)) }
  let crossing := fun e : Atom => SimpleWallCrossings S W M cs e.val.1.val e.val.2 e.property.1 e.property.2
  (∀ (I K : Obj) (w : (BrinkHowlettGroupoid cs J).Hom I K),
    ∃ es : List Atom,
      List.foldr
        (fun e tail L => L = e.val.1.val ∧ tail (crossing e).2.1)
        (fun L => L = K.val) es I.val ∧
      List.prod (List.map (fun e => (crossing e).1) es) = w.val) ∧
  (∀ (I K : Obj) (w : (BrinkHowlettGroupoid cs J).Hom I K)
    (e f : StandardExpressions cs J I K w), List.length e.val = List.length f.val)) :=
(by
  intro S W inst M cs J
  /-
  Corollary 4.13(1)-(2), printed p.18:
  https://arxiv.org/pdf/2509.21915#page=18
  Numbered inspiration: Alphabeta Math steps 1.1 and 2.1 at
  https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-cor-brink-howlett-generators-length-artin-tits-normalisers.
  Step 1.1 uses the proved arbitrary-rank StandardFactorCount endpoint.
  Unfolding StandardExpressions exposes the exact source/target threading
  and ordered product; forgetting length additivity proves generation.
  Step 2.1 compares both lengths with the SAME parallel-class count.
  Departure from the article's geometric proof: use this algebraic supplier
  to retain arbitrary rank. No finite-rank or spherical-type hypothesis is
  introduced. These local have blocks are projections, not new standalone
  literature results. The supplied defect report
  https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects
  does not identify Corollary 4.13's statement as defective. Its finding
  pdf-wall-root-characterisation (printed p.10, after (3.15)) rejects the
  auxiliary root inclusion: in rank one with I empty its target is empty
  although the image contains -alpha_a. That inclusion is unused here;
  SimpleWallCrossings retains the longest-element definition (3.14).
  -/
  constructor
  · intro I K w
    have hexists : Nonempty (StandardExpressions cs J I K w) :=
      (StandardFactorCount cs J I K w).1
    rcases hexists with ⟨e⟩
    exact ⟨e.val, e.property.1, e.property.2.1⟩
  · intro I K w e f
    have hcount := (StandardFactorCount cs J I K w).2.2
    exact (hcount e).trans (hcount f).symm)
