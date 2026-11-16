import Mathlib
import ArtinDeligne
import Proofs.FiniteWallPaths
import Proofs.UniversalWallGroupoid
import Proofs.SimpleWallCrossings

set_option maxHeartbeats 2000000

theorem UniversalGenerators : (∀ {S : Type*} [Finite S] (M : CoxeterMatrix S) (J : Set S),
  let W := CoxeterMatrix.Group M
  let cs := CoxeterMatrix.toCoxeterSystem M
  let Label := { p : W × Set S //
    Set.image (fun u : W => u * p.1) (CoxeterSystem.parabolic cs J : Set W) =
      Set.image (fun u : W => p.1 * u) (CoxeterSystem.parabolic cs p.2 : Set W) ∧
    CoxeterSystem.IsMinimalCosetRep cs p.2 p.1 }
  let component : Set S → S → Set S := fun I a =>
    { b | b ∈ Set.insert a I ∧ Relation.ReflTransGen
      (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b }
  let Atom := { e : Label × S // e.2 ∉ e.1.val.2 ∧
    Finite (CoxeterSystem.parabolic cs (component e.1.val.2 e.2)) }
  let crossing := fun e : Atom =>
    SimpleWallCrossings S W M cs e.val.1.val.2 e.val.2 e.property.1 e.property.2
  ∀ A B : Label, ∃ es : List Atom,
    List.foldr
      (fun e tail P => P = e.val.1.val ∧ tail ((crossing e).2.2 e.val.1.val.1))
      (fun P => P = B.val) es A.val ∧
    List.prod (List.map (fun e => (crossing e).1) es) = A.val.1⁻¹ * B.val.1 ∧
    Set.range (fun f : (UniversalWallGroupoid cs J).Hom A B => f.val) =
      {List.prod (List.map (fun e => (crossing e).1) es)}) :=
(by
  classical
  intro S _ M J
  /-
  Proposition 4.4, printed p.16:
  https://arxiv.org/pdf/2509.21915#page=16
  Numbered inspiration: steps 1.1, 2.1 and 3.1 at
  https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-prop-universal-generators-artin-tits-normalisers.
  Steps 1.1 and 2.1 are supplied by the completed FiniteWallPaths endpoint
  on exactly these labels. No additional chamber-identification premise is
  needed: its endpoint already records every intermediate chamber label.
  For step 3.1, induction on that finite relation constructs a source-tagged
  list and proves the ordered product by cancellation. This is a local
  implementation lemma, not a separately attributed article theorem.
  The reflexive case uses the empty list. The final range calculation uses
  the actual singleton-arrow definition, retaining both endpoint tags.
  Finite rank is the explicit user-directed geometric convention; no
  finiteness of W or W_J is used. No literature defect is invoked here.
  -/
  let W := CoxeterMatrix.Group M
  let cs := CoxeterMatrix.toCoxeterSystem M
  let Label := { p : W × Set S //
    Set.image (fun u : W => u * p.1) (CoxeterSystem.parabolic cs J : Set W) =
      Set.image (fun u : W => p.1 * u) (CoxeterSystem.parabolic cs p.2 : Set W) ∧
    CoxeterSystem.IsMinimalCosetRep cs p.2 p.1 }
  let component : Set S → S → Set S := fun I a =>
    { b | b ∈ Set.insert a I ∧ Relation.ReflTransGen
      (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b }
  let Atom := { e : Label × S // e.2 ∉ e.1.val.2 ∧
    Finite (CoxeterSystem.parabolic cs (component e.1.val.2 e.2)) }
  let crossing := fun e : Atom =>
    SimpleWallCrossings S W M cs e.val.1.val.2 e.val.2 e.property.1 e.property.2
  let step : Label → Label → Prop := fun p q =>
    ∃ (a : S) (ha : a ∉ p.val.2)
      (hD : Finite (CoxeterSystem.parabolic cs (component p.val.2 a))),
      (SimpleWallCrossings S W M cs p.val.2 a ha hD).2.2 p.val.1 = q.val
  have path_list (A B : Label) (h : Relation.ReflTransGen step A B) :
      ∃ es : List Atom,
        List.foldr
          (fun e tail P => P = e.val.1.val ∧ tail ((crossing e).2.2 e.val.1.val.1))
          (fun P => P = B.val) es A.val ∧
        List.prod (List.map (fun e => (crossing e).1) es) = A.val.1⁻¹ * B.val.1 := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl =>
        exact ⟨[], rfl, by simp⟩
    | @head A C hAC hCB ih =>
        rcases hAC with ⟨a, ha, hD, hcross⟩
        rcases ih with ⟨es, hes, hprod⟩
        let e : Atom := ⟨(A, a), ha, hD⟩
        have he : (crossing e).2.2 A.val.1 = C.val := hcross
        have hfirst : A.val.1 * (crossing e).1 = C.val.1 :=
          congrArg Prod.fst he
        refine ⟨e :: es, ?_, ?_⟩
        · change A.val = A.val ∧ _
          exact ⟨rfl, he.symm ▸ hes⟩
        · change (crossing e).1 * List.prod (List.map (fun e => (crossing e).1) es) = _
          rw [hprod, ← hfirst]
          simp only [mul_inv_rev, mul_assoc, mul_inv_cancel_left]
  dsimp only
  intro A B
  obtain ⟨es, hpath, hprod⟩ := path_list A B (FiniteWallPaths M J A B)
  refine ⟨es, hpath, hprod, ?_⟩
  /- Step 3.1: every arrow has this label, and the canonical arrow exists. -/
  ext z
  constructor
  · rintro ⟨f, rfl⟩
    exact (f.property.trans hprod.symm : f.val = _)
  · intro hz
    have hz' : z = A.val.1⁻¹ * B.val.1 := (Set.mem_singleton_iff.mp hz).trans hprod
    exact ⟨⟨z, hz'⟩, rfl⟩
)
