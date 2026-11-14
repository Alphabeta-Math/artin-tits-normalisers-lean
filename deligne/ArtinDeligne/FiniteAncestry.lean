module

public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Nat.Basic

/-!
# Finite carriers closed under a terminating reduction

A reduction which fixes a point or strictly decreases a natural measure has
finite ancestry from each finite set. Any invariant property of the starting
points is preserved. This is a purely finite termination lemma; its geometric
application must separately prove continuity and the carrier conditions.
-/

@[expose] public section

namespace ArtinNormalisers.Deligne5

universe u

/-- Close a finite set under a deterministic, terminating reduction without
introducing points outside a proved invariant property. -/
theorem exists_finite_closed_ancestry {P : Type u} (step : P → P) (measure : P → ℕ)
    (Q : P → Prop) (hstep : ∀ x, step x = x ∨ measure (step x) < measure x)
    (hQ : ∀ x, Q x → Q (step x)) :
    ∀ A : Finset P, (∀ x ∈ A, Q x) →
      ∃ B : Finset P, A ⊆ B ∧ (∀ x ∈ B, Q x) ∧ ∀ x ∈ B, step x ∈ B := by
  classical
  have single : ∀ n : ℕ, ∀ x : P, measure x = n → Q x →
      ∃ B : Finset P, x ∈ B ∧ (∀ y ∈ B, Q y) ∧ ∀ y ∈ B, step y ∈ B := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro x hn hx
      rcases hstep x with hfix | hdec
      · refine ⟨{x}, by simp, ?_, ?_⟩
        · intro y hy
          simpa only [Finset.mem_singleton.mp hy] using hx
        · intro y hy
          rw [Finset.mem_singleton.mp hy, hfix]
          simp
      · obtain ⟨B, hfx, hBQ, hclosed⟩ :=
          ih (measure (step x)) (by omega) (step x) rfl (hQ x hx)
        refine ⟨insert x B, Finset.mem_insert_self _ _, ?_, ?_⟩
        · intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact hx
          · exact hBQ y hy
        · intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact Finset.mem_insert_of_mem hfx
          · exact Finset.mem_insert_of_mem (hclosed y hy)
  intro A
  induction A using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨∅, by simp, by simp, by simp⟩
  | @insert x A hx ih =>
    intro hA
    obtain ⟨B, hAB, hBQ, hBclosed⟩ :=
      ih (fun y hy => hA y (Finset.mem_insert_of_mem hy))
    obtain ⟨C, hxC, hCQ, hCclosed⟩ :=
      single (measure x) x rfl (hA x (Finset.mem_insert_self _ _))
    refine ⟨B ∪ C, ?_, ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact Finset.mem_union_right _ hxC
      · exact Finset.mem_union_left _ (hAB hy)
    · intro y hy
      exact (Finset.mem_union.mp hy).elim (hBQ y) (hCQ y)
    · intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact Finset.mem_union_left _ (hBclosed y hy)
      · exact Finset.mem_union_right _ (hCclosed y hy)

end ArtinNormalisers.Deligne5
