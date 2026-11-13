module

public import TauCeti.GroupTheory.Coxeter.Parabolic
import Mathlib.Tactic.Group

/-!
# Minimal representatives in a Coxeter parabolic normalizer

Parabolic length additivity shows that a minimal representative which
normalizes a standard parabolic conjugates its simple generators among
themselves. No finiteness assumption is needed.
-/

@[expose] public section

namespace ArtinNormalisers.Coxeter

variable {I W : Type*} [Group W] {M : CoxeterMatrix I}
variable (cs : CoxeterSystem M W) {J : Set I} {d : W}

/-- Inversion preserves minimality for an element normalizing the parabolic. -/
theorem minimal_inv_of_mem_normalizer
    (hd : d ∈ Subgroup.normalizer (cs.parabolic J : Set W))
    (hmin : cs.IsMinimalCosetRep J d) :
    cs.IsMinimalCosetRep J d⁻¹ := by
  refine cs.isMinimalCosetRep_iff.mpr ?_
  intro i hi hdesc
  have hleft : cs.IsLeftDescent d i := cs.isRightDescent_inv_iff.mp hdesc
  have hc : d⁻¹ * cs.simple i * d ∈ cs.parabolic J :=
    (Subgroup.mem_normalizer_iff''.mp hd (cs.simple i)).mp (cs.simple_mem_parabolic hi)
  have hlen := cs.length_mul_of_isMinimalCosetRep hmin hc
  have heq : d * (d⁻¹ * cs.simple i * d) = cs.simple i * d := by group
  rw [heq] at hlen
  have hshort := cs.isLeftDescent_iff.mp hleft
  omega

/-- A minimal normalizer representative conjugates a simple generator of the
parabolic to another simple generator of that parabolic. -/
theorem exists_conjugate_simple_of_minimal
    (hd : d ∈ Subgroup.normalizer (cs.parabolic J : Set W))
    (hmin : cs.IsMinimalCosetRep J d) {i : I} (hi : i ∈ J) :
    ∃ j ∈ J, d * cs.simple i * d⁻¹ = cs.simple j := by
  let c := d * cs.simple i * d⁻¹
  have hc : c ∈ cs.parabolic J :=
    (Subgroup.mem_normalizer_iff.mp hd (cs.simple i)).mp (cs.simple_mem_parabolic hi)
  have hright := cs.length_mul_of_isMinimalCosetRep hmin (cs.simple_mem_parabolic hi)
  have hleft := cs.length_mul_of_isMinimalCosetRep
    (minimal_inv_of_mem_normalizer cs hd hmin) (inv_mem hc)
  rw [← mul_inv_rev, cs.length_inv, cs.length_inv, cs.length_inv] at hleft
  have heq : c * d = d * cs.simple i := by dsimp [c]; group
  rw [heq] at hleft
  rw [cs.length_simple] at hright
  have hclen : cs.length c = 1 := by omega
  obtain ⟨ω, hred, hJ, hprod⟩ := cs.exists_isReduced_wordProd_eq_of_mem_parabolic hc
  have hlen : ω.length = 1 := by rw [← hred.eq, hprod, hclen]
  obtain ⟨j, rfl⟩ := List.length_eq_one_iff.mp hlen
  refine ⟨j, hJ j (by simp), ?_⟩
  simpa only [cs.wordProd_singleton] using hprod.symm

/-- The reverse generator permutation is obtained from the inverse minimal
normalizer representative. -/
theorem exists_inverse_conjugate_simple_of_minimal
    (hd : d ∈ Subgroup.normalizer (cs.parabolic J : Set W))
    (hmin : cs.IsMinimalCosetRep J d) {i : I} (hi : i ∈ J) :
    ∃ j ∈ J, d⁻¹ * cs.simple i * d = cs.simple j := by
  simpa only [inv_inv] using
    exists_conjugate_simple_of_minimal cs (inv_mem hd)
      (minimal_inv_of_mem_normalizer cs hd hmin) hi

/-- Appending a parabolic simple generator to a reduced word of a minimal
representative preserves reducedness. -/
theorem isReduced_append_simple_of_minimal
    (hmin : cs.IsMinimalCosetRep J d) {ω : List I}
    (hω : cs.IsReduced ω) (hprod : cs.wordProd ω = d) {i : I} (hi : i ∈ J) :
    cs.IsReduced (ω ++ [i]) := by
  have hlen := cs.length_mul_of_isMinimalCosetRep hmin (cs.simple_mem_parabolic hi)
  rw [cs.length_simple] at hlen
  change cs.length (cs.wordProd (ω ++ [i])) = (ω ++ [i]).length
  rw [cs.wordProd_append, cs.wordProd_singleton, hprod, hlen,
    List.length_append, List.length_singleton, ← hω.eq, hprod]

/-- Prepending a parabolic simple generator to a reduced word of a minimal
normalizer representative preserves reducedness. -/
theorem isReduced_prepend_simple_of_minimal
    (hd : d ∈ Subgroup.normalizer (cs.parabolic J : Set W))
    (hmin : cs.IsMinimalCosetRep J d) {ω : List I}
    (hω : cs.IsReduced ω) (hprod : cs.wordProd ω = d) {i : I} (hi : i ∈ J) :
    cs.IsReduced (i :: ω) := by
  have hlen := cs.length_mul_of_isMinimalCosetRep
    (minimal_inv_of_mem_normalizer cs hd hmin) (cs.simple_mem_parabolic hi)
  have heq : d⁻¹ * cs.simple i = (cs.simple i * d)⁻¹ := by simp
  rw [heq, cs.length_inv, cs.length_inv, cs.length_simple] at hlen
  change cs.length (cs.wordProd (i :: ω)) = (i :: ω).length
  rw [cs.wordProd_cons, hprod, hlen, List.length_cons, ← hω.eq, hprod]

/-- A normalizer element can be adjusted on the right by a parabolic element
to obtain a minimal representative which still normalizes the parabolic. -/
theorem exists_minimal_normalizer {w : W}
    (hw : w ∈ Subgroup.normalizer (cs.parabolic J : Set W)) :
    ∃ d v, v ∈ cs.parabolic J ∧ d = w * v ∧
      d ∈ Subgroup.normalizer (cs.parabolic J : Set W) ∧ cs.IsMinimalCosetRep J d := by
  obtain ⟨v, hv, hmin⟩ := cs.exists_isMinimalCosetRep J w
  exact ⟨w * v, v, hv, rfl,
    mul_mem hw ((cs.parabolic J).le_normalizer hv), hmin⟩

end ArtinNormalisers.Coxeter
