module

public import ArtinNormalisers.Artin.Basic
public import ArtinNormalisers.Artin.CoxeterNormalizer
public import TauCeti.GroupTheory.Coxeter.Matsumoto

/-!
# Lifting normalizers of standard Coxeter parabolics

A minimal representative of a normalizing coset conjugates the selected
simple generators in both directions. Matsumoto's theorem evaluates those
relations in the Artin group, using one fixed reduced word throughout.
Multiplication by an element of the Artin parabolic then gives an exact lift
of the original normalizing element. Neither the index type nor the
parabolic subgroup is assumed finite.
-/

@[expose] public section

namespace ArtinNormalisers.Artin

variable {I : Type*} (M : CoxeterMatrix I) (J : Set I)

/-- Agreement with the provider's standard Coxeter parabolic. -/
theorem coxeterParabolic_eq :
    coxeterParabolic M J = M.toCoxeterSystem.parabolic J := by
  apply le_antisymm
  · change Subgroup.closure (M.simple '' J) ≤ _
    apply (Subgroup.closure_le _).2
    rintro _ ⟨i, hi, rfl⟩
    have h := M.toCoxeterSystem.simple_mem_parabolic hi
    rw [CoxeterMatrix.toCoxeterSystem_simple] at h
    exact h
  · apply M.toCoxeterSystem.parabolic_le_iff.2
    intro i hi
    rw [CoxeterMatrix.toCoxeterSystem_simple]
    exact Subgroup.subset_closure ⟨i, hi, rfl⟩

private theorem conjugate_mem_parabolic (a : Group M)
    (hgen : ∀ i ∈ J, a * generator M i * a⁻¹ ∈ parabolic M J)
    {x : Group M} (hx : x ∈ parabolic M J) :
    a * x * a⁻¹ ∈ parabolic M J := by
  have hle : parabolic M J ≤ (parabolic M J).comap (MulAut.conj a).toMonoidHom := by
    change Subgroup.closure (generator M '' J) ≤ _
    apply (Subgroup.closure_le _).2
    rintro _ ⟨i, hi, rfl⟩
    exact hgen i hi
  exact hle hx

/-- Two directions of the generator relations suffice even for an infinite
set of selected generators. -/
theorem mem_normalizer_of_generator_relations (a : Group M)
    (hf : ∀ i ∈ J, ∃ j ∈ J, a * generator M i = generator M j * a)
    (hb : ∀ i ∈ J, ∃ j ∈ J, generator M i * a = a * generator M j) :
    a ∈ Subgroup.normalizer (parabolic M J : Set (Group M)) := by
  have hf' : ∀ i ∈ J, a * generator M i * a⁻¹ ∈ parabolic M J := by
    intro i hi
    obtain ⟨j, hj, hrel⟩ := hf i hi
    rw [hrel, mul_inv_cancel_right]
    exact Subgroup.subset_closure ⟨j, hj, rfl⟩
  have hb' : ∀ i ∈ J, a⁻¹ * generator M i * (a⁻¹)⁻¹ ∈ parabolic M J := by
    intro i hi
    obtain ⟨j, hj, hrel⟩ := hb i hi
    have hconj : a⁻¹ * generator M i * a = generator M j := by
      rw [mul_assoc, hrel]
      simp
    rw [inv_inv, hconj]
    exact Subgroup.subset_closure ⟨j, hj, rfl⟩
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · exact conjugate_mem_parabolic M J a hf'
  · intro hx
    have := conjugate_mem_parabolic M J a⁻¹ hb' hx
    simpa [mul_assoc] using this

/-- A reduced word for a minimal normalizing representative has a positive
Artin lift which normalizes the Artin parabolic. -/
theorem wordProd_mem_normalizer_of_minimal {d : M.Group}
    (hd : d ∈ Subgroup.normalizer (M.toCoxeterSystem.parabolic J : Set M.Group))
    (hmin : M.toCoxeterSystem.IsMinimalCosetRep J d)
    {δ : List I} (hδ : M.toCoxeterSystem.IsReduced δ)
    (hprod : M.toCoxeterSystem.wordProd δ = d) :
    wordProd M δ ∈ Subgroup.normalizer (parabolic M J : Set (Group M)) := by
  let cs := M.toCoxeterSystem
  change cs.wordProd δ = d at hprod
  have hbraid := TauCeti.ArtinGroup.prod_map_gen_braidWord M
  have hrel : ∀ i ∈ J, ∀ j ∈ J, d * cs.simple i = cs.simple j * d →
      wordProd M δ * generator M i = generator M j * wordProd M δ := by
    intro i hi j hj hij
    have hright := Coxeter.isReduced_append_simple_of_minimal cs hmin hδ hprod hi
    have hleft := Coxeter.isReduced_prepend_simple_of_minimal cs hd hmin hδ hprod hj
    have heq : cs.wordProd (δ ++ [i]) = cs.wordProd (j :: δ) := by
      rw [cs.wordProd_append, cs.wordProd_singleton, cs.wordProd_cons, hprod]
      exact hij
    have hm := TauCeti.matsumoto cs (generator M) hbraid hright hleft heq
    simpa [wordProd, List.map_append, List.prod_append] using hm
  apply mem_normalizer_of_generator_relations M J (wordProd M δ)
  · intro i hi
    obtain ⟨j, hj, hij⟩ := Coxeter.exists_conjugate_simple_of_minimal cs hd hmin hi
    refine ⟨j, hj, hrel i hi j hj ?_⟩
    rw [← hij]
    simp [mul_assoc]
  · intro i hi
    have hd' := (Subgroup.normalizer (cs.parabolic J : Set M.Group)).inv_mem hd
    have hmin' := Coxeter.minimal_inv_of_mem_normalizer cs hd hmin
    obtain ⟨j, hj, hij⟩ := Coxeter.exists_conjugate_simple_of_minimal cs hd' hmin' hi
    refine ⟨j, hj, (hrel j hj i hi ?_).symm⟩
    rw [← hij]
    simp [mul_assoc]

/-- Every Coxeter normalizer element has an actual Artin normalizer preimage.
This is stronger than surjectivity after quotienting by the parabolics. -/
theorem exists_normalizer_lift {w : M.Group}
    (hw : w ∈ Subgroup.normalizer (coxeterParabolic M J : Set M.Group)) :
    ∃ a : Group M,
      a ∈ Subgroup.normalizer (parabolic M J : Set (Group M)) ∧ projection M a = w := by
  let cs := M.toCoxeterSystem
  have hw' : w ∈ Subgroup.normalizer (cs.parabolic J : Set M.Group) := by
    rwa [coxeterParabolic_eq] at hw
  obtain ⟨d, v, hv, hdw, hd, hmin⟩ := Coxeter.exists_minimal_normalizer cs hw'
  obtain ⟨δ, hδ, hprod'⟩ := cs.exists_isReduced d
  have hprod := hprod'.symm
  have hβ := wordProd_mem_normalizer_of_minimal M J hd hmin hδ hprod
  have hv' : v⁻¹ ∈ (parabolic M J).map (projection M) := by
    rw [map_parabolic, coxeterParabolic_eq]
    exact (cs.parabolic J).inv_mem hv
  obtain ⟨b, hb, hbp⟩ := hv'
  refine ⟨wordProd M δ * b,
    (Subgroup.normalizer (parabolic M J : Set (Group M))).mul_mem hβ
      (Subgroup.le_normalizer hb), ?_⟩
  rw [map_mul, projection_wordProd, hprod, hbp, hdw]
  simp

end ArtinNormalisers.Artin
