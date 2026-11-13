import ArtinRibbons.RibbonGroupoid
import OAI.Topology.ArtinGroups.Harmonic.RestrictedArtinHom

/-!
# Actual parabolic fundamental elements

For finite Coxeter groups, the fundamental element of each standard
parabolic is constructed by taking the positive lift of an actual longest
element in the restricted Coxeter presentation, mapping into the ambient
Artin presentation, and applying the proved generator-preserving parent
equivalence. No finite-rank assumption is added to finite Coxeter type.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Ribbon2

open OAI.HarmonicArtin OAI.HarmonicArtin.CoxeterExchange OAI.HarmonicArtin.Geometric

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group]

include M

theorem fundamental_finite_index : Finite I :=
  Finite.of_injective M.simple M.toCoxeterSystem.simple_injective

/-- Finiteness of the actual restricted Coxeter presentation follows from
its proved embedding into the finite ambient parabolic. -/
theorem restrictedParabolic_finite (J : Set I) : Finite (restrictedMatrix M J).Group := by
  classical
  let := fundamental_finite_index M
  let := Fintype.ofFinite I
  apply restricted_finite M J
  unfold IsSpherical
  infer_instance

theorem exists_parabolicLongestRestricted (J : Set I) :
    ∃ z : (restrictedMatrix M J).Group, ∀ w,
      (restrictedMatrix M J).toCoxeterSystem.length w ≤
        (restrictedMatrix M J).toCoxeterSystem.length z := by
  let := restrictedParabolic_finite M J
  exact exists_longest (restrictedMatrix M J).toCoxeterSystem

/-- A chosen longest element of the actual restricted Coxeter group. -/
noncomputable def parabolicLongestRestricted (J : Set I) : (restrictedMatrix M J).Group :=
  Classical.choose (exists_parabolicLongestRestricted M J)

theorem parabolicLongestRestricted_max (J : Set I) (w : (restrictedMatrix M J).Group) :
    (restrictedMatrix M J).toCoxeterSystem.length w ≤
      (restrictedMatrix M J).toCoxeterSystem.length (parabolicLongestRestricted M J) :=
  Classical.choose_spec (exists_parabolicLongestRestricted M J) w

/-- The ambient image of the actual parabolic longest element. -/
noncomputable def parabolicLongest (J : Set I) : M.Group :=
  restrictionHom M J (parabolicLongestRestricted M J)

/-- The actual Artin fundamental element, not an abstract symbol. -/
noncomputable def parabolicDelta (J : Set I) : Artin.Group M :=
  toParent M (restrictedArtinHom M J
    (positiveLift (restrictedMatrix M J) (parabolicLongestRestricted M J)))

theorem parabolicDelta_eq_wordProd (J : Set I) :
    parabolicDelta M J = Artin.wordProd M
      ((reducedExpression (restrictedMatrix M J) (parabolicLongestRestricted M J)).map
        Subtype.val) := by
  unfold parabolicDelta positiveLift
  rw [restrictedArtinHom_word]
  exact presentationEquiv_word M _

theorem parabolicDelta_mem_positiveParabolic (J : Set I) :
    parabolicDelta M J ∈ actualPositiveParabolic M J := by
  rw [parabolicDelta_eq_wordProd]
  apply wordProd_mem_actualPositiveParabolic
  intro i hi
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
  exact j.property

theorem projection_parabolicDelta (J : Set I) :
    Artin.projection M (parabolicDelta M J) = parabolicLongest M J := by
  rw [parabolicDelta_eq_wordProd, Artin.projection_wordProd]
  rw [← restriction_wordProd]
  exact congrArg (restrictionHom M J)
    (wordCoxeter_reducedExpression (restrictedMatrix M J) (parabolicLongestRestricted M J))

theorem parabolicLongest_mem_parabolic (J : Set I) :
    parabolicLongest M J ∈ Artin.coxeterParabolic M J :=
  restrictionHom_mem_parabolic M J _

/-- Positive lifting commutes with the actual parabolic inclusion, proved
by the reduced-word and length-preservation theorems. -/
theorem restrictedArtinHom_positiveLift (J : Set I) (w : (restrictedMatrix M J).Group) :
    restrictedArtinHom M J (positiveLift (restrictedMatrix M J) w) =
      positiveLift M (restrictionHom M J w) := by
  classical
  let := fundamental_finite_index M
  let := Fintype.ofFinite I
  let u := reducedExpression (restrictedMatrix M J) w
  have hr : M.toCoxeterSystem.IsReduced (u.map Subtype.val) :=
    (restriction_reduced_iff M J u).mpr (reducedExpression_reduced _ _)
  have he : wordCoxeter M (u.map Subtype.val) = restrictionHom M J w := by
    change M.toCoxeterSystem.wordProd (u.map Subtype.val) = restrictionHom M J w
    rw [← restriction_wordProd]
    exact congrArg (restrictionHom M J) (wordCoxeter_reducedExpression _ _)
  rw [← he, positiveLift_word M _ hr]
  exact restrictedArtinHom_word M J u

theorem parabolicDelta_eq_globalPositiveLift (J : Set I) :
    parabolicDelta M J = toParent M (positiveLift M (parabolicLongest M J)) := by
  unfold parabolicDelta parabolicLongest
  rw [restrictedArtinHom_positiveLift]

/-- The longest parabolic element acts on selected generators by an
actual permutation relation, transported to the unchanged parent group. -/
theorem parabolicDelta_generator_permutation (J : Set I) (i : J) :
    ∃ j : J, parabolicDelta M J * Artin.generator M i =
      Artin.generator M j * parabolicDelta M J := by
  classical
  let := fundamental_finite_index M
  let := Fintype.ofFinite I
  obtain ⟨j, hij⟩ := longest_conjugates_simple (restrictedMatrix M J).toCoxeterSystem
    (parabolicLongestRestricted M J) (parabolicLongestRestricted_max M J) i
  refine ⟨j, ?_⟩
  have h := positiveLift_longest_conjugate (restrictedMatrix M J)
    (parabolicLongestRestricted M J) (parabolicLongestRestricted_max M J) i j hij
  have he := congrArg (fun a => toParent M (restrictedArtinHom M J a)) h
  simpa only [map_mul, restrictedArtinHom_generator, toParent_generator, parabolicDelta] using he

/-- The inverse direction uses involutivity of the longest Coxeter element
and the same positive lift, rather than identifying a positive inverse lift
with the inverse Artin element. -/
theorem parabolicDelta_generator_permutation_reverse (J : Set I) (i : J) :
    ∃ j : J, Artin.generator M i * parabolicDelta M J =
      parabolicDelta M J * Artin.generator M j := by
  classical
  let := fundamental_finite_index M
  let := Fintype.ofFinite I
  let z := parabolicLongestRestricted M J
  have hz := parabolicLongestRestricted_max M J
  obtain ⟨j, hij⟩ := longest_conjugates_simple (restrictedMatrix M J).toCoxeterSystem z hz i
  have hzz := longest_mul_self (restrictedMatrix M J).toCoxeterSystem z hz
  have hji : z * (restrictedMatrix M J).toCoxeterSystem.simple j * z =
      (restrictedMatrix M J).toCoxeterSystem.simple i := by
    rw [← hij]
    calc
      z * (z * (restrictedMatrix M J).toCoxeterSystem.simple i * z) * z =
          (z * z) * (restrictedMatrix M J).toCoxeterSystem.simple i * (z * z) := by group
      _ = _ := by rw [hzz, one_mul, mul_one]
  have h := positiveLift_longest_conjugate (restrictedMatrix M J) z hz j i hji
  have he := congrArg (fun a => toParent M (restrictedArtinHom M J a)) h
  refine ⟨j, ?_⟩
  simpa only [map_mul, restrictedArtinHom_generator, toParent_generator, parabolicDelta, z] using he.symm

theorem parabolicDelta_isRibbon (J : Set I) :
    IsRibbon M ⟨J⟩ ⟨J⟩ (parabolicDelta M J) := by
  let d := parabolicDelta M J
  have hf : actualPositiveParabolic M J ≤
      (actualPositiveParabolic M J).comap (MulAut.conj d).toMonoidHom := by
    apply Submonoid.closure_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨j, hj⟩ := parabolicDelta_generator_permutation M J ⟨i, hi⟩
    change d * Artin.generator M i * d⁻¹ ∈ actualPositiveParabolic M J
    rw [hj, mul_inv_cancel_right]
    exact generator_mem_actualPositiveParabolic M J j.property
  have hb : actualPositiveParabolic M J ≤
      (actualPositiveParabolic M J).comap (MulAut.conj d⁻¹).toMonoidHom := by
    apply Submonoid.closure_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    obtain ⟨j, hj⟩ := parabolicDelta_generator_permutation_reverse M J ⟨i, hi⟩
    change d⁻¹ * Artin.generator M i * (d⁻¹)⁻¹ ∈ actualPositiveParabolic M J
    have he : d⁻¹ * Artin.generator M i * d = Artin.generator M j := by
      rw [mul_assoc, hj]
      simp [d]
    simpa only [inv_inv, he] using generator_mem_actualPositiveParabolic M J j.property
  intro b
  constructor
  · intro hb'
    have h := hb hb'
    change d⁻¹ * b * (d⁻¹)⁻¹ ∈ actualPositiveParabolic M J at h
    simpa only [inv_inv] using h
  · intro hb'
    have h := hf hb'
    change d * (d⁻¹ * b * d) * d⁻¹ ∈ actualPositiveParabolic M J at h
    simpa [mul_assoc] using h

omit [Finite M.Group] in
theorem restrictionHom_range (J : Set I) :
    (restrictionHom M J).range = Artin.coxeterParabolic M J := by
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    exact restrictionHom_mem_parabolic M J w
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨(restrictedMatrix M J).simple ⟨i, hi⟩, restrictionHom_simple M J ⟨i, hi⟩⟩

theorem parabolicLongest_max (J : Set I) {w : M.Group}
    (hw : w ∈ Artin.coxeterParabolic M J) :
    M.toCoxeterSystem.length w ≤ M.toCoxeterSystem.length (parabolicLongest M J) := by
  classical
  let := fundamental_finite_index M
  let := Fintype.ofFinite I
  rw [← restrictionHom_range M J] at hw
  obtain ⟨v, rfl⟩ := hw
  simp only [parabolicLongest, restriction_length]
  exact parabolicLongestRestricted_max M J v

theorem parabolicLongest_mul_self (J : Set I) :
    parabolicLongest M J * parabolicLongest M J = 1 := by
  classical
  let := fundamental_finite_index M
  let := Fintype.ofFinite I
  rw [parabolicLongest, ← map_mul,
    longest_mul_self (restrictedMatrix M J).toCoxeterSystem
      (parabolicLongestRestricted M J) (parabolicLongestRestricted_max M J), map_one]

/-- The index permutation induced by the actual fundamental element. -/
noncomputable def parabolicTwistIndex (J : Set I) (i : J) : J :=
  Classical.choose (parabolicDelta_generator_permutation M J i)

theorem parabolicTwistIndex_relation (J : Set I) (i : J) :
    parabolicDelta M J * Artin.generator M i =
      Artin.generator M (parabolicTwistIndex M J i) * parabolicDelta M J :=
  Classical.choose_spec (parabolicDelta_generator_permutation M J i)

theorem parabolicTwistIndex_involutive (J : Set I) :
    Function.Involutive (parabolicTwistIndex M J) := by
  intro i
  have hrel (j : J) : parabolicLongest M J * M.simple j * parabolicLongest M J =
      M.simple (parabolicTwistIndex M J j) := by
    have h := congrArg (Artin.projection M) (parabolicTwistIndex_relation M J j)
    simp only [map_mul, projection_parabolicDelta, Artin.projection_generator] at h
    rw [h, mul_assoc, parabolicLongest_mul_self, mul_one]
  apply Subtype.ext
  apply M.toCoxeterSystem.simple_injective
  change M.simple (parabolicTwistIndex M J (parabolicTwistIndex M J i) : I) = M.simple i
  rw [← hrel, ← hrel]
  calc
    parabolicLongest M J * (parabolicLongest M J * M.simple i * parabolicLongest M J) *
        parabolicLongest M J =
      (parabolicLongest M J * parabolicLongest M J) * M.simple i *
        (parabolicLongest M J * parabolicLongest M J) := by group
    _ = M.simple i := by rw [parabolicLongest_mul_self, one_mul, mul_one]

/-- The longest-element involution on the selected simple-generator indices. -/
noncomputable def parabolicTwist (J : Set I) : J ≃ J where
  toFun := parabolicTwistIndex M J
  invFun := parabolicTwistIndex M J
  left_inv := parabolicTwistIndex_involutive M J
  right_inv := parabolicTwistIndex_involutive M J

theorem parabolicTwist_relation (J : Set I) (i : J) :
    parabolicDelta M J * Artin.generator M i =
      Artin.generator M (parabolicTwist M J i) * parabolicDelta M J :=
  parabolicTwistIndex_relation M J i

theorem parabolicTwist_relation_reverse (J : Set I) (i : J) :
    Artin.generator M i * parabolicDelta M J =
      parabolicDelta M J * Artin.generator M (parabolicTwist M J i) := by
  have h := parabolicTwistIndex_relation M J (parabolicTwistIndex M J i)
  rw [parabolicTwistIndex_involutive M J i] at h
  exact h.symm

/-- The explicitly conjugated index set `ι_K(J)`. This definition is made
for every subset, while the ratio ribbon theorem assumes `J ⊆ K`. -/
noncomputable def parabolicTwistImage (K J : Set I) : Set I :=
  (fun i : K => (parabolicTwist M K i : I)) '' {i : K | (i : I) ∈ J}

omit [Finite M.Group] in
theorem isRibbon_of_generator_conjugates (J : Set I) (f : J → I) (β : Artin.Group M)
    (hf : ∀ i : J, β⁻¹ * Artin.generator M i * β = Artin.generator M (f i)) :
    IsRibbon M ⟨J⟩ ⟨Set.range f⟩ β := by
  let c := (MulAut.conj β⁻¹).toMonoidHom
  have hs : c '' (Artin.generator M '' J) = Artin.generator M '' Set.range f := by
    ext z
    constructor
    · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
      refine ⟨f ⟨i, hi⟩, ⟨⟨i, hi⟩, rfl⟩, ?_⟩
      change Artin.generator M (f ⟨i, hi⟩) = β⁻¹ * Artin.generator M i * (β⁻¹)⁻¹
      simpa only [inv_inv] using (hf ⟨i, hi⟩).symm
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      refine ⟨Artin.generator M i, ⟨i, i.property, rfl⟩, ?_⟩
      change β⁻¹ * Artin.generator M i * (β⁻¹)⁻¹ = Artin.generator M (f i)
      simpa only [inv_inv] using hf i
  have hm : (actualPositiveParabolic M J).map c = actualPositiveParabolic M (Set.range f) := by
    rw [actualPositiveParabolic, MonoidHom.map_mclosure, hs]
    rfl
  intro a
  constructor
  · intro ha
    have h : c a ∈ actualPositiveParabolic M (Set.range f) := by
      rw [← hm]
      exact ⟨a, ha, rfl⟩
    change β⁻¹ * a * (β⁻¹)⁻¹ ∈ actualPositiveParabolic M (Set.range f) at h
    simpa only [inv_inv] using h
  · intro ha
    have ha' : c a ∈ actualPositiveParabolic M (Set.range f) := by
      change β⁻¹ * a * (β⁻¹)⁻¹ ∈ actualPositiveParabolic M (Set.range f)
      simpa only [inv_inv] using ha
    rw [← hm] at ha'
    obtain ⟨b, hb, hba⟩ := ha'
    have he : b = a := (MulAut.conj β⁻¹).injective hba
    exact he ▸ hb

/-- Every parabolic element is a length-additive left factor of its
parabolic longest element, in the ambient Coxeter length. -/
theorem parabolicLongest_left_length (J : Set I) {w : M.Group}
    (hw : w ∈ Artin.coxeterParabolic M J) :
    M.toCoxeterSystem.length w +
      M.toCoxeterSystem.length (w⁻¹ * parabolicLongest M J) =
        M.toCoxeterSystem.length (parabolicLongest M J) := by
  classical
  let := fundamental_finite_index M
  let := Fintype.ofFinite I
  rw [← restrictionHom_range M J] at hw
  obtain ⟨v, rfl⟩ := hw
  let z := parabolicLongestRestricted M J
  have hz := parabolicLongestRestricted_max M J
  have hzz := longest_mul_self (restrictedMatrix M J).toCoxeterSystem z hz
  have hzi : z⁻¹ = z := by
    calc
      z⁻¹ = z⁻¹ * (z * z) := by rw [hzz, mul_one]
      _ = z := by group
  have h := length_mul_of_all_descents (restrictedMatrix M J).toCoxeterSystem z
    (all_descents_of_longest (restrictedMatrix M J).toCoxeterSystem z hz) v
  have hinv : (restrictedMatrix M J).toCoxeterSystem.length (v⁻¹ * z) =
      (restrictedMatrix M J).toCoxeterSystem.length (z * v) := by
    rw [← (restrictedMatrix M J).toCoxeterSystem.length_inv (z * v)]
    simp only [mul_inv_rev, hzi]
  simp only [parabolicLongest, ← map_inv, ← map_mul, restriction_length]
  change (restrictedMatrix M J).toCoxeterSystem.length v +
    (restrictedMatrix M J).toCoxeterSystem.length (v⁻¹ * z) =
      (restrictedMatrix M J).toCoxeterSystem.length z
  rw [hinv]
  omega

theorem parabolicDelta_ratio_positive (J K : Set I) (hJK : J ⊆ K) :
    (parabolicDelta M J)⁻¹ * parabolicDelta M K ∈ actualPositiveParabolic M K := by
  classical
  let := fundamental_finite_index M
  let := Fintype.ofFinite I
  have hmono : Artin.coxeterParabolic M J ≤ Artin.coxeterParabolic M K :=
    Subgroup.closure_mono (Set.image_mono hJK)
  have hwJ := hmono (parabolicLongest_mem_parabolic M J)
  have hlen := parabolicLongest_left_length M K hwJ
  have he := positiveLift_mul M (parabolicLongest M J)
    ((parabolicLongest M J)⁻¹ * parabolicLongest M K) (by
      simpa only [mul_inv_cancel_left] using hlen.symm)
  simp only [mul_inv_cancel_left] at he
  have hw : (parabolicLongest M J)⁻¹ * parabolicLongest M K ∈
      Artin.coxeterParabolic M K := (Artin.coxeterParabolic M K).mul_mem
        ((Artin.coxeterParabolic M K).inv_mem hwJ) (parabolicLongest_mem_parabolic M K)
  rw [← restrictionHom_range M K] at hw
  obtain ⟨v, hv⟩ := hw
  have hd : (parabolicDelta M J)⁻¹ * parabolicDelta M K =
      toParent M (restrictedArtinHom M K (positiveLift (restrictedMatrix M K) v)) := by
    rw [restrictedArtinHom_positiveLift, hv, parabolicDelta_eq_globalPositiveLift,
      parabolicDelta_eq_globalPositiveLift, he, map_mul]
    simp
  rw [hd]
  change toParent M (restrictedArtinHom M K
    (wordArtin (restrictedMatrix M K) (reducedExpression (restrictedMatrix M K) v))) ∈ _
  rw [restrictedArtinHom_word]
  rw [show toParent M (wordArtin M
    ((reducedExpression (restrictedMatrix M K) v).map Subtype.val)) =
      Artin.wordProd M ((reducedExpression (restrictedMatrix M K) v).map Subtype.val) from
        presentationEquiv_word M _]
  apply wordProd_mem_actualPositiveParabolic
  intro i hi
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
  exact j.property

theorem parabolicDelta_ratio_conjugates_generator (J K : Set I) (hJK : J ⊆ K) (i : J) :
    ((parabolicDelta M J)⁻¹ * parabolicDelta M K)⁻¹ * Artin.generator M i *
        ((parabolicDelta M J)⁻¹ * parabolicDelta M K) =
      Artin.generator M (parabolicTwist M K
        ⟨parabolicTwist M J i, hJK (parabolicTwist M J i).property⟩) := by
  let j : K := ⟨parabolicTwist M J i, hJK (parabolicTwist M J i).property⟩
  calc
    ((parabolicDelta M J)⁻¹ * parabolicDelta M K)⁻¹ * Artin.generator M i *
        ((parabolicDelta M J)⁻¹ * parabolicDelta M K) =
      (parabolicDelta M K)⁻¹ *
        (parabolicDelta M J * Artin.generator M i * (parabolicDelta M J)⁻¹) *
          parabolicDelta M K := by group
    _ = (parabolicDelta M K)⁻¹ * Artin.generator M j * parabolicDelta M K := by
      rw [parabolicTwist_relation, mul_inv_cancel_right]
    _ = Artin.generator M (parabolicTwist M K j) := by
      rw [mul_assoc, parabolicTwist_relation_reverse]
      simp

/-- Every nested-parabolic ratio has its genuine conjugated-index endpoint.
No elementary labels are discarded by imposing this as a selection filter. -/
theorem parabolicDelta_ratio_isRibbon (J K : Set I) (hJK : J ⊆ K) :
    IsRibbon M ⟨J⟩ ⟨parabolicTwistImage M K J⟩
      ((parabolicDelta M J)⁻¹ * parabolicDelta M K) := by
  let f : J → I := fun i => parabolicTwist M K
    ⟨parabolicTwist M J i, hJK (parabolicTwist M J i).property⟩
  have heq : Set.range f = parabolicTwistImage M K J := by
    ext k
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨⟨parabolicTwist M J i, hJK (parabolicTwist M J i).property⟩,
        (parabolicTwist M J i).property, rfl⟩
    · rintro ⟨i, hi, hik⟩
      let j : J := ⟨i, hi⟩
      obtain ⟨s, hs⟩ := (parabolicTwist M J).surjective j
      refine ⟨s, ?_⟩
      have hsub : (⟨parabolicTwist M J s, hJK (parabolicTwist M J s).property⟩ : K) = i := by
        apply Subtype.ext
        exact congrArg (fun t : J => (t : I)) hs
      dsimp only [f]
      rw [hsub]
      exact hik
  have h := isRibbon_of_generator_conjugates M J f
    ((parabolicDelta M J)⁻¹ * parabolicDelta M K)
      (parabolicDelta_ratio_conjugates_generator M J K hJK)
  rw [heq] at h
  exact h

/-- The actual outside elementary label of equation (5.3). Its positivity
and endpoint ribbon relation are separate theorems, not fields of this
definition. -/
noncomputable def elementaryMu (J : Set I) (a : I) : Artin.Group M :=
  (parabolicDelta M J)⁻¹ * parabolicDelta M (insert a J)

theorem elementaryMu_positive (J : Set I) (a : I) :
    elementaryMu M J a ∈ actualPositiveParabolic M (insert a J) :=
  parabolicDelta_ratio_positive M J (insert a J) (Set.subset_insert a J)

theorem elementaryMu_isRibbon (J : Set I) (a : I) :
    IsRibbon M ⟨J⟩ ⟨parabolicTwistImage M (insert a J) J⟩ (elementaryMu M J a) :=
  parabolicDelta_ratio_isRibbon M J (insert a J) (Set.subset_insert a J)

/-- For an outside generator, the endpoint is exactly the source formula
`(J+a) - ι_(J+a)(a)`. -/
theorem elementaryMu_endpoint (J : Set I) (a : I) (ha : a ∉ J) :
    parabolicTwistImage M (insert a J) J =
      insert a J \ {(parabolicTwist M (insert a J) ⟨a, Set.mem_insert a J⟩ : I)} := by
  classical
  let e := parabolicTwist M (insert a J)
  ext k
  change k ∈ (fun i : ↥(insert a J) => (e i : I)) '' {i : ↥(insert a J) | (i : I) ∈ J} ↔ _
  simp only [Set.mem_sdiff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    refine ⟨(e i).property, ?_⟩
    intro heq
    have hi' : i = ⟨a, Set.mem_insert a J⟩ := e.injective (Subtype.ext heq)
    have himem : (i : I) ∈ J := hi
    rw [hi'] at himem
    exact ha himem
  · rintro ⟨hk, hne⟩
    let i := e.symm ⟨k, hk⟩
    have hik : (e i : I) = k := congrArg Subtype.val (e.apply_symm_apply ⟨k, hk⟩)
    have hi : (i : I) ∈ J := by
      rcases Set.mem_insert_iff.mp i.property with hia | hi
      · have hi' : i = ⟨a, Set.mem_insert a J⟩ := Subtype.ext hia
        rw [hi'] at hik
        exact False.elim (hne hik.symm)
      · exact hi
    exact ⟨i, hi, hik⟩

omit [Finite M.Group] in
theorem generator_mem_actualPositiveParabolic_iff (J : Set I) (i : I) :
    Artin.generator M i ∈ actualPositiveParabolic M J ↔ i ∈ J := by
  constructor
  · intro hi
    have hs : M.simple i ∈ Artin.coxeterParabolic M J := by
      rw [← Artin.map_parabolic]
      exact Subgroup.mem_map.mpr
        ⟨Artin.generator M i, actualPositiveParabolic_le_parabolic M J hi,
          Artin.projection_generator M i⟩
    obtain ⟨u, hu, hr, he⟩ :=
      (mem_parabolic_iff_reduced_word M.toCoxeterSystem J (M.simple i)).mp hs
    have hlen : u.length = 1 := by
      rw [← hr.eq, he]
      exact M.toCoxeterSystem.length_simple i
    obtain ⟨j, rfl⟩ := List.length_eq_one_iff.mp hlen
    have hji : j = i := M.toCoxeterSystem.simple_injective
      (by simpa only [CoxeterSystem.wordProd_singleton,
        CoxeterMatrix.toCoxeterSystem_simple] using he)
    exact hji ▸ hu j (by simp)
  · exact generator_mem_actualPositiveParabolic M J

omit [Finite M.Group] in
/-- The actual positive conjugation condition determines the target index
set uniquely. This does not discard elementary labels without an endpoint. -/
theorem isRibbon_target_indices_unique {X Y Z : RibbonObject M} {β : Artin.Group M}
    (hY : IsRibbon M X Y β) (hZ : IsRibbon M X Z β) : Y.indices = Z.indices := by
  have sub {U V : RibbonObject M} (hU : IsRibbon M X U β) (hV : IsRibbon M X V β) :
      U.indices ⊆ V.indices := by
    intro i hi
    have hgen := generator_mem_actualPositiveParabolic M U.indices hi
    let a := β * Artin.generator M i * β⁻¹
    have ha : a ∈ actualPositiveParabolic M X.indices :=
      (hU a).mpr (by simpa [a, mul_assoc] using hgen)
    have hgen' : Artin.generator M i ∈ actualPositiveParabolic M V.indices := by
      simpa [a, mul_assoc] using (hV a).mp ha
    exact (generator_mem_actualPositiveParabolic_iff M V.indices i).mp hgen'
  exact Set.Subset.antisymm (sub hY hZ) (sub hZ hY)

theorem elementaryMu_endpoint_unique (J : Set I) (a : I) {K : Set I}
    (h : IsRibbon M ⟨J⟩ ⟨K⟩ (elementaryMu M J a)) :
    K = parabolicTwistImage M (insert a J) J :=
  isRibbon_target_indices_unique M h (elementaryMu_isRibbon M J a)

/-- Every actual elementary label has exactly one endpoint, including all
outside labels required by Definition 5.5. -/
theorem elementaryMu_unique_endpoint (J : Set I) (a : I) :
    ∃! K : Set I, IsRibbon M ⟨J⟩ ⟨K⟩ (elementaryMu M J a) :=
  ⟨parabolicTwistImage M (insert a J) J, elementaryMu_isRibbon M J a,
    fun _ h => elementaryMu_endpoint_unique M J a h⟩

/-- The elementary label as an actual morphism of the larger ribbon
groupoid, with the proved endpoint. -/
noncomputable def elementaryRibbon (J : Set I) (a : I) :
    RibbonHom M ⟨J⟩ ⟨parabolicTwistImage M (insert a J) J⟩ :=
  ⟨elementaryMu M J a, elementaryMu_isRibbon M J a⟩

@[simp]
theorem elementaryRibbon_value (J : Set I) (a : I) :
    (elementaryRibbon M J a).val = elementaryMu M J a := rfl

end ArtinNormalisers.Ribbon2
