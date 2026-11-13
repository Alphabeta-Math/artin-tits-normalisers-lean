import ArtinRibbons.FractionNormalForms
import ArtinRibbons.CofinalRibbons

/-!
# The actual reduced ribbon complement in the Artin normalizer

Coprime positive fraction saturation proves trivial intersection with the
selected parabolic. Cofinal positive ribbon fractions and positive normalizer
stripping provide the actual factorization, hence the canonical quotient
isomorphism. No normalizer factorization is included in a definition.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Ribbon2

open OAI.HarmonicArtin

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group]

private theorem selected_prefix_eq_one_of_reduced (J : Set I) {r : Artin.Group M}
    (hr : IsLeftParabolicallyReduced M J r) (c d : PositiveArtin M)
    (hc : positiveToParent M c ∈ actualPositiveParabolic M J)
    (hprod : r = positiveToParent M c * positiveToParent M d) : c = 1 := by
  obtain ⟨w, rfl⟩ := positive_word_surjective M c
  cases w with
  | nil => rfl
  | cons i w =>
    have hsupport := (positiveToParent_mem_iff_support M J _).1 hc
    have hi : i ∈ J := hsupport (by simp)
    apply False.elim
    apply hr i hi (positiveToParent M (wordPositive M w * d)) (positiveActualHom M _).property
    simpa [map_mul, positiveToParent_word, Artin.wordProd, mul_assoc] using hprod.symm

/-- Two positive left-reduced representatives of one parabolic coset agree. -/
theorem positive_leftReduced_fraction_parabolic_eq (J : Set I) {a b : Artin.Group M}
    (ha : a ∈ actualPositiveParabolic M Set.univ)
    (hb : b ∈ actualPositiveParabolic M Set.univ)
    (hared : IsLeftParabolicallyReduced M J a)
    (hbred : IsLeftParabolicallyReduced M J b)
    (hpar : a * b⁻¹ ∈ Artin.parabolic M J) : a = b := by
  rw [← positiveToParent_mrange_eq_actual M] at ha hb
  obtain ⟨a, rfl⟩ := ha
  obtain ⟨b, rfl⟩ := hb
  obtain ⟨d, c, z, hc, hz, hcop⟩ := exists_right_reduced_pair M a b
  have hmem : positiveToParent M c * (positiveToParent M z)⁻¹ ∈ Artin.parabolic M J := by
    have he : positiveToParent M a * (positiveToParent M b)⁻¹ =
        positiveToParent M c * (positiveToParent M z)⁻¹ := by
      rw [hc, hz, map_mul, map_mul]
      group
    rwa [he] at hpar
  obtain ⟨hcJ, hzJ⟩ := right_coprime_fraction_parabolic M J c z hcop hmem
  have hc1 := selected_prefix_eq_one_of_reduced M J hared c d hcJ
    (by rw [hc, map_mul])
  have hz1 := selected_prefix_eq_one_of_reduced M J hbred z d hzJ
    (by rw [hz, map_mul])
  rw [hc, hz, hc1, hz1]

/-- Every group element has a positive numerator over a power of the actual
central global fundamental square. -/
theorem positive_fraction_globalDelta_square (β : Artin.Group M) :
    ∃ (n : ℕ) (p : Artin.Group M), p ∈ actualPositiveParabolic M Set.univ ∧
      β = p * (((parabolicDelta M Set.univ) ^ 2) ^ n)⁻¹ := by
  let Ω := (parabolicDelta M Set.univ) ^ 2
  have hβ : β ∈ Subgroup.closure (Set.range (Artin.generator M)) := by
    rw [Artin.closure_range_generator M]
    exact Subgroup.mem_top β
  change ∃ n p, p ∈ actualPositiveParabolic M Set.univ ∧ β = p * (Ω ^ n)⁻¹
  induction hβ using Subgroup.closure_induction_left with
  | one => exact ⟨0, 1, Submonoid.one_mem _, by simp⟩
  | mul_left a ha y hy ih =>
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨n, p, hp, rfl⟩ := ih
    refine ⟨n, Artin.generator M i * p,
      Submonoid.mul_mem _ (generator_mem_actualPositiveParabolic M Set.univ (Set.mem_univ i)) hp,
      ?_⟩
    group
  | inv_mul_cancel a ha y hy ih =>
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨n, p, hp, rfl⟩ := ih
    obtain ⟨q, hq, hdelta⟩ :=
      (generator_leftDivides_parabolicDelta_iff M Set.univ i).2 (Set.mem_univ i)
    let v := q * parabolicDelta M Set.univ
    have hv : v ∈ actualPositiveParabolic M Set.univ :=
      Submonoid.mul_mem _ hq (parabolicDelta_mem_positiveParabolic M Set.univ)
    have hprod : Artin.generator M i * v = Ω := by
      dsimp only [v, Ω]
      rw [← mul_assoc, ← hdelta, pow_two]
    have hinv : (Artin.generator M i)⁻¹ = v * Ω⁻¹ := by
      apply (eq_mul_inv_iff_mul_eq).2
      rw [← hprod]
      group
    have hcomm : Ω⁻¹ * p = p * Ω⁻¹ :=
      ((globalDelta_square_commute M p).inv_left).eq
    refine ⟨n + 1, v * p, Submonoid.mul_mem _ hv hp, ?_⟩
    calc
      (Artin.generator M i)⁻¹ * (p * (Ω ^ n)⁻¹) =
          v * (Ω⁻¹ * p) * (Ω ^ n)⁻¹ := by rw [hinv]; group
      _ = v * (p * Ω⁻¹) * (Ω ^ n)⁻¹ := by rw [hcomm]
      _ = (v * p) * (Ω ^ (n + 1))⁻¹ := by rw [pow_succ, mul_inv_rev]; group

/-- Separate a global central denominator into a reduced cofinal factor and
a factor in the actual selected parabolic. -/
theorem globalDelta_square_pow_decompose (J : Set I) (n : ℕ) :
    ((parabolicDelta M Set.univ) ^ 2) ^ n =
      (cofinalLoop M J) ^ n * ((parabolicDelta M J) ^ 2) ^ n := by
  let d := parabolicDelta M J
  let Ω := (parabolicDelta M Set.univ) ^ 2
  have hΩd : Ω * d ^ 2 = d ^ 2 * Ω := (globalDelta_square_commute M (d ^ 2)).eq
  have hc : Commute (cofinalLoop M J) (d ^ 2) := by
    change ((d⁻¹) ^ 2 * Ω) * d ^ 2 = d ^ 2 * ((d⁻¹) ^ 2 * Ω)
    calc
      _ = (d⁻¹) ^ 2 * (Ω * d ^ 2) := by group
      _ = (d⁻¹) ^ 2 * (d ^ 2 * Ω) := by rw [hΩd]
      _ = _ := by group
  have hprod : cofinalLoop M J * d ^ 2 = Ω := by
    change ((d⁻¹) ^ 2 * Ω) * d ^ 2 = Ω
    calc
      _ = (d⁻¹) ^ 2 * (Ω * d ^ 2) := by group
      _ = (d⁻¹) ^ 2 * (d ^ 2 * Ω) := by rw [hΩd]
      _ = _ := by group
  calc
    Ω ^ n = (cofinalLoop M J * d ^ 2) ^ n := by rw [hprod]
    _ = (cofinalLoop M J) ^ n * (d ^ 2) ^ n := hc.mul_pow n

/-- The actual reduced ribbon loop subgroup meets the actual parabolic
trivially. This uses the proved signed positive ribbon fractions. -/
theorem reducedRibbonLoop_parabolic_eq_one (X : RibbonObject M) {β : Artin.Group M}
    (hβ : ReducedArrow M X X β) (hpar : β ∈ Artin.parabolic M X.indices) : β = 1 := by
  obtain ⟨n, p, hp, hfrac⟩ := ReducedArrow.positive_fraction M hβ
  have hc := positive_cofinalLoop_pow M X n
  have hmem : p * ((cofinalLoop M X.indices) ^ n)⁻¹ ∈ Artin.parabolic M X.indices := by
    rwa [← hfrac]
  have heq := positive_leftReduced_fraction_parabolic_eq M X.indices
    hp.positive hc.positive hp.leftReduced hc.leftReduced hmem
  rw [hfrac, heq, mul_inv_cancel]

theorem reducedRibbonQuotientMap_injective (X : RibbonObject M) :
    Function.Injective (reducedRibbonQuotientMap M X) := by
  apply (injective_iff_map_eq_one _).2
  intro β hβ
  apply Subtype.ext
  exact reducedRibbonLoop_parabolic_eq_one M X β.property
    ((reducedRibbonQuotientMap_eq_one_iff M X β).1 hβ)

/-- Every actual normalizer element is a selected parabolic element times an
actual signed path of outside ribbons. -/
theorem exists_parabolic_reducedRibbon_factorization (X : RibbonObject M)
    (β : Artin.Group M)
    (hβ : β ∈ Subgroup.normalizer (Artin.parabolic M X.indices : Set (Artin.Group M))) :
    ∃ a ∈ Artin.parabolic M X.indices,
      ∃ r ∈ reducedRibbonLoops M X, β = a * r := by
  obtain ⟨n, p, hp, hfrac⟩ := positive_fraction_globalDelta_square M β
  let Ω := (parabolicDelta M Set.univ) ^ 2
  have hΩN : Ω ^ n ∈
      Subgroup.normalizer (Artin.parabolic M X.indices : Set (Artin.Group M)) := by
    apply Subgroup.mem_normalizer_iff.2
    intro a
    have hcomm := (globalDelta_square_commute M a).pow_left n
    have he : Ω ^ n * a * (Ω ^ n)⁻¹ = a := by rw [hcomm.eq, mul_inv_cancel_right]
    rw [he]
  have hpN : p ∈
      Subgroup.normalizer (Artin.parabolic M X.indices : Set (Artin.Group M)) := by
    have he : p = β * Ω ^ n := by rw [hfrac]; dsimp only [Ω]; group
    rw [he]
    exact Subgroup.mul_mem _ hβ hΩN
  obtain ⟨a, r, b, ha, hr, hb, hprod, hrleft, hrright, hrN⟩ :=
    exists_positive_normalizer_double_reduction M X.indices p hp hpN
  have hrib : IsRibbon M X X r := reduced_normalizer_isRibbon M X.indices hr hrright hrN
  have hrgen : PositiveReducedArrow M X X r :=
    positive_leftReduced_ribbon_generated M hr hrleft hrib
  let D := ((parabolicDelta M X.indices) ^ 2) ^ n
  let t := b * D⁻¹
  have hD : D ∈ Artin.parabolic M X.indices :=
    Subgroup.pow_mem _ (Subgroup.pow_mem _
      (actualPositiveParabolic_le_parabolic M X.indices
        (parabolicDelta_mem_positiveParabolic M X.indices)) 2) n
  have ht : t ∈ Artin.parabolic M X.indices :=
    Subgroup.mul_mem _ (actualPositiveParabolic_le_parabolic M X.indices hb)
      (Subgroup.inv_mem _ hD)
  have ha' : a * (r * t * r⁻¹) ∈ Artin.parabolic M X.indices :=
    Subgroup.mul_mem _ (actualPositiveParabolic_le_parabolic M X.indices ha)
      ((Subgroup.mem_normalizer_iff.1 hrN t).1 ht)
  have hcgen := positive_cofinalLoop_pow M X n
  have hR : r * ((cofinalLoop M X.indices) ^ n)⁻¹ ∈ reducedRibbonLoops M X :=
    ReducedArrow.comp hrgen.toReducedArrow (ReducedArrow.inverse hcgen.toReducedArrow)
  refine ⟨a * (r * t * r⁻¹), ha', r * ((cofinalLoop M X.indices) ^ n)⁻¹, hR, ?_⟩
  rw [hfrac, hprod, globalDelta_square_pow_decompose M X.indices n, mul_inv_rev]
  dsimp only [t, D]
  group

theorem reducedRibbonQuotientMap_surjective (X : RibbonObject M) :
    Function.Surjective (reducedRibbonQuotientMap M X) := by
  intro q
  let A := Artin.parabolic M X.indices
  let N := Subgroup.normalizer (A : Set (Artin.Group M))
  obtain ⟨β, rfl⟩ := QuotientGroup.mk'_surjective (A.subgroupOf N) q
  obtain ⟨a, ha, r, hr, hprod⟩ :=
    exists_parabolic_reducedRibbon_factorization M X β.val β.property
  let aN : N := ⟨a, A.le_normalizer ha⟩
  let rN : N := reducedRibbonLoopsToNormalizer M X ⟨r, hr⟩
  have hβ : β = aN * rN := Subtype.ext hprod
  refine ⟨⟨r, hr⟩, ?_⟩
  change QuotientGroup.mk' (A.subgroupOf N) rN = QuotientGroup.mk' (A.subgroupOf N) β
  have ha1 : QuotientGroup.mk' (A.subgroupOf N) aN = 1 :=
    (QuotientGroup.eq_one_iff aN).2 ha
  rw [hβ, map_mul, ha1, one_mul]

/-- The canonical identification, with the actual quotient projection as
its underlying map, of reduced ribbon loops and the normalizer quotient. -/
noncomputable def reducedRibbonNormalizerQuotientEquiv (X : RibbonObject M) :
    reducedRibbonLoops M X ≃* Artin.normalizerQuotient M X.indices :=
  MulEquiv.ofBijective (reducedRibbonQuotientMap M X)
    ⟨reducedRibbonQuotientMap_injective M X, reducedRibbonQuotientMap_surjective M X⟩

@[simp] theorem reducedRibbonNormalizerQuotientEquiv_apply (X : RibbonObject M)
    (r : reducedRibbonLoops M X) :
    reducedRibbonNormalizerQuotientEquiv M X r = reducedRibbonQuotientMap M X r := rfl

/-- The actual conjugation action of reduced ribbon loops on the selected
parabolic subgroup. -/
def reducedRibbonParabolicAction (X : RibbonObject M) :
    reducedRibbonLoops M X →* MulAut (Artin.parabolic M X.indices) :=
  (Artin.parabolic M X.indices).normalizerMonoidHom.comp
    (reducedRibbonLoopsToNormalizer M X)

/-- Multiplication of the actual two factors, with its codomain restricted
to the actual normalizer. -/
def normalizerSemidirectMap (X : RibbonObject M) :
    (Artin.parabolic M X.indices) ⋊[reducedRibbonParabolicAction M X]
      (reducedRibbonLoops M X) →*
        Subgroup.normalizer (Artin.parabolic M X.indices : Set (Artin.Group M)) := by
  let f : (Artin.parabolic M X.indices) ⋊[reducedRibbonParabolicAction M X]
      (reducedRibbonLoops M X) →* Artin.Group M :=
    SemidirectProduct.lift (Artin.parabolic M X.indices).subtype
      (reducedRibbonLoops M X).subtype (by intro r; ext a; rfl)
  exact f.codRestrict _ (fun x => Subgroup.mul_mem _
    ((Artin.parabolic M X.indices).le_normalizer x.left.property)
    (reducedRibbonLoop_mem_normalizer M X x.right))

@[simp] theorem normalizerSemidirectMap_value (X : RibbonObject M)
    (x : (Artin.parabolic M X.indices) ⋊[reducedRibbonParabolicAction M X]
      (reducedRibbonLoops M X)) :
    (normalizerSemidirectMap M X x : Artin.Group M) =
      (x.left : Artin.Group M) * (x.right : Artin.Group M) := rfl

theorem normalizerSemidirectMap_bijective (X : RibbonObject M) :
    Function.Bijective (normalizerSemidirectMap M X) := by
  constructor
  · intro x y hxy
    have he := congrArg Subtype.val hxy
    change (x.left : Artin.Group M) * (x.right : Artin.Group M) =
      (y.left : Artin.Group M) * (y.right : Artin.Group M) at he
    have hloop : (x.right : Artin.Group M) * (y.right : Artin.Group M)⁻¹ ∈
        reducedRibbonLoops M X := Subgroup.mul_mem _ x.right.property
          (Subgroup.inv_mem _ y.right.property)
    have hprod : (x.right : Artin.Group M) * (y.right : Artin.Group M)⁻¹ =
        (x.left : Artin.Group M)⁻¹ * (y.left : Artin.Group M) := by
      have h := congrArg (fun a : Artin.Group M =>
        (x.left : Artin.Group M)⁻¹ * a * (y.right : Artin.Group M)⁻¹) he
      simpa [mul_assoc] using h
    have hpar : (x.right : Artin.Group M) * (y.right : Artin.Group M)⁻¹ ∈
        Artin.parabolic M X.indices := by
      rw [hprod]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ x.left.property) y.left.property
    have heq := reducedRibbonLoop_parabolic_eq_one M X hloop hpar
    have hright : x.right = y.right := Subtype.ext (mul_inv_eq_one.1 heq)
    have hleft : x.left = y.left := by
      apply Subtype.ext
      rw [hright] at he
      exact mul_right_cancel he
    exact SemidirectProduct.ext hleft hright
  · intro β
    obtain ⟨a, ha, r, hr, hprod⟩ :=
      exists_parabolic_reducedRibbon_factorization M X β.val β.property
    exact ⟨⟨⟨a, ha⟩, ⟨r, hr⟩⟩, Subtype.ext hprod.symm⟩

/-- The actual normalizer is the semidirect product of its standard
parabolic and its actual generated reduced ribbon loop subgroup. -/
noncomputable def normalizerSemidirectEquiv (X : RibbonObject M) :
    Subgroup.normalizer (Artin.parabolic M X.indices : Set (Artin.Group M)) ≃*
      (Artin.parabolic M X.indices) ⋊[reducedRibbonParabolicAction M X]
        (reducedRibbonLoops M X) :=
  (MulEquiv.ofBijective (normalizerSemidirectMap M X)
    (normalizerSemidirectMap_bijective M X)).symm

end ArtinNormalisers.Ribbon2
