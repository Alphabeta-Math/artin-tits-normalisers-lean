import ArtinRibbons.PositiveSupport
import ArtinRibbons.SphericalPositive
import ArtinRibbons.ParabolicReduction
import ArtinRibbons.RibbonGroupoid
import OAI.Topology.ArtinGroups.Harmonic.RestrictedArtinHom

/-!
# Coprime positive fractions in the actual spherical Artin group

The normal forms below are derived from the proved concrete positive gcds,
Ore multiples and faithful positive embedding. Parabolic saturation uses
positive words in the actual generated parabolic, not a normalizer premise.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Ribbon2

open OAI.HarmonicArtin OAI.HarmonicArtin.Geometric OAI.HarmonicArtin.CoxeterExchange

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group]

/-- A pair has no nontrivial common positive prefix. -/
def LeftCoprime (a b : PositiveArtin M) : Prop :=
  ∀ e, PositivePrefix M e a → PositivePrefix M e b → e = 1

/-- A pair has no nontrivial common positive suffix. -/
def RightCoprime (a b : PositiveArtin M) : Prop :=
  ∀ e, PositiveSuffix M e a → PositiveSuffix M e b → e = 1

theorem exists_left_reduced_pair (a b : PositiveArtin M) :
    ∃ d c z, a = d * c ∧ b = d * z ∧ LeftCoprime M c z := by
  obtain ⟨d, ⟨c, hc⟩, ⟨z, hz⟩, hd⟩ := positive_gcd_left M a b
  refine ⟨d, c, z, hc, hz, ?_⟩
  intro e hec hez
  have he := hd (d * e)
    (hc ▸ positivePrefix_mul_left M d hec)
    (hz ▸ positivePrefix_mul_left M d hez)
  have hdeg := positivePrefix_degree M he
  rw [positiveDegree_mul] at hdeg
  exact (positiveDegree_zero_iff M e).1 (by omega)

theorem exists_right_reduced_pair (a b : PositiveArtin M) :
    ∃ d c z, a = c * d ∧ b = z * d ∧ RightCoprime M c z := by
  obtain ⟨d, ⟨c, hc⟩, ⟨z, hz⟩, hd⟩ := positive_gcd_right M a b
  refine ⟨d, c, z, hc, hz, ?_⟩
  intro e ⟨x, hx⟩ ⟨y, hy⟩
  have he := hd (e * d)
    ⟨x, by rw [hc, hx, mul_assoc]⟩ ⟨y, by rw [hz, hy, mul_assoc]⟩
  obtain ⟨q, hq⟩ := he
  have hdeg := congrArg (positiveDegree M) hq
  simp only [positiveDegree_mul] at hdeg
  exact (positiveDegree_zero_iff M e).1 (by omega)

private theorem leftCoprime_common_prefix (a b : PositiveArtin M)
    (h : LeftCoprime M a b) (d e : PositiveArtin M)
    (hea : PositivePrefix M e (d * a)) (heb : PositivePrefix M e (d * b)) :
    PositivePrefix M e d := by
  obtain ⟨k, hka, hkb, hk⟩ := positive_gcd_left M (d * a) (d * b)
  obtain ⟨q, hq⟩ := hk d ⟨a, rfl⟩ ⟨b, rfl⟩
  have hqa := (positivePrefix_mul_left_iff M (positive_cancel_left M) d q a).1
    (hq ▸ hka)
  have hqb := (positivePrefix_mul_left_iff M (positive_cancel_left M) d q b).1
    (hq ▸ hkb)
  have hq1 := h q hqa hqb
  have hkd : k = d := by rw [hq, hq1, mul_one]
  simpa only [hkd] using hk e hea heb

private theorem suffix_mul_right_iff (d a b : PositiveArtin M) :
    PositiveSuffix M (a * d) (b * d) ↔ PositiveSuffix M a b := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, positive_cancel_right M d b (x * a) (by simpa only [mul_assoc] using hx)⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [hx, mul_assoc]⟩

private theorem rightCoprime_common_suffix (a b : PositiveArtin M)
    (h : RightCoprime M a b) (d e : PositiveArtin M)
    (hea : PositiveSuffix M e (a * d)) (heb : PositiveSuffix M e (b * d)) :
    PositiveSuffix M e d := by
  obtain ⟨k, hka, hkb, hk⟩ := positive_gcd_right M (a * d) (b * d)
  obtain ⟨q, hq⟩ := hk d ⟨a, rfl⟩ ⟨b, rfl⟩
  have hqa := (suffix_mul_right_iff M d q a).1 (hq ▸ hka)
  have hqb := (suffix_mul_right_iff M d q b).1 (hq ▸ hkb)
  have hq1 := h q hqa hqb
  have hkd : k = d := by rw [hq, hq1, one_mul]
  simpa only [hkd] using hk e hea heb

/-- Actual coprime left fractions have unique numerator and denominator. -/
theorem left_coprime_fraction_unique (a b c z : PositiveArtin M)
    (hab : LeftCoprime M a b) (hcz : LeftCoprime M c z)
    (heq : (positiveToParent M a)⁻¹ * positiveToParent M b =
      (positiveToParent M c)⁻¹ * positiveToParent M z) : a = c ∧ b = z := by
  obtain ⟨k, ⟨d, hd⟩, ⟨e, he⟩⟩ := positive_common_multiple_right M a c
  have hda : d * a = e * c := hd.symm.trans he
  have hdb : d * b = e * z := by
    apply positiveToParent_injective M
    have hm := congrArg (positiveToParent M) hda
    simp only [map_mul] at hm
    simp only [map_mul]
    calc
      positiveToParent M d * positiveToParent M b =
          (positiveToParent M d * positiveToParent M a) *
            ((positiveToParent M a)⁻¹ * positiveToParent M b) := by group
      _ = (positiveToParent M e * positiveToParent M c) *
            ((positiveToParent M c)⁻¹ * positiveToParent M z) := by rw [hm, heq]
      _ = positiveToParent M e * positiveToParent M z := by group
  have hed : PositivePrefix M e d := leftCoprime_common_prefix M a b hab d e
    ⟨c, hda⟩ ⟨z, hdb⟩
  have hde : PositivePrefix M d e := leftCoprime_common_prefix M c z hcz e d
    ⟨a, hda.symm⟩ ⟨b, hdb.symm⟩
  have h := positivePrefix_antisymm M hde hed
  rw [← h] at hda hdb
  exact ⟨positive_cancel_left M d a c hda, positive_cancel_left M d b z hdb⟩

/-- Actual coprime right fractions have unique numerator and denominator. -/
theorem right_coprime_fraction_unique (a b c z : PositiveArtin M)
    (hab : RightCoprime M a b) (hcz : RightCoprime M c z)
    (heq : positiveToParent M a * (positiveToParent M b)⁻¹ =
      positiveToParent M c * (positiveToParent M z)⁻¹) : a = c ∧ b = z := by
  obtain ⟨k, ⟨d, hd⟩, ⟨e, he⟩⟩ := positive_common_multiple_left M b z
  have hbd : b * d = z * e := hd.symm.trans he
  have had : a * d = c * e := by
    apply positiveToParent_injective M
    have hm := congrArg (positiveToParent M) hbd
    simp only [map_mul] at hm
    simp only [map_mul]
    calc
      positiveToParent M a * positiveToParent M d =
          (positiveToParent M a * (positiveToParent M b)⁻¹) *
            (positiveToParent M b * positiveToParent M d) := by group
      _ = (positiveToParent M c * (positiveToParent M z)⁻¹) *
            (positiveToParent M z * positiveToParent M e) := by rw [heq, hm]
      _ = positiveToParent M c * positiveToParent M e := by group
  have hed : PositiveSuffix M e d := rightCoprime_common_suffix M a b hab d e
    ⟨c, had⟩ ⟨z, hbd⟩
  have hde : PositiveSuffix M d e := rightCoprime_common_suffix M c z hcz e d
    ⟨a, had.symm⟩ ⟨b, hbd.symm⟩
  obtain ⟨x, hx⟩ := hed
  obtain ⟨y, hy⟩ := hde
  have hdeg := congrArg (positiveDegree M) hx
  have hdeg' := congrArg (positiveDegree M) hy
  simp only [positiveDegree_mul] at hdeg hdeg'
  have hxy : x = 1 := (positiveDegree_zero_iff M x).1 (by omega)
  have h : d = e := by simpa only [hxy, one_mul] using hx
  rw [← h] at had hbd
  exact ⟨positive_cancel_right M d a c had, positive_cancel_right M d b z hbd⟩

theorem exists_left_coprime_fraction (g : Artin.Group M) :
    ∃ a b : PositiveArtin M, LeftCoprime M a b ∧
      g = (positiveToParent M a)⁻¹ * positiveToParent M b := by
  obtain ⟨a, b, hg⟩ := positive_left_fraction M g
  obtain ⟨d, c, z, hc, hz, hcz⟩ := exists_left_reduced_pair M a b
  refine ⟨c, z, hcz, ?_⟩
  rw [hg, hc, hz, map_mul, map_mul]
  group

theorem exists_right_coprime_fraction (g : Artin.Group M) :
    ∃ a b : PositiveArtin M, RightCoprime M a b ∧
      g = positiveToParent M a * (positiveToParent M b)⁻¹ := by
  obtain ⟨a, b, hg⟩ := positive_fraction M g
  obtain ⟨d, c, z, hc, hz, hcz⟩ := exists_right_reduced_pair M a b
  refine ⟨c, z, hcz, ?_⟩
  rw [hg, hc, hz, map_mul, map_mul]
  group

/-- Positive fractions inside the actual generated parabolic. -/
theorem parabolic_positive_fraction (J : Set I) {g : Artin.Group M}
    (hg : g ∈ Artin.parabolic M J) :
    ∃ a b : PositiveArtin M,
      positiveToParent M a ∈ actualPositiveParabolic M J ∧
      positiveToParent M b ∈ actualPositiveParabolic M J ∧
      g = positiveToParent M a * (positiveToParent M b)⁻¹ := by
  classical
  let := Theorem18.finite_index M
  let := Fintype.ofFinite I
  have hJ : IsSpherical M J := by unfold IsSpherical; infer_instance
  have hg' : (presentationEquiv M).symm g ∈ artinParabolic M J := by
    have : g ∈ (artinParabolic M J).map (presentationEquiv M).toMonoidHom := by
      rwa [presentationEquiv_parabolic]
    obtain ⟨x, hx, hxe⟩ := this
    change presentationEquiv M x = g at hxe
    rw [← hxe, MulEquiv.symm_apply_apply]
    exact hx
  obtain ⟨u, v, hu, hv, he⟩ := sphericalParabolic_positive_fraction M J hJ hg'
  refine ⟨wordPositive M u, wordPositive M v, ?_, ?_, ?_⟩
  · rw [positiveToParent_word]
    exact wordProd_mem_actualPositiveParabolic M J u hu
  · rw [positiveToParent_word]
    exact wordProd_mem_actualPositiveParabolic M J v hv
  · have h := congrArg (presentationEquiv M) he
    simpa only [MulEquiv.apply_symm_apply, map_mul, map_inv,
      presentationEquiv_word, positiveToParent_word] using h

theorem parabolic_positive_left_fraction (J : Set I) {g : Artin.Group M}
    (hg : g ∈ Artin.parabolic M J) :
    ∃ a b : PositiveArtin M,
      positiveToParent M a ∈ actualPositiveParabolic M J ∧
      positiveToParent M b ∈ actualPositiveParabolic M J ∧
      g = (positiveToParent M a)⁻¹ * positiveToParent M b := by
  classical
  let := Theorem18.finite_index M
  let := Fintype.ofFinite I
  have hJ : IsSpherical M J := by unfold IsSpherical; infer_instance
  have hg' : (presentationEquiv M).symm g ∈ artinParabolic M J := by
    have : g ∈ (artinParabolic M J).map (presentationEquiv M).toMonoidHom := by
      rwa [presentationEquiv_parabolic]
    obtain ⟨x, hx, hxe⟩ := this
    change presentationEquiv M x = g at hxe
    rw [← hxe, MulEquiv.symm_apply_apply]
    exact hx
  rw [← restrictedArtinHom_range M J] at hg'
  obtain ⟨x, hx⟩ := hg'
  let := OAI.HarmonicArtin.Geometric.restricted_finite M J hJ
  obtain ⟨u, v, huv⟩ := finiteArtin_positive_left_fraction (restrictedMatrix M J) x
  refine ⟨wordPositive M (u.map Subtype.val), wordPositive M (v.map Subtype.val), ?_, ?_, ?_⟩
  · rw [positiveToParent_word]
    apply wordProd_mem_actualPositiveParabolic
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
    exact j.property
  · rw [positiveToParent_word]
    apply wordProd_mem_actualPositiveParabolic
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hi
    exact j.property
  · have he := congrArg (presentationEquiv M)
      (hx.symm.trans (congrArg (restrictedArtinHom M J) huv))
    simpa only [MulEquiv.apply_symm_apply, map_mul, map_inv,
      restrictedArtinHom_word, presentationEquiv_word, positiveToParent_word] using he

/-- A coprime left fraction of a parabolic element is supported on that parabolic. -/
theorem left_coprime_fraction_parabolic (J : Set I) (a b : PositiveArtin M)
    (hab : LeftCoprime M a b)
    (hg : (positiveToParent M a)⁻¹ * positiveToParent M b ∈ Artin.parabolic M J) :
    positiveToParent M a ∈ actualPositiveParabolic M J ∧
      positiveToParent M b ∈ actualPositiveParabolic M J := by
  obtain ⟨c, z, hc, hz, hfrac⟩ := parabolic_positive_left_fraction M J hg
  obtain ⟨d, c', z', hdc, hdz, hcop⟩ := exists_left_reduced_pair M c z
  have hc' := (positive_factors_mem_actualPositiveParabolic M J d c' (hdc ▸ hc)).2
  have hz' := (positive_factors_mem_actualPositiveParabolic M J d z' (hdz ▸ hz)).2
  have he : (positiveToParent M a)⁻¹ * positiveToParent M b =
      (positiveToParent M c')⁻¹ * positiveToParent M z' := by
    rw [hfrac, hdc, hdz, map_mul, map_mul]
    group
  obtain ⟨rfl, rfl⟩ := left_coprime_fraction_unique M a b c' z' hab hcop he
  exact ⟨hc', hz'⟩

theorem right_coprime_fraction_parabolic (J : Set I) (a b : PositiveArtin M)
    (hab : RightCoprime M a b)
    (hg : positiveToParent M a * (positiveToParent M b)⁻¹ ∈ Artin.parabolic M J) :
    positiveToParent M a ∈ actualPositiveParabolic M J ∧
      positiveToParent M b ∈ actualPositiveParabolic M J := by
  obtain ⟨c, z, hc, hz, hfrac⟩ := parabolic_positive_fraction M J hg
  obtain ⟨d, c', z', hdc, hdz, hcop⟩ := exists_right_reduced_pair M c z
  have hc' := (positive_factors_mem_actualPositiveParabolic M J c' d (hdc ▸ hc)).1
  have hz' := (positive_factors_mem_actualPositiveParabolic M J z' d (hdz ▸ hz)).1
  have he : positiveToParent M a * (positiveToParent M b)⁻¹ =
      positiveToParent M c' * (positiveToParent M z')⁻¹ := by
    rw [hfrac, hdc, hdz, map_mul, map_mul]
    group
  obtain ⟨rfl, rfl⟩ := right_coprime_fraction_unique M a b c' z' hab hcop he
  exact ⟨hc', hz'⟩

/-- A selected positive suffix of a right reduced element is trivial. -/
theorem selected_suffix_eq_one_of_reduced (J : Set I) {r : Artin.Group M}
    (hr : IsRightParabolicallyReduced M J r) (c d : PositiveArtin M)
    (hc : positiveToParent M c ∈ actualPositiveParabolic M J)
    (hprod : r = positiveToParent M d * positiveToParent M c) : c = 1 := by
  obtain ⟨w, rfl⟩ := positive_word_surjective M c
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton w i _ =>
    have hsupport := (positiveToParent_mem_iff_support M J _).1 hc
    have hi : i ∈ J := hsupport (by simp)
    have hp : positiveToParent M (d * wordPositive M w) ∈
        actualPositiveParabolic M Set.univ := (positiveActualHom M _).property
    apply False.elim
    apply hr i hi _ hp
    simpa [map_mul, positiveToParent_word, Artin.wordProd, mul_assoc] using hprod.symm

omit [Finite M.Group] in
private theorem positiveDegree_one_generator (z : PositiveArtin M)
    (hz : positiveDegree M z = 1) : ∃ i : I, z = positiveGenerator M i := by
  obtain ⟨w, rfl⟩ := positive_word_surjective M z
  rw [positiveDegree_word] at hz
  obtain ⟨i, rfl⟩ := List.length_eq_one_iff.1 hz
  exact ⟨i, rfl⟩

/-- The stripped positive normalizer conjugates each selected atom to a
selected atom. Right reduction is the essential extra hypothesis. -/
theorem reduced_normalizer_conjugates_generator (J : Set I) {r : Artin.Group M}
    (hr : r ∈ actualPositiveParabolic M Set.univ)
    (hred : IsRightParabolicallyReduced M J r)
    (hn : r ∈ Subgroup.normalizer (Artin.parabolic M J : Set (Artin.Group M)))
    {i : I} (hi : i ∈ J) :
    ∃ j ∈ J, r⁻¹ * Artin.generator M i * r = Artin.generator M j := by
  rw [← positiveToParent_mrange_eq_actual M] at hr
  obtain ⟨p, rfl⟩ := hr
  obtain ⟨d, c, z, hc, hz, hcz⟩ :=
    exists_left_reduced_pair M p (positiveGenerator M i * p)
  have he : (positiveToParent M c)⁻¹ * positiveToParent M z =
      (positiveToParent M p)⁻¹ * Artin.generator M i * positiveToParent M p := by
    calc
      (positiveToParent M c)⁻¹ * positiveToParent M z =
          (positiveToParent M p)⁻¹ * positiveToParent M (positiveGenerator M i * p) := by
        rw [hz, hc, map_mul, map_mul]
        group
      _ = _ := by rw [map_mul, positiveToParent_generator]; group
  have hmem : (positiveToParent M c)⁻¹ * positiveToParent M z ∈ Artin.parabolic M J := by
    rw [he]
    exact (Subgroup.mem_normalizer_iff''.1 hn _).1 (Subgroup.subset_closure ⟨i, hi, rfl⟩)
  obtain ⟨hcJ, hzJ⟩ := left_coprime_fraction_parabolic M J c z hcz hmem
  have hc1 : c = 1 := selected_suffix_eq_one_of_reduced M J hred c d hcJ
    (by rw [hc, map_mul])
  have he' : (positiveToParent M p)⁻¹ * Artin.generator M i * positiveToParent M p =
      positiveToParent M z := by simpa only [hc1, map_one, inv_one, one_mul] using he.symm
  have hzdeg : positiveDegree M z = 1 := by
    have h := congrArg (degree M) he'
    rw [degree_mul, degree_mul, degree_inv, degree_generator,
      degree_positiveToParent, degree_positiveToParent] at h
    omega
  obtain ⟨j, rfl⟩ := positiveDegree_one_generator M z hzdeg
  refine ⟨j, ?_, ?_⟩
  · exact (positiveToParent_mem_iff_support M J _).1 hzJ (by simp)
  · simpa only [positiveToParent_generator] using he'

omit [Finite M.Group] in
private theorem actualGenerator_injective : Function.Injective (Artin.generator M) := by
  intro i j hij
  apply M.toCoxeterSystem.simple_injective
  have h := congrArg (Artin.projection M) hij
  simpa only [Artin.projection_generator, CoxeterMatrix.toCoxeterSystem_simple] using h

omit [Finite M.Group] in
private theorem conjugate_positive_mem (J : Set I) (q : Artin.Group M)
    (hgen : ∀ i ∈ J, q⁻¹ * Artin.generator M i * q ∈ actualPositiveParabolic M J)
    {a : Artin.Group M} (ha : a ∈ actualPositiveParabolic M J) :
    q⁻¹ * a * q ∈ actualPositiveParabolic M J := by
  have hle : actualPositiveParabolic M J ≤
      (actualPositiveParabolic M J).comap (MulAut.conj q⁻¹).toMonoidHom := by
    apply Submonoid.closure_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    change q⁻¹ * Artin.generator M i * (q⁻¹)⁻¹ ∈ actualPositiveParabolic M J
    simpa only [inv_inv] using hgen i hi
  have h := hle ha
  change q⁻¹ * a * (q⁻¹)⁻¹ ∈ actualPositiveParabolic M J at h
  simpa only [inv_inv] using h

/-- A right-reduced positive normalizer is an actual positive-parabolic
transporter, rather than an assumed ribbon factor. -/
theorem reduced_normalizer_isRibbon (J : Set I) {r : Artin.Group M}
    (hr : r ∈ actualPositiveParabolic M Set.univ)
    (hred : IsRightParabolicallyReduced M J r)
    (hn : r ∈ Subgroup.normalizer (Artin.parabolic M J : Set (Artin.Group M))) :
    IsRibbon M ⟨J⟩ ⟨J⟩ r := by
  classical
  let := Theorem18.finite_index M
  have hgen (i : I) (hi : i ∈ J) := reduced_normalizer_conjugates_generator M J hr hred hn hi
  let f : J → J := fun i => ⟨(hgen i.val i.property).choose,
    (hgen i.val i.property).choose_spec.1⟩
  have hf (i : J) : r⁻¹ * Artin.generator M i.val * r = Artin.generator M (f i).val :=
    (hgen i.val i.property).choose_spec.2
  have hinj : Function.Injective f := by
    intro i j hij
    apply Subtype.ext
    apply actualGenerator_injective M
    have h : r⁻¹ * Artin.generator M i.val * r =
        r⁻¹ * Artin.generator M j.val * r := by rw [hf i, hf j, hij]
    have h' := congrArg (fun a => r * a * r⁻¹) h
    simpa only [mul_assoc, mul_inv_cancel_left, inv_mul_cancel_left,
      mul_inv_cancel_right, mul_inv_cancel, mul_one] using h'
  have hsurj := Finite.surjective_of_injective hinj
  have hforward : ∀ i ∈ J,
      r⁻¹ * Artin.generator M i * r ∈ actualPositiveParabolic M J := by
    intro i hi
    rw [hf ⟨i, hi⟩]
    exact generator_mem_actualPositiveParabolic M J (f ⟨i, hi⟩).property
  have hbackward : ∀ i ∈ J,
      (r⁻¹)⁻¹ * Artin.generator M i * r⁻¹ ∈ actualPositiveParabolic M J := by
    intro i hi
    obtain ⟨j, hj⟩ := hsurj ⟨i, hi⟩
    have h := hf j
    rw [hj] at h
    have heq : (r⁻¹)⁻¹ * Artin.generator M i * r⁻¹ = Artin.generator M j.val := by
      rw [← h]
      simp only [inv_inv]
      group
    rw [heq]
    exact generator_mem_actualPositiveParabolic M J j.property
  intro a
  constructor
  · exact conjugate_positive_mem M J r hforward
  · intro ha
    have h := conjugate_positive_mem M J r⁻¹ hbackward ha
    simpa [mul_assoc] using h

end ArtinNormalisers.Ribbon2
