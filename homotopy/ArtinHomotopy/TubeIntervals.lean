module

public import ArtinChambers.FaceProjection
public import ArtinChambers.TubeCover

/-!
# The actual tubes containing a point form a chamber interval

The two endpoints keep the imaginary signs at the vanishing real forms and
have opposite signs at the other forms. Thus tube membership is precisely
the existing, geometric chamber-between relation. This gives actual interval
bounds without assuming a Garside lattice or higher-topological comparison.
-/

@[expose] public section

namespace ArtinNormalisers.Homotopy5

open Chamber3

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  {H : Type*} [Finite H] (ℓ : H → E →L[ℝ] ℝ)

private theorem halfSpace_sign_unique (f : E →L[ℝ] ℝ) {x : E} {s t : Bool}
    (hs : x ∈ signHalfSpace f s) (ht : x ∈ signHalfSpace f t) : s = t := by
  cases s <;> cases t <;> try rfl
  · change f x < 0 at hs
    change 0 < f x at ht
    exact False.elim (lt_asymm hs ht)
  · change 0 < f x at hs
    change f x < 0 at ht
    exact False.elim (lt_asymm ht hs)

/-- The signs of the two projected chambers agree exactly on forms vanishing
at the real point; all other signs are opposite. -/
theorem faceChamber_pos_neg_sign_eq_iff (x : E) (C : Chamber ℓ) (h : H) :
    (faceChamber ℓ x C).signs h = (faceChamber ℓ (-x) C).signs h ↔ ℓ h x = 0 := by
  constructor
  · intro he
    by_contra hn
    have hneg : ℓ h (-x) ≠ 0 := by simpa only [map_neg, neg_ne_zero] using hn
    rw [faceChamber_signs_nonzero ℓ x C hn,
      faceChamber_signs_nonzero ℓ (-x) C hneg, map_neg] at he
    by_cases hp : 0 < ℓ h x
    · have hnp : ¬0 < -(ℓ h x) := not_lt.mpr (neg_nonpos.mpr hp.le)
      simp [hp, hnp] at he
    · have ha : ℓ h x < 0 := lt_of_le_of_ne (le_of_not_gt hp) hn
      have hna : 0 < -(ℓ h x) := neg_pos.mpr ha
      simp [hp, hna] at he
  · intro hz
    rw [faceChamber_signs_zero ℓ x C hz,
      faceChamber_signs_zero ℓ (-x) C (by simpa only [map_neg, neg_eq_zero] using hz)]

/-- A purely geometric interval is exactly agreement on the vanishing forms. -/
theorem chamberBetween_faceChamber_pos_neg_iff (x : E) (C D : Chamber ℓ) :
    ChamberBetween (faceChamber ℓ x C) D (faceChamber ℓ (-x) C) ↔
      ∀ h, ℓ h x = 0 → D.signs h = C.signs h := by
  constructor
  · intro h h₀ hz
    have he := h h₀ ((faceChamber_pos_neg_sign_eq_iff ℓ x C h₀).2 hz)
    rwa [faceChamber_signs_zero ℓ x C hz] at he
  · intro h h₀ he
    have hz := (faceChamber_pos_neg_sign_eq_iff ℓ x C h₀).1 he
    rw [h h₀ hz, faceChamber_signs_zero ℓ x C hz]

/-- Any actual tube witness supplies the same interval bounds. The witness
is chosen from the already proved cover, not assumed as geometric data. -/
noncomputable def tubeWitness (p : ComplexComplement ℓ) : Chamber ℓ :=
  Classical.choose (exists_mem_tubeSet ℓ p)

theorem mem_tubeWitness (p : ComplexComplement ℓ) : p ∈ tubeSet (tubeWitness ℓ p) :=
  Classical.choose_spec (exists_mem_tubeSet ℓ p)

noncomputable def tubeLowerChamber (p : ComplexComplement ℓ) : Chamber ℓ :=
  faceChamber ℓ p.val.1 (tubeWitness ℓ p)

noncomputable def tubeUpperChamber (p : ComplexComplement ℓ) : Chamber ℓ :=
  faceChamber ℓ (-p.val.1) (tubeWitness ℓ p)

/-- All chambers whose genuine tubes contain `p` form this precise interval.
In particular every such chamber has common actual simple interval bounds. -/
theorem mem_tubeSet_iff_chamberBetween (p : ComplexComplement ℓ) (D : Chamber ℓ) :
    p ∈ tubeSet D ↔ ChamberBetween (tubeLowerChamber ℓ p) D (tubeUpperChamber ℓ p) := by
  change p ∈ tubeSet D ↔ ChamberBetween (faceChamber ℓ p.val.1 (tubeWitness ℓ p)) D
    (faceChamber ℓ (-p.val.1) (tubeWitness ℓ p))
  rw [chamberBetween_faceChamber_pos_neg_iff]
  constructor
  · intro hp h hz
    exact halfSpace_sign_unique (ℓ h) (hp h hz) (mem_tubeWitness ℓ p h hz)
  · intro h h₀ hz
    rw [h h₀ hz]
    exact mem_tubeWitness ℓ p h₀ hz

end ArtinNormalisers.Homotopy5
