import ArtinHomotopy.RibbonGcd
import ArtinHomotopy.FaceResidues
import ArtinChambers.RibbonDeckLabels
import ArtinDeligne.IncomingOrder
import ArtinDeligne.MonotoneSignInterpolation

/-!
# Actual simple ribbons and actual geometric chamber intervals

The source half-turn is an actual simple positive lift. Its generated
positive divisors are exactly the generated arrows which are simple lifts.
Conversely every geometric positive chamber pair divides this half-turn.
Positive factors of a simple product remain simple. All comparisons refer
to the already constructed actual relative chambers and transporter lifts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace ArtinNormalisers.Deligne5

open Ribbon2 Homotopy5 Chamber3 Theorem18 Asphericity5

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group]

theorem facePrefix_univ (X : RibbonObject M) :
    facePrefix M X Set.univ = cofinalDelta M X.indices := by
  simp only [facePrefix, cofinalDelta, Set.union_univ]

theorem cofinalDelta_eq_simpleLift_projection (X : RibbonObject M) :
    cofinalDelta M X.indices =
      transporterPositiveLift M (Artin.projection M (cofinalDelta M X.indices)) := by
  rw [← facePrefix_univ M X]
  exact facePrefix_eq_simpleLift_projection M X Set.univ

theorem SimpleRibbon.eq_simpleLift {X Y : RibbonObject M} {s : Artin.Group M}
    (hs : SimpleRibbon M X Y s) :
    s = transporterPositiveLift M (Artin.projection M s) := by
  obtain ⟨q, hq, hsq⟩ := hs.2
  apply (actual_simple_factors M (d := Artin.projection M (cofinalDelta M X.indices)) hs.1.positive hq ?_).1
  exact hsq.symm.trans (cofinalDelta_eq_simpleLift_projection M X)

omit [Finite M.Group] in
/-- The full coordinate face is literally the origin of the actual flat. -/
theorem rawFacePoint_univ (J : Set I) (L : RawFacetLabel M J) :
    rawFacePoint M J L Set.univ = 0 := by
  apply (rawFacetCoordinates L).injective
  ext i
  rw [rawFacePoint_coordinates]
  simp

/-- Every actual chamber pair is a divisor of the genuine source half-turn. -/
theorem intervalPositive_prefix_cofinalDelta (J : Set I) (C D : ActualChamber M J) :
    RibbonPrefix M (transporterPositiveLift M (relativeTransport M J C D))
      (cofinalDelta M (actualChamberIndices M J C)) := by
  let L := chamberRawLabel M J C
  have hinc : ChamberIncident (actualForms M J) (rawFacePoint M J L Set.univ) D := by
    rw [rawFacePoint_univ M J L]
    exact (chamberIncident_iff_signs (E := relativeSubspace J) (actualForms M J)
      (0 : relativeSubspace J) D).mpr (by
      intro h hz
      exact False.elim (hz (map_zero (actualForms M J h))))
  have hpref := (rawFacePoint_incident_iff_ribbonPrefix M J L Set.univ D).mp hinc
  simpa only [L, chamberRawLabel_chamber, chamberRawLabel_indices, facePrefix,
    Set.union_univ, cofinalDelta] using hpref

theorem simpleRibbon_intervalPositive (J : Set I) (C D : ActualChamber M J) :
    SimpleRibbon M ⟨actualChamberIndices M J C⟩ ⟨actualChamberIndices M J D⟩
      (transporterPositiveLift M (relativeTransport M J C D)) :=
  ⟨transporterPositiveLift_generated M (relativeTransport_conjugacy M J C D)
    (relativeTransport_minimal M J C D), intervalPositive_prefix_cofinalDelta M J C D⟩

/-- Actual simple positive generation is precisely the half-turn divisor
predicate; the converse uses an actual standard source chamber and endpoint. -/
theorem simpleRibbon_iff_positive_eq_simpleLift (X Y : RibbonObject M) (s : Artin.Group M) :
    SimpleRibbon M X Y s ↔ PositiveReducedArrow M X Y s ∧
      s = transporterPositiveLift M (Artin.projection M s) := by
  constructor
  · intro hs
    exact ⟨hs.1, SimpleRibbon.eq_simpleLift M hs⟩
  · rintro ⟨hp, hs⟩
    let C : ChamberFiber M X.indices X :=
      ⟨standardActualChamber M X.indices, standardActualChamber_indices M X.indices⟩
    let D := fiberTarget M X.indices (Artin.projection M s)
      (isRibbon_projection_transporter M hp.isRibbon) C
    have hrel : relativeTransport M X.indices C.val D.val = Artin.projection M s :=
      relativeTransport_fiberTarget M X.indices _ _
        (simple_reduced_projection_minimal M hp.isRibbon hp.leftReduced hs) C
    refine ⟨hp, ?_⟩
    have hprefix := intervalPositive_prefix_cofinalDelta M X.indices C.val D.val
    rw [hrel, ← hs] at hprefix
    simpa only [C, standardActualChamber_indices] using hprefix

theorem simpleRibbon_one (X : RibbonObject M) : SimpleRibbon M X X 1 := by
  refine ⟨.identity X, ?_⟩
  exact ⟨cofinalDelta M X.indices, cofinalDelta_positive M X.indices, by simp⟩

/-- Both genuine generated factors of an actual simple ribbon are simple. -/
theorem SimpleRibbon.factors {X Y Z : RibbonObject M} {a b : Artin.Group M}
    (hab : SimpleRibbon M X Z (a * b))
    (ha : PositiveReducedArrow M X Y a) (hb : PositiveReducedArrow M Y Z b) :
    SimpleRibbon M X Y a ∧ SimpleRibbon M Y Z b := by
  have he := SimpleRibbon.eq_simpleLift M hab
  obtain ⟨haeq, hbeq⟩ := actual_simple_factors M ha.positive hb.positive he
  exact ⟨(simpleRibbon_iff_positive_eq_simpleLift M X Y a).mpr ⟨ha, haeq⟩,
    (simpleRibbon_iff_positive_eq_simpleLift M Y Z b).mpr ⟨hb, hbeq⟩⟩

theorem SimpleRibbon.prefix {X Y Z : RibbonObject M} {a b : Artin.Group M}
    (hb : SimpleRibbon M X Z b) (ha : PositiveReducedArrow M X Y a)
    (hab : RibbonPrefix M a b) : SimpleRibbon M X Y a := by
  obtain ⟨q, hq, he⟩ := positive_ribbon_prefix_tail M ha hb.1 hab
  rw [he] at hb
  exact (SimpleRibbon.factors M hb ha hq).1

theorem SimpleRibbon.tail {X Y Z : RibbonObject M} {a b : Artin.Group M}
    (hab : SimpleRibbon M X Z (a * b))
    (ha : PositiveReducedArrow M X Y a) (hb : PositiveReducedArrow M Y Z b) :
    SimpleRibbon M Y Z b := (SimpleRibbon.factors M hab ha hb).2

/-- The actual endpoint of a simple ribbon has its precise canonical
minimal relative transporter, rather than only a conjugacy class. -/
theorem relativeTransport_simpleFiberTarget (J : Set I) {X Y : RibbonObject M}
    {s : Artin.Group M} (hs : SimpleRibbon M X Y s) (C : ChamberFiber M J X) :
    relativeTransport M J C.val
      (fiberTarget M J (Artin.projection M s)
        (isRibbon_projection_transporter M hs.1.isRibbon) C).val = Artin.projection M s :=
  relativeTransport_fiberTarget M J _ _
    (simple_reduced_projection_minimal M hs.1.isRibbon hs.1.leftReduced
      (SimpleRibbon.eq_simpleLift M hs)) C

/-- A simple product gives a genuine chamber-between relation at its actual
intermediate endpoint. This is the local geometric input for all subchains. -/
theorem chamberBetween_of_simple_product (J : Set I)
    {X Y Z : RibbonObject M} {a b : Artin.Group M}
    (ha : PositiveReducedArrow M X Y a) (hb : PositiveReducedArrow M Y Z b)
    (hab : SimpleRibbon M X Z (a * b)) (C : ChamberFiber M J X) :
    ChamberBetween C.val
      (fiberTarget M J (Artin.projection M a)
        (isRibbon_projection_transporter M ha.isRibbon) C).val
      (fiberTarget M J (Artin.projection M (a * b))
        (isRibbon_projection_transporter M hab.1.isRibbon) C).val := by
  have has := (SimpleRibbon.factors M hab ha hb).1
  rw [chamberBetween_iff_relativeTransport_length,
    relativeTransport_simpleFiberTarget M J has C,
    relativeTransport_simpleFiberTarget M J hab C]
  rw [map_mul, inv_mul_cancel_left]
  simpa only [map_mul] using
    actual_simple_factors_length M ha.positive hb.positive (SimpleRibbon.eq_simpleLift M hab)


/-- Incoming simple quotients recover the actual relative chamber transporter. -/
theorem incoming_relativeTransport {B0 : RibbonObject M} {u v : IncomingVertex M B0}
    (hs : SimpleRibbon M u.source v.source (u.difference v)) :
    relativeTransport M B0.indices u.chamber v.chamber =
      Artin.projection M (u.difference v) := by
  have h := relativeTransport_simpleFiberTarget M B0.indices hs u.chamberFiber
  change relativeTransport M B0.indices u.chamber _ = _ at h
  simpa only [IncomingVertex.fiberTarget_chamber] using h

/-- Every ordered subtriple of an actual simple incoming chain is geodesic. -/
theorem incoming_chamberBetween {B0 : RibbonObject M} {u v w : IncomingVertex M B0}
    (huv : u ≤ v) (hvw : v ≤ w)
    (huw : SimpleRibbon M u.source w.source (u.difference w)) :
    ChamberBetween u.chamber v.chamber w.chamber := by
  have hs : SimpleRibbon M u.source w.source (u.difference v * v.difference w) := by
    simpa only [IncomingVertex.difference_mul] using huw
  have h := chamberBetween_of_simple_product M B0.indices huv hvw hs u.chamberFiber
  simp only [IncomingVertex.difference_mul] at h
  change ChamberBetween u.chamber _ _ at h
  simpa only [IncomingVertex.fiberTarget_chamber] using h

/-- A Boolean sequence with no alternating subtriple has one sign order.
No strict monotonicity of the indexing-to-vertex map is assumed. -/
theorem bool_sign_order_separated {κ : Type*} [LinearOrder κ] (s : κ → Bool)
    (hb : ∀ i j k, i ≤ j → j ≤ k → s i = s k → s j = s i) :
    (∀ i j, s i = false → s j = true → i < j) ∨
      (∀ i j, s i = true → s j = false → i < j) := by
  classical
  by_cases hn : ∀ i j, s i = false → s j = true → i < j
  · exact Or.inl hn
  · right
    push Not at hn
    obtain ⟨i, j, hi, hj, hji⟩ := hn
    have hji' : j ≤ i := hji
    intro k l hk hl
    by_contra hkl
    have hlk : l ≤ k := le_of_not_gt hkl
    rcases le_total l j with hlj | hjl
    · have he := hb l j i hlj hji' (by rw [hl, hi])
      simp only [hj, hl, Bool.true_eq_false] at he
    · have he := hb j l k hjl hlk (by rw [hj, hk])
      simp only [hl, hj, Bool.false_eq_true] at he

omit [Finite M.Group] in
/-- A chamber's sign is exactly the strict sign of any of its actual points. -/
theorem chamber_sign_true_iff (J : Set I) (C : ActualChamber M J)
    {c : relativeSubspace J} (hc : c ∈ C.region) (R : RelativeRoot M J) :
    C.signs R = true ↔ 0 < actualForms M J R c := by
  have h := hc R
  change (if C.signs R then 0 < actualForms M J R c else actualForms M J R c < 0) at h
  cases hs : C.signs R
  · rw [hs] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    simp only [Bool.false_eq_true, false_iff]
    exact not_lt_of_ge h.le
  · rw [hs] at h
    simp only [↓reduceIte] at h
    simp only [true_iff]
    exact h

omit [Finite M.Group] in
theorem chamber_sign_false_of_neg (J : Set I) (C : ActualChamber M J)
    {c : relativeSubspace J} (hc : c ∈ C.region) (R : RelativeRoot M J)
    (hn : actualForms M J R c < 0) : C.signs R = false := by
  cases hs : C.signs R
  · rfl
  · exact False.elim (lt_asymm ((chamber_sign_true_iff M J C hc R).mp hs) hn)

/-- Actual chamber points along a simple incoming chain have one sign change
with strictly separated integer heights, including all repeated vertices. -/
theorem incoming_signHeightSeparated {B0 : RibbonObject M}
    {κ : Type*} [LinearOrder κ] (v : κ → IncomingVertex M B0)
    (hv : Monotone v)
    (hs : ∀ i j, i ≤ j → SimpleRibbon M (v i).source (v j).source
      ((v i).difference (v j)))
    (c : κ → relativeSubspace B0.indices) (hc : ∀ i, c i ∈ (v i).chamber.region)
    (R : RelativeRoot M B0.indices) :
    SignHeightSeparated (fun i => actualForms M B0.indices R (c i))
      (fun i => ((v i).height : ℝ)) := by
  let s : κ → Bool := fun i => (v i).chamber.signs R
  have hbool : ∀ i j k, i ≤ j → j ≤ k → s i = s k → s j = s i := by
    intro i j k hij hjk he
    exact incoming_chamberBetween M (hv hij) (hv hjk) (hs i k (hij.trans hjk)) R he
  have hheight {i j : κ} (hij : i < j) (hneq : s i ≠ s j) :
      ((v i).height : ℝ) < ((v j).height : ℝ) := by
    have hvne : v i ≠ v j := by
      intro he
      apply hneq
      exact congrArg (fun u : IncomingVertex M B0 => u.chamber.signs R) he
    have hlt : (v i).height < (v j).height :=
      IncomingVertex.height_lt (lt_of_le_of_ne (hv hij.le) hvne)
    exact_mod_cast hlt
  rcases bool_sign_order_separated s hbool with hn | hp
  · left
    intro i j hi hj
    have hsi : s i = false := chamber_sign_false_of_neg M B0.indices _ (hc i) R hi
    have hsj : s j = true := (chamber_sign_true_iff M B0.indices _ (hc j) R).mpr hj
    exact hheight (hn i j hsi hsj) (by rw [hsi, hsj]; decide)
  · right
    intro i j hi hj
    have hsi : s i = true := (chamber_sign_true_iff M B0.indices _ (hc i) R).mpr hi
    have hsj : s j = false := chamber_sign_false_of_neg M B0.indices _ (hc j) R hj
    exact hheight (hp i j hsi hsj) (by rw [hsi, hsj]; decide)

end ArtinNormalisers.Deligne5
