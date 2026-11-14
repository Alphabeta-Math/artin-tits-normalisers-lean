import ArtinDeligne.IncomingJoins

/-!
# Actual meets and monotone finite-packet intervals

The ribbon gcd above a common lower vertex gives an actual global meet.
An arbitrary lower bound is compared by first joining it with the chosen
common lower vertex. Thus the meet property does not presume that every
lower bound lies in one chosen positive coordinate chart.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Deligne5

open Ribbon2 Homotopy5 Chamber3

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group]

namespace IncomingVertex

variable {M} {B0 : RibbonObject M}

/-- A common lower chart and the genuine generated ribbon gcd construct a
meet with the full global greatest-lower-bound property. -/
theorem exists_meet_of_common_lower (u v a : IncomingVertex M B0) (hau : a ≤ u) (hav : a ≤ v) :
    ∃ m : IncomingVertex M B0, m ≤ u ∧ m ≤ v ∧
      ∀ w : IncomingVertex M B0, w ≤ u → w ≤ v → w ≤ m := by
  obtain ⟨U, d, hd, ⟨ru, hru, hdu⟩, ⟨rv, hrv, hdv⟩, hgreatest⟩ :=
    positive_reduced_ribbon_gcd_left_with_tails M hau hav
  let m : IncomingVertex M B0 :=
    ⟨U, d⁻¹ * a.value, .comp (.inverse hd.toReducedArrow) a.reduced⟩
  have hmu : m.difference u = ru := by
    change (d⁻¹ * a.value) * u.value⁻¹ = ru
    calc
      _ = d⁻¹ * (a.difference u) := by dsimp only [difference]; group
      _ = ru := by rw [hdu]; group
  have hmv : m.difference v = rv := by
    change (d⁻¹ * a.value) * v.value⁻¹ = rv
    calc
      _ = d⁻¹ * (a.difference v) := by dsimp only [difference]; group
      _ = rv := by rw [hdv]; group
  refine ⟨m, ?_, ?_, ?_⟩
  · change PositiveReducedArrow M U u.source (m.difference u)
    rw [hmu]
    exact hru
  · change PositiveReducedArrow M U v.source (m.difference v)
    rw [hmv]
    exact hrv
  · intro w hwu hwv
    let s : IncomingVertex M B0 := w ⊔ a
    have has : a ≤ s := le_sup_right
    have hsu : s ≤ u := sup_le hwu hau
    have hsv : s ≤ v := sup_le hwv hav
    have hpu : RibbonPrefix M (a.difference s) (a.difference u) :=
      ⟨s.difference u, hsu.positive, (difference_mul a s u).symm⟩
    have hpv : RibbonPrefix M (a.difference s) (a.difference v) :=
      ⟨s.difference v, hsv.positive, (difference_mul a s v).symm⟩
    obtain ⟨t, ht, hdt⟩ := hgreatest s.source (a.difference s) has hpu hpv
    have hsm : s.difference m = t := by
      change s.value * (d⁻¹ * a.value)⁻¹ = t
      rw [hdt]
      dsimp only [difference]
      group
    have hsmle : s ≤ m := by
      change PositiveReducedArrow M s.source U (s.difference m)
      rw [hsm]
      exact ht
    exact le_trans le_sup_left hsmle

/-- Existence of actual global binary meets. -/
theorem exists_meet (u v : IncomingVertex M B0) :
    ∃ m : IncomingVertex M B0, m ≤ u ∧ m ≤ v ∧
      ∀ w : IncomingVertex M B0, w ≤ u → w ≤ v → w ≤ m := by
  obtain ⟨a, hau, hav⟩ := exists_common_lower u v
  exact exists_meet_of_common_lower u v a hau hav

noncomputable def binaryMeet (u v : IncomingVertex M B0) : IncomingVertex M B0 :=
  Classical.choose (exists_meet u v)

theorem binaryMeet_le_left (u v : IncomingVertex M B0) : binaryMeet u v ≤ u :=
  (Classical.choose_spec (exists_meet u v)).1

theorem binaryMeet_le_right (u v : IncomingVertex M B0) : binaryMeet u v ≤ v :=
  (Classical.choose_spec (exists_meet u v)).2.1

theorem le_binaryMeet {u v w : IncomingVertex M B0} (hwu : w ≤ u) (hwv : w ≤ v) :
    w ≤ binaryMeet u v := (Classical.choose_spec (exists_meet u v)).2.2 w hwu hwv

theorem binaryMeet_eq_of_glb {u v m : IncomingVertex M B0} (hmu : m ≤ u) (hmv : m ≤ v)
    (hgreatest : ∀ w : IncomingVertex M B0, w ≤ u → w ≤ v → w ≤ m) : binaryMeet u v = m :=
  le_antisymm (hgreatest _ (binaryMeet_le_left u v) (binaryMeet_le_right u v))
    (le_binaryMeet hmu hmv)

theorem binaryMeet_isGLB (u v : IncomingVertex M B0) : IsGLB {u, v} (binaryMeet u v) := by
  constructor
  · intro w hw
    rcases Set.mem_insert_iff.mp hw with h | h
    · subst w
      exact binaryMeet_le_left u v
    · have he : w = v := Set.mem_singleton_iff.mp h
      subst w
      exact binaryMeet_le_right u v
  · intro w hw
    exact le_binaryMeet (hw (Set.mem_insert u {v}))
      (hw (Set.mem_insert_of_mem u (Set.mem_singleton v)))

/-- Derived from the actual ribbon gcd, with no order-completeness premise. -/
noncomputable instance semilatticeInf : SemilatticeInf (IncomingVertex M B0) :=
  SemilatticeInf.ofIsGLB binaryMeet binaryMeet_isGLB

/-- Both actual ribbon universal properties provide the incoming lattice. -/
noncomputable instance lattice : Lattice (IncomingVertex M B0) where
  __ := semilatticeSup
  __ := semilatticeInf

@[simp] theorem binaryMeet_eq_inf (u v : IncomingVertex M B0) : binaryMeet u v = u ⊓ v := rfl

noncomputable def finiteMeet (F : Finset (IncomingVertex M B0)) (hF : F.Nonempty) :
    IncomingVertex M B0 := F.inf' hF id

theorem finiteMeet_isGLB (F : Finset (IncomingVertex M B0)) (hF : F.Nonempty) :
    IsGLB (F : Set (IncomingVertex M B0)) (finiteMeet F hF) := Finset.isGLB_inf' hF

theorem finiteMeet_le (F : Finset (IncomingVertex M B0)) (hF : F.Nonempty)
    {u : IncomingVertex M B0} (hu : u ∈ F) : finiteMeet F hF ≤ u := Finset.inf'_le id hu

theorem le_finiteMeet (F : Finset (IncomingVertex M B0)) (hF : F.Nonempty)
    {u : IncomingVertex M B0} (hu : ∀ v ∈ F, u ≤ v) : u ≤ finiteMeet F hF :=
  Finset.le_inf' hF id hu

/-- Enlarging a nonempty packet decreases its actual meet. -/
theorem finiteMeet_antitone {F G : Finset (IncomingVertex M B0)} (hFG : F ⊆ G)
    (hF : F.Nonempty) (hG : G.Nonempty) : finiteMeet G hG ≤ finiteMeet F hF :=
  le_finiteMeet F hF (fun _ hu => finiteMeet_le G hG (hFG hu))

theorem finiteMeet_le_finiteJoin (F : Finset (IncomingVertex M B0)) (hF : F.Nonempty) :
    finiteMeet F hF ≤ finiteJoin F hF := by
  exact (finiteMeet_le F hF hF.choose_spec).trans (le_finiteJoin F hF hF.choose_spec)

/-- The actual simple interval packet associated to a nonempty finite set. -/
noncomputable def packetInterval (F : Finset (IncomingVertex M B0)) (hF : F.Nonempty) :
    Set (IncomingVertex M B0) := Set.Icc (finiteMeet F hF) (finiteJoin F hF)

theorem mem_packetInterval_iff (F : Finset (IncomingVertex M B0)) (hF : F.Nonempty)
    (u : IncomingVertex M B0) :
    u ∈ packetInterval F hF ↔ finiteMeet F hF ≤ u ∧ u ≤ finiteJoin F hF := Iff.rfl

theorem subset_packetInterval (F : Finset (IncomingVertex M B0)) (hF : F.Nonempty) :
    (F : Set (IncomingVertex M B0)) ⊆ packetInterval F hF := by
  intro u hu
  exact ⟨finiteMeet_le F hF hu, le_finiteJoin F hF hu⟩

theorem packetInterval_nonempty (F : Finset (IncomingVertex M B0)) (hF : F.Nonempty) :
    (packetInterval F hF).Nonempty :=
  ⟨finiteMeet F hF, le_rfl, finiteMeet_le_finiteJoin F hF⟩

/-- This carrier is monotone in packet inclusion in both interval endpoints. -/
theorem packetInterval_mono {F G : Finset (IncomingVertex M B0)} (hFG : F ⊆ G)
    (hF : F.Nonempty) (hG : G.Nonempty) : packetInterval F hF ⊆ packetInterval G hG := by
  intro u hu
  exact ⟨(finiteMeet_antitone hFG hF hG).trans hu.1,
    hu.2.trans (finiteJoin_mono hFG hF hG)⟩

/-- A packet in a simple interval has its entire meet/join interval there. -/
theorem packetInterval_subset_Icc (F : Finset (IncomingVertex M B0)) (hF : F.Nonempty)
    (a b : IncomingVertex M B0) (ha : ∀ v ∈ F, a ≤ v) (hb : ∀ v ∈ F, v ≤ b) :
    packetInterval F hF ⊆ Set.Icc a b := by
  intro u hu
  exact ⟨(le_finiteMeet F hF ha).trans hu.1, hu.2.trans (finiteJoin_le F hF hb)⟩

/-- Meet/join endpoint bounds and the simple total factor are derived from
any actual simple interval containing the packet. -/
theorem finiteMeetJoin_simple_interval (F : Finset (IncomingVertex M B0)) (hF : F.Nonempty)
    (a b : IncomingVertex M B0) (ha : ∀ v ∈ F, a ≤ v) (hb : ∀ v ∈ F, v ≤ b)
    (hs : SimpleRibbon M a.source b.source (a.difference b)) :
    a ≤ finiteMeet F hF ∧ finiteMeet F hF ≤ finiteJoin F hF ∧ finiteJoin F hF ≤ b ∧
      SimpleRibbon M (finiteMeet F hF).source (finiteJoin F hF).source
        ((finiteMeet F hF).difference (finiteJoin F hF)) := by
  have ham := le_finiteMeet F hF ha
  have hmj := finiteMeet_le_finiteJoin F hF
  have hjb := finiteJoin_le F hF hb
  exact ⟨ham, hmj, hjb, simple_difference_of_interval hs ham hmj hjb⟩

/-- Every ordered pair in the carrier has an actual simple connecting ribbon. -/
theorem packetInterval_simple {F : Finset (IncomingVertex M B0)} (hF : F.Nonempty)
    {a b : IncomingVertex M B0} (ha : ∀ v ∈ F, a ≤ v) (hb : ∀ v ∈ F, v ≤ b)
    (hs : SimpleRibbon M a.source b.source (a.difference b))
    {u v : IncomingVertex M B0} (hu : u ∈ packetInterval F hF)
    (hv : v ∈ packetInterval F hF) (huv : u ≤ v) :
    SimpleRibbon M u.source v.source (u.difference v) := by
  have hsub := packetInterval_subset_Icc F hF a b ha hb
  exact simple_difference_of_interval hs (hsub hu).1 huv (hsub hv).2

/-- The order geodesics in such a carrier are genuine chamber geodesics. -/
theorem packetInterval_chamberBetween {F : Finset (IncomingVertex M B0)} (hF : F.Nonempty)
    {a b : IncomingVertex M B0} (ha : ∀ v ∈ F, a ≤ v) (hb : ∀ v ∈ F, v ≤ b)
    (hs : SimpleRibbon M a.source b.source (a.difference b))
    {u v w : IncomingVertex M B0} (hu : u ∈ packetInterval F hF)
    (hw : w ∈ packetInterval F hF) (huv : u ≤ v) (hvw : v ≤ w) :
    ChamberBetween u.chamber v.chamber w.chamber :=
  incoming_chamberBetween M huv hvw (packetInterval_simple hF ha hb hs hu hw (huv.trans hvw))

end IncomingVertex

end ArtinNormalisers.Deligne5
