import ArtinDeligne.IncomingOrder
import ArtinDeligne.SimpleTransport

/-!
# Actual finite joins of incoming ribbon vertices

Concrete source powers of the cofinal loop give common lower bounds. Above
such a lower vertex, the proved positive ribbon lcm constructs an actual join
and its universal property. The join-semilattice instance and nonempty finite
joins are derived from these actual constructions, not assumed as fields.

Order intervals with simple total factor are closed under finite joins, and
all resulting connecting factors are actual simple ribbons. No invariance of
chambers under arbitrary target loops is used or asserted.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Deligne5

open Ribbon2 Homotopy5

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group]

namespace IncomingVertex

variable {M} {B0 : RibbonObject M}

/-- A concrete actual incoming vertex, with the fixed target as its source. -/
noncomputable def cofinalLowerVertex (B0 : RibbonObject M) (n : ℕ) : IncomingVertex M B0 :=
  ⟨B0, cofinalLoop M B0.indices ^ n, (positive_cofinalLoop_pow M B0 n).toReducedArrow⟩

/-- Inverse-arrow clearing and cofinal naturality give actual lower bounds. -/
theorem eventually_cofinalLower_le (u : IncomingVertex M B0) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → cofinalLowerVertex (M := M) B0 m ≤ u := by
  let v : IncomingVertex M u.source := ⟨B0, u.value⁻¹, .inverse u.reduced⟩
  obtain ⟨n, hn⟩ := v.eventually_positive
  refine ⟨n, ?_⟩
  intro m hnm
  have hpos := hn m hnm
  have he : u.value⁻¹ * cofinalLoop M u.source.indices ^ m =
      cofinalLoop M B0.indices ^ m * u.value⁻¹ :=
    (u.reduced.isRibbon.inv M).cofinalLoop_pow_mul M m
  change PositiveReducedArrow M B0 u.source
    (cofinalLoop M B0.indices ^ m * u.value⁻¹)
  simpa only [v, cofinalShift_value, he] using hpos

/-- One actual cofinal lower vertex bounds an arbitrary finite packet below;
all sufficiently large powers work, including degenerate cofinal loops. -/
theorem finite_eventually_cofinalLower_le (F : Finset (IncomingVertex M B0)) :
    ∃ n : ℕ, ∀ u ∈ F, ∀ m : ℕ, n ≤ m → cofinalLowerVertex (M := M) B0 m ≤ u := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert u F _ ih =>
    obtain ⟨n, hn⟩ := u.eventually_cofinalLower_le
    obtain ⟨k, hk⟩ := ih
    refine ⟨max n k, ?_⟩
    intro v hv m hm
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hn m ((le_max_left _ _).trans hm)
    · exact hk v hv m ((le_max_right _ _).trans hm)

theorem exists_common_lower (u v : IncomingVertex M B0) :
    ∃ a : IncomingVertex M B0, a ≤ u ∧ a ≤ v := by
  obtain ⟨n, hn⟩ := u.eventually_cofinalLower_le
  obtain ⟨m, hm⟩ := v.eventually_cofinalLower_le
  exact ⟨cofinalLowerVertex B0 (max n m), hn _ (le_max_left _ _), hm _ (le_max_right _ _)⟩

/-- Above an actual common lower vertex, the actual positive ribbon lcm
constructs a least upper bound of the two incoming vertices. -/
theorem exists_join_of_common_lower (u v a : IncomingVertex M B0) (hau : a ≤ u) (hav : a ≤ v) :
    ∃ j : IncomingVertex M B0, u ≤ j ∧ v ≤ j ∧
      ∀ w : IncomingVertex M B0, u ≤ w → v ≤ w → j ≤ w := by
  obtain ⟨U, l, hl, ⟨ru, hru, hlu⟩, ⟨rv, hrv, hlv⟩, hleast⟩ :=
    positive_reduced_ribbon_lcm_left M hau hav
  let j : IncomingVertex M B0 :=
    ⟨U, l⁻¹ * a.value, .comp (.inverse hl.toReducedArrow) a.reduced⟩
  have huj : u.difference j = ru := by
    change u.value * (l⁻¹ * a.value)⁻¹ = ru
    rw [hlu]
    dsimp only [difference]
    group
  have hvj : v.difference j = rv := by
    change v.value * (l⁻¹ * a.value)⁻¹ = rv
    rw [hlv]
    dsimp only [difference]
    group
  refine ⟨j, ?_, ?_, ?_⟩
  · change PositiveReducedArrow M u.source U (u.difference j)
    rw [huj]
    exact hru
  · change PositiveReducedArrow M v.source U (v.difference j)
    rw [hvj]
    exact hrv
  · intro w huw hvw
    have haw : a ≤ w := hau.trans huw
    have hpu : RibbonPrefix M (a.difference u) (a.difference w) :=
      ⟨u.difference w, huw.positive, (difference_mul a u w).symm⟩
    have hpv : RibbonPrefix M (a.difference v) (a.difference w) :=
      ⟨v.difference w, hvw.positive, (difference_mul a v w).symm⟩
    obtain ⟨t, ht, hwt⟩ := positive_ribbon_prefix_tail M hl haw
      (hleast _ haw.positive hpu hpv)
    have hjw : j.difference w = t := by
      change (l⁻¹ * a.value) * w.value⁻¹ = t
      calc
        _ = l⁻¹ * (a.difference w) := by dsimp only [difference]; group
        _ = t := by rw [hwt]; group
    change PositiveReducedArrow M U w.source (j.difference w)
    rw [hjw]
    exact ht

/-- Existence of actual binary joins with their full order universal property. -/
theorem exists_join (u v : IncomingVertex M B0) :
    ∃ j : IncomingVertex M B0, u ≤ j ∧ v ≤ j ∧
      ∀ w : IncomingVertex M B0, u ≤ w → v ≤ w → j ≤ w := by
  obtain ⟨a, hau, hav⟩ := exists_common_lower u v
  exact exists_join_of_common_lower u v a hau hav

/-- A chosen actual join. Its independence of all earlier choices follows
from the proved least-upper-bound property and antisymmetry. -/
noncomputable def binaryJoin (u v : IncomingVertex M B0) : IncomingVertex M B0 :=
  Classical.choose (exists_join u v)

theorem le_binaryJoin_left (u v : IncomingVertex M B0) : u ≤ binaryJoin u v :=
  (Classical.choose_spec (exists_join u v)).1

theorem le_binaryJoin_right (u v : IncomingVertex M B0) : v ≤ binaryJoin u v :=
  (Classical.choose_spec (exists_join u v)).2.1

theorem binaryJoin_le {u v w : IncomingVertex M B0} (huw : u ≤ w) (hvw : v ≤ w) :
    binaryJoin u v ≤ w := (Classical.choose_spec (exists_join u v)).2.2 w huw hvw

theorem binaryJoin_eq_of_lub {u v j : IncomingVertex M B0} (huj : u ≤ j) (hvj : v ≤ j)
    (hleast : ∀ w : IncomingVertex M B0, u ≤ w → v ≤ w → j ≤ w) : binaryJoin u v = j :=
  le_antisymm (binaryJoin_le huj hvj) (hleast _ (le_binaryJoin_left u v) (le_binaryJoin_right u v))

theorem binaryJoin_isLUB (u v : IncomingVertex M B0) : IsLUB {u, v} (binaryJoin u v) := by
  constructor
  · intro w hw
    rcases Set.mem_insert_iff.mp hw with h | h
    · subst w
      exact le_binaryJoin_left u v
    · have he : w = v := Set.mem_singleton_iff.mp h
      subst w
      exact le_binaryJoin_right u v
  · intro w hw
    exact binaryJoin_le (hw (Set.mem_insert u {v}))
      (hw (Set.mem_insert_of_mem u (Set.mem_singleton v)))

/-- The incoming join-semilattice is derived from the actual ribbon lcm. -/
noncomputable instance semilatticeSup : SemilatticeSup (IncomingVertex M B0) :=
  SemilatticeSup.ofIsLUB binaryJoin binaryJoin_isLUB

@[simp] theorem binaryJoin_eq_sup (u v : IncomingVertex M B0) : binaryJoin u v = u ⊔ v := rfl

/-- The actual join of a nonempty finite incoming packet, without choosing a
global bottom vertex for the empty packet. -/
noncomputable def finiteJoin (F : Finset (IncomingVertex M B0)) (hF : F.Nonempty) :
    IncomingVertex M B0 := F.sup' hF id

theorem finiteJoin_isLUB (F : Finset (IncomingVertex M B0)) (hF : F.Nonempty) :
    IsLUB (F : Set (IncomingVertex M B0)) (finiteJoin F hF) := Finset.isLUB_sup' hF

theorem le_finiteJoin (F : Finset (IncomingVertex M B0)) (hF : F.Nonempty)
    {u : IncomingVertex M B0} (hu : u ∈ F) : u ≤ finiteJoin F hF := Finset.le_sup' id hu

theorem finiteJoin_le (F : Finset (IncomingVertex M B0)) (hF : F.Nonempty)
    {u : IncomingVertex M B0} (hu : ∀ v ∈ F, v ≤ u) : finiteJoin F hF ≤ u :=
  Finset.sup'_le hF id hu

/-- Packet inclusion is genuinely monotone for the constructed finite joins. -/
theorem finiteJoin_mono {F G : Finset (IncomingVertex M B0)} (hFG : F ⊆ G)
    (hF : F.Nonempty) (hG : G.Nonempty) : finiteJoin F hF ≤ finiteJoin G hG := by
  exact finiteJoin_le F hF (fun u hu => le_finiteJoin G hG (hFG hu))

/-- Every ordered subinterval of an actual simple incoming interval is simple. -/
theorem simple_difference_of_interval {a b u v : IncomingVertex M B0}
    (hs : SimpleRibbon M a.source b.source (a.difference b))
    (hau : a ≤ u) (huv : u ≤ v) (hvb : v ≤ b) :
    SimpleRibbon M u.source v.source (u.difference v) := by
  have htotal : SimpleRibbon M a.source b.source (a.difference u * u.difference b) := by
    simpa only [difference_mul] using hs
  have htail := (SimpleRibbon.factors M htotal hau (huv.trans hvb)).2
  have htail' : SimpleRibbon M u.source b.source (u.difference v * v.difference b) := by
    simpa only [difference_mul] using htail
  exact (SimpleRibbon.factors M htail' huv hvb).1

/-- The finite join remains inside an actual simple interval containing a
nonempty packet. Both bounding factors and all packet-to-join factors are simple. -/
theorem finiteJoin_simple_interval (F : Finset (IncomingVertex M B0)) (hF : F.Nonempty)
    (a b : IncomingVertex M B0) (ha : ∀ v ∈ F, a ≤ v) (hb : ∀ v ∈ F, v ≤ b)
    (hs : SimpleRibbon M a.source b.source (a.difference b)) :
    a ≤ finiteJoin F hF ∧ finiteJoin F hF ≤ b ∧
      SimpleRibbon M a.source (finiteJoin F hF).source (a.difference (finiteJoin F hF)) ∧
      SimpleRibbon M (finiteJoin F hF).source b.source ((finiteJoin F hF).difference b) ∧
      ∀ v ∈ F, SimpleRibbon M v.source (finiteJoin F hF).source
        (v.difference (finiteJoin F hF)) := by
  let v := hF.choose
  have hv : v ∈ F := hF.choose_spec
  have haj : a ≤ finiteJoin F hF := (ha v hv).trans (le_finiteJoin F hF hv)
  have hjb : finiteJoin F hF ≤ b := finiteJoin_le F hF hb
  refine ⟨haj, hjb,
    simple_difference_of_interval hs le_rfl haj hjb,
    simple_difference_of_interval hs haj hjb le_rfl, ?_⟩
  intro w hw
  exact simple_difference_of_interval hs (ha w hw) (le_finiteJoin F hF hw) hjb

end IncomingVertex

end ArtinNormalisers.Deligne5
