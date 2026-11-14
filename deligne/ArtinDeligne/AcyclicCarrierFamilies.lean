module

public import ArtinDeligne.ParametricExtension
public import ArtinDeligne.ParametricFaceGluing
public import ArtinDeligneVendor.Topology.Realization.SimplexFaceGluing
public import Mathlib.Data.Fintype.EquivFin

/-! Coherent maps in actual finite geometric simplices, constructed from
contractible monotone carriers. The finite-face predicate may include being a
chain in any partial order; no global linear extension is needed. -/
@[expose] public section
set_option autoImplicit false
attribute [local instance] Classical.decEq Classical.propDecidable

namespace ArtinNormalisers.Deligne5

open Convexity Topology
open scoped unitInterval

universe u v
variable {P : Type u} {Y : Type v} [TopologicalSpace Y]

/-- Zero-coordinate insertion along an inclusion of finite vertex sets. -/
def carrierFaceInclusion {A B : Finset P} (h : A ⊆ B) : A → B :=
  fun a ↦ ⟨a.val, h a.property⟩

lemma carrierFaceInclusion_injective {A B : Finset P} (h : A ⊆ B) :
    Function.Injective (carrierFaceInclusion h) := by
  intro a b hab
  exact Subtype.ext (congrArg (fun z : B ↦ z.val) hab)

lemma carrierFaceInclusion_comp {A B C : Finset P} (hAB : A ⊆ B) (hBC : B ⊆ C) :
    carrierFaceInclusion hBC ∘ carrierFaceInclusion hAB =
      carrierFaceInclusion (hAB.trans hBC) := rfl

/-- Equal points of two geometric faces have an actual common preimage in
 their intersection. No intersection compatibility is assumed. -/
lemma carrierFace_intersection_preimage {A B C : Finset P}
    (hAC : A ⊆ C) (hBC : B ⊆ C)
    (x : StdSimplex ℝ A) (y : StdSimplex ℝ B)
    (hxy : x.map (carrierFaceInclusion hAC) = y.map (carrierFaceInclusion hBC)) :
    ∃ z : StdSimplex ℝ (↥(A ∩ B : Finset P)),
      z.map (carrierFaceInclusion Finset.inter_subset_left) = x ∧
      z.map (carrierFaceInclusion Finset.inter_subset_right) = y := by
  classical
  have hxrange : x ∈ Set.range (StdSimplex.map
      (carrierFaceInclusion (Finset.inter_subset_left : A ∩ B ⊆ A))) := by
    apply (StdSimplex.mem_range_map_iff _ x).mpr
    intro a ha
    have haB : a.val ∉ B := by
      intro h
      exact ha ⟨⟨a.val, Finset.mem_inter.mpr ⟨a.property, h⟩⟩, Subtype.ext rfl⟩
    have hn : carrierFaceInclusion hAC a ∉ Set.range (carrierFaceInclusion hBC) := by
      rintro ⟨b, hb⟩
      exact haB ((congrArg (fun z : C ↦ z.val) hb) ▸ b.property)
    have hz : (y.map (carrierFaceInclusion hBC)).weights (carrierFaceInclusion hAC a) = 0 :=
      Finsupp.mapDomain_of_notMem_range y.weights _ hn
    rw [← hxy, StdSimplex.map_apply_injective (carrierFaceInclusion_injective hAC)] at hz
    exact hz
  obtain ⟨z, hz⟩ := hxrange
  refine ⟨z, hz, StdSimplex.simplex_map_injective (carrierFaceInclusion_injective hBC) ?_⟩
  rw [StdSimplex.map_map, ← hxy, ← hz, StdSimplex.map_map]
  rfl

/-- The supplied carrier data contain contractibility and monotonicity only,
not maps, extensions, homotopies, or coherence conclusions. -/
structure FiniteCarrierData (P : Type u) (Y : Type v) [TopologicalSpace Y] where
  admissible : Finset P → Prop
  hereditary : ∀ {A B}, A ⊆ B → admissible B → admissible A
  carrier : Finset P → Set Y
  contractible : ∀ F, F.Nonempty → admissible F → ContractibleSpace (carrier F)
  monotone : ∀ {A B}, A ⊆ B → A.Nonempty → admissible B → carrier A ⊆ carrier B

/-- A finite-cardinality stage of the construction. -/
structure PartialCarrierFamily (D : FiniteCarrierData P Y) (n : ℕ) where
  map : ∀ F : Finset P, F.Nonempty → D.admissible F → F.card ≤ n →
    C(StdSimplex ℝ F, Y)
  carried : ∀ F hne hF hn x, map F hne hF hn x ∈ D.carrier F
  compatible : ∀ {A B} (hA : A.Nonempty) (hB : B.Nonempty)
    (ha : D.admissible A) (hb : D.admissible B)
    (hAn : A.card ≤ n) (hBn : B.card ≤ n) (hAB : A ⊆ B) (x : StdSimplex ℝ A),
    map B hB hb hBn (x.map (carrierFaceInclusion hAB)) = map A hA ha hAn x

namespace PartialCarrierFamily

variable {D : FiniteCarrierData P Y} {n : ℕ}

/-- Coherence on smaller faces already gives equality on every actual overlap. -/
lemma eq_of_map_eq (f : PartialCarrierFamily D n) {A B C : Finset P}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (ha : D.admissible A) (hb : D.admissible B)
    (hAn : A.card ≤ n) (hBn : B.card ≤ n)
    (hAC : A ⊆ C) (hBC : B ⊆ C)
    (x : StdSimplex ℝ A) (y : StdSimplex ℝ B)
    (hxy : x.map (carrierFaceInclusion hAC) = y.map (carrierFaceInclusion hBC)) :
    f.map A hA ha hAn x = f.map B hB hb hBn y := by
  obtain ⟨z, hzx, hzy⟩ := carrierFace_intersection_preimage hAC hBC x y hxy
  obtain ⟨a, _⟩ := z.support_weights_nonempty
  have hne : (A ∩ B).Nonempty := ⟨a.val, a.property⟩
  have had : D.admissible (A ∩ B) := D.hereditary Finset.inter_subset_left ha
  have hcard : (A ∩ B).card ≤ n := (Finset.card_le_card Finset.inter_subset_left).trans hAn
  rw [← hzx, ← hzy,
    f.compatible hne hA had ha hcard hAn Finset.inter_subset_left,
    f.compatible hne hB had hb hcard hBn Finset.inter_subset_right]


/-- Extend one new finite face using only the already constructed lower faces.
The conclusion retains compatibility with every smaller face, not only facets. -/
theorem exists_face_extension (f : PartialCarrierFamily D n)
    (F : Finset P) (hne : F.Nonempty) (hF : D.admissible F) (hc : F.card = n + 1) :
    ∃ g : C(StdSimplex ℝ F, Y),
      (∀ x, g x ∈ D.carrier F) ∧
      ∀ G (hneG : G.Nonempty) (hG : D.admissible G) (hGn : G.card ≤ n)
        (hGF : G ⊆ F) (x : StdSimplex ℝ G),
        g (x.map (carrierFaceInclusion hGF)) = f.map G hneG hG hGn x := by
  classical
  let _ := D.contractible F hne hF
  cases n with
  | zero =>
    obtain ⟨z, _⟩ := id_nullhomotopic (D.carrier F)
    refine ⟨ContinuousMap.const _ z.val, fun _ ↦ z.property, ?_⟩
    intro G hneG hG hGn
    have := hneG.card_pos
    omega
  | succ k =>
    let e : Fin (k + 2) ≃ F := (F.equivFinOfCardEq hc).symm
    let A (i : Fin (k + 2)) : Finset P := F.erase (e i).val
    have hAF (i : Fin (k + 2)) : A i ⊆ F := Finset.erase_subset _ _
    have hAc (i : Fin (k + 2)) : (A i).card = k + 1 := by
      dsimp [A]
      rw [Finset.card_erase_of_mem (e i).property, hc]
      omega
    have hAn (i : Fin (k + 2)) : (A i).card ≤ k + 1 := (hAc i).le
    have hAe (i : Fin (k + 2)) : (A i).Nonempty :=
      Finset.card_pos.mp (by rw [hAc]; omega)
    have hAd (i : Fin (k + 2)) : D.admissible (A i) := D.hereditary (hAF i) hF
    let v (i : Fin (k + 2)) : Fin (k + 1) → A i := fun j ↦
      ⟨(e (i.succAbove j)).val, Finset.mem_erase.mpr
        ⟨fun he ↦ Fin.succAbove_ne i j (e.injective (Subtype.ext he)),
          (e (i.succAbove j)).property⟩⟩
    have hv (i : Fin (k + 2)) : carrierFaceInclusion (hAF i) ∘ v i = e ∘ i.succAbove := rfl
    let H (i : Fin (k + 2)) : C(StdSimplex ℝ (Fin (k + 1)) × I, D.carrier F) :=
      ⟨fun q ↦ ⟨f.map (A i) (hAe i) (hAd i) (hAn i) (q.1.map (v i)),
        D.monotone (hAF i) (hAe i) hF (f.carried _ _ _ _ _)⟩,
        ((f.map (A i) (hAe i) (hAd i) (hAn i)).continuous.comp
          ((StdSimplex.continuous_map ℝ (v i)).comp continuous_fst)).subtype_mk _⟩
    have hcompat (i j : Fin (k + 2)) (x y : StdSimplex ℝ (Fin (k + 1))) (t : I)
        (hxy : x.map i.succAbove = y.map j.succAbove) : H i (x, t) = H j (y, t) := by
      apply Subtype.ext
      exact f.eq_of_map_eq (hAe i) (hAe j) (hAd i) (hAd j) (hAn i) (hAn j)
        (hAF i) (hAF j) (x.map (v i)) (y.map (v j)) (by
          simpa only [StdSimplex.map_map, ← Function.comp_def, hv] using
            congrArg (StdSimplex.map e) hxy)
    obtain ⟨B, hB⟩ := StdSimplex.exists_simplex_boundary_track k H hcompat
    let b : C(PUnit.{1} × StdSimplex.boundary (k + 1), D.carrier F) :=
      ⟨fun q ↦ B (q.2, 0), by fun_prop⟩
    obtain ⟨L, hL⟩ := exists_parameterized_simplex_extension (k + 1) b
    let g : C(StdSimplex ℝ F, Y) :=
      ⟨fun q ↦ (L (PUnit.unit, q.map e.symm)).val, by fun_prop⟩
    refine ⟨g, fun q ↦ (L (PUnit.unit, q.map e.symm)).property, ?_⟩
    intro G hneG hG hGn hGF x
    have hlt : G.card < F.card := by omega
    have hnsub : ¬F ⊆ G := fun h ↦ (not_lt_of_ge (Finset.card_le_card h)) hlt
    obtain ⟨a, haF, haG⟩ := Finset.not_subset.mp hnsub
    let i : Fin (k + 2) := e.symm ⟨a, haF⟩
    let q := (x.map (carrierFaceInclusion hGF)).map e.symm
    have hqi : q.weights i = 0 := by
      rw [show q = x.map (e.symm ∘ carrierFaceInclusion hGF) from
        (StdSimplex.map_map _ _ _)]
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨j, hj⟩
      have he := congrArg (fun t ↦ (e t).val) hj
      exact haG (show a ∈ G from (by simpa [i] using he) ▸ j.property)
    obtain ⟨z, hz⟩ := (StdSimplex.mem_range_map_succAbove_iff i q).mpr hqi
    have hqe : q.map e = x.map (carrierFaceInclusion hGF) := by
      dsimp [q]
      rw [StdSimplex.map_map]
      rw [show (fun a : F ↦ e (e.symm a)) = id from funext e.apply_symm_apply,
        StdSimplex.map_id]
    have hfz : (z.map (v i)).map (carrierFaceInclusion (hAF i)) =
        x.map (carrierFaceInclusion hGF) := by
      rw [StdSimplex.map_map]
      change z.map (e ∘ i.succAbove) = _
      rw [StdSimplex.map_comp, hz, hqe]
    have hface : g (x.map (carrierFaceInclusion hGF)) =
        f.map (A i) (hAe i) (hAd i) (hAn i) (z.map (v i)) := by
      change (L (PUnit.unit, q)).val = _
      have hbq : (⟨q, i, hqi⟩ : StdSimplex.boundary (k + 1)) =
          StdSimplex.simplexBoundaryFace k i z := Subtype.ext hz.symm
      have h := congrArg Subtype.val (hL PUnit.unit ⟨q, i, hqi⟩)
      change (L (PUnit.unit, q)).val = _ at h
      rw [show b (PUnit.unit, ⟨q, i, hqi⟩) = B (⟨q, i, hqi⟩, 0) from rfl,
        hbq, hB] at h
      exact h
    exact hface.trans (f.eq_of_map_eq (hAe i) hneG (hAd i) hG (hAn i) hGn
      (hAF i) hGF (z.map (v i)) x hfz)


/-- The empty stage contains no nonempty face. -/
def empty (D : FiniteCarrierData P Y) : PartialCarrierFamily D 0 where
  map _F hne _ hn := False.elim ((not_lt_of_ge hn) hne.card_pos)
  carried _F hne _ hn := False.elim ((not_lt_of_ge hn) hne.card_pos)
  compatible hA _ _ _ hAn := False.elim ((not_lt_of_ge hAn) hA.card_pos)

/-- One cardinality step, with every filler obtained from actual HEP. -/
noncomputable def next (f : PartialCarrierFamily D n) : PartialCarrierFamily D (n + 1) := by
  classical
  let g (F : Finset P) (hne : F.Nonempty) (hF : D.admissible F) (hFn : F.card ≤ n + 1) :
      C(StdSimplex ℝ F, Y) :=
    if h : F.card ≤ n then f.map F hne hF h
    else (f.exists_face_extension F hne hF (by omega)).choose
  have hg (F : Finset P) (hne : F.Nonempty) (hF : D.admissible F)
      (hFn : F.card ≤ n + 1) (h : ¬F.card ≤ n) :=
    (f.exists_face_extension F hne hF (show F.card = n + 1 by omega)).choose_spec
  refine ⟨g, ?_, ?_⟩
  · intro F hne hF hn x
    by_cases h : F.card ≤ n
    · simpa only [g, dite_eq_left h] using f.carried F hne hF h x
    · simpa only [g, dite_eq_right h] using (hg F hne hF hn h).1 x
  · intro A B hA hB ha hb hAn hBn hAB x
    by_cases hBsmall : B.card ≤ n
    · have hAsmall := (Finset.card_le_card hAB).trans hBsmall
      simpa only [g, dite_eq_left hBsmall, dite_eq_left hAsmall] using
        f.compatible hA hB ha hb hAsmall hBsmall hAB x
    · by_cases hAsmall : A.card ≤ n
      · simpa only [g, dite_eq_right hBsmall, dite_eq_left hAsmall] using
          (hg B hB hb hBn hBsmall).2 A hA ha hAsmall hAB x
      · have heq : A = B := Finset.eq_of_subset_of_card_le hAB (by omega)
        subst B
        have hi : carrierFaceInclusion hAB = id := rfl
        rw [hi, StdSimplex.map_id]

lemma next_map_old (f : PartialCarrierFamily D n) (F : Finset P)
    (hne : F.Nonempty) (hF : D.admissible F) (hn : F.card ≤ n) :
    f.next.map F hne hF (hn.trans (Nat.le_succ n)) = f.map F hne hF hn := by
  simp only [next, dite_eq_left hn]

/-- Cardinal recursion supplies stages in every dimension. -/
noncomputable def stages (D : FiniteCarrierData P Y) : (n : ℕ) → PartialCarrierFamily D n
  | 0 => empty D
  | n + 1 => (stages D n).next

lemma stages_map_stable (D : FiniteCarrierData P Y) {m n : ℕ} (hmn : m ≤ n)
    (F : Finset P) (hne : F.Nonempty) (hF : D.admissible F) (hFm : F.card ≤ m) :
    (stages D n).map F hne hF (hFm.trans hmn) = (stages D m).map F hne hF hFm := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    exact ((stages D n).next_map_old F hne hF (hFm.trans hmn)).trans ih

end PartialCarrierFamily


/-- A coherent all-dimensional family, here a constructed conclusion. -/
structure CarrierFamily (D : FiniteCarrierData P Y) where
  map : ∀ F : Finset P, F.Nonempty → D.admissible F → C(StdSimplex ℝ F, Y)
  carried : ∀ F hne hF x, map F hne hF x ∈ D.carrier F
  compatible : ∀ {A B} (hA : A.Nonempty) (hB : B.Nonempty)
    (ha : D.admissible A) (hb : D.admissible B) (hAB : A ⊆ B) (x : StdSimplex ℝ A),
    map B hB hb (x.map (carrierFaceInclusion hAB)) = map A hA ha x

/-- Monotone actual contractible carriers admit coherent geometric simplex
maps in every finite dimension. No coherent family is an input. -/
noncomputable def FiniteCarrierData.family (D : FiniteCarrierData P Y) : CarrierFamily D where
  map F hne hF := (PartialCarrierFamily.stages D F.card).map F hne hF le_rfl
  carried F hne hF := (PartialCarrierFamily.stages D F.card).carried F hne hF le_rfl
  compatible {A B} hA hB ha hb hAB x := by
    have hn := Finset.card_le_card hAB
    exact ((PartialCarrierFamily.stages D B.card).compatible hA hB ha hb hn le_rfl hAB x).trans
      (ContinuousMap.congr_fun (PartialCarrierFamily.stages_map_stable D hn A hA ha le_rfl) x)


/-- Finite stages of coherent endpoint-preserving homotopies. -/
structure PartialCarrierHomotopy (D : FiniteCarrierData P Y)
    (f₀ f₁ : CarrierFamily D) (n : ℕ) where
  hom : ∀ F : Finset P, (hne : F.Nonempty) → (hF : D.admissible F) → F.card ≤ n →
    ContinuousMap.Homotopy (f₀.map F hne hF) (f₁.map F hne hF)
  carried : ∀ F hne hF hn t x, hom F hne hF hn (t, x) ∈ D.carrier F
  compatible : ∀ {A B} (hA : A.Nonempty) (hB : B.Nonempty)
    (ha : D.admissible A) (hb : D.admissible B)
    (hAn : A.card ≤ n) (hBn : B.card ≤ n) (hAB : A ⊆ B) (t : I) (x : StdSimplex ℝ A),
    hom B hB hb hBn (t, x.map (carrierFaceInclusion hAB)) = hom A hA ha hAn (t, x)

namespace PartialCarrierHomotopy
variable {D : FiniteCarrierData P Y} {f₀ f₁ : CarrierFamily D} {n : ℕ}

lemma eq_of_map_eq (f : PartialCarrierHomotopy D f₀ f₁ n) {A B C : Finset P}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (ha : D.admissible A) (hb : D.admissible B)
    (hAn : A.card ≤ n) (hBn : B.card ≤ n)
    (hAC : A ⊆ C) (hBC : B ⊆ C) (t : I)
    (x : StdSimplex ℝ A) (y : StdSimplex ℝ B)
    (hxy : x.map (carrierFaceInclusion hAC) = y.map (carrierFaceInclusion hBC)) :
    f.hom A hA ha hAn (t, x) = f.hom B hB hb hBn (t, y) := by
  obtain ⟨z, hzx, hzy⟩ := carrierFace_intersection_preimage hAC hBC x y hxy
  obtain ⟨a, _⟩ := z.support_weights_nonempty
  have hne : (A ∩ B).Nonempty := ⟨a.val, a.property⟩
  have had : D.admissible (A ∩ B) := D.hereditary Finset.inter_subset_left ha
  have hcard : (A ∩ B).card ≤ n := (Finset.card_le_card Finset.inter_subset_left).trans hAn
  rw [← hzx, ← hzy,
    f.compatible hne hA had ha hcard hAn Finset.inter_subset_left,
    f.compatible hne hB had hb hcard hBn Finset.inter_subset_right]

lemma map_equiv_cancel {A : Type*} {B : Type*} (e : A ≃ B) (x : StdSimplex ℝ B) :
    (x.map e.symm).map e = x := by
  rw [StdSimplex.map_map,
    show (fun a ↦ e (e.symm a)) = id from funext e.apply_symm_apply,
    StdSimplex.map_id]

/-- A single new homotopy face is filled by actual endpoint-relative HEP. -/
theorem exists_face_extension (f : PartialCarrierHomotopy D f₀ f₁ n)
    (F : Finset P) (hne : F.Nonempty) (hF : D.admissible F) (hc : F.card = n + 1) :
    ∃ g : ContinuousMap.Homotopy (f₀.map F hne hF) (f₁.map F hne hF),
      (∀ t x, g (t, x) ∈ D.carrier F) ∧
      ∀ G (hneG : G.Nonempty) (hG : D.admissible G) (hGn : G.card ≤ n)
        (hGF : G ⊆ F) (t : I) (x : StdSimplex ℝ G),
        g (t, x.map (carrierFaceInclusion hGF)) = f.hom G hneG hG hGn (t, x) := by
  classical
  let _ := D.contractible F hne hF
  let a₀ : C(StdSimplex ℝ F, D.carrier F) :=
    ⟨fun x ↦ ⟨f₀.map F hne hF x, f₀.carried F hne hF x⟩,
      (f₀.map F hne hF).continuous.subtype_mk _⟩
  let a₁ : C(StdSimplex ℝ F, D.carrier F) :=
    ⟨fun x ↦ ⟨f₁.map F hne hF x, f₁.carried F hne hF x⟩,
      (f₁.map F hne hF).continuous.subtype_mk _⟩
  cases n with
  | zero =>
    obtain ⟨z, ⟨L⟩⟩ := id_nullhomotopic (D.carrier F)
    let L₀ : ContinuousMap.Homotopy a₀ (ContinuousMap.const _ z) :=
      (L.compContinuousMap a₀).cast (by ext; rfl) (by ext; rfl)
    let L₁ : ContinuousMap.Homotopy a₁ (ContinuousMap.const _ z) :=
      (L.compContinuousMap a₁).cast (by ext; rfl) (by ext; rfl)
    let K := L₀.trans L₁.symm
    let g : ContinuousMap.Homotopy (f₀.map F hne hF) (f₁.map F hne hF) :=
      ⟨⟨fun p ↦ (K p).val, by fun_prop⟩,
        fun x ↦ congrArg Subtype.val (K.apply_zero x),
        fun x ↦ congrArg Subtype.val (K.apply_one x)⟩
    refine ⟨g, fun t x ↦ (K (t, x)).property, ?_⟩
    intro G hneG hG hGn
    have := hneG.card_pos
    omega
  | succ k =>
    let e : Fin (k + 2) ≃ F := (F.equivFinOfCardEq hc).symm
    let A (i : Fin (k + 2)) : Finset P := F.erase (e i).val
    have hAF (i : Fin (k + 2)) : A i ⊆ F := Finset.erase_subset _ _
    have hAc (i : Fin (k + 2)) : (A i).card = k + 1 := by
      dsimp [A]
      rw [Finset.card_erase_of_mem (e i).property, hc]
      omega
    have hAn (i : Fin (k + 2)) : (A i).card ≤ k + 1 := (hAc i).le
    have hAe (i : Fin (k + 2)) : (A i).Nonempty :=
      Finset.card_pos.mp (by rw [hAc]; omega)
    have hAd (i : Fin (k + 2)) : D.admissible (A i) := D.hereditary (hAF i) hF
    let v (i : Fin (k + 2)) : Fin (k + 1) → A i := fun j ↦
      ⟨(e (i.succAbove j)).val, Finset.mem_erase.mpr
        ⟨fun he ↦ Fin.succAbove_ne i j (e.injective (Subtype.ext he)),
          (e (i.succAbove j)).property⟩⟩
    have hv (i : Fin (k + 2)) : carrierFaceInclusion (hAF i) ∘ v i = e ∘ i.succAbove := rfl
    let H (i : Fin (k + 2)) : C(StdSimplex ℝ (Fin (k + 1)) × I, D.carrier F) :=
      ⟨fun q ↦ ⟨f.hom (A i) (hAe i) (hAd i) (hAn i) (q.2, q.1.map (v i)),
        D.monotone (hAF i) (hAe i) hF (f.carried _ _ _ _ _ _)⟩,
        ((f.hom (A i) (hAe i) (hAd i) (hAn i)).continuous.comp
          (continuous_snd.prodMk ((StdSimplex.continuous_map ℝ (v i)).comp continuous_fst))).subtype_mk _⟩
    have hcompat (i j : Fin (k + 2)) (x y : StdSimplex ℝ (Fin (k + 1))) (t : I)
        (hxy : x.map i.succAbove = y.map j.succAbove) : H i (x, t) = H j (y, t) := by
      apply Subtype.ext
      exact f.eq_of_map_eq (hAe i) (hAe j) (hAd i) (hAd j) (hAn i) (hAn j)
        (hAF i) (hAF j) t (x.map (v i)) (y.map (v j)) (by
          simpa only [StdSimplex.map_map, ← Function.comp_def, hv] using
            congrArg (StdSimplex.map e) hxy)
    obtain ⟨B, hB⟩ := StdSimplex.exists_simplex_boundary_track k H hcompat
    let b : C(I × StdSimplex.boundary (k + 1), D.carrier F) :=
      ⟨fun q ↦ B (q.2, q.1), by fun_prop⟩
    let g₀ : C(StdSimplex ℝ (Fin (k + 2)), D.carrier F) :=
      a₀.comp ⟨StdSimplex.map e, StdSimplex.continuous_map ℝ e⟩
    let g₁ : C(StdSimplex ℝ (Fin (k + 2)), D.carrier F) :=
      a₁.comp ⟨StdSimplex.map e, StdSimplex.continuous_map ℝ e⟩
    have hb₀ (q : StdSimplex.boundary (k + 1)) : b (0, q) = g₀ q.val := by
      obtain ⟨i, hi⟩ := q.property
      obtain ⟨z, hz⟩ := (StdSimplex.mem_range_map_succAbove_iff i q.val).mpr hi
      have heq : StdSimplex.simplexBoundaryFace k i z = q := Subtype.ext hz
      change B (q, 0) = _
      rw [← heq, hB]
      apply Subtype.ext
      change f.hom _ _ _ _ (0, z.map (v i)) = f₀.map F hne hF ((z.map i.succAbove).map e)
      rw [ContinuousMap.Homotopy.apply_zero]
      simpa only [StdSimplex.map_map, ← Function.comp_def, hv] using
        (f₀.compatible (hAe i) hne (hAd i) hF (hAF i) (z.map (v i))).symm
    have hb₁ (q : StdSimplex.boundary (k + 1)) : b (1, q) = g₁ q.val := by
      obtain ⟨i, hi⟩ := q.property
      obtain ⟨z, hz⟩ := (StdSimplex.mem_range_map_succAbove_iff i q.val).mpr hi
      have heq : StdSimplex.simplexBoundaryFace k i z = q := Subtype.ext hz
      change B (q, 1) = _
      rw [← heq, hB]
      apply Subtype.ext
      change f.hom _ _ _ _ (1, z.map (v i)) = f₁.map F hne hF ((z.map i.succAbove).map e)
      rw [ContinuousMap.Homotopy.apply_one]
      simpa only [StdSimplex.map_map, ← Function.comp_def, hv] using
        (f₁.compatible (hAe i) hne (hAd i) hF (hAF i) (z.map (v i))).symm
    obtain ⟨L, hL⟩ := exists_simplex_boundary_homotopy_extension (k + 1) g₀ g₁ b hb₀ hb₁
    let g : ContinuousMap.Homotopy (f₀.map F hne hF) (f₁.map F hne hF) :=
      ⟨⟨fun p ↦ (L (p.1, p.2.map e.symm)).val, by fun_prop⟩,
        fun x ↦ (congrArg Subtype.val (L.apply_zero (x.map e.symm))).trans
          (congrArg (f₀.map F hne hF) (map_equiv_cancel e x)),
        fun x ↦ (congrArg Subtype.val (L.apply_one (x.map e.symm))).trans
          (congrArg (f₁.map F hne hF) (map_equiv_cancel e x))⟩
    refine ⟨g, fun t x ↦ (L (t, x.map e.symm)).property, ?_⟩
    intro G hneG hG hGn hGF t x
    have hlt : G.card < F.card := by omega
    have hnsub : ¬F ⊆ G := fun h ↦ (not_lt_of_ge (Finset.card_le_card h)) hlt
    obtain ⟨a, haF, haG⟩ := Finset.not_subset.mp hnsub
    let i : Fin (k + 2) := e.symm ⟨a, haF⟩
    let q := (x.map (carrierFaceInclusion hGF)).map e.symm
    have hqi : q.weights i = 0 := by
      rw [show q = x.map (e.symm ∘ carrierFaceInclusion hGF) from
        (StdSimplex.map_map _ _ _)]
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨j, hj⟩
      have he := congrArg (fun s ↦ (e s).val) hj
      exact haG (show a ∈ G from (by simpa [i] using he) ▸ j.property)
    obtain ⟨z, hz⟩ := (StdSimplex.mem_range_map_succAbove_iff i q).mpr hqi
    have hqe : q.map e = x.map (carrierFaceInclusion hGF) := map_equiv_cancel e _
    have hfz : (z.map (v i)).map (carrierFaceInclusion (hAF i)) =
        x.map (carrierFaceInclusion hGF) := by
      rw [StdSimplex.map_map]
      change z.map (e ∘ i.succAbove) = _
      rw [StdSimplex.map_comp, hz, hqe]
    have hface : g (t, x.map (carrierFaceInclusion hGF)) =
        f.hom (A i) (hAe i) (hAd i) (hAn i) (t, z.map (v i)) := by
      change (L (t, q)).val = _
      have hbq : (⟨q, i, hqi⟩ : StdSimplex.boundary (k + 1)) =
          StdSimplex.simplexBoundaryFace k i z := Subtype.ext hz.symm
      have h := congrArg Subtype.val (hL t ⟨q, i, hqi⟩)
      change (L (t, q)).val = _ at h
      rw [show b (t, ⟨q, i, hqi⟩) = B (⟨q, i, hqi⟩, t) from rfl,
        hbq, hB] at h
      exact h
    exact hface.trans (f.eq_of_map_eq (hAe i) hneG (hAd i) hG (hAn i) hGn
      (hAF i) hGF t (z.map (v i)) x hfz)


/-- No nonempty face occurs at homotopy stage zero. -/
def empty (D : FiniteCarrierData P Y) (f₀ f₁ : CarrierFamily D) :
    PartialCarrierHomotopy D f₀ f₁ 0 where
  hom _F hne _ hn := False.elim ((not_lt_of_ge hn) hne.card_pos)
  carried _F hne _ hn := False.elim ((not_lt_of_ge hn) hne.card_pos)
  compatible hA _ _ _ hAn := False.elim ((not_lt_of_ge hAn) hA.card_pos)

/-- A homotopy stage is extended by the proved relative cylinder filler. -/
noncomputable def next (f : PartialCarrierHomotopy D f₀ f₁ n) :
    PartialCarrierHomotopy D f₀ f₁ (n + 1) := by
  classical
  let g (F : Finset P) (hne : F.Nonempty) (hF : D.admissible F) (hFn : F.card ≤ n + 1) :
      ContinuousMap.Homotopy (f₀.map F hne hF) (f₁.map F hne hF) :=
    if h : F.card ≤ n then f.hom F hne hF h
    else (f.exists_face_extension F hne hF (by omega)).choose
  have hg (F : Finset P) (hne : F.Nonempty) (hF : D.admissible F)
      (hFn : F.card ≤ n + 1) (h : ¬F.card ≤ n) :=
    (f.exists_face_extension F hne hF (show F.card = n + 1 by omega)).choose_spec
  refine ⟨g, ?_, ?_⟩
  · intro F hne hF hn t x
    by_cases h : F.card ≤ n
    · simpa only [g, dite_eq_left h] using f.carried F hne hF h t x
    · simpa only [g, dite_eq_right h] using (hg F hne hF hn h).1 t x
  · intro A B hA hB ha hb hAn hBn hAB t x
    by_cases hBsmall : B.card ≤ n
    · have hAsmall := (Finset.card_le_card hAB).trans hBsmall
      simpa only [g, dite_eq_left hBsmall, dite_eq_left hAsmall] using
        f.compatible hA hB ha hb hAsmall hBsmall hAB t x
    · by_cases hAsmall : A.card ≤ n
      · simpa only [g, dite_eq_right hBsmall, dite_eq_left hAsmall] using
          (hg B hB hb hBn hBsmall).2 A hA ha hAsmall hAB t x
      · have heq : A = B := Finset.eq_of_subset_of_card_le hAB (by omega)
        subst B
        have hi : carrierFaceInclusion hAB = id := rfl
        rw [hi, StdSimplex.map_id]

lemma next_hom_old (f : PartialCarrierHomotopy D f₀ f₁ n) (F : Finset P)
    (hne : F.Nonempty) (hF : D.admissible F) (hn : F.card ≤ n) :
    f.next.hom F hne hF (hn.trans (Nat.le_succ n)) = f.hom F hne hF hn := by
  simp only [next, dite_eq_left hn]

/-- All-dimensional homotopy stages are recursively constructed. -/
noncomputable def stages (D : FiniteCarrierData P Y) (f₀ f₁ : CarrierFamily D) :
    (n : ℕ) → PartialCarrierHomotopy D f₀ f₁ n
  | 0 => empty D f₀ f₁
  | n + 1 => (stages D f₀ f₁ n).next

lemma stages_hom_stable (D : FiniteCarrierData P Y) (f₀ f₁ : CarrierFamily D)
    {m n : ℕ} (hmn : m ≤ n)
    (F : Finset P) (hne : F.Nonempty) (hF : D.admissible F) (hFm : F.card ≤ m) :
    (stages D f₀ f₁ n).hom F hne hF (hFm.trans hmn) =
      (stages D f₀ f₁ m).hom F hne hF hFm := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    exact ((stages D f₀ f₁ n).next_hom_old F hne hF (hFm.trans hmn)).trans ih

end PartialCarrierHomotopy


/-- Coherent carried homotopies, constructed below from two carried families. -/
structure CarrierHomotopy {D : FiniteCarrierData P Y} (f₀ f₁ : CarrierFamily D) where
  hom : ∀ F : Finset P, (hne : F.Nonempty) → (hF : D.admissible F) →
    ContinuousMap.Homotopy (f₀.map F hne hF) (f₁.map F hne hF)
  carried : ∀ F hne hF t x, hom F hne hF (t, x) ∈ D.carrier F
  compatible : ∀ {A B} (hA : A.Nonempty) (hB : B.Nonempty)
    (ha : D.admissible A) (hb : D.admissible B) (hAB : A ⊆ B) (t : I) (x : StdSimplex ℝ A),
    hom B hB hb (t, x.map (carrierFaceInclusion hAB)) = hom A hA ha (t, x)

/-- Any two carried coherent families admit an actual coherent homotopy in
all finite dimensions, retaining the whole original carrier on each face. -/
noncomputable def CarrierFamily.homotopy {D : FiniteCarrierData P Y}
    (f₀ f₁ : CarrierFamily D) : CarrierHomotopy f₀ f₁ where
  hom F hne hF := (PartialCarrierHomotopy.stages D f₀ f₁ F.card).hom F hne hF le_rfl
  carried F hne hF := (PartialCarrierHomotopy.stages D f₀ f₁ F.card).carried F hne hF le_rfl
  compatible {A B} hA hB ha hb hAB t x := by
    have hn := Finset.card_le_card hAB
    exact ((PartialCarrierHomotopy.stages D f₀ f₁ B.card).compatible
      hA hB ha hb hn le_rfl hAB t x).trans
      (congrArg (fun H ↦ H (t, x))
        (PartialCarrierHomotopy.stages_hom_stable D f₀ f₁ hn A hA ha le_rfl))

/-- Full-family coherence implies equality at every actual geometric overlap. -/
lemma CarrierFamily.eq_of_map_eq {D : FiniteCarrierData P Y} (f : CarrierFamily D)
    {A B C : Finset P} (hA : A.Nonempty) (hB : B.Nonempty)
    (ha : D.admissible A) (hb : D.admissible B) (hAC : A ⊆ C) (hBC : B ⊆ C)
    (x : StdSimplex ℝ A) (y : StdSimplex ℝ B)
    (hxy : x.map (carrierFaceInclusion hAC) = y.map (carrierFaceInclusion hBC)) :
    f.map A hA ha x = f.map B hB hb y := by
  obtain ⟨z, hzx, hzy⟩ := carrierFace_intersection_preimage hAC hBC x y hxy
  obtain ⟨a, _⟩ := z.support_weights_nonempty
  have hne : (A ∩ B).Nonempty := ⟨a.val, a.property⟩
  have had : D.admissible (A ∩ B) := D.hereditary Finset.inter_subset_left ha
  rw [← hzx, ← hzy,
    f.compatible hne hA had ha Finset.inter_subset_left,
    f.compatible hne hB had hb Finset.inter_subset_right]

/-- The overlap may also be tested in the original ambient vertex simplex. -/
lemma CarrierFamily.eq_of_map_val_eq {D : FiniteCarrierData P Y} (f : CarrierFamily D)
    {A B : Finset P} (hA : A.Nonempty) (hB : B.Nonempty)
    (ha : D.admissible A) (hb : D.admissible B)
    (x : StdSimplex ℝ A) (y : StdSimplex ℝ B)
    (hxy : x.map Subtype.val = y.map Subtype.val) :
    f.map A hA ha x = f.map B hB hb y := by
  apply f.eq_of_map_eq hA hB ha hb (Finset.subset_union_left) (Finset.subset_union_right) x y
  apply StdSimplex.simplex_map_injective (f := (Subtype.val : (A ∪ B : Finset P) → P))
    Subtype.val_injective
  simpa only [StdSimplex.map_map, carrierFaceInclusion] using hxy


section Parameterized
universe w
variable {X : Type w} [TopologicalSpace X]

/-- Literal restriction of a parameter along antitone source domains. -/
def carrierParameterRestrict {R : Finset P → Set X} (hR : Antitone R)
    {A B : Finset P} (hAB : A ⊆ B) : R B → R A :=
  fun x ↦ ⟨x.val, hR hAB x.property⟩

lemma continuous_carrierParameterRestrict {R : Finset P → Set X} (hR : Antitone R)
    {A B : Finset P} (hAB : A ⊆ B) : Continuous (carrierParameterRestrict hR hAB) :=
  continuous_subtype_val.subtype_mk _

/-- Given endpoint maps on varying actual parameter domains. Coherence here is
only coherence of the given endpoint maps, not a homotopy or extension premise. -/
structure ParameterizedCarrierFamily (D : FiniteCarrierData P Y)
    (R : Finset P → Set X) (hR : Antitone R) where
  map : ∀ F : Finset P, F.Nonempty → D.admissible F → C(R F × StdSimplex ℝ F, Y)
  carried : ∀ F hne hF x z, map F hne hF (x, z) ∈ D.carrier F
  compatible : ∀ {A B} (hA : A.Nonempty) (hB : B.Nonempty)
    (ha : D.admissible A) (hb : D.admissible B) (hAB : A ⊆ B)
    (x : R B) (z : StdSimplex ℝ A),
    map B hB hb (x, z.map (carrierFaceInclusion hAB)) =
      map A hA ha (carrierParameterRestrict hR hAB x, z)

/-- Finite stages for the homotopies, with no contractibility requirement on
any parameter domain. -/
structure PartialParameterizedCarrierHomotopy {D : FiniteCarrierData P Y}
    {R : Finset P → Set X} {hR : Antitone R}
    (f₀ f₁ : ParameterizedCarrierFamily D R hR) (n : ℕ) where
  hom : ∀ F : Finset P, (hne : F.Nonempty) → (hF : D.admissible F) → F.card ≤ n →
    ContinuousMap.Homotopy (f₀.map F hne hF) (f₁.map F hne hF)
  carried : ∀ F hne hF hn t x z, hom F hne hF hn (t, (x, z)) ∈ D.carrier F
  compatible : ∀ {A B} (hA : A.Nonempty) (hB : B.Nonempty)
    (ha : D.admissible A) (hb : D.admissible B)
    (hAn : A.card ≤ n) (hBn : B.card ≤ n) (hAB : A ⊆ B)
    (t : I) (x : R B) (z : StdSimplex ℝ A),
    hom B hB hb hBn (t, (x, z.map (carrierFaceInclusion hAB))) =
      hom A hA ha hAn (t, (carrierParameterRestrict hR hAB x, z))

namespace PartialParameterizedCarrierHomotopy
variable {D : FiniteCarrierData P Y} {R : Finset P → Set X} {hR : Antitone R}
  {f₀ f₁ : ParameterizedCarrierFamily D R hR} {n : ℕ}

/-- Actual geometric overlaps in a common parameter domain have equal values
at every already constructed homotopy stage. -/
lemma eq_of_map_eq (f : PartialParameterizedCarrierHomotopy f₀ f₁ n)
    {A B C : Finset P} (hA : A.Nonempty) (hB : B.Nonempty)
    (ha : D.admissible A) (hb : D.admissible B) (hAn : A.card ≤ n) (hBn : B.card ≤ n)
    (hAC : A ⊆ C) (hBC : B ⊆ C) (t : I) (p : R C)
    (x : StdSimplex ℝ A) (y : StdSimplex ℝ B)
    (hxy : x.map (carrierFaceInclusion hAC) = y.map (carrierFaceInclusion hBC)) :
    f.hom A hA ha hAn (t, (carrierParameterRestrict hR hAC p, x)) =
      f.hom B hB hb hBn (t, (carrierParameterRestrict hR hBC p, y)) := by
  obtain ⟨z, hzx, hzy⟩ := carrierFace_intersection_preimage hAC hBC x y hxy
  obtain ⟨a, _⟩ := z.support_weights_nonempty
  have hne : (A ∩ B).Nonempty := ⟨a.val, a.property⟩
  have had : D.admissible (A ∩ B) := D.hereditary Finset.inter_subset_left ha
  have hcard : (A ∩ B).card ≤ n := (Finset.card_le_card Finset.inter_subset_left).trans hAn
  rw [← hzx, ← hzy,
    f.compatible hne hA had ha hcard hAn Finset.inter_subset_left,
    f.compatible hne hB had hb hcard hBn Finset.inter_subset_right]
  rfl

/-- A single new homotopy face is filled by actual endpoint-relative HEP. -/
theorem exists_face_extension (f : PartialParameterizedCarrierHomotopy f₀ f₁ n)
    (F : Finset P) (hne : F.Nonempty) (hF : D.admissible F) (hc : F.card = n + 1) :
    ∃ g : ContinuousMap.Homotopy (f₀.map F hne hF) (f₁.map F hne hF),
      (∀ t p x, g (t, (p, x)) ∈ D.carrier F) ∧
      ∀ G (hneG : G.Nonempty) (hG : D.admissible G) (hGn : G.card ≤ n)
        (hGF : G ⊆ F) (t : I) (p : R F) (x : StdSimplex ℝ G),
        g (t, (p, x.map (carrierFaceInclusion hGF))) =
          f.hom G hneG hG hGn (t, (carrierParameterRestrict hR hGF p, x)) := by
  classical
  let _ := D.contractible F hne hF
  let a₀ : C(R F × StdSimplex ℝ F, D.carrier F) :=
    ⟨fun x ↦ ⟨f₀.map F hne hF x, f₀.carried F hne hF x.1 x.2⟩,
      (f₀.map F hne hF).continuous.subtype_mk _⟩
  let a₁ : C(R F × StdSimplex ℝ F, D.carrier F) :=
    ⟨fun x ↦ ⟨f₁.map F hne hF x, f₁.carried F hne hF x.1 x.2⟩,
      (f₁.map F hne hF).continuous.subtype_mk _⟩
  cases n with
  | zero =>
    obtain ⟨z, ⟨L⟩⟩ := id_nullhomotopic (D.carrier F)
    let L₀ : ContinuousMap.Homotopy a₀ (ContinuousMap.const _ z) :=
      (L.compContinuousMap a₀).cast (by ext; rfl) (by ext; rfl)
    let L₁ : ContinuousMap.Homotopy a₁ (ContinuousMap.const _ z) :=
      (L.compContinuousMap a₁).cast (by ext; rfl) (by ext; rfl)
    let K := L₀.trans L₁.symm
    let g : ContinuousMap.Homotopy (f₀.map F hne hF) (f₁.map F hne hF) :=
      ⟨⟨fun p ↦ (K p).val, by fun_prop⟩,
        fun x ↦ congrArg Subtype.val (K.apply_zero x),
        fun x ↦ congrArg Subtype.val (K.apply_one x)⟩
    refine ⟨g, fun t p x ↦ (K (t, (p, x))).property, ?_⟩
    intro G hneG hG hGn
    have := hneG.card_pos
    omega
  | succ k =>
    let e : Fin (k + 2) ≃ F := (F.equivFinOfCardEq hc).symm
    let A (i : Fin (k + 2)) : Finset P := F.erase (e i).val
    have hAF (i : Fin (k + 2)) : A i ⊆ F := Finset.erase_subset _ _
    have hAc (i : Fin (k + 2)) : (A i).card = k + 1 := by
      dsimp [A]
      rw [Finset.card_erase_of_mem (e i).property, hc]
      omega
    have hAn (i : Fin (k + 2)) : (A i).card ≤ k + 1 := (hAc i).le
    have hAe (i : Fin (k + 2)) : (A i).Nonempty :=
      Finset.card_pos.mp (by rw [hAc]; omega)
    have hAd (i : Fin (k + 2)) : D.admissible (A i) := D.hereditary (hAF i) hF
    let v (i : Fin (k + 2)) : Fin (k + 1) → A i := fun j ↦
      ⟨(e (i.succAbove j)).val, Finset.mem_erase.mpr
        ⟨fun he ↦ Fin.succAbove_ne i j (e.injective (Subtype.ext he)),
          (e (i.succAbove j)).property⟩⟩
    have hv (i : Fin (k + 2)) : carrierFaceInclusion (hAF i) ∘ v i = e ∘ i.succAbove := rfl
    let H (i : Fin (k + 2)) :
        C(R F × (StdSimplex ℝ (Fin (k + 1)) × I), D.carrier F) :=
      ⟨fun q ↦ ⟨f.hom (A i) (hAe i) (hAd i) (hAn i)
          (q.2.2, (carrierParameterRestrict hR (hAF i) q.1, q.2.1.map (v i))),
        D.monotone (hAF i) (hAe i) hF (f.carried _ _ _ _ _ _ _)⟩,
        ((f.hom (A i) (hAe i) (hAd i) (hAn i)).continuous.comp
          ((continuous_snd.comp continuous_snd).prodMk
            (((continuous_carrierParameterRestrict hR (hAF i)).comp continuous_fst).prodMk
              ((StdSimplex.continuous_map ℝ (v i)).comp
                (continuous_fst.comp continuous_snd))))).subtype_mk _⟩
    have hcompat (i j : Fin (k + 2)) (p : R F) (x y : StdSimplex ℝ (Fin (k + 1))) (t : I)
        (hxy : x.map i.succAbove = y.map j.succAbove) : H i (p, (x, t)) = H j (p, (y, t)) := by
      apply Subtype.ext
      exact f.eq_of_map_eq (hAe i) (hAe j) (hAd i) (hAd j) (hAn i) (hAn j)
        (hAF i) (hAF j) t p (x.map (v i)) (y.map (v j)) (by
          simpa only [StdSimplex.map_map, ← Function.comp_def, hv] using
            congrArg (StdSimplex.map e) hxy)
    obtain ⟨B, hB⟩ := exists_parameterized_simplex_boundary_track k H hcompat
    let b : C(I × (R F × StdSimplex.boundary (k + 1)), D.carrier F) :=
      ⟨fun q ↦ B (q.2.1, (q.2.2, q.1)), by fun_prop⟩
    let g₀ : C(R F × StdSimplex ℝ (Fin (k + 2)), D.carrier F) :=
      a₀.comp ⟨fun p ↦ (p.1, p.2.map e), by fun_prop⟩
    let g₁ : C(R F × StdSimplex ℝ (Fin (k + 2)), D.carrier F) :=
      a₁.comp ⟨fun p ↦ (p.1, p.2.map e), by fun_prop⟩
    have hb₀ (p : R F) (q : StdSimplex.boundary (k + 1)) : b (0, (p, q)) = g₀ (p, q.val) := by
      obtain ⟨i, hi⟩ := q.property
      obtain ⟨z, hz⟩ := (StdSimplex.mem_range_map_succAbove_iff i q.val).mpr hi
      have heq : StdSimplex.simplexBoundaryFace k i z = q := Subtype.ext hz
      change B (p, (q, 0)) = _
      rw [← heq, hB]
      apply Subtype.ext
      change f.hom _ _ _ _ (0, (carrierParameterRestrict hR (hAF i) p, z.map (v i))) =
        f₀.map F hne hF (p, (z.map i.succAbove).map e)
      rw [ContinuousMap.Homotopy.apply_zero]
      simpa only [StdSimplex.map_map, ← Function.comp_def, hv] using
        (f₀.compatible (hAe i) hne (hAd i) hF (hAF i) p (z.map (v i))).symm
    have hb₁ (p : R F) (q : StdSimplex.boundary (k + 1)) : b (1, (p, q)) = g₁ (p, q.val) := by
      obtain ⟨i, hi⟩ := q.property
      obtain ⟨z, hz⟩ := (StdSimplex.mem_range_map_succAbove_iff i q.val).mpr hi
      have heq : StdSimplex.simplexBoundaryFace k i z = q := Subtype.ext hz
      change B (p, (q, 1)) = _
      rw [← heq, hB]
      apply Subtype.ext
      change f.hom _ _ _ _ (1, (carrierParameterRestrict hR (hAF i) p, z.map (v i))) =
        f₁.map F hne hF (p, (z.map i.succAbove).map e)
      rw [ContinuousMap.Homotopy.apply_one]
      simpa only [StdSimplex.map_map, ← Function.comp_def, hv] using
        (f₁.compatible (hAe i) hne (hAd i) hF (hAF i) p (z.map (v i))).symm
    obtain ⟨L, hL⟩ := exists_parameterized_simplex_homotopy_extension (k + 1) g₀ g₁ b hb₀ hb₁
    let g : ContinuousMap.Homotopy (f₀.map F hne hF) (f₁.map F hne hF) :=
      ⟨⟨fun p ↦ (L (p.1, (p.2.1, p.2.2.map e.symm))).val, by fun_prop⟩,
        fun x ↦ (congrArg Subtype.val (L.apply_zero (x.1, x.2.map e.symm))).trans
          (congrArg (fun z ↦ f₀.map F hne hF (x.1, z)) (PartialCarrierHomotopy.map_equiv_cancel e x.2)),
        fun x ↦ (congrArg Subtype.val (L.apply_one (x.1, x.2.map e.symm))).trans
          (congrArg (fun z ↦ f₁.map F hne hF (x.1, z)) (PartialCarrierHomotopy.map_equiv_cancel e x.2))⟩
    refine ⟨g, fun t p x ↦ (L (t, (p, x.map e.symm))).property, ?_⟩
    intro G hneG hG hGn hGF t p x
    have hlt : G.card < F.card := by omega
    have hnsub : ¬F ⊆ G := fun h ↦ (not_lt_of_ge (Finset.card_le_card h)) hlt
    obtain ⟨a, haF, haG⟩ := Finset.not_subset.mp hnsub
    let i : Fin (k + 2) := e.symm ⟨a, haF⟩
    let q := (x.map (carrierFaceInclusion hGF)).map e.symm
    have hqi : q.weights i = 0 := by
      rw [show q = x.map (e.symm ∘ carrierFaceInclusion hGF) from
        (StdSimplex.map_map _ _ _)]
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨j, hj⟩
      have he := congrArg (fun s ↦ (e s).val) hj
      exact haG (show a ∈ G from (by simpa [i] using he) ▸ j.property)
    obtain ⟨z, hz⟩ := (StdSimplex.mem_range_map_succAbove_iff i q).mpr hqi
    have hqe : q.map e = x.map (carrierFaceInclusion hGF) := PartialCarrierHomotopy.map_equiv_cancel e _
    have hfz : (z.map (v i)).map (carrierFaceInclusion (hAF i)) =
        x.map (carrierFaceInclusion hGF) := by
      rw [StdSimplex.map_map]
      change z.map (e ∘ i.succAbove) = _
      rw [StdSimplex.map_comp, hz, hqe]
    have hface : g (t, (p, x.map (carrierFaceInclusion hGF))) =
        f.hom (A i) (hAe i) (hAd i) (hAn i)
          (t, (carrierParameterRestrict hR (hAF i) p, z.map (v i))) := by
      change (L (t, (p, q))).val = _
      have hbq : (⟨q, i, hqi⟩ : StdSimplex.boundary (k + 1)) =
          StdSimplex.simplexBoundaryFace k i z := Subtype.ext hz.symm
      have h := congrArg Subtype.val (hL t p ⟨q, i, hqi⟩)
      change (L (t, (p, q))).val = _ at h
      rw [show b (t, (p, ⟨q, i, hqi⟩)) = B (p, (⟨q, i, hqi⟩, t)) from rfl,
        hbq, hB] at h
      exact h
    exact hface.trans (f.eq_of_map_eq (hAe i) hneG (hAd i) hG (hAn i) hGn
      (hAF i) hGF t p (z.map (v i)) x hfz)


/-- No nonempty face occurs at homotopy stage zero. -/
def empty (f₀ f₁ : ParameterizedCarrierFamily D R hR) :
    PartialParameterizedCarrierHomotopy f₀ f₁ 0 where
  hom _F hne _ hn := False.elim ((not_lt_of_ge hn) hne.card_pos)
  carried _F hne _ hn := False.elim ((not_lt_of_ge hn) hne.card_pos)
  compatible hA _ _ _ hAn := False.elim ((not_lt_of_ge hAn) hA.card_pos)

/-- A homotopy stage is extended by the proved relative cylinder filler. -/
noncomputable def next (f : PartialParameterizedCarrierHomotopy f₀ f₁ n) :
    PartialParameterizedCarrierHomotopy f₀ f₁ (n + 1) := by
  classical
  let g (F : Finset P) (hne : F.Nonempty) (hF : D.admissible F) (hFn : F.card ≤ n + 1) :
      ContinuousMap.Homotopy (f₀.map F hne hF) (f₁.map F hne hF) :=
    if h : F.card ≤ n then f.hom F hne hF h
    else (f.exists_face_extension F hne hF (by omega)).choose
  have hg (F : Finset P) (hne : F.Nonempty) (hF : D.admissible F)
      (hFn : F.card ≤ n + 1) (h : ¬F.card ≤ n) :=
    (f.exists_face_extension F hne hF (show F.card = n + 1 by omega)).choose_spec
  refine ⟨g, ?_, ?_⟩
  · intro F hne hF hn t p x
    by_cases h : F.card ≤ n
    · simpa only [g, dite_eq_left h] using f.carried F hne hF h t p x
    · simpa only [g, dite_eq_right h] using (hg F hne hF hn h).1 t p x
  · intro A B hA hB ha hb hAn hBn hAB t p x
    by_cases hBsmall : B.card ≤ n
    · have hAsmall := (Finset.card_le_card hAB).trans hBsmall
      simpa only [g, dite_eq_left hBsmall, dite_eq_left hAsmall] using
        f.compatible hA hB ha hb hAsmall hBsmall hAB t p x
    · by_cases hAsmall : A.card ≤ n
      · simpa only [g, dite_eq_right hBsmall, dite_eq_left hAsmall] using
          (hg B hB hb hBn hBsmall).2 A hA ha hAsmall hAB t p x
      · have heq : A = B := Finset.eq_of_subset_of_card_le hAB (by omega)
        subst B
        have hi : carrierFaceInclusion hAB = id := rfl
        rw [hi, StdSimplex.map_id]
        rfl

lemma next_hom_old (f : PartialParameterizedCarrierHomotopy f₀ f₁ n) (F : Finset P)
    (hne : F.Nonempty) (hF : D.admissible F) (hn : F.card ≤ n) :
    f.next.hom F hne hF (hn.trans (Nat.le_succ n)) = f.hom F hne hF hn := by
  simp only [next, dite_eq_left hn]

/-- All-dimensional homotopy stages are recursively constructed. -/
noncomputable def stages (f₀ f₁ : ParameterizedCarrierFamily D R hR) :
    (n : ℕ) → PartialParameterizedCarrierHomotopy f₀ f₁ n
  | 0 => empty f₀ f₁
  | n + 1 => (stages f₀ f₁ n).next

lemma stages_hom_stable (f₀ f₁ : ParameterizedCarrierFamily D R hR)
    {m n : ℕ} (hmn : m ≤ n)
    (F : Finset P) (hne : F.Nonempty) (hF : D.admissible F) (hFm : F.card ≤ m) :
    (stages f₀ f₁ n).hom F hne hF (hFm.trans hmn) =
      (stages f₀ f₁ m).hom F hne hF hFm := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    exact ((stages f₀ f₁ n).next_hom_old F hne hF (hFm.trans hmn)).trans ih

end PartialParameterizedCarrierHomotopy

/-- The result of the varying-parameter construction, containing actual
homotopies with the given endpoint maps and all face restrictions. -/
structure ParameterizedCarrierHomotopy {D : FiniteCarrierData P Y}
    {R : Finset P → Set X} {hR : Antitone R}
    (f₀ f₁ : ParameterizedCarrierFamily D R hR) where
  hom : ∀ F : Finset P, (hne : F.Nonempty) → (hF : D.admissible F) →
    ContinuousMap.Homotopy (f₀.map F hne hF) (f₁.map F hne hF)
  carried : ∀ F hne hF t x z, hom F hne hF (t, (x, z)) ∈ D.carrier F
  compatible : ∀ {A B} (hA : A.Nonempty) (hB : B.Nonempty)
    (ha : D.admissible A) (hb : D.admissible B) (hAB : A ⊆ B)
    (t : I) (x : R B) (z : StdSimplex ℝ A),
    hom B hB hb (t, (x, z.map (carrierFaceInclusion hAB))) =
      hom A hA ha (t, (carrierParameterRestrict hR hAB x, z))

/-- Actual all-dimensional parameterized carrier homotopies, with source
pieces varying antitonically. Neither local compactness nor contractibility
of the parameter spaces is required. -/
noncomputable def ParameterizedCarrierFamily.homotopy
    {D : FiniteCarrierData P Y} {R : Finset P → Set X} {hR : Antitone R}
    (f₀ f₁ : ParameterizedCarrierFamily D R hR) : ParameterizedCarrierHomotopy f₀ f₁ where
  hom F hne hF := (PartialParameterizedCarrierHomotopy.stages f₀ f₁ F.card).hom F hne hF le_rfl
  carried F hne hF := (PartialParameterizedCarrierHomotopy.stages f₀ f₁ F.card).carried F hne hF le_rfl
  compatible {A B} hA hB ha hb hAB t p x := by
    have hn := Finset.card_le_card hAB
    exact ((PartialParameterizedCarrierHomotopy.stages f₀ f₁ B.card).compatible
      hA hB ha hb hn le_rfl hAB t p x).trans
      (congrArg (fun H ↦ H (t, (carrierParameterRestrict hR hAB p, x)))
        (PartialParameterizedCarrierHomotopy.stages_hom_stable f₀ f₁ hn A hA ha le_rfl))

end Parameterized

end ArtinNormalisers.Deligne5
