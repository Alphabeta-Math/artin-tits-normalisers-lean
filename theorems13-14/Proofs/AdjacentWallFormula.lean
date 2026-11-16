import Mathlib
import ArtinDeligne
import Proofs.ChamberLabelling
import Proofs.SimpleWallCrossings

set_option maxHeartbeats 2000000

theorem AdjacentWallFormula : (∀ {S : Type*} [Finite S] (M : CoxeterMatrix S) (J : Set S),
  let W := CoxeterMatrix.Group M
  let cs := CoxeterMatrix.toCoxeterSystem M
  let Θ := ArtinNormalisers.Theorem18.relativeSubspace J
  letI : TopologicalSpace Θ := TopologicalSpace.induced
    (fun f : Θ => ArtinNormalisers.Theorem18.dualCoordinates f.val)
    (inferInstance : TopologicalSpace (S → Real))
  let arrangement : Set (Submodule Real Θ) := (RelativeCone M J).2.2.2.2.2
  let label : W → Set S → Prop := fun x I =>
    Set.image (fun u : W => u * x) (CoxeterSystem.parabolic cs J : Set W) =
      Set.image (fun u : W => x * u) (CoxeterSystem.parabolic cs I : Set W) ∧
    CoxeterSystem.IsMinimalCosetRep cs I x
  let face : Set S → Set (ArtinNormalisers.Theorem18.Dual S) := fun I =>
    { f | f ∈ ArtinNormalisers.Theorem18.relativeSubspace I ∧
      ∀ i : S, i ∉ I → 0 < ArtinNormalisers.Theorem18.dualCoordinates f i }
  let region : W → Set S → Set Θ := fun x I =>
    { f | ∃ g : ArtinNormalisers.Theorem18.Dual S,
      g ∈ face I ∧ ArtinNormalisers.Theorem18.dualAction M x g = f.val }
  let affineDimension : Set Θ → Nat := fun A =>
    Module.finrank Real (AffineSubspace.direction (affineSpan Real A))
  let wall : Set Θ → Set Θ → Prop := fun C F =>
    Set.Nonempty F ∧ ∃ H : Submodule Real Θ, H ∈ arrangement ∧
      F = closure C ∩ (H : Set Θ) ∧ affineDimension F + 1 = affineDimension C
  let component : Set S → S → Set S := fun I a =>
    { b | b ∈ Set.insert a I ∧ Relation.ReflTransGen
      (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b }
  ∀ (x y : W) (I K : Set S), label x I → label y K →
    ∀ F : Set Θ, region x I ≠ region y K → wall (region x I) F → wall (region y K) F →
    ∃ (a a' : S) (ha : a ∉ I) (ha' : a' ∉ K),
      F = closure (region x (Set.insert a I)) ∧
      F = closure (region y (Set.insert a' K)) ∧
      (∀ c : S, c ∉ I → F = closure (region x (Set.insert c I)) → c = a) ∧
      (∀ c : S, c ∉ K → F = closure (region y (Set.insert c K)) → c = a') ∧
      Set.insert a I = Set.insert a' K ∧
      component I a = component K a' ∧
      CoxeterSystem.parabolic cs (component I a) = CoxeterSystem.parabolic cs (component K a') ∧
      ∃ (hD : Finite (CoxeterSystem.parabolic cs (component I a)))
        (hD' : Finite (CoxeterSystem.parabolic cs (component K a'))),
        let forward := SimpleWallCrossings S W M cs I a ha hD
        let reverse := SimpleWallCrossings S W M cs K a' ha' hD'
        forward.2.2 x = (y, K) ∧ reverse.2.2 y = (x, I) ∧
        K = Set.insert a I \ {a'} ∧ I = Set.insert a' K \ {a} ∧
        forward.1 * reverse.1 = (1 : W) ∧ reverse.1 * forward.1 = (1 : W)) :=
(/- Compilation resource setting: the driver wrapper uses command-level
   -DmaxHeartbeats=2000000. The accepted endpoint is unchanged. -/
fun {S} inst M J =>
open Set ArtinNormalisers.Artin ArtinNormalisers.Landmark1 ArtinNormalisers.Theorem18 ArtinNormalisers.Chamber3 CoxeterSystem in
by
  classical
  /- Proposition 3.17, printed p.11: https://arxiv.org/pdf/2509.21915#page=11.
  Numbered inspiration: parent steps 1.1, 2.1, 3.1:
  https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-prop-adjacent-wall-formula-artin-tits-normalisers;
  common-facet steps 1.1, 2.1, 3.1:
  https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-author-4ac39e6f1702-common-facet;
  component-opposition steps 1.1, 1.2, 2.1:
  https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-author-4ac39e6f1702-component-opposition;
  component-crossing-label steps 1.1, 2.1, 3.1:
  https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-author-4ac39e6f1702-component-crossing-label;
  finite-crossing-roots steps 1.1--4.1:
  https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-author-4ac39e6f1702-finite-crossing-roots;
  finite-relative-longest steps 1.1--2.1:
  https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-author-a7d202611130-finite-relative-longest.
  These implementation helpers have no standalone original article statements;
  parents are Proposition 3.17/Lemma 3.20(1), p.11, and Lemma 4.15, p.19.
  Departures: exact affine-span dimensions classify orthant sections; addition
  supplies a common open-facet point. Actual maxima and epsilon opposition are
  certified before use. The opposite-coordinate identity is proved on the whole
  candidate flat, so the two-chart recognition argument does not assume candidate
  membership. Finite inversions and propagation of root support prove sphericality.
  Path reversal and cancellation prove the final inverse formulas.
  Literature defects: https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects.
  Finding pdf-adjacency-uniqueness-wording says: 'State uniqueness for the indices
  describing the specified common wall, then list the subset equality among their
  properties.' Evidence: in A2 with J=I=K=empty and adjacent labels (1,empty),
  (s1,empty), both pairs (1,1),(2,2) satisfy subset equality. We retain specified-wall
  uniqueness. Finding pdf-wall-root-characterisation concerns p.10 after (3.15):
  in rank one, I=K=empty and v=s_a give an empty printed target Phi_K^-.
  That auxiliary characterization is unused; the actual longest-element definition
  is retained. Finite rank is explicit user direction for geometry, not a reported
  rank defect. Neither W_I nor W_(I+a) is assumed finite. Algebraic covering remains
  arbitrary-rank. Prior bounded searches are reused without an exhaustive-absence
  claim. No unfinished helper result is assumed.
  -/
  let r_pos (T : Type _) : Set (T → ℝ) := {q | ∀ i, 0 < q i}
  let r_nn (T : Type _) : Set (T → ℝ) := {q | ∀ i, 0 ≤ q i}
  let r_oface {T : Type _} (A : Set T) : Set (T → ℝ) :=
    {q | (∀ i ∈ A, q i = 0) ∧ ∀ i ∉ A, 0 < q i}
  let r_cface {T : Type _} (A : Set T) : Set (T → ℝ) :=
    {q | (∀ i ∈ A, q i = 0) ∧ ∀ i, 0 ≤ q i}
  let r_flat {T : Type _} (A : Set T) : Submodule ℝ (T → ℝ) := {
    carrier := {q | ∀ i ∈ A, q i = 0}
    zero_mem' := by simp
    add_mem' := by intro x y hx hy i hi; simp [hx i hi, hy i hi]
    smul_mem' := by intro c x hx i hi; simp [hx i hi] }
  let r_dim {E : Type _} [AddCommGroup E] [Module ℝ E] (A : Set E) : ℕ :=
    Module.finrank ℝ (AffineSubspace.direction (affineSpan ℝ A))
  have r_closure_pos (T : Type _) : closure (r_pos T) = r_nn T := by
    have h : r_pos T = Set.pi univ (fun _ : T => Set.Ioi (0 : ℝ)) := by ext q; simp [r_pos]
    rw [h, closure_pi_set]
    ext q
    simp only [mem_pi, mem_univ, forall_const, closure_Ioi, mem_Ici, r_nn, mem_ofPred_eq]
  have r_closure_oface {T : Type _} (A : Set T) : closure (r_oface A) = r_cface A := by
    classical
    have h : r_oface A = Set.pi univ (fun i : T => if i ∈ A then {(0 : ℝ)} else Set.Ioi 0) := by
      ext q
      simp only [r_oface, mem_setOf_eq, mem_pi, mem_univ, forall_const]
      constructor
      · intro h i
        by_cases hi : i ∈ A
        · simpa only [if_pos hi, mem_singleton_iff] using h.1 i hi
        · simpa only [if_neg hi, mem_Ioi] using h.2 i hi
      · intro h
        exact ⟨fun i hi => by simpa [hi] using h i,
          fun i hi => by simpa [hi] using h i⟩
    rw [h, closure_pi_set]
    ext q
    simp only [r_cface, mem_setOf_eq, mem_pi, mem_univ, forall_const]
    constructor
    · intro h
      refine ⟨fun i hi => ?_, fun i => ?_⟩
      · simpa [hi] using h i
      · by_cases hi : i ∈ A
        · have hz : q i = 0 := by simpa [hi] using h i
          simp [hz]
        · simpa [hi, closure_Ioi] using h i
    · intro h i
      by_cases hi : i ∈ A
      · simpa only [if_pos hi, isClosed_singleton.closure_eq, mem_singleton_iff] using h.1 i hi
      · simpa [hi, closure_Ioi] using h.2 i
  let r_flatEquiv {T : Type _} (A : Set T) :
      r_flat A ≃ₗ[ℝ] ({i : T // i ∉ A} → ℝ) := by
    classical
    exact {
      toFun := fun q i => q.val i
      invFun := fun q => ⟨fun i => if h : i ∈ A then 0 else q ⟨i, h⟩, by
        intro i hi; simp [hi]⟩
      left_inv := by
        intro q; apply Subtype.ext; funext i
        by_cases hi : i ∈ A
        · simp only [dif_pos hi]; exact (q.property i hi).symm
        · simp [hi]
      right_inv := by intro q; funext i; simp [i.property]
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have r_direction_cface {T : Type _} (A : Set T) :
      (affineSpan ℝ (r_cface A)).direction = r_flat A := by
    have h0 : (0 : T → ℝ) ∈ r_cface A := by simp [r_cface]
    rw [direction_affineSpan, vectorSpan_eq_span_vsub_set_right ℝ h0]
    have he : (fun p : T → ℝ => p -ᵥ (0 : T → ℝ)) '' r_cface A = r_cface A := by simp
    rw [he]
    apply le_antisymm
    · exact Submodule.span_le.mpr fun q hq => hq.1
    · intro q hq
      let p : T → ℝ := fun i => max (q i) 0
      let n : T → ℝ := fun i => max (-q i) 0
      have hp : p ∈ r_cface A := ⟨fun i hi => by simp [p, hq i hi], fun i => le_max_right _ _⟩
      have hn : n ∈ r_cface A := ⟨fun i hi => by simp [n, hq i hi], fun i => le_max_right _ _⟩
      have heq : q = p - n := by
        funext i
        dsimp [p, n]
        by_cases hi : 0 ≤ q i
        · rw [max_eq_left hi, max_eq_right (neg_nonpos.mpr hi)]; simp
        · have hi' : q i ≤ 0 := le_of_not_ge hi
          rw [max_eq_right hi', max_eq_left (neg_nonneg.mpr hi')]; simp
      rw [heq]
      exact Submodule.sub_mem _ (Submodule.subset_span hp) (Submodule.subset_span hn)
  have r_dim_cface {T : Type _} [Finite T] (A : Set T) :
      r_dim (r_cface A) = Nat.card {i : T // i ∉ A} := by
    classical
    letI := Fintype.ofFinite {i : T // i ∉ A}
    unfold r_dim
    rw [r_direction_cface, (r_flatEquiv A).finrank_eq, Module.finrank_pi, Nat.card_eq_fintype_card]
  have r_dim_pos (T : Type _) [Finite T] : r_dim (r_pos T) = Nat.card T := by
    classical
    letI := Fintype.ofFinite T
    have ho : IsOpen (r_pos T) := by
      have he : r_pos T = ⋂ i : T, {q : T → ℝ | 0 < q i} := by ext q; simp [r_pos]
      rw [he]
      exact isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (continuous_apply i)
    have hs := ho.affineSpan_eq_top ⟨fun _ => 1, fun _ => zero_lt_one⟩
    unfold r_dim
    rw [hs, AffineSubspace.direction_top, finrank_top, Module.finrank_pi, Nat.card_eq_fintype_card]
  have r_dim_image {T E : Type _} [AddCommGroup E] [Module ℝ E]
      (e : (T → ℝ) ≃ₗ[ℝ] E) (A : Set (T → ℝ)) : r_dim (e '' A) = r_dim A := by
    unfold r_dim
    change Module.finrank ℝ (affineSpan ℝ (e.toLinearMap.toAffineMap '' A)).direction = _
    rw [← AffineSubspace.map_span, AffineSubspace.map_direction]
    exact e.finrank_map_eq _
  have r_section_eq {T : Type _} [Fintype T] (c : T → ℝ) (hc : ∀ i, 0 ≤ c i) :
      {q : T → ℝ | q ∈ r_nn T ∧ ∑ i, c i * q i = 0} = r_cface {i | 0 < c i} := by
    ext q
    constructor
    · rintro ⟨hq, he⟩
      refine ⟨fun i hi => ?_, hq⟩
      have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i ∈ Finset.univ) =>
        mul_nonneg (hc i) (hq i))).mp he
      exact (mul_eq_zero.mp (hall i (Finset.mem_univ i))).resolve_left (ne_of_gt hi)
    · rintro ⟨hz, hq⟩
      refine ⟨hq, Finset.sum_eq_zero fun i _ => ?_⟩
      by_cases hi : 0 < c i
      · rw [hz i hi, mul_zero]
      · have hc0 : c i = 0 := le_antisymm (le_of_not_gt hi) (hc i)
        rw [hc0, zero_mul]
  have r_cface_unique {T : Type _} (a b : T)
      (he : r_cface ({a} : Set T) = r_cface {b}) : a = b := by
    classical
    by_contra h
    let q : T → ℝ := Pi.single b 1
    have hq : q ∈ r_cface ({a} : Set T) := by
      refine ⟨?_, ?_⟩
      · intro i hi; have hi' : i = a := hi; subst i; simp [q, h, Ne.symm h]
      · intro i; simp [q, Pi.single_apply]; split_ifs <;> norm_num
    rw [he] at hq
    have := hq.1 b (by simp)
    simpa [q] using this
  have r_section_codim {T : Type _} [Finite T] [Fintype T]
      (c : T → ℝ) (hc : ∀ i, 0 ≤ c i)
      (hd : r_dim {q : T → ℝ | q ∈ r_nn T ∧ ∑ i, c i * q i = 0} + 1 = r_dim (r_pos T)) :
      ∃ a : T, {q : T → ℝ | q ∈ r_nn T ∧ ∑ i, c i * q i = 0} = r_cface {a} := by
    classical
    rw [r_section_eq c hc, r_dim_cface, r_dim_pos] at hd
    have hcard := Fintype.card_subtype_compl (fun i => 0 < c i)
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hd
    have hle := Fintype.card_subtype_le (fun i => 0 < c i)
    have hone : Fintype.card {i : T // 0 < c i} = 1 := by
      simp only [← Nat.card_eq_fintype_card] at hd hcard hle ⊢
      change Nat.card {i : T // ¬ 0 < c i} + 1 = Nat.card T at hd
      omega
    obtain ⟨a, ha⟩ := Fintype.card_eq_one_iff.mp hone
    refine ⟨a.val, ?_⟩
    rw [r_section_eq c hc]
    congr 1
    ext i
    constructor
    · intro hi; exact congrArg Subtype.val (ha ⟨i, hi⟩)
    · intro hi; have : i = a.val := hi; subst i; exact a.property
  let r_coords {S : Type _} (I : Set S) :
      relativeSubspace I ≃L[ℝ] ({i : S // i ∉ I} → ℝ) := by
    classical
    let e : relativeSubspace I ≃ₗ[ℝ] ({i : S // i ∉ I} → ℝ) := {
      toFun := fun f i => dualCoordinates f.val i
      invFun := fun q => ⟨dualCoordinates.symm (fun i => if h : i ∈ I then 0 else q ⟨i, h⟩), by
        intro i hi
        change dualCoordinates (dualCoordinates.symm _) i = 0
        simp [hi]⟩
      left_inv := by
        intro f; apply Subtype.ext; apply dualCoordinates.injective; funext i
        simp only [LinearEquiv.apply_symm_apply]
        by_cases hi : i ∈ I
        · simp [hi]; exact (f.property i hi).symm
        · simp [hi]
      right_inv := by intro q; funext i; simp [i.property]
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
    refine { toLinearEquiv := e, continuous_toFun := ?_, continuous_invFun := ?_ }
    · exact continuous_pi fun i =>
        (continuous_apply (i : S)).comp
          (dualCoordinatesHomeomorph.continuous_toFun.comp continuous_subtype_val)
    · apply Continuous.subtype_mk
      exact dualCoordinatesHomeomorph.symm.continuous_toFun.comp (continuous_pi fun i => by
        by_cases hi : i ∈ I
        · simpa only [hi, dite_true] using (continuous_const : Continuous (fun _ : ({i : S // i ∉ I} → ℝ) => (0 : ℝ)))
        · simpa only [hi, dite_false] using (continuous_apply (⟨i, hi⟩ : {i : S // i ∉ I})))
  have r_coords_apply {S : Type _} (I : Set S) (f : relativeSubspace I)
      (i : {i : S // i ∉ I}) : r_coords I f i = dualCoordinates f.val i := rfl
  have r_coords_symm_apply {S : Type _} (I : Set S)
      (q : {i : S // i ∉ I} → ℝ) (i : {i : S // i ∉ I}) :
      dualCoordinates ((r_coords I).symm q).val i = q i := by
    have := congrFun ((r_coords I).apply_symm_apply q) i
    exact this
  have r_coset_conj {S : Type _} (M : CoxeterMatrix S) (J I : Set S) (x : M.Group)
      (h : Set.image (fun u : M.Group => u * x) (M.toCoxeterSystem.parabolic J : Set M.Group) =
        Set.image (fun u : M.Group => x * u) (M.toCoxeterSystem.parabolic I : Set M.Group)) :
      (coxeterParabolic M I).map
        (MulAut.conj x).toMonoidHom = coxeterParabolic M J := by
    ext v
    constructor
    · rintro ⟨u, hu, huv⟩
      change x * u * x⁻¹ = v at huv
      have hm : x * u ∈ Set.image (fun t : M.Group => t * x)
          (M.toCoxeterSystem.parabolic J : Set M.Group) :=
        h.symm ▸ Set.mem_image_of_mem (fun t : M.Group => x * t) hu
      obtain ⟨t, ht, he⟩ := hm
      have hev : t = v := by rw [← huv, ← he]; group
      exact hev ▸ ht
    · intro hv
      have hm : v * x ∈ Set.image (fun t : M.Group => x * t)
          (M.toCoxeterSystem.parabolic I : Set M.Group) :=
        h ▸ Set.mem_image_of_mem (fun t : M.Group => t * x) hv
      obtain ⟨t, ht, he⟩ := hm
      refine ⟨t, ht, ?_⟩
      change x * t = v * x at he
      change x * t * x⁻¹ = v
      rw [he]; group
  let r_chart {S : Type _} {M : CoxeterMatrix S} {J : Set S}
      (L : RawFacetLabel M J) : ({i : S // i ∉ L.indices} → ℝ) ≃L[ℝ] relativeSubspace J :=
    (r_coords L.indices).symm.trans (facetFlatEquiv L)
  let r_region {S : Type _} (M : CoxeterMatrix S) (J : Set S) (x : M.Group) (I : Set S) :
      Set (relativeSubspace J) :=
    {f | ∃ g : Dual S, g ∈ standardFacet M I ∧ dualAction M x g = f.val}
  have r_region_chart {S : Type _} {M : CoxeterMatrix S} {J : Set S}
      (L : RawFacetLabel M J) : r_region M J L.representative L.indices = r_chart L '' r_pos _ := by
    ext f
    constructor
    · rintro ⟨g, hg, he⟩
      refine ⟨r_coords L.indices ⟨g, hg.1⟩, fun i => hg.2 i i.property, ?_⟩
      change facetFlatEquiv L ((r_coords L.indices).symm (r_coords L.indices ⟨g, hg.1⟩)) = f
      rw [ContinuousLinearEquiv.symm_apply_apply]
      exact Subtype.ext he
    · rintro ⟨q, hq, rfl⟩
      refine ⟨((r_coords L.indices).symm q).val, ⟨((r_coords L.indices).symm q).property, ?_⟩, rfl⟩
      intro i hi
      have h := r_coords_symm_apply L.indices q ⟨i, hi⟩
      change ((r_coords L.indices).symm q).val (simpleRoot i) = q ⟨i, hi⟩ at h
      rw [h]
      exact hq ⟨i, hi⟩
  have r_insert_region_chart {S : Type _} {M : CoxeterMatrix S} {J : Set S}
      (L : RawFacetLabel M J) (a : S) (ha : a ∉ L.indices) :
      r_region M J L.representative (insert a L.indices) =
        r_chart L '' r_oface ({⟨a, ha⟩} : Set {i : S // i ∉ L.indices}) := by
    ext f
    constructor
    · rintro ⟨g, hg, he⟩
      have hgI : g ∈ relativeSubspace L.indices := fun i hi => hg.1 i (mem_insert_of_mem a hi)
      refine ⟨r_coords L.indices ⟨g, hgI⟩, ⟨?_, ?_⟩, ?_⟩
      · intro i hi; have : i = ⟨a, ha⟩ := hi; subst i
        exact hg.1 a (mem_insert a L.indices)
      · intro i hi
        apply hg.2 i
        simp only [mem_insert_iff, not_or]
        exact ⟨fun heq => hi (by exact Subtype.ext heq), i.property⟩
      · change facetFlatEquiv L ((r_coords L.indices).symm (r_coords L.indices ⟨g, hgI⟩)) = f
        rw [ContinuousLinearEquiv.symm_apply_apply]
        exact Subtype.ext he
    · rintro ⟨q, hq, rfl⟩
      let g := ((r_coords L.indices).symm q).val
      have hga : g (simpleRoot a) = 0 := by
        exact (r_coords_symm_apply L.indices q ⟨a, ha⟩).trans (hq.1 _ (by simp))
      refine ⟨g, ⟨?_, ?_⟩, rfl⟩
      · intro i hi
        rcases hi with rfl | hi
        · exact hga
        · exact ((r_coords L.indices).symm q).property i hi
      · intro i hi
        have hiI : i ∉ L.indices := fun h => hi (mem_insert_of_mem a h)
        have hia : (⟨i, hiI⟩ : {i : S // i ∉ L.indices}) ∉ ({⟨a, ha⟩} : Set _) := by
          intro heq
          exact hi (Or.inl (congrArg Subtype.val heq))
        have h := r_coords_symm_apply L.indices q ⟨i, hiI⟩
        change g (simpleRoot i) = q ⟨i, hiI⟩ at h
        rw [h]
        exact hq.2 _ hia
  have r_eval_sum {S : Type _} [Fintype S] (I : Set S)
      (f : relativeSubspace I) (r : Vector S) :
      f.val r = ∑ i : {i : S // i ∉ I}, r i * dualCoordinates f.val i := by
    classical
    have he : r = ∑ i : S, r i • simpleRoot i := by
      ext k
      simp [simpleRoot, Finsupp.single_apply, Finset.sum_ite_eq']
    conv_lhs => rw [he, map_sum]
    simp only [map_smul, smul_eq_mul]
    have hz : (∑ i : {i : S // i ∈ I}, r i * f.val (simpleRoot i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [f.property i i.property, mul_zero]
    have h := Fintype.sum_subtype_add_sum_subtype (fun i => i ∈ I)
      (fun i => r i * f.val (simpleRoot i))
    rw [hz, zero_add] at h
    exact h.symm
  have r_chart_eval {S : Type _} [Fintype S] {M : CoxeterMatrix S} {J : Set S}
      (L : RawFacetLabel M J) (q : {i : S // i ∉ L.indices} → ℝ) (r : Vector S) :
      (r_chart L q).val r = ∑ i : {i : S // i ∉ L.indices},
        (M.toCoxeterSystem.geometricRepresentation L.representative⁻¹ r) i * q i := by
    change ((r_coords L.indices).symm q).val
      (M.toCoxeterSystem.geometricRepresentation L.representative⁻¹ r) = _
    rw [r_eval_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [r_coords_symm_apply]
  have r_wall_index {S : Type _} [Finite S] {M : CoxeterMatrix S} {J : Set S}
      (L : RawFacetLabel M J) (r : Vector S) (hr : r ∈ M.toCoxeterSystem.geometricRoots)
      (F : Set (relativeSubspace J))
      (hF : F = closure (r_region M J L.representative L.indices) ∩
        (restrictedHyperplane J r : Set (relativeSubspace J)))
      (hd : r_dim F + 1 = r_dim (r_region M J L.representative L.indices)) :
      ∃ (a : S) (ha : a ∉ L.indices),
        F = closure (r_region M J L.representative (insert a L.indices)) ∧
        ∀ c : S, c ∉ L.indices →
          F = closure (r_region M J L.representative (insert c L.indices)) → c = a := by
    classical
    letI := Fintype.ofFinite S
    let T := {i : S // i ∉ L.indices}
    let v := M.toCoxeterSystem.geometricRepresentation L.representative⁻¹ r
    have hv : v ∈ M.toCoxeterSystem.geometricRoots :=
      (M.toCoxeterSystem.geometricRepresentation_apply_mem_geometricRoots_iff _).mpr hr
    have hcoeff : ∃ c : T → ℝ, (∀ i, 0 ≤ c i) ∧ ∀ q : T → ℝ,
        ((r_chart L q).val r = 0 ↔ ∑ i, c i * q i = 0) := by
      rcases M.toCoxeterSystem.pos_or_neg_of_mem_geometricRoots hv with hp | hn
      · refine ⟨fun i => v i, fun i => hp.le i, fun q => ?_⟩
        rw [r_chart_eval]
      · refine ⟨fun i => -v i, fun i => neg_nonneg.mpr (hn.le i), fun q => ?_⟩
        rw [r_chart_eval]
        change (∑ i : T, v i * q i = 0) ↔ ∑ i : T, -v i * q i = 0
        simp only [neg_mul, Finset.sum_neg_distrib, neg_eq_zero]
    obtain ⟨c, hc, hker⟩ := hcoeff
    let secSet : Set (T → ℝ) := {q | q ∈ r_nn T ∧ ∑ i, c i * q i = 0}
    have himage : F = r_chart L '' secSet := by
      rw [hF, r_region_chart, ← ContinuousLinearEquiv.image_closure, r_closure_pos]
      ext f
      constructor
      · rintro ⟨⟨q, hq, rfl⟩, hf⟩
        exact ⟨q, ⟨hq, (hker q).mp hf⟩, rfl⟩
      · rintro ⟨q, ⟨hq, he⟩, rfl⟩
        exact ⟨⟨q, hq, rfl⟩, (hker q).mpr he⟩
    have hds : r_dim secSet + 1 = r_dim (r_pos T) := by
      rw [himage, r_region_chart] at hd
      have h1 : r_dim (r_chart L '' secSet) = r_dim secSet := by apply r_dim_image
      have h2 : r_dim (r_chart L '' r_pos T) = r_dim (r_pos T) := by apply r_dim_image
      rw [h1, h2] at hd
      exact hd
    obtain ⟨a, ha⟩ := r_section_codim c hc hds
    have hface : F = r_chart L '' r_cface ({a} : Set T) := himage.trans (congrArg _ ha)
    refine ⟨a.val, a.property, ?_, ?_⟩
    · rw [r_insert_region_chart L a.val a.property, ← ContinuousLinearEquiv.image_closure,
        r_closure_oface]
      exact hface
    · intro b hb he
      rw [r_insert_region_chart L b hb, ← ContinuousLinearEquiv.image_closure,
        r_closure_oface, hface] at he
      have heq := (r_chart L).injective.image_injective he
      exact congrArg Subtype.val (r_cface_unique (⟨b, hb⟩ : T) a heq.symm)
  have r_of_sub {T : Type _} {D : Set T} {q : T → ℝ} (hq : q ∈ r_oface D) : q ∈ r_cface D := by
      refine ⟨hq.1, fun i => ?_⟩
      by_cases hi : i ∈ D
      · rw [hq.1 i hi]
      · exact (hq.2 i hi).le
  have r_add_face {T : Type _} {D : Set T} {p q : T → ℝ}
        (hp : p ∈ r_oface D) (hq : q ∈ r_cface D) : p + q ∈ r_oface D := by
      refine ⟨fun i hi => by change p i + q i = 0; rw [hp.1 i hi, hq.1 i hi, add_zero], fun i hi => ?_⟩
      exact add_pos_of_pos_of_nonneg (hp.2 i hi) (hq.2 i)
  have r_common_point {A B E : Type _} [AddCommGroup E] [Module ℝ E]
      [TopologicalSpace E] (X : (A → ℝ) ≃L[ℝ] E) (Y : (B → ℝ) ≃L[ℝ] E)
      (a : A) (b : B) (he : X '' r_cface ({a} : Set A) = Y '' r_cface ({b} : Set B)) :
      (X '' r_oface ({a} : Set A) ∩ Y '' r_oface ({b} : Set B)).Nonempty := by
    classical
    let u : A → ℝ := fun i => if i = a then 0 else 1
    let v : B → ℝ := fun i => if i = b then 0 else 1
    have hu : u ∈ r_oface ({a} : Set A) := by
      constructor
      · intro i hi; have : i = a := hi; simp [u, this]
      · intro i hi; simpa [u, show i ≠ a from hi] using (zero_lt_one : (0 : ℝ) < 1)
    have hv : v ∈ r_oface ({b} : Set B) := by
      constructor
      · intro i hi; have : i = b := hi; simp [v, this]
      · intro i hi; simpa [v, show i ≠ b from hi] using (zero_lt_one : (0 : ℝ) < 1)
    have hx : X u ∈ Y '' r_cface ({b} : Set B) := he ▸ ⟨u, r_of_sub hu, rfl⟩
    have hy : Y v ∈ X '' r_cface ({a} : Set A) := he.symm ▸ ⟨v, r_of_sub hv, rfl⟩
    obtain ⟨ux, hux, hxe⟩ := hx
    obtain ⟨vy, hvy, hye⟩ := hy
    refine ⟨X u + Y v, ⟨u + vy, r_add_face hu hvy, ?_⟩,
      ⟨v + ux, r_add_face hv hux, ?_⟩⟩
    · rw [map_add, hye]
    · rw [map_add, hxe, add_comm]
  have r_common_indices {S : Type _} {M : CoxeterMatrix S} {J : Set S}
      (x y : M.Group) (I K : Set S)
      (h : (r_region M J x I ∩ r_region M J y K).Nonempty) : I = K := by
    obtain ⟨p, ⟨f, hf, hxf⟩, ⟨g, hg, hyg⟩⟩ := h
    have htrans : dualAction M (y⁻¹ * x) f = g := by
      rw [map_mul, mul_apply_eq_comp, hxf, ← hyg]
      rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
    exact standardFacet_translate_indices_eq M hf (y⁻¹ * x) (htrans.symm ▸ hg)
  have RelativeCommonWall : (∀ {S : Type _} [Finite S] (M : CoxeterMatrix S) (J : Set S),
    let W := M.Group
    let cs := M.toCoxeterSystem
    let Θ := relativeSubspace J
    letI : TopologicalSpace Θ := TopologicalSpace.induced
      (fun f : Θ => dualCoordinates f.val)
      (inferInstance : TopologicalSpace (S → Real))
    let arrangement : Set (Submodule Real Θ) := (RelativeCone M J).2.2.2.2.2
    let label : W → Set S → Prop := fun x I =>
      Set.image (fun u : W => u * x) (parabolic cs J : Set W) =
        Set.image (fun u : W => x * u) (parabolic cs I : Set W) ∧
      IsMinimalCosetRep cs I x
    let face : Set S → Set (Dual S) := fun I =>
      { f | f ∈ relativeSubspace I ∧ ∀ i : S, i ∉ I → 0 < dualCoordinates f i }
    let r_region : W → Set S → Set Θ := fun x I =>
      { f | ∃ g : Dual S, g ∈ face I ∧ dualAction M x g = f.val }
    let affineDimension : Set Θ → Nat := fun A =>
      Module.finrank Real (AffineSubspace.direction (affineSpan Real A))
    let wall : Set Θ → Set Θ → Prop := fun C F =>
      Set.Nonempty F ∧ ∃ H : Submodule Real Θ, H ∈ arrangement ∧
        F = closure C ∩ (H : Set Θ) ∧ affineDimension F + 1 = affineDimension C
    let component : Set S → S → Set S := fun I a =>
      { b | b ∈ Set.insert a I ∧ Relation.ReflTransGen
        (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b }
    ∀ (x y : W) (I K : Set S), label x I → label y K →
      ∀ F : Set Θ, r_region x I ≠ r_region y K → wall (r_region x I) F → wall (r_region y K) F →
      ∃ (a a' : S) (ha : a ∉ I) (ha' : a' ∉ K),
        F = closure (r_region x (Set.insert a I)) ∧
        F = closure (r_region y (Set.insert a' K)) ∧
        (∀ c : S, c ∉ I → F = closure (r_region x (Set.insert c I)) → c = a) ∧
        (∀ c : S, c ∉ K → F = closure (r_region y (Set.insert c K)) → c = a') ∧
        Set.insert a I = Set.insert a' K) := by
    classical
    intro S _ M J
    dsimp only
    have htop : TopologicalSpace.induced
        (fun f : relativeSubspace J => dualCoordinates f.val)
        (inferInstance : TopologicalSpace (S → ℝ)) =
        (inferInstance : TopologicalSpace (relativeSubspace J)) := induced_compose.symm
    rw [htop]
    intro x y I K hx hy F _ hwallx hwally
    let X : RawFacetLabel M J := ⟨I, x, r_coset_conj M J I x hx.1⟩
    let Y : RawFacetLabel M J := ⟨K, y, r_coset_conj M J K y hy.1⟩
    obtain ⟨_, H, hH, hFx, hdx⟩ := hwallx
    obtain ⟨r, hr, rfl⟩ := hH
    obtain ⟨a, ha, hfa, hua⟩ := r_wall_index X r hr.1.1 F hFx hdx
    obtain ⟨_, H', hH', hFy, hdy⟩ := hwally
    obtain ⟨r', hr', rfl⟩ := hH'
    obtain ⟨b, hb, hfb, hub⟩ := r_wall_index Y r' hr'.1.1 F hFy hdy
    refine ⟨a, b, ha, hb, hfa, hfb, hua, hub, ?_⟩
    apply r_common_indices (J := J) x y
    change (r_region M J X.representative (Set.insert a X.indices) ∩
      r_region M J Y.representative (Set.insert b Y.indices)).Nonempty
    have hxreg := r_insert_region_chart X a ha
    have hyreg := r_insert_region_chart Y b hb
    change r_region M J X.representative (Set.insert a X.indices) = _ at hxreg
    change r_region M J Y.representative (Set.insert b Y.indices) = _ at hyreg
    rw [hxreg, hyreg]
    refine r_common_point (E := relativeSubspace J)
      (r_chart X) (r_chart Y) ⟨a, ha⟩ ⟨b, hb⟩ ?_
    have he := hfa.symm.trans hfb
    change closure (r_region M J X.representative (Set.insert a X.indices)) =
      closure (r_region M J Y.representative (Set.insert b Y.indices)) at he
    rw [hxreg, hyreg, ← ContinuousLinearEquiv.image_closure,
      ← ContinuousLinearEquiv.image_closure, r_closure_oface, r_closure_oface] at he
    exact he
  let c_component {S : Type _} {M : CoxeterMatrix S} (I : Set S) (a : S) : Set S :=
    {b | b ∈ Set.insert a I ∧ Relation.ReflTransGen
      (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b}
  let c_selectedLongest {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (D : Set S)
      (hD : Finite (cs.parabolic D)) (L : Set S) (hL : L ⊆ D) : cs.parabolic L :=
    letI : Finite (cs.parabolic L) := Finite.of_injective
      (fun w : cs.parabolic L => (⟨(w : W), (cs.parabolic_mono hL) w.property⟩ : cs.parabolic D))
      (fun _ _ h => Subtype.ext (congrArg (fun z : cs.parabolic D => (z : W)) h))
    Classical.choose (Finite.exists_max (fun w : cs.parabolic L => cs.length (w : W)))
  let c_selectedOpposition {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (I : Set S) (a : S)
      (hD : Finite (cs.parabolic (c_component (M := M) I a))) :
      c_component (M := M) I a ≃ c_component (M := M) I a :=
    let D := c_component (M := M) I a
    let wD : W := c_selectedLongest cs D hD D (fun _ h => h)
    @Classical.epsilon (D ≃ D) ⟨Equiv.refl D⟩
      (fun e => ∀ i : D, cs.geometricRepresentation wD (Finsupp.single (i : S) (1 : ℝ)) =
        -Finsupp.single (e i : S) 1)
  have c_actual_certificate {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (I : Set S) (a : S) (ha : a ∉ I)
      (hD : Finite (cs.parabolic (c_component (M := M) I a))) :
      let D := c_component (M := M) I a
      let E := D \ {a}
      let wD : W := c_selectedLongest cs D hD D (fun _ h => h)
      let wE : W := c_selectedLongest cs D hD E Set.sdiff_subset
      let ν := c_selectedOpposition cs I a hD
      let crossing := SimpleWallCrossings S W M cs I a ha hD
      (∀ u : cs.parabolic D, cs.length (u : W) ≤ cs.length wD) ∧
      (∀ u : cs.parabolic E, cs.length (u : W) ≤ cs.length wE) ∧
      wD * wD = 1 ∧ Function.Involutive ν ∧
      (∀ i : D, cs.geometricRepresentation wD (Finsupp.single (i : S) (1 : ℝ)) =
        -Finsupp.single (ν i : S) 1) ∧
      crossing.1 = wE * wD ∧
      crossing.2.1 = Set.insert a I \ {(ν ⟨a, Set.mem_insert a I, Relation.ReflTransGen.refl⟩ : S)} ∧
      (cs.parabolic crossing.2.1).map (MulAut.conj crossing.1).toMonoidHom = cs.parabolic I ∧
      cs.geometricRepresentation crossing.1 ''
        ((fun i : S => Finsupp.single i (1 : ℝ)) '' crossing.2.1) =
        (fun i : S => Finsupp.single i (1 : ℝ)) '' I ∧
      crossing.1 ∈ cs.parabolic (Set.insert a I) := by
    let D := c_component (M := M) I a
    have oppositionWork (L : Set S) (z : cs.parabolic L)
        (hz : ∀ u : cs.parabolic L, cs.length (u : W) ≤ cs.length (z : W)) :
        (z : W) * z = 1 ∧ ∃ e : L ≃ L, Function.Involutive e ∧
          (∀ i : L, cs.geometricRepresentation (z : W) (Finsupp.single (i : S) 1) =
            -Finsupp.single (e i : S) 1) ∧
          (∀ i : L, (z : W) * cs.simple (i : S) * (z : W)⁻¹ = cs.simple (e i : S)) := by
      classical
      let act := cs.geometricRepresentation
      let root : S → S →₀ ℝ := fun i => Finsupp.single i 1
      have outside (w : W) (hw : w ∈ cs.parabolic L) (k : S) (hk : k ∉ L)
          (x : S →₀ ℝ) : act w x k = x k := by
        obtain ⟨u, hu, rfl⟩ := cs.exists_wordProd_eq_of_mem_parabolic hw
        induction u with
        | nil => simp [act]
        | cons i u ih =>
          have hki : k ≠ i := fun h => hk (h ▸ hu i (by simp))
          simp only [cs.wordProd_cons, map_mul, mul_apply_eq_comp]
          rw [cs.geometricRepresentation_simple, M.geometricReflection_apply_apply_of_ne hki]
          exact ih (fun j hj => hu j (by simp [hj])) (cs.wordProd_mem_parabolic (fun j hj => hu j (by simp [hj])))
      have desc (i : S) (hi : i ∈ L) : cs.length ((z : W) * cs.simple i) + 1 = cs.length z := by
        have h := hz ⟨_, (cs.parabolic L).mul_mem z.property (cs.simple_mem_parabolic hi)⟩
        change cs.length ((z : W) * cs.simple i) ≤ cs.length (z : W) at h
        rcases cs.length_mul_simple (z : W) i with h' | h' <;> omega
      have cols (i : S) (hi : i ∈ L) : act (z : W) (root i) ≤ 0 :=
        ((cs.geometricRepresentation_single_neg_iff (z : W) i).mpr (by
          change cs.length ((z : W) * cs.simple i) < cs.length (z : W)
          have := desc i hi
          omega)).le
      have nonpos (x : S →₀ ℝ) (hx : 0 ≤ x) (hs : ∀ k, k ∉ L → x k = 0) :
          act (z : W) x ≤ 0 := by
        have he : x = ∑ i ∈ x.support, x i • root i := by
          ext k
          simp [root, Finsupp.single_apply, Finset.sum_ite_eq']
        rw [he, map_sum]
        intro k
        simp only [Finset.sum_apply', map_smul, Finsupp.smul_apply,
          Pi.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply]
        apply Finset.sum_nonpos
        intro i hi
        have hiL : i ∈ L := by
          by_contra hn
          exact (Finsupp.mem_support_iff.mp hi) (hs i hn)
        exact mul_nonpos_of_nonneg_of_nonpos (hx i) (cols i hiL k)
      have len (u : W) (hu : u ∈ cs.parabolic L) :
          cs.length ((z : W) * u) + cs.length u = cs.length z := by
        obtain ⟨v, hv, hL, rfl⟩ := cs.exists_isReduced_wordProd_eq_of_mem_parabolic hu
        have H : ∀ v : List S, cs.IsReduced v → (∀ i ∈ v, i ∈ L) →
            cs.length ((z : W) * cs.wordProd v) + v.length = cs.length z := by
          intro v
          induction v using List.reverseRecOn with
          | nil => simp
          | append_singleton v i ih =>
            intro hred hL
            have hrv : cs.IsReduced v := by simpa only [List.take_left] using hred.take v.length
            have hvL : ∀ j ∈ v, j ∈ L := fun j hj => hL j (by simp [hj])
            have hiL := hL i (by simp)
            have hp := ih hrv hvL
            have has : cs.length (cs.wordProd v * cs.simple i) = cs.length (cs.wordProd v) + 1 := by
              simpa only [cs.wordProd_append, cs.wordProd_singleton, List.length_append,
                List.length_singleton, hrv.eq] using hred.eq
            have hpos : 0 < act (cs.wordProd v) (root i) :=
              (cs.geometricRepresentation_single_pos_iff _ _).mpr (by
                change ¬ cs.length (cs.wordProd v * cs.simple i) < cs.length (cs.wordProd v)
                omega)
            have hs : ∀ k, k ∉ L → act (cs.wordProd v) (root i) k = 0 := by
              intro k hk
              rw [outside _ (cs.wordProd_mem_parabolic hvL) k hk]
              simp [root, show i ≠ k from fun h => hk (h ▸ hiL)]
            have hn := nonpos _ hpos.le hs
            have hneg : act ((z : W) * cs.wordProd v) (root i) < 0 := by
              refine lt_of_le_of_ne ?_ ?_
              · simpa only [map_mul, mul_apply_eq_comp] using hn
              · exact (cs.ne_zero_of_mem_geometricRoots ⟨_, i, rfl⟩)
            have hd := (cs.geometricRepresentation_single_neg_iff _ i).mp hneg
            have hh := cs.length_mul_simple ((z : W) * cs.wordProd v) i
            change cs.length (((z : W) * cs.wordProd v) * cs.simple i) <
              cs.length ((z : W) * cs.wordProd v) at hd
            simp only [cs.wordProd_append, cs.wordProd_singleton, List.length_append, List.length_singleton]
            rw [← mul_assoc]
            omega
        simpa only [hv.eq] using H v hv hL
      have zz : (z : W) * z = 1 := cs.length_eq_zero_iff.mp (by
        have := len (z : W) z.property
        omega)
      have zinv : (z : W)⁻¹ = z := inv_eq_of_mul_eq_one_left zz
      have index (i : L) : ∃ j : L,
          act (z : W) (root i) = -root j ∧
          (z : W) * cs.simple i * (z : W)⁻¹ = cs.simple j := by
        have hleft : cs.length (cs.simple (i : S) * (z : W)) + 1 = cs.length z := by
          have h := hz ⟨_, (cs.parabolic L).mul_mem (cs.simple_mem_parabolic i.property) z.property⟩
          change cs.length (cs.simple (i : S) * (z : W)) ≤ cs.length (z : W) at h
          rcases cs.length_simple_mul (z : W) i with h' | h' <;> omega
        have hlen := len (cs.simple i * (z : W))
          ((cs.parabolic L).mul_mem (cs.simple_mem_parabolic i.property) z.property)
        obtain ⟨j, hj⟩ := cs.length_eq_one_iff.mp (show cs.length ((z : W) * cs.simple i * z) = 1 by
          rw [mul_assoc]; omega)
        let r := act (z : W) (root i)
        have heig : M.geometricReflection j r = -r := by
          rw [← cs.geometricRepresentation_simple, ← hj]
          simp only [map_mul, mul_apply_eq_comp]
          change act (z : W) (act (cs.simple i) (act (z : W) (act (z : W) (root i)))) = -r
          have hc : act (z : W) (act (z : W) (root i)) = root i := by
            rw [← mul_apply_eq_comp, ← map_mul, zz]; simp [act]
          rw [hc, cs.geometricRepresentation_simple, M.geometricReflection_apply_single_self, map_neg]
        have supp (k : S) (hk : k ≠ j) : r k = 0 := by
          have h := congrArg (fun x : S →₀ ℝ => x k) heig
          rw [M.geometricReflection_apply_apply_of_ne hk] at h
          simp only [Finsupp.neg_apply] at h
          linarith
        have hr : r = -root j := by
          rcases cs.eq_single_or_eq_neg_single_of_mem_geometricRoots ⟨(z : W), i, rfl⟩ supp with h | h
          · have hn := cols i i.property j
            rw [show act (z : W) (root i) = root j from h] at hn
            norm_num [root] at hn
          · exact h
        have hjL : j ∈ L := by
          by_contra hn
          have h := outside (z : W) z.property j hn (root i)
          change r j = (root i) j at h
          rw [hr] at h
          have hij : (i : S) ≠ j := fun h => hn (h ▸ i.property)
          simp [root, hij] at h
        exact ⟨⟨j, hjL⟩, hr, by simpa [zinv] using hj⟩
      choose f hf hg using index
      have hinv : Function.Involutive f := by
        intro i
        apply Subtype.ext
        apply Finsupp.single_left_injective (show (1 : ℝ) ≠ 0 by norm_num)
        have h : act (z : W) (act (z : W) (root i)) = root i := by
          rw [← mul_apply_eq_comp, ← map_mul, zz]; simp [act]
        rw [hf i, map_neg, hf (f i), neg_neg] at h
        exact h
      let e : L ≃ L := { toFun := f, invFun := f, left_inv := hinv, right_inv := hinv }
      exact ⟨zz, e, hinv, hf, hg⟩
    classical
    letI : Finite (cs.parabolic D) := hD
    let subfinite (L : Set S) (hL : L ⊆ D) : Finite (cs.parabolic L) :=
      Finite.of_injective
        (fun w : cs.parabolic L => (⟨(w : W), (cs.parabolic_mono hL) w.property⟩ : cs.parabolic D))
        (fun _ _ h => Subtype.ext (congrArg (fun z : cs.parabolic D => (z : W)) h))
    let longest (L : Set S) (hL : L ⊆ D) : cs.parabolic L :=
      letI := subfinite L hL
      Classical.choose (Finite.exists_max (fun w : cs.parabolic L => cs.length (w : W)))
    have longest_max (L : Set S) (hL : L ⊆ D) :
        ∀ u : cs.parabolic L, cs.length (u : W) ≤ cs.length (longest L hL : W) := by
      letI := subfinite L hL
      exact Classical.choose_spec (Finite.exists_max (fun w : cs.parabolic L => cs.length (w : W)))
    let wD : W := longest D (fun _ h => h)
    let E : Set S := D \ {a}
    let wE : W := longest E Set.sdiff_subset
    let ν : D ≃ D := @Classical.epsilon (D ≃ D) ⟨Equiv.refl D⟩
      (fun e => ∀ i : D, cs.geometricRepresentation wD (Finsupp.single (i : S) (1 : ℝ)) =
        -Finsupp.single (e i : S) 1)
    let aD : D := ⟨a, ⟨Set.mem_insert a I, Relation.ReflTransGen.refl⟩⟩
    let K : Set S := Set.insert a I \ {(ν aD : S)}
    let v : W := wE * wD
    have hDopp := oppositionWork D (longest D (fun _ h => h)) (longest_max D (fun _ h => h))
    obtain ⟨eD, heDinv, heDroot, heDgen⟩ := hDopp.2
    have hνroot : ∀ i : D, cs.geometricRepresentation wD (Finsupp.single (i : S) (1 : ℝ)) =
        -Finsupp.single (ν i : S) 1 := by
      exact Classical.epsilon_spec_aux ⟨Equiv.refl D⟩
        (fun e : D ≃ D => ∀ i : D, cs.geometricRepresentation wD (Finsupp.single (i : S) (1 : ℝ)) =
          -Finsupp.single (e i : S) 1) ⟨eD, heDroot⟩
    have hνeq : ν = eD := by
      apply Equiv.ext
      intro i
      apply Subtype.ext
      apply Finsupp.single_left_injective (show (1 : ℝ) ≠ 0 by norm_num)
      exact neg_injective ((hνroot i).symm.trans (heDroot i))
    have hνinv : Function.Involutive ν := by simpa only [hνeq] using heDinv
    have hνgen : ∀ i : D, wD * cs.simple (i : S) * wD⁻¹ = cs.simple (ν i : S) := by
      simpa only [hνeq] using heDgen
    obtain ⟨μ, hμinv, hμroot, hμgen⟩ :=
      (oppositionWork E (longest E Set.sdiff_subset) (longest_max E Set.sdiff_subset)).2
    have hDsub : D ⊆ Set.insert a I := fun _ h => h.1
    have hEsub : E ⊆ I := by
      intro i hi
      rcases hDsub hi.1 with h | h
      · exact False.elim (hi.2 (Set.mem_singleton_iff.mpr h))
      · exact h
    have hwD : wD ∈ cs.parabolic D := (longest D (fun _ h => h)).property
    have hwE : wE ∈ cs.parabolic D := cs.parabolic_mono Set.sdiff_subset (longest E Set.sdiff_subset).property
    have hdisconnect : ∀ w : W, w ∈ cs.parabolic D → ∀ k : S, k ∈ I \ D →
        cs.geometricRepresentation w (Finsupp.single k (1 : ℝ)) = Finsupp.single k 1 ∧
        Commute w (cs.simple k) := by
      intro w hw k hk
      have htwo (d : S) (hd : d ∈ D) : M d k = 2 := by
        by_contra hne
        have hdk : d ≠ k := fun h => hk.2 (h ▸ hd)
        have hkD : k ∈ D := ⟨Set.mem_insert_of_mem a hk.1,
          Relation.ReflTransGen.tail hd.2 ⟨hd.1, Set.mem_insert_of_mem a hk.1, hdk, hne⟩⟩
        exact hk.2 hkD
      have hfixgen (d : S) (hd : d ∈ D) :
          cs.geometricRepresentation (cs.simple d) (Finsupp.single k (1 : ℝ)) = Finsupp.single k 1 := by
        rw [cs.geometricRepresentation_simple]
        apply M.geometricReflection_apply_of_eq_zero
        simp [M.geometricForm_single_single, htwo d hd, Real.cos_pi_div_two]
      obtain ⟨u, hu, rfl⟩ := cs.exists_wordProd_eq_of_mem_parabolic hw
      have H : ∀ u : List S, (∀ i ∈ u, i ∈ D) →
          cs.geometricRepresentation (cs.wordProd u) (Finsupp.single k (1 : ℝ)) = Finsupp.single k 1 ∧
          Commute (cs.wordProd u) (cs.simple k) := by
        intro u
        induction u with
        | nil => simp [Commute]
        | cons d u ih =>
          intro hu
          obtain ⟨hr, hc⟩ := ih (fun i hi => hu i (by simp [hi]))
          have hd := hu d (by simp)
          refine ⟨?_, ?_⟩
          · rw [cs.wordProd_cons, map_mul, mul_apply_eq_comp, hr, hfixgen d hd]
          · rw [cs.wordProd_cons]
            exact (cs.commute_simple_of_eq_two (htwo d hd)).mul_left hc
      exact H u hu
    let root : S → S →₀ ℝ := fun i => Finsupp.single i 1
    have hcomponent (k : D) (hk : (k : S) ≠ (ν aD : S)) :
        ∃ i : E, cs.geometricRepresentation v (root k) = root i ∧
          v * cs.simple k * v⁻¹ = cs.simple i := by
      have hνk : (ν k : S) ≠ a := by
        intro heq
        have hh : ν k = aD := Subtype.ext heq
        have hh' : k = ν aD := by rw [← hνinv k, hh]
        exact hk (congrArg Subtype.val hh')
      let j : E := ⟨ν k, ⟨(ν k).property, hνk⟩⟩
      refine ⟨μ j, ?_, ?_⟩
      · change cs.geometricRepresentation (wE * wD) (Finsupp.single (k : S) 1) =
          Finsupp.single (μ j : S) 1
        rw [map_mul, mul_apply_eq_comp, hνroot k, map_neg, hμroot j, neg_neg]
      · change (wE * wD) * cs.simple k * (wE * wD)⁻¹ = cs.simple (μ j : S)
        calc
          _ = wE * (wD * cs.simple k * wD⁻¹) * wE⁻¹ := by group
          _ = cs.simple (μ j : S) := by rw [hνgen k, hμgen j]
    have hforward (k : S) (hk : k ∈ K) : ∃ i ∈ I,
        cs.geometricRepresentation v (root k) = root i ∧
        v * cs.simple k * v⁻¹ = cs.simple i := by
      by_cases hkd : k ∈ D
      · obtain ⟨i, hr, hg⟩ := hcomponent ⟨k, hkd⟩ hk.2
        exact ⟨i, hEsub i.property, hr, hg⟩
      · have hkI : k ∈ I := by
          rcases hk.1 with heq | hi
          · exact False.elim (hkd (heq ▸ aD.property))
          · exact hi
        obtain ⟨hrD, hgD⟩ := hdisconnect wD hwD k ⟨hkI, hkd⟩
        obtain ⟨hrE, hgE⟩ := hdisconnect wE hwE k ⟨hkI, hkd⟩
        refine ⟨k, hkI, ?_, ?_⟩
        · change cs.geometricRepresentation (wE * wD) (root k) = root k
          rw [map_mul, mul_apply_eq_comp, hrD, hrE]
        · change (wE * wD) * cs.simple k * (wE * wD)⁻¹ = cs.simple k
          rw [hgE.mul_left hgD]
          simp only [mul_inv_cancel_right]
    have hreverse (i : S) (hi : i ∈ I) : ∃ k ∈ K,
        cs.geometricRepresentation v (root k) = root i ∧
        v * cs.simple k * v⁻¹ = cs.simple i := by
      by_cases hid : i ∈ D
      · let iE : E := ⟨i, ⟨hid, fun h => ha ((Set.mem_singleton_iff.mp h) ▸ hi)⟩⟩
        let j : D := ⟨μ iE, (μ iE).property.1⟩
        let k : D := ν j
        have hkne : (k : S) ≠ (ν aD : S) := by
          intro heq
          have hh : j = aD := ν.injective (Subtype.ext heq)
          exact (μ iE).property.2 (Set.mem_singleton_iff.mpr (congrArg Subtype.val hh))
        have hkK : (k : S) ∈ K := ⟨hDsub k.property, hkne⟩
        have hνk : ν k = j := hνinv j
        have hr : cs.geometricRepresentation v (root k) = root i := by
          change cs.geometricRepresentation (wE * wD) (Finsupp.single (k : S) 1) = Finsupp.single i 1
          rw [map_mul, mul_apply_eq_comp, hνroot k, map_neg]
          change -cs.geometricRepresentation wE (Finsupp.single (ν k : S) 1) = Finsupp.single i 1
          rw [hνk, hμroot (μ iE), hμinv iE, neg_neg]
        have hg : v * cs.simple k * v⁻¹ = cs.simple i := by
          change (wE * wD) * cs.simple k * (wE * wD)⁻¹ = cs.simple i
          calc
            _ = wE * (wD * cs.simple k * wD⁻¹) * wE⁻¹ := by group
            _ = cs.simple i := by rw [hνgen k, hνk, hμgen (μ iE), hμinv iE]
        exact ⟨k, hkK, hr, hg⟩
      · have hiK : i ∈ K := ⟨Set.mem_insert_of_mem a hi, fun heq => hid (heq ▸ (ν aD).property)⟩
        obtain ⟨hrD, hgD⟩ := hdisconnect wD hwD i ⟨hi, hid⟩
        obtain ⟨hrE, hgE⟩ := hdisconnect wE hwE i ⟨hi, hid⟩
        refine ⟨i, hiK, ?_, ?_⟩
        · change cs.geometricRepresentation (wE * wD) (root i) = root i
          rw [map_mul, mul_apply_eq_comp, hrD, hrE]
        · change (wE * wD) * cs.simple i * (wE * wD)⁻¹ = cs.simple i
          rw [hgE.mul_left hgD]
          simp only [mul_inv_cancel_right]
    have hroots : cs.geometricRepresentation v '' (root '' K) = root '' I := by
      ext r
      constructor
      · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
        obtain ⟨i, hi, hr, _⟩ := hforward k hk
        exact ⟨i, hi, hr.symm⟩
      · rintro ⟨i, hi, rfl⟩
        obtain ⟨k, hk, hr, _⟩ := hreverse i hi
        exact ⟨root k, ⟨k, hk, rfl⟩, hr⟩
    have hgens : (MulAut.conj v) '' (cs.simple '' K) = cs.simple '' I := by
      ext s
      constructor
      · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
        obtain ⟨i, hi, _, hg⟩ := hforward k hk
        exact ⟨i, hi, hg.symm⟩
      · rintro ⟨i, hi, rfl⟩
        obtain ⟨k, hk, _, hg⟩ := hreverse i hi
        exact ⟨cs.simple k, ⟨k, hk, rfl⟩, hg⟩
    have hconj : (cs.parabolic K).map (MulAut.conj v).toMonoidHom = cs.parabolic I := by
      rw [CoxeterSystem.parabolic, MonoidHom.map_closure]
      exact congrArg Subgroup.closure hgens
    have hv : v ∈ cs.parabolic (Set.insert a I) :=
      cs.parabolic_mono hDsub ((cs.parabolic D).mul_mem hwE hwD)
    exact ⟨longest_max D (fun _ h => h), longest_max E Set.sdiff_subset,
      hDopp.1, hνinv, hνroot, rfl, rfl, hconj, hroots, hv⟩
  have c_literal_label_preserved {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J I K : Set S) (x v : W)
      (hcos : (fun u : W => u * x) '' (cs.parabolic J : Set W) =
        (fun u : W => x * u) '' (cs.parabolic I : Set W))
      (hmin : cs.IsMinimalCosetRep I x)
      (hconj : (cs.parabolic K).map (MulAut.conj v).toMonoidHom = cs.parabolic I)
      (hroots : cs.geometricRepresentation v ''
        ((fun i : S => Finsupp.single i (1 : ℝ)) '' K) =
        (fun i : S => Finsupp.single i (1 : ℝ)) '' I) :
      (fun u : W => u * (x * v)) '' (cs.parabolic J : Set W) =
        (fun u : W => (x * v) * u) '' (cs.parabolic K : Set W) ∧
      cs.IsMinimalCosetRep K (x * v) := by
    constructor
    · ext r
      constructor
      · rintro ⟨j, hj, rfl⟩
        have hji : j * x ∈ (fun u : W => x * u) '' (cs.parabolic I : Set W) := hcos ▸ ⟨j, hj, rfl⟩
        obtain ⟨i, hi, hxi⟩ := hji
        change x * i = j * x at hxi
        rw [← hconj] at hi
        obtain ⟨k, hk, hki⟩ := hi
        change v * k * v⁻¹ = i at hki
        refine ⟨k, hk, ?_⟩
        calc
          (x * v) * k = (x * i) * v := by rw [← hki]; group
          _ = j * (x * v) := by rw [hxi]; group
      · rintro ⟨k, hk, rfl⟩
        have hi : v * k * v⁻¹ ∈ cs.parabolic I := by
          rw [← hconj]
          exact ⟨k, hk, rfl⟩
        have hxj : x * (v * k * v⁻¹) ∈
            (fun u : W => u * x) '' (cs.parabolic J : Set W) :=
          hcos.symm ▸ ⟨v * k * v⁻¹, hi, rfl⟩
        obtain ⟨j, hj, hjx⟩ := hxj
        change j * x = x * (v * k * v⁻¹) at hjx
        refine ⟨j, hj, ?_⟩
        calc
          j * (x * v) = (j * x) * v := by group
          _ = (x * (v * k * v⁻¹)) * v := by rw [hjx]
          _ = (x * v) * k := by group
    · apply cs.isMinimalCosetRep_iff.mpr
      intro k hk
      have hr : cs.geometricRepresentation v (Finsupp.single k (1 : ℝ)) ∈
          (fun i : S => Finsupp.single i (1 : ℝ)) '' I :=
        hroots ▸ ⟨Finsupp.single k 1, ⟨k, hk, rfl⟩, rfl⟩
      obtain ⟨i, hi, heq⟩ := hr
      have hpos : 0 < cs.geometricRepresentation x (Finsupp.single i (1 : ℝ)) :=
        (cs.geometricRepresentation_single_pos_iff x i).mpr (cs.isMinimalCosetRep_iff.mp hmin i hi)
      apply (cs.geometricRepresentation_single_pos_iff (x * v) k).mp
      simpa only [map_mul, mul_apply_eq_comp, ← heq] using hpos
  have c_actual_label {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J I : Set S) (x : W)
      (a : S) (ha : a ∉ I)
      (hD : Finite (cs.parabolic (c_component (M := M) I a)))
      (hx : (fun u : W => u * x) '' (cs.parabolic J : Set W) =
        (fun u : W => x * u) '' (cs.parabolic I : Set W) ∧ cs.IsMinimalCosetRep I x) :
      let crossing := SimpleWallCrossings S W M cs I a ha hD
      (fun u : W => u * (x * crossing.1)) '' (cs.parabolic J : Set W) =
        (fun u : W => (x * crossing.1) * u) '' (cs.parabolic crossing.2.1 : Set W) ∧
      cs.IsMinimalCosetRep crossing.2.1 (x * crossing.1) := by
    have hc := c_actual_certificate cs I a ha hD
    exact c_literal_label_preserved cs J I _ x _ hx.1 hx.2
      hc.2.2.2.2.2.2.2.1 hc.2.2.2.2.2.2.2.2.1
  let c_face {S : Type _} (I : Set S) : Set (Dual S) :=
    {f | f ∈ relativeSubspace I ∧ ∀ i : S, i ∉ I → 0 < dualCoordinates f i}
  let c_region {S : Type _} (M : CoxeterMatrix S) (J : Set S) (x : M.Group) (I : Set S) :
      Set (relativeSubspace J) :=
    {f | ∃ g : Dual S, g ∈ c_face I ∧ dualAction M x g = f.val}
  have c_facet_action_eq {S : Type _} (M : CoxeterMatrix S) (J L : Set S) (x v : M.Group)
      (hv : v ∈ M.toCoxeterSystem.parabolic L) :
      c_region M J (x * v) L = c_region M J x L := by
    have hfix (g : Dual S) (hg : g ∈ relativeSubspace L) : dualAction M v g = g := by
      apply (mem_relativeSubspace_iff_fixed M L g).mp hg
      rw [coxeterParabolic_eq]
      exact hv
    ext f
    constructor
    · rintro ⟨g, hg, heq⟩
      refine ⟨g, hg, ?_⟩
      rw [map_mul, mul_apply_eq_comp, hfix g hg.1] at heq
      exact heq
    · rintro ⟨g, hg, heq⟩
      refine ⟨g, hg, ?_⟩
      rw [map_mul, mul_apply_eq_comp, hfix g hg.1]
      exact heq
  have c_actual_open_enlarged_facets {S : Type _} [Finite S] (M : CoxeterMatrix S) (J I : Set S)
      (x : M.Group) (a : S) (ha : a ∉ I)
      (hD : Finite (M.toCoxeterSystem.parabolic (c_component (M := M) I a))) :
      let D := c_component (M := M) I a
      let ν := c_selectedOpposition M.toCoxeterSystem I a hD
      let b : S := ν ⟨a, Set.mem_insert a I, Relation.ReflTransGen.refl⟩
      let crossing := SimpleWallCrossings S M.Group M M.toCoxeterSystem I a ha hD
      b ∈ D ∧ b ∉ crossing.2.1 ∧ Set.insert b crossing.2.1 = Set.insert a I ∧
      c_region M J (x * crossing.1) (Set.insert b crossing.2.1) =
        c_region M J x (Set.insert a I) := by
    classical
    let D := c_component (M := M) I a
    let ν := c_selectedOpposition M.toCoxeterSystem I a hD
    let b : S := ν ⟨a, Set.mem_insert a I, Relation.ReflTransGen.refl⟩
    let crossing := SimpleWallCrossings S M.Group M M.toCoxeterSystem I a ha hD
    have hc := c_actual_certificate M.toCoxeterSystem I a ha hD
    have hb : b ∈ D := (ν ⟨a, Set.mem_insert a I, Relation.ReflTransGen.refl⟩).property
    have hK : crossing.2.1 = Set.insert a I \ {b} := hc.2.2.2.2.2.2.1
    have hbn : b ∉ crossing.2.1 := by rw [hK]; simp
    have hins : Set.insert b crossing.2.1 = Set.insert a I := by
      rw [hK]
      have hbL : b ∈ Set.insert a I := hb.1
      ext c
      change (c = b ∨ (c = a ∨ c ∈ I) ∧ c ≠ b) ↔ (c = a ∨ c ∈ I)
      have hbL : b = a ∨ b ∈ I := hbL
      constructor
      · rintro (rfl | ⟨hc, _⟩)
        · exact hbL
        · exact hc
      · intro hc
        by_cases hcb : c = b
        · exact Or.inl hcb
        · exact Or.inr ⟨hc, hcb⟩
    refine ⟨hb, hbn, hins, ?_⟩
    rw [hins]
    exact c_facet_action_eq M J (Set.insert a I) x crossing.1 hc.2.2.2.2.2.2.2.2.2
  have full_flat_opposite_evaluation
      {S : Type _} (M : CoxeterMatrix S) (I D : Set S)
      (aD : D) (ha : aD.val ∉ I) (hDsub : D ⊆ Set.insert aD.val I)
      (wD wE : M.Group) (ν : D ≃ D)
      (hDsq : wD * wD = 1)
      (hνroot : ∀ i : D, M.toCoxeterSystem.geometricRepresentation wD
        (Finsupp.single i.val (1 : ℝ)) = -Finsupp.single (ν i).val (1 : ℝ))
      (hwE : wE ∈ M.toCoxeterSystem.parabolic (D \ {aD.val}))
      (f : Dual S)
      (hf : f ∈ relativeSubspace (Set.insert aD.val I \ {(ν aD).val})) :
      dualAction M (wE * wD) f (Finsupp.single aD.val (1 : ℝ)) =
        -f (Finsupp.single (ν aD).val (1 : ℝ)) := by
    have hDinv : wD⁻¹ = wD := inv_eq_of_mul_eq_one_left hDsq
    let g := dualAction M wD f
    have hg : g ∈ relativeSubspace (D \ {aD.val}) := by
      intro i hi
      have hne : (ν ⟨i, hi.1⟩).val ≠ (ν aD).val := by
        intro he
        have he' := congrArg Subtype.val (ν.injective (Subtype.ext he))
        exact hi.2 (Set.mem_singleton_iff.mpr he')
      have hz : f (Finsupp.single (ν ⟨i, hi.1⟩).val (1 : ℝ)) = 0 :=
        hf _ ⟨hDsub (ν ⟨i, hi.1⟩).property, hne⟩
      change (dualAction M wD f) (Finsupp.single i (1 : ℝ)) = 0
      rw [dualAction_apply, hDinv, hνroot ⟨i, hi.1⟩, map_neg, hz, neg_zero]
    have hfix : dualAction M wE g = g :=
      (mem_relativeSubspace_iff_fixed M (D \ {aD.val}) g).mp hg wE hwE
    change (dualAction M (wE * wD) f) (Finsupp.single aD.val (1 : ℝ)) = _
    rw [map_mul, mul_apply_eq_comp]
    change (dualAction M wE g) _ = _
    rw [hfix]
    change (dualAction M wD f) _ = _
    rw [dualAction_apply, hDinv, hνroot aD, map_neg]
  have FiniteComponentOppositeChamber : (∀ {S : Type _} [Finite S] (M : CoxeterMatrix S) (J : Set S),
    let W := M.Group
    let cs := M.toCoxeterSystem
    let Θ := relativeSubspace J
    letI : TopologicalSpace Θ := TopologicalSpace.induced
      (fun f : Θ => dualCoordinates f.val) (inferInstance : TopologicalSpace (S → Real))
    let arrangement : Set (Submodule Real Θ) := (RelativeCone M J).2.2.2.2.2
    let label : W → Set S → Prop := fun x I =>
      Set.image (fun u : W => u * x) (parabolic cs J : Set W) =
        Set.image (fun u : W => x * u) (parabolic cs I : Set W) ∧ IsMinimalCosetRep cs I x
    let face : Set S → Set (Dual S) := fun I =>
      { f | f ∈ relativeSubspace I ∧ ∀ i : S, i ∉ I → 0 < dualCoordinates f i }
    let region : W → Set S → Set Θ := fun x I =>
      { f | ∃ g : Dual S, g ∈ face I ∧ dualAction M x g = f.val }
    let affineDimension : Set Θ → Nat := fun A =>
      Module.finrank Real (AffineSubspace.direction (affineSpan Real A))
    let wall : Set Θ → Set Θ → Prop := fun C F =>
      Set.Nonempty F ∧ ∃ H : Submodule Real Θ, H ∈ arrangement ∧
        F = closure C ∩ (H : Set Θ) ∧ affineDimension F + 1 = affineDimension C
    let component : Set S → S → Set S := fun I a =>
      { b | b ∈ Set.insert a I ∧ Relation.ReflTransGen
        (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b }
    ∀ (x : W) (I : Set S), label x I →
      ∀ (a : S) (ha : a ∉ I) (hD : Finite (parabolic cs (component I a))),
        let forward := SimpleWallCrossings S W M cs I a ha hD
        label (x * forward.1) forward.2.1 ∧
        (∃ b : S, b ∈ component I a ∧ b ∉ forward.2.1 ∧
          forward.2.1 = Set.insert a I \ {b} ∧
          closure (region x (Set.insert a I)) =
            closure (region (x * forward.1) (Set.insert b forward.2.1))) ∧
        (∀ (y : W) (K : Set S), label y K →
          ∀ F : Set Θ, region x I ≠ region y K → wall (region x I) F → wall (region y K) F →
            F = closure (region x (Set.insert a I)) → forward.2.2 x = (y, K))) := by
    classical
    intro S inst M J
    let W := M.Group
    let cs := M.toCoxeterSystem
    have nonnegClosure (I : Set S) (f : relativeSubspace I)
        (hf : ∀ i, i ∉ I → 0 ≤ dualCoordinates f.val i) :
        f ∈ closure {q : relativeSubspace I | q.val ∈ standardFacet M I} := by
      letI : IsTopologicalAddGroup (Dual S) := dualTopologicalAddGroup
      letI : ContinuousSMul ℝ (Dual S) := dualContinuousSMul
      let d : relativeSubspace I := ⟨canonicalDominant I, canonicalDominant_mem_relativeSubspace I⟩
      let γ : ℝ → relativeSubspace I := fun t => f + t • d
      have hc : Continuous γ :=
        (show Continuous (fun t : ℝ => f.val + t • d.val) from
          continuous_const.add (continuous_id.smul continuous_const)).subtype_mk _
      have ht : Filter.Tendsto γ (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds f) := by
        have h := hc.continuousAt.tendsto.mono_left
          (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
        simpa only [γ, zero_smul, add_zero] using h
      apply mem_closure_of_tendsto ht
      filter_upwards [self_mem_nhdsWithin] with t ht
      refine ⟨(γ t).property, ?_⟩
      intro i hi
      change 0 < f.val (simpleRoot i) + t * (canonicalDominant I) (simpleRoot i)
      rw [canonicalDominant_apply_simpleRoot]
      simp only [if_neg hi, mul_one]
      exact add_pos_of_nonneg_of_pos (hf i hi) ht
    dsimp only
    have htop : TopologicalSpace.induced
        (fun f : relativeSubspace J => dualCoordinates f.val)
        (inferInstance : TopologicalSpace (S → ℝ)) =
        (inferInstance : TopologicalSpace (relativeSubspace J)) := induced_compose.symm
    rw [htop]
    intro x I hx a ha hD
    let D := c_component (M := M) I a
    let ν := c_selectedOpposition cs I a hD
    let b : S := ν ⟨a, Set.mem_insert a I, Relation.ReflTransGen.refl⟩
    let forward := SimpleWallCrossings S W M cs I a ha hD
    let L := forward.2.1
    have hc := c_actual_certificate cs I a ha hD
    have hK : L = Set.insert a I \ {b} := hc.2.2.2.2.2.2.1
    have hlabel := c_actual_label cs J I x a ha hD hx
    have hopen := c_actual_open_enlarged_facets M J I x a ha hD
    have hbD : b ∈ D := hopen.1
    have hb : b ∉ L := hopen.2.1
    have hins : Set.insert b L = Set.insert a I := hopen.2.2.1
    let Θ := relativeSubspace J
    let R : W → Set S → Set Θ := fun w N =>
      {p | ∃ g, g ∈ standardFacet M N ∧ dualAction M w g = p.val}
    have hequal : R (x * forward.1) (Set.insert b L) = R x (Set.insert a I) := hopen.2.2.2
    refine ⟨hlabel, ⟨b, hbD, hb, hK, congrArg closure hequal.symm⟩, ?_⟩
    intro y K hy F hne hwallx hwally hF
    change R x I ≠ R y K at hne
    change F = closure (R x (Set.insert a I)) at hF
    let X : RawFacetLabel M J := ⟨I, x, r_coset_conj M J I x hx.1⟩
    let Y : RawFacetLabel M J := ⟨K, y, r_coset_conj M J K y hy.1⟩
    let Z : RawFacetLabel M J :=
      ⟨L, x * forward.1, r_coset_conj M J L (x * forward.1) hlabel.1⟩
    let eX := facetFlatEquiv X
    let eZ := facetFlatEquiv Z
    have hRX : R x I = translatedFacet X := by ext q; exact (mem_translatedFacet_iff X q).symm
    have hRY : R y K = translatedFacet Y := by ext q; exact (mem_translatedFacet_iff Y q).symm
    have hRZ : R (x * forward.1) L = translatedFacet Z := by
      ext q; exact (mem_translatedFacet_iff Z q).symm
    let d : relativeSubspace I :=
      ⟨canonicalDominant (Set.insert a I), fun i hi =>
        canonicalDominant_mem_relativeSubspace (Set.insert a I) i (Set.mem_insert_of_mem a hi)⟩
    let p : Θ := eX d
    have hpR : p ∈ R x (Set.insert a I) :=
      ⟨d.val, canonicalDominant_mem_standardFacet M (Set.insert a I), rfl⟩
    have hpZ : p ∈ R (x * forward.1) (Set.insert b L) := hequal.symm ▸ hpR
    have hpF : p ∈ F := hF ▸ subset_closure hpR
    have hpY : p ∈ closure (R y K) := by
      obtain ⟨H, hH, hF', hdim⟩ := hwally.2
      rw [hF'] at hpF
      exact hpF.1
    let G : Set Θ := {q |
      (∀ i : S, i ∉ Set.insert a I → 0 < dualCoordinates (eX.symm q).val i) ∧
      (∀ i : S, i ∉ Set.insert b L → 0 < dualCoordinates (eZ.symm q).val i)}
    have positiveOpen (N : Set S) (e : relativeSubspace N ≃L[ℝ] Θ) (c : S) :
        IsOpen {q : Θ | ∀ i : S, i ∉ Set.insert c N →
          0 < dualCoordinates (e.symm q).val i} := by
      simp only [Set.setOf_forall]
      apply isOpen_iInter_of_finite
      intro i
      apply isOpen_iInter_of_finite
      intro hi
      exact isOpen_lt continuous_const
        ((continuous_evaluation (simpleRoot i)).comp
          (continuous_subtype_val.comp e.symm.continuous))
    have hG : IsOpen G := (positiveOpen I eX a).inter (positiveOpen L eZ b)
    have hpg : p ∈ G := by
      constructor
      · intro i hi
        change 0 < dualCoordinates (eX.symm (eX d)).val i
        rw [eX.symm_apply_apply]
        change 0 < (canonicalDominant (Set.insert a I)) (simpleRoot i)
        rw [canonicalDominant_apply_simpleRoot]
        simp [hi]
      · obtain ⟨g, hg, he⟩ := hpZ
        have hgz : g ∈ relativeSubspace L := fun i hi => hg.1 i (Set.mem_insert_of_mem b hi)
        have hchart : eZ ⟨g, hgz⟩ = p := Subtype.ext he
        intro i hi
        rw [← hchart, eZ.symm_apply_apply]
        exact hg.2 i hi
    obtain ⟨q, hqG, hqY⟩ := mem_closure_iff.mp hpY G hG hpg
    have hqa : dualCoordinates (eX.symm q).val a < 0 := by
      by_contra hn
      have hqnonneg : ∀ i, i ∉ I → 0 ≤ dualCoordinates (eX.symm q).val i := by
        intro i hi
        by_cases he : i = a
        · simpa [he] using le_of_not_gt hn
        · exact (hqG.1 i (fun h => (Set.mem_insert_iff.mp h).elim he hi)).le
      have hclos := nonnegClosure I (eX.symm q) hqnonneg
      have hqX : q ∈ closure (R x I) := by
        rw [hRX, translatedFacet, ← eX.image_closure]
        exact ⟨eX.symm q, hclos, eX.apply_symm_apply q⟩
      have ho : IsOpen (R y K) := hRY ▸ isOpen_translatedFacet Y
      obtain ⟨r, hrY, hrX⟩ := mem_closure_iff.mp hqX (R y K) ho hqY
      apply hne
      rw [hRX, hRY]
      exact translatedFacet_eq_of_intersection X Y ⟨r, hRX ▸ hrX, hRY ▸ hrY⟩
    have hflat := full_flat_opposite_evaluation M I D
      (⟨a, Set.mem_insert a I, Relation.ReflTransGen.refl⟩ : D) ha (fun _ h => h.1)
      (c_selectedLongest cs D hD D (fun _ h => h) : W)
      (c_selectedLongest cs D hD (D \ {a}) Set.sdiff_subset : W)
      ν hc.2.2.1 hc.2.2.2.2.1
      (c_selectedLongest cs D hD (D \ {a}) Set.sdiff_subset).property
      (eZ.symm q).val (hK ▸ (eZ.symm q).property)
    have hidentity : (eX.symm q).val = dualAction M forward.1 (eZ.symm q).val := by
      have h := congrArg (fun f : Dual S => dualAction M x⁻¹ f)
        (congrArg Subtype.val (eZ.apply_symm_apply q))
      change dualAction M x⁻¹ (dualAction M (x * forward.1) (eZ.symm q).val) =
          dualAction M x⁻¹ q.val at h
      rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel_left] at h
      exact h.symm
    have hqb : 0 < dualCoordinates (eZ.symm q).val b := by
      change dualAction M forward.1 (eZ.symm q).val (Finsupp.single a (1 : ℝ)) =
        -(eZ.symm q).val (Finsupp.single b (1 : ℝ)) at hflat
      change (eX.symm q).val (Finsupp.single a (1 : ℝ)) < 0 at hqa
      rw [hidentity, hflat] at hqa
      exact neg_neg_iff_pos.mp hqa
    have hqZ : q ∈ R (x * forward.1) L := by
      refine ⟨(eZ.symm q).val, ⟨(eZ.symm q).property, ?_⟩, ?_⟩
      · intro i hi
        by_cases hib : i = b
        · subst i
          exact hqb
        · exact hqG.2 i (fun h => (Set.mem_insert_iff.mp h).elim hib hi)
      · exact congrArg Subtype.val (eZ.apply_symm_apply q)
    have hi := translatedFacet_intersection_indices_coset Z Y ⟨q, hRZ ▸ hqZ, hRY ▸ hqY⟩
    have hLK : L = K := hi.1
    have hrep : x * forward.1 = y := by
      apply IsMinimalCosetRep.eq_of_inv_mul_mem cs hlabel.2
      · change cs.IsMinimalCosetRep L y
        rw [hLK]
        exact hy.2
      · exact hi.2
    apply Prod.ext
    · exact hrep
    · exact hLK
  have AdjacentSphericalComponent : (∀ {S : Type _} [Finite S] (M : CoxeterMatrix S) (J : Set S),
  let W := M.Group
  let cs := M.toCoxeterSystem
  let Θ := relativeSubspace J
  letI : TopologicalSpace Θ := TopologicalSpace.induced
    (fun f : Θ => dualCoordinates f.val) (inferInstance : TopologicalSpace (S → Real))
  let arrangement : Set (Submodule Real Θ) := (RelativeCone M J).2.2.2.2.2
  let label : W → Set S → Prop := fun x I =>
    Set.image (fun u : W => u * x) (parabolic cs J : Set W) =
      Set.image (fun u : W => x * u) (parabolic cs I : Set W) ∧ IsMinimalCosetRep cs I x
  let face : Set S → Set (Dual S) := fun I =>
    { f | f ∈ relativeSubspace I ∧ ∀ i : S, i ∉ I → 0 < dualCoordinates f i }
  let region : W → Set S → Set Θ := fun x I =>
    { f | ∃ g : Dual S, g ∈ face I ∧ dualAction M x g = f.val }
  let affineDimension : Set Θ → Nat := fun A =>
    Module.finrank Real (AffineSubspace.direction (affineSpan Real A))
  let wall : Set Θ → Set Θ → Prop := fun C F =>
    Set.Nonempty F ∧ ∃ H : Submodule Real Θ, H ∈ arrangement ∧
      F = closure C ∩ (H : Set Θ) ∧ affineDimension F + 1 = affineDimension C
  let component : Set S → S → Set S := fun I a =>
    { b | b ∈ Set.insert a I ∧ Relation.ReflTransGen
      (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b }
  ∀ (x y : W) (I K : Set S), label x I → label y K →
    ∀ F : Set Θ, region x I ≠ region y K → wall (region x I) F → wall (region y K) F →
    ∀ (a : S), a ∉ I → F = closure (region x (Set.insert a I)) →
      Finite (parabolic cs (component I a))) := by
      classical
      intro S inst M J
      let W := M.Group
      let cs := M.toCoxeterSystem
      have parabolic_eq_one_of_fixes_simple (cs : CoxeterSystem M W)
          {L : Set S} {w : W} (hw : w ∈ cs.parabolic L)
          (hfix : ∀ i ∈ L, cs.geometricRepresentation w (Finsupp.single i 1) =
            Finsupp.single i (1 : ℝ)) : w = 1 := by
        by_contra hne
        obtain ⟨i, hi, hd⟩ := cs.exists_rightDescent_mem_of_mem_parabolic_of_ne_one hw hne
        have hn := (cs.geometricRepresentation_single_neg_iff w i).mpr hd
        rw [hfix i hi] at hn
        exact (Finsupp.single_nonneg.mpr (show (0 : ℝ) ≤ 1 by norm_num)).not_gt hn
      have finite_parabolic_of_invariant_spanning_set (cs : CoxeterSystem M W)
          (L : Set S) (E : Set (S →₀ ℝ)) (hE : E.Finite)
          (hstable : ∀ w ∈ cs.parabolic L, ∀ v ∈ E, cs.geometricRepresentation w v ∈ E)
          (hspan : ∀ i ∈ L, Finsupp.single i (1 : ℝ) ∈ Submodule.span ℝ E) :
          Finite (cs.parabolic L) := by
        let : Finite E := hE.to_subtype
        let action : cs.parabolic L → (E → E) := fun w v =>
          ⟨cs.geometricRepresentation w.val v.val, hstable w.val w.property v.val v.property⟩
        apply Finite.of_injective action
        intro g h heq
        have heqE : ∀ v ∈ E, cs.geometricRepresentation g.val v =
            cs.geometricRepresentation h.val v := by
          intro v hv
          exact congrArg Subtype.val (congrFun heq ⟨v, hv⟩)
        have heqSpan : Submodule.span ℝ E ≤
            LinearMap.eqLocus (cs.geometricRepresentation g.val) (cs.geometricRepresentation h.val) :=
          Submodule.span_le.mpr heqE
        apply Subtype.ext
        have hfix : ∀ i ∈ L,
            cs.geometricRepresentation (h.val⁻¹ * g.val) (Finsupp.single i 1) =
              Finsupp.single i (1 : ℝ) := by
          intro i hi
          have hh := heqSpan (hspan i hi)
          change cs.geometricRepresentation g.val (Finsupp.single i 1) =
            cs.geometricRepresentation h.val (Finsupp.single i 1) at hh
          rw [map_mul, mul_apply_eq_comp, hh, Representation.inv_self_apply]
        have hid := parabolic_eq_one_of_fixes_simple cs
          ((cs.parabolic L).mul_mem ((cs.parabolic L).inv_mem h.property) g.property) hfix
        exact (inv_mul_eq_one.mp hid).symm
      have finite_indices_of_spanning_set (L : Set S) (E : Set (S →₀ ℝ))
          (hE : E.Finite)
          (hspan : ∀ i ∈ L, Finsupp.single i (1 : ℝ) ∈ Submodule.span ℝ E) : L.Finite := by
        classical
        let F : Set S := ⋃ v ∈ E, (v.support : Set S)
        have hF : F.Finite := hE.biUnion fun v _ => v.support.finite_toSet
        apply hF.subset
        intro i hi
        by_contra hni
        have hz : ∀ v ∈ E, v i = 0 := by
          intro v hv
          by_contra hvn
          exact hni (Set.mem_iUnion.mpr ⟨v, Set.mem_iUnion.mpr
            ⟨hv, Finsupp.mem_support_iff.mpr hvn⟩⟩)
        have hker : Submodule.span ℝ E ≤ (Finsupp.lapply i : (S →₀ ℝ) →ₗ[ℝ] ℝ).ker :=
          Submodule.span_le.mpr hz
        have hh := hker (hspan i hi)
        change (Finsupp.single i (1 : ℝ)) i = 0 at hh
        simp at hh
      let orbitRoots (cs : CoxeterSystem M W) (L : Set S) : Set (S →₀ ℝ) :=
        {v | ∃ w ∈ cs.parabolic L, ∃ i ∈ L,
          cs.geometricRepresentation w (Finsupp.single i 1) = v}
      have orbitRoots_stable (cs : CoxeterSystem M W) (L : Set S)
          (w : W) (hw : w ∈ cs.parabolic L) (v : S →₀ ℝ)
          (hv : v ∈ orbitRoots cs L) : cs.geometricRepresentation w v ∈ orbitRoots cs L := by
        obtain ⟨u, hu, i, hi, rfl⟩ := hv
        exact ⟨w * u, (cs.parabolic L).mul_mem hw hu, i, hi, by rw [map_mul, mul_apply_eq_comp]⟩
      have rootDifference_stable (cs : CoxeterSystem M W) (I T : Set S) (hIT : I ⊆ T)
          (w : W) (hw : w ∈ cs.parabolic I) (v : S →₀ ℝ)
          (hv : v ∈ orbitRoots cs T \ orbitRoots cs I) :
          cs.geometricRepresentation w v ∈ orbitRoots cs T \ orbitRoots cs I := by
        refine ⟨orbitRoots_stable cs T w (cs.parabolic_mono hIT hw) v hv.1, ?_⟩
        intro hh
        have hi := orbitRoots_stable cs I w⁻¹ ((cs.parabolic I).inv_mem hw)
          (cs.geometricRepresentation w v) hh
        exact hv.2 (by simpa only [Representation.inv_self_apply] using hi)
      have finite_parabolic_of_finite_roots (cs : CoxeterSystem M W) (L : Set S)
          (hroots : (orbitRoots cs L).Finite) : Finite (cs.parabolic L) := by
        apply finite_parabolic_of_invariant_spanning_set cs L (orbitRoots cs L) hroots
        · exact orbitRoots_stable cs L
        · intro i hi
          apply Submodule.subset_span
          exact ⟨1, (cs.parabolic L).one_mem, i, hi, by simp⟩
      have finite_roots_of_finite_parabolic (cs : CoxeterSystem M W) (L : Set S)
          (hL : L.Finite) [Finite (cs.parabolic L)] : (orbitRoots cs L).Finite := by
        let : Finite L := hL.to_subtype
        let f : cs.parabolic L × L → (S →₀ ℝ) := fun p =>
          cs.geometricRepresentation p.1.val (Finsupp.single p.2.val 1)
        apply (Set.finite_range f).subset
        intro v hv
        obtain ⟨w, hw, i, hi, he⟩ := hv
        exact ⟨(⟨w, hw⟩, ⟨i, hi⟩), he⟩
      have spherical_support_of_span_and_split (cs : CoxeterSystem M W)
          (I D : Set S) (E : Set (S →₀ ℝ)) (hE : E.Finite)
          (hstable : ∀ w ∈ cs.parabolic I, ∀ v ∈ E, cs.geometricRepresentation w v ∈ E)
          (hspan : ∀ i ∈ D, Finsupp.single i (1 : ℝ) ∈ Submodule.span ℝ E)
          (hsplit : orbitRoots cs D ⊆ orbitRoots cs (D ∩ I) ∪ E) :
          Finite (cs.parabolic D) := by
        have hD := finite_indices_of_spanning_set D E hE hspan
        have hH : (D ∩ I).Finite := hD.subset Set.inter_subset_left
        let : Finite (cs.parabolic (D ∩ I)) :=
          finite_parabolic_of_invariant_spanning_set cs (D ∩ I) E hE
            (fun w hw => hstable w (cs.parabolic_mono Set.inter_subset_right hw))
            (fun i hi => hspan i hi.1)
        have hroots := finite_roots_of_finite_parabolic cs (D ∩ I) hH
        exact finite_parabolic_of_finite_roots cs D ((hroots.union hE).subset hsplit)
      have rootUnion (cs : CoxeterSystem M W) (D E : Set S)
          (hsep : ∀ i ∈ D, ∀ j ∈ E, M i j = 2) :
          let act := cs.geometricRepresentation
          let root : S → (S →₀ ℝ) := fun i => Finsupp.single i 1
          let roots : Set S → Set (S →₀ ℝ) := fun L =>
            {x | ∃ w : W, w ∈ cs.parabolic L ∧ ∃ i ∈ L, act w (root i) = x}
          roots (D ∪ E) = roots D ∪ roots E := by
        classical
        dsimp only
        let act := cs.geometricRepresentation
        let root : S → (S →₀ ℝ) := fun i => Finsupp.single i 1
        let roots : Set S → Set (S →₀ ℝ) := fun L =>
          {x | ∃ w : W, w ∈ cs.parabolic L ∧ ∃ i ∈ L, act w (root i) = x}
        change roots (D ∪ E) = roots D ∪ roots E
        have fix (L : Set S) (e : S) (he : ∀ i ∈ L, M i e = 2)
            (w : W) (hw : w ∈ cs.parabolic L) : act w (root e) = root e := by
          obtain ⟨v, hv, rfl⟩ := cs.exists_wordProd_eq_of_mem_parabolic hw
          clear hw
          induction v with
          | nil => simp [act]
          | cons i v ih =>
            rw [cs.wordProd_cons, map_mul, mul_apply_eq_comp,
              ih (fun j hj => hv j (by simp [hj])), cs.geometricRepresentation_simple]
            apply M.geometricReflection_apply_of_eq_zero
            dsimp only [root]
            rw [M.geometricForm_single_single, he i (hv i (by simp))]
            norm_num [Real.cos_pi_div_two]
        have commuteBlocks (L F : Set S) (h : ∀ i ∈ L, ∀ j ∈ F, M i j = 2)
            (u v : W) (hu : u ∈ cs.parabolic L) (hv : v ∈ cs.parabolic F) : Commute u v := by
          obtain ⟨a, ha, rfl⟩ := cs.exists_wordProd_eq_of_mem_parabolic hu
          obtain ⟨b, hb, rfl⟩ := cs.exists_wordProd_eq_of_mem_parabolic hv
          clear hu hv
          have single (i : S) (hi : i ∈ L) : Commute (cs.simple i) (cs.wordProd b) := by
            induction b with
            | nil => simp
            | cons j b ih =>
              rw [cs.wordProd_cons]
              exact (cs.commute_simple_of_eq_two (h i hi j (hb j (by simp)))).mul_right
                (ih (fun k hk => hb k (by simp [hk])))
          induction a with
          | nil => simp
          | cons i a ih =>
            rw [cs.wordProd_cons]
            exact (single i (ha i (by simp))).mul_left (ih (fun j hj => ha j (by simp [hj])))
        have factor (L F : Set S) (h : ∀ i ∈ L, ∀ j ∈ F, M i j = 2)
            (w : W) (hw : w ∈ cs.parabolic (L ∪ F)) :
            ∃ u ∈ cs.parabolic L, ∃ v ∈ cs.parabolic F, w = u * v := by
          obtain ⟨a, ha, rfl⟩ := cs.exists_wordProd_eq_of_mem_parabolic hw
          clear hw
          induction a with
          | nil => exact ⟨1, (cs.parabolic L).one_mem, 1, (cs.parabolic F).one_mem, by simp⟩
          | cons i a ih =>
            obtain ⟨u, hu, v, hv, hp⟩ := ih (fun j hj => ha j (by simp [hj]))
            rcases ha i (by simp) with hi | hi
            · refine ⟨cs.simple i * u, mul_mem (cs.simple_mem_parabolic hi) hu, v, hv, ?_⟩
              rw [cs.wordProd_cons, hp, mul_assoc]
            · refine ⟨u, hu, cs.simple i * v, mul_mem (cs.simple_mem_parabolic hi) hv, ?_⟩
              rw [cs.wordProd_cons, hp, ← mul_assoc,
                (commuteBlocks L F h u (cs.simple i) hu (cs.simple_mem_parabolic hi)).eq.symm, mul_assoc]
        have rootsMono {L F : Set S} (h : L ⊆ F) : roots L ⊆ roots F := by
          rintro x ⟨w, hw, i, hi, hx⟩
          exact ⟨w, cs.parabolic_mono h hw, i, h hi, hx⟩
        ext x
        constructor
        · rintro ⟨w, hw, i, hi, rfl⟩
          obtain ⟨u, hu, v, hv, rfl⟩ := factor D E hsep w hw
          rcases hi with hi | hi
          · left
            refine ⟨u, hu, i, hi, ?_⟩
            rw [map_mul, mul_apply_eq_comp,
              fix E i (fun j hj => (M.symmetric j i).trans (hsep i hi j hj)) v hv]
          · right
            refine ⟨v, hv, i, hi, ?_⟩
            rw [(commuteBlocks D E hsep u v hu hv).eq, map_mul, mul_apply_eq_comp,
              fix D i (fun j hj => hsep j hj i hi) u hu]
        · rintro (hx | hx)
          · exact rootsMono Set.subset_union_left hx
          · exact rootsMono Set.subset_union_right hx
      have outside (cs : CoxeterSystem M W) (L : Set S) (w : W)
          (hw : w ∈ cs.parabolic L) (k : S) (hk : k ∉ L) (x : S →₀ ℝ) :
          cs.geometricRepresentation w x k = x k := by
        obtain ⟨u, hu, rfl⟩ := cs.exists_wordProd_eq_of_mem_parabolic hw
        clear hw
        induction u with
        | nil => simp
        | cons i u ih =>
          have hki : k ≠ i := fun h => hk (h ▸ hu i (by simp))
          rw [cs.wordProd_cons, map_mul, mul_apply_eq_comp,
            cs.geometricRepresentation_simple, M.geometricReflection_apply_apply_of_ne hki]
          exact ih (fun j hj => hu j (by simp [hj]))
      have supported (cs : CoxeterSystem M W) (L : Set S)
          {x : S →₀ ℝ} (hx : x ∈ orbitRoots cs L) : ∀ k, k ∉ L → x k = 0 := by
        obtain ⟨w, hw, i, hi, rfl⟩ := hx
        intro k hk
        rw [outside cs L w hw k hk]
        simp [show i ≠ k from fun h => hk (h ▸ hi)]
      let componentSupport (M : CoxeterMatrix S) (I T : Set S) : Set S :=
        {i | i ∈ T ∧ ∃ c : S, c ∈ T ∧ c ∉ I ∧
          Relation.ReflTransGen (fun j k : S => j ∈ T ∧ k ∈ T ∧ j ≠ k ∧ M j k ≠ 2) c i}
      have edge_nonzero (M : CoxeterMatrix S) {i j : S} (hne : i ≠ j) (hm : M i j ≠ 2) :
          (2 * M.geometricForm (Finsupp.single i 1) (Finsupp.single j 1)) ≠ 0 := by
        rw [M.geometricForm_single_single]
        have hc : Real.cos (Real.pi / (M i j : ℝ)) ≠ 0 := by
          by_cases hz : M i j = 0
          · simp [hz]
          · have hn := M.off_diagonal i j hne
            have hgt : 2 < M i j := by omega
            have hreal : (2 : ℝ) < M i j := by exact_mod_cast hgt
            apply ne_of_gt
            apply Real.cos_pos_of_mem_Ioo
            constructor
            · have := div_pos Real.pi_pos (lt_trans (by norm_num : (0 : ℝ) < 2) hreal)
              have := Real.pi_pos
              linarith
            · exact div_lt_div_of_pos_left Real.pi_pos (by norm_num) hreal
        simpa only [one_mul] using mul_ne_zero (show (2 : ℝ) ≠ 0 by norm_num) (neg_ne_zero.mpr hc)
      -- Finite-relative-longest steps 1.1--2.1: propagate support from T\I.
      have support_span (cs : CoxeterSystem M W) (I T : Set S) (hIT : I ⊆ T) :
          ∀ i ∈ componentSupport M I T, Finsupp.single i (1 : ℝ) ∈
            Submodule.span ℝ (orbitRoots cs T \ orbitRoots cs I) := by
        classical
        let E := orbitRoots cs T \ orbitRoots cs I
        let U := Submodule.span ℝ E
        have seed (c : S) (hc : c ∈ T) (hci : c ∉ I) : Finsupp.single c (1 : ℝ) ∈ U := by
          apply Submodule.subset_span
          refine ⟨⟨1, (cs.parabolic T).one_mem, c, hc, by simp⟩, ?_⟩
          intro hh
          have := supported cs I hh c hci
          simp at this
        have stable (j : S) (hj : j ∈ I) : ∀ x ∈ U,
            cs.geometricRepresentation (cs.simple j) x ∈ U := by
          have hle : U ≤ U.comap (cs.geometricRepresentation (cs.simple j)) := by
            apply Submodule.span_le.mpr
            intro x hx
            exact Submodule.subset_span
              (rootDifference_stable cs I T hIT (cs.simple j) (cs.simple_mem_parabolic hj) x hx)
          exact fun x hx => hle hx
        intro i hi
        obtain ⟨hiT, c, hcT, hcI, hpath⟩ := hi
        have H : ∀ k : S,
            Relation.ReflTransGen (fun j k : S => j ∈ T ∧ k ∈ T ∧ j ≠ k ∧ M j k ≠ 2) c k →
            Finsupp.single k (1 : ℝ) ∈ U := by
          intro k hk
          induction hk with
          | refl => exact seed c hcT hcI
          | @tail j k hp he ih =>
            by_cases hkI : k ∈ I
            · have hs := U.sub_mem ih (stable k hkI _ ih)
              rw [cs.geometricRepresentation_simple, M.geometricReflection_apply] at hs
              have heq : Finsupp.single j (1 : ℝ) -
                  (Finsupp.single j 1 - (2 * M.geometricForm (Finsupp.single k 1)
                      (Finsupp.single j 1)) • Finsupp.single k 1) =
                  (2 * M.geometricForm (Finsupp.single k 1) (Finsupp.single j 1)) • Finsupp.single k 1 := by abel
              rw [heq] at hs
              exact (Submodule.smul_mem_iff U (edge_nonzero M he.2.2.1.symm
                (fun h => he.2.2.2 ((M.symmetric j k).trans h)))).mp hs
            · exact seed k he.2.1 hkI
        exact H i hpath
      have support_split (cs : CoxeterSystem M W) (I T : Set S) (hIT : I ⊆ T) :
          orbitRoots cs (componentSupport M I T) ⊆
            orbitRoots cs (componentSupport M I T ∩ I) ∪ (orbitRoots cs T \ orbitRoots cs I) := by
        classical
        let D := componentSupport M I T
        have hDT : D ⊆ T := fun _ hi => hi.1
        have sep : ∀ i ∈ D, ∀ j ∈ I \ D, M i j = 2 := by
          intro i hi j hj
          by_contra hm
          have hij : i ≠ j := fun h => hj.2 (h ▸ hi)
          obtain ⟨hiT, c, hcT, hcI, hp⟩ := hi
          exact hj.2 ⟨hIT hj.1, c, hcT, hcI,
            Relation.ReflTransGen.tail hp ⟨hiT, hIT hj.1, hij, hm⟩⟩
        have hI : I = (D ∩ I) ∪ (I \ D) := by
          ext i; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]; tauto
        have hrootI : orbitRoots cs I = orbitRoots cs (D ∩ I) ∪ orbitRoots cs (I \ D) := by
          conv_lhs => rw [hI]
          exact rootUnion cs (D ∩ I) (I \ D) (fun i hi j hj => sep i hi.1 j hj)
        intro x hx
        by_cases hxI : x ∈ orbitRoots cs I
        · rw [hrootI] at hxI
          rcases hxI with hh | hh
          · exact Or.inl hh
          · exfalso
            have hz : x = 0 := by
              ext k
              by_cases hk : k ∈ D
              · exact supported cs (I \ D) hh k (fun he => he.2 hk)
              · exact supported cs D hx k hk
            obtain ⟨u, hu, i, hi, hr⟩ := hx
            exact cs.ne_zero_of_mem_geometricRoots ⟨u, i, hr⟩ hz
        · right
          refine ⟨?_,hxI⟩
          obtain ⟨w,hw,i,hi,hr⟩ := hx
          exact ⟨w,cs.parabolic_mono hDT hw,i,hDT hi,hr⟩
      have finiteRootDifferenceSphericalSupport (cs : CoxeterSystem M W) (I T : Set S)
          (hIT : I ⊆ T) (hfinite : (orbitRoots cs T \ orbitRoots cs I).Finite) :
          Finite (cs.parabolic (componentSupport M I T)) := by
        exact spherical_support_of_span_and_split cs I (componentSupport M I T) _ hfinite
          (rootDifference_stable cs I T hIT) (support_span cs I T hIT) (support_split cs I T hIT)
      have positiveOutside (cs : CoxeterSystem M W) (L : Set S) (w : W)
          (hw : w ∈ cs.parabolic L) (x : S →₀ ℝ) (hx : x ∈ cs.geometricRoots)
          (hp : 0 < x) (hn : x ∉ orbitRoots cs L) : 0 < cs.geometricRepresentation w x := by
        obtain ⟨v,hv,rfl⟩ := cs.exists_wordProd_eq_of_mem_parabolic hw
        clear hw
        induction v generalizing x with
        | nil => simpa using hp
        | cons i v ih =>
          have hvL : ∀ j ∈ v, j ∈ L := fun j hj => hv j (by simp [hj])
          have hroot := (cs.geometricRepresentation_apply_mem_geometricRoots_iff (cs.wordProd v)).mpr hx
          have hnot : cs.geometricRepresentation (cs.wordProd v) x ∉ orbitRoots cs L := by
            intro hh
            have hi := orbitRoots_stable cs L (cs.wordProd v)⁻¹
              ((cs.parabolic L).inv_mem (cs.wordProd_mem_parabolic hvL)) _ hh
            exact hn (by simpa only [Representation.inv_self_apply] using hi)
          rw [cs.wordProd_cons, map_mul, mul_apply_eq_comp, cs.geometricRepresentation_simple]
          apply cs.geometricReflection_pos_of_mem_geometricRoots hroot (ih x hx hp hn hvL)
          intro he
          apply hnot
          rw [he]
          exact ⟨1, (cs.parabolic L).one_mem, i, hv i (by simp), by simp⟩
      have expand (x : S →₀ ℝ) : x = ∑ i ∈ x.support, x i • Finsupp.single i (1 : ℝ) := by
        ext k
        simp [Finsupp.single_apply, Finset.sum_ite_eq']
      have action_nonneg (g : W) (L : Set S)
          (hc : ∀ i ∈ L, 0 ≤ cs.geometricRepresentation g (Finsupp.single i 1))
          (x : S →₀ ℝ) (hp : 0 ≤ x) (hx : ∀ k, k ∉ L → x k = 0) :
          0 ≤ cs.geometricRepresentation g x := by
        rw [expand x, map_sum]
        intro k
        simp only [Finset.sum_apply', map_smul, Finsupp.smul_apply, Pi.smul_apply,
          smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply]
        apply Finset.sum_nonneg
        intro i hi
        have hiL : i ∈ L := by
          by_contra hn
          exact (Finsupp.mem_support_iff.mp hi) (hx i hn)
        exact mul_nonneg (hp i) (hc i hiL k)
      have positive_supported_root_mem_parabolic (L : Set S) (x : S →₀ ℝ)
          (hr : x ∈ cs.geometricRoots) (hp : 0 < x)
          (hs : ∀ k, k ∉ L → x k = 0) : x ∈ orbitRoots cs L := by
        by_contra hn
        obtain ⟨u, i, hu⟩ := hr
        let y := cs.simple i * u⁻¹
        have hy : cs.geometricRepresentation y x = -Finsupp.single i (1 : ℝ) := by
          rw [← hu]
          simp only [y, map_mul, mul_apply_eq_comp, Representation.inv_self_apply,
            cs.geometricRepresentation_simple, M.geometricReflection_apply_single_self]
        obtain ⟨v, hv, hmin⟩ := cs.exists_isMinimalCosetRep L y
        let z := cs.geometricRepresentation v⁻¹ x
        have hzpos : 0 < z := positiveOutside cs L v⁻¹ ((cs.parabolic L).inv_mem hv) x ⟨u, i, hu⟩ hp hn
        have hzs : ∀ k, k ∉ L → z k = 0 := by
          intro k hk
          rw [outside cs L v⁻¹ ((cs.parabolic L).inv_mem hv) k hk]
          exact hs k hk
        have hc : ∀ j ∈ L, 0 ≤ cs.geometricRepresentation (y * v) (Finsupp.single j 1) := by
          intro j hj
          exact ((cs.geometricRepresentation_single_pos_iff _ _).mpr
            (cs.isMinimalCosetRep_iff.mp hmin j hj)).le
        have hh := action_nonneg (y * v) L hc z hzpos.le hzs
        have he : cs.geometricRepresentation (y * v) z = -Finsupp.single i (1 : ℝ) := by
          dsimp only [z]
          rw [map_mul, mul_apply_eq_comp, Representation.self_inv_apply, hy]
        rw [he] at hh
        have hcoord := hh i
        norm_num at hcoord
      have finiteInv (cs : CoxeterSystem M W) (w : W) :
          Set.Finite {α | α ∈ cs.geometricRoots ∧ 0 < α ∧ cs.geometricRepresentation w α < 0} := by
        classical
        induction w using cs.simple_induction_right with
        | one =>
          have he : {α | α ∈ cs.geometricRoots ∧ 0 < α ∧ cs.geometricRepresentation (1 : W) α < 0} = ∅ := by
            ext α
            simp only [Set.mem_ofPred_eq, map_one, one_apply_eq_self, Set.mem_empty_iff_false, iff_false]
            rintro ⟨_, hp, hn⟩
            exact (lt_asymm hp hn)
          rw [he]
          exact Set.finite_empty
        | mul_simple_right w i ih =>
          apply ((ih.image (M.geometricReflection i)).union (Set.finite_singleton (Finsupp.single i 1))).subset
          intro α hα
          by_cases he : α = Finsupp.single i 1
          · exact Or.inr he
          · apply Or.inl
            refine ⟨M.geometricReflection i α, ⟨?_, ?_, ?_⟩, ?_⟩
            · exact (cs.geometricReflection_apply_mem_geometricRoots_iff i).mpr hα.1
            · exact cs.geometricReflection_pos_of_mem_geometricRoots hα.1 hα.2.1 he
            · simpa only [map_mul, mul_apply_eq_comp, cs.geometricRepresentation_simple] using hα.2.2
            · exact LinearMap.congr_fun (M.geometricReflection_mul_self i) α
      have orbitNeg (L : Set S) {β : S →₀ ℝ} (hβ : β ∈ orbitRoots cs L) :
          -β ∈ orbitRoots cs L := by
        obtain ⟨w, hw, i, hi, rfl⟩ := hβ
        refine ⟨w * cs.simple i, (cs.parabolic L).mul_mem hw (cs.simple_mem_parabolic hi), i, hi, ?_⟩
        simp only [map_mul, mul_apply_eq_comp, cs.geometricRepresentation_simple,
          M.geometricReflection_apply_single_self, map_neg]
      have evalSupported (I : Set S) (a : S) (f : Dual S)
          (hf : f ∈ relativeSubspace I)
          (β : S →₀ ℝ) (hβ : ∀ k, k ∉ Set.insert a I → β k = 0) :
          f β = β a * f (Finsupp.single a (1 : ℝ)) := by
        have hb : β = ∑ i ∈ β.support, β i • Finsupp.single i (1 : ℝ) := by
          ext k
          simp [Finsupp.single_apply, Finset.sum_ite_eq']
        conv_lhs => rw [hb, map_sum]
        simp only [map_smul, smul_eq_mul]
        by_cases ha : a ∈ β.support
        · apply Finset.sum_eq_single a
          · intro i hi hia
            have hiI : i ∈ I := by
              by_contra hn
              exact (Finsupp.mem_support_iff.mp hi) (hβ i (fun h => (Set.mem_insert_iff.mp h).elim hia hn))
            have hz : f (Finsupp.single i (1 : ℝ)) = 0 := hf i hiI
            rw [hz, mul_zero]
          · exact fun hn => False.elim (hn ha)
        · have hz : β a = 0 := Finsupp.notMem_support_iff.mp ha
          rw [hz, zero_mul]
          apply Finset.sum_eq_zero
          intro i hi
          have hiI : i ∈ I := by
            by_contra hn
            have hia : i ≠ a := fun h => ha (h ▸ hi)
            exact (Finsupp.mem_support_iff.mp hi) (hβ i (fun h => (Set.mem_insert_iff.mp h).elim hia hn))
          have hz : f (Finsupp.single i (1 : ℝ)) = 0 := hf i hiI
          rw [hz, mul_zero]
      have differenceFinite (I : Set S) (a : S) (ha : a ∉ I)
          (u : W) (f g : Dual S)
          (hf : f ∈ relativeSubspace I) (hfa : f (Finsupp.single a 1) < 0)
          (hg : IsDominant g) (he : ∀ β, f β = g (cs.geometricRepresentation u β)) :
          (orbitRoots cs (Set.insert a I) \ orbitRoots cs I).Finite := by
        let P : Set (S →₀ ℝ) := {β | β ∈ orbitRoots cs (Set.insert a I) ∧ β ∉ orbitRoots cs I ∧ 0 < β}
        have hP : P.Finite := (finiteInv cs u).subset (by
          intro β hβ
          have hr : β ∈ cs.geometricRoots := by
            obtain ⟨w, hw, i, hi, he⟩ := hβ.1
            exact ⟨w, i, he⟩
          have hpos : 0 < β a := by
            have hz : β a ≠ 0 := by
              intro hz
              apply hβ.2.1
              apply positive_supported_root_mem_parabolic I β hr hβ.2.2
              intro k hk
              by_cases hka : k = a
              · simpa [hka] using hz
              · exact supported cs (Set.insert a I) hβ.1 k (fun h => (Set.mem_insert_iff.mp h).elim hka hk)
            exact lt_of_le_of_ne (hβ.2.2.le a) (Ne.symm hz)
          have hval : f β < 0 := by
            rw [evalSupported I a f hf β (supported cs (Set.insert a I) hβ.1)]
            exact mul_neg_of_pos_of_neg hpos hfa
          refine ⟨hr, hβ.2.2, ?_⟩
          rcases cs.pos_or_neg_of_mem_geometricRoots
            ((cs.geometricRepresentation_apply_mem_geometricRoots_iff u).mpr hr) with hp | hn
          · exfalso
            have hh := evaluation_nonpos_of_nonpos hg (neg_nonpos.mpr hp.le)
            rw [map_neg, ← he β] at hh
            linarith
          · exact hn)
        apply (hP.union (hP.image (fun β => -β))).subset
        intro β hβ
        have hr : β ∈ cs.geometricRoots := by
          obtain ⟨w, hw, i, hi, he⟩ := hβ.1
          exact ⟨w, i, he⟩
        rcases cs.pos_or_neg_of_mem_geometricRoots hr with hp | hn
        · exact Or.inl ⟨hβ.1, hβ.2, hp⟩
        · apply Or.inr
          refine ⟨-β, ⟨orbitNeg _ hβ.1, ?_, neg_pos.mpr hn⟩, neg_neg β⟩
          intro hh
          exact hβ.2 (by simpa only [neg_neg] using orbitNeg I hh)
      have singleSpherical (I : Set S) (a : S) (ha : a ∉ I)
          (hfin : (orbitRoots cs (Set.insert a I) \ orbitRoots cs I).Finite) :
          Finite (cs.parabolic {b | b ∈ Set.insert a I ∧ Relation.ReflTransGen
            (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b}) := by
        have hh := finiteRootDifferenceSphericalSupport cs I (Set.insert a I) (Set.subset_insert a I) hfin
        have he : componentSupport M I (Set.insert a I) =
            {b | b ∈ Set.insert a I ∧ Relation.ReflTransGen
            (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b} := by
          ext b
          constructor
          · rintro ⟨hb, c, hc, hcI, hp⟩
            have hca : c = a := (Set.mem_insert_iff.mp hc).resolve_right hcI
            exact ⟨hb, hca ▸ hp⟩
          · rintro ⟨hb, hp⟩
            exact ⟨hb, a, Set.mem_insert a I, ha, hp⟩
        rw [he] at hh
        exact hh
      have nonnegClosure (I : Set S) (f : relativeSubspace I)
          (hf : ∀ i, i ∉ I → 0 ≤ dualCoordinates f.val i) :
          f ∈ closure {q : relativeSubspace I | q.val ∈ standardFacet M I} := by
        letI : IsTopologicalAddGroup (Dual S) := dualTopologicalAddGroup
        letI : ContinuousSMul ℝ (Dual S) := dualContinuousSMul
        let d : relativeSubspace I := ⟨canonicalDominant I, canonicalDominant_mem_relativeSubspace I⟩
        let γ : ℝ → relativeSubspace I := fun t => f + t • d
        have hc : Continuous γ :=
          (show Continuous (fun t : ℝ => f.val + t • d.val) from
            continuous_const.add (continuous_id.smul continuous_const)).subtype_mk _
        have ht : Filter.Tendsto γ (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds f) := by
          have h := hc.continuousAt.tendsto.mono_left
            (show nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
          simpa only [γ, zero_smul, add_zero] using h
        apply mem_closure_of_tendsto ht
        filter_upwards [self_mem_nhdsWithin] with t ht
        refine ⟨(γ t).property, ?_⟩
        intro i hi
        change 0 < f.val (simpleRoot i) + t * (canonicalDominant I) (simpleRoot i)
        rw [canonicalDominant_apply_simpleRoot]
        simp only [if_neg hi, mul_one]
        exact add_pos_of_nonneg_of_pos (hf i hi) ht
      have htop : TopologicalSpace.induced
          (fun f : relativeSubspace J => dualCoordinates f.val)
          (inferInstance : TopologicalSpace (S → ℝ)) =
          (inferInstance : TopologicalSpace (relativeSubspace J)) := induced_compose.symm
      dsimp only
      intro x y I K hx hy F hne hwallx hwally a ha hF
      rw [htop] at hwallx hwally hF
      let Θ := relativeSubspace J
      let R : W → Set S → Set Θ := fun w L =>
        {p | ∃ g, g ∈ standardFacet M L ∧ dualAction M w g = p.val}
      change R x I ≠ R y K at hne
      change F = closure (R x (Set.insert a I)) at hF
      have hcoset (x : W) (I : Set S) :
          Set.image (fun u : W => u * x) (cs.parabolic J : Set W) =
            Set.image (fun u : W => x * u) (cs.parabolic I : Set W) ↔
          (coxeterParabolic M I).map (MulAut.conj x).toMonoidHom = coxeterParabolic M J := by
        constructor
        · intro h
          ext v
          constructor
          · rintro ⟨u, hu, huv⟩
            change x * u * x⁻¹ = v at huv
            have hm : x * u ∈ Set.image (fun t : W => t * x) (cs.parabolic J : Set W) :=
              h.symm ▸ Set.mem_image_of_mem (fun t : W => x * t) hu
            obtain ⟨t, ht, he⟩ := hm
            have hev : t = v := by rw [← huv, ← he]; group
            exact hev ▸ ht
          · intro hv
            have hm : v * x ∈ Set.image (fun t : W => x * t) (cs.parabolic I : Set W) :=
              h ▸ Set.mem_image_of_mem (fun t : W => t * x) hv
            obtain ⟨t, ht, he⟩ := hm
            refine ⟨t, ht, ?_⟩
            change x * t = v * x at he
            change x * t * x⁻¹ = v
            rw [he]
            group
        · intro h
          apply Set.Subset.antisymm
          · rintro _ ⟨v, hv, rfl⟩
            change v ∈ coxeterParabolic M J at hv
            rw [← h, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hv
            refine ⟨x⁻¹ * v * x, hv, ?_⟩
            group
          · rintro _ ⟨v, hv, rfl⟩
            have hm : x * v * x⁻¹ ∈ coxeterParabolic M J := by
              rw [← h]
              exact ⟨v, hv, rfl⟩
            refine ⟨x * v * x⁻¹, hm, ?_⟩
            group
      let Lx : RawFacetLabel M J := ⟨I, x, (hcoset x I).mp hx.1⟩
      let Ly : RawFacetLabel M J := ⟨K, y, (hcoset y K).mp hy.1⟩
      let e := facetFlatEquiv Lx
      have hRx : R x I = translatedFacet Lx := by ext p; exact (mem_translatedFacet_iff Lx p).symm
      have hRy : R y K = translatedFacet Ly := by ext p; exact (mem_translatedFacet_iff Ly p).symm
      let d : relativeSubspace I :=
        ⟨canonicalDominant (Set.insert a I), fun i hi =>
          canonicalDominant_mem_relativeSubspace (Set.insert a I) i (Set.mem_insert_of_mem a hi)⟩
      let p : Θ := e d
      have hpR : p ∈ R x (Set.insert a I) := by
        exact ⟨d.val, canonicalDominant_mem_standardFacet M (Set.insert a I), rfl⟩
      have hpF : p ∈ F := hF ▸ subset_closure hpR
      have hpY : p ∈ closure (R y K) := by
        obtain ⟨H, hH, hF', hdim⟩ := hwally.2
        rw [hF'] at hpF
        exact hpF.1
      let G : Set Θ := {q | ∀ i : S, i ∉ Set.insert a I → 0 < dualCoordinates (e.symm q).val i}
      have hG : IsOpen G := by
        simp only [G, Set.setOf_forall]
        apply isOpen_iInter_of_finite
        intro i
        apply isOpen_iInter_of_finite
        intro hi
        exact isOpen_lt continuous_const
          ((continuous_evaluation (simpleRoot i)).comp (continuous_subtype_val.comp e.symm.continuous))
      have hpg : p ∈ G := by
        intro i hi
        change 0 < dualCoordinates (e.symm (e d)).val i
        rw [e.symm_apply_apply]
        change 0 < (canonicalDominant (Set.insert a I)) (simpleRoot i)
        rw [canonicalDominant_apply_simpleRoot]
        simp [hi]
      obtain ⟨q, hqG, hqY⟩ := mem_closure_iff.mp hpY G hG hpg
      have hqa : dualCoordinates (e.symm q).val a < 0 := by
        by_contra hn
        have hqnonneg : ∀ i, i ∉ I → 0 ≤ dualCoordinates (e.symm q).val i := by
          intro i hi
          by_cases he : i = a
          · simpa [he] using le_of_not_gt hn
          · exact (hqG i (fun h => (Set.mem_insert_iff.mp h).elim he hi)).le
        have hc := nonnegClosure I (e.symm q) hqnonneg
        have hqX : q ∈ closure (R x I) := by
          rw [hRx, translatedFacet]
          rw [← e.image_closure]
          exact ⟨e.symm q, hc, e.apply_symm_apply q⟩
        have ho : IsOpen (R y K) := hRy ▸ isOpen_translatedFacet Ly
        obtain ⟨r, hrY, hrX⟩ := mem_closure_iff.mp hqX (R y K) ho hqY
        apply hne
        rw [hRx, hRy]
        exact translatedFacet_eq_of_intersection Lx Ly ⟨r, hRx ▸ hrX, hRy ▸ hrY⟩
      obtain ⟨g, hg, heq⟩ := hqY
      apply singleSpherical I a ha
      apply differenceFinite I a ha (y⁻¹ * x) (e.symm q).val g (e.symm q).property hqa
        (standardFacet_isDominant M hg)
      intro β
      change (dualAction M x⁻¹ q.val) β = g (cs.geometricRepresentation (y⁻¹ * x) β)
      rw [← heq]
      change g (cs.geometricRepresentation y⁻¹ (cs.geometricRepresentation (x⁻¹)⁻¹ β)) = _
      rw [inv_inv, map_mul, mul_apply_eq_comp]
  classical
  let W := M.Group
  let cs := M.toCoxeterSystem
  let component : Set S → S → Set S := fun I a =>
    { b | b ∈ Set.insert a I ∧ Relation.ReflTransGen
      (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b }
  dsimp only
  intro x y I K hx hy F hne hwallx hwally
  -- Parent step 1.1: the specified wall determines the indices and spherical components.
  obtain ⟨a, a', ha, ha', hFx, hFy, hux, huy, hL⟩ :=
    RelativeCommonWall M J x y I K hx hy F hne hwallx hwally
  have hD : Finite (parabolic cs (component I a)) :=
    AdjacentSphericalComponent M J x y I K hx hy F hne hwallx hwally a ha hFx
  have hD' : Finite (parabolic cs (component K a')) :=
    AdjacentSphericalComponent M J y x K I hy hx F hne.symm hwally hwallx a' ha' hFy
  let forward := SimpleWallCrossings S W M cs I a ha hD
  let reverse := SimpleWallCrossings S W M cs K a' ha' hD'
  -- Parent step 2.1: recognize each specified opposite chamber using actual choices.
  have hforward := FiniteComponentOppositeChamber M J x I hx a ha hD
  have hreverse := FiniteComponentOppositeChamber M J y K hy a' ha' hD'
  have hxy : forward.2.2 x = (y, K) := hforward.2.2 y K hy F hne hwallx hwally hFx
  have hyx : reverse.2.2 y = (x, I) := hreverse.2.2 x I hx F hne.symm hwally hwallx hFy
  have htarget : forward.2.1 = K := congrArg Prod.snd hxy
  have htarget' : reverse.2.1 = I := congrArg Prod.snd hyx
  obtain ⟨b, hbD, hb, hKb, hFb⟩ := hforward.2.1
  have ha'L : a' ∈ Set.insert a I := by rw [hL]; exact Set.mem_insert a' K
  have ha'b : a' = b := by
    by_contra h
    apply ha'
    rw [← htarget, hKb]
    exact ⟨ha'L, by simpa only [Set.mem_singleton_iff] using h⟩
  have ha'D : a' ∈ component I a := by rw [ha'b]; exact hbD
  have hK : K = Set.insert a I \ {a'} := by rw [← htarget, hKb, ha'b]
  obtain ⟨c, hcD, hc, hIc, hFc⟩ := hreverse.2.1
  have haL : a ∈ Set.insert a' K := by rw [← hL]; exact Set.mem_insert a I
  have hac : a = c := by
    by_contra h
    apply ha
    rw [← htarget', hIc]
    exact ⟨haL, by simpa only [Set.mem_singleton_iff] using h⟩
  have hI : I = Set.insert a' K \ {a} := by rw [← htarget', hIc, hac]
  -- Parent step 3.1: reverse paths identify components; cancellation proves both inverses.
  have hcomp : component I a = component K a' := by
    let R : S → S → Prop := fun i j =>
      i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2
    have symR : ∀ i j, R i j → R j i := by
      intro i j hij
      exact ⟨hij.2.1, hij.1, hij.2.2.1.symm, by rw [M.symmetric]; exact hij.2.2.2⟩
    have reversePath : ∀ {i j}, Relation.ReflTransGen R i j → Relation.ReflTransGen R j i := by
      intro i j p
      induction p with
      | refl => exact Relation.ReflTransGen.refl
      | @tail j k p hjk ih => exact Relation.ReflTransGen.head (symR j k hjk) ih
    have pa : Relation.ReflTransGen R a a' := ha'D.2
    have pb : Relation.ReflTransGen R a' a := reversePath pa
    have hrel : (fun i j : S => i ∈ Set.insert a' K ∧ j ∈ Set.insert a' K ∧
        i ≠ j ∧ M i j ≠ 2) = R := by
      dsimp [R]
      rw [hL]
    apply Set.ext
    intro d
    change (d ∈ Set.insert a I ∧ Relation.ReflTransGen R a d) ↔
      (d ∈ Set.insert a' K ∧ Relation.ReflTransGen _ a' d)
    rw [hrel, ← hL]
    exact ⟨fun hd => ⟨hd.1, pb.trans hd.2⟩, fun hd => ⟨hd.1, pa.trans hd.2⟩⟩
  have hparabolic : parabolic cs (component I a) = parabolic cs (component K a') :=
    congrArg (parabolic cs) hcomp
  have hfirst : x * forward.1 = y := congrArg Prod.fst hxy
  have hsecond : y * reverse.1 = x := congrArg Prod.fst hyx
  have hprod : forward.1 * reverse.1 = (1 : W) := by
    apply mul_left_cancel (a := x)
    calc
      x * (forward.1 * reverse.1) = (x * forward.1) * reverse.1 := (mul_assoc _ _ _).symm
      _ = x := by rw [hfirst, hsecond]
      _ = x * 1 := (mul_one x).symm
  have hprod' : reverse.1 * forward.1 = (1 : W) := by
    apply mul_left_cancel (a := y)
    calc
      y * (reverse.1 * forward.1) = (y * reverse.1) * forward.1 := (mul_assoc _ _ _).symm
      _ = y := by rw [hsecond, hfirst]
      _ = y * 1 := (mul_one y).symm
  exact ⟨a, a', ha, ha', hFx, hFy, hux, huy, hL, hcomp, hparabolic,
    hD, hD', hxy, hyx, hK, hI, hprod, hprod'⟩)
