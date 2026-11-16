import Mathlib
import ArtinDeligne
import Proofs.BrinkHowlettGroupoid

theorem FiniteRelativeLongest : (∀ {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (I : Set S) (a b : S), a ∉ I → b ∉ I → a ≠ b → let T : Set S := Set.insert a (Set.insert b I); let parabolicRoots : Set S → Set (Finsupp S Real) := fun L => {α | ∃ w : W, w ∈ CoxeterSystem.parabolic cs L ∧ ∃ i : S, i ∈ L ∧ CoxeterSystem.geometricRepresentation cs w (Finsupp.single i (1 : Real)) = α}; let simpleRoots : Set S → Set (Finsupp S Real) := fun L => Set.image (fun i : S => Finsupp.single i (1 : Real)) L; let positiveRoots : Set (Finsupp S Real) := {α | α ∈ CoxeterSystem.geometricRoots cs ∧ 0 < α}; let negativeRoots : Set (Finsupp S Real) := {α | α ∈ CoxeterSystem.geometricRoots cs ∧ α < 0}; let D : Set S := {i | i ∈ T ∧ (Relation.ReflTransGen (fun j k : S => j ∈ T ∧ k ∈ T ∧ j ≠ k ∧ M j k ≠ 2) a i ∨ Relation.ReflTransGen (fun j k : S => j ∈ T ∧ k ∈ T ∧ j ≠ k ∧ M j k ≠ 2) b i)}; Set.Finite (parabolicRoots T \ parabolicRoots I) → Finite (CoxeterSystem.parabolic cs D) ∧ ∃ wD : CoxeterSystem.parabolic cs D, ∃ wDI : CoxeterSystem.parabolic cs (D ∩ I), (∀ u : CoxeterSystem.parabolic cs D, CoxeterSystem.length cs (u : W) ≤ CoxeterSystem.length cs (wD : W)) ∧ (∀ u : CoxeterSystem.parabolic cs (D ∩ I), CoxeterSystem.length cs (u : W) ≤ CoxeterSystem.length cs (wDI : W)) ∧ (let r : W := (wD : W) * (wDI : W); let q : W := r⁻¹; ∃ K : Set S, K ⊆ T ∧ (∃ g : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (CoxeterSystem.parabolic cs K) = CoxeterSystem.parabolic cs I) ∧ Set.image (CoxeterSystem.geometricRepresentation cs r) (simpleRoots I) = simpleRoots K ∧ Set.image (CoxeterSystem.geometricRepresentation cs q) (simpleRoots K) = simpleRoots I ∧ positiveRoots ∩ Set.image (CoxeterSystem.geometricRepresentation cs q) negativeRoots = (parabolicRoots T ∩ positiveRoots) \ (parabolicRoots I ∩ positiveRoots))) :=
(by
  /- FiniteRelativeLongest is a portal helper, not a standalone article lemma.
     Parent: Lemma 4.15/(4.16), Remark 4.17, printed p.19,
     https://arxiv.org/pdf/2509.21915#page=19.
     Numbered inspiration: steps 1.1, 2.1, 3.1 of
     https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-author-a7d202611130-finite-relative-longest.
     Necessary departure: prove spherical support by a faithful finite root action,
     rather than assume the portal's mathematical external input as a Lean theorem.
     Then prove opposition for arbitrary ambient-length maxima, positivity outside
     parabolic roots, disconnected extension and inverse transport in local blocks.
     Matrix entry 0 remains an edge. No ambient rank or type restriction is added.

     Reused completed helper advice and the executable fragments preserved in
     proof-helper-1-21aa3735-f7c2-4500-9847-8df7f3c9bf0d.json,
     proof-main-34b8b608-3d02-4feb-a0a2-57909a0df743.json and
     proof-helper-3-c3019c31-3b32-4685-a572-a2fcfdeac994.json.
     The subsequently reported complete temporary artifacts TtbYBr and JQG3so
     are absent; the missing implementations were reconstructed here and checked,
     never treated as imported declarations. Reused the supplied investigations'
     bounded GitHub searches. Fresh reading covers the portal helper and article
     p.19 context, actual providers and the relevant defect finding; no fresh
     full-article, bibliography or transitive-source reading is claimed.
     Existing providers are unchanged between requested project revision
     8668c70d25e6c5d63c313bac756052f9c83ee7f0 and observed HEAD
     1bdd7a76d6447fe84bc46aab09120f20292bf334. -/
  classical
  intro S W inst M cs I a b ha hb hab
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
      (hv : v ∈ orbitRoots cs L) :
      cs.geometricRepresentation w v ∈ orbitRoots cs L := by
    obtain ⟨u, hu, i, hi, rfl⟩ := hv
    exact ⟨w * u, (cs.parabolic L).mul_mem hw hu, i, hi,
      by rw [map_mul, mul_apply_eq_comp]⟩

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
        simp [root, M.geometricForm_single_single, he i (hv i (by simp)), Real.cos_pi_div_two]
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
        exact (single i (ha i (by simp))).mul_left
          (ih (fun j hj => ha j (by simp [hj])))
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
            (commuteBlocks L F h u (cs.simple i) hu (cs.simple_mem_parabolic hi)).eq.symm,
            mul_assoc]
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

  -- Portal steps 1.1--2.1: extend the one-seed span argument to all T\I.
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
            (by simpa only [M.symmetric k j] using he.2.2.2))).mp hs
        · exact seed k he.2.1 hkI
    exact H i hpath

  -- Orbit roots of disconnected blocks split, and their supports are disjoint.
  have support_split (cs : CoxeterSystem M W) (I T : Set S) (hIT : I ⊆ T) :
      orbitRoots cs (componentSupport M I T) ⊆
        orbitRoots cs (componentSupport M I T ∩ I) ∪
          (orbitRoots cs T \ orbitRoots cs I) := by
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
    have hI : I = (D ∩ I) ∪ (I \ D) := by ext i; simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]; tauto
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
      (rootDifference_stable cs I T hIT) (support_span cs I T hIT)
      (support_split cs I T hIT)

  have oppositionWork (cs : CoxeterSystem M W) (L : Set S) (z : cs.parabolic L)
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
  have opposition_target (cs : CoxeterSystem M W) (I D : Set S)
      (wD : cs.parabolic D) (wJ : cs.parabolic (D ∩ I))
      (opD : D ≃ D) (opJ : ↥(D ∩ I) ≃ ↥(D ∩ I))
      (hD : ∀ i : D, cs.geometricRepresentation (wD : W) (Finsupp.single (i : S) 1) =
        -Finsupp.single (opD i : S) 1)
      (hJ : ∀ i : ↥(D ∩ I), cs.geometricRepresentation (wJ : W) (Finsupp.single (i : S) 1) =
        -Finsupp.single (opJ i : S) 1) :
      let r : W := (wD : W) * (wJ : W)
      let KD : Set S := (fun i : D => (opD i : S)) '' {i : D | (i : S) ∈ I}
      r ∈ cs.parabolic D ∧ KD ⊆ D ∧
        cs.geometricRepresentation r '' ((fun i : S => Finsupp.single i (1 : ℝ)) '' (D ∩ I)) =
          (fun i : S => Finsupp.single i (1 : ℝ)) '' KD := by
    classical
    dsimp only
    refine ⟨mul_mem wD.property (cs.parabolic_mono Set.inter_subset_left wJ.property), ?_, ?_⟩
    · rintro k ⟨i, hi, rfl⟩
      exact (opD i).property
    · ext x
      constructor
      · rintro ⟨y, ⟨i, hi, rfl⟩, rfl⟩
        let j : ↥(D ∩ I) := ⟨i, hi⟩
        let k : D := ⟨(opJ j : S), (opJ j).property.1⟩
        refine ⟨(opD k : S), ⟨k, (opJ j).property.2, rfl⟩, ?_⟩
        rw [map_mul, mul_apply_eq_comp, hJ j, map_neg, hD k, neg_neg]
      · rintro ⟨k, ⟨j, hj, rfl⟩, rfl⟩
        let jI : ↥(D ∩ I) := ⟨(j : S), j.property, hj⟩
        let i := opJ.symm jI
        refine ⟨Finsupp.single (i : S) 1, ⟨(i : S), i.property, rfl⟩, ?_⟩
        rw [map_mul, mul_apply_eq_comp, hJ i, map_neg]
        have he : (opJ i : S) = (j : S) := congrArg Subtype.val (opJ.apply_symm_apply jI)
        rw [he, hD j, neg_neg]

  have root_conjugacy (cs : CoxeterSystem M W) (g : W) (L F : Set S)
      (ht : cs.geometricRepresentation g ''
        ((fun i : S => Finsupp.single i (1 : ℝ)) '' L) =
        (fun i : S => Finsupp.single i (1 : ℝ)) '' F) :
      (cs.parabolic L).map (MulAut.conj g).toMonoidHom = cs.parabolic F := by
    classical
    let act := cs.geometricRepresentation
    let root : S → (S →₀ ℝ) := fun i => Finsupp.single i 1
    have reflect (g : W) (i k : S) (h : act g (root i) = root k) :
        g * cs.simple i * g⁻¹ = cs.simple k := by
      apply cs.geometricRepresentation_injective
      apply LinearMap.ext
      intro x
      have form : M.geometricForm (root i) (act g⁻¹ x) = M.geometricForm (root k) x := by
        calc
          _ = M.geometricForm (act g (root i)) (act g (act g⁻¹ x)) :=
            (cs.geometricForm_geometricRepresentation g (root i) (act g⁻¹ x)).symm
          _ = _ := by rw [h, Representation.self_inv_apply]
      change act (g * cs.simple i * g⁻¹) x = act (cs.simple k) x
      dsimp only [act, root] at h form ⊢
      simp only [map_mul, mul_apply_eq_comp, cs.geometricRepresentation_simple,
        M.geometricReflection_apply, map_sub, map_smul]
      rw [form, h, Representation.self_inv_apply]
    have genImage : (MulAut.conj g).toMonoidHom '' (cs.simple '' L) = cs.simple '' F := by
      ext y
      constructor
      · rintro ⟨z, ⟨i, hi, rfl⟩, rfl⟩
        have hm : act g (root i) ∈ root '' F := ht ▸ Set.mem_image_of_mem _ (Set.mem_image_of_mem _ hi)
        obtain ⟨k, hk, he⟩ := hm
        exact ⟨k, hk, (reflect g i k he.symm).symm⟩
      · rintro ⟨k, hk, rfl⟩
        have hm : root k ∈ act g '' (root '' L) := ht.symm ▸ Set.mem_image_of_mem _ hk
        obtain ⟨x, ⟨i, hi, rfl⟩, he⟩ := hm
        exact ⟨cs.simple i, ⟨i, hi, rfl⟩, reflect g i k he⟩
    simp only [CoxeterSystem.parabolic, MonoidHom.map_closure, genImage]

  -- Root positivity outside a parabolic orbit set is preserved by that parabolic.
  have positiveOutside (cs : CoxeterSystem M W) (L : Set S) (w : W)
      (hw : w ∈ cs.parabolic L) (x : S →₀ ℝ) (hx : x ∈ cs.geometricRoots)
      (hp : 0 < x) (hn : x ∉ orbitRoots cs L) :
      0 < cs.geometricRepresentation w x := by
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

  -- A maximum negates every positive orbit root; only finite supports are summed.
  have longest_neg (cs : CoxeterSystem M W) (L : Set S) (z : cs.parabolic L)
      (hz : ∀ u : cs.parabolic L, cs.length (u : W) ≤ cs.length (z : W))
      (x : S →₀ ℝ) (hx : x ∈ orbitRoots cs L) (hp : 0 < x) :
      cs.geometricRepresentation (z : W) x < 0 := by
    classical
    obtain ⟨zz,e,he,heq,hgen⟩ := oppositionWork cs L z hz
    have hcol (i : S) (hi : i ∈ L) :
        cs.geometricRepresentation (z : W) (Finsupp.single i 1) ≤ 0 := by
      rw [heq ⟨i,hi⟩]
      exact neg_nonpos.mpr (Finsupp.single_nonneg.mpr (by norm_num))
    have hn : cs.geometricRepresentation (z : W) x ≤ 0 := by
      have hex : x = ∑ i ∈ x.support, x i • Finsupp.single i (1 : ℝ) := by
        ext k
        simp [Finsupp.single_apply, Finset.sum_ite_eq']
      rw [hex,map_sum]
      intro k
      simp only [Finset.sum_apply',map_smul,Finsupp.smul_apply,Pi.smul_apply,
        smul_eq_mul,Finsupp.coe_zero,Pi.zero_apply]
      apply Finset.sum_nonpos
      intro i hi
      have hiL : i ∈ L := by
        by_contra hn
        exact (Finsupp.mem_support_iff.mp hi) (supported cs L hx i hn)
      exact mul_nonpos_of_nonneg_of_nonpos (hp.le i) (hcol i hiL k)
    apply lt_of_le_of_ne hn
    apply cs.ne_zero_of_mem_geometricRoots
    apply (cs.geometricRepresentation_apply_mem_geometricRoots_iff (z : W)).mpr
    obtain ⟨u,hu,i,hi,he⟩ := hx
    exact ⟨u,i,he⟩

  -- These two image identities follow by cancelling inverse representation maps.
  have SphericalSupportRelativeLongest (cs : CoxeterSystem M W) (I T D : Set S)
      (hIT : I ⊆ T) (hDT : D ⊆ T) (hrest : T \ D ⊆ I)
      (hsep : ∀ i ∈ D, ∀ j ∈ T \ D, M i j = 2)
      (hD : Finite (cs.parabolic D))
      (wD : cs.parabolic D) (wJ : cs.parabolic (D ∩ I))
      (hwD : ∀ u : cs.parabolic D, cs.length (u : W) ≤ cs.length (wD : W))
      (hwJ : ∀ u : cs.parabolic (D ∩ I), cs.length (u : W) ≤ cs.length (wJ : W)) :
      let P := orbitRoots cs
      let piRoots : Set S → Set (S →₀ ℝ) := fun L => (fun i : S => Finsupp.single i (1 : ℝ)) '' L
      let Φp : Set (S →₀ ℝ) := {x | x ∈ cs.geometricRoots ∧ 0 < x}
      let Φn : Set (S →₀ ℝ) := {x | x ∈ cs.geometricRoots ∧ x < 0}
      let r : W := (wD : W) * (wJ : W)
      ∃ K : Set S, K ⊆ T ∧
        (cs.parabolic I).map (MulAut.conj r).toMonoidHom = cs.parabolic K ∧
        cs.geometricRepresentation r '' piRoots I = piRoots K ∧
        Φp ∩ cs.geometricRepresentation r⁻¹ '' Φn =
          (P T ∩ Φp) \ (P I ∩ Φp) := by
    classical
    dsimp only
    let act := cs.geometricRepresentation
    let E := T \ D
    let J := D ∩ I
    let r : W := (wD : W) * (wJ : W)
    let piRoots : Set S → Set (S →₀ ℝ) := fun L => (fun i : S => Finsupp.single i (1 : ℝ)) '' L
    have ht : T = D ∪ E := by ext i; dsimp [E]; simp only [Set.mem_union,Set.mem_sdiff]; exact ⟨fun hi => by by_cases h : i ∈ D <;> tauto,fun h => h.elim (fun hd => hDT hd) And.left⟩
    have hi : I = J ∪ E := by
      ext i
      change i ∈ I ↔ (i ∈ D ∧ i ∈ I) ∨ (i ∈ T ∧ i ∉ D)
      constructor
      · intro hh; by_cases hd : i ∈ D
        · exact Or.inl ⟨hd,hh⟩
        · exact Or.inr ⟨hIT hh,hd⟩
      · intro hh; exact hh.elim And.right (fun h => hrest h)
    have splitT : orbitRoots cs T = orbitRoots cs D ∪ orbitRoots cs E := by
      rw [ht]; exact rootUnion cs D E hsep
    have splitI : orbitRoots cs I = orbitRoots cs J ∪ orbitRoots cs E := by
      rw [hi]; exact rootUnion cs J E (fun i hi j hj => hsep i hi.1 j hj)
    have disjoint : Disjoint (orbitRoots cs D) (orbitRoots cs E) := by
      apply Set.disjoint_left.mpr
      intro x hx hy
      have hz : x = 0 := by
        ext k
        by_cases hk : k ∈ D
        · exact supported cs E hy k (fun hh => hh.2 hk)
        · exact supported cs D hx k hk
      obtain ⟨u,hu,i,hi,he⟩ := hx
      exact cs.ne_zero_of_mem_geometricRoots ⟨u,i,he⟩ hz
    have diff (x : S →₀ ℝ) :
        (x ∈ orbitRoots cs T ∧ x ∉ orbitRoots cs I) ↔
        (x ∈ orbitRoots cs D ∧ x ∉ orbitRoots cs J) := by
      rw [splitT,splitI]
      have hJD : orbitRoots cs J ⊆ orbitRoots cs D := by
        rintro y ⟨u,hu,i,hi,he⟩
        exact ⟨u,cs.parabolic_mono Set.inter_subset_left hu,i,hi.1,he⟩
      have hd := Set.disjoint_left.mp disjoint
      simp only [Set.mem_union]
      constructor
      · rintro ⟨hx,hni⟩
        rcases hx with hx | hx
        · exact ⟨hx,fun h => hni (Or.inl h)⟩
        · exact False.elim (hni (Or.inr hx))
      · rintro ⟨hx,hn⟩
        exact ⟨Or.inl hx,fun h => h.elim hn (hd hx)⟩
    obtain ⟨zzD,opD,hopD,hrootD,hgenD⟩ := oppositionWork cs D wD hwD
    obtain ⟨zzJ,opJ,hopJ,hrootJ,hgenJ⟩ := oppositionWork cs J wJ hwJ
    obtain ⟨hr,hKD,htransport⟩ := opposition_target cs I D wD wJ opD opJ hrootD hrootJ
    let KD : Set S := (fun i : D => (opD i : S)) '' {i : D | (i : S) ∈ I}
    let K := KD ∪ E
    have hKT : K ⊆ T := fun i hi => hi.elim (fun h => hDT (hKD h)) And.left
    have fixedE : act r '' piRoots E = piRoots E := by
      have fix (e : S) (he : e ∈ E) : act r (Finsupp.single e 1) = Finsupp.single e 1 := by
        obtain ⟨v,hv,heq⟩ := cs.exists_wordProd_eq_of_mem_parabolic hr
        change act ((wD : W) * (wJ : W)) (Finsupp.single e 1) = Finsupp.single e 1
        rw [← heq]
        clear heq
        induction v with
        | nil => simp [act]
        | cons i v ih =>
          rw [cs.wordProd_cons,map_mul,mul_apply_eq_comp,ih (fun j hj => hv j (by simp [hj])),cs.geometricRepresentation_simple]
          apply M.geometricReflection_apply_of_eq_zero
          simp [M.geometricForm_single_single,hsep i (hv i (by simp)) e he,Real.cos_pi_div_two]
      ext x
      constructor
      · rintro ⟨y,⟨e,he,rfl⟩,rfl⟩; exact ⟨e,he,(fix e he).symm⟩
      · rintro ⟨e,he,rfl⟩; exact ⟨_,⟨e,he,rfl⟩,fix e he⟩
    have rootTransport : act r '' piRoots I = piRoots K := by
      rw [hi]
      change act r '' ((fun i : S => Finsupp.single i (1 : ℝ)) '' (J ∪ E)) = piRoots K
      rw [Set.image_union,Set.image_union,fixedE]
      change act r '' piRoots J ∪ piRoots E = (fun i : S => Finsupp.single i (1 : ℝ)) '' (KD ∪ E)
      rw [Set.image_union]
      exact congrArg (fun X => X ∪ piRoots E) htransport
    refine ⟨K,hKT,root_conjugacy cs r I K rootTransport,rootTransport,?_⟩
    have rootMem {L : Set S} {x : S →₀ ℝ} (hx : x ∈ orbitRoots cs L) : x ∈ cs.geometricRoots := by
      obtain ⟨u,hu,i,hi,he⟩ := hx; exact ⟨u,i,he⟩
    have wrD : (wJ : W) ∈ cs.parabolic D := cs.parabolic_mono Set.inter_subset_left wJ.property
    have negiff (x : S →₀ ℝ) (hx : x ∈ cs.geometricRoots) (hp : 0 < x) :
        act r x < 0 ↔ x ∈ orbitRoots cs D ∧ x ∉ orbitRoots cs J := by
      constructor
      · intro hn
        have hxD : x ∈ orbitRoots cs D := by
          by_contra hno
          exact (positiveOutside cs D r hr x hx hp hno).not_gt hn
        refine ⟨hxD,?_⟩
        intro hxJ
        have hnJ := longest_neg cs J wJ hwJ x hxJ hp
        have hbD := orbitRoots_stable cs D (wJ : W) wrD x hxD
        have hnegRoot : -act (wJ : W) x ∈ orbitRoots cs D := by
          obtain ⟨u,hu,i,hi,he⟩ := hbD
          refine ⟨u * cs.simple i,mul_mem hu (cs.simple_mem_parabolic hi),i,hi,?_⟩
          rw [map_mul,mul_apply_eq_comp,cs.geometricRepresentation_simple,
            M.geometricReflection_apply_single_self,map_neg,he]
        have hh := longest_neg cs D wD hwD (-act (wJ : W) x) hnegRoot (neg_pos.mpr hnJ)
        rw [map_neg] at hh
        have hhpos : 0 < act r x := by
          rw [show act r x = act (wD : W) (act (wJ : W) x) from by rw [map_mul,mul_apply_eq_comp]]
          exact neg_neg_iff_pos.mp hh
        exact hhpos.not_gt hn
      · rintro ⟨hxD,hxJ⟩
        have hpos := positiveOutside cs J (wJ : W) wJ.property x hx hp hxJ
        have hbD := orbitRoots_stable cs D (wJ : W) wrD x hxD
        change cs.geometricRepresentation ((wD : W) * (wJ : W)) x < 0
        rw [map_mul,mul_apply_eq_comp]
        exact longest_neg cs D wD hwD _ hbD hpos
    ext x
    constructor
    · rintro ⟨hp,y,hy,he⟩
      have hneg : act r x < 0 := by rw [← he,Representation.self_inv_apply]; exact hy.2
      have hh := (diff x).mpr ((negiff x hp.1 hp.2).mp hneg)
      exact ⟨⟨hh.1,hp⟩,fun h => hh.2 h.1⟩
    · rintro ⟨⟨hT,hp⟩,hI⟩
      have hno : x ∉ orbitRoots cs I := fun hh => hI ⟨hh,hp⟩
      have hneg := (negiff x hp.1 hp.2).mpr ((diff x).mp ⟨hT,hno⟩)
      refine ⟨hp,act r x,⟨(cs.geometricRepresentation_apply_mem_geometricRoots_iff r).mpr hp.1,hneg⟩,?_⟩
      exact Representation.inv_self_apply _ _ _

  classical
  let T : Set S := Set.insert a (Set.insert b I)
  let parabolicRoots : Set S → Set (Finsupp S Real) := fun L =>
    {α | ∃ w : W, w ∈ CoxeterSystem.parabolic cs L ∧ ∃ i : S, i ∈ L ∧
      CoxeterSystem.geometricRepresentation cs w (Finsupp.single i (1 : Real)) = α}
  let simpleRoots : Set S → Set (Finsupp S Real) := fun L =>
    Set.image (fun i : S => Finsupp.single i (1 : Real)) L
  let positiveRoots : Set (Finsupp S Real) := {α | α ∈ CoxeterSystem.geometricRoots cs ∧ 0 < α}
  let negativeRoots : Set (Finsupp S Real) := {α | α ∈ CoxeterSystem.geometricRoots cs ∧ α < 0}
  let edge : S → S → Prop := fun j k => j ∈ T ∧ k ∈ T ∧ j ≠ k ∧ M j k ≠ 2
  let D : Set S := {i | i ∈ T ∧
    (Relation.ReflTransGen edge a i ∨ Relation.ReflTransGen edge b i)}
  change Set.Finite (parabolicRoots T \ parabolicRoots I) → _
  intro hfin
  have hIT : I ⊆ T := fun i hi => Or.inr (Or.inr hi)
  have hDT : D ⊆ T := fun i hi => hi.1
  /- Steps 1.1--2.1: the finite faithful root-action proof above replaces the
     portal's unformalized reflection criterion; every hypothesis is discharged. -/
  have hD : Finite (CoxeterSystem.parabolic cs D) := by
    have h := finiteRootDifferenceSphericalSupport cs I T hIT hfin
    have hsets :
        {i | i ∈ T ∧ ∃ c : S, c ∈ T ∧ c ∉ I ∧ Relation.ReflTransGen edge c i} = D := by
      apply Set.ext
      intro i
      constructor
      · rintro ⟨hi, c, hcT, hcI, hci⟩
        rcases hcT with hca | hcb | hc
        · subst c
          exact ⟨hi, Or.inl hci⟩
        · subst c
          exact ⟨hi, Or.inr hci⟩
        · exact False.elim (hcI hc)
      · rintro ⟨hi, hai | hbi⟩
        · exact ⟨hi, a, Or.inl rfl, ha, hai⟩
        · exact ⟨hi, b, Or.inr (Or.inl rfl), hb, hbi⟩
    change Finite (cs.parabolic {i | i ∈ T ∧ ∃ c : S, c ∈ T ∧ c ∉ I ∧ Relation.ReflTransGen edge c i}) at h
    rw [hsets] at h
    exact h
  have hrest : T \ D ⊆ I := by
    rintro i ⟨hi, hni⟩
    rcases hi with hia | hib | hiI
    · subst i
      exact False.elim (hni ⟨Or.inl rfl, Or.inl Relation.ReflTransGen.refl⟩)
    · subst i
      exact False.elim (hni ⟨Or.inr (Or.inl rfl), Or.inr Relation.ReflTransGen.refl⟩)
    · exact hiI
  have hsep : ∀ i : S, i ∈ D → ∀ j : S, j ∈ T \ D → M i j = 2 := by
    intro i hi j hj
    by_contra hm
    have hij : i ≠ j := by
      intro he
      subst j
      exact hj.2 hi
    have he : edge i j := ⟨hi.1, hj.1, hij, hm⟩
    apply hj.2
    rcases hi.2 with hai | hbi
    · exact ⟨hj.1, Or.inl (Relation.ReflTransGen.tail hai he)⟩
    · exact ⟨hj.1, Or.inr (Relation.ReflTransGen.tail hbi he)⟩
  /- Step 2.1: maximize ambient length only on finite W_D and W_(D ∩ I).
     Components of I outside D remain unrestricted. -/
  letI : Finite (CoxeterSystem.parabolic cs D) := hD
  have hDI : D ∩ I ⊆ D := fun _ hi => hi.1
  let incl : CoxeterSystem.parabolic cs (D ∩ I) → CoxeterSystem.parabolic cs D :=
    fun u => ⟨u.val, (CoxeterSystem.parabolic_mono cs hDI) u.property⟩
  have hincl : Function.Injective incl := by
    intro u v h
    exact Subtype.ext (congrArg (fun z : CoxeterSystem.parabolic cs D => z.val) h)
  letI : Finite (CoxeterSystem.parabolic cs (D ∩ I)) := Finite.of_injective incl hincl
  obtain ⟨wD, hwD⟩ := Finite.exists_max (fun u : CoxeterSystem.parabolic cs D => CoxeterSystem.length cs u.val)
  obtain ⟨wDI, hwDI⟩ := Finite.exists_max (fun u : CoxeterSystem.parabolic cs (D ∩ I) => CoxeterSystem.length cs u.val)
  /- Step 2.1: apply the proved spherical calculation and commuting extension. -/
  obtain ⟨K, hKT, hconj, hroot, hinvset⟩ :=
    SphericalSupportRelativeLongest cs I T D hIT hDT hrest hsep hD wD wDI hwD hwDI
  refine ⟨hD, wD, wDI, hwD, hwDI, K, hKT, ?_, hroot, ?_, hinvset⟩
  · /- Step 3.1: reverse conjugacy using q = r⁻¹. -/
    exact ⟨((wD : W) * (wDI : W))⁻¹,
      ArtinNormalisers.Chamber3.inverse_parabolic_transporter cs hconj⟩
  · /- Step 3.1: invert root transport to obtain the article arrow I → K.
       Source: https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-author-a7d202611130-finite-relative-longest
       This is a portal helper for article Lemma 4.15/(4.16), Remark 4.17,
       printed p.19, not a standalone article lemma.
       The defect report does not reject this endpoint. Its exact finding
       pdf-wall-root-characterisation rejects the auxiliary characterization
       immediately after (3.15), p.10: for rank one and I empty, Φ_K^- is
       empty although the relevant root maps to its negative. That formula
       is unused; the longest-element definition is retained.
       Report: https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects
       With N(x)=Φ⁺∩xΦ⁻, N(q) concerns negativity under r, not under q. -/
    calc
      Set.image (CoxeterSystem.geometricRepresentation cs ((wD : W) * (wDI : W))⁻¹)
          (simpleRoots K) =
        Set.image (CoxeterSystem.geometricRepresentation cs ((wD : W) * (wDI : W))⁻¹)
          (Set.image (CoxeterSystem.geometricRepresentation cs ((wD : W) * (wDI : W)))
            (simpleRoots I)) := congrArg _ hroot.symm
      _ = simpleRoots I := by
        simp only [Set.image_image, Representation.inv_self_apply, Set.image_id'])
