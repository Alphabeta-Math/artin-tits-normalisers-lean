import Mathlib
import ArtinDeligne
import Proofs.BrinkHowlettGroupoid
import Proofs.StandardExpressions

theorem StandardFactorCount : (∀ {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) (I K : { L : Set S // ∃ g : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (CoxeterSystem.parabolic cs L) = CoxeterSystem.parabolic cs J }) (w : (BrinkHowlettGroupoid cs J).Hom I K), let roots : Set (Finsupp S Real) := CoxeterSystem.geometricRoots cs; let act := CoxeterSystem.geometricRepresentation cs; let parallelClass : Finsupp S Real → Set (Finsupp S Real) := fun α => { β | β ∈ roots ∧ ∀ L, ∀ f : (BrinkHowlettGroupoid cs J).Hom L I, (0 < act f.val α ↔ 0 < act f.val β) }; let realRoot : Finsupp S Real → Prop := fun α => α ∈ roots ∧ ∃ L, ∃ f : (BrinkHowlettGroupoid cs J).Hom L I, ¬ (0 < α ↔ 0 < act f.val α); let inversions : Set (Finsupp S Real) := { α | α ∈ roots ∧ 0 < α } ∩ Set.image (act w.val) { α | α ∈ roots ∧ α < 0 }; let classes : Set (Set (Finsupp S Real)) := { c | (∃ α, realRoot α ∧ c = parallelClass α) ∧ c ⊆ inversions }; Nonempty (StandardExpressions cs J I K w) ∧ Set.Finite classes ∧ ∀ e : StandardExpressions cs J I K w, List.length e.val = Nat.card { c : Set (Finsupp S Real) // c ∈ classes }) :=
(by
  set_option maxHeartbeats 4000000 in
    /-
    Portal helper, not a standalone article lemma. Parent: Lemma 4.10 and
    Corollary 4.13, printed p.18, https://arxiv.org/pdf/2509.21915#page=18.
    https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-author-b19d43a8e520-bh-standard-factor-count
    steps 1.1, 1.2, 2.1 inspire existence, additive induction and factor counting.
    Necessary departures: prove arbitrary-rank existence and the single-class
    assertion locally. Suffix induction replaces successive prefixes; both
    subadditivity bounds establish suffix standardness.

    Additional numbered inspiration: finite-relative-longest steps 1.1, 2.1, 3.1,
    https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-author-a7d202611130-finite-relative-longest;
    opposite-identification steps 1.1, 1.2, 3.1, 4.1,
    https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-author-b19d43a8e520-bh-opposite-identification;
    parallel-root-classes steps 1.1, 2.1, 3.1, 4.1,
    https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-author-b19d43a8e520-bh-parallel-root-classes;
    compressed-additivity steps 1.1, 2.1,
    https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-author-b19d43a8e520-bh-compressed-additivity.
    The implementation helpers have no standalone original article statements.
    Opposite root-action arrows retain the SAME label: x:I->K acts from K to I.
    No rank restriction, finite ambient group or spherical-source assumption occurs.

    Literature defect: pdf-wall-root-characterisation,
    https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects#pdf-wall-root-characterisation
    rejects the auxiliary inclusion after (3.15), p.10. Evidence: S={a}, I=J=empty,
    K=empty, v=s_a maps alpha_a to -alpha_a although the printed target Phi_K^- is
    empty. Disposition: retain the longest-element definition (3.14), certify its
    choices and use ElementaryWallMorphism. The defective characterization is unused.
    No endpoint is substituted; the factor-count formula is sourced from the portal.

    Integrated completed helper reports 56eec666 and 748ba0fc. Consulted completed
    relative-longest reports c8ae4709 and da43298b before recovery. Generic blocks
    below are copied from CURRENT generated Proofs/FiniteRelativeLongest.lean,
    SHA256 08b3c101a99314b19ec5b2dab180dac6ab85339f8328c2387b525b51f5f53dbd,
    under /home/lazyinspirit/Projects/artin-tits-normalisers-lean/theorems13-14/.
    They are not attributed to the base Git revision, and the exported theorem's
    two distinct vertices are never equated. Both formerly missing endpoints are
    now proved locally. The earlier conditional audit is not a proof of them.
    Reused supplied investigations' actual bounded GitHub searches and reading
    limits; no fresh whole-article or complete transitive-source reading is claimed.

    The expression compiled in /tmp/lean-agent-PNm0mn/Check.lean under Lean
    v4.36.0-rc2, exit 0, against existing compiled dependencies. Axiom audit:
    propext, Classical.choice, Quot.sound only. No pending prerequisites remain.
    Existing providers are unchanged from requested commit
    8668c70d25e6c5d63c313bac756052f9c83ee7f0 to observed HEAD
    1bdd7a76d6447fe84bc46aab09120f20292bf334. No agents, repository writes or
    remote changes. Verification is not a fresh dependency rebuild.
    -/
    intro S W inst M cs J I K w
    classical
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
    -- Finite-relative-longest steps 1.1--2.1: propagate the seed span along edges.
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
      have hI : I = (D ∩ I) ∪ (I \ D) := by
        ext i
        simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_sdiff]
        tauto
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
        refine ⟨?_, hxI⟩
        obtain ⟨w, hw, i, hi, hr⟩ := hx
        exact ⟨w, cs.parabolic_mono hDT hw, i, hDT hi, hr⟩
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
          exact ih (fun j hj => hu j (by simp [hj]))
            (cs.wordProd_mem_parabolic (fun j hj => hu j (by simp [hj])))
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
            rw [← mul_apply_eq_comp, ← map_mul, zz]
            simp [act]
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
          rw [← mul_apply_eq_comp, ← map_mul, zz]
          simp [act]
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
    have positiveOutside (cs : CoxeterSystem M W) (L : Set S) (w : W)
        (hw : w ∈ cs.parabolic L) (x : S →₀ ℝ) (hx : x ∈ cs.geometricRoots)
        (hp : 0 < x) (hn : x ∉ orbitRoots cs L) :
        0 < cs.geometricRepresentation w x := by
      obtain ⟨v, hv, rfl⟩ := cs.exists_wordProd_eq_of_mem_parabolic hw
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
    have longest_neg (cs : CoxeterSystem M W) (L : Set S) (z : cs.parabolic L)
        (hz : ∀ u : cs.parabolic L, cs.length (u : W) ≤ cs.length (z : W))
        (x : S →₀ ℝ) (hx : x ∈ orbitRoots cs L) (hp : 0 < x) :
        cs.geometricRepresentation (z : W) x < 0 := by
      classical
      obtain ⟨zz, e, he, heq, hgen⟩ := oppositionWork cs L z hz
      have hcol (i : S) (hi : i ∈ L) :
          cs.geometricRepresentation (z : W) (Finsupp.single i 1) ≤ 0 := by
        rw [heq ⟨i, hi⟩]
        exact neg_nonpos.mpr (Finsupp.single_nonneg.mpr (by norm_num))
      have hn : cs.geometricRepresentation (z : W) x ≤ 0 := by
        have hex : x = ∑ i ∈ x.support, x i • Finsupp.single i (1 : ℝ) := by
          ext k
          simp [Finsupp.single_apply, Finset.sum_ite_eq']
        rw [hex, map_sum]
        intro k
        simp only [Finset.sum_apply', map_smul, Finsupp.smul_apply, Pi.smul_apply,
          smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply]
        apply Finset.sum_nonpos
        intro i hi
        have hiL : i ∈ L := by
          by_contra hn
          exact (Finsupp.mem_support_iff.mp hi) (supported cs L hx i hn)
        exact mul_nonpos_of_nonneg_of_nonpos (hp.le i) (hcol i hiL k)
      apply lt_of_le_of_ne hn
      apply cs.ne_zero_of_mem_geometricRoots
      apply (cs.geometricRepresentation_apply_mem_geometricRoots_iff (z : W)).mpr
      obtain ⟨u, hu, i, hi, he⟩ := hx
      exact ⟨u, i, he⟩
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
      have ht : T = D ∪ E := by
        ext i
        dsimp [E]
        simp only [Set.mem_union, Set.mem_sdiff]
        exact ⟨fun hi => by by_cases h : i ∈ D <;> tauto,
          fun h => h.elim (fun hd => hDT hd) And.left⟩
      have hi : I = J ∪ E := by
        ext i
        change i ∈ I ↔ (i ∈ D ∧ i ∈ I) ∨ (i ∈ T ∧ i ∉ D)
        constructor
        · intro hh
          by_cases hd : i ∈ D
          · exact Or.inl ⟨hd, hh⟩
          · exact Or.inr ⟨hIT hh, hd⟩
        · intro hh
          exact hh.elim And.right (fun h => hrest h)
      have splitT : orbitRoots cs T = orbitRoots cs D ∪ orbitRoots cs E := by
        rw [ht]
        exact rootUnion cs D E hsep
      have splitI : orbitRoots cs I = orbitRoots cs J ∪ orbitRoots cs E := by
        rw [hi]
        exact rootUnion cs J E (fun i hi j hj => hsep i hi.1 j hj)
      have disjoint : Disjoint (orbitRoots cs D) (orbitRoots cs E) := by
        apply Set.disjoint_left.mpr
        intro x hx hy
        have hz : x = 0 := by
          ext k
          by_cases hk : k ∈ D
          · exact supported cs E hy k (fun hh => hh.2 hk)
          · exact supported cs D hx k hk
        obtain ⟨u, hu, i, hi, he⟩ := hx
        exact cs.ne_zero_of_mem_geometricRoots ⟨u, i, he⟩ hz
      have diff (x : S →₀ ℝ) :
          (x ∈ orbitRoots cs T ∧ x ∉ orbitRoots cs I) ↔
          (x ∈ orbitRoots cs D ∧ x ∉ orbitRoots cs J) := by
        rw [splitT, splitI]
        have hJD : orbitRoots cs J ⊆ orbitRoots cs D := by
          rintro y ⟨u, hu, i, hi, he⟩
          exact ⟨u, cs.parabolic_mono Set.inter_subset_left hu, i, hi.1, he⟩
        have hd := Set.disjoint_left.mp disjoint
        simp only [Set.mem_union]
        constructor
        · rintro ⟨hx, hni⟩
          rcases hx with hx | hx
          · exact ⟨hx, fun h => hni (Or.inl h)⟩
          · exact False.elim (hni (Or.inr hx))
        · rintro ⟨hx, hn⟩
          exact ⟨Or.inl hx, fun h => h.elim hn (hd hx)⟩
      obtain ⟨zzD, opD, hopD, hrootD, hgenD⟩ := oppositionWork cs D wD hwD
      obtain ⟨zzJ, opJ, hopJ, hrootJ, hgenJ⟩ := oppositionWork cs J wJ hwJ
      obtain ⟨hr, hKD, htransport⟩ := opposition_target cs I D wD wJ opD opJ hrootD hrootJ
      let KD : Set S := (fun i : D => (opD i : S)) '' {i : D | (i : S) ∈ I}
      let K := KD ∪ E
      have hKT : K ⊆ T := fun i hi => hi.elim (fun h => hDT (hKD h)) And.left
      have fixedE : act r '' piRoots E = piRoots E := by
        have fix (e : S) (he : e ∈ E) : act r (Finsupp.single e 1) = Finsupp.single e 1 := by
          obtain ⟨v, hv, heq⟩ := cs.exists_wordProd_eq_of_mem_parabolic hr
          change act ((wD : W) * (wJ : W)) (Finsupp.single e 1) = Finsupp.single e 1
          rw [← heq]
          clear heq
          induction v with
          | nil => simp [act]
          | cons i v ih =>
            rw [cs.wordProd_cons, map_mul, mul_apply_eq_comp,
              ih (fun j hj => hv j (by simp [hj])), cs.geometricRepresentation_simple]
            apply M.geometricReflection_apply_of_eq_zero
            simp [M.geometricForm_single_single, hsep i (hv i (by simp)) e he, Real.cos_pi_div_two]
        ext x
        constructor
        · rintro ⟨y, ⟨e, he, rfl⟩, rfl⟩
          exact ⟨e, he, (fix e he).symm⟩
        · rintro ⟨e, he, rfl⟩
          exact ⟨_, ⟨e, he, rfl⟩, fix e he⟩
      have rootTransport : act r '' piRoots I = piRoots K := by
        rw [hi]
        change act r '' ((fun i : S => Finsupp.single i (1 : ℝ)) '' (J ∪ E)) = piRoots K
        rw [Set.image_union, Set.image_union, fixedE]
        change act r '' piRoots J ∪ piRoots E = (fun i : S => Finsupp.single i (1 : ℝ)) '' (KD ∪ E)
        rw [Set.image_union]
        exact congrArg (fun X => X ∪ piRoots E) htransport
      refine ⟨K, hKT, root_conjugacy cs r I K rootTransport, rootTransport, ?_⟩
      have rootMem {L : Set S} {x : S →₀ ℝ} (hx : x ∈ orbitRoots cs L) : x ∈ cs.geometricRoots := by
        obtain ⟨u, hu, i, hi, he⟩ := hx
        exact ⟨u, i, he⟩
      have wrD : (wJ : W) ∈ cs.parabolic D := cs.parabolic_mono Set.inter_subset_left wJ.property
      have negiff (x : S →₀ ℝ) (hx : x ∈ cs.geometricRoots) (hp : 0 < x) :
          act r x < 0 ↔ x ∈ orbitRoots cs D ∧ x ∉ orbitRoots cs J := by
        constructor
        · intro hn
          have hxD : x ∈ orbitRoots cs D := by
            by_contra hno
            exact (positiveOutside cs D r hr x hx hp hno).not_gt hn
          refine ⟨hxD, ?_⟩
          intro hxJ
          have hnJ := longest_neg cs J wJ hwJ x hxJ hp
          have hbD := orbitRoots_stable cs D (wJ : W) wrD x hxD
          have hnegRoot : -act (wJ : W) x ∈ orbitRoots cs D := by
            obtain ⟨u, hu, i, hi, he⟩ := hbD
            refine ⟨u * cs.simple i, mul_mem hu (cs.simple_mem_parabolic hi), i, hi, ?_⟩
            rw [map_mul, mul_apply_eq_comp, cs.geometricRepresentation_simple,
              M.geometricReflection_apply_single_self, map_neg, he]
          have hh := longest_neg cs D wD hwD (-act (wJ : W) x) hnegRoot (neg_pos.mpr hnJ)
          rw [map_neg] at hh
          have hhpos : 0 < act r x := by
            rw [show act r x = act (wD : W) (act (wJ : W) x) from by rw [map_mul, mul_apply_eq_comp]]
            exact neg_neg_iff_pos.mp hh
          exact hhpos.not_gt hn
        · rintro ⟨hxD, hxJ⟩
          have hpos := positiveOutside cs J (wJ : W) wJ.property x hx hp hxJ
          have hbD := orbitRoots_stable cs D (wJ : W) wrD x hxD
          change cs.geometricRepresentation ((wD : W) * (wJ : W)) x < 0
          rw [map_mul, mul_apply_eq_comp]
          exact longest_neg cs D wD hwD _ hbD hpos
      ext x
      constructor
      · rintro ⟨hp, y, hy, he⟩
        have hneg : act r x < 0 := by
          rw [← he, Representation.self_inv_apply]
          exact hy.2
        have hh := (diff x).mpr ((negiff x hp.1 hp.2).mp hneg)
        exact ⟨⟨hh.1, hp⟩, fun h => hh.2 h.1⟩
      · rintro ⟨⟨hT, hp⟩, hI⟩
        have hno : x ∉ orbitRoots cs I := fun hh => hI ⟨hh, hp⟩
        have hneg := (negiff x hp.1 hp.2).mpr ((diff x).mp ⟨hT, hno⟩)
        refine ⟨hp, act r x, ⟨(cs.geometricRepresentation_apply_mem_geometricRoots_iff r).mpr hp.1, hneg⟩, ?_⟩
        exact Representation.inv_self_apply _ _ _
    -- Factor-count step 1.1: an independent arbitrary-rank existence proof.
    have hexists : ∀ (I K : { L : Set S // ∃ g : W,
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (cs.parabolic L) = cs.parabolic J })
        (w : (BrinkHowlettGroupoid cs J).Hom I K),
        Nonempty (StandardExpressions cs J I K w) := by
      have expand (x : S →₀ ℝ) : x = ∑ i ∈ x.support, x i • Finsupp.single i (1 : ℝ) := by
        ext k
        simp [Finsupp.single_apply, Finset.sum_ite_eq']
      have action_support (g : W) (L F : Set S)
          (hc : ∀ i ∈ L, ∀ k, k ∉ F → cs.geometricRepresentation g (Finsupp.single i 1) k = 0)
          (x : S →₀ ℝ) (hx : ∀ k, k ∉ L → x k = 0) :
          ∀ k, k ∉ F → cs.geometricRepresentation g x k = 0 := by
        intro k hk
        rw [expand x, map_sum]
        simp only [Finset.sum_apply', map_smul, Finsupp.smul_apply, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_eq_zero
        intro i hi
        have hiL : i ∈ L := by
          by_contra hn
          exact (Finsupp.mem_support_iff.mp hi) (hx i hn)
        rw [hc i hiL k hk, mul_zero]
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
      let piRoots : Set S → Set (S →₀ ℝ) := fun L => (fun i : S => Finsupp.single i (1 : ℝ)) '' L
      have image_support (g : W) (L F : Set S)
          (he : cs.geometricRepresentation g '' piRoots L = piRoots F)
          (x : S →₀ ℝ) (hx : ∀ k, k ∉ L → x k = 0) :
          ∀ k, k ∉ F → cs.geometricRepresentation g x k = 0 := by
        apply action_support g L F _ x hx
        intro i hi k hk
        have hm := he ▸ Set.mem_image_of_mem (cs.geometricRepresentation g)
          (Set.mem_image_of_mem (fun j : S => Finsupp.single j (1 : ℝ)) hi)
        obtain ⟨j, hj, hjr⟩ := hm
        rw [← hjr]
        simp [show j ≠ k from fun h => hk (h ▸ hj)]
      have inverse_image (g : W) (L F : Set S)
          (he : cs.geometricRepresentation g '' piRoots L = piRoots F) :
          cs.geometricRepresentation g⁻¹ '' piRoots F = piRoots L := by
        rw [← he, Set.image_image]
        simp only [Representation.inv_self_apply, Set.image_id']
      have singleton_relative_sign (I K : Set S) (w : W)
          (hw : cs.geometricRepresentation w '' piRoots K = piRoots I)
          (a : S) (ha : a ∉ I)
          (han : cs.geometricRepresentation w⁻¹ (Finsupp.single a 1) < 0)
          (x : S →₀ ℝ) (hx : x ∈ orbitRoots cs (Set.insert a I))
          (hp : 0 < x) (hn : x ∉ orbitRoots cs I) :
          cs.geometricRepresentation w⁻¹ x < 0 := by
        have hr : x ∈ cs.geometricRoots := by
          obtain ⟨u, hu, i, hi, he⟩ := hx
          exact ⟨u, i, he⟩
        have hxa : 0 < x a := by
          apply lt_of_le_of_ne (hp.le a)
          intro he
          apply hn
          apply positive_supported_root_mem_parabolic I x hr hp
          intro k hk
          by_cases hka : k = a
          · subst k
            exact he.symm
          · exact supported cs (Set.insert a I) hx k (by rintro (heq | hi); exact hka heq; exact hk hi)
        let z := cs.geometricRepresentation w⁻¹ (Finsupp.single a (1 : ℝ))
        have hznot : ¬ ∀ k, k ∉ K → z k = 0 := by
          intro hz
          have hh := image_support w K I hw z hz a ha
          have hcancel : cs.geometricRepresentation w z = Finsupp.single a (1 : ℝ) :=
            Representation.self_inv_apply _ _ _
          rw [hcancel] at hh
          simp at hh
        obtain ⟨k, hk⟩ := not_forall.mp hznot
        obtain ⟨hk, hzk⟩ := not_imp.mp hk
        have hzkneg : z k < 0 := lt_of_le_of_ne (han.le k) hzk
        let t := x - x a • Finsupp.single a (1 : ℝ)
        have ht : ∀ j, j ∉ I → t j = 0 := by
          intro j hj
          by_cases hja : j = a
          · subst j
            simp [t]
          · have hh := supported cs (Set.insert a I) hx j (by rintro (heq | hi); exact hja heq; exact hj hi)
            simp [t, hh, Finsupp.single_apply, hja]
        have htimage := image_support w⁻¹ I K (inverse_image w K I hw) t ht k hk
        have hcoord : cs.geometricRepresentation w⁻¹ x k = x a * z k := by
          dsimp only [t] at htimage
          simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
            Pi.smul_apply, smul_eq_mul] at htimage
          exact sub_eq_zero.mp htimage
        have hncoord : cs.geometricRepresentation w⁻¹ x k < 0 := by
          rw [hcoord]
          exact mul_neg_of_pos_of_neg hxa hzkneg
        rcases cs.pos_or_neg_of_mem_geometricRoots
          ((cs.geometricRepresentation_apply_mem_geometricRoots_iff _).mpr hr) with hp' | hn'
        · exact False.elim ((hp'.le k).not_gt hncoord)
        · exact hn'
      let roots := cs.geometricRoots
      let act := cs.geometricRepresentation
      let N : W → Set (S →₀ ℝ) := fun x => {α | α ∈ roots ∧ 0 < α ∧ act x⁻¹ α < 0}
      have image_N (x : W) : N x = {α | α ∈ roots ∧ 0 < α} ∩
          Set.image (act x) {α | α ∈ roots ∧ α < 0} := by
        ext α
        constructor
        · rintro ⟨hr, hp, hn⟩
          exact ⟨⟨hr, hp⟩, act x⁻¹ α,
            ⟨(cs.geometricRepresentation_apply_mem_geometricRoots_iff _).2 hr, hn⟩,
            Representation.self_inv_apply _ _ _⟩
        · rintro ⟨⟨hr, hp⟩, β, ⟨_, hn⟩, rfl⟩
          exact ⟨hr, hp, by simpa [act] using hn⟩
      have finite_N (x : W) : Set.Finite (N x) := by
        induction hn : cs.length x using Nat.strong_induction_on generalizing x with
        | ind n ih =>
          by_cases hx : x = 1
          · subst x
            have hz : N 1 = ∅ := by
              ext α
              simp only [N, Set.mem_ofPred_eq, inv_one, map_one, one_apply_eq_self,
                Set.mem_empty_iff_false, iff_false]
              rintro ⟨_, hp, hm⟩
              exact lt_asymm hp hm
            rw [hz]
            exact Set.finite_empty
          obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one hx
          have hlen := cs.isLeftDescent_iff.1 hi
          have hf := ih (cs.length (cs.simple i * x)) (by omega) (cs.simple i * x) rfl
          apply (hf.image (M.geometricReflection i)).insert (Finsupp.single i 1) |>.subset
          intro α hα
          by_cases heq : α = Finsupp.single i 1
          · exact Or.inl heq
          · refine Or.inr ⟨M.geometricReflection i α, ?_, ?_⟩
            · refine ⟨(cs.geometricReflection_apply_mem_geometricRoots_iff i).2 hα.1,
                cs.geometricReflection_pos_of_mem_geometricRoots hα.1 hα.2.1 heq, ?_⟩
              change cs.geometricRepresentation (cs.simple i * x)⁻¹
                (M.geometricReflection i α) < 0
              rw [mul_inv_rev, cs.inv_simple, map_mul, mul_apply_eq_comp,
                cs.geometricRepresentation_simple]
              have h := LinearMap.congr_fun (M.geometricReflection_mul_self i) α
              change M.geometricReflection i (M.geometricReflection i α) = α at h
              rw [h]
              exact hα.2.2
            · have h := LinearMap.congr_fun (M.geometricReflection_mul_self i) α
              exact h
      have orbit_neg (L : Set S) (x : S →₀ ℝ) (hx : x ∈ orbitRoots cs L) :
          -x ∈ orbitRoots cs L := by
        obtain ⟨u, hu, i, hi, he⟩ := hx
        refine ⟨u * cs.simple i, (cs.parabolic L).mul_mem hu (cs.simple_mem_parabolic hi), i, hi, ?_⟩
        rw [map_mul, mul_apply_eq_comp, cs.geometricRepresentation_simple,
          M.geometricReflection_apply_single_self, map_neg, he]
      let Obj := {L : Set S // ∃ g : W,
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (cs.parabolic L) = cs.parabolic J}
      let component : Set S → S → Set S := fun L a =>
        {b | b ∈ Set.insert a L ∧ Relation.ReflTransGen
          (fun i j : S => i ∈ Set.insert a L ∧ j ∈ Set.insert a L ∧ i ≠ j ∧ M i j ≠ 2) a b}
      let Atom := {p : Obj × S // p.2 ∉ p.1.val ∧ Finite (cs.parabolic (component p.1.val p.2))}
      let crossing := fun e : Atom => SimpleWallCrossings S W M cs e.val.1.val e.val.2 e.property.1 e.property.2
      have elementary_prefix (I K : Obj) (w : (BrinkHowlettGroupoid cs J).Hom I K) (hne : w.val ≠ 1) :
          ∃ (e : Atom) (L : Obj) (f : (BrinkHowlettGroupoid cs J).Hom I L),
            e.val.1 = I ∧ L.val = (crossing e).2.1 ∧ f.val = (crossing e).1 ∧
            f.val ≠ 1 ∧ cs.length w.val = cs.length f.val + cs.length (f.val⁻¹ * w.val) := by
        obtain ⟨a, had⟩ := cs.exists_leftDescent_of_ne_one hne
        have han : act w.val⁻¹ (Finsupp.single a 1) < 0 :=
          (cs.geometricRepresentation_single_neg_iff _ _).mpr (cs.isRightDescent_inv_iff.mpr had)
        have hw : act w.val '' piRoots K.val = piRoots I.val := w.property
        have hinv := inverse_image w.val K.val I.val hw
        have ha : a ∉ I.val := by
          intro ha
          have hm := hinv ▸ Set.mem_image_of_mem (act w.val⁻¹)
            (Set.mem_image_of_mem (fun i : S => Finsupp.single i (1 : ℝ)) ha)
          obtain ⟨k, hk, he⟩ := hm
          rw [← he] at han
          exact (Finsupp.single_nonneg.mpr (show (0 : ℝ) ≤ 1 by norm_num)).not_gt han
        let T := Set.insert a I.val
        have hsub : ∀ x, x ∈ orbitRoots cs T → 0 < x → x ∉ orbitRoots cs I.val → x ∈ N w.val := by
          intro x hx hp hn
          refine ⟨?_, hp, singleton_relative_sign I.val K.val w.val hw a ha han x hx hp hn⟩
          obtain ⟨u, hu, i, hi, he⟩ := hx
          exact ⟨u, i, he⟩
        have hfin : (orbitRoots cs T \ orbitRoots cs I.val).Finite := by
          apply ((finite_N w.val).union ((finite_N w.val).image Neg.neg)).subset
          intro x hx
          have hr : x ∈ cs.geometricRoots := by
            obtain ⟨u, hu, i, hi, he⟩ := hx.1
            exact ⟨u, i, he⟩
          rcases cs.pos_or_neg_of_mem_geometricRoots hr with hp | hn
          · exact Or.inl (hsub x hx.1 hp hx.2)
          · right
            refine ⟨-x, hsub (-x) (orbit_neg T x hx.1) (neg_pos.mpr hn) ?_, neg_neg x⟩
            intro hh
            exact hx.2 (by simpa only [neg_neg] using orbit_neg I.val (-x) hh)
        let D := component I.val a
        have hIT : I.val ⊆ T := Set.subset_insert a I.val
        have hDT : D ⊆ T := fun i hi => hi.1
        have haD : a ∈ D := ⟨Or.inl rfl, Relation.ReflTransGen.refl⟩
        have hD : Finite (cs.parabolic D) := by
          have h := finiteRootDifferenceSphericalSupport cs I.val T hIT hfin
          have hset : componentSupport M I.val T = D := by
            ext i
            constructor
            · rintro ⟨hi, c, hc, hnc, hci⟩
              rcases hc with rfl | hc
              · exact ⟨hi, hci⟩
              · exact False.elim (hnc hc)
            · rintro ⟨hi, hai⟩
              exact ⟨hi, a, Or.inl rfl, ha, hai⟩
          rw [hset] at h
          exact h
        have hrest : T \ D ⊆ I.val := by
          rintro i ⟨hi, hni⟩
          rcases hi with rfl | hi
          · exact False.elim (hni haD)
          · exact hi
        have hsep : ∀ i ∈ D, ∀ j ∈ T \ D, M i j = 2 := by
          intro i hi j hj
          by_contra hm
          have hij : i ≠ j := fun he => hj.2 (he ▸ hi)
          exact hj.2 ⟨hj.1, Relation.ReflTransGen.tail hi.2 ⟨hi.1, hj.1, hij, hm⟩⟩
        have hDI : D ∩ I.val = D \ {a} := by
          ext i
          constructor
          · rintro ⟨hi, hiI⟩
            exact ⟨hi, fun he => ha (he ▸ hiI)⟩
          · rintro ⟨hi, hia⟩
            refine ⟨hi, ?_⟩
            rcases hi.1 with he | hiI
            · exact False.elim (hia he)
            · exact hiI
        letI : Finite (cs.parabolic D) := hD
        let pick : (L : Set S) → L ⊆ D → cs.parabolic L := fun L hL =>
          letI : Finite (cs.parabolic L) := Finite.of_injective
            (fun u : cs.parabolic L => (⟨u.val, cs.parabolic_mono hL u.property⟩ : cs.parabolic D))
            (fun _ _ h => Subtype.ext (congrArg (fun z : cs.parabolic D => z.val) h))
          Classical.choose (Finite.exists_max (fun u : cs.parabolic L => cs.length u.val))
        have pick_max (L : Set S) (hL : L ⊆ D) :
            ∀ u : cs.parabolic L, cs.length u.val ≤ cs.length (pick L hL).val := by
          letI : Finite (cs.parabolic L) := Finite.of_injective
            (fun u : cs.parabolic L => (⟨u.val, cs.parabolic_mono hL u.property⟩ : cs.parabolic D))
            (fun _ _ h => Subtype.ext (congrArg (fun z : cs.parabolic D => z.val) h))
          exact Classical.choose_spec (Finite.exists_max (fun u : cs.parabolic L => cs.length u.val))
        let d := pick D (fun _ h => h)
        let j := pick (D \ {a}) Set.sdiff_subset
        let jI : cs.parabolic (D ∩ I.val) := ⟨j.val, by rw [hDI]; exact j.property⟩
        have hdmax := pick_max D (fun _ h => h)
        have hjmax : ∀ u : cs.parabolic (D ∩ I.val), cs.length u.val ≤ cs.length jI.val := by
          intro u
          exact pick_max (D \ {a}) Set.sdiff_subset ⟨u.val, hDI ▸ u.property⟩
        obtain ⟨F, hFT, hconj, hroot, hN⟩ :=
          SphericalSupportRelativeLongest cs I.val T D hIT hDT hrest hsep hD d jI hdmax hjmax
        have hdInv : d.val⁻¹ = d.val := inv_eq_of_mul_eq_one_left (oppositionWork cs D d hdmax).1
        have hjInv : jI.val⁻¹ = jI.val := inv_eq_of_mul_eq_one_left
          (oppositionWork cs (D ∩ I.val) jI hjmax).1
        let e : Atom := ⟨(I, a), ha, hD⟩
        have heq : (crossing e).1 = (d.val * jI.val)⁻¹ := by
          rw [mul_inv_rev, hdInv, hjInv]
          rfl
        have hN' : N (crossing e).1 =
            (orbitRoots cs T ∩ {x | x ∈ cs.geometricRoots ∧ 0 < x}) \
              (orbitRoots cs I.val ∩ {x | x ∈ cs.geometricRoots ∧ 0 < x}) := by
          rw [image_N, heq]
          exact hN
        have hprefix : cs.length w.val = cs.length (crossing e).1 +
            cs.length ((crossing e).1⁻¹ * w.val) := by
          apply (ArtinNormalisers.Chamber3.length_eq_add_iff_rootInversions_subset_system cs _ _).mpr
          intro x hr hp hn
          have hm : x ∈ N (crossing e).1 := ⟨hr, hp, hn⟩
          rw [hN'] at hm
          exact (hsub x hm.1.1 hp (fun h => hm.2 ⟨h, hr, hp⟩)).2.2
        have hvne : (crossing e).1 ≠ 1 := by
          have haR : Finsupp.single a (1 : ℝ) ∈ orbitRoots cs T :=
            ⟨1, (cs.parabolic T).one_mem, a, Or.inl rfl, by simp⟩
          have hanI : Finsupp.single a (1 : ℝ) ∉ orbitRoots cs I.val := by
            intro hh
            have h := supported cs I.val hh a ha
            simp at h
          have hpos : 0 < (Finsupp.single a (1 : ℝ)) := by
            apply lt_of_le_of_ne (Finsupp.single_nonneg.mpr (by norm_num))
            exact Ne.symm (Finsupp.single_ne_zero.mpr (by norm_num))
          have hm : Finsupp.single a (1 : ℝ) ∈ N (crossing e).1 := by
            rw [hN']
            exact ⟨⟨haR, cs.single_mem_geometricRoots a, hpos⟩, fun hh => hanI hh.1⟩
          intro he
          have hn := hm.2.2
          rw [he, inv_one, map_one, one_apply_eq_self] at hn
          exact lt_asymm hpos hn
        obtain ⟨hL, f, hf⟩ := ElementaryWallMorphism cs J I.val I.property a ha hD
        exact ⟨e, ⟨(crossing e).2.1, hL⟩, f, rfl, rfl, hf, hf ▸ hvne, hf ▸ hprefix⟩
      intro I K w
      induction hn : cs.length w.val using Nat.strong_induction_on generalizing I K w with
      | ind n ih =>
        by_cases hw : w.val = 1
        · have hroot : piRoots K.val = piRoots I.val := by
            have hp := w.property
            rw [hw, map_one] at hp
            simpa only [one_apply_eq_self, Set.image_id'] using hp
          have hKI : K.val = I.val := by
            apply Set.ext
            intro i
            constructor
            · intro hi
              have hm : Finsupp.single i (1 : ℝ) ∈ piRoots I.val := by
                rw [← hroot]
                exact ⟨i, hi, rfl⟩
              obtain ⟨j, hj, he⟩ := hm
              have hji := Finsupp.single_left_injective (show (1 : ℝ) ≠ 0 by norm_num) he
              exact hji ▸ hj
            · intro hi
              have hm : Finsupp.single i (1 : ℝ) ∈ piRoots K.val := by
                rw [hroot]
                exact ⟨i, hi, rfl⟩
              obtain ⟨j, hj, he⟩ := hm
              have hji := Finsupp.single_left_injective (show (1 : ℝ) ≠ 0 by norm_num) he
              exact hji ▸ hj
          refine ⟨⟨[], ?_, ?_, ?_⟩⟩
          · exact hKI.symm
          · exact hw.symm
          · simp only [hw, cs.length_one, List.map_nil, List.sum_nil]
        · obtain ⟨e, L, f, heI, hL, hf, hne, hadd⟩ := elementary_prefix I K w hw
          let y := (BrinkHowlettGroupoid cs J).comp ((BrinkHowlettGroupoid cs J).inv f) w
          have hy : y.val = f.val⁻¹ * w.val := rfl
          have hpos : 0 < cs.length f.val := Nat.pos_of_ne_zero (fun hz => hne (cs.length_eq_zero_iff.mp hz))
          have hshort : cs.length y.val < n := by
            rw [hy]
            omega
          obtain ⟨es⟩ := ih (cs.length y.val) hshort L K y rfl
          have hes := es.property
          change
            es.val.foldr (fun e tail A => A = e.val.1.val ∧ tail (crossing e).2.1)
              (fun A => A = K.val) L.val ∧
            (es.val.map (fun e => (crossing e).1)).prod = y.val ∧
            cs.length y.val = (es.val.map (fun e => cs.length (crossing e).1)).sum at hes
          refine ⟨⟨e :: es.val, ?_, ?_, ?_⟩⟩
          · exact ⟨congrArg Subtype.val heI.symm, hL ▸ hes.1⟩
          · change (crossing e).1 * (es.val.map (fun e => (crossing e).1)).prod = w.val
            rw [hes.2.1, ← hf, hy, mul_inv_cancel_left]
          · change cs.length w.val = cs.length (crossing e).1 +
              (es.val.map (fun e => cs.length (crossing e).1)).sum
            rw [← hes.2.2, ← hf, hy]
            exact hadd
    -- General-rank single-class assertion, independent of existence.
    have hsingle :
      let Obj := { L : Set S // ∃ g : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (CoxeterSystem.parabolic cs L) = CoxeterSystem.parabolic cs J }
      let roots : Set (Finsupp S Real) := CoxeterSystem.geometricRoots cs
      let act := CoxeterSystem.geometricRepresentation cs
      let parallelClass : Obj → Finsupp S Real → Set (Finsupp S Real) := fun I α =>
        { β | β ∈ roots ∧ ∀ L, ∀ f : (BrinkHowlettGroupoid cs J).Hom L I,
          (0 < act f.val α ↔ 0 < act f.val β) }
      let realRoot : Obj → Finsupp S Real → Prop := fun I α =>
        α ∈ roots ∧ ∃ L, ∃ f : (BrinkHowlettGroupoid cs J).Hom L I,
          ¬ (0 < α ↔ 0 < act f.val α)
      let classes : Obj → W → Set (Set (Finsupp S Real)) := fun I x =>
        { c | (∃ α, realRoot I α ∧ c = parallelClass I α) ∧
          c ⊆ ({ α | α ∈ roots ∧ 0 < α } ∩
            Set.image (act x) { α | α ∈ roots ∧ α < 0 }) }
      ∀ (I : Obj) (a : S) (ha : a ∉ I.val),
        let D : Set S := { b | b ∈ Set.insert a I.val ∧ Relation.ReflTransGen
          (fun i j : S => i ∈ Set.insert a I.val ∧ j ∈ Set.insert a I.val ∧ i ≠ j ∧ M i j ≠ 2) a b }
        ∀ hD : Finite (CoxeterSystem.parabolic cs D),
        Nat.card { c // c ∈ classes I (SimpleWallCrossings S W M cs I.val a ha hD).1 } = 1 := by
      let sroot (i : S) : S →₀ ℝ := Finsupp.single i 1
      let sObj (cs : CoxeterSystem M W) (J : Set S) :=
        {L : Set S // ∃ g : W, (cs.parabolic L).map (MulAut.conj g).toMonoidHom = cs.parabolic J}
      let sN (cs : CoxeterSystem M W) (x : W) : Set (S →₀ ℝ) :=
        {α | α ∈ cs.geometricRoots ∧ 0 < α ∧ cs.geometricRepresentation x⁻¹ α < 0}
      let spc (cs : CoxeterSystem M W) (J : Set S) (I : sObj cs J) (α : S →₀ ℝ) :=
        {β | β ∈ cs.geometricRoots ∧ ∀ L, ∀ f : (BrinkHowlettGroupoid cs J).Hom L I,
          (0 < cs.geometricRepresentation f.val α ↔ 0 < cs.geometricRepresentation f.val β)}
      let srealRoot (cs : CoxeterSystem M W) (J : Set S) (I : sObj cs J) (α : S →₀ ℝ) :=
        α ∈ cs.geometricRoots ∧ ∃ L, ∃ f : (BrinkHowlettGroupoid cs J).Hom L I,
          ¬ (0 < α ↔ 0 < cs.geometricRepresentation f.val α)
      let sclasses (cs : CoxeterSystem M W) (J : Set S) (I : sObj cs J) (x : W) :=
        {c | (∃ α, srealRoot cs J I α ∧ c = spc cs J I α) ∧ c ⊆ sN cs x}
      have expansion (α : S →₀ ℝ) : α = ∑ i ∈ α.support, α i • sroot i := by
        classical
        ext k
        simp [sroot, Finsupp.single_apply, Finset.sum_ite_eq']
      have supported_map (cs : CoxeterSystem M W) (x : W) (I L : Set S)
          (h : Set.image (cs.geometricRepresentation x) (Set.image sroot I) = Set.image sroot L)
          (α : S →₀ ℝ) (hs : ∀ k, k ∉ I → α k = 0) :
          ∀ k, k ∉ L → cs.geometricRepresentation x α k = 0 := by
        classical
        intro k hk
        rw [expansion α, map_sum]
        simp only [Finset.sum_apply', map_smul, Finsupp.smul_apply, Pi.smul_apply, smul_eq_mul]
        apply Finset.sum_eq_zero
        intro i hi
        have hiI : i ∈ I := by
          by_contra hn
          exact (Finsupp.mem_support_iff.mp hi) (hs i hn)
        have hr : cs.geometricRepresentation x (sroot i) ∈ Set.image sroot L := by
          rw [← h]
          exact ⟨sroot i, ⟨i, hiI, rfl⟩, rfl⟩
        obtain ⟨j, hj, he⟩ := hr
        rw [← he]
        simp [sroot, show j ≠ k from fun he => hk (he ▸ hj)]
      have nonneg_map (cs : CoxeterSystem M W) (x : W) (I L : Set S)
          (h : Set.image (cs.geometricRepresentation x) (Set.image sroot I) = Set.image sroot L)
          (α : S →₀ ℝ) (hp : 0 ≤ α) (hs : ∀ k, k ∉ I → α k = 0) :
          0 ≤ cs.geometricRepresentation x α := by
        classical
        rw [expansion α, map_sum]
        apply Finset.sum_nonneg
        intro i hi
        have hiI : i ∈ I := by
          by_contra hn
          exact (Finsupp.mem_support_iff.mp hi) (hs i hn)
        have hr : cs.geometricRepresentation x (sroot i) ∈ Set.image sroot L := by
          rw [← h]
          exact ⟨sroot i, ⟨i, hiI, rfl⟩, rfl⟩
        obtain ⟨j, hj, he⟩ := hr
        rw [map_smul, ← he]
        exact smul_nonneg (hp i) (Finsupp.single_nonneg.mpr (by norm_num))
      have outside_coordinate (cs : CoxeterSystem M W) (x : W) (I L : Set S)
          (h : Set.image (cs.geometricRepresentation x) (Set.image sroot I) = Set.image sroot L)
          (a : S) (α : S →₀ ℝ) (hs : ∀ k, k ∉ Set.insert a I → α k = 0)
          (k : S) (hk : k ∉ L) :
          cs.geometricRepresentation x α k = α a * cs.geometricRepresentation x (sroot a) k := by
        let β := α - α a • sroot a
        have hβ : ∀ i, i ∉ I → β i = 0 := by
          intro i hi
          by_cases he : i = a
          · subst i
            simp [β, sroot]
          · simp [β, sroot, Finsupp.single_apply, he,
              hs i (by intro hh; rcases hh with hh | hh; exact he hh; exact hi hh)]
        have hz := supported_map cs x I L h β hβ k hk
        have hz' : cs.geometricRepresentation x α k - α a * cs.geometricRepresentation x (sroot a) k = 0 := by
          simpa only [β, map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul] using hz
        exact sub_eq_zero.mp hz'
      have uniform (cs : CoxeterSystem M W) (J : Set S) (I : sObj cs J)
          (a : S) (ha : a ∉ I.val) (α : S →₀ ℝ)
          (hr : α ∈ cs.geometricRoots) (hp : 0 < α a)
          (hs : ∀ k, k ∉ Set.insert a I.val → α k = 0) :
          ∀ L, ∀ f : (BrinkHowlettGroupoid cs J).Hom L I,
            (0 < cs.geometricRepresentation f.val α ↔
              0 < cs.geometricRepresentation f.val (sroot a)) := by
        intro L f
        let act := cs.geometricRepresentation
        have hf : Set.image (act f.val) (Set.image sroot I.val) = Set.image sroot L.val := f.property
        have hfi : Set.image (act f.val⁻¹) (Set.image sroot L.val) = Set.image sroot I.val :=
          ((BrinkHowlettGroupoid cs J).inv f).property
        have hqroot : act f.val (sroot a) ∈ cs.geometricRoots := ⟨f.val, a, rfl⟩
        have hαroot := (cs.geometricRepresentation_apply_mem_geometricRoots_iff f.val).2 hr
        have hnz : ∃ k, k ∉ L.val ∧ act f.val (sroot a) k ≠ 0 := by
          by_contra hn
          push Not at hn
          have hh := supported_map cs f.val⁻¹ L.val I.val hfi (act f.val (sroot a)) hn a ha
          change (act f.val⁻¹ (act f.val (sroot a))) a = 0 at hh
          rw [Representation.inv_self_apply] at hh
          norm_num [sroot] at hh
        obtain ⟨k, hk, hq⟩ := hnz
        have hcoord := outside_coordinate cs f.val I.val L.val hf a α hs k hk
        change act f.val α k = α a * act f.val (sroot a) k at hcoord
        constructor
        · intro hα
          rcases cs.pos_or_neg_of_mem_geometricRoots hqroot with hpos | hneg
          · exact hpos
          · have hqk : act f.val (sroot a) k < 0 := lt_of_le_of_ne (hneg.le k) hq
            have hαk := hα.le k
            change 0 ≤ act f.val α k at hαk
            rw [hcoord] at hαk
            exact False.elim ((mul_neg_of_pos_of_neg hp hqk).not_ge hαk)
        · intro hqpos
          rcases cs.pos_or_neg_of_mem_geometricRoots hαroot with hpos | hneg
          · exact hpos
          · have hqk : 0 < act f.val (sroot a) k := lt_of_le_of_ne (hqpos.le k) (Ne.symm hq)
            have hαk := hneg.le k
            change act f.val α k ≤ 0 at hαk
            rw [hcoord] at hαk
            exfalso
            have := mul_pos hp hqk
            linarith
      let scomponent (M : CoxeterMatrix S) (I : Set S) (a : S) : Set S :=
        {b | b ∈ Set.insert a I ∧ Relation.ReflTransGen
          (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b}
      have elementary (cs : CoxeterSystem M W) (J : Set S) (I : sObj cs J)
          (a : S) (ha : a ∉ I.val) (hD : Finite (cs.parabolic (scomponent M I.val a))) :
          let v := (SimpleWallCrossings S W M cs I.val a ha hD).1
          sclasses cs J I v = {spc cs J I (sroot a)} ∧
          Nat.card {c // c ∈ sclasses cs J I v} = 1 := by
        classical
        let D := scomponent M I.val a
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
        let d : W := longest D (fun _ h => h)
        let E : Set S := D \ {a}
        let e : W := longest E Set.sdiff_subset
        let v := (SimpleWallCrossings S W M cs I.val a ha hD).1
        have hv : v = e * d := rfl
        have hdmem : d ∈ cs.parabolic D := (longest D (fun _ h => h)).property
        have hemem : e ∈ cs.parabolic E := (longest E Set.sdiff_subset).property
        have da : a ∈ D := ⟨Set.mem_insert a I.val, Relation.ReflTransGen.refl⟩
        have hDsub : D ⊆ Set.insert a I.val := fun _ h => h.1
        obtain ⟨hdd, ν, hνinv, hνroot, hνgen⟩ :=
          oppositionWork cs D (longest D (fun _ h => h)) (longest_max D (fun _ h => h))
        obtain ⟨hee, μ, hμinv, hμroot, hμgen⟩ :=
          oppositionWork cs E (longest E Set.sdiff_subset) (longest_max E Set.sdiff_subset)
        change d * d = 1 at hdd
        change e * e = 1 at hee
        have hdi : d⁻¹ = d := inv_eq_of_mul_eq_one_left hdd
        have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_left hee
        have hvi : v⁻¹ = d * e := by rw [hv, mul_inv_rev, hdi, hei]
        have hchoiceInverse : v = (d * e)⁻¹ := by rw [mul_inv_rev, hdi, hei, hv]
        -- Epsilon's specification is used only after proving opposition existence.
        let ν₀ : D ≃ D := @Classical.epsilon (D ≃ D) ⟨Equiv.refl D⟩
          (fun t => ∀ i : D, cs.geometricRepresentation d (sroot i) = -sroot (t i : S))
        have hν₀root : ∀ i : D, cs.geometricRepresentation d (sroot i) = -sroot (ν₀ i : S) :=
          Classical.epsilon_spec_aux ⟨Equiv.refl D⟩
            (fun t : D ≃ D => ∀ i : D, cs.geometricRepresentation d (sroot (i : S)) =
              -sroot (t i : S)) ⟨ν, hνroot⟩
        have hν₀eq : ν₀ = ν := by
          apply Equiv.ext
          intro i
          apply Subtype.ext
          apply Finsupp.single_left_injective (show (1 : ℝ) ≠ 0 by norm_num)
          exact neg_injective ((hν₀root i).symm.trans (hνroot i))
        have hν₀inv : Function.Involutive ν₀ := by simpa only [hν₀eq] using hνinv
        have hν₀gen : ∀ i : D, d * cs.simple (i : S) * d⁻¹ = cs.simple (ν₀ i : S) := by
          simpa only [hν₀eq] using hνgen
        have htarget : (SimpleWallCrossings S W M cs I.val a ha hD).2.1 =
            Set.insert a I.val \ {(ν₀ ⟨a, da⟩ : S)} := rfl
        have hvmem : v⁻¹ ∈ cs.parabolic D := by
          rw [hvi]
          exact (cs.parabolic D).mul_mem hdmem (cs.parabolic_mono Set.sdiff_subset hemem)
        obtain ⟨hK, x, hx⟩ := ElementaryWallMorphism cs J I.val I.property a ha hD
        let K : sObj cs J := ⟨(SimpleWallCrossings S W M cs I.val a ha hD).2.1, hK⟩
        change (BrinkHowlettGroupoid cs J).Hom I K at x
        change x.val = v at hx
        let act := cs.geometricRepresentation
        have hinvImage : Set.image (act v⁻¹) (Set.image sroot I.val) = Set.image sroot K.val := by
          rw [← hx]
          exact ((BrinkHowlettGroupoid cs J).inv x).property
        have supported_inversions (α : S →₀ ℝ) (hα : α ∈ sN cs v) :
            ∀ k, k ∉ D → α k = 0 := by
          intro k hk
          have hz := outside cs D v⁻¹ hvmem k hk α
          have hp := hα.2.1.le k
          have hn := hα.2.2.le k
          change act v⁻¹ α k ≤ 0 at hn
          rw [hz] at hn
          exact le_antisymm hn hp
        have positive_a (α : S →₀ ℝ) (hα : α ∈ sN cs v) : 0 < α a := by
          have hpa := hα.2.1.le a
          change 0 ≤ α a at hpa
          by_contra hn
          have haz : α a = 0 := le_antisymm (le_of_not_gt hn) hpa
          have hs : ∀ k, k ∉ I.val → α k = 0 := by
            intro k hk
            by_cases he : k = a
            · simpa [he] using haz
            · exact supported_inversions α hα k (fun h => by
                rcases hDsub h with h | h
                · exact he h
                · exact hk h)
          have hh := nonneg_map cs v⁻¹ I.val K.val hinvImage α hα.2.1.le hs
          exact (not_lt_of_ge hh) hα.2.2
        have seed : sroot a ∈ sN cs v := by
          let p := act e (sroot a)
          have hpa : p a = 1 := by
            change act e (sroot a) a = 1
            rw [outside cs E e hemem a (by simp [E])]
            simp [sroot]
          have hpRoot : p ∈ cs.geometricRoots := ⟨e, a, rfl⟩
          have hp : 0 < p := by
            rcases cs.pos_or_neg_of_mem_geometricRoots hpRoot with h | h
            · exact h
            · have hh := h.le a
              change p a ≤ 0 at hh
              rw [hpa] at hh
              norm_num at hh
          have hs : ∀ k, k ∉ D → p k = 0 := by
            intro k hk
            change act e (sroot a) k = 0
            rw [outside cs E e hemem k (fun h => hk h.1)]
            simp [sroot, show a ≠ k from fun h => hk (h ▸ da)]
          have hdcol (i : S) (hi : i ∈ D) : act d (sroot i) ≤ 0 := by
            have hh := hνroot ⟨i, hi⟩
            change act d (sroot i) = -sroot (ν ⟨i, hi⟩ : S) at hh
            rw [hh]
            exact neg_nonpos.mpr (Finsupp.single_nonneg.mpr (by norm_num))
          have hdnp : act d p ≤ 0 := by
            rw [expansion p, map_sum]
            intro k
            simp only [Finset.sum_apply', map_smul, Finsupp.smul_apply, smul_eq_mul,
              Finsupp.coe_zero, Pi.zero_apply]
            apply Finset.sum_nonpos
            intro i hi
            have hiD : i ∈ D := by
              by_contra hn
              exact (Finsupp.mem_support_iff.mp hi) (hs i hn)
            exact mul_nonpos_of_nonneg_of_nonpos (hp.le i) (hdcol i hiD k)
          refine ⟨?_, ?_, ?_⟩
          · exact ⟨1, a, by simp [sroot]⟩
          · exact lt_of_le_of_ne (Finsupp.single_nonneg.mpr (by norm_num))
              (by intro hh; have := congrArg (fun z : S →₀ ℝ => z a) hh; norm_num [sroot] at this)
          · rw [hvi, map_mul, mul_apply_eq_comp]
            apply lt_of_le_of_ne hdnp
            exact cs.ne_zero_of_mem_geometricRoots ⟨d * e, a, by simp only [map_mul, mul_apply_eq_comp]; rfl⟩
        have hsign (α : S →₀ ℝ) (hα : α ∈ sN cs v) :
            ∀ L, ∀ f : (BrinkHowlettGroupoid cs J).Hom L I,
              (0 < act f.val α ↔ 0 < act f.val (sroot a)) := by
          apply uniform cs J I a ha α hα.1 (positive_a α hα)
          intro k hk
          exact supported_inversions α hα k (fun h => hk (hDsub h))
        have real_of_inv (α : S →₀ ℝ) (hα : α ∈ sN cs v) : srealRoot cs J I α := by
          refine ⟨hα.1, K, (BrinkHowlettGroupoid cs J).inv x, ?_⟩
          intro hh
          have hh' := hh.mp hα.2.1
          change 0 < act x.val⁻¹ α at hh'
          rw [hx] at hh'
          exact lt_asymm hh' hα.2.2
        have saturated (α : S →₀ ℝ) (hα : α ∈ sN cs v) : spc cs J I α ⊆ sN cs v := by
          intro β hβ
          have hpos := hβ.2 I ((BrinkHowlettGroupoid cs J).id I)
          change (0 < act 1 α ↔ 0 < act 1 β) at hpos
          simp only [map_one, one_apply_eq_self] at hpos
          have hneg := hβ.2 K ((BrinkHowlettGroupoid cs J).inv x)
          change (0 < act x.val⁻¹ α ↔ 0 < act x.val⁻¹ β) at hneg
          rw [hx] at hneg
          refine ⟨hβ.1, hpos.mp hα.2.1, ?_⟩
          rcases cs.pos_or_neg_of_mem_geometricRoots
            ((cs.geometricRepresentation_apply_mem_geometricRoots_iff v⁻¹).2 hβ.1) with hp | hn
          · exact False.elim (lt_asymm (hneg.mpr hp) hα.2.2)
          · exact hn
        have eqpc (α : S →₀ ℝ) (hα : α ∈ sN cs v) : spc cs J I α = spc cs J I (sroot a) := by
          ext β
          constructor
          · intro hβ
            exact ⟨hβ.1, fun L f => ((hsign α hα L f).symm).trans (hβ.2 L f)⟩
          · intro hβ
            exact ⟨hβ.1, fun L f => (hsign α hα L f).trans (hβ.2 L f)⟩
        have hfamily : sclasses cs J I v = {spc cs J I (sroot a)} := by
          ext c
          constructor
          · rintro ⟨⟨α, hα, rfl⟩, hsub⟩
            have hself : α ∈ spc cs J I α := ⟨hα.1, fun _ _ => Iff.rfl⟩
            exact Set.mem_singleton_iff.mpr (eqpc α (hsub hself))
          · intro hc
            rw [Set.mem_singleton_iff.mp hc]
            exact ⟨⟨sroot a, real_of_inv _ seed, rfl⟩, saturated _ seed⟩
        refine ⟨hfamily, ?_⟩
        rw [hfamily]
        simp
      have N_eq_image (cs : CoxeterSystem M W) (v : W) :
          sN cs v = {α | α ∈ cs.geometricRoots ∧ 0 < α} ∩
            Set.image (cs.geometricRepresentation v) {α | α ∈ cs.geometricRoots ∧ α < 0} := by
        ext α
        constructor
        · rintro ⟨hr, hp, hn⟩
          exact ⟨⟨hr, hp⟩, cs.geometricRepresentation v⁻¹ α,
            ⟨(cs.geometricRepresentation_apply_mem_geometricRoots_iff _).2 hr, hn⟩,
            Representation.self_inv_apply _ _ _⟩
        · rintro ⟨⟨hr, hp⟩, β, ⟨_, hn⟩, rfl⟩
          exact ⟨hr, hp, by simpa only [Representation.inv_self_apply] using hn⟩
      intro Obj roots act parallelClass realRoot classes I a ha D hD
      let v := (SimpleWallCrossings S W M cs I.val a ha hD).1
      have hclasses : classes I v = sclasses cs J I v := by
        ext c
        change ((∃ α, realRoot I α ∧ c = parallelClass I α) ∧
          c ⊆ ({α | α ∈ roots ∧ 0 < α} ∩ Set.image (act v) {α | α ∈ roots ∧ α < 0})) ↔ _
        rw [← N_eq_image]
        rfl
      change Nat.card {c // c ∈ classes I v} = 1
      rw [hclasses]
      exact (elementary cs J I a ha hD).2
    let Obj := { L : Set S // ∃ g : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (CoxeterSystem.parabolic cs L) = CoxeterSystem.parabolic cs J }
    let roots : Set (Finsupp S Real) := CoxeterSystem.geometricRoots cs
    let act := CoxeterSystem.geometricRepresentation cs
    let parallelClass : Obj → Finsupp S Real → Set (Finsupp S Real) := fun A α =>
      { β | β ∈ roots ∧ ∀ L, ∀ f : (BrinkHowlettGroupoid cs J).Hom L A,
        (0 < act f.val α ↔ 0 < act f.val β) }
    let realRoot : Obj → Finsupp S Real → Prop := fun A α =>
      α ∈ roots ∧ ∃ L, ∃ f : (BrinkHowlettGroupoid cs J).Hom L A,
        ¬ (0 < α ↔ 0 < act f.val α)
    let classes : Obj → W → Set (Set (Finsupp S Real)) := fun A x =>
      { c | (∃ α, realRoot A α ∧ c = parallelClass A α) ∧
        c ⊆ ({ α | α ∈ roots ∧ 0 < α } ∩
          Set.image (act x) { α | α ∈ roots ∧ α < 0 }) }
    let count := fun (A : Obj) (x : W) => Nat.card { c // c ∈ classes A x }
    let component : Set S → S → Set S := fun L a =>
      { b | b ∈ Set.insert a L ∧ Relation.ReflTransGen
        (fun i j : S => i ∈ Set.insert a L ∧ j ∈ Set.insert a L ∧ i ≠ j ∧ M i j ≠ 2) a b }
    let Atom := { p : Obj × S // p.2 ∉ p.1.val ∧
      Finite (CoxeterSystem.parabolic cs (component p.1.val p.2)) }
    let crossing := fun e : Atom =>
      SimpleWallCrossings S W M cs e.val.1.val e.val.2 e.property.1 e.property.2
    let product := fun es : List Atom => (es.map (fun e => (crossing e).1)).prod
    let weight := fun es : List Atom => (es.map (fun e => cs.length (crossing e).1)).sum
    let composable := fun (es : List Atom) (A B : Set S) =>
      es.foldr (fun e tail L => L = e.val.1.val ∧ tail (crossing e).2.1)
        (fun L => L = B) A
    let N : W → Set (Finsupp S Real) := fun x =>
      {α | α ∈ roots ∧ 0 < α ∧ act x⁻¹ α < 0}
    have image_N (x : W) : N x = {α | α ∈ roots ∧ 0 < α} ∩
        Set.image (act x) {α | α ∈ roots ∧ α < 0} := by
      ext α
      constructor
      · rintro ⟨hr, hp, hn⟩
        exact ⟨⟨hr, hp⟩, act x⁻¹ α,
          ⟨(cs.geometricRepresentation_apply_mem_geometricRoots_iff _).2 hr, hn⟩,
          Representation.self_inv_apply _ _ _⟩
      · rintro ⟨⟨hr, hp⟩, β, ⟨_, hn⟩, rfl⟩
        exact ⟨hr, hp, by simpa [act] using hn⟩
    -- Parallel-root-classes step 4.1: only finiteness is needed.
    have finite_N (x : W) : Set.Finite (N x) := by
      induction hn : cs.length x using Nat.strong_induction_on generalizing x with
      | ind n ih =>
        by_cases hx : x = 1
        · subst x
          have hz : N 1 = ∅ := by
            ext α
            simp only [N, Set.mem_ofPred_eq, inv_one, map_one, one_apply_eq_self,
              Set.mem_empty_iff_false, iff_false]
            rintro ⟨_, hp, hm⟩
            exact lt_asymm hp hm
          rw [hz]
          exact Set.finite_empty
        obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one hx
        have hlen := cs.isLeftDescent_iff.1 hi
        have hf := ih (cs.length (cs.simple i * x)) (by omega) (cs.simple i * x) rfl
        apply (hf.image (M.geometricReflection i)).insert (Finsupp.single i 1) |>.subset
        intro α hα
        by_cases heq : α = Finsupp.single i 1
        · exact Or.inl heq
        · refine Or.inr ⟨M.geometricReflection i α, ?_, ?_⟩
          · refine ⟨(cs.geometricReflection_apply_mem_geometricRoots_iff i).2 hα.1,
              cs.geometricReflection_pos_of_mem_geometricRoots hα.1 hα.2.1 heq, ?_⟩
            change cs.geometricRepresentation (cs.simple i * x)⁻¹
              (M.geometricReflection i α) < 0
            rw [mul_inv_rev, cs.inv_simple, map_mul, mul_apply_eq_comp,
              cs.geometricRepresentation_simple]
            have h := LinearMap.congr_fun (M.geometricReflection_mul_self i) α
            change M.geometricReflection i (M.geometricReflection i α) = α at h
            rw [h]
            exact hα.2.2
          · have h := LinearMap.congr_fun (M.geometricReflection_mul_self i) α
            exact h
    have hfinite (A B : Obj) (x : (BrinkHowlettGroupoid cs J).Hom A B) :
        Set.Finite (classes A x.val) := by
      apply (finite_N x.val).powerset.subset
      intro c hc
      change c ⊆ N x.val
      rw [image_N]
      exact hc.2
    have pc_self (A : Obj) {α : Finsupp S Real} (hr : α ∈ roots) :
        α ∈ parallelClass A α := ⟨hr, fun _ _ => Iff.rfl⟩
    -- Parallel-root-classes steps 1.1, 2.1: full class transport in both directions.
    have pc_transport (A B : Obj) (x : (BrinkHowlettGroupoid cs J).Hom A B)
        (α : Finsupp S Real) :
        Set.image (act x.val) (parallelClass B α) = parallelClass A (act x.val α) := by
      ext β
      constructor
      · rintro ⟨γ, hγ, rfl⟩
        refine ⟨(cs.geometricRepresentation_apply_mem_geometricRoots_iff _).2 hγ.1, ?_⟩
        intro L f
        have h := hγ.2 L ((BrinkHowlettGroupoid cs J).comp f x)
        change (0 < act (f.val * x.val) α ↔ 0 < act (f.val * x.val) γ) at h
        simpa only [map_mul, mul_apply_eq_comp] using h
      · intro hβ
        refine ⟨act x.val⁻¹ β, ⟨(cs.geometricRepresentation_apply_mem_geometricRoots_iff _).2 hβ.1, ?_⟩,
          Representation.self_inv_apply _ _ _⟩
        intro L f
        have h := hβ.2 L ((BrinkHowlettGroupoid cs J).comp f
          ((BrinkHowlettGroupoid cs J).inv x))
        change (0 < act (f.val * x.val⁻¹) (act x.val α) ↔
          0 < act (f.val * x.val⁻¹) β) at h
        simpa only [map_mul, mul_apply_eq_comp, Representation.inv_self_apply] using h
    -- Parallel-root-classes step 3.1: identity and inverse tests give saturation.
    have saturated (A B : Obj) (x : (BrinkHowlettGroupoid cs J).Hom A B)
        {α : Finsupp S Real} (hα : α ∈ N x.val) : parallelClass A α ⊆ N x.val := by
      intro β hβ
      have hp := hβ.2 A ((BrinkHowlettGroupoid cs J).id A)
      have hn := hβ.2 B ((BrinkHowlettGroupoid cs J).inv x)
      change (0 < act 1 α ↔ 0 < act 1 β) at hp
      simp only [map_one, one_apply_eq_self] at hp
      have hp' : 0 < β := hp.mp hα.2.1
      have hr := (cs.geometricRepresentation_apply_mem_geometricRoots_iff x.val⁻¹).2 hβ.1
      refine ⟨hβ.1, hp', ?_⟩
      apply (cs.pos_or_neg_of_mem_geometricRoots hr).resolve_left
      intro hb
      have ha : 0 < act x.val⁻¹ α := hn.mpr hb
      exact lt_asymm ha hα.2.2
    have real_N (A B : Obj) (x : (BrinkHowlettGroupoid cs J).Hom A B)
        {α : Finsupp S Real} (hα : α ∈ N x.val) : realRoot A α := by
      refine ⟨hα.1, B, (BrinkHowlettGroupoid cs J).inv x, ?_⟩
      intro h
      exact lt_asymm (h.mp hα.2.1) hα.2.2
    have classes_image (A B : Obj) (x : (BrinkHowlettGroupoid cs J).Hom A B) :
        classes A x.val = Set.image (parallelClass A) (N x.val) := by
      ext c
      constructor
      · rintro ⟨⟨α, hr, rfl⟩, hs⟩
        exact ⟨α, (image_N x.val).symm ▸ hs (pc_self A hr.1), rfl⟩
      · rintro ⟨α, hα, rfl⟩
        exact ⟨⟨α, real_N A B x hα, rfl⟩, fun β hβ =>
          (image_N x.val) ▸ saturated A B x hα hβ⟩
    -- Compressed-additivity step 1.1: derive the reduced union using weak prefixes.
    have reduced (x y : W) (hl : cs.length (x * y) = cs.length x + cs.length y) :
        N (x * y) = N x ∪ Set.image (act x) (N y) ∧
        Disjoint (N x) (Set.image (act x) (N y)) := by
      have hprefix : N x ⊆ N (x * y) := by
        intro α hα
        exact ⟨hα.1, hα.2.1,
          ArtinNormalisers.Chamber3.rootInversions_subset_of_length_eq_add_system cs x (x * y)
            (by simpa only [inv_mul_cancel_left] using hl) α hα.1 hα.2.1 hα.2.2⟩
      have pos_transport {β : Finsupp S Real} (hβ : β ∈ N y) : 0 < act x β := by
        have hr := (cs.geometricRepresentation_apply_mem_geometricRoots_iff x).2 hβ.1
        apply (cs.pos_or_neg_of_mem_geometricRoots hr).resolve_right
        intro hn
        have hn' : -act x β ∈ N x := by
          refine ⟨(cs.neg_mem_geometricRoots_iff).2 hr, neg_pos.mpr hn, ?_⟩
          simpa [act] using (neg_neg_iff_pos.mpr hβ.2.1 : -β < 0)
        have h := (hprefix hn').2.2
        have hh : act (x * y)⁻¹ (-act x β) = -act y⁻¹ β := by
          simp [act, mul_inv_rev, map_mul, mul_apply_eq_comp]
        rw [hh] at h
        exact lt_asymm (neg_pos.mpr hβ.2.2) h
      constructor
      · ext α
        constructor
        · intro hα
          have hr := (cs.geometricRepresentation_apply_mem_geometricRoots_iff x⁻¹).2 hα.1
          rcases cs.pos_or_neg_of_mem_geometricRoots hr with hp | hn
          · right
            refine ⟨act x⁻¹ α, ⟨hr, hp, ?_⟩, Representation.self_inv_apply _ _ _⟩
            have h := hα.2.2
            simpa only [act, mul_inv_rev, map_mul, mul_apply_eq_comp] using h
          · exact Or.inl ⟨hα.1, hα.2.1, hn⟩
        · rintro (hα | ⟨β, hβ, rfl⟩)
          · exact hprefix hα
          · refine ⟨(cs.geometricRepresentation_apply_mem_geometricRoots_iff _).2 hβ.1,
              pos_transport hβ, ?_⟩
            simpa [act, mul_inv_rev, map_mul, mul_apply_eq_comp] using hβ.2.2
      · apply Set.disjoint_left.mpr
        rintro α hα ⟨β, hβ, rfl⟩
        have h := hα.2.2
        have hh : act x⁻¹ (act x β) = β := Representation.inv_self_apply _ _ _
        rw [hh] at h
        exact lt_asymm hβ.2.1 h
    -- Compressed-additivity step 2.1: disjoint finite families and injective transport.
    have hadd (A B D : Obj) (x : (BrinkHowlettGroupoid cs J).Hom A B)
        (y : (BrinkHowlettGroupoid cs J).Hom B D)
        (hl : cs.length (x.val * y.val) = cs.length x.val + cs.length y.val) :
        count A (x.val * y.val) = count A x.val + count B y.val := by
      let z := (BrinkHowlettGroupoid cs J).comp x y
      let tr : Set (Finsupp S Real) → Set (Finsupp S Real) := Set.image (act x.val)
      have hu : classes A (x.val * y.val) = classes A x.val ∪ tr '' classes B y.val := by
        have hz : z.val = x.val * y.val := rfl
        have hc := classes_image A D z
        rw [hz] at hc
        rw [hc, classes_image A B x, classes_image B D y]
        change parallelClass A '' N (x.val * y.val) = _
        rw [(reduced x.val y.val hl).1, Set.image_union]
        congr 1
        ext c
        constructor
        · rintro ⟨α, ⟨β, hβ, rfl⟩, rfl⟩
          exact ⟨parallelClass B β, ⟨β, hβ, rfl⟩, pc_transport A B x β⟩
        · rintro ⟨_, ⟨β, hβ, rfl⟩, rfl⟩
          exact ⟨act x.val β, ⟨β, hβ, rfl⟩, (pc_transport A B x β).symm⟩
      have hd : Disjoint (classes A x.val) (tr '' classes B y.val) := by
        apply Set.disjoint_left.mpr
        rintro c hc ⟨d, hd, hdc⟩
        rw [classes_image B D y] at hd
        obtain ⟨β, hβ, rfl⟩ := hd
        have hm : act x.val β ∈ c := hdc ▸ Set.mem_image_of_mem _ (pc_self B hβ.1)
        have hn : act x.val β ∈ N x.val := (image_N x.val).symm ▸ hc.2 hm
        exact Set.disjoint_left.mp (reduced x.val y.val hl).2 hn ⟨β, hβ, rfl⟩
      have hi : Function.Injective tr :=
        (Representation.apply_bijective act x.val).1.image_injective
      change (classes A (x.val * y.val)).ncard = (classes A x.val).ncard + (classes B y.val).ncard
      rw [hu, Set.ncard_union_eq hd (hfinite A B x) ((hfinite B D y).image tr),
        Set.ncard_image_of_injective _ hi]
    -- Factor-count step 2.1, empty case.
    have one_count (A : Obj) : count A 1 = 0 := by
      have hempty : classes A 1 = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro c hc
        obtain ⟨⟨α, hα, rfl⟩, hsub⟩ := hc
        have hself : α ∈ parallelClass A α := ⟨hα.1, fun _ _ => Iff.rfl⟩
        obtain ⟨hpos, β, hβ, heq⟩ := hsub hself
        have heq' : β = α := by simpa [act] using heq
        subst β
        exact (not_lt_of_ge hpos.2.le) hβ.2
      simp [count, hempty]
    -- Step 1.2: subadditivity bounds every suffix product.
    have weight_bound (es : List Atom) : cs.length (product es) ≤ weight es := by
      induction es with
      | nil => simp [product, weight]
      | cons e es ih =>
        change cs.length ((crossing e).1 * product es) ≤ cs.length (crossing e).1 + weight es
        exact (cs.length_mul_le _ _).trans (Nat.add_le_add_left ih _)
    -- Steps 1.2 and 2.1, integrated through suffix induction.
    have word_count : ∀ (es : List Atom) (A B : Obj)
        (f : (BrinkHowlettGroupoid cs J).Hom A B),
        composable es A.val B.val → product es = f.val →
        cs.length f.val = weight es → es.length = count A f.val := by
      intro es
      induction es with
      | nil =>
        intro A B f hc hp hl
        have hf : f.val = 1 := hp.symm
        simpa [hf] using (one_count A).symm
      | cons e es ih =>
        intro A B f hc hp hl
        change A.val = e.val.1.val ∧ composable es (crossing e).2.1 B.val at hc
        have hAe : A = e.val.1 := Subtype.ext hc.1
        subst A
        obtain ⟨htarget, x, hx⟩ := ElementaryWallMorphism cs J e.val.1.val
          e.val.1.property e.val.2 e.property.1 e.property.2
        have hx' : x.val = (crossing e).1 := hx
        let T : Obj := ⟨(crossing e).2.1, htarget⟩
        change (BrinkHowlettGroupoid cs J).Hom e.val.1 T at x
        let y : (BrinkHowlettGroupoid cs J).Hom T B :=
          (BrinkHowlettGroupoid cs J).comp ((BrinkHowlettGroupoid cs J).inv x) f
        have hy : y.val = product es := by
          change x.val⁻¹ * f.val = product es
          change (crossing e).1 * product es = f.val at hp
          rw [hx, ← hp, inv_mul_cancel_left]
        have hf : f.val = x.val * y.val := by
          change f.val = x.val * (x.val⁻¹ * f.val)
          simp
        have hlen : cs.length (x.val * y.val) = cs.length x.val + cs.length y.val := by
          have hb := weight_bound es
          have hm := cs.length_mul_le x.val y.val
          change cs.length f.val = cs.length (crossing e).1 + weight es at hl
          rw [← hf, hx'] at hm
          rw [← hy] at hb
          rw [← hf, hx']
          omega
        have htail : cs.length y.val = weight es := by
          change cs.length f.val = cs.length (crossing e).1 + weight es at hl
          rw [hf, hlen, hx'] at hl
          omega
        have hrec := ih T B y hc.2 hy.symm htail
        have hxcount : count e.val.1 x.val = 1 := by
          rw [hx]
          exact hsingle e.val.1 e.val.2 e.property.1 e.property.2
        have hsum : count e.val.1 f.val = count e.val.1 x.val + count T y.val := by
          rw [hf]
          exact hadd e.val.1 T B x y hlen
        simp only [List.length_cons]
        omega
    refine ⟨hexists I K w, hfinite I K w, ?_⟩
    intro e
    exact word_count e.val I K w e.property.1 e.property.2.1 e.property.2.2)
