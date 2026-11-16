import Mathlib
import ArtinDeligne
import Proofs.StandardExpressions
import Proofs.StandardFactorCount
import Proofs.GeneratorsAndStandardLength
import Proofs.TwoGeneratorMinimal
import Proofs.AtomicBraidRelations

set_option maxHeartbeats 2000000

theorem AtomicMatsumoto : (∀ {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) (I K : { L : Set S // ∃ g : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (CoxeterSystem.parabolic cs L) = CoxeterSystem.parabolic cs J }) (w : (BrinkHowlettGroupoid cs J).Hom I K) (e f : StandardExpressions cs J I K w), Relation.ReflTransGen (AtomicBraidRelations cs J) e.val f.val) :=
(by
  intro S W inst M cs J
  classical
  have commonPrefixFinite : let Obj := {L : Set S // ∃ g : W,
      (cs.parabolic L).map (MulAut.conj g).toMonoidHom = cs.parabolic J}
    let component := fun (L : Set S) (c : S) =>
      {d | d ∈ Set.insert c L ∧ Relation.ReflTransGen
        (fun i j : S => i ∈ Set.insert c L ∧ j ∈ Set.insert c L ∧ i ≠ j ∧ M i j ≠ 2) c d}
    let parabolicRoots := fun (L : Set S) =>
      {α | ∃ u : W, u ∈ cs.parabolic L ∧ ∃ i ∈ L,
        cs.geometricRepresentation u (Finsupp.single i (1 : ℝ)) = α}
    let leftDiv := fun u v : W => cs.length v = cs.length u + cs.length (u⁻¹ * v)
    ∀ (I K : Obj) (w : (BrinkHowlettGroupoid cs J).Hom I K)
      (a b : S) (ha : a ∉ I.val) (hb : b ∉ I.val), a ≠ b →
      ∀ (hDa : Finite (cs.parabolic (component I.val a)))
        (hDb : Finite (cs.parabolic (component I.val b))),
      leftDiv (SimpleWallCrossings S W M cs I.val a ha hDa).1 w.val →
      leftDiv (SimpleWallCrossings S W M cs I.val b hb hDb).1 w.val →
      Set.Finite (parabolicRoots (Set.insert a (Set.insert b I.val)) \ parabolicRoots I.val) := by
    /- Inspiration: main portal step 3.1:
    https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-thm-atomic-matsumoto-artin-tits-normalisers
    Derive the finite relative-root condition from the actual common prefixes.
    All support arguments use finite supports; no rank or type restriction enters.
    Inverse orientation is essential: w^-1 takes the simple roots of I to K.
    Recovered local blocks below come from the completed TwoGeneratorMinimal proof,
    not exported declarations. The defective auxiliary characterization after (3.15)
    is unused; retain the longest-element construction and its proved inversion formula.
    Exact report finding:
    https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects#pdf-wall-root-characterisation
    Evidence and disposition: article printed p.10, paragraph after (3.15),
    https://arxiv.org/pdf/2509.21915#page=10. In rank one I=K=empty,
    v_(a,I)=s_a sends alpha_a to -alpha_a, while Phi_K^- is empty.
    Discard that auxiliary inclusion and use definition (3.14) with the proved
    inversion formula below. The accepted endpoint is unchanged.
    Parent article: Theorem 4.21, https://arxiv.org/pdf/2509.21915#page=20. -/
    classical
    have f29 (cs : CoxeterSystem M W) (L : Set S) (z : cs.parabolic L)
        (hz : ∀ u : cs.parabolic L, cs.length (u : W) ≤ cs.length (z : W)) :
        (∀ u : W, u ∈ cs.parabolic L → cs.length ((z : W) * u) + cs.length u = cs.length z) ∧
        (z : W) * z = 1 ∧ ∃ e : L ≃ L, Function.Involutive e ∧
          (∀ i : L, cs.geometricRepresentation (z : W) (Finsupp.single (i : S) 1) =
            -Finsupp.single (e i : S) 1) ∧
          (∀ i : L, (z : W) * cs.simple (i : S) * (z : W)⁻¹ = cs.simple (e i : S)) := by
      clear * - S W inst M cs J L z hz
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
      exact ⟨len, zz, e, hinv, hf, hg⟩
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
    have oppositionWork (cs : CoxeterSystem M W) (L : Set S) (z : cs.parabolic L)
        (hz : ∀ u : cs.parabolic L, cs.length (u : W) ≤ cs.length (z : W)) :
        (z : W) * z = 1 ∧ ∃ e : L ≃ L, Function.Involutive e ∧
          (∀ i : L, cs.geometricRepresentation (z : W) (Finsupp.single (i : S) 1) =
            -Finsupp.single (e i : S) 1) ∧
          (∀ i : L, (z : W) * cs.simple (i : S) * (z : W)⁻¹ = cs.simple (e i : S)) := by
      exact (f29 cs L z hz).2
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
    have ElementaryRootInversions : (∀ (cs : CoxeterSystem M W) (I : Set S) (a : S) (ha : a ∉ I),
    let component : Set S → S → Set S := fun L c =>
      {d | d ∈ Set.insert c L ∧ Relation.ReflTransGen
        (fun i j : S => i ∈ Set.insert c L ∧ j ∈ Set.insert c L ∧ i ≠ j ∧ M i j ≠ 2) c d}
    let parabolicRoots : Set S → Set (Finsupp S Real) := fun L =>
      {α | ∃ u : W, u ∈ cs.parabolic L ∧ ∃ i : S, i ∈ L ∧
        cs.geometricRepresentation u (Finsupp.single i (1 : Real)) = α}
    let positiveRoots : Set (Finsupp S Real) := {α | α ∈ cs.geometricRoots ∧ 0 < α}
    let negativeRoots : Set (Finsupp S Real) := {α | α ∈ cs.geometricRoots ∧ α < 0}
    let N : W → Set (Finsupp S Real) := fun x =>
      positiveRoots ∩ Set.image (cs.geometricRepresentation x) negativeRoots
    ∀ hD : Finite (cs.parabolic (component I a)),
      N (SimpleWallCrossings S W M cs I a ha hD).1 =
        (parabolicRoots (Set.insert a I) ∩ positiveRoots) \ (parabolicRoots I ∩ positiveRoots)) := by
      intro cs I a ha
      let component : Set S → S → Set S := fun L c =>
        {d | d ∈ Set.insert c L ∧ Relation.ReflTransGen
          (fun i j : S => i ∈ Set.insert c L ∧ j ∈ Set.insert c L ∧ i ≠ j ∧ M i j ≠ 2) c d}
      change ∀ hD : Finite (cs.parabolic (component I a)), _
      intro hD
      let T := Set.insert a I
      let D := component I a
      have hIT : I ⊆ T := Set.subset_insert a I
      have hDT : D ⊆ T := fun i hi => hi.1
      have haD : a ∈ D := ⟨Or.inl rfl, Relation.ReflTransGen.refl⟩
      have hrest : T \ D ⊆ I := by
        rintro i ⟨hi, hni⟩
        rcases hi with rfl | hi
        · exact False.elim (hni haD)
        · exact hi
      have hsep : ∀ i ∈ D, ∀ j ∈ T \ D, M i j = 2 := by
        intro i hi j hj
        by_contra hm
        have hij : i ≠ j := fun he => hj.2 (he ▸ hi)
        exact hj.2 ⟨hj.1, Relation.ReflTransGen.tail hi.2 ⟨hi.1, hj.1, hij, hm⟩⟩
      have hDI : D ∩ I = D \ {a} := by
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
      let jI : cs.parabolic (D ∩ I) := ⟨j.val, by rw [hDI]; exact j.property⟩
      have hdmax := pick_max D (fun _ h => h)
      have hjmax : ∀ u : cs.parabolic (D ∩ I), cs.length u.val ≤ cs.length jI.val := by
        intro u
        exact pick_max (D \ {a}) Set.sdiff_subset ⟨u.val, hDI ▸ u.property⟩
      obtain ⟨F, hFT, hconj, hroot, hN⟩ :=
        SphericalSupportRelativeLongest cs I T D hIT hDT hrest hsep hD d jI hdmax hjmax
      have hdInv : d.val⁻¹ = d.val := inv_eq_of_mul_eq_one_left (oppositionWork cs D d hdmax).1
      have hjInv : jI.val⁻¹ = jI.val := inv_eq_of_mul_eq_one_left
        (oppositionWork cs (D ∩ I) jI hjmax).1
      have heq : (SimpleWallCrossings S W M cs I a ha hD).1 = (d.val * jI.val)⁻¹ := by
        rw [mul_inv_rev, hdInv, hjInv]
        rfl
      rw [heq]
      exact hN
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
    let Obj := {L : Set S // ∃ g : W,
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (cs.parabolic L) = cs.parabolic J}
    let component : Set S → S → Set S := fun L c =>
      {d | d ∈ Set.insert c L ∧ Relation.ReflTransGen
        (fun i j : S => i ∈ Set.insert c L ∧ j ∈ Set.insert c L ∧ i ≠ j ∧ M i j ≠ 2) c d}
    let parabolicRoots : Set S → Set (Finsupp S Real) := fun L =>
      {α | ∃ u : W, u ∈ cs.parabolic L ∧ ∃ i : S, i ∈ L ∧
        cs.geometricRepresentation u (Finsupp.single i (1 : Real)) = α}
    let positiveRoots : Set (Finsupp S Real) := {α | α ∈ cs.geometricRoots ∧ 0 < α}
    let negativeRoots : Set (Finsupp S Real) := {α | α ∈ cs.geometricRoots ∧ α < 0}
    let N : W → Set (Finsupp S Real) := fun x =>
      positiveRoots ∩ Set.image (cs.geometricRepresentation x) negativeRoots
    let leftDiv : W → W → Prop := fun u v =>
      cs.length v = cs.length u + cs.length (u⁻¹ * v)
    change ∀ (I K : Obj) (w : (BrinkHowlettGroupoid cs J).Hom I K)
      (a b : S) (ha : a ∉ I.val) (hb : b ∉ I.val), a ≠ b →
      ∀ (hDa : Finite (cs.parabolic (component I.val a)))
        (hDb : Finite (cs.parabolic (component I.val b))),
      leftDiv (SimpleWallCrossings S W M cs I.val a ha hDa).1 w.val →
      leftDiv (SimpleWallCrossings S W M cs I.val b hb hDb).1 w.val →
      Set.Finite (parabolicRoots (Set.insert a (Set.insert b I.val)) \ parabolicRoots I.val)
    intro I K' w a b ha hb hab hDa hDb hwa hwb
    let va := (SimpleWallCrossings S W M cs I.val a ha hDa).1
    let vb := (SimpleWallCrossings S W M cs I.val b hb hDb).1
    have image_N (x : W) (α : Finsupp S Real) :
        α ∈ N x ↔ α ∈ cs.geometricRoots ∧ 0 < α ∧ cs.geometricRepresentation x⁻¹ α < 0 := by
      constructor
      · rintro ⟨hp, β, hn, rfl⟩
        exact ⟨hp.1, hp.2, by simpa only [Representation.inv_self_apply] using hn.2⟩
      · rintro ⟨hr, hp, hn⟩
        refine ⟨⟨hr, hp⟩, cs.geometricRepresentation x⁻¹ α,
          ⟨(cs.geometricRepresentation_apply_mem_geometricRoots_iff x⁻¹).mpr hr, hn⟩, ?_⟩
        exact Representation.self_inv_apply _ _ _
    have hNa : N va = (parabolicRoots (Set.insert a I.val) ∩ positiveRoots) \
        (parabolicRoots I.val ∩ positiveRoots) :=
      ElementaryRootInversions cs I.val a ha hDa
    have hNb : N vb = (parabolicRoots (Set.insert b I.val) ∩ positiveRoots) \
        (parabolicRoots I.val ∩ positiveRoots) :=
      ElementaryRootInversions cs I.val b hb hDb
    have prefix_N {u v : W} (h : leftDiv u v) : N u ⊆ N v := by
      intro x hx
      obtain ⟨hr, hp, hn⟩ := (image_N u x).mp hx
      exact (image_N v x).mpr ⟨hr, hp,
        ArtinNormalisers.Chamber3.rootInversions_subset_of_length_eq_add_system cs u v h x hr hp hn⟩
    have seed (c : S) (hc : c ∉ I.val) (v : W)
        (hNv : N v = (parabolicRoots (Set.insert c I.val) ∩ positiveRoots) \
          (parabolicRoots I.val ∩ positiveRoots)) (hv : leftDiv v w.val) :
        cs.geometricRepresentation w.val⁻¹ (Finsupp.single c (1 : ℝ)) < 0 := by
      have hr : Finsupp.single c (1 : ℝ) ∈ cs.geometricRoots := ⟨1, c, by simp⟩
      have hp : 0 < Finsupp.single c (1 : ℝ) := by
        exact lt_of_le_of_ne (Finsupp.single_nonneg.mpr (by norm_num)) (by intro he; have hh := congrArg (fun z : S →₀ ℝ => z c) he; simp at hh)
      have hmem : Finsupp.single c (1 : ℝ) ∈ N v := by
        rw [hNv]
        refine ⟨⟨⟨1, (cs.parabolic _).one_mem, c, Or.inl rfl, by simp⟩, hr, hp⟩, ?_⟩
        intro hh
        have hz := supported cs I.val hh.1 c hc
        simp at hz
      exact ((image_N w.val _).mp (prefix_N hv hmem)).2.2
    have han := seed a ha va hNa hwa
    have hbn := seed b hb vb hNb hwb
    let act := cs.geometricRepresentation
    let root : S → S →₀ ℝ := fun i => Finsupp.single i 1
    have hw : act w.val '' piRoots K'.val = piRoots I.val := w.property
    have hinv := inverse_image w.val K'.val I.val hw
    have neg_outside (c : S) (hc : c ∉ I.val) (hcneg : act w.val⁻¹ (root c) < 0) :
        ∃ k, k ∉ K'.val ∧ act w.val⁻¹ (root c) k < 0 := by
      have hn : ¬ ∀ k, k ∉ K'.val → act w.val⁻¹ (root c) k = 0 := by
        intro hz
        have hh := image_support w.val K'.val I.val hw _ hz c hc
        rw [Representation.self_inv_apply] at hh
        simp [root] at hh
      obtain ⟨k, hk⟩ := not_forall.mp hn
      obtain ⟨hk, hne⟩ := not_imp.mp hk
      exact ⟨k, hk, lt_of_le_of_ne (hcneg.le k) hne⟩
    have positive_inclusion :
        {x | x ∈ parabolicRoots (Set.insert a (Set.insert b I.val)) ∧
          x ∉ parabolicRoots I.val ∧ 0 < x} ⊆
        {x | x ∈ cs.geometricRoots ∧ 0 < x ∧ act w.val⁻¹ x < 0} := by
      rintro x ⟨hxT, hnI, hp⟩
      have hr : x ∈ cs.geometricRoots := by
        obtain ⟨u, hu, i, hi, he⟩ := hxT
        exact ⟨u, i, he⟩
      have habpos : 0 < x a ∨ 0 < x b := by
        by_contra hn
        push_neg at hn
        have hxa : x a = 0 := le_antisymm hn.1 (hp.le a)
        have hxb : x b = 0 := le_antisymm hn.2 (hp.le b)
        apply hnI
        apply positive_supported_root_mem_parabolic I.val x hr hp
        intro k hk
        by_cases hka : k = a
        · subst k; exact hxa
        by_cases hkb : k = b
        · subst k; exact hxb
        exact supported cs (Set.insert a (Set.insert b I.val)) hxT k (by
          rintro (he | he | hi)
          · exact hka he
          · exact hkb he
          · exact hk hi)
      let t := x - x a • root a - x b • root b
      have ht : ∀ k, k ∉ I.val → t k = 0 := by
        intro k hk
        by_cases hka : k = a
        · subst k
          simp [t, root, Finsupp.single_apply, hab]
        by_cases hkb : k = b
        · subst k
          simp [t, root, Finsupp.single_apply, hab.symm]
        have hz := supported cs (Set.insert a (Set.insert b I.val)) hxT k (by
          rintro (he | he | hi)
          · exact hka he
          · exact hkb he
          · exact hk hi)
        simp [t, root, hz, Finsupp.single_apply, hka, hkb]
      have coord (k : S) (hk : k ∉ K'.val) :
          act w.val⁻¹ x k = x a * act w.val⁻¹ (root a) k + x b * act w.val⁻¹ (root b) k := by
        have hh := image_support w.val⁻¹ I.val K'.val hinv t ht k hk
        dsimp only [t] at hh
        simp only [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply,
          Pi.smul_apply, smul_eq_mul] at hh
        linarith
      have hnegcoord : ∃ k, act w.val⁻¹ x k < 0 := by
        rcases habpos with hxa | hxb
        · obtain ⟨k, hk, hak⟩ := neg_outside a ha han
          refine ⟨k, ?_⟩
          rw [coord k hk]
          have hlt := mul_neg_of_pos_of_neg hxa hak
          have hle := mul_nonpos_of_nonneg_of_nonpos (hp.le b) (hbn.le k)
          linarith
        · obtain ⟨k, hk, hbk⟩ := neg_outside b hb hbn
          refine ⟨k, ?_⟩
          rw [coord k hk]
          have hlt := mul_neg_of_pos_of_neg hxb hbk
          have hle := mul_nonpos_of_nonneg_of_nonpos (hp.le a) (han.le k)
          linarith
      have hneg : act w.val⁻¹ x < 0 := by
        rcases cs.pos_or_neg_of_mem_geometricRoots
          ((cs.geometricRepresentation_apply_mem_geometricRoots_iff _).mpr hr) with hpos | hneg
        · obtain ⟨k, hk⟩ := hnegcoord
          exact False.elim ((hpos.le k).not_gt hk)
        · exact hneg
      exact ⟨hr, hp, hneg⟩
  
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
  
    have hposfin : Set.Finite
        {x | x ∈ parabolicRoots (Set.insert a (Set.insert b I.val)) ∧
          x ∉ parabolicRoots I.val ∧ 0 < x} :=
      (finiteInv cs w.val⁻¹).subset positive_inclusion
    have root_neg (L : Set S) (x : S →₀ ℝ) (hx : x ∈ parabolicRoots L) :
        -x ∈ parabolicRoots L := by
      obtain ⟨u, hu, i, hi, he⟩ := hx
      refine ⟨u * cs.simple i, mul_mem hu (cs.simple_mem_parabolic hi), i, hi, ?_⟩
      rw [map_mul, mul_apply_eq_comp, cs.geometricRepresentation_simple,
        M.geometricReflection_apply_single_self, map_neg, he]
    apply (hposfin.union (hposfin.image (fun x => -x))).subset
    rintro x ⟨hxT, hxI⟩
    have hr : x ∈ cs.geometricRoots := by
      obtain ⟨u, hu, i, hi, he⟩ := hxT
      exact ⟨u, i, he⟩
    rcases cs.pos_or_neg_of_mem_geometricRoots hr with hp | hn
    · exact Or.inl ⟨hxT, hxI, hp⟩
    · apply Or.inr
      refine ⟨-x, ⟨root_neg _ _ hxT, ?_, neg_pos.mpr hn⟩, neg_neg x⟩
      intro hh
      exact hxI (by simpa only [neg_neg] using root_neg _ _ hh)

  let Obj := { L : Set S // ∃ g : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g))
      (cs.parabolic L) = cs.parabolic J }
  let component : Set S → S → Set S := fun L a =>
    { b | b ∈ Set.insert a L ∧ Relation.ReflTransGen
      (fun i j : S => i ∈ Set.insert a L ∧ j ∈ Set.insert a L ∧ i ≠ j ∧ M i j ≠ 2) a b }
  let Atom := { p : Obj × S // p.2 ∉ p.1.val ∧ Finite (cs.parabolic (component p.1.val p.2)) }
  let crossing := fun t : Atom => SimpleWallCrossings S W M cs t.val.1.val t.val.2 t.property.1 t.property.2
  let Comp := fun (es : List Atom) (I K : Set S) =>
    List.foldr (fun t tail L => L = t.val.1.val ∧ tail (crossing t).2.1) (fun L => L = K) es I
  let word := fun es : List Atom => (es.map (fun t => (crossing t).1)).prod
  let weight := fun es : List Atom => (es.map (fun t => cs.length (crossing t).1)).sum
  let leftDiv := fun u v : W => cs.length v = cs.length u + cs.length (u⁻¹ * v)
  let parabolicRoots := fun L : Set S => {α | ∃ u : W, u ∈ cs.parabolic L ∧ ∃ i : S, i ∈ L ∧ cs.geometricRepresentation u (Finsupp.single i (1 : ℝ)) = α}
  have word_length_le (es : List (Atom)) : cs.length (word es) ≤ weight es := by
    induction es with
    | nil => simp [word, weight, cs.length_one]
    | cons t es ih =>
      change cs.length ((crossing t).1 * word es) ≤
        cs.length (crossing t).1 + weight es
      exact (cs.length_mul_le _ _).trans (Nat.add_le_add_left ih _)
  
  have comp_append (es fs : List (Atom)) (L F G : Set S)
      (hes : Comp es L F) (hfs : Comp fs F G) :
      Comp (es ++ fs) L G := by
    induction es generalizing L with
    | nil =>
      change L = F at hes
      subst L
      exact hfs
    | cons e es ih => exact ⟨hes.1, ih _ hes.2⟩
  
  /- Steps 2.1 and 4.1: extract a typed residual arrow. Its source is the
  prescribed crossing target. The whole-word equality and the triangle
  inequality force tail additivity; no tail additivity premise is used. -/
  have suffix (I K : Obj) (w : (BrinkHowlettGroupoid cs J).Hom I K)
      (e : StandardExpressions cs J I K w) (t : Atom) (es : List (Atom))
      (he : e.val = t :: es) :
      ∃ (L : Obj) (z : (BrinkHowlettGroupoid cs J).Hom L K),
        L.val = (crossing t).2.1 ∧
        z.val = (crossing t).1⁻¹ * w.val ∧
        ∃ ez : StandardExpressions cs J L K z, ez.val = es := by
    have hc : Comp (t :: es) I.val K.val := by
      have hc0 : Comp e.val I.val K.val := e.property.1
      rw [he] at hc0
      exact hc0
    have hp : (crossing t).1 * word es = w.val := by
      have hp0 : word e.val = w.val := e.property.2.1
      rw [he] at hp0
      exact hp0
    have hl : cs.length w.val = cs.length (crossing t).1 + weight es := by
      have hl0 : cs.length w.val = weight e.val := e.property.2.2
      rw [he] at hl0
      exact hl0
    have hI : I = t.val.1 := Subtype.ext hc.1
    obtain ⟨hL, v0, hv0⟩ := ElementaryWallMorphism cs J t.val.1.val
      t.val.1.property t.val.2 t.property.1 t.property.2
    let L : Obj := ⟨(crossing t).2.1, hL⟩
    let v : (BrinkHowlettGroupoid cs J).Hom I L := by
      cases hI
      exact v0
    have hv : v.val = (crossing t).1 := by
      cases hI
      exact hv0
    let z : (BrinkHowlettGroupoid cs J).Hom L K :=
      (BrinkHowlettGroupoid cs J).comp ((BrinkHowlettGroupoid cs J).inv v) w
    have hz : z.val = (crossing t).1⁻¹ * w.val := by
      change v.val⁻¹ * w.val = _
      rw [hv]
    have hzp : z.val = word es := by rw [hz, ← hp, inv_mul_cancel_left]
    have hle := word_length_le es
    have htri := cs.length_mul_le (crossing t).1 (word es)
    rw [hp] at htri
    have htail : cs.length z.val = weight es := by
      rw [hzp]
      omega
    refine ⟨L, z, rfl, hz, ⟨es, ?_, hzp.symm, htail⟩, rfl⟩
    exact hc.2
  
  /- Same head means the same target object and the same residual label.
  Proof-irrelevant subtype equality handles the dependent arrow type. -/
  have same_head (I K : Obj) (w : (BrinkHowlettGroupoid cs J).Hom I K)
      (e f : StandardExpressions cs J I K w) (t : Atom)
      (es fs : List (Atom)) (he : e.val = t :: es) (hf : f.val = t :: fs) :
      ∃ (L : Obj) (z : (BrinkHowlettGroupoid cs J).Hom L K)
        (ez fz : StandardExpressions cs J L K z), ez.val = es ∧ fz.val = fs := by
    obtain ⟨L, z, hL, hz, ez, hez⟩ := suffix I K w e t es he
    obtain ⟨L', z', hL', hz', fz, hfz⟩ := suffix I K w f t fs hf
    have hLL : L' = L := Subtype.ext (hL'.trans hL.symm)
    subst L'
    have hzz : z' = z := Subtype.ext (hz'.trans hz.symm)
    subst z'
    exact ⟨L, z, ez, fz, hez, hfz⟩
  
  /- Remark 4.14; the endpoint-threading routine above reuses the completed
  Proofs/TwoGeneratorMinimal.lean comp_append block (lines 1875ff). -/
  have concatenate (I L K : Obj)
      (x : (BrinkHowlettGroupoid cs J).Hom I L)
      (y : (BrinkHowlettGroupoid cs J).Hom L K)
      (w : (BrinkHowlettGroupoid cs J).Hom I K)
      (ex : StandardExpressions cs J I L x) (ey : StandardExpressions cs J L K y)
      (hp : x.val * y.val = w.val)
      (hl : cs.length w.val = cs.length x.val + cs.length y.val) :
      ∃ ew : StandardExpressions cs J I K w, ew.val = ex.val ++ ey.val := by
    refine ⟨⟨ex.val ++ ey.val, ?_, ?_, ?_⟩, rfl⟩
    · exact comp_append ex.val ey.val I.val L.val K.val ex.property.1 ey.property.1
    · simpa only [List.map_append, List.prod_append, ex.property.2.1, ey.property.2.1] using hp
    · simpa only [List.map_append, List.sum_append, ← ex.property.2.2, ← ey.property.2.2] using hl
  
  have head_prefix (I K : Obj) (w : (BrinkHowlettGroupoid cs J).Hom I K)
      (e : StandardExpressions cs J I K w) (t : Atom) (es : List (Atom))
      (he : e.val = t :: es) :
      I = t.val.1 ∧ cs.length w.val = cs.length (crossing t).1 +
        cs.length ((crossing t).1⁻¹ * w.val) := by
    have hc : Comp (t :: es) I.val K.val := by
      have hc0 : Comp e.val I.val K.val := e.property.1
      rw [he] at hc0
      exact hc0
    obtain ⟨L, z, _, hz, ez, hez⟩ := suffix I K w e t es he
    have hl : cs.length w.val = cs.length (crossing t).1 + weight es := by
      have hl0 : cs.length w.val = weight e.val := e.property.2.2
      rw [he] at hl0
      exact hl0
    have htail : cs.length z.val = weight es := by
      have htail0 : cs.length z.val = weight ez.val := ez.property.2.2
      rw [hez] at htail0
      exact htail0
    exact ⟨Subtype.ext hc.1, by rw [← hz, htail]; exact hl⟩
  
  have liftHead : ∀ (I K : Obj) (t : Atom) (es fs : List Atom),
    Comp (t :: es) I.val K.val → Relation.ReflTransGen (AtomicBraidRelations cs J) es fs → Relation.ReflTransGen (AtomicBraidRelations cs J) (t :: es) (t :: fs) := by
    let Moves := Relation.ReflTransGen (AtomicBraidRelations cs J)
    have appendComp (xs ys : List (Atom)) (A B : Set S) :
        Comp (xs ++ ys) A B ↔
          ∃ C, Comp xs A C ∧ Comp ys C B := by
      induction xs generalizing A with
      | nil =>
        change Comp ys A B ↔ ∃ C, A = C ∧ Comp ys C B
        exact ⟨fun h => ⟨A, rfl, h⟩, fun ⟨C, h, hc⟩ => h.symm ▸ hc⟩
      | cons x xs ih =>
        change (A = x.val.1.val ∧ Comp (xs ++ ys) (crossing x).2.1 B) ↔ _
        rw [ih]
        constructor
        · rintro ⟨h, C, hc, hd⟩
          exact ⟨C, ⟨h, hc⟩, hd⟩
        · rintro ⟨C, ⟨h, hc⟩, hd⟩
          exact ⟨h, C, hc, hd⟩
    have targetUnique (xs : List (Atom)) : ∀ A B C,
        Comp xs A B → Comp xs A C → B = C := by
      induction xs with
      | nil =>
        intro A B C h h'
        exact h.symm.trans h'
      | cons x xs ih =>
        intro A B C h h'
        exact ih _ _ _ h.2 h'.2
    have endpoints (xs : List (Atom)) (hn : xs ≠ [])
        (A B C D : Set S) (h : Comp xs A B) (h' : Comp xs C D) :
        A = C ∧ B = D := by
      cases xs with
      | nil => exact (hn rfl).elim
      | cons x xs =>
        exact ⟨h.1.trans h'.1.symm, targetUnique xs _ _ _ h.2 h'.2⟩
    have typedPair (u v : List (Atom)) (L H : Obj)
        (hu : Comp u L.val H.val) (hv : Comp v L.val H.val)
        (hnu : u ≠ []) (hnv : v ≠ []) :
        ∀ A B, Comp u A B ↔ Comp v A B := by
      intro A B
      constructor
      · intro h
        obtain ⟨rfl, rfl⟩ := endpoints u hnu A B L.val H.val h hu
        exact hv
      · intro h
        obtain ⟨rfl, rfl⟩ := endpoints v hnv A B L.val H.val h hv
        exact hu
    have replaceComp (pre u v post : List (Atom))
        (h : ∀ A B, Comp u A B ↔ Comp v A B) (A B : Set S) :
        Comp (pre ++ u ++ post) A B ↔ Comp (pre ++ v ++ post) A B := by
      simp only [appendComp]
      constructor
      · rintro ⟨C, ⟨D, hp, hu⟩, ht⟩
        exact ⟨C, ⟨D, hp, (h D C).mp hu⟩, ht⟩
      · rintro ⟨C, ⟨D, hp, hv⟩, ht⟩
        exact ⟨C, ⟨D, hp, (h D C).mpr hv⟩, ht⟩
    have moveComp (es fs : List (Atom)) (hm : AtomicBraidRelations cs J es fs) :
        ∀ A B, Comp es A B ↔ Comp fs A B := by
      obtain ⟨pre, u, v, post, hb, rfl, rfl, _⟩ := hm
      apply replaceComp pre u v post
      obtain ⟨L, a, b, ha, hb, hab, hfin, hpair⟩ := hb
      have h0 := TwoGeneratorMinimal cs J L a b ha hb hab hfin
      let hDa := Classical.choose h0
      have h1 := Classical.choose_spec h0
      let hDb := Classical.choose h1
      have h2 := Classical.choose_spec h1
      let H := Classical.choose h2
      have h3 := Classical.choose_spec h2
      let q := Classical.choose h3
      have h4 := Classical.choose_spec h3
      let ea : StandardExpressions cs J L H q := Classical.choose h4
      let eb : StandardExpressions cs J L H q := Classical.choose (Classical.choose_spec h4)
      have he := Classical.choose_spec (Classical.choose_spec h4)
      have nonemptyPair (xs ys : List (Atom))
          (hne : xs ≠ ys) (hlen : xs.length = ys.length) : xs ≠ [] ∧ ys ≠ [] := by
        constructor
        · intro hx
          have hy : ys = [] := List.length_eq_zero_iff.mp (hlen.symm.trans (congrArg List.length hx))
          exact hne (hx.trans hy.symm)
        · intro hy
          have hx : xs = [] := List.length_eq_zero_iff.mp (hlen.trans (congrArg List.length hy))
          exact hne (hx.trans hy.symm)
      have hn := nonemptyPair ea.val eb.val
        (fun h => he.2.2.1 (Subtype.ext h)) he.2.2.2.2.1
      change (u = ea.val ∧ v = eb.val) ∨ (u = eb.val ∧ v = ea.val) at hpair
      rcases hpair with hp | hp
      · intro A B
        rw [hp.1, hp.2]
        exact typedPair ea.val eb.val L H ea.property.1 eb.property.1 hn.1 hn.2 A B
      · intro A B
        rw [hp.1, hp.2]
        exact typedPair eb.val ea.val L H eb.property.1 ea.property.1 hn.2 hn.1 A B
    have liftMove (I K : Obj) (t : Atom) (es fs : List (Atom))
        (hc : Comp (t :: es) I.val K.val)
        (hm : AtomicBraidRelations cs J es fs) :
        AtomicBraidRelations cs J (t :: es) (t :: fs) ∧
          Comp (t :: fs) I.val K.val := by
      have hf : Comp (t :: fs) I.val K.val :=
        ⟨hc.1, (moveComp es fs hm _ _).mp hc.2⟩
      obtain ⟨pre, u, v, post, hb, he, hf', _⟩ := hm
      refine ⟨?_, hf⟩
      refine ⟨t :: pre, u, v, post, hb, ?_, ?_, I, K, hc, hf⟩
      · simpa only [List.cons_append] using congrArg (List.cons t) he
      · simpa only [List.cons_append] using congrArg (List.cons t) hf'
    intro I K t es fs hc hm
    have aux : ∀ {fs}, Moves es fs →
        Moves (t :: es) (t :: fs) ∧ Comp (t :: fs) I.val K.val := by
      intro fs hm
      induction hm with
      | refl => exact ⟨Relation.ReflTransGen.refl, hc⟩
      | @tail ys zs hchain hstep ih =>
        obtain ⟨hlift, hcomp⟩ := liftMove I K t ys zs ih.2 hstep
        exact ⟨ih.1.tail hlift, hcomp⟩
    exact (aux hm).1


  have selectedBridge
      (I K : Obj) (w : (BrinkHowlettGroupoid cs J).Hom I K)
      (t s : Atom) (ht : t.val.1 = I) (hs : s.val.1 = I)
      (hab : t.val.2 ≠ s.val.2)
      (hfin : Set.Finite (parabolicRoots (Set.insert t.val.2 (Set.insert s.val.2 I.val)) \ parabolicRoots I.val))
      (hpt : leftDiv (crossing t).1 w.val)
      (hps : leftDiv (crossing s).1 w.val)
      (cat : ∀ (H : Obj) (q : (BrinkHowlettGroupoid cs J).Hom I H)
        (z : (BrinkHowlettGroupoid cs J).Hom H K)
        (eq : StandardExpressions cs J I H q) (ez : StandardExpressions cs J H K z),
        q.val * z.val = w.val → cs.length w.val = cs.length q.val + cs.length z.val →
        ∃ g : StandardExpressions cs J I K w, g.val = eq.val ++ ez.val) :
      ∃ (g h : StandardExpressions cs J I K w) (gs hs : List (Atom)),
        g.val = t :: gs ∧ h.val = s :: hs ∧ AtomicBraidRelations cs J g.val h.val := by
    classical
    have ha : t.val.2 ∉ I.val := by simpa only [ht] using t.property.1
    have hb : s.val.2 ∉ I.val := by simpa only [hs] using s.property.1
    let h0 := TwoGeneratorMinimal cs J I t.val.2 s.val.2 ha hb hab hfin
    let hDa := Classical.choose h0
    let h1 := Classical.choose_spec h0
    let hDb := Classical.choose h1
    let h2 := Classical.choose_spec h1
    let H := Classical.choose h2
    let h3 := Classical.choose_spec h2
    let q := Classical.choose h3
    let h4 := Classical.choose_spec h3
    let ea := Classical.choose h4
    let eb := Classical.choose (Classical.choose_spec h4)
    have spec := Classical.choose_spec (Classical.choose_spec h4)
    have hta : (⟨(I, t.val.2), ⟨ha, hDa⟩⟩ : Atom) = t := by
      apply Subtype.ext
      exact Prod.ext ht.symm rfl
    have hsb : (⟨(I, s.val.2), ⟨hb, hDb⟩⟩ : Atom) = s := by
      apply Subtype.ext
      exact Prod.ext hs.symm rfl
    have hpt' : leftDiv (SimpleWallCrossings S W M cs I.val t.val.2 ha hDa).1 w.val := by
      change leftDiv (crossing (⟨(I,t.val.2),⟨ha,hDa⟩⟩ : Atom)).1 w.val
      rw [hta]
      exact hpt
    have hps' : leftDiv (SimpleWallCrossings S W M cs I.val s.val.2 hb hDb).1 w.val := by
      change leftDiv (crossing (⟨(I,s.val.2),⟨hb,hDb⟩⟩ : Atom)).1 w.val
      rw [hsb]
      exact hps
    have hqw := (spec.2.2.2.2.2.2.2 K w hpt' hps').1
    let B := BrinkHowlettGroupoid cs J
    let z : B.Hom H K := B.comp (B.inv q) w
    have hz : z.val = q.val⁻¹ * w.val := rfl
    obtain ⟨ez⟩ := (StandardFactorCount cs J H K z).1
    have hmul : q.val * z.val = w.val := by rw [hz]; exact mul_inv_cancel_left _ _
    have hlen : cs.length w.val = cs.length q.val + cs.length z.val := by
      rw [hz]; exact hqw
    obtain ⟨g, hg⟩ := cat H q z ea ez hmul hlen
    obtain ⟨h, hh⟩ := cat H q z eb ez hmul hlen
    obtain ⟨ta, hea⟩ := spec.2.2.2.2.2.1
    obtain ⟨tb, heb⟩ := spec.2.2.2.2.2.2.1
    change ea.val = (⟨(I, t.val.2), ⟨ha, hDa⟩⟩ : Atom) :: ta at hea
    have hea' : ea.val = t :: ta := Eq.trans hea (congrArg (fun x : Atom => x :: ta) hta)
    change eb.val = (⟨(I, s.val.2), ⟨hb, hDb⟩⟩ : Atom) :: tb at heb
    have heb' : eb.val = s :: tb := Eq.trans heb (congrArg (fun x : Atom => x :: tb) hsb)
    refine ⟨g, h, ta ++ ez.val, tb ++ ez.val, ?_, ?_, ?_⟩
    · rw [hg, hea']; rfl
    · rw [hh, heb']; rfl
    · refine ⟨[], ea.val, eb.val, ez.val, ?_, ?_, ?_, I, K, g.property.1, h.property.1⟩
      · refine ⟨I, t.val.2, s.val.2, ha, hb, hab, hfin, ?_⟩
        exact Or.inl ⟨rfl, rfl⟩
      · exact hg
      · exact hh
  
  let Moves := Relation.ReflTransGen (AtomicBraidRelations cs J)
  have moveSymm (xs ys : List Atom) (h : AtomicBraidRelations cs J xs ys) :
      AtomicBraidRelations cs J ys xs := by
    obtain ⟨pre, u, v, post, hb, hx, hy, L, H, hc, hd⟩ := h
    refine ⟨pre, v, u, post, ?_, hy, hx, L, H, hd, hc⟩
    obtain ⟨L, a, b, ha, hb, hab, hfin, hp⟩ := hb
    refine ⟨L, a, b, ha, hb, hab, hfin, ?_⟩
    rcases hp with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · exact Or.inr ⟨hv, hu⟩
    · exact Or.inl ⟨hv, hu⟩
  have movesSymm {xs ys : List Atom} (h : Moves xs ys) : Moves ys xs := by
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail h hs ih => exact (Relation.ReflTransGen.single (moveSymm _ _ hs)).trans ih
  /- Portal steps 1.1, 2.1, 4.1 and 5.1. Strong induction includes the
     one-factor case; no separate uniqueness assertion for it is needed.
     The measure is the common factor count, supplied by the proved corollary. -/
  have induction : ∀ n : Nat, ∀ (I K : Obj) (w : (BrinkHowlettGroupoid cs J).Hom I K)
      (e f : StandardExpressions cs J I K w), e.val.length = n → Moves e.val f.val := by
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro I K w e f hn
      have hcount := (GeneratorsAndStandardLength cs J).2 I K w e f
      by_cases he0 : e.val = []
      · have hf0 : f.val = [] := List.length_eq_zero_iff.mp (by rw [← hcount, he0]; rfl)
        rw [he0, hf0]
      obtain ⟨t, es, he⟩ := List.exists_cons_of_ne_nil he0
      have hf0 : f.val ≠ [] := by
        intro hf
        rw [he, hf] at hcount
        simp at hcount
      obtain ⟨s, fs, hf⟩ := List.exists_cons_of_ne_nil hf0
      have sameHeadConnect : ∀ (e f : StandardExpressions cs J I K w)
          (t : Atom) (es fs : List Atom), e.val = t :: es → f.val = t :: fs →
          e.val.length = n → Moves e.val f.val := by
        intro e f t es fs he hf hne
        obtain ⟨L, z, ez, fz, hez, hfz⟩ := same_head I K w e f t es fs he hf
        have hlt : es.length < n := by rw [he] at hne; simp only [List.length_cons] at hne; omega
        have hchain := ih es.length hlt L K z ez fz (congrArg List.length hez)
        rw [hez, hfz] at hchain
        have hc : Comp (t :: es) I.val K.val := he ▸ e.property.1
        have h := liftHead I K t es fs hc hchain
        simpa only [he, hf] using h
      by_cases hidx : t.val.2 = s.val.2
      · have ht := (head_prefix I K w e t es he).1
        have hs := (head_prefix I K w f s fs hf).1
        have hts : t = s := Subtype.ext (Prod.ext (ht.symm.trans hs) hidx)
        subst s
        exact sameHeadConnect e f t es fs he hf hn
      · have ht := head_prefix I K w e t es he
        have hs := head_prefix I K w f s fs hf
        have ha : t.val.2 ∉ I.val := by rw [ht.1]; exact t.property.1
        have hb : s.val.2 ∉ I.val := by rw [hs.1]; exact s.property.1
        have hDa : Finite (cs.parabolic (component I.val t.val.2)) := by rw [ht.1]; exact t.property.2
        have hDb : Finite (cs.parabolic (component I.val s.val.2)) := by rw [hs.1]; exact s.property.2
        have hpt : leftDiv (SimpleWallCrossings S W M cs I.val t.val.2 ha hDa).1 w.val := by
          simpa only [ht.1] using ht.2
        have hps : leftDiv (SimpleWallCrossings S W M cs I.val s.val.2 hb hDb).1 w.val := by
          simpa only [hs.1] using hs.2
        -- Step 3.1: derive full relative-root finiteness from these two actual prefixes.
        have hfin := commonPrefixFinite I K w t.val.2 s.val.2 ha hb hidx hDa hDb hpt hps
        obtain ⟨g, h, gs, hs', hg, hh, hmove⟩ := selectedBridge I K w t s ht.1.symm hs.1.symm
          hidx hfin ht.2 hs.2 (fun H q z eq ez => concatenate I H K q z w eq ez)
        have heg := sameHeadConnect e g t es gs he hg hn
        have hfh := sameHeadConnect f h s fs hs' hf hh (hcount.symm.trans hn)
        exact heg.trans ((Relation.ReflTransGen.single hmove).trans (movesSymm hfh))
  intro I K w e f
  exact induction e.val.length I K w e f rfl
)
