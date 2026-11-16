import Mathlib
import ArtinDeligne
import Proofs.StandardExpressions
import Proofs.FiniteRelativeLongest
import Proofs.StandardFactorCount
import Proofs.GeneratorsAndStandardLength

theorem TwoGeneratorMinimal : (∀ {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S),
  let Obj := { L : Set S // ∃ g : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (CoxeterSystem.parabolic cs L) = CoxeterSystem.parabolic cs J }
  let component : Set S → S → Set S := fun L c => { d | d ∈ Set.insert c L ∧ Relation.ReflTransGen (fun i j : S => i ∈ Set.insert c L ∧ j ∈ Set.insert c L ∧ i ≠ j ∧ M i j ≠ 2) c d }
  let parabolicRoots : Set S → Set (Finsupp S Real) := fun L => { α | ∃ u : W, u ∈ CoxeterSystem.parabolic cs L ∧ ∃ i : S, i ∈ L ∧ CoxeterSystem.geometricRepresentation cs u (Finsupp.single i (1 : Real)) = α }
  let leftDiv : W → W → Prop := fun u v => CoxeterSystem.length cs v = CoxeterSystem.length cs u + CoxeterSystem.length cs (u⁻¹ * v)
  ∀ (I : Obj) (a b : S) (ha : a ∉ I.val) (hb : b ∉ I.val),
    a ≠ b →
    Set.Finite (parabolicRoots (Set.insert a (Set.insert b I.val)) \ parabolicRoots I.val) →
    ∃ (hDa : Finite (CoxeterSystem.parabolic cs (component I.val a))) (hDb : Finite (CoxeterSystem.parabolic cs (component I.val b))),
    let va : W := (SimpleWallCrossings S W M cs I.val a ha hDa).1
    let vb : W := (SimpleWallCrossings S W M cs I.val b hb hDb).1
    ∃ (K : Obj) (q : (BrinkHowlettGroupoid cs J).Hom I K) (ea eb : StandardExpressions cs J I K q),
      leftDiv va q.val ∧ leftDiv vb q.val ∧
      ea ≠ eb ∧
      (∀ e : StandardExpressions cs J I K q, e = ea ∨ e = eb) ∧
      List.length ea.val = List.length eb.val ∧
      (∃ ta, ea.val = List.cons ⟨(I, a), ⟨ha, hDa⟩⟩ ta) ∧
      (∃ tb, eb.val = List.cons ⟨(I, b), ⟨hb, hDb⟩⟩ tb) ∧
      (∀ (K' : Obj) (w : (BrinkHowlettGroupoid cs J).Hom I K'), leftDiv va w.val → leftDiv vb w.val → leftDiv q.val w.val ∧ ∀ e : StandardExpressions cs J I K' w, List.length ea.val ≤ List.length e.val)) :=
(by
  /- Lemma 4.15/(4.16), printed p.19: https://arxiv.org/pdf/2509.21915#page=19.
  Inspiration: steps 1.1, 2.1, 2.2, 3.1 at
  https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-two-generator-minimal-artin-tits-normalisers.
  The finite relative-root hypothesis supplies finite component parabolics. No ambient rank or type restriction.
  All maxima and epsilon selections below are certified. Local implementation blocks have no standalone article statements.
  For steps 1.1/2.1 at
  https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-author-a7d202611130-rank-two-standard-words,
  we prove confinement and deterministic nonbacktracking continuation directly. Reverse crossings and positive length
  exclude backtracking; equal factor counts determine the continuation. StandardFactorCount supplies both suffix words.
  Dyer--Gimenez https://arxiv.org/abs/2606.12937v1, section 1.27, pp.10--11, writes rightmost factors
  nu(alpha,K), nu(beta,K) with alpha,beta in K, undefined under Remark 1.26, as the portal Source notes record.
  Neither this clause nor the independent exactly-two assertion is assumed: initial factors and exhaustion are proved.
  The auxiliary inclusion following (3.15), article p.10, is unused. Exact defect source:
  https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects#pdf-wall-root-characterisation.
  Evidence: in rank one I=K=empty and v=s_a maps alpha_a to -alpha_a, while Phi_K^- is empty.
  Disposition: retain the longest-element definition (3.14) and prove the inversion formulas directly.
  Broader reading and bounded GitHub searches are reused only as recorded in the supplied evidence.
  No fresh full-article, transitive-source or bibliography reading, or translation review, is claimed. -/
  intro S W inst M cs J
  exact (set_option maxHeartbeats 0 in by
    classical
    let f1 {M : CoxeterMatrix S} (L : Set S) (c : S) : Set S :=
      {d | d ∈ Set.insert c L ∧ Relation.ReflTransGen
        (fun i j : S => i ∈ Set.insert c L ∧ j ∈ Set.insert c L ∧ i ≠ j ∧ M i j ≠ 2) c d}
    let f2 {M : CoxeterMatrix S} (I : Set S) (a b : S) : Set S :=
      let T := Set.insert a (Set.insert b I)
      {i | i ∈ T ∧ (Relation.ReflTransGen
        (fun j k : S => j ∈ T ∧ k ∈ T ∧ j ≠ k ∧ M j k ≠ 2) a i ∨
        Relation.ReflTransGen
        (fun j k : S => j ∈ T ∧ k ∈ T ∧ j ≠ k ∧ M j k ≠ 2) b i)}
    let f3 (cs : CoxeterSystem M W) (L : Set S) : Set (S →₀ ℝ) :=
      {x | ∃ w : W, w ∈ cs.parabolic L ∧ ∃ i ∈ L,
        cs.geometricRepresentation w (Finsupp.single i 1) = x}
    let f4 (cs : CoxeterSystem M W) (w : W) : Set (S →₀ ℝ) :=
      {x | x ∈ cs.geometricRoots ∧ 0 < x} ∩
        cs.geometricRepresentation w '' {x | x ∈ cs.geometricRoots ∧ x < 0}
    have f5 (cs : CoxeterSystem M W) (w : W) (x : S →₀ ℝ) :
        x ∈ f4 cs w ↔ x ∈ cs.geometricRoots ∧ 0 < x ∧
          cs.geometricRepresentation w⁻¹ x < 0 := by
      clear * - S W inst M cs J w x f4
      constructor
      · rintro ⟨⟨hr, hp⟩, y, ⟨_, hn⟩, rfl⟩
        exact ⟨hr, hp, by simpa only [Representation.inv_self_apply] using hn⟩
      · rintro ⟨hr, hp, hn⟩
        exact ⟨⟨hr, hp⟩, cs.geometricRepresentation w⁻¹ x,
          ⟨(cs.geometricRepresentation_apply_mem_geometricRoots_iff _).mpr hr, hn⟩,
          Representation.self_inv_apply _ _ _⟩
    have f6 (cs : CoxeterSystem M W) {u v : W} (h : f4 cs u = f4 cs v) : u = v := by
      clear * - S W inst M cs J u v h f4 f5
      have pref (x y : W) (hxy : f4 cs x ⊆ f4 cs y) :
          cs.length y = cs.length x + cs.length (x⁻¹ * y) := by
        apply (ArtinNormalisers.Chamber3.length_eq_add_iff_rootInversions_subset_system cs x y).mpr
        intro r hr hp hn
        exact ((f5 cs y r).mp
          (hxy ((f5 cs x r).mpr ⟨hr, hp, hn⟩))).2.2
      have huv  := pref u v (by rw [h])
      have hvu := pref v u (by rw [h])
      have hz : u⁻¹ * v = 1 := cs.length_eq_zero_iff.mp (by omega)
      exact (inv_mul_eq_one.mp hz)
    have f7 (cs : CoxeterSystem M W) (I : Set S) (a b : S) (ha : a ∉ I) (hb : b ∉ I)
        (hab : a ≠ b) (hf : Set.Finite (f3 cs (Set.insert a (Set.insert b I)) \ f3 cs I))
        (q : W) (hq : f4 cs q =
          (f3 cs (Set.insert a (Set.insert b I)) ∩ {x | x ∈ cs.geometricRoots ∧ 0 < x}) \
            (f3 cs I ∩ {x | x ∈ cs.geometricRoots ∧ 0 < x})) :
        Finite (cs.parabolic (f2 (M := M) I a b)) ∧
        ∃ d : cs.parabolic (f2 (M := M) I a b),
        ∃ j : cs.parabolic (f2 (M := M) I a b ∩ I),
          q = ((d : W) * (j : W))⁻¹ ∧ q ∈ cs.parabolic (f2 (M := M) I a b) := by
      clear * - S W inst M cs J I a b ha hb hab hf q hq f6 f4 f3 f2
      obtain ⟨hD, d, j, _, _, K, _, _, _, _, hN⟩ := FiniteRelativeLongest cs I a b ha hb hab hf
      have he : q = ((d : W) * (j : W))⁻¹ := f6 cs (hq.trans hN.symm)
      refine ⟨hD, d, j, he, ?_⟩
      rw [he]
      exact inv_mem (mul_mem d.property (cs.parabolic_mono Set.inter_subset_left j.property))
    have f8 (cs : CoxeterSystem M W) (L : Set S) (w : W) (hw : w ∈ cs.parabolic L)
        (k : S) (hk : k ∉ L) (x : S →₀ ℝ) :
        cs.geometricRepresentation w x k = x k := by
      clear * - S W inst M cs J L w hw k hk x
      obtain ⟨u, hu, rfl⟩ := cs.exists_wordProd_eq_of_mem_parabolic hw
      clear hw
      induction u with
      | nil => simp
      | cons i u ih =>
        have hki : k ≠ i := fun h => hk (h ▸ hu i (by simp))
        rw [cs.wordProd_cons, map_mul, mul_apply_eq_comp,
          cs.geometricRepresentation_simple, M.geometricReflection_apply_apply_of_ne hki]
        exact ih (fun j hj => hu j (by simp [hj]))
    have f9 (cs : CoxeterSystem M W) {D : Set S} {i : S}
        (hi : cs.simple i ∈ cs.parabolic D) : i ∈ D := by
      clear * - S W inst M cs J D i hi
      obtain ⟨u, hu, hD, hp⟩ := cs.exists_isReduced_wordProd_eq_of_mem_parabolic hi
      have hl : u.length = 1 := by rw [← hu.eq, hp, cs.length_simple]
      obtain ⟨j, rfl⟩ := List.length_eq_one_iff.mp hl
      have hij : j = i := cs.simple_injective (by simpa using hp)
      exact hij ▸ hD j (by simp)
    have f10 (cs : CoxeterSystem M W) {A : Type _} (label : A → W) (es : List A) (D : Set S)
        (hadd : cs.length (es.map label).prod = (es.map (fun e => cs.length (label e))).sum)
        (hprod : (es.map label).prod ∈ cs.parabolic D) :
        ∀ e ∈ es, label e ∈ cs.parabolic D := by
      clear * - S W inst M cs J A label es D hadd hprod f9
      classical
      choose word hred hword using (fun e : A => cs.exists_isReduced (label e))
      have prod_eq (es : List A) : cs.wordProd (es.flatMap word) = (es.map label).prod := by
        induction es with
        | nil => simp
        | cons e es ih => simp [cs.wordProd_append, ih, ← hword e]
      have len_eq (es : List A) : (es.flatMap word).length =
          (es.map (fun e => cs.length (label e))).sum := by
        induction es with
        | nil => simp
        | cons e es ih => simp [ih, ← (hred e).eq, ← hword e]
      have hr : cs.IsReduced (es.flatMap word) := by
        change cs.length (cs.wordProd (es.flatMap word)) = (es.flatMap word).length
        rw [prod_eq, len_eq]
        exact hadd
      have hall : ∀ i ∈ es.flatMap word, i ∈ D := fun i hi =>
        f9 cs (cs.simple_mem_parabolic_of_isReduced _ hr (by rwa [prod_eq]) i hi)
      intro e he
      rw [hword e]
      exact cs.wordProd_mem_parabolic (fun i hi => hall i (List.mem_flatMap.mpr ⟨e, he, hi⟩))
    have f11 (cs : CoxeterSystem M W) (L D : Set S) (c : S) (hc : c ∉ L)
        (hF : Finite (cs.parabolic (f1 (M := M) L c)))
        (hv : (SimpleWallCrossings S W M cs L c hc hF).1 ∈ cs.parabolic D) : c ∈ D := by
      clear * - S W inst M cs J L D c hc hF hv f1 f8
      classical
      let F := f1 (M := M) L c
      letI : Finite (cs.parabolic F) := hF
      let subfinite (A : Set S) (hA : A ⊆ F) : Finite (cs.parabolic A) :=
        Finite.of_injective (fun w : cs.parabolic A =>
          (⟨w.val, cs.parabolic_mono hA w.property⟩ : cs.parabolic F))
          (fun _ _ h => Subtype.ext (congrArg (fun z : cs.parabolic F => z.val) h))
      let longest (A : Set S) (hA : A ⊆ F) : cs.parabolic A :=
        letI := subfinite A hA
        Classical.choose (Finite.exists_max (fun w : cs.parabolic A => cs.length w.val))
      have maxF (u : cs.parabolic F) : cs.length u.val ≤
          cs.length (longest F (fun _ h => h)).val := by
        letI := subfinite F (fun _ h => h)
        exact Classical.choose_spec (Finite.exists_max
          (fun w : cs.parabolic F => cs.length w.val)) u
      let d : cs.parabolic F := longest F (fun _ h => h)
      let j : cs.parabolic (F \ {c}) := longest (F \ {c}) Set.sdiff_subset
      change (j : W) * (d : W) ∈ cs.parabolic D at hv
      have hcF : c ∈ F := ⟨Set.mem_insert _ _, Relation.ReflTransGen.refl⟩
      have hm := maxF ⟨d.val * cs.simple c, mul_mem d.property (cs.simple_mem_parabolic hcF)⟩
      have hn : cs.geometricRepresentation d.val (Finsupp.single c (1 : ℝ)) < 0 := by
        apply (cs.geometricRepresentation_single_neg_iff _ c).mpr
        change cs.length (d.val * cs.simple c) < cs.length d.val
        have hdich := cs.length_mul_simple d.val c
        change cs.length (d.val * cs.simple c) ≤ cs.length d.val at hm
        rcases hdich with h | h <;> omega
      by_contra hcD
      have ho := f8 cs D (j.val * d.val) hv c hcD (Finsupp.single c 1)
      rw [map_mul, mul_apply_eq_comp, f8 cs (F \ {c}) j.val j.property c (by simp)] at ho
      have hle : cs.geometricRepresentation d.val (Finsupp.single c (1 : ℝ)) c ≤ 0 := hn.le c
      simp only [Finsupp.single_eq_same] at ho
      linarith
    have f12 {M : CoxeterMatrix S} (I : Set S) (a b : S) :
        a ∈ f2 (M := M) I a b ∧ b ∈ f2 (M := M) I a b ∧
        f2 (M := M) I a b ⊆ Set.insert a (Set.insert b I) ∧
        (∀ i ∈ f2 (M := M) I a b, ∀ j ∈ I \ f2 (M := M) I a b, M i j = 2) := by
      clear * - S W inst M cs J I a b f2
      let T := Set.insert a (Set.insert b I)
      let D := f2 (M := M) I a b
      have haD : a ∈ D := ⟨Set.mem_insert _ _, Or.inl Relation.ReflTransGen.refl⟩
      have hbD : b ∈ D := ⟨Set.mem_insert_of_mem _ (Set.mem_insert _ _), Or.inr Relation.ReflTransGen.refl⟩
      refine ⟨haD, hbD, fun _ h => h.1, ?_⟩
      intro i hi j hj
      by_contra hij
      have hne : i ≠ j := fun he => hj.2 (he ▸ hi)
      have edge : i ∈ T ∧ j ∈ T ∧ i ≠ j ∧ M i j ≠ 2 :=
        ⟨hi.1, Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hj.1), hne, hij⟩
      apply hj.2
      exact ⟨edge.2.1, hi.2.elim
        (fun hp => Or.inl (hp.tail edge)) (fun hp => Or.inr (hp.tail edge))⟩
    let f13 (D E L : Set S) : Prop :=
      ∃ x ∈ D, ∃ y ∈ D, x ≠ y ∧ L = E ∪ (D \ {x, y})
    have f14 {M : CoxeterMatrix S} (I : Set S) (a b : S) (ha : a ∉ I) (hb : b ∉ I) (hab : a ≠ b) :
        f13 (f2 (M := M) I a b) (I \ f2 (M := M) I a b) I := by
      clear * - S W inst M cs J I a b ha hb hab f13 f2 f12
      classical
      obtain ⟨haD, hbD, hDT, _⟩ := f12 (M := M) I a b
      refine ⟨a, haD, b, hbD, hab, ?_⟩
      ext t
      have hT : t ∈ f2 (M := M) I a b → t = a ∨ t = b ∨ t ∈ I := fun h => hDT h
      change t ∈ I ↔ (t ∈ I ∧ t ∉ f2 (M := M) I a b) ∨
        (t ∈ f2 (M := M) I a b ∧ ¬ (t = a ∨ t = b))
      constructor
      · intro hi
        by_cases hd : t ∈ f2 (M := M) I a b
        · exact Or.inr ⟨hd, fun h => h.elim (fun h => ha (h ▸ hi)) (fun h => hb (h ▸ hi))⟩
        · exact Or.inl ⟨hi, hd⟩
      · rintro (⟨hi, _⟩ | ⟨hd, hn⟩)
        · exact hi
        · rcases hT hd with he | he | hi
          · exact False.elim (hn (Or.inl he))
          · exact False.elim (hn (Or.inr he))
          · exact hi
    have f15 {M : CoxeterMatrix S} (D E L : Set S) (hsep : ∀ i ∈ D, ∀ j ∈ E, M i j = 2)
        (hL : f13 D E L) (c : S) (hcD : c ∈ D) : f1 (M := M) L c ⊆ D := by
      clear * - S W inst M cs J D E L hsep hL c hcD f13 f1
      obtain ⟨x, _, y, _, _, rfl⟩ := hL
      intro d hd
      have H : ∀ d, Relation.ReflTransGen
          (fun i j : S => i ∈ Set.insert c (E ∪ (D \ {x, y})) ∧
            j ∈ Set.insert c (E ∪ (D \ {x, y})) ∧ i ≠ j ∧ M i j ≠ 2) c d → d ∈ D := by
        intro d hp
        induction hp with
        | refl => exact hcD
        | @tail d e hp edge ih =>
          by_cases he : e ∈ D
          · exact he
          have heE : e ∈ E := by
            rcases edge.2.1 with rfl | hE | hD
            · exact False.elim (he hcD)
            · exact hE
            · exact False.elim (he hD.1)
          exact False.elim (edge.2.2.2 (hsep d ih e heE))
      exact H d hd.2
    have f16 (cs : CoxeterSystem M W) (L : Set S) (c : S) (hc : c ∉ L)
        (hF : Finite (cs.parabolic (f1 (M := M) L c))) :
        ∃ t ∈ f1 (M := M) L c,
          (SimpleWallCrossings S W M cs L c hc hF).2.1 = Set.insert c L \ {t} := by
      clear * - S W inst M cs J L c hc hF f1
      classical
      unfold SimpleWallCrossings
      dsimp only
      exact ⟨_, Subtype.property _, rfl⟩
    have f17 (D E : Set S) (x y t : S) (hx : x ∈ D)
        (htE : t ∉ E) (hxy : x ≠ y) (hty : t ≠ y) :
        Set.insert x (E ∪ (D \ {x, y})) \ {t} = E ∪ (D \ {t, y}) := by
      clear * - S W inst M cs J D E x y t hx htE hxy hty
      classical
      ext k
      change ((k = x ∨ k ∈ E ∨ (k ∈ D ∧ ¬(k = x ∨ k = y))) ∧ k ≠ t) ↔
        k ∈ E ∨ (k ∈ D ∧ ¬(k = t ∨ k = y))
      by_cases hkx : k = x
      · subst k
        aesop
      · by_cases hkt : k = t
        · subst k
          aesop
        · tauto
    have f18 (cs : CoxeterSystem M W) (D E L : Set S) (hdis : Disjoint D E)
        (hsep : ∀ i ∈ D, ∀ j ∈ E, M i j = 2) (hL : f13 D E L)
        (c : S) (hc : c ∉ L) (hcD : c ∈ D)
        (hF : Finite (cs.parabolic (f1 (M := M) L c))) :
        f13 D E (SimpleWallCrossings S W M cs L c hc hF).2.1 := by
      clear * - S W inst M cs J D E L hdis hsep hL c hc hcD hF f13 f1 f15 f17 f16
      classical
      have hFD := f15 D E L hsep hL c hcD
      obtain ⟨t, ht, heq⟩ := f16 cs L c hc hF
      have htD := hFD ht
      have htL : t ∈ Set.insert c L := ht.1
      obtain ⟨x, hx, y, hy, hxy, hL⟩ := hL
      have hcxy : c = x ∨ c = y := by
        by_contra hn
        apply hc
        rw [hL]
        right
        exact ⟨hcD, by simpa using hn⟩
      have htE : t ∉ E := fun h => Set.disjoint_left.mp hdis htD h
      have case_x (x y : S) (hx : x ∈ D) (hy : y ∈ D) (hxy : x ≠ y)
          (hL : L = E ∪ (D \ {x, y})) (hc : c = x) :
          f13 D E (Set.insert c L \ {t}) := by
        have hty : t ≠ y := by
          intro he
          subst t
          rcases htL with he | he
          · exact hxy (hc.symm.trans he.symm)
          · rw [hL] at he
            rcases he with he | he
            · exact htE he
            · exact he.2 (by simp)
        refine ⟨t, htD, y, hy, hty, ?_⟩
        rw [hL, hc]
        exact f17 D E x y t hx htE hxy hty
      rcases hcxy with hcx | hcy
      · rw [heq]
        exact case_x x y hx hy hxy hL hcx
      · rw [heq]
        apply case_x y x hy hx hxy.symm _ hcy
        simpa only [Set.pair_comm] using hL
    let f19 (cs : CoxeterSystem M W) (J : Set S) := {L : Set S // ∃ g : W,
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (cs.parabolic L) = cs.parabolic J}
    let f20 (cs : CoxeterSystem M W) (J : Set S) := {p : f19 cs J × S // p.2 ∉ p.1.val ∧
      Finite (cs.parabolic (f1 (M := M) p.1.val p.2))}
    let f21 (cs : CoxeterSystem M W) {J : Set S} (e : f20 cs J) :=
      SimpleWallCrossings S W M cs e.val.1.val e.val.2 e.property.1 e.property.2
    let f22 (cs : CoxeterSystem M W) {J : Set S} (es : List (f20 cs J)) (L K : Set S) : Prop :=
      List.foldr (fun e tail N => N = e.val.1.val ∧ tail (f21 cs e).2.1)
        (fun N => N = K) es L
    have f23 (cs : CoxeterSystem M W) {J : Set S} (D E : Set S) (hdis : Disjoint D E)
        (hsep : ∀ i ∈ D, ∀ j ∈ E, M i j = 2)
        (es : List (f20 cs J)) (L K : Set S) (hcomp : f22 cs es L K)
        (hstart : f13 D E L)
        (hmem : ∀ e ∈ es, (f21 cs e).1 ∈ cs.parabolic D) :
        f13 D E K ∧ ∀ e ∈ es,
          f13 D E e.val.1.val ∧ e.val.2 ∈ D ∧ f1 (M := M) e.val.1.val e.val.2 ⊆ D := by
      clear * - S W inst M cs J D E hdis hsep es L K hcomp hstart hmem f20 f22 f13 f1 f15 f21 f11 f18
      induction es generalizing L with
      | nil =>
        change L = K at hcomp
        subst L
        exact ⟨hstart, by simp⟩
      | cons e es ih =>
        obtain ⟨hsource, htail⟩ := hcomp
        subst L
        have hcD := f11 cs e.val.1.val D e.val.2 e.property.1 e.property.2
          (hmem e (by simp))
        have hFD := f15 D E e.val.1.val hsep hstart e.val.2 hcD
        have hnext := f18 cs D E e.val.1.val hdis hsep hstart e.val.2 e.property.1 hcD e.property.2
        obtain ⟨hend, hall⟩ := ih _ htail hnext (fun t ht => hmem t (by simp [ht]))
        refine ⟨hend, ?_⟩
        intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · exact ⟨hstart, hcD, hFD⟩
        · exact hall t ht
    have f24 (cs : CoxeterSystem M W) (J : Set S) (I K : f19 cs J) (a b : S)
        (ha : a ∉ I.val) (hb : b ∉ I.val) (hab : a ≠ b)
        (hf : Set.Finite (f3 cs (Set.insert a (Set.insert b I.val)) \ f3 cs I.val))
        (q : (BrinkHowlettGroupoid cs J).Hom I K)
        (hq : f4 cs q.val =
          (f3 cs (Set.insert a (Set.insert b I.val)) ∩ {x | x ∈ cs.geometricRoots ∧ 0 < x}) \
            (f3 cs I.val ∩ {x | x ∈ cs.geometricRoots ∧ 0 < x}))
        (e : StandardExpressions cs J I K q) :
        let D := f2 (M := M) I.val a b
        let E := I.val \ D
        Finite (cs.parabolic D) ∧ f13 D E K.val ∧
          ∀ t ∈ e.val, (f21 cs t).1 ∈ cs.parabolic D ∧
            f13 D E t.val.1.val ∧ t.val.2 ∈ D ∧ f1 (M := M) t.val.1.val t.val.2 ⊆ D := by
      let D := f2 (M := M) I.val a b
      let E := I.val \ D
      obtain ⟨hD, d, j, hcanon, hqD⟩ := f7 cs I.val a b ha hb hab hf q.val hq
      have hfac : ∀ t ∈ e.val, (f21 cs t).1 ∈ cs.parabolic D := by
        have hp : (e.val.map (fun t : f20 cs J => (f21 cs t).1)).prod = q.val := e.property.2.1
        have hl : cs.length (e.val.map (fun t : f20 cs J => (f21 cs t).1)).prod =
            (e.val.map (fun t => cs.length (f21 cs t).1)).sum := by
          rw [hp]
          exact e.property.2.2
        apply f10 cs (fun t : f20 cs J => (f21 cs t).1) e.val D hl
        rw [hp]
        exact hqD
      have hcomp : f22 cs e.val I.val K.val := e.property.1
      have hdis : Disjoint D E := Set.disjoint_left.mpr (fun _ hd he => he.2 hd)
      have hsep : ∀ i ∈ D, ∀ j ∈ E, M i j = 2 := (f12 (M := M) I.val a b).2.2.2
      obtain ⟨hend, hall⟩ := f23 cs D E hdis hsep e.val I.val K.val hcomp
        (f14 (M := M) I.val a b ha hb hab) hfac
      exact ⟨hD, hend, fun t ht => ⟨hfac t ht, hall t ht⟩⟩
    have f25 (D E L : Set S) (hdis : Disjoint D E) (hL : f13 D E L) :
        ∃ x ∈ D, ∃ y ∈ D, x ≠ y ∧ D \ L = {x, y} := by
      clear * - S W inst M cs J D E L hdis hL f13
      obtain ⟨x, hx, y, hy, hxy, rfl⟩ := hL
      refine ⟨x, hx, y, hy, hxy, ?_⟩
      ext k
      have hDE : k ∈ D → k ∉ E := fun h => Set.disjoint_left.mp hdis h
      change (k ∈ D ∧ ¬ (k ∈ E ∨ (k ∈ D ∧ ¬ (k = x ∨ k = y)))) ↔ k = x ∨ k = y
      constructor
      · tauto
      · rintro (rfl | rfl)
        · exact ⟨hx, by tauto⟩
        · exact ⟨hy, by tauto⟩
    have f26 (cs : CoxeterSystem M W) {J : Set S} (e f : f20 cs J)
        (hs : e.val.1.val = f.val.1.val) (hi : e.val.2 = f.val.2) : e = f :=
      Subtype.ext (Prod.ext (Subtype.ext hs) hi)
    have f27 (cs : CoxeterSystem M W) {J : Set S} (D E L : Set S) (hdis : Disjoint D E)
        (hL : f13 D E L) :
        ∃ x ∈ D, ∃ y ∈ D, x ≠ y ∧ ∀ t : f20 cs J,
          t.val.1.val = L → (f21 cs t).1 ∈ cs.parabolic D →
          t.val.2 = x ∨ t.val.2 = y := by
      clear * - S W inst M cs J D E L hdis hL f20 f13 f21 f11 f25
      obtain ⟨x, hx, y, hy, hxy, hmiss⟩ := f25 D E L hdis hL
      refine ⟨x, hx, y, hy, hxy, ?_⟩
      intro t hs ht
      have hcD := f11 cs t.val.1.val D t.val.2 t.property.1 t.property.2 ht
      have hcL : t.val.2 ∉ L := hs ▸ t.property.1
      have hm : t.val.2 ∈ D \ L := ⟨hcD, hcL⟩
      rw [hmiss] at hm
      exact hm
    let f28 (M : CoxeterMatrix S) (L : Set S) (c : S) : Set S :=
      {d | d ∈ Set.insert c L ∧ Relation.ReflTransGen
        (fun i j : S => i ∈ Set.insert c L ∧ j ∈ Set.insert c L ∧ i ≠ j ∧ M i j ≠ 2) c d}
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
    let f30 (cs : CoxeterSystem M W) (D : Set S) (hD : Finite (cs.parabolic D))
        (L : Set S) (hL : L ⊆ D) : Finite (cs.parabolic L) :=
      letI := hD
      Finite.of_injective (fun w : cs.parabolic L =>
        (⟨w.val, cs.parabolic_mono hL w.property⟩ : cs.parabolic D))
        (fun _ _ h => Subtype.ext (congrArg (fun z : cs.parabolic D => z.val) h))
    let f31 (cs : CoxeterSystem M W) (D : Set S) (hD : Finite (cs.parabolic D))
        (L : Set S) (hL : L ⊆ D) : cs.parabolic L :=
      letI := f30 cs D hD L hL
      Classical.choose (Finite.exists_max (fun w : cs.parabolic L => cs.length w.val))
    have f32 (cs : CoxeterSystem M W) (D : Set S) (hD : Finite (cs.parabolic D))
        (L : Set S) (hL : L ⊆ D) (u : cs.parabolic L) :
        cs.length u.val ≤ cs.length (f31 cs D hD L hL).val := by
      clear * - S W inst M cs J D hD L hL u f31 f30
      letI := f30 cs D hD L hL
      exact Classical.choose_spec (Finite.exists_max (fun w : cs.parabolic L => cs.length w.val)) u
    let f33 (cs : CoxeterSystem M W) (D : Set S) (hD : Finite (cs.parabolic D)) : D ≃ D :=
      @Classical.epsilon (D ≃ D) ⟨Equiv.refl D⟩ (fun e => ∀ i : D,
        cs.geometricRepresentation (f31 cs D hD D (fun _ h => h)).val
          (Finsupp.single (i : S) 1) = -Finsupp.single (e i : S) 1)
    have f34 (cs : CoxeterSystem M W) (D : Set S)
        (hD : Finite (cs.parabolic D)) :
        let z := (f31 cs D hD D (fun _ h => h)).val
        let e := f33 cs D hD
        (∀ u : W, u ∈ cs.parabolic D → cs.length (z * u) + cs.length u = cs.length z) ∧
        z * z = 1 ∧ Function.Involutive e ∧
          (∀ i : D, cs.geometricRepresentation z (Finsupp.single (i : S) 1) =
            -Finsupp.single (e i : S) 1) ∧
          (∀ i : D, z * cs.simple (i : S) * z⁻¹ = cs.simple (e i : S)) := by
      clear * - S W inst M cs J D hD f31 f32 f33 f29
      classical
      obtain ⟨hlen, hzz, e, hinv, hr, hg⟩ := f29 cs D
        (f31 cs D hD D (fun _ h => h)) (f32 cs D hD D (fun _ h => h))
      have hspec : ∀ i : D,
          cs.geometricRepresentation (f31 cs D hD D (fun _ h => h)).val
            (Finsupp.single (i : S) 1) = -Finsupp.single (f33 cs D hD i : S) 1 :=
        @Classical.epsilon_spec_aux (D ≃ D) ⟨Equiv.refl D⟩
          (fun f => ∀ i : D, cs.geometricRepresentation (f31 cs D hD D (fun _ h => h)).val
            (Finsupp.single (i : S) 1) = -Finsupp.single (f i : S) 1) ⟨e, hr⟩
      have heq : f33 cs D hD = e := by
        apply Equiv.ext
        intro i
        apply Subtype.ext
        apply Finsupp.single_left_injective (by norm_num : (1 : ℝ) ≠ 0)
        exact neg_injective ((hspec i).symm.trans (hr i))
      exact ⟨hlen, hzz, heq.symm ▸ hinv, hspec, heq.symm ▸ hg⟩
    have f35 (cs : CoxeterSystem M W) (I : Set S) (a : S)
        (ha : a ∉ I) (hD : Finite (cs.parabolic (f28 M I a))) :
        let D := f28 M I a
        let aD : D := ⟨a, Set.mem_insert a I, Relation.ReflTransGen.refl⟩
        SimpleWallCrossings S W M cs I a ha hD =
          ((f31 cs D hD (D \ {a}) Set.sdiff_subset).val *
            (f31 cs D hD D (fun _ h => h)).val,
            Set.insert a I \ {(f33 cs D hD aD : S)},
            fun x => (x * ((f31 cs D hD (D \ {a}) Set.sdiff_subset).val *
            (f31 cs D hD D (fun _ h => h)).val),
            Set.insert a I \ {(f33 cs D hD aD : S)})) := rfl
    have f36 (cs : CoxeterSystem M W) (D : Set S) (z t : cs.parabolic D)
        (hz : ∀ u : cs.parabolic D, cs.length u.val ≤ cs.length z.val)
        (ht : ∀ u : cs.parabolic D, cs.length u.val ≤ cs.length t.val) : z = t := by
      clear * - S W inst M cs J D z t hz ht f29
      have hlen := (f29 cs D z hz).1 t.val t.property
      have hsame : cs.length z.val = cs.length t.val := le_antisymm (ht z) (hz t)
      have hzt : z.val * t.val = 1 := cs.length_eq_zero_iff.mp (by omega)
      have hzz := (f29 cs D z hz).2.1
      apply Subtype.ext
      calc z.val = z.val * (z.val * t.val) := by rw [hzt, mul_one]
           _ = t.val := by rw [← mul_assoc, hzz, one_mul]
    have f37 (cs : CoxeterSystem M W) (D : Set S)
        (hD : Finite (cs.parabolic D)) (u : W) (hu : u ∈ cs.parabolic D) :
        let z := (f31 cs D hD D (fun _ h => h)).val
        cs.length (z * u * z) = cs.length u := by
      clear * - S W inst M cs J D hD u hu f31 f34
      dsimp only
      let z := (f31 cs D hD D (fun _ h => h)).val
      obtain ⟨hlen, hzz, _⟩ := f34 cs D hD
      change (∀ u : W, u ∈ cs.parabolic D → cs.length (z * u) + cs.length u = cs.length z) at hlen
      have hz : z ∈ cs.parabolic D := (f31 cs D hD D (fun _ h => h)).property
      have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_left hzz
      have h1 := hlen u⁻¹ (inv_mem hu)
      have h2 := hlen (u * z) (mul_mem hu hz)
      have hi : cs.length (z * u⁻¹) = cs.length (u * z) := by
        rw [← cs.length_inv (z * u⁻¹), mul_inv_rev, inv_inv, hzinv]
      rw [hi, cs.length_inv] at h1
      change cs.length (z * u * z) = cs.length u
      rw [mul_assoc]
      omega
    have f38 (cs : CoxeterSystem M W) (D : Set S)
        (hD : Finite (cs.parabolic D)) (a : D) (u : W)
        (hu : u ∈ cs.parabolic (D \ {(a : S)})) :
        let z := (f31 cs D hD D (fun _ h => h)).val
        z * u * z ∈ cs.parabolic (D \ {(f33 cs D hD a : S)}) := by
      clear * - S W inst M cs J D hD a u hu f31 f33 f34
      dsimp only
      let z := (f31 cs D hD D (fun _ h => h)).val
      obtain ⟨_, hzz, hinv, _, hgen⟩ := f34 cs D hD
      have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_left hzz
      obtain ⟨v, hv, rfl⟩ := cs.exists_wordProd_eq_of_mem_parabolic hu
      clear hu
      induction v with
      | nil => simpa [cs.wordProd_nil, hzz] using (cs.parabolic (D \ {(f33 cs D hD a : S)})).one_mem
      | cons i v ih =>
        have hi := hv i (by simp)
        have hidx : (f33 cs D hD ⟨i,hi.1⟩ : S) ≠ (f33 cs D hD a : S) := by
          intro he
          have h := (f33 cs D hD).injective (Subtype.ext he)
          exact hi.2 (congrArg Subtype.val h)
        have hg : z * cs.simple i * z = cs.simple (f33 cs D hD ⟨i,hi.1⟩ : S) := by
          have h := hgen ⟨i,hi.1⟩
          change z * cs.simple i * z⁻¹ = _ at h
          simpa only [hzinv] using h
        have heq : z * cs.wordProd (i :: v) * z =
            (z * cs.simple i * z) * (z * cs.wordProd v * z) := by
          rw [cs.wordProd_cons]
          symm
          calc
            _ = z * cs.simple i * (z * z) * cs.wordProd v * z := by group
            _ = _ := by rw [hzz]; group
        rw [heq, hg]
        exact mul_mem (cs.simple_mem_parabolic ⟨(f33 cs D hD ⟨i,hi.1⟩).property, hidx⟩)
          (ih (fun j hj => hv j (by simp [hj])))
    have f39 (cs : CoxeterSystem M W) (D : Set S)
        (hD : Finite (cs.parabolic D)) (a : D) :
        let z := (f31 cs D hD D (fun _ h => h)).val
        (f31 cs D hD (D \ {(f33 cs D hD a : S)}) Set.sdiff_subset).val =
          z * (f31 cs D hD (D \ {(a : S)}) Set.sdiff_subset).val * z := by
      clear * - S W inst M cs J D hD a f37 f38 f31 f32 f36 f33 f34
      dsimp only
      let z := (f31 cs D hD D (fun _ h => h)).val
      let y := f31 cs D hD (D \ {(a : S)}) Set.sdiff_subset
      let b := f33 cs D hD a
      let t := f31 cs D hD (D \ {(b : S)}) Set.sdiff_subset
      have hc := f38 cs D hD a y.val y.property
      let r : cs.parabolic (D \ {(b : S)}) := ⟨z * y.val * z, hc⟩
      have hinv := (f34 cs D hD).2.2.1 a
      have hrmax (u : cs.parabolic (D \ {(b : S)})) : cs.length u.val ≤ cs.length r.val := by
        have hu := f38 cs D hD b u.val u.property
        change z * u.val * z ∈ cs.parabolic (D \ {(f33 cs D hD b : S)}) at hu
        have hop : (f33 cs D hD b : S) = a := congrArg Subtype.val hinv
        rw [hop] at hu
        have hm := f32 cs D hD (D \ {(a : S)}) Set.sdiff_subset ⟨_,hu⟩
        rw [f37 cs D hD u.val (cs.parabolic_mono Set.sdiff_subset u.property)] at hm
        change cs.length u.val ≤ cs.length (z * y.val * z)
        rw [f37 cs D hD y.val (cs.parabolic_mono Set.sdiff_subset y.property)]
        exact hm
      exact congrArg Subtype.val (f36 cs (D \ {(b : S)}) t r
        (f32 cs D hD (D \ {(b : S)}) Set.sdiff_subset) hrmax)
    have f40 (T : Set S) (b : S) (hb : b ∈ T) :
        Set.insert b (T \ {b}) = T := by
      clear * - S W inst M cs J T b hb
      classical
      ext x
      change (x = b ∨ (x ∈ T ∧ x ≠ b)) ↔ x ∈ T
      by_cases h : x = b <;> aesop
    have f41 (M : CoxeterMatrix S) (I : Set S) (a b : S)
        (hb : b ∈ f28 M I a) :
        f28 M (Set.insert a I \ {b}) b = f28 M I a := by
      clear * - S W inst M cs J I a b hb f28 f40
      have hs := f40 (Set.insert a I) b hb.1
      unfold f28
      rw [hs]
      let R := fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2
      have rev {x y : S} (h : Relation.ReflTransGen R x y) : Relation.ReflTransGen R y x := by
        induction h with
        | refl => exact .refl
        | @tail y z hp he ih =>
          exact ih.head ⟨he.2.1, he.1, he.2.2.1.symm, fun hz => he.2.2.2 ((M.symmetric _ _).trans hz)⟩
      have hab : Relation.ReflTransGen R a b := hb.2
      ext d
      constructor
      · rintro ⟨hd,hp⟩
        exact ⟨hd, hab.trans hp⟩
      · rintro ⟨hd,hp⟩
        exact ⟨hd, (rev hab).trans hp⟩
    have f42 (cs : CoxeterSystem M W) (I D : Set S) (a : S)
        (ha : a ∉ I) (haD : a ∈ D) (hcomp : f28 M I a = D)
        (hD : Finite (cs.parabolic D)) (hF : Finite (cs.parabolic (f28 M I a))) :
        SimpleWallCrossings S W M cs I a ha hF =
          ((f31 cs D hD (D \ {a}) Set.sdiff_subset).val *
            (f31 cs D hD D (fun _ h => h)).val,
            Set.insert a I \ {(f33 cs D hD ⟨a,haD⟩ : S)},
            fun x => (x * ((f31 cs D hD (D \ {a}) Set.sdiff_subset).val *
            (f31 cs D hD D (fun _ h => h)).val),
            Set.insert a I \ {(f33 cs D hD ⟨a,haD⟩ : S)})) := by
      clear * - S W inst M cs J I D a ha haD hcomp hD hF f28 f31 f33
      subst D
      rfl
    have f43 (cs : CoxeterSystem M W) (I : Set S) (a : S)
        (ha : a ∉ I) (hD : Finite (cs.parabolic (f28 M I a))) :
        let D := f28 M I a
        let aD : D := ⟨a, Set.mem_insert a I, Relation.ReflTransGen.refl⟩
        let b : S := f33 cs D hD aD
        let forward := SimpleWallCrossings S W M cs I a ha hD
        b ∈ D ∧ Set.insert b forward.2.1 = Set.insert a I ∧
        f28 M forward.2.1 b = D ∧
        ∃ (hb : b ∉ forward.2.1)
          (hD' : Finite (cs.parabolic (f28 M forward.2.1 b))),
          let reverse := SimpleWallCrossings S W M cs forward.2.1 b hb hD'
          reverse.2.1 = I ∧ reverse.1 = forward.1⁻¹ ∧
          forward.1 * reverse.1 = 1 ∧ reverse.1 * forward.1 = 1 := by
      clear * - S W inst M cs J I a ha hD f28 f41 f35 f42 f40 f31 f39 f32 f33 f29 f34
      classical
      dsimp only
      let D := f28 M I a
      let aD : D := ⟨a, Set.mem_insert a I, Relation.ReflTransGen.refl⟩
      let ν := f33 cs D hD
      let b : S := ν aD
      let K : Set S := Set.insert a I \ {b}
      let z : W := f31 cs D hD D (fun _ h => h)
      let y : W := f31 cs D hD (D \ {a}) Set.sdiff_subset
      let t : W := f31 cs D hD (D \ {b}) Set.sdiff_subset
      have hdata := f35 cs I a ha hD
      change SimpleWallCrossings S W M cs I a ha hD =
        (y * z, K, fun x => (x * (y * z), K)) at hdata
      rw [hdata]
      dsimp only
      have hbD : b ∈ D := (ν aD).property
      have hbL : b ∈ Set.insert a I := hbD.1
      have hb : b ∉ K := fun h => h.2 rfl
      have hset : Set.insert b K = Set.insert a I := f40 _ _ hbL
      have hcomp : f28 M K b = D := f41 M I a b hbD
      have hD' : Finite (cs.parabolic (f28 M K b)) := hcomp.symm ▸ hD
      refine ⟨hbD, hset, hcomp, hb, hD', ?_⟩
      have hreverse := f42 cs K D b hb hbD hcomp hD hD'
      have hνinv := (f34 cs D hD).2.2.1
      have hop : (ν ⟨b,hbD⟩ : S) = a := congrArg Subtype.val (hνinv aD)
      have htarget : Set.insert b K \ {(ν ⟨b,hbD⟩ : S)} = I := by
        rw [hop, hset]
        apply Set.ext
        intro i
        change ((i = a ∨ i ∈ I) ∧ i ≠ a) ↔ i ∈ I
        constructor
        · exact fun h => h.1.resolve_left (fun hi => h.2 hi)
        · intro hi
          exact ⟨Or.inr hi, fun he => ha (he ▸ hi)⟩
      change SimpleWallCrossings S W M cs K b hb hD' =
        (t * z, Set.insert b K \ {(ν ⟨b,hbD⟩ : S)},
          fun x => (x * (t * z), Set.insert b K \ {(ν ⟨b,hbD⟩ : S)})) at hreverse
      rw [htarget] at hreverse
      rw [hreverse]
      dsimp only
      have zz := (f34 cs D hD).2.1
      have yy := (f29 cs (D \ {a})
        (f31 cs D hD (D \ {a}) Set.sdiff_subset)
        (f32 cs D hD (D \ {a}) Set.sdiff_subset)).2.1
      have hconj : t = z * y * z := f39 cs D hD aD
      have hzInv : z⁻¹ = z := inv_eq_of_mul_eq_one_left zz
      have hyInv : y⁻¹ = y := inv_eq_of_mul_eq_one_left yy
      have hlabel : t * z = (y * z)⁻¹ := by
        rw [hconj, mul_assoc (z * y) z z, zz, mul_one, mul_inv_rev, hzInv, hyInv]
      refine ⟨rfl, hlabel, ?_, ?_⟩
      · rw [hlabel, mul_inv_cancel]
      · rw [hlabel, inv_mul_cancel]
    let f44 {A : Type _} (R : A → A → Prop) (p : A) (es : List A) : Prop :=
      es.foldr (fun e tail p => R p e ∧ tail e) (fun _ => True) p
    have f45 {A : Type _} (R : A → A → Prop)
        (hdet : ∀ p e f, R p e → R p f → e = f)
        (p : A) (es fs : List A) (he : f44 R p es) (hf : f44 R p fs)
        (hlen : es.length = fs.length) : es = fs := by
      clear * - S W inst M cs J A R hdet p es fs he hf hlen f44
      induction es generalizing p fs with
      | nil => cases fs <;> simp_all
      | cons e es ih =>
        cases fs with
        | nil => simp at hlen
        | cons f fs =>
          have hef := hdet p e f he.1 hf.1
          subst f
          have ht := ih e fs he.2 hf.2 (by simpa using hlen)
          exact congrArg (List.cons e) ht
    let f46 {A : Type _} (value : A → W) (es : List A) : W := (es.map value).prod
    let f47 {A : Type _} (cs : CoxeterSystem M W) (value : A → W) (es : List A) : ℕ :=
      (es.map (fun e => cs.length (value e))).sum
    have f48 {A : Type _} (cs : CoxeterSystem M W) (value : A → W) (es : List A) :
        cs.length (f46 value es) ≤ f47 cs value es := by
      clear * - S W inst M cs J A value es f46 f47
      induction es with
      | nil => simp [f46,f47]
      | cons e es ih =>
        change cs.length (value e * f46 value es) ≤ cs.length (value e) + f47 cs value es
        exact (cs.length_mul_le _ _).trans (Nat.add_le_add_left ih _)
    have f49 {A : Type _} (cs : CoxeterSystem M W) (value : A → W) (e : A) (es : List A)
        (h : cs.length (f46 value (e :: es)) = f47 cs value (e :: es)) :
        cs.length (f46 value es) = f47 cs value es := by
      clear * - S W inst M cs J A value e es h f46 f47 f48
      have hb := f48 cs value es
      have hm := cs.length_mul_le (value e) (f46 value es)
      change cs.length (value e * f46 value es) = cs.length (value e) + f47 cs value es at h
      omega
    have f50 {A : Type _} (cs : CoxeterSystem M W) (value : A → W)
        (e f : A) (es : List A)
        (hpos : 0 < cs.length (value e))
        (h : cs.length (f46 value (e :: f :: es)) = f47 cs value (e :: f :: es)) :
        value e * value f ≠ 1 := by
      clear * - S W inst M cs J A value e f es hpos h f46 f47 f48
      intro hback
      have hb := f48 cs value es
      change cs.length (value e * (value f * f46 value es)) =
        cs.length (value e) + (cs.length (value f) + f47 cs value es) at h
      rw [← mul_assoc, hback, one_mul] at h
      omega
    -- Endpoint tags remain in the same global f51 type throughout.
    let f52 (cs : CoxeterSystem M W) (J : Set S) :=
      {L : Set S // ∃ g : W, Subgroup.map (MulAut.conj g).toMonoidHom
        (cs.parabolic L) = cs.parabolic J}
    let f53 (M : CoxeterMatrix S) (L : Set S) (c : S) : Set S :=
      {d | d ∈ Set.insert c L ∧ Relation.ReflTransGen
        (fun i j : S => i ∈ Set.insert c L ∧ j ∈ Set.insert c L ∧ i ≠ j ∧ M i j ≠ 2) c d}
    let f51 (cs : CoxeterSystem M W) (J : Set S) :=
      {p : f52 cs J × S // p.2 ∉ p.1.val ∧ Finite (cs.parabolic (f53 M p.1.val p.2))}
    let f54 (cs : CoxeterSystem M W) {J : Set S} (e : f51 cs J) :=
      SimpleWallCrossings S W M cs e.val.1.val e.val.2 e.property.1 e.property.2
    let f55 (cs : CoxeterSystem M W) {J : Set S}
        (es : List (f51 cs J)) (L K : Set S) : Prop :=
      List.foldr (fun e tail N => N = e.val.1.val ∧ tail (f54 cs e).2.1)
        (fun N => N = K) es L
    let f56 (cs : CoxeterSystem M W) {J : Set S} (Good : f51 cs J → Prop)
        (p e : f51 cs J) : Prop :=
      Good p ∧ Good e ∧ e.val.1.val = (f54 cs p).2.1 ∧
        (f54 cs p).1 * (f54 cs e).1 ≠ 1
    have f57 (cs : CoxeterSystem M W) (J : Set S)
        (Good : f51 cs J → Prop)
        (hpos : ∀ e, Good e → 0 < cs.length (f54 cs e).1)
        (p : f51 cs J) (es : List (f51 cs J)) (L K : Set S)
        (hcomp : f55 cs (p :: es) L K)
        (hgood : ∀ e ∈ p :: es, Good e)
        (hadd : cs.length (f46 (fun e : f51 cs J => (f54 cs e).1) (p :: es)) =
          f47 cs (fun e : f51 cs J => (f54 cs e).1) (p :: es)) :
        f44 (f56 cs Good) p es := by
      clear * - S W inst M cs J Good hpos p es L K hcomp hgood hadd f51 f44 f55 f56 f54 f50 f46 f49 f47
      induction es generalizing p L with
      | nil => trivial
      | cons e es ih =>
        have htail : f55 cs (e :: es) (f54 cs p).2.1 K := hcomp.2
        have hsource : e.val.1.val = (f54 cs p).2.1 := htail.1.symm
        have hp := hgood p (by simp)
        have he := hgood e (by simp)
        refine ⟨⟨hp, he, hsource, f50 cs _ p e es (hpos p hp) hadd⟩, ?_⟩
        exact ih e _ htail (fun t ht => hgood t (by simp [ht])) (f49 cs _ p _ hadd)
    have f58 (cs : CoxeterSystem M W) (J : Set S)
        (Good : f51 cs J → Prop)
        (hpos : ∀ e, Good e → 0 < cs.length (f54 cs e).1)
        (hdet : ∀ p e f, f56 cs Good p e → f56 cs Good p f → e = f)
        (I K : f52 cs J) (q : (BrinkHowlettGroupoid cs J).Hom I K)
        (e f : StandardExpressions cs J I K q)
        (he : ∀ t ∈ e.val, Good t) (hf : ∀ t ∈ f.val, Good t)
        (p : f51 cs J) (es fs : List (f51 cs J))
        (hes : e.val = p :: es) (hfs : f.val = p :: fs) : e = f := by
      clear * - S W inst M cs J Good hpos hdet I K q e f he hf p es fs hes hfs f51 f55 f56 f52 f45 f54 f46 f57 f47
      have hel : cs.length (f46 (fun t : f51 cs J => (f54 cs t).1) e.val) =
          f47 cs (fun t : f51 cs J => (f54 cs t).1) e.val := by
        have hp : f46 (fun t : f51 cs J => (f54 cs t).1) e.val = q.val := e.property.2.1
        rw [hp]
        exact e.property.2.2
      have hfl : cs.length (f46 (fun t : f51 cs J => (f54 cs t).1) f.val) =
          f47 cs (fun t : f51 cs J => (f54 cs t).1) f.val := by
        have hp : f46 (fun t : f51 cs J => (f54 cs t).1) f.val = q.val := f.property.2.1
        rw [hp]
        exact f.property.2.2
      have hec : f55 cs e.val I.val K.val := e.property.1
      have hfc : f55 cs f.val I.val K.val := f.property.1
      rw [hes] at he hec hel
      rw [hfs] at hf hfc hfl
      have hc := f45 (f56 cs Good) hdet p es fs
        (f57 cs J Good hpos p es _ _ hec he hel)
        (f57 cs J Good hpos p fs _ _ hfc hf hfl)
        (by have h := (GeneratorsAndStandardLength cs J).2 I K q e f; rw [hes,hfs] at h; exact Nat.add_right_cancel h)
      apply Subtype.ext
      rw [hes,hfs,hc]
    let f59
        (cs : CoxeterSystem M W) (J : Set S) :=
      {L : Set S // ∃ g : W, Subgroup.map (MulAut.conj g).toMonoidHom
        (cs.parabolic L) = cs.parabolic J}
    let f60  (M : CoxeterMatrix S) (L : Set S) (c : S) : Set S :=
      {d | d ∈ Set.insert c L ∧ Relation.ReflTransGen
        (fun i j : S => i ∈ Set.insert c L ∧ j ∈ Set.insert c L ∧ i ≠ j ∧ M i j ≠ 2) c d}
    let f61
        (cs : CoxeterSystem M W) (J : Set S) :=
      {p : f59 cs J × S // p.2 ∉ p.1.val ∧ Finite (cs.parabolic (f60 M p.1.val p.2))}
    -- Local implementation helper for Lemma 4.15/(4.16), printed p.19.
    -- It is not a separately stated article result.
    have f62
        (cs : CoxeterSystem M W) (J : Set S) (I K : f59 cs J)
        (q : (BrinkHowlettGroupoid cs J).Hom I K)
        (c : S) (hc : c ∉ I.val) (hD : Finite (cs.parabolic (f60 M I.val c)))
        (hp : cs.length q.val =
          cs.length (SimpleWallCrossings S W M cs I.val c hc hD).1 +
          cs.length ((SimpleWallCrossings S W M cs I.val c hc hD).1⁻¹ * q.val)) :
        ∃ e : StandardExpressions cs J I K q,
          ∃ tail : List (f61 cs J), e.val = ⟨(I,c), ⟨hc,hD⟩⟩ :: tail := by
      clear * - S W inst M cs J I K q c hc hD hp f61 f59 f60
      classical
      let v := SimpleWallCrossings S W M cs I.val c hc hD
      obtain ⟨hC, f, hf⟩ := ElementaryWallMorphism cs J I.val I.property c hc hD
      let C : f59 cs J := ⟨v.2.1, hC⟩
      let z : (BrinkHowlettGroupoid cs J).Hom C K :=
        (BrinkHowlettGroupoid cs J).comp ((BrinkHowlettGroupoid cs J).inv f) q
      have hz : z.val = v.1⁻¹ * q.val := by
        change f.val⁻¹ * q.val = _
        rw [hf]
      obtain ⟨ez⟩ := (StandardFactorCount cs J C K z).1
      let atom : f61 cs J := ⟨(I,c), ⟨hc,hD⟩⟩
      refine ⟨⟨atom :: ez.val, ?_, ?_, ?_⟩, ez.val, rfl⟩
      · exact ⟨rfl, ez.property.1⟩
      · change v.1 * List.prod (List.map _ ez.val) = q.val
        rw [ez.property.2.1, hz]
        exact mul_inv_cancel_left _ _
      · change cs.length q.val = cs.length v.1 + List.sum (List.map _ ez.val)
        rw [← ez.property.2.2, hz]
        exact hp
    -- Independent prescribed initial words; no rank-two classification is used.
    have f63
        (cs : CoxeterSystem M W) (J : Set S) (I K : f59 cs J)
        (q : (BrinkHowlettGroupoid cs J).Hom I K)
        (a b : S) (ha : a ∉ I.val) (hb : b ∉ I.val) (hab : a ≠ b)
        (hDa : Finite (cs.parabolic (f60 M I.val a)))
        (hDb : Finite (cs.parabolic (f60 M I.val b)))
        (hpa : cs.length q.val = cs.length (SimpleWallCrossings S W M cs I.val a ha hDa).1 +
          cs.length ((SimpleWallCrossings S W M cs I.val a ha hDa).1⁻¹ * q.val))
        (hpb : cs.length q.val = cs.length (SimpleWallCrossings S W M cs I.val b hb hDb).1 +
          cs.length ((SimpleWallCrossings S W M cs I.val b hb hDb).1⁻¹ * q.val)) :
        ∃ ea eb : StandardExpressions cs J I K q,
          ea ≠ eb ∧ ea.val.length = eb.val.length ∧
          (∃ ta : List (f61 cs J), ea.val = ⟨(I,a), ⟨ha,hDa⟩⟩ :: ta) ∧
          (∃ tb : List (f61 cs J), eb.val = ⟨(I,b), ⟨hb,hDb⟩⟩ :: tb) := by
      clear * - S W inst M cs J I K q a b ha hb hab hDa hDb hpa hpb f61 f59 f60 f62
      obtain ⟨ea, ta, hta⟩ := f62 cs J I K q a ha hDa hpa
      obtain ⟨eb, tb, htb⟩ := f62 cs J I K q b hb hDb hpb
      refine ⟨ea, eb, ?_, (GeneratorsAndStandardLength cs J).2 I K q ea eb,
        ⟨ta,hta⟩, ⟨tb,htb⟩⟩
      intro heq
      have h := congrArg Subtype.val heq
      rw [hta, htb] at h
      exact hab (congrArg (fun e : f61 cs J => e.val.2) (List.cons.inj h).1)
    -- Sufficient exhaustion boundary; does not assert this missing boundary.
    let f64 (cs : CoxeterSystem M W) (J : Set S) := f52 cs J
    let f65 (cs : CoxeterSystem M W) (J : Set S) := f51 cs J
    let f66 (cs : CoxeterSystem M W) {J : Set S} (e : f65 cs J) :=
      f54 cs e
    have f67 (cs : CoxeterSystem M W) (J : Set S) (e : f65 cs J) :
        0 < cs.length (f66 cs e).1 := by
      clear * - S W inst M cs J e f65 f66 f11
      by_contra hn
      have hz : (f66 cs e).1 = 1 := cs.length_eq_zero_iff.mp (Nat.eq_zero_of_not_pos hn)
      have hm : (f66 cs e).1 ∈ cs.parabolic (∅ : Set S) := by
        rw [hz]
        exact (cs.parabolic ∅).one_mem
      have h := f11 cs e.val.1.val ∅ e.val.2 e.property.1 e.property.2 hm
      exact h
    let f68 (cs : CoxeterSystem M W) (J : Set S) (D E : Set S) (e : f65 cs J) : Prop :=
      f13 D E e.val.1.val ∧ e.val.2 ∈ D ∧
        f1 (M := M) e.val.1.val e.val.2 ⊆ D ∧
        (f66 cs e).1 ∈ cs.parabolic D
    have f69 (cs : CoxeterSystem M W) (J : Set S) (D E : Set S)
        (hdis : Disjoint D E) (hsep : ∀ i ∈ D, ∀ j ∈ E, M i j = 2)
        (p : f65 cs J) (hp : f68 cs J D E p) :
        ∃ r : f65 cs J, f68 cs J D E r ∧
          r.val.1.val = (f66 cs p).2.1 ∧
          (f66 cs p).1 * (f66 cs r).1 = 1 := by
      clear * - S W inst M cs J D E hdis hsep p hp f65 f68 f64 f66 f13 f1 f18 f28 f33 f43
      classical
      obtain ⟨hbF, _, hcomp, hb, hF, ht, hlabel, hmul, _⟩ :=
        f43 cs p.val.1.val p.val.2 p.property.1 p.property.2
      obtain ⟨hC, f, hf⟩ := ElementaryWallMorphism cs J p.val.1.val p.val.1.property
        p.val.2 p.property.1 p.property.2
      let b : S := f33 cs
        (f28 M p.val.1.val p.val.2) p.property.2
        ⟨p.val.2, Set.mem_insert _ _, Relation.ReflTransGen.refl⟩
      let C : f64 cs J := ⟨(f66 cs p).2.1, hC⟩
      let r : f65 cs J := ⟨(C,b), hb,hF⟩
      have hstate : f13 D E C.val :=
        f18 cs D E p.val.1.val hdis hsep hp.1 p.val.2
          p.property.1 hp.2.1 p.property.2
      have hbD : b ∈ D := hp.2.2.1 hbF
      have hFD : f1 (M := M) C.val b ⊆ D := by
        change f28 M (f66 cs p).2.1 b ⊆ D
        have hc : f28 M (f66 cs p).2.1 b =
            f28 M p.val.1.val p.val.2 := hcomp
        rw [hc]
        exact hp.2.2.1
      have hval : (f66 cs r).1 = (f66 cs p).1⁻¹ := hlabel
      refine ⟨r, ⟨hstate, hbD, hFD, ?_⟩, rfl, hmul⟩
      rw [hval]
      exact inv_mem hp.2.2.2
    have f70 (cs : CoxeterSystem M W) (J : Set S) (D E : Set S)
        (hdis : Disjoint D E) (hsep : ∀ i ∈ D, ∀ j ∈ E, M i j = 2)
        (p e f : f65 cs J)
        (he : f56 cs (f68 cs J D E) p e)
        (hf : f56 cs (f68 cs J D E) p f) : e = f := by
      clear * - S W inst M cs J D E hdis hsep p e f he hf f56 f65 f68 f69 f26 f27
      obtain ⟨r, hr, hrs, hback⟩ := f69 cs J D E hdis hsep p he.1
      obtain ⟨x,hx,y,hy,hxy,hout⟩ := f27 cs D E r.val.1.val hdis hr.1
      have hes : e.val.1.val = r.val.1.val := he.2.2.1.trans hrs.symm
      have hfs : f.val.1.val = r.val.1.val := hf.2.2.1.trans hrs.symm
      have hei := hout e hes he.2.1.2.2.2
      have hfi := hout f hfs hf.2.1.2.2.2
      have hri := hout r rfl hr.2.2.2
      have hd : e.val.2 = f.val.2 ∨ e.val.2 = r.val.2 ∨ f.val.2 = r.val.2 := by
        rcases hei with he | he <;> rcases hfi with hf | hf <;> rcases hri with hr | hr <;>
          first | exact Or.inl (he.trans hf.symm) | exact Or.inr (Or.inl (he.trans hr.symm)) | exact Or.inr (Or.inr (hf.trans hr.symm))
      rcases hd with hi | hi | hi
      · exact f26 cs e f (hes.trans hfs.symm) hi
      · have her := f26 cs e r hes hi
        exact False.elim (he.2.2.2 (her.symm ▸ hback))
      · have hfr := f26 cs f r hfs hi
        exact False.elim (hf.2.2.2 (hfr.symm ▸ hback))
    have f0 (cs : CoxeterSystem M W) (J : Set S) (I K : f64 cs J)
        (a b : S) (ha : a ∉ I.val) (hb : b ∉ I.val) (hab : a ≠ b)
        (hfin : Set.Finite (f3 cs (Set.insert a (Set.insert b I.val)) \
          f3 cs I.val))
        (hDa : Finite (cs.parabolic (f53 M I.val a)))
        (hDb : Finite (cs.parabolic (f53 M I.val b)))
        (q : (BrinkHowlettGroupoid cs J).Hom I K)
        (hN : f4 cs q.val =
          (f3 cs (Set.insert a (Set.insert b I.val)) ∩
            {x | x ∈ cs.geometricRoots ∧ 0 < x}) \
          (f3 cs I.val ∩ {x | x ∈ cs.geometricRoots ∧ 0 < x}))
        (hpa : cs.length q.val = cs.length (SimpleWallCrossings S W M cs I.val a ha hDa).1 +
          cs.length ((SimpleWallCrossings S W M cs I.val a ha hDa).1⁻¹ * q.val))
        (hpb : cs.length q.val = cs.length (SimpleWallCrossings S W M cs I.val b hb hDb).1 +
          cs.length ((SimpleWallCrossings S W M cs I.val b hb hDb).1⁻¹ * q.val)) :
        ∃ ea eb : StandardExpressions cs J I K q,
          ea ≠ eb ∧ (∀ e : StandardExpressions cs J I K q, e = ea ∨ e = eb) ∧
          (∃ ta : List (f65 cs J), ea.val = ⟨(I,a),ha,hDa⟩ :: ta) ∧
          (∃ tb : List (f65 cs J), eb.val = ⟨(I,b),hb,hDb⟩ :: tb) := by
      classical
      obtain ⟨ea,eb,hne,hlen,⟨ta,hta⟩,⟨tb,htb⟩⟩ :=
        f63 cs J I K q a b ha hb hab hDa hDb hpa hpb
      have hta' : ea.val = (⟨(I,a),ha,hDa⟩ : f65 cs J) :: ta := hta
      have htb' : eb.val = (⟨(I,b),hb,hDb⟩ : f65 cs J) :: tb := htb
      let D := f2 (M := M) I.val a b
      let E := I.val \ D
      have hdis : Disjoint D E := Set.disjoint_left.mpr (fun _ hd he => he.2 hd)
      have hsep : ∀ i ∈ D, ∀ j ∈ E, M i j = 2 :=
        (f12 (M := M) I.val a b).2.2.2
      have hall (e : StandardExpressions cs J I K q) : ∀ t ∈ e.val, f68 cs J D E t := by
        intro t ht
        have h := ((f24 cs J I K a b ha hb hab hfin q hN e).2.2 t ht)
        exact ⟨h.2.1, h.2.2.1, h.2.2.2, h.1⟩
      have hpos : ∀ t : f65 cs J, f68 cs J D E t → 0 < cs.length (f66 cs t).1 :=
        fun t _ => f67 cs J t
      refine ⟨ea,eb,hne,?_,⟨ta,hta⟩,⟨tb,htb⟩⟩
      intro e
      have helen := (GeneratorsAndStandardLength cs J).2 I K q e ea
      have hnon : e.val ≠ [] := by
        intro hempty
        have hlencons : e.val.length = ta.length + 1 :=
          helen.trans (congrArg List.length hta')
        have hzero : e.val.length = 0 := congrArg List.length hempty
        omega
      obtain ⟨p,es,hes⟩ := List.exists_cons_of_ne_nil hnon
      have hp := hall e p (hes.symm ▸ List.mem_cons_self)
      have hs : I.val = p.val.1.val := by
        have hc : f55 cs e.val I.val K.val := e.property.1
        rw [hes] at hc
        exact hc.1
      have hip : p.val.2 ∈ D := hp.2.1
      have hin : p.val.2 ∉ I.val := hs.symm ▸ p.property.1
      have hidx : p.val.2 = a ∨ p.val.2 = b := by
        have ht := (f12 (M := M) I.val a b).2.2.1 hip
        rcases ht with ht | ht | ht
        · exact Or.inl ht
        · exact Or.inr ht
        · exact False.elim (hin ht)
      rcases hidx with hi | hi
      · left
        have hpatom : p = (⟨(I,a),ha,hDa⟩ : f65 cs J) := f26 cs _ _ hs.symm hi
        apply f58 cs J (f68 cs J D E) hpos
          (f70 cs J D E hdis hsep) I K q e ea (hall e) (hall ea) p es ta hes
        exact hta'.trans (congrArg (fun t : f65 cs J => t :: ta) hpatom.symm)
      · right
        have hpatom : p = (⟨(I,b),hb,hDb⟩ : f65 cs J) := f26 cs _ _ hs.symm hi
        apply f58 cs J (f68 cs J D E) hpos
          (f70 cs J D E hdis hsep) I K q e eb (hall e) (hall eb) p es tb hes
        exact htb'.trans (congrArg (fun t : f65 cs J => t :: tb) hpatom.symm)
    clear * - S W inst M cs J f0 f29
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
    change ∀ (I : Obj) (a b : S) (ha : a ∉ I.val) (hb : b ∉ I.val), _
    intro I a b ha hb hab hfin
    let T := Set.insert a (Set.insert b I.val)
    let D : Set S := {i | i ∈ T ∧ (Relation.ReflTransGen
      (fun j k : S => j ∈ T ∧ k ∈ T ∧ j ≠ k ∧ M j k ≠ 2) a i ∨
      Relation.ReflTransGen
      (fun j k : S => j ∈ T ∧ k ∈ T ∧ j ≠ k ∧ M j k ≠ 2) b i)}
    -- Portal step 1.1: inverse relative-longest arrow.
    have hlong := FiniteRelativeLongest cs I.val a b ha hb hab hfin
    obtain ⟨hD, wD, wDI, hmaxD, hmaxDI, Kset, hKT, hKI, hr, hq, hN⟩ := hlong
    have hcomp (c : S) (hc : c = a ∨ c = b) : component I.val c ⊆ D := by
      have hT : Set.insert c I.val ⊆ T := by
        intro i hi
        rcases Set.mem_insert_iff.mp hi with rfl | hi
        · rcases hc with rfl | rfl
          · exact Set.mem_insert _ _
          · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
        · exact Set.mem_insert_of_mem a (Set.mem_insert_of_mem b hi)
      intro d hd
      have hp : Relation.ReflTransGen
          (fun j k : S => j ∈ T ∧ k ∈ T ∧ j ≠ k ∧ M j k ≠ 2) c d := by
        exact Relation.ReflTransGen.mono
          (fun i j hij => ⟨hT hij.1, hT hij.2.1, hij.2.2⟩) c d hd.2
      exact ⟨hT hd.1, hc.elim (fun h => Or.inl (h ▸ hp)) (fun h => Or.inr (h ▸ hp))⟩
    have subfinite (L : Set S) (hL : L ⊆ D) : Finite (cs.parabolic L) := by
      letI : Finite (cs.parabolic D) := hD
      exact Finite.of_injective
        (fun x : cs.parabolic L =>
          (⟨x.val, cs.parabolic_mono hL x.property⟩ : cs.parabolic D))
        (fun x y h => Subtype.ext (congrArg (fun t : cs.parabolic D => t.val) h))
    let hDa := subfinite (component I.val a) (hcomp a (Or.inl rfl))
    let hDb := subfinite (component I.val b) (hcomp b (Or.inr rfl))
    refine ⟨hDa, hDb, ?_⟩
    let va := (SimpleWallCrossings S W M cs I.val a ha hDa).1
    let vb := (SimpleWallCrossings S W M cs I.val b hb hDb).1
    have hK : ∃ g : W,
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (cs.parabolic Kset) = cs.parabolic J := by
      obtain ⟨g, hg⟩ := I.property
      obtain ⟨k, hk⟩ := hKI
      refine ⟨g * k, ?_⟩
      have heq : (MulAut.conj (g * k)).toMonoidHom =
          (MulAut.conj g).toMonoidHom.comp (MulAut.conj k).toMonoidHom := by
        ext x
        simp [MulAut.conj_apply, mul_assoc]
      rw [heq, ← Subgroup.map_map, hk, hg]
    let K : Obj := ⟨Kset, hK⟩
    let q : (BrinkHowlettGroupoid cs J).Hom I K := ⟨((wD : W) * (wDI : W))⁻¹, hq⟩
    have hNq : N q.val = (parabolicRoots T ∩ positiveRoots) \
        (parabolicRoots I.val ∩ positiveRoots) := hN
    have roots_mono {L F : Set S} (h : L ⊆ F) : parabolicRoots L ⊆ parabolicRoots F := by
      rintro α ⟨u, hu, i, hi, he⟩
      exact ⟨u, cs.parabolic_mono h hu, i, h hi, he⟩
    have image_N (x : W) (α : Finsupp S Real) :
        α ∈ N x ↔ α ∈ cs.geometricRoots ∧ 0 < α ∧ cs.geometricRepresentation x⁻¹ α < 0 := by
      constructor
      · rintro ⟨hp, β, hn, rfl⟩
        exact ⟨hp.1, hp.2, by simpa only [Representation.inv_self_apply] using hn.2⟩
      · rintro ⟨hr, hp, hn⟩
        refine ⟨⟨hr, hp⟩, cs.geometricRepresentation x⁻¹ α,
          ⟨(cs.geometricRepresentation_apply_mem_geometricRoots_iff x⁻¹).mpr hr, hn⟩, ?_⟩
        exact Representation.self_inv_apply _ _ _
    have prefix_of_N {x y : W} (h : N x ⊆ N y) : leftDiv x y := by
      apply (ArtinNormalisers.Chamber3.length_eq_add_iff_rootInversions_subset_system cs x y).mpr
      intro α hr hp hn
      exact ((image_N y α).mp (h ((image_N x α).mpr ⟨hr, hp, hn⟩))).2.2
    -- Step 2.1: the elementary inversion formula is proved above.
    have hNa : N va = (parabolicRoots (Set.insert a I.val) ∩ positiveRoots) \
        (parabolicRoots I.val ∩ positiveRoots) :=
      ElementaryRootInversions cs I.val a ha hDa
    have hNb : N vb = (parabolicRoots (Set.insert b I.val) ∩ positiveRoots) \
        (parabolicRoots I.val ∩ positiveRoots) :=
      ElementaryRootInversions cs I.val b hb hDb
    have hpa : leftDiv va q.val := by
      apply prefix_of_N
      rw [hNa, hNq]
      intro α hα
      refine ⟨⟨roots_mono ?_ hα.1.1, hα.1.2⟩, hα.2⟩
      intro i hi
      exact hi.elim (fun h => h ▸ Set.mem_insert a _) (fun h => Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ h))
    have hpb : leftDiv vb q.val := by
      apply prefix_of_N
      rw [hNb, hNq]
      intro α hα
      refine ⟨⟨roots_mono ?_ hα.1.1, hα.1.2⟩, hα.2⟩
      exact fun i hi => Set.mem_insert_of_mem a hi
    -- Step 2.1: classification by confinement and deterministic continuation.
    obtain ⟨ea, eb, hne, honly, hstarta, hstartb⟩ :=
      f0 cs J I K a b ha hb hab hfin hDa hDb q hNq hpa hpb
    refine ⟨K, q, ea, eb, hpa, hpb, hne, honly,
      (GeneratorsAndStandardLength cs J).2 I K q ea eb, hstarta, hstartb, ?_⟩
    intro K' w hwa hwb
    -- Step 2.2: simultaneous prefix is proved by finite-support coordinates.
    have hqw : leftDiv q.val w.val := by
      apply prefix_of_N
      have prefix_N {u v : W} (h : leftDiv u v) : N u ⊆ N v := by
        intro x hx
        obtain ⟨hr, hp, hn⟩ := (image_N u x).mp hx
        exact (image_N v x).mpr ⟨hr, hp,
          (ArtinNormalisers.Chamber3.length_eq_add_iff_rootInversions_subset_system cs u v).mp h x hr hp hn⟩
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
      rw [hNq]
      rintro x ⟨⟨hxT, hr, hp⟩, hxI⟩
      have hnI : x ∉ orbitRoots cs I.val := fun hh => hxI ⟨hh, hr, hp⟩
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
      exact (image_N w.val x).mpr ⟨hr, hp, hneg⟩
    refine ⟨hqw, ?_⟩
    let z : (BrinkHowlettGroupoid cs J).Hom K K' :=
      (BrinkHowlettGroupoid cs J).comp ((BrinkHowlettGroupoid cs J).inv q) w
    have hz : z.val = q.val⁻¹ * w.val := rfl
    obtain ⟨ez⟩ := (StandardFactorCount cs J K K' z).1
    let Atom := {p : Obj × S // p.2 ∉ p.1.val ∧
      Finite (cs.parabolic (component p.1.val p.2))}
    let crossing := fun e : Atom =>
      SimpleWallCrossings S W M cs e.val.1.val e.val.2 e.property.1 e.property.2
    let composable := fun (es : List Atom) (L F : Set S) =>
      List.foldr (fun e tail N => N = e.val.1.val ∧ tail (crossing e).2.1)
        (fun N => N = F) es L
    -- Step 3.1: endpoint threading, including the empty expression.
    have comp_append (es fs : List Atom) (L F G : Set S)
        (hes : composable es L F) (hfs : composable fs F G) :
        composable (es ++ fs) L G := by
      induction es generalizing L with
      | nil =>
        change L = F at hes
        subst L
        exact hfs
      | cons e es ih =>
        exact ⟨hes.1, ih _ hes.2⟩
    let ecat : StandardExpressions cs J I K' w := by
      refine ⟨ea.val ++ ez.val, comp_append ea.val ez.val I.val K.val K'.val ea.property.1 ez.property.1, ?_, ?_⟩
      · simp only [List.map_append, List.prod_append, ea.property.2.1, ez.property.2.1, hz]
        exact mul_inv_cancel_left _ _
      · simp only [List.map_append, List.sum_append, ← ea.property.2.2, ← ez.property.2.2, hz]
        exact hqw
    intro e
    have hcount := (GeneratorsAndStandardLength cs J).2 I K' w ecat e
    change List.length (ea.val ++ ez.val) = List.length e.val at hcount
    rw [List.length_append] at hcount
    rw [← hcount]
    exact Nat.le_add_right _ _
  )
)
