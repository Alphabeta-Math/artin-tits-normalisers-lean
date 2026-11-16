import Mathlib
import ArtinDeligne
import Proofs.RelativeLocalFiniteness
import Proofs.ChamberLabelling
import Proofs.AdjacentWallFormula

set_option maxHeartbeats 2000000

theorem GeodesicAdditivity : (∀ {S : Type*} [Finite S] (M : CoxeterMatrix S) (J : Set S),
  let W := CoxeterMatrix.Group M
  let cs := CoxeterMatrix.toCoxeterSystem M
  let Label := { p : W × Set S //
    Set.image (fun u : W => u * p.1) (CoxeterSystem.parabolic cs J : Set W) =
      Set.image (fun u : W => p.1 * u) (CoxeterSystem.parabolic cs p.2 : Set W) ∧
    CoxeterSystem.IsMinimalCosetRep cs p.2 p.1 }
  let component : Set S → S → Set S := fun I a =>
    { b | b ∈ Set.insert a I ∧ Relation.ReflTransGen
      (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b }
  let Step := { e : Label × S // e.2 ∉ e.1.val.2 ∧
    Finite (CoxeterSystem.parabolic cs (component e.1.val.2 e.2)) }
  let crossing := fun e : Step =>
    SimpleWallCrossings S W M cs e.val.1.val.2 e.val.2 e.property.1 e.property.2
  let path : Label → Label → List Step → Prop := fun p q es =>
    List.foldr
      (fun e tail r => r = e.val.1.val ∧ tail ((crossing e).2.2 e.val.1.val.1))
      (fun r => r = q.val) es p.val
  ∀ (p q : Label) (es : List Step), path p q es →
    ((∀ fs : List Step, path p q fs → List.length es ≤ List.length fs) ↔
      CoxeterSystem.length cs (List.prod (List.map (fun e => (crossing e).1) es)) =
        List.sum (List.map (fun e => CoxeterSystem.length cs (crossing e).1) es))) :=
(by
  classical
  /-
  Proposition 3.29, printed pp.13–14, https://arxiv.org/pdf/2509.21915#page=13.
  Numbered inspiration: GeodesicAdditivity 1.1 (endpoint products telescope)
  and 2.1 (word induction and nonnegative ambient length deficits):
  https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-prop-geodesic-additivity-artin-tits-normalisers.
  Necessary departure from the geometric route in 1.1/3.1: use the completed
  algebraic StandardFactorCount and the proved triangle/equality criterion.
  General containment, disjointness and whole-class cancellation below prove
  that criterion without presuming positivity of transported classes. The
  actual chamber-arrow correspondence supplies both endpoint arrows and the
  lift of a canonical standard word. These local implementation blocks have
  no separate original standalone article statements. Their parent results
  are this proposition and Lemma 4.10/Corollary 4.13, printed p.18.
  All helper-round premises are discharged by local proofs below. The final
  comparison uses the canonical lifted word to attain the lower bound, and
  handles the empty list in both word induction and lifting.
  The finite-rank hypothesis is the accepted user-directed convention; no
  finite ambient Coxeter group or spherical-source hypothesis is introduced.
  Source reading: the complete relevant portal entries, parent article context
  and completed internal source blocks were consulted; broader full-article
  and graph investigations are reused only as recorded in the prior reports.
  The Proposition 4.6 proof typo (left descent) is addressed in provedCMC
  through the correctly oriented imported inverse-minimality result; see
  https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects#pdf-prop46-left-descent-typo--confirmed.
  It requires no change to either accepted endpoint. No translation review.
  -/
  /- Completed internal BrinkHowlettGroupoid: included locally; no new prerequisite. -/
  let BrinkHowlettGroupoid : (∀ {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S), CategoryTheory.Groupoid { I : Set S // ∃ w : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj w)) (CoxeterSystem.parabolic cs I) = CoxeterSystem.parabolic cs J }) :=
  (by
    intro S W inst M cs J
    let roots : Set S → Set (Finsupp S Real) :=
      fun I => Set.image (fun i : S => Finsupp.single i (1 : Real)) I
    exact {
      Hom := fun I K => { w : W //
        Set.image (CoxeterSystem.geometricRepresentation cs w) (roots K.val) = roots I.val }
      id := fun I => ⟨1, by simp⟩
      comp := fun {I K L} x y => ⟨x.val * y.val, by
        calc
          Set.image (CoxeterSystem.geometricRepresentation cs (x.val * y.val)) (roots L.val)
              = Set.image (CoxeterSystem.geometricRepresentation cs x.val)
                  (Set.image (CoxeterSystem.geometricRepresentation cs y.val) (roots L.val)) := by
                    simp only [map_mul, mul_apply_eq_comp, Set.image_image]
          _ = roots I.val := by rw [y.property, x.property]⟩
      id_comp := fun x => Subtype.ext (one_mul x.val)
      comp_id := fun x => Subtype.ext (mul_one x.val)
      assoc := fun x y z => Subtype.ext (mul_assoc x.val y.val z.val)
      inv := fun {I K} x => ⟨x.val⁻¹, by
        calc
          Set.image (CoxeterSystem.geometricRepresentation cs x.val⁻¹) (roots I.val)
              = Set.image (CoxeterSystem.geometricRepresentation cs x.val⁻¹)
                  (Set.image (CoxeterSystem.geometricRepresentation cs x.val) (roots K.val)) :=
                    congrArg (Set.image (CoxeterSystem.geometricRepresentation cs x.val⁻¹)) x.property.symm
          _ = roots K.val := by
            simp only [Set.image_image, Representation.inv_self_apply, Set.image_id']⟩
      inv_comp := fun x => Subtype.ext (inv_mul_cancel x.val)
      comp_inv := fun x => Subtype.ext (mul_inv_cancel x.val)
    })
  /- Completed internal ElementaryWallMorphism: included locally; no new prerequisite. -/
  have ElementaryWallMorphism : (∀ {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J I : Set S) (hI : ∃ w : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj w)) (CoxeterSystem.parabolic cs I) = CoxeterSystem.parabolic cs J) (a : S) (ha : a ∉ I), let D : Set S := {b | b ∈ Set.insert a I ∧ Relation.ReflTransGen (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b}; ∀ hD : Finite (CoxeterSystem.parabolic cs D), let crossing := SimpleWallCrossings S W M cs I a ha hD; ∃ hK : ∃ w : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj w)) (CoxeterSystem.parabolic cs crossing.2.1) = CoxeterSystem.parabolic cs J, ∃ f : (BrinkHowlettGroupoid cs J).Hom ⟨I, hI⟩ ⟨crossing.2.1, hK⟩, f.val = crossing.1) :=
  (by
    /- Lemma 4.2, printed p. 15, https://arxiv.org/pdf/2509.21915#page=15.
    Alphabeta inspiration: steps 1.1, 2.1, 3.1, 4.1 of
    https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-wall-is-morphism-artin-tits-normalisers.
    No rank restriction is introduced. The following local opposition argument is a new
    implementation helper, not a separately stated article theorem; its parents are
    Notation 2.5 / (2.6), printed p. 5, and Lemma 4.2. In place of step 1.1's restriction
    route, we use reduced parabolic words and their finitely supported root vectors.
    Thus the existing finite-index restriction APIs are never applied at infinite rank.
    Literature gap: the article proof says 'Since I, K are both finite and since |I|=|K|'.
    This is unavailable here: I and K can be infinite although W_D is finite. Steps
    2.1--3.1 below supply explicit inverse index witnesses, so no cardinality inference
    is used. This is a proof repair, not a change of endpoint.
    The supplied defect report, finding pdf-wall-root-characterisation,
    https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects#pdf-wall-root-characterisation,
    rejects the auxiliary root inclusion after (3.15), printed p. 10 (its rank-one
    counterexample has I empty). We never use it; the longest-element definition remains.
    The prior source/graph investigations are reused as reports, not represented as fresh
    full-article or full-dependency reading. Current reading covers the parent Lemma 4.2,
    its surrounding definitions, the complete numbered portal proof, and the cited defect.
    Local source search found the actual arbitrary-rank root/word APIs used below;
    a fresh bounded GitHub search for geometricRepresentation_single_neg_iff language:Lean
    returned zero results, and the pinned mathlib Coxeter search found no opposition endpoint.
    Neither is an exhaustive absence claim. -/
    intro S W inst M cs J I hI a ha D hD
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
    change ∃ hK : ∃ g : W, (cs.parabolic K).map (MulAut.conj g).toMonoidHom = cs.parabolic J,
      ∃ f : (BrinkHowlettGroupoid cs J).Hom ⟨I, hI⟩ ⟨K, hK⟩, f.val = v
    /- Step 1.1: certify the actual selected maxima. Existence of the opposition
    predicate is proved before epsilon_spec_aux is invoked. -/
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
    /- Step 3.1: append a diagram edge to the component path to prove exponent two;
    then extend root fixing and generator commutation along a word in D. -/
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
    /- Step 2.1: the two opposition maps give the same index for roots and generators. -/
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
    /- Steps 2.1--3.1: explicit surjectivity, valid for infinite I and K.
    For i in E choose k = nu(mu(i)); on I minus D use k = i. -/
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
    /- Step 4.1: map the generated subgroups, then use g*v as associate witness.
    Composition and root action follow the article's left-to-right convention. -/
    have hconj : (cs.parabolic K).map (MulAut.conj v).toMonoidHom = cs.parabolic I := by
      rw [CoxeterSystem.parabolic, MonoidHom.map_closure]
      exact congrArg Subgroup.closure hgens
    obtain ⟨g, hg⟩ := hI
    have hK : ∃ g : W, (cs.parabolic K).map (MulAut.conj g).toMonoidHom = cs.parabolic J := by
      refine ⟨g * v, ?_⟩
      have hc : (MulAut.conj (g * v)).toMonoidHom =
          (MulAut.conj g).toMonoidHom.comp (MulAut.conj v).toMonoidHom := by
        ext w
        simp [MulAut.conj_apply, mul_assoc]
      rw [hc, ← Subgroup.map_map, hconj, hg]
    exact ⟨hK, ⟨v, hroots⟩, rfl⟩
  )
  /- Completed internal StandardExpressions: included locally; no new prerequisite. -/
  let StandardExpressions : (∀ {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) (I K : { L : Set S // ∃ g : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (CoxeterSystem.parabolic cs L) = CoxeterSystem.parabolic cs J }) (w : (BrinkHowlettGroupoid cs J).Hom I K), Type _) :=
  (fun {S W} _inst {M} cs J I K w =>
    let Obj := { L : Set S // ∃ g : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (CoxeterSystem.parabolic cs L) = CoxeterSystem.parabolic cs J }
    let component : Set S → S → Set S := fun L a =>
      { b | b ∈ Set.insert a L ∧ Relation.ReflTransGen
        (fun i j : S => i ∈ Set.insert a L ∧ j ∈ Set.insert a L ∧ i ≠ j ∧ M i j ≠ 2) a b }
    let Atom := { p : Obj × S // p.2 ∉ p.1.val ∧ Finite (CoxeterSystem.parabolic cs (component p.1.val p.2)) }
    let crossing := fun e : Atom => SimpleWallCrossings S W M cs e.val.1.val e.val.2 e.property.1 e.property.2
    { es : List Atom //
      List.foldr
        (fun e tail L => L = e.val.1.val ∧ tail (crossing e).2.1)
        (fun L => L = K.val) es I.val ∧
      List.prod (List.map (fun e => (crossing e).1) es) = w.val ∧
      CoxeterSystem.length cs w.val =
        List.sum (List.map (fun e => CoxeterSystem.length cs (crossing e).1) es) })
  /- Completed internal StandardFactorCount: included locally; no new prerequisite. -/
  have StandardFactorCount : (∀ {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) (I K : { L : Set S // ∃ g : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (CoxeterSystem.parabolic cs L) = CoxeterSystem.parabolic cs J }) (w : (BrinkHowlettGroupoid cs J).Hom I K), let roots : Set (Finsupp S Real) := CoxeterSystem.geometricRoots cs; let act := CoxeterSystem.geometricRepresentation cs; let parallelClass : Finsupp S Real → Set (Finsupp S Real) := fun α => { β | β ∈ roots ∧ ∀ L, ∀ f : (BrinkHowlettGroupoid cs J).Hom L I, (0 < act f.val α ↔ 0 < act f.val β) }; let realRoot : Finsupp S Real → Prop := fun α => α ∈ roots ∧ ∃ L, ∃ f : (BrinkHowlettGroupoid cs J).Hom L I, ¬ (0 < α ↔ 0 < act f.val α); let inversions : Set (Finsupp S Real) := { α | α ∈ roots ∧ 0 < α } ∩ Set.image (act w.val) { α | α ∈ roots ∧ α < 0 }; let classes : Set (Set (Finsupp S Real)) := { c | (∃ α, realRoot α ∧ c = parallelClass α) ∧ c ⊆ inversions }; Nonempty (StandardExpressions cs J I K w) ∧ Set.Finite classes ∧ ∀ e : StandardExpressions cs J I K w, List.length e.val = Nat.card { c : Set (Finsupp S Real) // c ∈ classes }) :=
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
            simp only [root, M.geometricForm_single_single, one_mul]
            rw [he i (hv i (by simp))]
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
                (by rw [M.symmetric k j]; exact he.2.2.2))).mp hs
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
              simp only [M.geometricForm_single_single, one_mul]
              rw [hsep i (hv i (by simp)) e he]
              norm_num [Real.cos_pi_div_two]
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
            · simp only [β, sroot, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
                Finsupp.single_apply, he, Ne.symm he, if_false, mul_zero, sub_zero]
              exact hs i (by intro hh; rcases hh with hh | hh; exact he hh; exact hi hh)
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
  let UniversalWallGroupoid : ∀ {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S), CategoryTheory.Groupoid { p : W × Set S // Set.image (fun u : W => u * p.1) (CoxeterSystem.parabolic cs J : Set W) = Set.image (fun u : W => p.1 * u) (CoxeterSystem.parabolic cs p.2 : Set W) ∧ CoxeterSystem.IsMinimalCosetRep cs p.2 p.1 } :=
  fun {S W} _inst {M} cs J => {
    Hom := fun A B => { w : W // w = A.val.1⁻¹ * B.val.1 }
    id := fun A => ⟨1, (inv_mul_cancel A.val.1).symm⟩
    comp := fun {A B C} f g => ⟨f.val * g.val, by
      rw [f.property, g.property]
      simp only [mul_assoc, mul_inv_cancel_left]⟩
    id_comp := fun f => Subtype.ext (one_mul f.val)
    comp_id := fun f => Subtype.ext (mul_one f.val)
    assoc := fun f g h => Subtype.ext (mul_assoc f.val g.val h.val)
    inv := fun {A B} f => ⟨f.val⁻¹, by
      rw [f.property, mul_inv_rev, inv_inv]⟩
    inv_comp := fun f => Subtype.ext (inv_mul_cancel f.val)
    comp_inv := fun f => Subtype.ext (mul_inv_cancel f.val)
  }
  let accepted_ChamberMorphismCorrespondence_type : Prop :=
  ∀ {S W : Type _} [Finite S] [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S),
    let Obj := { I : Set S // ∃ g : W,
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g))
        (CoxeterSystem.parabolic cs I) = CoxeterSystem.parabolic cs J }
    let label : W → Set S → Prop := fun x I =>
      Set.image (fun u : W => u * x) (CoxeterSystem.parabolic cs J : Set W) =
        Set.image (fun u : W => x * u) (CoxeterSystem.parabolic cs I : Set W) ∧
      CoxeterSystem.IsMinimalCosetRep cs I x
    (∀ (I K : Obj) (x y : W), label x I.val → label y K.val →
      ∃ f : (BrinkHowlettGroupoid cs J).Hom I K, f.val = x⁻¹ * y) ∧
    (∀ (I K : Obj) (w : (BrinkHowlettGroupoid cs J).Hom I K)
      (x : W) (hx : label x I.val),
      ∃ htarget : label (x * w.val) K.val,
        ∃! f : (UniversalWallGroupoid cs J).Hom
          ⟨(x, I.val), hx⟩ ⟨(x * w.val, K.val), htarget⟩,
          f.val = w.val)
  let Obj {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) :=
    { I : Set S // ∃ g : W, (cs.parabolic I).map (MulAut.conj g).toMonoidHom = cs.parabolic J }
  let Label {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) :=
    { p : W × Set S // Set.image (fun u : W => u * p.1) (cs.parabolic J : Set W) =
      Set.image (fun u : W => p.1 * u) (cs.parabolic p.2 : Set W) ∧
      cs.IsMinimalCosetRep p.2 p.1 }
  let component {S : Type _} (M : CoxeterMatrix S) (I : Set S) (a : S) :=
    { b | b ∈ Set.insert a I ∧ Relation.ReflTransGen
      (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b }
  let Atom {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) :=
    { e : Obj cs J × S // e.2 ∉ e.1.val ∧ Finite (cs.parabolic (component M e.1.val e.2)) }
  let Step {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) :=
    { e : Label cs J × S // e.2 ∉ e.1.val.2 ∧ Finite (cs.parabolic (component M e.1.val.2 e.2)) }
  let cross {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) (e : Atom cs J) :=
    SimpleWallCrossings S W M cs e.val.1.val e.val.2 e.property.1 e.property.2
  let scross {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) (e : Step cs J) :=
    SimpleWallCrossings S W M cs e.val.1.val.2 e.val.2 e.property.1 e.property.2
  let composable {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) (es : List (Atom cs J)) (I K : Set S) :=
    List.foldr (fun e tail L => L = e.val.1.val ∧ tail (cross cs J e).2.1)
      (fun L => L = K) es I
  let product {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) (es : List (Atom cs J)) :=
    (es.map (fun e => (cross cs J e).1)).prod
  let weight {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) (es : List (Atom cs J)) :=
    (es.map (fun e => cs.length (cross cs J e).1)).sum
  let path {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S)
      (p q : Label cs J) (es : List (Step cs J)) :=
    List.foldr (fun e tail r => r = e.val.1.val ∧ tail ((scross cs J e).2.2 e.val.1.val.1))
      (fun r => r = q.val) es p.val
  let canonical {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S)
      (I K : Obj cs J) (w : (BrinkHowlettGroupoid cs J).Hom I K) :=
    Classical.choice (StandardFactorCount cs J I K w).1
  let d {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S)
      (I K : Obj cs J) (w : (BrinkHowlettGroupoid cs J).Hom I K) : Nat :=
    (canonical cs J I K w).val.length
  have standard_count {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S)
      (I K : Obj cs J) (w : (BrinkHowlettGroupoid cs J).Hom I K)
      (e : StandardExpressions cs J I K w) : e.val.length = d cs J I K w := by
    exact ((StandardFactorCount cs J I K w).2.2 e).trans
      ((StandardFactorCount cs J I K w).2.2 (canonical cs J I K w)).symm
  let toObj {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) (p : Label cs J) : Obj cs J :=
    ⟨p.val.2, ⟨p.val.1, by
      ext u
      constructor
      · rintro ⟨v, hv, rfl⟩
        have hm : p.val.1 * v ∈ Set.image (fun u : W => p.val.1 * u)
            (cs.parabolic p.val.2 : Set W) := ⟨v, hv, rfl⟩
        rw [← p.property.1] at hm
        obtain ⟨z, hz, he⟩ := hm
        have he' : p.val.1 * v * p.val.1⁻¹ = z := by
          rw [← he, mul_inv_cancel_right]
        change p.val.1 * v * p.val.1⁻¹ ∈ cs.parabolic J
        rw [he']
        exact hz
      · intro hu
        have hm : u * p.val.1 ∈ Set.image (fun u : W => u * p.val.1)
            (cs.parabolic J : Set W) := ⟨u, hu, rfl⟩
        rw [p.property.1] at hm
        obtain ⟨v, hv, he⟩ := hm
        refine ⟨v, hv, ?_⟩
        change p.val.1 * v * p.val.1⁻¹ = u
        change p.val.1 * v = u * p.val.1 at he
        rw [he, mul_inv_cancel_right]⟩⟩
  let toAtom {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) (e : Step cs J) : Atom cs J :=
    ⟨(toObj cs J e.val.1, e.val.2), e.property⟩
  have cross_toAtom {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) (e : Step cs J) :
      cross cs J (toAtom cs J e) = scross cs J e := rfl
  let Triangle {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) : Prop :=
    ∀ (I K L : Obj cs J) (x : (BrinkHowlettGroupoid cs J).Hom I K)
      (y : (BrinkHowlettGroupoid cs J).Hom K L),
      d cs J I L ((BrinkHowlettGroupoid cs J).comp x y) ≤ d cs J I K x + d cs J K L y ∧
      (d cs J I L ((BrinkHowlettGroupoid cs J).comp x y) = d cs J I K x + d cs J K L y ↔
        cs.length (x.val * y.val) = cs.length x.val + cs.length y.val)
  let candidate_triangle_type : Prop :=
    ∀ {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S),
      Triangle cs J
  have provedTriangle : candidate_triangle_type := by
    intro S W inst M cs J
    have candidate_triangle :
        let Obj := {L : Set S // ∃ g : W,
          Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (cs.parabolic L) =
            cs.parabolic J}
        let d := fun (A B : Obj) (w : (BrinkHowlettGroupoid cs J).Hom A B) =>
          (Classical.choice (StandardFactorCount cs J A B w).1).val.length
        ∀ (A B C : Obj) (x : (BrinkHowlettGroupoid cs J).Hom A B)
          (y : (BrinkHowlettGroupoid cs J).Hom B C),
          d A C ((BrinkHowlettGroupoid cs J).comp x y) ≤ d A B x + d B C y ∧
          (d A C ((BrinkHowlettGroupoid cs J).comp x y) = d A B x + d B C y ↔
            cs.length (x.val * y.val) = cs.length x.val + cs.length y.val) := by
      have factorCountTriangle
          (A B C : {L : Set S // ∃ g : W,
            Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (cs.parabolic L) =
              cs.parabolic J})
          (x : (BrinkHowlettGroupoid cs J).Hom A B)
          (y : (BrinkHowlettGroupoid cs J).Hom B C)
          (ex : StandardExpressions cs J A B x)
          (ey : StandardExpressions cs J B C y)
          (ez : StandardExpressions cs J A C ((BrinkHowlettGroupoid cs J).comp x y)) :
          ez.val.length ≤ ex.val.length + ey.val.length ∧
            (ez.val.length = ex.val.length + ey.val.length ↔
              cs.length (x.val * y.val) = cs.length x.val + cs.length y.val) := by
          classical
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
          have containment (A B D : Obj) (x : (BrinkHowlettGroupoid cs J).Hom A B)
              (y : (BrinkHowlettGroupoid cs J).Hom B D) :
              classes A (x.val * y.val) ⊆ classes A x.val ∪
                (Set.image (act x.val)) '' classes B y.val := by
            have hz := classes_image A D ((BrinkHowlettGroupoid cs J).comp x y)
            change classes A (x.val * y.val) = _ at hz
            rw [hz]
            rintro c ⟨α, hα, rfl⟩
            change α ∈ N (x.val * y.val) at hα
            have hr := (cs.geometricRepresentation_apply_mem_geometricRoots_iff x.val⁻¹).2 hα.1
            rcases cs.pos_or_neg_of_mem_geometricRoots hr with hp | hn
            · right
              have hβ : act x.val⁻¹ α ∈ N y.val := by
                refine ⟨hr, hp, ?_⟩
                simpa only [act, mul_inv_rev, map_mul, mul_apply_eq_comp] using hα.2.2
              refine ⟨parallelClass B (act x.val⁻¹ α), ?_, ?_⟩
              · rw [classes_image B D y]
                exact ⟨_, hβ, rfl⟩
              · rw [pc_transport A B x, Representation.self_inv_apply]
            · left
              rw [classes_image A B x]
              exact ⟨α, ⟨hα.1, hα.2.1, hn⟩, rfl⟩
          have disjoint_families (A B D : Obj) (x : (BrinkHowlettGroupoid cs J).Hom A B)
              (y : (BrinkHowlettGroupoid cs J).Hom B D) :
              Disjoint (classes A x.val) ((Set.image (act x.val)) '' classes B y.val) := by
            apply Set.disjoint_left.mpr
            rintro c hc ⟨d, hd, hdc⟩
            rw [classes_image B D y] at hd
            obtain ⟨β, hβ, rfl⟩ := hd
            have hm : act x.val β ∈ c := hdc ▸ Set.mem_image_of_mem _ (pc_self B hβ.1)
            have hn : act x.val β ∈ N x.val := (image_N x.val).symm ▸ hc.2 hm
            have hn' : act x.val⁻¹ (act x.val β) < 0 := hn.2.2
            rw [Representation.inv_self_apply] at hn'
            exact lt_asymm hβ.2.1 hn'
          -- A missing inversion deletes an entire nonempty class, not just a root.
          have missing_class (A B D : Obj) (x : (BrinkHowlettGroupoid cs J).Hom A B)
              (y : (BrinkHowlettGroupoid cs J).Hom B D)
              {α : Finsupp S Real} (hα : α ∈ N x.val) (hn : α ∉ N (x.val * y.val)) :
              (parallelClass A α).Nonempty ∧
              parallelClass A α ∈ classes A x.val ∧
              Disjoint (parallelClass A α) (N (x.val * y.val)) ∧
              parallelClass A α ∉ classes A (x.val * y.val) ∧
              parallelClass A α ∉ (Set.image (act x.val)) '' classes B y.val := by
            have hself := pc_self A hα.1
            have hc : parallelClass A α ∈ classes A x.val := by
              rw [classes_image A B x]
              exact ⟨α, hα, rfl⟩
            refine ⟨⟨α, hself⟩, hc, ?_, ?_, ?_⟩
            · apply Set.disjoint_left.mpr
              intro β hβ hβz
              apply hn
              have hsym : α ∈ parallelClass A β :=
                ⟨hα.1, fun L f => (hβ.2 L f).symm⟩
              exact saturated A D ((BrinkHowlettGroupoid cs J).comp x y) hβz hsym
            · intro hcz
              exact hn ((image_N (x.val * y.val)).symm ▸ hcz.2 hself)
            · intro htr
              exact Set.disjoint_left.mp (disjoint_families A B D x y) hc htr
          have triangle_count (A B D : Obj) (x : (BrinkHowlettGroupoid cs J).Hom A B)
              (y : (BrinkHowlettGroupoid cs J).Hom B D) :
              count A (x.val * y.val) ≤ count A x.val + count B y.val ∧
              (count A (x.val * y.val) = count A x.val + count B y.val ↔
                cs.length (x.val * y.val) = cs.length x.val + cs.length y.val) := by
            let tr := Set.image (act x.val)
            have hi : Function.Injective tr :=
              (Representation.apply_bijective act x.val).1.image_injective
            have hf : Set.Finite (classes A x.val ∪ tr '' classes B y.val) :=
              (hfinite A B x).union ((hfinite B D y).image tr)
            have hcard : (classes A x.val ∪ tr '' classes B y.val).ncard =
                count A x.val + count B y.val := by
              change _ = (classes A x.val).ncard + (classes B y.val).ncard
              rw [Set.ncard_union_eq (disjoint_families A B D x y)
                (hfinite A B x) ((hfinite B D y).image tr),
                Set.ncard_image_of_injective _ hi]
            have hle : count A (x.val * y.val) ≤ count A x.val + count B y.val := by
              rw [← hcard]
              exact Set.ncard_le_ncard (containment A B D x y) hf
            refine ⟨hle, ?_⟩
            constructor
            · intro heq
              have hfamily : classes A (x.val * y.val) =
                  classes A x.val ∪ tr '' classes B y.val := by
                exact Set.eq_of_subset_of_ncard_le (containment A B D x y)
                  (by rw [hcard]; exact heq.ge) hf
              have hprefix := (ArtinNormalisers.Chamber3.length_eq_add_iff_rootInversions_subset_system
                cs x.val (x.val * y.val)).mpr ?_
              · simpa only [inv_mul_cancel_left] using hprefix
              · intro α hr hp hn
                have hin : α ∈ N x.val := ⟨hr, hp, hn⟩
                have hc : parallelClass A α ∈ classes A x.val := by
                  rw [classes_image A B x]
                  exact ⟨α, hin, rfl⟩
                have hcz : parallelClass A α ∈ classes A (x.val * y.val) := by
                  rw [hfamily]
                  exact Or.inl hc
                have hinz : α ∈ N (x.val * y.val) := by
                  by_contra hnot
                  exact (missing_class A B D x y hin hnot).2.2.2.1 hcz
                exact hinz.2.2
            · exact hadd A B D x y
          have hx := (StandardFactorCount cs J A B x).2.2 ex
          have hy := (StandardFactorCount cs J B C y).2.2 ey
          have hz := (StandardFactorCount cs J A C ((BrinkHowlettGroupoid cs J).comp x y)).2.2 ez
          change ex.val.length = count A x.val at hx
          change ey.val.length = count B y.val at hy
          change ez.val.length = count A (x.val * y.val) at hz
          rw [hx, hy, hz]
          exact triangle_count A B C x y
      intro Obj d A B C x y
      exact factorCountTriangle A B C x y
        (Classical.choice (StandardFactorCount cs J A B x).1)
        (Classical.choice (StandardFactorCount cs J B C y).1)
        (Classical.choice (StandardFactorCount cs J A C
          ((BrinkHowlettGroupoid cs J).comp x y)).1)
    exact candidate_triangle
  have provedCMC : accepted_ChamberMorphismCorrespondence_type :=
  by
    classical
    intro S W _ _ M cs J
    
    let Obj := {L : Set S // ∃ g : W,
      (cs.parabolic L).map (MulAut.conj g).toMonoidHom = cs.parabolic J}
    let label : W → Set S → Prop := fun x I =>
      (fun u : W => u * x) '' (cs.parabolic J : Set W) =
        (fun u : W => x * u) '' (cs.parabolic I : Set W) ∧
      cs.IsMinimalCosetRep I x
    let root : S → (S →₀ ℝ) := fun i => Finsupp.single i 1
    let piRoots : Set S → Set (S →₀ ℝ) := fun L => root '' L
    have coset_conj (x : W) (I : Set S)
        (h : (fun u : W => u * x) '' (cs.parabolic J : Set W) =
          (fun u : W => x * u) '' (cs.parabolic I : Set W)) :
        (cs.parabolic I).map (MulAut.conj x).toMonoidHom = cs.parabolic J := by
      ext v
      constructor
      · rintro ⟨u, hu, huv⟩
        change x * u * x⁻¹ = v at huv
        have hm : x * u ∈ (fun t : W => t * x) '' (cs.parabolic J : Set W) :=
          h.symm ▸ Set.mem_image_of_mem (fun t : W => x * t) hu
        obtain ⟨t, ht, he⟩ := hm
        have hev : t = v := by rw [← huv, ← he]; group
        exact hev ▸ ht
      · intro hv
        have hm : v * x ∈ (fun t : W => x * t) '' (cs.parabolic I : Set W) :=
          h ▸ Set.mem_image_of_mem (fun t : W => t * x) hv
        obtain ⟨t, ht, he⟩ := hm
        refine ⟨t, ht, ?_⟩
        change x * t = v * x at he
        change x * t * x⁻¹ = v
        rw [he]
        group
    have transporter_root (x : W) (I F : Set S)
        (hc : (cs.parabolic I).map (MulAut.conj x).toMonoidHom = cs.parabolic F)
        (hm : cs.IsMinimalCosetRep I x) {i : S} (hi : i ∈ I) :
        ∃ j ∈ F, cs.geometricRepresentation x (root i) = root j := by
      obtain ⟨j, hj, he⟩ := ArtinNormalisers.Chamber3.transporter_conjugates_simple cs hc hm hi
      let v := cs.geometricRepresentation x (root i)
      have hneg : M.geometricReflection j v = -v := by
        have hprod : cs.simple j * x = x * cs.simple i := by rw [← he]; group
        calc
          _ = cs.geometricRepresentation (cs.simple j * x) (root i) := by
            rw [map_mul, mul_apply_eq_comp, cs.geometricRepresentation_simple]
          _ = -v := by
            rw [hprod, cs.geometricRepresentation_mul_simple_single]
      have hr : v ∈ cs.geometricRoots := ⟨x, i, rfl⟩
      have hpos : 0 < v := (cs.geometricRepresentation_single_pos_iff x i).mpr
        (cs.isMinimalCosetRep_iff.mp hm i hi)
      have hs : ∀ k, k ≠ j → v k = 0 := by
        intro k hk
        have hh := congrArg (fun z : S →₀ ℝ => z k) hneg
        rw [M.geometricReflection_apply_apply_of_ne hk] at hh
        change v k = -v k at hh
        linarith
      rcases cs.eq_single_or_eq_neg_single_of_mem_geometricRoots hr hs with hh | hh
      · exact ⟨j, hj, hh⟩
      · have hn : v j = -1 := by rw [hh]; simp
        have hp := hpos.le j
        change 0 ≤ v j at hp
        linarith
    have label_roots (x : W) (I : Set S) (hx : label x I) :
        cs.geometricRepresentation x '' piRoots I = piRoots J := by
      have hc := coset_conj x I hx.1
      have hci := ArtinNormalisers.Chamber3.inverse_parabolic_transporter cs hc
      have hmi := ArtinNormalisers.Chamber3.minimal_inv_of_parabolic_transporter cs hc hx.2
      ext z
      constructor
      · rintro ⟨_, ⟨i, hi, rfl⟩, rfl⟩
        obtain ⟨j, hj, he⟩ := transporter_root x I J hc hx.2 hi
        exact ⟨j, hj, he.symm⟩
      · rintro ⟨j, hj, rfl⟩
        obtain ⟨i, hi, he⟩ := transporter_root x⁻¹ J I hci hmi hj
        refine ⟨root i, ⟨i, hi, rfl⟩, ?_⟩
        rw [← he, Representation.self_inv_apply]
  
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
    constructor
    · intro I K x y hx hy
      have hxroot := label_roots x I.val hx
      have hyroot := label_roots y K.val hy
      refine ⟨⟨x⁻¹ * y, ?_⟩, rfl⟩
      change cs.geometricRepresentation (x⁻¹ * y) '' piRoots K.val = piRoots I.val
      calc
        _ = cs.geometricRepresentation x⁻¹ ''
            (cs.geometricRepresentation y '' piRoots K.val) := by
          simp only [map_mul, mul_apply_eq_comp, Set.image_image]
        _ = cs.geometricRepresentation x⁻¹ ''
            (cs.geometricRepresentation x '' piRoots I.val) := by rw [hyroot, hxroot]
        _ = piRoots I.val := by
          simp only [Set.image_image, Representation.inv_self_apply, Set.image_id']
    · intro I K w x hx
      have hw : cs.geometricRepresentation w.val '' piRoots K.val = piRoots I.val := w.property
      have hc := root_conjugacy cs w.val K.val I.val hw
      have ht : label (x * w.val) K.val :=
        c_literal_label_preserved cs J I.val K.val x w.val hx.1 hx.2 hc hw
      refine ⟨ht, ⟨w.val, ?_⟩, rfl, ?_⟩
      · change w.val = x⁻¹ * (x * w.val)
        simp only [inv_mul_cancel_left]
      · intro f hf
        exact Subtype.ext hf
  have weight_bound {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) (es : List (Atom cs J)) :
      cs.length (product cs J es) ≤ weight cs J es := by
    induction es with
    | nil => simp [product, weight]
    | cons e es ih =>
      change cs.length ((cross cs J e).1 * product cs J es) ≤
        cs.length (cross cs J e).1 + weight cs J es
      exact (cs.length_mul_le _ _).trans (Nat.add_le_add_left ih _)
  
  -- Reconstructed because WordProof.txt and WordCheck.lean were unavailable.
  -- Local implementation helper only; parent Proposition 3.29, p.13--14.
  -- Portal inspiration: step 2.1 (nonnegative length deficits).
  have word_metric {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) (ht : Triangle cs J) :
      ∀ (es : List (Atom cs J)) (A B : Obj cs J)
        (f : (BrinkHowlettGroupoid cs J).Hom A B),
        composable cs J es A.val B.val → product cs J es = f.val →
        d cs J A B f ≤ es.length ∧
        (d cs J A B f = es.length ↔ cs.length f.val = weight cs J es) := by
    intro es
    induction es with
    | nil =>
      intro A B f hc hp
      let hstd : StandardExpressions cs J A B f :=
        ⟨[], hc, hp, by simpa only [product, List.map_nil, List.prod_nil, List.sum_nil] using
          (congrArg cs.length hp).symm.trans (cs.length_one)⟩
      have hd : 0 = d cs J A B f := by
        simpa only [hstd, List.length_nil] using standard_count cs J A B f hstd
      have hf : f.val = 1 := hp.symm
      simp only [List.length_nil] at hd ⊢
      exact ⟨by omega, by simp [← hd, hf, weight]⟩
    | cons e es ih =>
      intro A B f hc hp
      change A.val = e.val.1.val ∧ composable cs J es (cross cs J e).2.1 B.val at hc
      have hAe : A = e.val.1 := Subtype.ext hc.1
      subst A
      obtain ⟨htarget, x, hx⟩ := ElementaryWallMorphism cs J e.val.1.val
        e.val.1.property e.val.2 e.property.1 e.property.2
      let T : Obj cs J := ⟨(cross cs J e).2.1, htarget⟩
      change (BrinkHowlettGroupoid cs J).Hom e.val.1 T at x
      change x.val = (cross cs J e).1 at hx
      let y : (BrinkHowlettGroupoid cs J).Hom T B :=
        (BrinkHowlettGroupoid cs J).comp ((BrinkHowlettGroupoid cs J).inv x) f
      have hy : y.val = product cs J es := by
        change x.val⁻¹ * f.val = product cs J es
        change (cross cs J e).1 * product cs J es = f.val at hp
        rw [hx, ← hp, inv_mul_cancel_left]
      have hf : f.val = x.val * y.val := by
        change f.val = x.val * (x.val⁻¹ * f.val)
        simp
      have hcomp : (BrinkHowlettGroupoid cs J).comp x y = f := Subtype.ext hf.symm
      let hstd : StandardExpressions cs J e.val.1 T x :=
        ⟨[e], ⟨rfl, rfl⟩, by simpa only [product, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] using hx.symm,
          by change cs.length x.val = cs.length (cross cs J e).1 + 0; rw [hx, add_zero]⟩
      have hxcount : d cs J e.val.1 T x = 1 := by
        simpa only [hstd, List.length_cons, List.length_nil] using
          (standard_count cs J _ _ x hstd).symm
      have htri := ht e.val.1 T B x y
      rw [hcomp, hxcount] at htri
      have hrec := ih T B y hc.2 hy.symm
      have hb := weight_bound cs J es
      have hm := cs.length_mul_le x.val y.val
      rw [← hy] at hb
      rw [← hf] at hm
      change d cs J e.val.1 B f ≤ es.length + 1 ∧
        (d cs J e.val.1 B f = es.length + 1 ↔
          cs.length f.val = cs.length (cross cs J e).1 + weight cs J es)
      refine ⟨by omega, ?_⟩
      constructor
      · intro heq
        have htEq : d cs J e.val.1 B f = 1 + d cs J T B y := by omega
        have hyEq : d cs J T B y = es.length := by omega
        have hlen := htri.2.mp htEq
        rw [← hf, hx, hrec.2.mp hyEq] at hlen
        exact hlen
      · intro hlen
        have htail : cs.length y.val = weight cs J es := by rw [hx] at hm; omega
        have hxy : cs.length (x.val * y.val) = cs.length x.val + cs.length y.val := by
          rw [← hf, hx, htail]; exact hlen
        have htEq := htri.2.mpr hxy
        have hyEq := hrec.2.mpr htail
        omega
  have path_word {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S)
      (p q : Label cs J) (es : List (Step cs J)) (hp : path cs J p q es) :
      composable cs J (es.map (toAtom cs J)) p.val.2 q.val.2 ∧
      product cs J (es.map (toAtom cs J)) = p.val.1⁻¹ * q.val.1 := by
    have aux : ∀ (es : List (Step cs J)) (r : W × Set S),
        List.foldr (fun e tail r => r = e.val.1.val ∧
          tail ((scross cs J e).2.2 e.val.1.val.1)) (fun r => r = q.val) es r →
        composable cs J (es.map (toAtom cs J)) r.2 q.val.2 ∧
        r.1 * product cs J (es.map (toAtom cs J)) = q.val.1 := by
      intro es
      induction es with
      | nil =>
        intro r hr
        change r = q.val at hr
        subst r
        exact ⟨rfl, mul_one _⟩
      | cons e es ih =>
        intro r hr
        change r = e.val.1.val ∧ _ at hr
        obtain ⟨hc, hprod⟩ := ih ((scross cs J e).2.2 e.val.1.val.1) hr.2
        rw [hr.1]
        constructor
        · exact ⟨rfl, hc⟩
        · change e.val.1.val.1 * ((scross cs J e).1 *
            product cs J (es.map (toAtom cs J))) = q.val.1
          change (e.val.1.val.1 * (scross cs J e).1) *
            product cs J (es.map (toAtom cs J)) = q.val.1 at hprod
          rw [← mul_assoc]
          exact hprod
    obtain ⟨hc, he⟩ := aux es p.val hp
    refine ⟨hc, ?_⟩
    rw [← he, inv_mul_cancel_left]
  
  -- Lifts a composable atom list with prescribed endpoints. Empty lists are included.
  -- Local implementation helper for Proposition 3.29, pp.13--14; arrow preservation
  -- is the explicitly quantified Proposition 4.6 premise, not an assumed theorem.
  have lift_word {S W : Type _} [Group W] {M : CoxeterMatrix S} [Finite S] (cs : CoxeterSystem M W) (J : Set S)
      (cmc : accepted_ChamberMorphismCorrespondence_type) :
      ∀ (es : List (Atom cs J)) (A B : Obj cs J) (p q : Label cs J),
        p.val.2 = A.val → q.val.2 = B.val →
        p.val.1 * product cs J es = q.val.1 → composable cs J es A.val B.val →
        ∃ fs : List (Step cs J), path cs J p q fs ∧ fs.length = es.length := by
    intro es
    induction es with
    | nil =>
      intro A B p q hp hq he hc
      have hpq : p.val = q.val := by
        apply Prod.ext
        · simpa only [product, List.map_nil, List.prod_nil, mul_one] using he
        · exact hp.trans (hc.trans hq.symm)
      exact ⟨[], hpq, rfl⟩
    | cons e es ih =>
      intro A B p q hp hq he hc
      change A.val = e.val.1.val ∧ composable cs J es (cross cs J e).2.1 B.val at hc
      have hpe : p.val.2 = e.val.1.val := hp.trans hc.1
      obtain ⟨hT, x, hx⟩ := ElementaryWallMorphism cs J e.val.1.val e.val.1.property
        e.val.2 e.property.1 e.property.2
      let T : Obj cs J := ⟨(cross cs J e).2.1, hT⟩
      change (BrinkHowlettGroupoid cs J).Hom e.val.1 T at x
      have hlabel := p.property
      rw [hpe] at hlabel
      obtain ⟨hr, _⟩ := (cmc (S := S) (W := W) (M := M) cs J).2 e.val.1 T x p.val.1 hlabel
      rw [hx] at hr
      let r : Label cs J := ⟨(p.val.1 * (cross cs J e).1, T.val), hr⟩
      have htail : r.val.1 * product cs J es = q.val.1 := by
        change (p.val.1 * (cross cs J e).1) * product cs J es = q.val.1
        rw [mul_assoc]
        exact he
      obtain ⟨fs, hfs, hlen⟩ := ih T B r q rfl hq htail hc.2
      let s : Step cs J := ⟨(p, e.val.2), by simpa only [hpe] using e.property⟩
      have hcross : (scross cs J s).2.2 p.val.1 = r.val := by
        have hsource : toObj cs J p = e.val.1 := Subtype.ext hpe
        have ha : toAtom cs J s = e := by apply Subtype.ext; exact Prod.ext hsource rfl
        change (cross cs J (toAtom cs J s)).2.2 p.val.1 = r.val
        rw [ha]
        rfl
      refine ⟨s :: fs, ?_, by simpa only [List.length_cons, hlen]⟩
      change p.val = p.val ∧ _
      refine ⟨rfl, ?_⟩
      rw [hcross]
      exact hfs
  have conditionalIntegration
      (triangle : candidate_triangle_type)
      (cmc : accepted_ChamberMorphismCorrespondence_type) :
  ∀ {S : Type _} [Finite S] (M : CoxeterMatrix S) (J : Set S),
    let W := CoxeterMatrix.Group M
    let cs := CoxeterMatrix.toCoxeterSystem M
    let Label := { p : W × Set S //
      Set.image (fun u : W => u * p.1) (CoxeterSystem.parabolic cs J : Set W) =
        Set.image (fun u : W => p.1 * u) (CoxeterSystem.parabolic cs p.2 : Set W) ∧
      CoxeterSystem.IsMinimalCosetRep cs p.2 p.1 }
    let component : Set S → S → Set S := fun I a =>
      { b | b ∈ Set.insert a I ∧ Relation.ReflTransGen
        (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b }
    let Step := { e : Label × S // e.2 ∉ e.1.val.2 ∧
      Finite (CoxeterSystem.parabolic cs (component e.1.val.2 e.2)) }
    let crossing := fun e : Step =>
      SimpleWallCrossings S W M cs e.val.1.val.2 e.val.2 e.property.1 e.property.2
    let path : Label → Label → List Step → Prop := fun p q es =>
      List.foldr
        (fun e tail r => r = e.val.1.val ∧ tail ((crossing e).2.2 e.val.1.val.1))
        (fun r => r = q.val) es p.val
    ∀ (p q : Label) (es : List Step), path p q es →
      ((∀ fs : List Step, path p q fs → List.length es ≤ List.length fs) ↔
        CoxeterSystem.length cs (List.prod (List.map (fun e => (crossing e).1) es)) =
          List.sum (List.map (fun e => CoxeterSystem.length cs (crossing e).1) es)) := by
    intro S inst M J
    let cs := CoxeterMatrix.toCoxeterSystem M
    change ∀ (p q : Label cs J) (es : List (Step cs J)),
      path cs J p q es →
      ((∀ fs : List (Step cs J), path cs J p q fs → es.length ≤ fs.length) ↔
        cs.length ((es.map (fun e => (scross cs J e).1)).prod) =
          (es.map (fun e => cs.length (scross cs J e).1)).sum)
    intro p q es hp
    obtain ⟨w, hw⟩ := (cmc (S := S) (W := CoxeterMatrix.Group M) (M := M) cs J).1
      (toObj cs J p) (toObj cs J q) p.val.1 q.val.1 p.property q.property
    have metric_for : ∀ (fs : List (Step cs J)), path cs J p q fs →
        d cs J (toObj cs J p) (toObj cs J q) w ≤ fs.length ∧
        (d cs J (toObj cs J p) (toObj cs J q) w = fs.length ↔
          cs.length ((fs.map (fun e => (scross cs J e).1)).prod) =
            (fs.map (fun e => cs.length (scross cs J e).1)).sum) := by
      intro fs hfs
      obtain ⟨hc, hprod⟩ := path_word cs J p q fs hfs
      have hprod' : product cs J (fs.map (toAtom cs J)) = w.val := hprod.trans hw.symm
      have hm := word_metric cs J (triangle cs J) (fs.map (toAtom cs J))
        (toObj cs J p) (toObj cs J q) w hc hprod'
      have hprod'' : ((fs.map (fun e => (scross cs J e).1)).prod) = w.val := by
        simpa only [product, List.map_map, Function.comp_def, cross_toAtom] using hprod'
      simpa only [List.length_map, weight, List.map_map, Function.comp_def, cross_toAtom, hprod''] using hm
    have hm := metric_for es hp
    constructor
    · intro hgeo
      let ce := canonical cs J (toObj cs J p) (toObj cs J q) w
      have he : p.val.1 * product cs J ce.val = q.val.1 := by
        have hce : product cs J ce.val = w.val := ce.property.2.1
        rw [hce, hw, mul_inv_cancel_left]
      obtain ⟨fs, hfs, hlen⟩ := lift_word cs J cmc ce.val
        (toObj cs J p) (toObj cs J q) p q rfl rfl he ce.property.1
      have hf : fs.length = d cs J (toObj cs J p) (toObj cs J q) w := hlen
      have hg := hgeo fs hfs
      have hd : d cs J (toObj cs J p) (toObj cs J q) w = es.length := by omega
      exact hm.2.mp hd
    · intro hadd fs hfs
      have heq := hm.2.mpr hadd
      have hf := (metric_for fs hfs).1
      omega
  intro S hS M J
  exact conditionalIntegration provedTriangle provedCMC M J
)
