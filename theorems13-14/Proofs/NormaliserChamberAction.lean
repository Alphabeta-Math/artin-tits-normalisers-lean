import Mathlib
import ArtinDeligne
import Proofs.RelativeCone
import Proofs.ChamberLabelling
import Proofs.AdjacentWallFormula

set_option maxHeartbeats 2000000

theorem NormaliserChamberAction : (∀ {S : Type*} [Finite S] (M : CoxeterMatrix S) (J : Set S),
  let W := CoxeterMatrix.Group M
  let cs := CoxeterMatrix.toCoxeterSystem M
  let Label := { p : W × Set S //
    Set.image (fun u : W => u * p.1) (CoxeterSystem.parabolic cs J : Set W) =
      Set.image (fun u : W => p.1 * u) (CoxeterSystem.parabolic cs p.2 : Set W) ∧
    CoxeterSystem.IsMinimalCosetRep cs p.2 p.1 }
  let Θ := ArtinNormalisers.Theorem18.relativeSubspace J
  letI : TopologicalSpace Θ := TopologicalSpace.induced
    (fun f : Θ => ArtinNormalisers.Theorem18.dualCoordinates f.val)
    (inferInstance : TopologicalSpace (S → Real))
  let arrangement : Set (Submodule Real Θ) := (RelativeCone M J).2.2.2.2.2
  let face : Set S → Set (ArtinNormalisers.Theorem18.Dual S) := fun I =>
    { f | f ∈ ArtinNormalisers.Theorem18.relativeSubspace I ∧
      ∀ i : S, i ∉ I → 0 < ArtinNormalisers.Theorem18.dualCoordinates f i }
  let region : Label → Set Θ := fun p =>
    { f | ∃ h : ArtinNormalisers.Theorem18.Dual S,
      h ∈ face p.val.2 ∧ ArtinNormalisers.Theorem18.dualAction M p.val.1 h = f.val }
  let affineDimension : Set Θ → Nat := fun C =>
    Module.finrank Real (AffineSubspace.direction (affineSpan Real C))
  let wall : Set Θ → Set Θ → Prop := fun C F =>
    Set.Nonempty F ∧ ∃ H : Submodule Real Θ, H ∈ arrangement ∧
      F = closure C ∩ (H : Set Θ) ∧ affineDimension F + 1 = affineDimension C
  let adjacent : Label → Label → Prop := fun p q =>
    region p ≠ region q ∧ ∃ F : Set Θ, wall (region p) F ∧ wall (region q) F
  let component : Set S → S → Set S := fun I a =>
    { b | b ∈ Set.insert a I ∧ Relation.ReflTransGen
      (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b }
  let Norm := ArtinNormalisers.Theorem18.CoxeterNormalizer M J
  let N := ArtinNormalisers.Artin.coxeterNormalizerQuotient M J
  let quotientMap : Norm → N := QuotientGroup.mk'
    ((ArtinNormalisers.Artin.coxeterParabolic M J).subgroupOf Norm)
  ∃ action : N →* Equiv.Perm Label,
    (∀ (g : Norm) (p : Label),
      let y := action (quotientMap g) p
      y.val.2 = p.val.2 ∧
      CoxeterSystem.IsMinimalCosetRep cs p.val.2 y.val.1 ∧
      ∃ u : W, u ∈ CoxeterSystem.parabolic cs p.val.2 ∧
        y.val.1 = g.val * p.val.1 * u) ∧
    (∀ p q : Label, (∃ g : N, action g p = q) ↔ p.val.2 = q.val.2) ∧
    (∀ (g : N) (p : Label), action g p = p → g = 1) ∧
    (∀ (g : N) (p : Label),
      Set.image (ArtinNormalisers.Theorem18.quotientRepresentation M J g) (region p) =
        region (action g p)) ∧
    (∀ (g : N) (p q : Label), adjacent p q → adjacent (action g p) (action g q)) ∧
    (∀ (g : N) (p q : Label), adjacent p q →
      ∀ (a : S) (ha : a ∉ p.val.2)
        (hD : Finite (CoxeterSystem.parabolic cs (component p.val.2 a))),
        (SimpleWallCrossings S W M cs p.val.2 a ha hD).2.2 p.val.1 = q.val →
        (SimpleWallCrossings S W M cs p.val.2 a ha hD).2.2 (action g p).val.1 =
          (action g q).val)) :=
(by
  classical
  intro S inst M J
  let W := CoxeterMatrix.Group M
  let cs := CoxeterMatrix.toCoxeterSystem M
  let Label := { p : W × Set S //
    Set.image (fun u : W => u * p.1) (CoxeterSystem.parabolic cs J : Set W) =
      Set.image (fun u : W => p.1 * u) (CoxeterSystem.parabolic cs p.2 : Set W) ∧
    CoxeterSystem.IsMinimalCosetRep cs p.2 p.1 }
  /- Lemma 3.24, printed p.12, https://arxiv.org/pdf/2509.21915#page=12.
  Portal inspiration: steps 1.1, 2.1--2.4 and 3.1 at
  https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-normaliser-chamber-action-artin-tits-normalisers.
  The local blocks below have no original standalone article statements.
  Departure from the geometric exposition: canonical minimal representatives
  construct the action and its quotient descent first; parabolic fixing gives
  region covariance. Pairing and opposite-root kernels transport walls;
  root positivity proves crossing minimality before coset uniqueness is used.
  The completed internal elementary-wall proof is embedded locally, rather
  than assuming an additional imported endpoint. Its source comments are retained.
  Finite rank in the geometric endpoint follows explicit user direction;
  no finite Coxeter group or spherical parabolic is assumed globally.
  Literature disposition: defect report finding pdf-d4-normaliser-freeness,
  https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects#pdf-d4-normaliser-freeness,
  concerns the later printed p.29 example: nontrivial W_J elements act trivially.
  It explicitly does not refute Lemma 3.24. Freeness here is proved only after
  passage to Norm(W_J)/W_J; no endpoint substitution is made. -/
  let BrinkHowlettGroupoid : (∀ (cs : CoxeterSystem M W) (J : Set S), CategoryTheory.Groupoid { I : Set S // ∃ w : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj w)) (CoxeterSystem.parabolic cs I) = CoxeterSystem.parabolic cs J }) :=
  (by
    intro cs J
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
  have ElementaryWallMorphism : (∀ (cs : CoxeterSystem M W) (J I : Set S) (hI : ∃ w : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj w)) (CoxeterSystem.parabolic cs I) = CoxeterSystem.parabolic cs J) (a : S) (ha : a ∉ I), let D : Set S := {b | b ∈ Set.insert a I ∧ Relation.ReflTransGen (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b}; ∀ hD : Finite (CoxeterSystem.parabolic cs D), let crossing := SimpleWallCrossings S W M cs I a ha hD; ∃ hK : ∃ w : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj w)) (CoxeterSystem.parabolic cs crossing.2.1) = CoxeterSystem.parabolic cs J, ∃ f : (BrinkHowlettGroupoid cs J).Hom ⟨I, hI⟩ ⟨crossing.2.1, hK⟩, f.val = crossing.1) :=
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
    intro cs J I hI a ha D hD
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
  have checkedAlgebra :
      let W := M.Group
      let cs := M.toCoxeterSystem
      let Label := {p : W × Set S //
        (fun u => u * p.1) '' (cs.parabolic J : Set W) =
        (fun u => p.1 * u) '' (cs.parabolic p.2 : Set W) ∧
        cs.IsMinimalCosetRep p.2 p.1}
      let Norm := ArtinNormalisers.Theorem18.CoxeterNormalizer M J
      let N := ArtinNormalisers.Artin.coxeterNormalizerQuotient M J
      let quotientMap : Norm → N := QuotientGroup.mk'
        ((ArtinNormalisers.Artin.coxeterParabolic M J).subgroupOf Norm)
      ∃ action : N →* Equiv.Perm Label,
        (∀ (g : Norm) (p : Label),
          let y := action (quotientMap g) p
          y.val.2 = p.val.2 ∧ cs.IsMinimalCosetRep p.val.2 y.val.1 ∧
          ∃ u : W, u ∈ cs.parabolic p.val.2 ∧ y.val.1 = g.val * p.val.1 * u) ∧
        (∀ p q : Label, (∃ g : N, action g p = q) ↔ p.val.2 = q.val.2) ∧
        (∀ (g : N) (p : Label), action g p = p → g = 1) := by
    classical
    let W := M.Group
    let cs := M.toCoxeterSystem
    let Label := {p : W × Set S //
        (fun u => u * p.1) '' (cs.parabolic J : Set W) =
        (fun u => p.1 * u) '' (cs.parabolic p.2 : Set W) ∧
        cs.IsMinimalCosetRep p.2 p.1}
    let Norm := ArtinNormalisers.Theorem18.CoxeterNormalizer M J
    let N := ArtinNormalisers.Artin.coxeterNormalizerQuotient M J
    let H := (ArtinNormalisers.Artin.coxeterParabolic M J).subgroupOf Norm
    let quotientMap : Norm → N := QuotientGroup.mk' H
    have coset_iff_conj (P Q : Subgroup W) (x : W) :
        (fun u => u * x) '' (P : Set W) = (fun u => x * u) '' (Q : Set W) ↔
        Q.map (MulAut.conj x).toMonoidHom = P := by
      constructor
      · intro h
        ext z
        rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
        constructor
        · intro hz
          have ht : z * x ∈ (fun u => x * u) '' (Q : Set W) :=
            ⟨x⁻¹ * z * x, hz, by group⟩
          rw [← h] at ht
          obtain ⟨u, hu, he⟩ := ht
          have : u = z := mul_right_cancel he
          simpa [this] using hu
        · intro hz
          have ht : z * x ∈ (fun u => u * x) '' (P : Set W) := ⟨z, hz, rfl⟩
          rw [h] at ht
          obtain ⟨u, hu, he⟩ := ht
          have : x⁻¹ * z * x = u := by
            change x * u = z * x at he
            calc
              x⁻¹ * z * x = x⁻¹ * (z * x) := by group
              _ = x⁻¹ * (x * u) := by rw [← he]
              _ = u := by group
          simpa [this] using hu
      · intro h
        ext z
        constructor
        · rintro ⟨u, hu, rfl⟩
          change u ∈ P at hu
          rw [← h, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hu
          exact ⟨x⁻¹ * u * x, hu, by group⟩
        · rintro ⟨u, hu, rfl⟩
          refine ⟨x * u * x⁻¹, ?_, by group⟩
          rw [← h]
          exact ⟨u, hu, rfl⟩
  
    have conj_product (P : Subgroup W) (x y : W) :
        P.map (MulAut.conj (x * y)).toMonoidHom =
          (P.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
      rw [Subgroup.map_map]
      apply congrArg (fun f : W →* W => P.map f)
      apply MonoidHom.ext
      intro z
      change (x*y)*z*(x*y)⁻¹ = x*(y*z*y⁻¹)*x⁻¹
      group
  
    let A : Norm →* Equiv.Perm Label := by
      have htrans (g : Norm) (p : Label) :
          (cs.parabolic p.val.2).map (MulAut.conj (g.val * p.val.1)).toMonoidHom =
            cs.parabolic J := by
        rw [conj_product, (coset_iff_conj _ _ _).mp p.property.1]
        rw [MulEquiv.toMonoidHom_eq_coe]
        simpa only [ArtinNormalisers.Artin.coxeterParabolic_eq] using
          Subgroup.mem_normalizer_iff_map_conj_eq.mp g.property
      let act : Norm → Label → Label := fun g p =>
        ⟨(cs.minimalCosetRep p.val.2 (g.val * p.val.1), p.val.2),
          (coset_iff_conj _ _ _).mpr
            (ArtinNormalisers.Chamber3.minimalCosetRep_transports_parabolic cs (htrans g p)),
          cs.isMinimalCosetRep_minimalCosetRep _ _⟩
      have act_spec (g : Norm) (p : Label) :
          ∃ u, u ∈ cs.parabolic p.val.2 ∧ (act g p).val.1 = g.val * p.val.1 * u := by
        refine ⟨(g.val * p.val.1)⁻¹ * (act g p).val.1,
          cs.inv_mul_minimalCosetRep_mem _ _, ?_⟩
        group
      have act_one (p : Label) : act 1 p = p := by
        apply Subtype.ext
        refine Prod.ext ?_ rfl
        apply CoxeterSystem.IsMinimalCosetRep.eq_of_inv_mul_mem cs
          (cs.isMinimalCosetRep_minimalCosetRep _ _) p.property.2
        obtain ⟨u, hu, he⟩ := act_spec 1 p
        change (act 1 p).val.1⁻¹ * p.val.1 ∈ _
        rw [he]
        simpa only [Subgroup.coe_one, one_mul, mul_inv_rev, mul_assoc,
          inv_mul_cancel_left, inv_mul_cancel, mul_one] using (cs.parabolic p.val.2).inv_mem hu
      have act_mul (g h : Norm) (p : Label) : act (g * h) p = act g (act h p) := by
        apply Subtype.ext
        refine Prod.ext ?_ rfl
        apply CoxeterSystem.IsMinimalCosetRep.eq_of_inv_mul_mem cs
          (cs.isMinimalCosetRep_minimalCosetRep _ _) (cs.isMinimalCosetRep_minimalCosetRep _ _)
        obtain ⟨u, hu, he⟩ := act_spec (g*h) p
        obtain ⟨v, hv, hf⟩ := act_spec h p
        obtain ⟨t, ht, hk⟩ := act_spec g (act h p)
        change (act (g*h) p).val.1⁻¹ * (act g (act h p)).val.1 ∈ _
        rw [he, hk, hf]
        have hh : ((g*h).val*p.val.1*u)⁻¹ *
            (g.val*(h.val*p.val.1*v)*t) = u⁻¹*v*t := by
          change ((g.val*h.val)*p.val.1*u)⁻¹ * _ = _
          group
        rw [hh]
        exact (cs.parabolic p.val.2).mul_mem ((cs.parabolic p.val.2).mul_mem
          ((cs.parabolic p.val.2).inv_mem hu) hv) ht
      exact {
        toFun := fun g => {
          toFun := act g
          invFun := act g⁻¹
          left_inv := fun p => by rw [← act_mul, inv_mul_cancel, act_one]
          right_inv := fun p => by rw [← act_mul, mul_inv_cancel, act_one] }
        map_one' := by apply Equiv.ext; intro p; exact act_one p
        map_mul' := by intro g h; apply Equiv.ext; intro p; exact act_mul g h p }
  
    have A_snd (g : Norm) (p : Label) : (A g p).val.2 = p.val.2 := rfl
    have A_min (g : Norm) (p : Label) : cs.IsMinimalCosetRep p.val.2 (A g p).val.1 :=
      cs.isMinimalCosetRep_minimalCosetRep _ _
    have A_spec (g : Norm) (p : Label) :
        ∃ u : W, u ∈ cs.parabolic p.val.2 ∧ (A g p).val.1 = g.val * p.val.1 * u := by
      refine ⟨(g.val * p.val.1)⁻¹ * (A g p).val.1,
        cs.inv_mul_minimalCosetRep_mem _ _, ?_⟩
      group
    have parabolic_kernel : H ≤ A.ker := by
      intro g hg
      apply MonoidHom.mem_ker.mpr
      apply Equiv.ext
      intro p
      change A g p = p
      apply Subtype.ext
      refine Prod.ext ?_ (A_snd g p)
      have hgJ : g.val ∈ cs.parabolic J := by
        change g.val ∈ ArtinNormalisers.Artin.coxeterParabolic M J at hg
        simpa only [ArtinNormalisers.Artin.coxeterParabolic_eq] using hg
      have hp := (coset_iff_conj _ _ _).mp p.property.1
      rw [← hp, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hgJ
      obtain ⟨u, hu, he⟩ := A_spec g p
      apply CoxeterSystem.IsMinimalCosetRep.eq_of_inv_mul_mem cs (A_min g p) p.property.2
      rw [he]
      have heq : (g.val * p.val.1 * u)⁻¹ * p.val.1 =
          u⁻¹ * (p.val.1⁻¹ * g.val * p.val.1)⁻¹ := by group
      rw [heq]
      exact (cs.parabolic p.val.2).mul_mem
        ((cs.parabolic p.val.2).inv_mem hu) ((cs.parabolic p.val.2).inv_mem hgJ)
    let action : N →* Equiv.Perm Label := QuotientGroup.lift H A parabolic_kernel
    have action_mk (g : Norm) : action (quotientMap g) = A g := rfl
    refine ⟨action, ?_, ?_, ?_⟩
    · intro g p
      change (action (quotientMap g) p).val.2 = p.val.2 ∧ _
      rw [action_mk]
      exact ⟨A_snd g p, A_min g p, A_spec g p⟩
    · intro p q
      constructor
      · rintro ⟨g, hg⟩
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H g
        change action (quotientMap g) p = q at hg
        rw [action_mk] at hg
        exact (A_snd g p).symm.trans (congrArg (fun z : Label => z.val.2) hg)
      · intro hpq
        have hp := (coset_iff_conj _ _ _).mp p.property.1
        have hq := (coset_iff_conj _ _ _).mp q.property.1
        have hinv : (cs.parabolic J).map (MulAut.conj p.val.1⁻¹).toMonoidHom =
            cs.parabolic p.val.2 := ArtinNormalisers.Chamber3.inverse_parabolic_transporter cs hp
        have hg : q.val.1 * p.val.1⁻¹ ∈
            Subgroup.normalizer (cs.parabolic J : Set W) := by
          apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
          rw [← MulEquiv.toMonoidHom_eq_coe, conj_product, hinv, hpq, hq]
        let g : Norm := ⟨q.val.1 * p.val.1⁻¹, by
          change _ ∈ Subgroup.normalizer (ArtinNormalisers.Artin.coxeterParabolic M J : Set W)
          rw [ArtinNormalisers.Artin.coxeterParabolic_eq]
          exact hg⟩
        refine ⟨quotientMap g, ?_⟩
        rw [action_mk]
        apply Subtype.ext
        refine Prod.ext ?_ ((A_snd g p).trans hpq)
        apply CoxeterSystem.IsMinimalCosetRep.eq_of_inv_mul_mem cs
          (A_min g p) (by simpa only [hpq] using q.property.2)
        obtain ⟨u, hu, he⟩ := A_spec g p
        rw [he]
        have heq : (g.val * p.val.1 * u)⁻¹ * q.val.1 = u⁻¹ := by
          dsimp [g]
          group
        rw [heq]
        exact (cs.parabolic p.val.2).inv_mem hu
    · intro g p hg
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H g
      change action (quotientMap g) p = p at hg
      rw [action_mk] at hg
      obtain ⟨u, hu, he⟩ := A_spec g p
      have hf : (A g p).val.1 = p.val.1 := congrArg (fun z : Label => z.val.1) hg
      have heq : g.val = p.val.1 * u⁻¹ * p.val.1⁻¹ := by
        rw [hf] at he
        calc
          g.val = (g.val * p.val.1 * u) * u⁻¹ * p.val.1⁻¹ := by group
          _ = p.val.1 * u⁻¹ * p.val.1⁻¹ := by rw [← he]
      have hgJ : g.val ∈ cs.parabolic J := by
        rw [← (coset_iff_conj _ _ _).mp p.property.1, heq]
        exact ⟨u⁻¹, (cs.parabolic p.val.2).inv_mem hu, rfl⟩
      apply (QuotientGroup.eq_one_iff g).mpr
      change g.val ∈ ArtinNormalisers.Artin.coxeterParabolic M J
      simpa only [ArtinNormalisers.Artin.coxeterParabolic_eq] using hgJ
  have checkedRegionCovariance :
    let W := CoxeterMatrix.Group M
    let cs := CoxeterMatrix.toCoxeterSystem M
    let Label := { p : W × Set S //
      Set.image (fun u : W => u * p.1) (CoxeterSystem.parabolic cs J : Set W) =
        Set.image (fun u : W => p.1 * u) (CoxeterSystem.parabolic cs p.2 : Set W) ∧
      CoxeterSystem.IsMinimalCosetRep cs p.2 p.1 }
    let Θ := ArtinNormalisers.Theorem18.relativeSubspace J
    letI : TopologicalSpace Θ := TopologicalSpace.induced
      (fun f : Θ => ArtinNormalisers.Theorem18.dualCoordinates f.val)
      (inferInstance : TopologicalSpace (S → Real))
    let face : Set S → Set (ArtinNormalisers.Theorem18.Dual S) := fun I =>
      { f | f ∈ ArtinNormalisers.Theorem18.relativeSubspace I ∧
        ∀ i : S, i ∉ I → 0 < ArtinNormalisers.Theorem18.dualCoordinates f i }
    let region : Label → Set Θ := fun p =>
      { f | ∃ h : ArtinNormalisers.Theorem18.Dual S,
        h ∈ face p.val.2 ∧ ArtinNormalisers.Theorem18.dualAction M p.val.1 h = f.val }
    let Norm := ArtinNormalisers.Theorem18.CoxeterNormalizer M J
    let N := ArtinNormalisers.Artin.coxeterNormalizerQuotient M J
    let quotientMap : Norm → N := QuotientGroup.mk'
      ((ArtinNormalisers.Artin.coxeterParabolic M J).subgroupOf Norm)
    ∀ action : N →* Equiv.Perm Label,
      (∀ (g : Norm) (p : Label),
        let y := action (quotientMap g) p
        y.val.2 = p.val.2 ∧
        CoxeterSystem.IsMinimalCosetRep cs p.val.2 y.val.1 ∧
        ∃ u : W, u ∈ CoxeterSystem.parabolic cs p.val.2 ∧
          y.val.1 = g.val * p.val.1 * u) →
      ∀ (n : N) (p : Label),
        Set.image (ArtinNormalisers.Theorem18.quotientRepresentation M J n) (region p) =
          region (action n p) := by
    dsimp only
    intro action formula
    let W := CoxeterMatrix.Group M
    let cs := CoxeterMatrix.toCoxeterSystem M
    let Label := { p : W × Set S //
      Set.image (fun u : W => u * p.1) (CoxeterSystem.parabolic cs J : Set W) =
        Set.image (fun u : W => p.1 * u) (CoxeterSystem.parabolic cs p.2 : Set W) ∧
      CoxeterSystem.IsMinimalCosetRep cs p.2 p.1 }
    let Θ := ArtinNormalisers.Theorem18.relativeSubspace J
    let face : Set S → Set (ArtinNormalisers.Theorem18.Dual S) := fun I =>
      { f | f ∈ ArtinNormalisers.Theorem18.relativeSubspace I ∧
        ∀ i : S, i ∉ I → 0 < ArtinNormalisers.Theorem18.dualCoordinates f i }
    let region : Label → Set Θ := fun p =>
      { f | ∃ h : ArtinNormalisers.Theorem18.Dual S,
        h ∈ face p.val.2 ∧ ArtinNormalisers.Theorem18.dualAction M p.val.1 h = f.val }
    let Norm := ArtinNormalisers.Theorem18.CoxeterNormalizer M J
    let N := ArtinNormalisers.Artin.coxeterNormalizerQuotient M J
    let quotientMap : Norm → N := QuotientGroup.mk'
      ((ArtinNormalisers.Artin.coxeterParabolic M J).subgroupOf Norm)
    -- Portal step 1.1 / F3: the right parabolic factor fixes the face pointwise.
    have region_covariance : ∀ (n : N) (p : Label),
        Set.image (ArtinNormalisers.Theorem18.quotientRepresentation M J n) (region p) =
          region (action n p) := by
      have maps_region (n : N) (p : Label) :
          Set.MapsTo (ArtinNormalisers.Theorem18.quotientRepresentation M J n)
            (region p) (region (action n p)) := by
        obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
          ((ArtinNormalisers.Artin.coxeterParabolic M J).subgroupOf Norm) n
        obtain ⟨hI, _hminimal, u, hu, hy⟩ := formula g p
        intro f hf
        obtain ⟨h, hh, he⟩ := hf
        have hfix : ArtinNormalisers.Theorem18.dualAction M u h = h :=
          (ArtinNormalisers.Theorem18.mem_relativeSubspace_iff_fixed M p.val.2 h).mp hh.1 u
            (by simpa only [ArtinNormalisers.Artin.coxeterParabolic_eq] using hu)
        refine ⟨h, ?_, ?_⟩
        · change h ∈ face (action (quotientMap g) p).val.2
          rw [hI]
          exact hh
        · rw [hy, map_mul, mul_apply_eq_comp, hfix, map_mul, mul_apply_eq_comp, he]
          exact ((congrArg Subtype.val
            (ArtinNormalisers.Theorem18.quotientRepresentation_mk M J g f)).trans
              (ArtinNormalisers.Theorem18.normalizerRepresentation_apply_val M J g f)).symm
      -- Apply the same inclusion to the inverse quotient element. This uses
      -- only the representation and permutation action laws, with no topology
      -- or separate assertion that an ambient translated face lies in Θ_J.
      intro n p
      apply Set.Subset.antisymm
      · rintro _ ⟨f, hf, rfl⟩
        exact maps_region n p hf
      · intro f hf
        let t := ArtinNormalisers.Theorem18.quotientRepresentation M J n⁻¹ f
        have ht : t ∈ region p := by
          have h := maps_region n⁻¹ (action n p) hf
          simpa only [← Equiv.Perm.mul_apply, ← map_mul, inv_mul_cancel,
            map_one, Equiv.Perm.one_apply] using h
        refine ⟨t, ht, ?_⟩
        exact Representation.self_inv_apply (ArtinNormalisers.Theorem18.quotientRepresentation M J) n f
    exact region_covariance
  have wallTransport :
      let Θ := ArtinNormalisers.Theorem18.relativeSubspace J
      letI : TopologicalSpace Θ := TopologicalSpace.induced
        (fun f : Θ => ArtinNormalisers.Theorem18.dualCoordinates f.val)
        (inferInstance : TopologicalSpace (S → Real))
      let arrangement : Set (Submodule Real Θ) := (RelativeCone M J).2.2.2.2.2
      let affineDimension : Set Θ → Nat := fun C =>
        Module.finrank Real (AffineSubspace.direction (affineSpan Real C))
      let wall : Set Θ → Set Θ → Prop := fun C F =>
        Set.Nonempty F ∧ ∃ H : Submodule Real Θ, H ∈ arrangement ∧
          F = closure C ∩ (H : Set Θ) ∧ affineDimension F + 1 = affineDimension C
      ∀ g : ArtinNormalisers.Theorem18.CoxeterNormalizer M J,
        let T := ArtinNormalisers.Chamber3.normalizerFlatEquiv M J g
        (∀ C F : Set Θ, wall C F → wall (T '' C) (T '' F)) ∧
        (∀ (region : Label → Set Θ) (σ : Label → Label),
          (∀ p, T '' region p = region (σ p)) →
          ∀ p q, (region p ≠ region q ∧ ∃ F, wall (region p) F ∧ wall (region q) F) →
            region (σ p) ≠ region (σ q) ∧
              ∃ F, wall (region (σ p)) F ∧ wall (region (σ q)) F) := by
    classical
    let Θ := ArtinNormalisers.Theorem18.relativeSubspace J
    have htop : TopologicalSpace.induced
        (fun f : Θ => ArtinNormalisers.Theorem18.dualCoordinates f.val)
        (inferInstance : TopologicalSpace (S → Real)) =
        (inferInstance : TopologicalSpace Θ) := by
      exact induced_compose.symm
    dsimp only
    rw [htop]
    let arrangement : Set (Submodule Real Θ) := (RelativeCone M J).2.2.2.2.2
    let affineDimension : Set Θ → Nat := fun C =>
      Module.finrank Real (AffineSubspace.direction (affineSpan Real C))
    let wall : Set Θ → Set Θ → Prop := fun C F =>
      Set.Nonempty F ∧ ∃ H : Submodule Real Θ, H ∈ arrangement ∧
        F = closure C ∩ (H : Set Θ) ∧ affineDimension F + 1 = affineDimension C
    change ∀ g : ArtinNormalisers.Theorem18.CoxeterNormalizer M J, _
    intro g
    let T := ArtinNormalisers.Chamber3.normalizerFlatEquiv M J g
    -- Pairing gives transport of the actual restricted evaluation kernels.
    have hkernel (r : ArtinNormalisers.Theorem18.Vector S) :
        (ArtinNormalisers.Theorem18.restrictedHyperplane J r).map T.toLinearMap =
          ArtinNormalisers.Theorem18.restrictedHyperplane J (M.toCoxeterSystem.geometricRepresentation g.val r) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        change (ArtinNormalisers.Theorem18.dualAction M g.val x.val)
          (M.toCoxeterSystem.geometricRepresentation g.val r) = 0
        rw [ArtinNormalisers.Theorem18.dualAction_pairing]
        exact hx
      · intro hy
        refine ⟨T.symm y, ?_, T.apply_symm_apply y⟩
        have hp := ArtinNormalisers.Theorem18.dualAction_pairing M g.val (T.symm y).val r
        change (T (T.symm y)).val
          (M.toCoxeterSystem.geometricRepresentation g.val r) = (T.symm y).val r at hp
        rw [T.apply_symm_apply] at hp
        exact hp.symm.trans hy
    have hnegKernel (r : ArtinNormalisers.Theorem18.Vector S) : ArtinNormalisers.Theorem18.restrictedHyperplane J (-r) =
        ArtinNormalisers.Theorem18.restrictedHyperplane J r := by
      ext f
      change f.val (-r) = 0 ↔ f.val r = 0
      rw [map_neg, neg_eq_zero]
    -- The endpoint arrangement uses positive retained roots. Transported roots
    -- need not be positive: use the root-sign dichotomy and equal opposite kernels.
    have harrangement (H : Submodule Real Θ) (hH : H ∈ arrangement) :
        H.map T.toLinearMap ∈ arrangement := by
      obtain ⟨r, hr, rfl⟩ := hH
      have hs := ArtinNormalisers.Theorem18.geometricAction_mem_retainedRoots M J g hr.1
      have hsroot : M.toCoxeterSystem.geometricRepresentation g.val r ∈
          M.toCoxeterSystem.geometricRoots := hs.1
      rw [hkernel]
      rcases M.toCoxeterSystem.pos_or_neg_of_mem_geometricRoots hsroot with hpos | hneg
      · exact ⟨_, ⟨hs, hpos⟩, rfl⟩
      · have hns : -(M.toCoxeterSystem.geometricRepresentation g.val r) ∈
            ArtinNormalisers.Theorem18.retainedRoots M J := by
          refine ⟨?_, ?_⟩
          · exact M.toCoxeterSystem.neg_mem_geometricRoots_iff.mpr hsroot
          · obtain ⟨f, hf⟩ := hs.2
            exact ⟨f, by simpa only [map_neg, neg_ne_zero] using hf⟩
        exact ⟨_, ⟨hns, neg_pos.mpr hneg⟩, hnegKernel _⟩
    have hdimension (C : Set Θ) : affineDimension (T '' C) = affineDimension C := by
      change Module.finrank Real (affineSpan Real (T '' C)).direction = _
      let f : Θ →ᵃ[Real] Θ := (T.toLinearMap : Θ →ₗ[Real] Θ).toAffineMap
      change Module.finrank Real (affineSpan Real (f '' C)).direction = _
      rw [← AffineSubspace.map_span f, AffineSubspace.map_direction]
      exact T.toLinearEquiv.finrank_map_eq _
    -- General wall-image argument, kept local rather than a prerequisite item.
    have hwallImage (C F : Set Θ) (hF : wall C F) : wall (T '' C) (T '' F) := by
      obtain ⟨hne, H, hH, hFH, hdim⟩ := hF
      refine ⟨hne.image T, H.map T.toLinearMap, harrangement H hH, ?_, ?_⟩
      · change T '' F = closure (T '' C) ∩ T '' (H : Set Θ)
        rw [hFH, Set.image_inter T.injective, T.image_closure]
      · rw [hdimension, hdimension]
        exact hdim
    refine ⟨hwallImage, ?_⟩
    intro region σ hcov p q hpq
    obtain ⟨hne, F, hp, hq⟩ := hpq
    refine ⟨?_, T '' F, ?_, ?_⟩
    · intro heq
      apply hne
      apply T.injective.image_injective
      rw [hcov, hcov, heq]
    · rw [← hcov]
      exact hwallImage _ _ hp
    · rw [← hcov]
      exact hwallImage _ _ hq
  have quotientAdjacencyFromCovariance :
      let Θ := ArtinNormalisers.Theorem18.relativeSubspace J
      letI : TopologicalSpace Θ := TopologicalSpace.induced
        (fun f : Θ => ArtinNormalisers.Theorem18.dualCoordinates f.val)
        (inferInstance : TopologicalSpace (S → Real))
      let arrangement : Set (Submodule Real Θ) := (RelativeCone M J).2.2.2.2.2
      let affineDimension : Set Θ → Nat := fun C =>
        Module.finrank Real (AffineSubspace.direction (affineSpan Real C))
      let wall : Set Θ → Set Θ → Prop := fun C F =>
        Set.Nonempty F ∧ ∃ H : Submodule Real Θ, H ∈ arrangement ∧
          F = closure C ∩ (H : Set Θ) ∧ affineDimension F + 1 = affineDimension C
      ∀ (region : Label → Set Θ)
        (action : ArtinNormalisers.Artin.coxeterNormalizerQuotient M J →* Equiv.Perm Label),
        (∀ n p, ArtinNormalisers.Theorem18.quotientRepresentation M J n '' region p = region (action n p)) →
        ∀ n p q,
          (region p ≠ region q ∧ ∃ F, wall (region p) F ∧ wall (region q) F) →
          region (action n p) ≠ region (action n q) ∧
            ∃ F, wall (region (action n p)) F ∧ wall (region (action n q)) F := by
    dsimp only
    intro region action hcov n p q hpq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
      ((ArtinNormalisers.Artin.coxeterParabolic M J).subgroupOf (ArtinNormalisers.Theorem18.CoxeterNormalizer M J)) n
    have hrep : ⇑(ArtinNormalisers.Theorem18.quotientRepresentation M J
        (QuotientGroup.mk' ((ArtinNormalisers.Artin.coxeterParabolic M J).subgroupOf
          (ArtinNormalisers.Theorem18.CoxeterNormalizer M J)) g)) = ⇑(ArtinNormalisers.Chamber3.normalizerFlatEquiv M J g) := by
      funext x
      exact ArtinNormalisers.Theorem18.quotientRepresentation_mk M J g x
    apply (wallTransport g).2 region (action _) _ p q hpq
    intro r
    rw [← hrep]
    exact hcov _ r
  let Θ := ArtinNormalisers.Theorem18.relativeSubspace J
  letI : TopologicalSpace Θ := TopologicalSpace.induced
    (fun f : Θ => ArtinNormalisers.Theorem18.dualCoordinates f.val)
    (inferInstance : TopologicalSpace (S → Real))
  let arrangement : Set (Submodule Real Θ) := (RelativeCone M J).2.2.2.2.2
  let face : Set S → Set (ArtinNormalisers.Theorem18.Dual S) := fun I =>
    { f | f ∈ ArtinNormalisers.Theorem18.relativeSubspace I ∧
      ∀ i : S, i ∉ I → 0 < ArtinNormalisers.Theorem18.dualCoordinates f i }
  let region : Label → Set Θ := fun p =>
    { f | ∃ h : ArtinNormalisers.Theorem18.Dual S,
      h ∈ face p.val.2 ∧ ArtinNormalisers.Theorem18.dualAction M p.val.1 h = f.val }
  let affineDimension : Set Θ → Nat := fun C =>
    Module.finrank Real (AffineSubspace.direction (affineSpan Real C))
  let wall : Set Θ → Set Θ → Prop := fun C F =>
    Set.Nonempty F ∧ ∃ H : Submodule Real Θ, H ∈ arrangement ∧
      F = closure C ∩ (H : Set Θ) ∧ affineDimension F + 1 = affineDimension C
  let adjacent : Label → Label → Prop := fun p q =>
    region p ≠ region q ∧ ∃ F : Set Θ, wall (region p) F ∧ wall (region q) F
  let component : Set S → S → Set S := fun I a =>
    { b | b ∈ Set.insert a I ∧ Relation.ReflTransGen
      (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b }
  let Norm := ArtinNormalisers.Theorem18.CoxeterNormalizer M J
  let N := ArtinNormalisers.Artin.coxeterNormalizerQuotient M J
  let quotientMap : Norm → N := QuotientGroup.mk'
    ((ArtinNormalisers.Artin.coxeterParabolic M J).subgroupOf Norm)
  have nca_crossing_equivariance :
      ∀ (action : N →* Equiv.Perm Label),
        (∀ (g : Norm) (p : Label),
          let y := action (quotientMap g) p
          y.val.2 = p.val.2 ∧
          CoxeterSystem.IsMinimalCosetRep cs p.val.2 y.val.1 ∧
          ∃ u : W, u ∈ CoxeterSystem.parabolic cs p.val.2 ∧
            y.val.1 = g.val * p.val.1 * u) →
        ∀ (adjacent : Label → Label → Prop) (n : N) (p q : Label), adjacent p q →
        ∀ (a : S) (ha : a ∉ p.val.2)
          (hD : Finite (CoxeterSystem.parabolic cs (component p.val.2 a))),
          (SimpleWallCrossings S W M cs p.val.2 a ha hD).2.2 p.val.1 = q.val →
          (SimpleWallCrossings S W M cs p.val.2 a ha hD).2.2 (action n p).val.1 =
            (action n q).val := by
    intro action hrep adjacent n p q _ a ha hD hpq
    have coset_iff_conj (P Q : Subgroup W) (x : W) :
        (fun u => u * x) '' (P : Set W) = (fun u => x * u) '' (Q : Set W) ↔
        Q.map (MulAut.conj x).toMonoidHom = P := by
      constructor
      · intro h
        ext z
        rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
        constructor
        · intro hz
          have ht : z * x ∈ (fun u => x * u) '' (Q : Set W) :=
            ⟨x⁻¹ * z * x, hz, by group⟩
          rw [← h] at ht
          obtain ⟨u, hu, he⟩ := ht
          have : u = z := mul_right_cancel he
          simpa [this] using hu
        · intro hz
          have ht : z * x ∈ (fun u => u * x) '' (P : Set W) := ⟨z, hz, rfl⟩
          rw [h] at ht
          obtain ⟨u, hu, he⟩ := ht
          have : x⁻¹ * z * x = u := by
            change x * u = z * x at he
            calc
              x⁻¹ * z * x = x⁻¹ * (z * x) := by group
              _ = x⁻¹ * (x * u) := by rw [← he]
              _ = u := by group
          simpa [this] using hu
      · intro h
        ext z
        constructor
        · rintro ⟨u, hu, rfl⟩
          change u ∈ P at hu
          rw [← h, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hu
          exact ⟨x⁻¹ * u * x, hu, by group⟩
        · rintro ⟨u, hu, rfl⟩
          refine ⟨x * u * x⁻¹, ?_, by group⟩
          rw [← h]
          exact ⟨u, hu, rfl⟩
  
    have conj_product (P : Subgroup W) (x y : W) :
        P.map (MulAut.conj (x * y)).toMonoidHom =
          (P.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
      rw [Subgroup.map_map]
      apply congrArg (fun f : W →* W => P.map f)
      apply MonoidHom.ext
      intro z
      change (x*y)*z*(x*y)⁻¹ = x*(y*z*y⁻¹)*x⁻¹
      group
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective
      ((ArtinNormalisers.Artin.coxeterParabolic M J).subgroupOf Norm) n
    let c := SimpleWallCrossings S W M cs p.val.2 a ha hD
    have hq1 : q.val.1 = p.val.1 * c.1 := (congrArg Prod.fst hpq).symm
    have hq2 : q.val.2 = c.2.1 := (congrArg Prod.snd hpq).symm
    have hpconj := (coset_iff_conj (cs.parabolic J) (cs.parabolic p.val.2) p.val.1).mp p.property.1
    have hqconj := (coset_iff_conj (cs.parabolic J) (cs.parabolic q.val.2) q.val.1).mp q.property.1
    have hI : ∃ w : W, (cs.parabolic p.val.2).map (MulAut.conj w).toMonoidHom =
        cs.parabolic J := ⟨p.val.1, hpconj⟩
    obtain ⟨hK, f, hf⟩ := ElementaryWallMorphism cs J p.val.2 hI a ha hD
    have hroots : cs.geometricRepresentation c.1 ''
        ((fun i : S => Finsupp.single i (1 : Real)) '' c.2.1) =
        (fun i : S => Finsupp.single i (1 : Real)) '' p.val.2 := by
      have h := f.property
      change cs.geometricRepresentation f.val ''
        ((fun i : S => Finsupp.single i (1 : Real)) '' c.2.1) =
        (fun i : S => Finsupp.single i (1 : Real)) '' p.val.2 at h
      rwa [hf] at h
    have hconj : (cs.parabolic c.2.1).map (MulAut.conj c.1).toMonoidHom =
        cs.parabolic p.val.2 := by
      apply Subgroup.map_injective (f := (MulAut.conj p.val.1).toMonoidHom)
        (MulAut.conj p.val.1).injective
      rw [← conj_product, ← hq2, ← hq1, hqconj, hpconj]
    obtain ⟨_, hymin, u, hu, hy⟩ := hrep g p
    obtain ⟨hz2, hzmin, t, ht, hz⟩ := hrep g q
    have hmin : cs.IsMinimalCosetRep c.2.1
        ((action (quotientMap g) p).val.1 * c.1) := by
      apply cs.isMinimalCosetRep_iff.mpr
      intro k hk
      have hr : cs.geometricRepresentation c.1 (Finsupp.single k (1 : Real)) ∈
          (fun i : S => Finsupp.single i (1 : Real)) '' p.val.2 :=
        hroots ▸ ⟨Finsupp.single k 1, ⟨k, hk, rfl⟩, rfl⟩
      obtain ⟨i, hi, heq⟩ := hr
      have hpos : 0 < cs.geometricRepresentation (action (quotientMap g) p).val.1
          (Finsupp.single i (1 : Real)) :=
        (cs.geometricRepresentation_single_pos_iff _ i).mpr
          (cs.isMinimalCosetRep_iff.mp hymin i hi)
      apply (cs.geometricRepresentation_single_pos_iff _ k).mp
      simpa only [map_mul, mul_apply_eq_comp, ← heq] using hpos
    have hw : c.1⁻¹ * u * c.1 ∈ cs.parabolic c.2.1 := by
      rw [← hconj, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hu
      exact hu
    have htK : t ∈ cs.parabolic c.2.1 := by simpa only [hq2] using ht
    have hdiff : ((action (quotientMap g) p).val.1 * c.1)⁻¹ *
        (action (quotientMap g) q).val.1 ∈ cs.parabolic c.2.1 := by
      have hmem := (cs.parabolic c.2.1).mul_mem ((cs.parabolic c.2.1).inv_mem hw) htK
      convert hmem using 1; rw [hy, hz, hq1]; group
    have hzminK : cs.IsMinimalCosetRep c.2.1 (action (quotientMap g) q).val.1 := by
      simpa only [hq2] using hzmin
    have heq : (action (quotientMap g) p).val.1 * c.1 =
        (action (quotientMap g) q).val.1 :=
      CoxeterSystem.IsMinimalCosetRep.eq_of_inv_mul_mem cs hmin hzminK hdiff
    change ((action (quotientMap g) p).val.1 * c.1, c.2.1) = (action (quotientMap g) q).val
    exact Prod.ext heq (hz2.trans hq2).symm
  obtain ⟨action, hrep, horbit, hfree⟩ := checkedAlgebra
  have hcov : ∀ n p, Set.image (ArtinNormalisers.Theorem18.quotientRepresentation M J n) (region p) = region (action n p) :=
    checkedRegionCovariance action hrep
  refine ⟨action, hrep, horbit, hfree, hcov, ?_, ?_⟩
  · exact quotientAdjacencyFromCovariance region action hcov
  · exact nca_crossing_equivariance action hrep adjacent
)
