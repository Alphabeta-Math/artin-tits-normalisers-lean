import Mathlib
import ArtinDeligne
import Proofs.BrinkHowlettGroupoid
import Proofs.UniversalWallGroupoid
import Proofs.UniversalGenerators
import Proofs.ChamberMorphismCorrespondence
import Proofs.NormaliserChamberAction

set_option maxHeartbeats 2000000

theorem UniversalBrinkHowlettCover : (∀ {S : Type*} (M : CoxeterMatrix S) (J : Set S),
  let W := CoxeterMatrix.Group M
  let cs := CoxeterMatrix.toCoxeterSystem M
  let Obj := { I : Set S // ∃ g : W,
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g))
      (CoxeterSystem.parabolic cs I) = CoxeterSystem.parabolic cs J }
  let Label := { p : W × Set S //
    Set.image (fun u : W => u * p.1) (CoxeterSystem.parabolic cs J : Set W) =
      Set.image (fun u : W => p.1 * u) (CoxeterSystem.parabolic cs p.2 : Set W) ∧
    CoxeterSystem.IsMinimalCosetRep cs p.2 p.1 }
  letI : CategoryTheory.Groupoid Obj := BrinkHowlettGroupoid cs J
  letI : CategoryTheory.Groupoid Label := UniversalWallGroupoid cs J
  let N := ArtinNormalisers.Artin.coxeterNormalizerQuotient M J
  let Norm := ArtinNormalisers.Theorem18.CoxeterNormalizer M J
  let quotientMap : Norm → N := QuotientGroup.mk'
    ((ArtinNormalisers.Artin.coxeterParabolic M J).subgroupOf Norm)
  Nonempty Label ∧
  (∀ A B : Label, Nonempty ((UniversalWallGroupoid cs J).Hom A B)) ∧
  (∀ A : Label, Subsingleton ((UniversalWallGroupoid cs J).Hom A A)) ∧
  ∃ F : CategoryTheory.Functor Label Obj,
    (∀ A : Label, (F.obj A).val = A.val.2) ∧
    (∀ (A B : Label) (f : (UniversalWallGroupoid cs J).Hom A B),
      (F.map f).val = f.val) ∧
    ArtinNormalisers.Chamber3.IsCoveringFunctor F ∧
    Function.Surjective F.obj ∧
    ∃ deck : Subgroup (Equiv.Perm Label),
      (∀ σ : Equiv.Perm Label, σ ∈ deck ↔
        (∀ A : Label, (σ A).val.2 = A.val.2) ∧
        (∀ A B : Label,
          (σ A).val.1⁻¹ * (σ B).val.1 = A.val.1⁻¹ * B.val.1)) ∧
      ∃ e : MulEquiv N deck,
        (∀ (n : N) (A : Label), (e n).val A = A → n = 1) ∧
        (∀ (g : Norm) (A : Label), ∃ u : W,
          u ∈ CoxeterSystem.parabolic cs A.val.2 ∧
          ((e (quotientMap g)).val A).val.1 = g.val * A.val.1 * u) ∧
        (∀ A B : Label,
          F.obj A = F.obj B ↔ ∃ n : N, (e n).val A = B) ∧
        (let UpstairsArrow := Σ A : Label, Σ B : Label,
            (UniversalWallGroupoid cs J).Hom A B
         let BaseArrow := Σ I : Obj, Σ K : Obj,
            (BrinkHowlettGroupoid cs J).Hom I K
         let arrowMap : UpstairsArrow → BaseArrow := fun p =>
            ⟨F.obj p.1, F.obj p.2.1, F.map p.2.2⟩
         Function.Surjective arrowMap ∧
         ∀ p q : UpstairsArrow,
           arrowMap p = arrowMap q ↔ ∃ n : N,
             (e n).val p.1 = q.1 ∧ (e n).val p.2.1 = q.2.1) ∧
        (∀ finiteRank : Finite S,
          letI : Finite S := finiteRank
          let Θ := ArtinNormalisers.Theorem18.relativeSubspace J
          letI : TopologicalSpace Θ := TopologicalSpace.induced
            (fun f : Θ => ArtinNormalisers.Theorem18.dualCoordinates f.val)
            (inferInstance : TopologicalSpace (S → Real))
          let data := RelativeCone M J
          let coneInterior : Set Θ := data.2.1
          let arrangement : Set (Submodule Real Θ) := data.2.2.2.2.2
          let complement : Set Θ := { f | f ∈ coneInterior ∧
            ∀ H : Submodule Real Θ, H ∈ arrangement → f ∉ (H : Set Θ) }
          let Chamber := { C : Set Θ // ∃ f : Θ,
            f ∈ complement ∧ C = connectedComponentIn complement f }
          let face : Set S → Set (ArtinNormalisers.Theorem18.Dual S) := fun I =>
            { f | f ∈ ArtinNormalisers.Theorem18.relativeSubspace I ∧
              ∀ i : S, i ∉ I → 0 < ArtinNormalisers.Theorem18.dualCoordinates f i }
          let region : Label → Set Θ := fun A =>
            { f | ∃ g : ArtinNormalisers.Theorem18.Dual S,
              g ∈ face A.val.2 ∧ ArtinNormalisers.Theorem18.dualAction M A.val.1 g = f.val }
          let affineDimension : Set Θ → Nat := fun C =>
            Module.finrank Real (AffineSubspace.direction (affineSpan Real C))
          let wall : Set Θ → Set Θ → Prop := fun C H =>
            Set.Nonempty H ∧ ∃ P : Submodule Real Θ, P ∈ arrangement ∧
              H = closure C ∩ (P : Set Θ) ∧ affineDimension H + 1 = affineDimension C
          let adjacent : Label → Label → Prop := fun A B =>
            region A ≠ region B ∧ ∃ H : Set Θ, wall (region A) H ∧ wall (region B) H
          let component : Set S → S → Set S := fun I a =>
            { b | b ∈ Set.insert a I ∧ Relation.ReflTransGen
              (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧
                i ≠ j ∧ M i j ≠ 2) a b }
          let Step := { p : Label × S // p.2 ∉ p.1.val.2 ∧
            Finite (CoxeterSystem.parabolic cs (component p.1.val.2 p.2)) }
          let crossing := fun s : Step =>
            SimpleWallCrossings S W M cs s.val.1.val.2 s.val.2 s.property.1 s.property.2
          (∃ c : Equiv Label Chamber, ∀ A : Label, (c A).val = region A) ∧
          (∀ (n : N) (A : Label),
            Set.image (ArtinNormalisers.Theorem18.quotientRepresentation M J n) (region A) =
              region ((e n).val A)) ∧
          (∀ A B : Label, adjacent A B ↔
            ∃ s : Step, s.val.1 = A ∧ (crossing s).2.2 A.val.1 = B.val) ∧
          (∀ (A B : Label) (s : Step), s.val.1 = A →
            (crossing s).2.2 A.val.1 = B.val →
            ∀ f : (UniversalWallGroupoid cs J).Hom A B,
              (F.map f).val = (crossing s).1) ∧
          (∀ (A B : Label) (f : (UniversalWallGroupoid cs J).Hom A B),
            ∃ es : List Step,
              List.foldr
                (fun s tail P => P = s.val.1.val ∧
                  tail ((crossing s).2.2 s.val.1.val.1))
                (fun P => P = B.val) es A.val ∧
              List.prod (List.map (fun s => (crossing s).1) es) = f.val ∧
              List.prod (List.map (fun s => (crossing s).1) es) = (F.map f).val) ∧
          (∀ (I K : Obj) (w : (BrinkHowlettGroupoid cs J).Hom I K),
            ∃ (A B : Label) (es : List Step),
              F.obj A = I ∧ F.obj B = K ∧
              List.foldr
                (fun s tail P => P = s.val.1.val ∧
                  tail ((crossing s).2.2 s.val.1.val.1))
                (fun P => P = B.val) es A.val ∧
              List.prod (List.map (fun s => (crossing s).1) es) = w.val))) :=
(by
  /- Theorem 1.3 / 4.7, printed pp.2,16--17:
     https://arxiv.org/pdf/2509.21915#page=16
     https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-thm-universal-brink-howlett-cover-artin-tits-normalisers
     This expression integrates the saved proof-main-4d3444e5 baseline and the
     completed helper reports ef2c3dcd (deck), 11b08d0f (total-arrow fibres),
     b6bd31f2 (both adjacency directions), and 8f490349 (other geometry).
     These are local implementation blocks of this parent theorem, with no
     separate original standalone statements. Every block is proved below.
     Steps 1.1,2.1,3.1,4.1 inspire root transport, lifting and universality;
     steps 2.2,3.2,4.2,5.1 inspire the concrete action and full deck carrier;
     steps 1.2,6.1 inspire the chamber, crossing and generation clauses.
     Departures: the simple-root/minimal-transporter API proves the required
     arbitrary-rank transport directly; the base label (1,J) identifies every
     strict deck permutation, without an abstract quotient-cover theorem or
     a normaliser-splitting premise. Dependent total-arrow fibres are proved
     explicitly, after the same chosen action satisfies all three hypotheses.
     The geometric converse constructs an actual retained-root wall in an
     orthant chart rather than assuming that every crossing has a neighbour.
     Finite rank is used only within the geometric clause, by explicit user
     direction. No finiteness of W or W_J is assumed.

     Literature evidence and disposition, retaining the accepted endpoints:
     https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects#pdf-wall-root-characterisation
     The article, printed p.10 after (3.15), says "Note that va,I can be
     alternatively characterised". For S={a}, I=J=empty and x=1, K=empty
     and v=s_a; alpha_a is in the printed source, but Phi_K^- is empty.
     The report's correction is "Remove this auxiliary characterization
     pending a proved corrected formula; retain the longest-element
     definition (3.14)." Here only the proved longest-element/opposition
     construction is used; that auxiliary inclusion is unused.
     https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects#pdf-adjacency-uniqueness-wording
     The article, printed p.11, Proposition 3.17, says "Then there exists
     a unique" before the subset equality. In type A2 with I=J=K=empty,
     chambers (1,empty),(s_1,empty), both index pairs (1,1),(2,2) satisfy
     I+a=K+a'; only (1,1) describes the specified common wall. The report
     says "State uniqueness for the indices describing the specified common
     wall, then list the subset equality among their properties." We apply
     the supplied specified-wall theorem with its actual wall hypotheses.
     The p.16 left-descent typo and the p.9 ambient-ball counterexample are
     recorded with evidence and dispositions beside the relevant blocks.
     None of these proof issues substitutes a new main endpoint.
  -/
  intro S M J
  classical
  have algebraicCorrespondence : (∀ {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S),
    let c_Obj := { I : Set S // ∃ g : W,
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g))
        (CoxeterSystem.parabolic cs I) = CoxeterSystem.parabolic cs J }
    let label : W → Set S → Prop := fun x I =>
      Set.image (fun u : W => u * x) (CoxeterSystem.parabolic cs J : Set W) =
        Set.image (fun u : W => x * u) (CoxeterSystem.parabolic cs I : Set W) ∧
      CoxeterSystem.IsMinimalCosetRep cs I x
    (∀ (I K : c_Obj) (x y : W), label x I.val → label y K.val →
      ∃ f : (BrinkHowlettGroupoid cs J).Hom I K, f.val = x⁻¹ * y) ∧
    (∀ (I K : c_Obj) (w : (BrinkHowlettGroupoid cs J).Hom I K)
      (x : W) (hx : label x I.val),
      ∃ htarget : label (x * w.val) K.val,
        ∃! f : (UniversalWallGroupoid cs J).Hom
          ⟨(x, I.val), hx⟩ ⟨(x * w.val, K.val), htarget⟩,
          f.val = w.val)) :=
  (by
    /- Proposition 4.6, printed p.16; Alphabeta numbered proof:
       https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-prop-chambers-morphisms-artin-tits-normalisers
       The local algebra blocks below reuse the completed implementation in
       theorems13-14/Proofs/FiniteWallPaths.lean, lines 2292-2443, read-only.
       They are implementation lemmas, not additional standalone article results.
       This local implementation lemma has arbitrary rank. The accepted main endpoint is unchanged. No geometric or finite-rank theorem is used here. -/
    intro S W groupW M cs J
    classical
    let root : S → (S →₀ ℝ) := fun i => Finsupp.single i 1
    let piRoots : Set S → Set (S →₀ ℝ) := fun L => root '' L
    let label : W → Set S → Prop := fun x I =>
      (fun u : W => u * x) '' (cs.parabolic J : Set W) =
        (fun u : W => x * u) '' (cs.parabolic I : Set W) ∧
      cs.IsMinimalCosetRep I x
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
    /- Portal Proposition 4.6 step 1.1 uses the simple-root transport of each label.
       Reuse the completed FiniteWallPaths implementation: minimal parabolic
       transporters conjugate simple generators; root positivity selects the
       positive simple root. All imported hypotheses are explicit below. -/
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
    · -- Portal step 1.1: apply the inverse action to the two root-set equalities.
      intro I K x y hx hy
      have hp := label_roots x I.val hx
      have hq := label_roots y K.val hy
      have hi : cs.geometricRepresentation x⁻¹ '' piRoots J = piRoots I.val := by
        rw [← hp, Set.image_image]
        simp only [Representation.inv_self_apply, Set.image_id']
      refine ⟨⟨x⁻¹ * y, ?_⟩, rfl⟩
      change cs.geometricRepresentation (x⁻¹ * y) '' piRoots K.val = piRoots I.val
      calc
        _ = cs.geometricRepresentation x⁻¹ ''
            (cs.geometricRepresentation y '' piRoots K.val) := by
              simp only [map_mul, mul_apply_eq_comp, Set.image_image]
        _ = _ := by rw [hq, hi]
    · intro I K w x hx
      have hr : cs.geometricRepresentation w.val '' piRoots K.val = piRoots I.val :=
        w.property
      /- Portal step 1.2: reflection equivariance and faithfulness give the
         parabolic conjugacy, then literal coset transport.
         Steps 1.3 and 2.1: the implementation uses the equivalent simple-root
         right-descent criterion directly, avoiding the unnecessary expansion
         of all positive parabolic roots. This is a proof-method departure only.
         Literature: the defect report finding pdf-prop46-left-descent-typo
         (https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects)
         identifies the printed proof's right/left descent typo, replacing
         ℓ(ys_j)<ℓ(y) by ℓ(s_jy)<ℓ(y). It does not refute Proposition 4.6.
         We use the checked minimal-transporter and right-descent APIs instead. -/
      have hc := root_conjugacy cs w.val K.val I.val hr
      have ht : label (x * w.val) K.val :=
        c_literal_label_preserved cs J I.val K.val x w.val hx.1 hx.2 hc hr
      refine ⟨ht, ⟨⟨w.val, ?_⟩, rfl, ?_⟩⟩
      · change w.val = x⁻¹ * (x * w.val)
        simp only [inv_mul_cancel_left]
      · intro f hf
        exact Subtype.ext hf
  )

  have algebraicAction {S : Type _} (M : CoxeterMatrix S) (J : Set S) :
      let W := M.Group
      let cs := M.toCoxeterSystem
      let c_Label := {p : W × Set S //
        (fun u => u * p.1) '' (cs.parabolic J : Set W) =
        (fun u => p.1 * u) '' (cs.parabolic p.2 : Set W) ∧
        cs.IsMinimalCosetRep p.2 p.1}
      let Norm := ArtinNormalisers.Theorem18.CoxeterNormalizer M J
      let N := ArtinNormalisers.Artin.coxeterNormalizerQuotient M J
      let quotientMap : Norm → N := QuotientGroup.mk'
        ((ArtinNormalisers.Artin.coxeterParabolic M J).subgroupOf Norm)
      ∃ action : N →* Equiv.Perm c_Label,
        (∀ (g : Norm) (p : c_Label),
          let y := action (quotientMap g) p
          y.val.2 = p.val.2 ∧ cs.IsMinimalCosetRep p.val.2 y.val.1 ∧
          ∃ u : W, u ∈ cs.parabolic p.val.2 ∧ y.val.1 = g.val * p.val.1 * u) ∧
        (∀ p q : c_Label, (∃ g : N, action g p = q) ↔ p.val.2 = q.val.2) ∧
        (∀ (g : N) (p : c_Label), action g p = p → g = 1) := by
    classical
    let W := M.Group
    let cs := M.toCoxeterSystem
    let c_Label := {p : W × Set S //
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

    let A : Norm →* Equiv.Perm c_Label := by
      have htrans (g : Norm) (p : c_Label) :
          (cs.parabolic p.val.2).map (MulAut.conj (g.val * p.val.1)).toMonoidHom =
            cs.parabolic J := by
        rw [conj_product, (coset_iff_conj _ _ _).mp p.property.1]
        rw [MulEquiv.toMonoidHom_eq_coe]
        simpa only [ArtinNormalisers.Artin.coxeterParabolic_eq] using
          Subgroup.mem_normalizer_iff_map_conj_eq.mp g.property
      let act : Norm → c_Label → c_Label := fun g p =>
        ⟨(cs.minimalCosetRep p.val.2 (g.val * p.val.1), p.val.2),
          (coset_iff_conj _ _ _).mpr
            (ArtinNormalisers.Chamber3.minimalCosetRep_transports_parabolic cs (htrans g p)),
          cs.isMinimalCosetRep_minimalCosetRep _ _⟩
      have act_spec (g : Norm) (p : c_Label) :
          ∃ u, u ∈ cs.parabolic p.val.2 ∧ (act g p).val.1 = g.val * p.val.1 * u := by
        refine ⟨(g.val * p.val.1)⁻¹ * (act g p).val.1,
          cs.inv_mul_minimalCosetRep_mem _ _, ?_⟩
        group
      have act_one (p : c_Label) : act 1 p = p := by
        apply Subtype.ext
        refine Prod.ext ?_ rfl
        apply CoxeterSystem.IsMinimalCosetRep.eq_of_inv_mul_mem cs
          (cs.isMinimalCosetRep_minimalCosetRep _ _) p.property.2
        obtain ⟨u, hu, he⟩ := act_spec 1 p
        change (act 1 p).val.1⁻¹ * p.val.1 ∈ _
        rw [he]
        simpa only [Subgroup.coe_one, one_mul, mul_inv_rev, mul_assoc,
          inv_mul_cancel_left, inv_mul_cancel, mul_one] using (cs.parabolic p.val.2).inv_mem hu
      have act_mul (g h : Norm) (p : c_Label) : act (g * h) p = act g (act h p) := by
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

    have A_snd (g : Norm) (p : c_Label) : (A g p).val.2 = p.val.2 := rfl
    have A_min (g : Norm) (p : c_Label) : cs.IsMinimalCosetRep p.val.2 (A g p).val.1 :=
      cs.isMinimalCosetRep_minimalCosetRep _ _
    have A_spec (g : Norm) (p : c_Label) :
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
    let action : N →* Equiv.Perm c_Label := QuotientGroup.lift H A parabolic_kernel
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
        exact (A_snd g p).symm.trans (congrArg (fun z : c_Label => z.val.2) hg)
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
      have hf : (A g p).val.1 = p.val.1 := congrArg (fun z : c_Label => z.val.1) hg
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

  have coset_iff_conj {W : Type _} [Group W] (P Q : Subgroup W) (x : W) :
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

  have root_conjugacy {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (g : W) (L F : Set S)
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

  let c_Obj {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) :=
    {I : Set S // ∃ g : W, (cs.parabolic I).map (MulAut.conj g).toMonoidHom = cs.parabolic J}

  let c_Label {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) :=
    {p : W × Set S // (fun u : W => u * p.1) '' (cs.parabolic J : Set W) =
      (fun u : W => p.1 * u) '' (cs.parabolic p.2 : Set W) ∧ cs.IsMinimalCosetRep p.2 p.1}

  have label_root_iff {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) (x : W) (I : Set S) :
      ((fun u : W => u * x) '' (cs.parabolic J : Set W) =
        (fun u : W => x * u) '' (cs.parabolic I : Set W) ∧
        cs.IsMinimalCosetRep I x) ↔
      cs.geometricRepresentation x '' ((fun i : S => Finsupp.single i (1 : Real)) '' I) =
        (fun i : S => Finsupp.single i (1 : Real)) '' J := by
    constructor
    · intro hx
      let A : c_Obj cs J := ⟨J, 1, by
        ext u
        rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
        simp⟩
      let B : c_Obj cs J := ⟨I, x, (coset_iff_conj _ _ _).mp hx.1⟩
      have hone : (fun u : W => u * 1) '' (cs.parabolic J : Set W) =
          (fun u : W => 1 * u) '' (cs.parabolic J : Set W) ∧
          cs.IsMinimalCosetRep J 1 := ⟨by simp, cs.isMinimalCosetRep_one J⟩
      obtain ⟨w, hw⟩ := (algebraicCorrespondence cs J).1 A B 1 x hone hx
      have hr := w.property
      rw [hw] at hr
      simpa only [inv_one, one_mul] using hr
    · intro hr
      refine ⟨(coset_iff_conj _ _ _).mpr (root_conjugacy cs x I J hr), ?_⟩
      apply cs.isMinimalCosetRep_iff.mpr
      intro i hi
      have hm : cs.geometricRepresentation x (Finsupp.single i (1 : Real)) ∈
          (fun j : S => Finsupp.single j (1 : Real)) '' J :=
        hr ▸ ⟨Finsupp.single i 1, ⟨i, hi, rfl⟩, rfl⟩
      obtain ⟨j, _, hj⟩ := hm
      apply (cs.geometricRepresentation_single_pos_iff x i).mp
      rw [← hj]
      exact lt_of_le_of_ne (Finsupp.single_nonneg.mpr zero_le_one) (by
        intro h
        have hh := congrArg (fun v : S →₀ Real => v j) h
        norm_num at hh)

  /- Local implementation of Theorem 4.7, printed pp.16–17 (Theorem 1.3, p.2).
  No standalone article statement is attributed to this helper.
  https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-thm-universal-brink-howlett-cover-artin-tits-normalisers
  Portal steps 1.1, 2.2 and 3.2 inspire simple-system transport and the
  quotient action. Step 5.1 inspires identification of the full deck group.
  Departure: instead of using the abstract quotient-cover theorem or a
  normaliser splitting, prove the full carrier by the base label (1,J),
  minimal-coset uniqueness and the already constructed concrete action.
  All statements in this block have arbitrary rank and Coxeter type. -/
  have strictDeck {S : Type _} (M : CoxeterMatrix S) (J : Set S) :
      let cs := M.toCoxeterSystem
      let L := c_Label cs J
      let N := ArtinNormalisers.Artin.coxeterNormalizerQuotient M J
      let Norm := ArtinNormalisers.Theorem18.CoxeterNormalizer M J
      let quotientMap : Norm → N := QuotientGroup.mk'
        ((ArtinNormalisers.Artin.coxeterParabolic M J).subgroupOf Norm)
      let a := Classical.choose (algebraicAction M J)
      (∀ (n : N) (A : L), (a n A).val.2 = A.val.2) ∧
      (∀ (n : N) (A B : L),
        (a n A).val.1⁻¹ * (a n B).val.1 = A.val.1⁻¹ * B.val.1) ∧
      ∃ deck : Subgroup (Equiv.Perm L),
        (∀ σ : Equiv.Perm L, σ ∈ deck ↔
          (∀ A : L, (σ A).val.2 = A.val.2) ∧
          (∀ A B : L, (σ A).val.1⁻¹ * (σ B).val.1 = A.val.1⁻¹ * B.val.1)) ∧
        ∃ e : N ≃* deck,
          (∀ n : N, (e n).val = a n) ∧
          (∀ (n : N) (A : L), (e n).val A = A → n = 1) ∧
          (∀ (g : Norm) (A : L), ∃ u : M.Group,
            u ∈ cs.parabolic A.val.2 ∧
            ((e (quotientMap g)).val A).val.1 = g.val * A.val.1 * u) ∧
          (∀ A B : L, A.val.2 = B.val.2 ↔ ∃ n : N, (e n).val A = B) := by
    classical
    let W := M.Group
    let cs := M.toCoxeterSystem
    let L := c_Label cs J
    let N := ArtinNormalisers.Artin.coxeterNormalizerQuotient M J
    let Norm := ArtinNormalisers.Theorem18.CoxeterNormalizer M J
    let H := (ArtinNormalisers.Artin.coxeterParabolic M J).subgroupOf Norm
    let quotientMap : Norm → N := QuotientGroup.mk' H
    let a := Classical.choose (algebraicAction M J)
    have ha := Classical.choose_spec (algebraicAction M J)
    let A0 : L := ⟨(1, J), by simp, cs.isMinimalCosetRep_one J⟩
    have snd (n : N) (A : L) : (a n A).val.2 = A.val.2 := by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H n
      exact (ha.1 g A).1
    -- Portal 1.1 and 2.2: positive simple-system transport composes literally.
    have left_label (d : W) (hd : c_Label cs J) (hcoord : hd.val = (d, J))
        (A : L) :
        (fun u : W => u * (d * A.val.1)) '' (cs.parabolic J : Set W) =
          (fun u : W => (d * A.val.1) * u) '' (cs.parabolic A.val.2 : Set W) ∧
          cs.IsMinimalCosetRep A.val.2 (d * A.val.1) := by
      apply (label_root_iff cs J _ _).mpr
      have hdroot := (label_root_iff cs J hd.val.1 hd.val.2).mp hd.property
      rw [hcoord] at hdroot
      have hAroot := (label_root_iff cs J A.val.1 A.val.2).mp A.property
      calc
        _ = cs.geometricRepresentation d ''
            (cs.geometricRepresentation A.val.1 ''
              ((fun i : S => Finsupp.single i (1 : ℝ)) '' A.val.2)) := by
                simp only [map_mul, mul_apply_eq_comp, Set.image_image]
        _ = _ := by rw [hAroot]; exact hdroot
    have left_formula (n : N) (A : L) :
        (a n A).val.1 = (a n A0).val.1 * A.val.1 := by
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective H n
      let d := (a (quotientMap g) A0).val.1
      have hlabel := left_label d (a (quotientMap g) A0)
        (Prod.ext rfl (snd _ A0)) A
      obtain ⟨u, hu, he⟩ := (ha.1 g A0).2.2
      obtain ⟨v, hv, hf⟩ := (ha.1 g A).2.2
      have huJ : u ∈ cs.parabolic J := hu
      have hm : u * A.val.1 ∈
          (fun t : W => A.val.1 * t) '' (cs.parabolic A.val.2 : Set W) :=
        A.property.1 ▸ Set.mem_image_of_mem (fun t : W => t * A.val.1) huJ
      obtain ⟨t, ht, hte⟩ := hm
      apply CoxeterSystem.IsMinimalCosetRep.eq_of_inv_mul_mem cs (ha.1 g A).2.1 hlabel.2
      change (a (quotientMap g) A).val.1⁻¹ * (d * A.val.1) ∈ _
      rw [hf]
      have hd : d = g.val * u := by
        change d = g.val * 1 * u at he
        simpa only [mul_one] using he
      rw [hd]
      have heq : (g.val * A.val.1 * v)⁻¹ * ((g.val * u) * A.val.1) = v⁻¹ * t := by
        change A.val.1 * t = u * A.val.1 at hte
        calc
          _ = (g.val * A.val.1 * v)⁻¹ * (g.val * (u * A.val.1)) := by group
          _ = (g.val * A.val.1 * v)⁻¹ * (g.val * (A.val.1 * t)) := by rw [hte]
          _ = _ := by group
      rw [heq]
      exact (cs.parabolic A.val.2).mul_mem ((cs.parabolic A.val.2).inv_mem hv) ht
    have disp (n : N) (A B : L) :
        (a n A).val.1⁻¹ * (a n B).val.1 = A.val.1⁻¹ * B.val.1 := by
      rw [left_formula n A, left_formula n B]
      group
    -- Portal 5.1: a strict deck permutation is determined by its value at A0.
    have full (σ : Equiv.Perm L)
        (hs : ∀ A : L, (σ A).val.2 = A.val.2)
        (hd : ∀ A B : L, (σ A).val.1⁻¹ * (σ B).val.1 = A.val.1⁻¹ * B.val.1) :
        ∃ n : N, a n = σ := by
      let d := (σ A0).val.1
      have hc := (coset_iff_conj _ _ _).mp (σ A0).property.1
      rw [hs A0] at hc
      let g : Norm := ⟨d, by
        apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        simpa only [ArtinNormalisers.Artin.coxeterParabolic_eq,
          ← MulEquiv.toMonoidHom_eq_coe] using hc⟩
      have hbase : a (quotientMap g) A0 = σ A0 := by
        apply Subtype.ext
        refine Prod.ext ?_ ((snd _ A0).trans (hs A0).symm)
        apply CoxeterSystem.IsMinimalCosetRep.eq_of_inv_mul_mem cs (ha.1 g A0).2.1
          (by simpa only [hs A0] using (σ A0).property.2)
        obtain ⟨u, hu, he⟩ := (ha.1 g A0).2.2
        rw [he]
        change (d * 1 * u)⁻¹ * d ∈ cs.parabolic J
        simpa only [mul_one, mul_inv_rev, mul_assoc, inv_mul_cancel_left,
          inv_mul_cancel, mul_one] using (cs.parabolic J).inv_mem hu
      refine ⟨quotientMap g, ?_⟩
      apply Equiv.ext
      intro A
      apply Subtype.ext
      refine Prod.ext ?_ ((snd _ A).trans (hs A).symm)
      rw [left_formula, congrArg (fun z : L => z.val.1) hbase]
      have ht := hd A0 A
      change d⁻¹ * (σ A).val.1 = 1⁻¹ * A.val.1 at ht
      calc
        d * A.val.1 = d * (d⁻¹ * (σ A).val.1) := by simpa only [inv_one, one_mul] using congrArg (fun z : W => d * z) ht.symm
        _ = _ := by group
    let deck : Subgroup (Equiv.Perm L) := a.range
    have carrier (σ : Equiv.Perm L) : σ ∈ deck ↔
        (∀ A : L, (σ A).val.2 = A.val.2) ∧
        (∀ A B : L, (σ A).val.1⁻¹ * (σ B).val.1 = A.val.1⁻¹ * B.val.1) := by
      constructor
      · rintro ⟨n, rfl⟩
        exact ⟨snd n, disp n⟩
      · rintro ⟨hs, hd⟩
        exact full σ hs hd
    have inj : Function.Injective a := by
      intro n m h
      have hfix : a (m⁻¹ * n) A0 = A0 := by
        rw [map_mul, map_inv, h]
        exact (a m).symm_apply_apply A0
      have he := ha.2.2 (m⁻¹ * n) A0 hfix
      have : n = m := by
        calc
          n = m * (m⁻¹ * n) := by group
          _ = m := by rw [he, mul_one]
      exact this
    let e : N ≃* deck := MulEquiv.ofBijective a.rangeRestrict
      ⟨fun n m h => inj (congrArg Subtype.val h), a.rangeRestrict_surjective⟩
    have he (n : N) : (e n).val = a n := rfl
    refine ⟨snd, disp, deck, carrier, e, he, ?_, ?_, ?_⟩
    · intro n A hfix
      exact ha.2.2 n A hfix
    · intro g A
      exact (ha.1 g A).2.2
    · intro A B
      exact (ha.2.1 A B).symm

  letI c_labelCat {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) : CategoryTheory.Groupoid (c_Label cs J) := UniversalWallGroupoid cs J
  letI c_objCat {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) : CategoryTheory.Groupoid (c_Obj cs J) := BrinkHowlettGroupoid cs J

  let toObj {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) (A : c_Label cs J) : c_Obj cs J :=
    ⟨A.val.2, A.val.1, (coset_iff_conj _ _ _).mp A.property.1⟩

  /- Local implementation blocks, no standalone article statements.
     Theorem 4.7 printed pp.16–17, portal steps 2.1, 3.1 and 4.1:
     https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-thm-universal-brink-howlett-cover-artin-tits-normalisers
     All data and lifts here have arbitrary rank. The copied algebraic
     correspondence above is proved by root positivity and the existing
     minimal-transporter API, not an assumed Dyer–Gimenez premise. -/
  let projection {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) :
      letI : CategoryTheory.Groupoid (c_Label cs J) := UniversalWallGroupoid cs J
      letI : CategoryTheory.Groupoid (c_Obj cs J) := BrinkHowlettGroupoid cs J
      CategoryTheory.Functor (c_Label cs J) (c_Obj cs J) := by
    letI : CategoryTheory.Groupoid (c_Label cs J) := UniversalWallGroupoid cs J
    letI : CategoryTheory.Groupoid (c_Obj cs J) := BrinkHowlettGroupoid cs J
    exact {
      obj := toObj cs J
      map := fun {A B} f => ⟨f.val, by
        rw [f.property]
        obtain ⟨w, hw⟩ := (algebraicCorrespondence cs J).1
          (toObj cs J A) (toObj cs J B) A.val.1 B.val.1 A.property B.property
        exact hw ▸ w.property⟩
      map_id := fun A => Subtype.ext rfl
      map_comp := fun f g => Subtype.ext rfl }

  have projection_obj_val {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) (A : c_Label cs J) :
      ((projection cs J).obj A).val = A.val.2 := rfl

  have projection_map_val {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S)
      (A B : c_Label cs J) (f : (UniversalWallGroupoid cs J).Hom A B) :
      ((projection cs J).map f).val = f.val := rfl

  have projection_surjective {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) :
      Function.Surjective (projection cs J).obj := by
    intro I
    obtain ⟨g, hg⟩ := I.property
    let x := cs.minimalCosetRep I.val g
    have hx : (fun u : W => u * x) '' (cs.parabolic J : Set W) =
        (fun u : W => x * u) '' (cs.parabolic I.val : Set W) ∧
        cs.IsMinimalCosetRep I.val x :=
      ⟨(coset_iff_conj _ _ _).mpr
        (ArtinNormalisers.Chamber3.minimalCosetRep_transports_parabolic cs hg),
        cs.isMinimalCosetRep_minimalCosetRep _ _⟩
    exact ⟨⟨(x, I.val), hx⟩, Subtype.ext rfl⟩

  have projection_covering {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) :
      ArtinNormalisers.Chamber3.IsCoveringFunctor (projection cs J) := by
    intro A
    constructor
    · intro p q h
      have htype : p.1.val.2 = q.1.val.2 :=
        congrArg (fun t => t.1.val) h
      have hval : p.2.val = q.2.val :=
        congrArg (fun t => t.2.val) h
      have hcoord : p.1.val.1 = q.1.val.1 := by
        have hw := hval
        rw [p.2.property, q.2.property] at hw
        exact mul_left_cancel hw
      have ht : p.1 = q.1 := Subtype.ext (Prod.ext hcoord htype)
      rcases p with ⟨P, p⟩
      rcases q with ⟨Q, q⟩
      dsimp only at ht
      subst Q
      have hf : p = q := Subtype.ext hval
      cases hf
      rfl
    · rintro ⟨K, w⟩
      obtain ⟨htarget, _, _, _⟩ := (algebraicCorrespondence cs J).2
        (toObj cs J A) K w A.val.1 A.property
      let B : c_Label cs J := ⟨(A.val.1 * w.val, K.val), htarget⟩
      refine ⟨⟨B, ⟨w.val, ?_⟩⟩, ?_⟩
      · change w.val = A.val.1⁻¹ * (A.val.1 * w.val)
        simp only [inv_mul_cancel_left]
      · rfl

  have upstairs_nonempty {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) :
      Nonempty (c_Label cs J) := by
    refine ⟨⟨(1, J), ?_, cs.isMinimalCosetRep_one J⟩⟩
    simp

  have upstairs_connected {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S)
      (A B : c_Label cs J) : Nonempty ((UniversalWallGroupoid cs J).Hom A B) :=
    ⟨⟨A.val.1⁻¹ * B.val.1, rfl⟩⟩

  have upstairs_thin {S W : Type _} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S)
      (A B : c_Label cs J) : Subsingleton ((UniversalWallGroupoid cs J).Hom A B) :=
    ⟨fun f g => Subtype.ext (f.property.trans g.property.symm)⟩

  have checkedGeometricAdjacency : (∀ {S : Type _} [Finite S] (M : CoxeterMatrix S) (J : Set S),
    let W := CoxeterMatrix.Group M
    let cs := CoxeterMatrix.toCoxeterSystem M
    let Θ := ArtinNormalisers.Theorem18.relativeSubspace J
    letI : TopologicalSpace Θ := TopologicalSpace.induced
      (fun f : Θ => ArtinNormalisers.Theorem18.dualCoordinates f.val)
      (inferInstance : TopologicalSpace (S → Real))
    let arrangement : Set (Submodule Real Θ) := (RelativeCone M J).2.2.2.2.2
    let Label := {p : W × Set S //
      Set.image (fun u : W => u * p.1) (CoxeterSystem.parabolic cs J : Set W) =
        Set.image (fun u : W => p.1 * u) (CoxeterSystem.parabolic cs p.2 : Set W) ∧
      CoxeterSystem.IsMinimalCosetRep cs p.2 p.1 }
    let face : Set S → Set (ArtinNormalisers.Theorem18.Dual S) := fun I =>
      { f | f ∈ ArtinNormalisers.Theorem18.relativeSubspace I ∧
        ∀ i : S, i ∉ I → 0 < ArtinNormalisers.Theorem18.dualCoordinates f i }
    let region : Label → Set Θ := fun A =>
      { f | ∃ g : ArtinNormalisers.Theorem18.Dual S,
        g ∈ face A.val.2 ∧ ArtinNormalisers.Theorem18.dualAction M A.val.1 g = f.val }
    let affineDimension : Set Θ → Nat := fun A =>
      Module.finrank Real (AffineSubspace.direction (affineSpan Real A))
    let wall : Set Θ → Set Θ → Prop := fun C F =>
      Set.Nonempty F ∧ ∃ H : Submodule Real Θ, H ∈ arrangement ∧
        F = closure C ∩ (H : Set Θ) ∧ affineDimension F + 1 = affineDimension C
    let component : Set S → S → Set S := fun I a =>
      { b | b ∈ Set.insert a I ∧ Relation.ReflTransGen
        (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b }
    let adjacent : Label → Label → Prop := fun A B =>
      region A ≠ region B ∧ ∃ H : Set Θ, wall (region A) H ∧ wall (region B) H
    let Step := { p : Label × S // p.2 ∉ p.1.val.2 ∧
      Finite (CoxeterSystem.parabolic cs (component p.1.val.2 p.2)) }
    let crossing := fun s : Step =>
      SimpleWallCrossings S W M cs s.val.1.val.2 s.val.2 s.property.1 s.property.2
    ∀ A B : Label, adjacent A B ↔
      ∃ s : Step, s.val.1 = A ∧ (crossing s).2.2 A.val.1 = B.val) :=
  by
    intro S inst M J
    have exactAdjacency : (  let W := CoxeterMatrix.Group M
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
        ((region x I ≠ region y K ∧ ∃ F : Set Θ, wall (region x I) F ∧ wall (region y K) F) ↔
          ∃ (a : S) (ha : a ∉ I) (hD : Finite (cs.parabolic (component I a))),
            (SimpleWallCrossings S W M cs I a ha hD).2.2 x = (y, K))) :=
    open Set ArtinNormalisers.Artin ArtinNormalisers.Landmark1 ArtinNormalisers.Theorem18 ArtinNormalisers.Chamber3 CoxeterSystem in
    by
      classical
      /- Reuse of completed internal proof bodies, read-only:
         theorems13-14/Proofs/AdjacentWallFormula.lean, orthant blocks lines 88–197,
         flat-coordinate blocks lines 244–358, actual-choice/crossing blocks
         lines 545–1040. These are local implementation lemmas, not external
         declarations at the historical source revision.
         Numbered inspiration: component-opposition steps 1.1,1.2,2.1 and
         component-crossing-label steps 1.1,2.1,3.1:
         https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-author-4ac39e6f1702-component-opposition
         https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-author-4ac39e6f1702-component-crossing-label
         Parent: Proposition 3.17 and (3.14)–(3.15), printed pp.10–11.
         The specified-wall uniqueness correction is retained in the supplied
         AdjacentWallFormula; no equality-only uniqueness is asserted here. -/
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
      /- Local converse implementation, no standalone article statement.
         Parent: Theorems 1.3/4.7, pp.2,16–17, and Proposition 3.17,
         equations (3.14)–(3.15), pp.10–11, https://arxiv.org/pdf/2509.21915#page=10.
         Inspiration: covering step 1.2 and adjacent-wall steps 1.1,2.1,3.1:
         https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-thm-universal-brink-howlett-cover-artin-tits-normalisers
         https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-prop-adjacent-wall-formula-artin-tits-normalisers
         Additional converse argument: a transported coordinate kernel is an actual
         retained-root hyperplane; orthant charts give its closed trace and dimension.
         The full-flat opposition identity proves distinctness without presupposing
         an adjacent neighbour. The defective auxiliary root inclusion is unused. -/
      have facet_wall {S : Type _} [Finite S] {M : CoxeterMatrix S} {J : Set S}
          (X : RawFacetLabel M J) (a : S) (ha : a ∉ X.indices) :
          let Θ := relativeSubspace J
          let F := closure (r_region M J X.representative (insert a X.indices))
          F.Nonempty ∧ ∃ P : Submodule ℝ Θ, P ∈ (RelativeCone M J).2.2.2.2.2 ∧
            F = closure (r_region M J X.representative X.indices) ∩ (P : Set Θ) ∧
            r_dim F + 1 = r_dim (r_region M J X.representative X.indices) := by
        classical
        let T := {i : S // i ∉ X.indices}
        let aT : T := ⟨a, ha⟩
        let r := M.toCoxeterSystem.geometricRepresentation X.representative (simpleRoot a)
        have hev (q : T → ℝ) : (r_chart X q).val r = q aT := by
          change dualAction M X.representative ((r_coords X.indices).symm q).val
            (M.toCoxeterSystem.geometricRepresentation X.representative (simpleRoot a)) = _
          rw [dualAction_apply, Representation.inv_self_apply]
          exact r_coords_symm_apply X.indices q aT
        have hr : r ∈ M.toCoxeterSystem.geometricRoots := ⟨X.representative, a, rfl⟩
        have hret : r ∈ retainedRoots M J := by
          refine ⟨hr, r_chart X (fun _ => 1), ?_⟩
          rw [hev]
          norm_num
        obtain ⟨r', hr', hp', hker⟩ : ∃ r' : Vector S,
            r' ∈ retainedRoots M J ∧ 0 < r' ∧
            restrictedHyperplane J r' = restrictedHyperplane J r := by
          rcases M.toCoxeterSystem.pos_or_neg_of_mem_geometricRoots hr with hp | hn
          · exact ⟨r, hret, hp, rfl⟩
          · refine ⟨-r, ⟨M.toCoxeterSystem.neg_mem_geometricRoots_iff.mpr hr, ?_⟩,
              neg_pos.mpr hn, ?_⟩
            · refine ⟨r_chart X (fun _ => 1), ?_⟩
              rw [map_neg, hev]
              norm_num
            · ext f
              change f.val (-r) = 0 ↔ f.val r = 0
              rw [map_neg, neg_eq_zero]
        let P := restrictedHyperplane J r'
        have hP : P ∈ (RelativeCone M J).2.2.2.2.2 := ⟨r', ⟨hr', hp'⟩, rfl⟩
        have hface : closure (r_region M J X.representative (insert a X.indices)) =
            r_chart X '' r_cface ({aT} : Set T) := by
          rw [r_insert_region_chart X a ha, ← ContinuousLinearEquiv.image_closure, r_closure_oface]
        refine ⟨?_, P, hP, ?_, ?_⟩
        · rw [hface]
          exact ⟨r_chart X 0, 0, ⟨by intro i hi; rfl, by intro i; exact le_refl 0⟩, rfl⟩
        · rw [hface, r_region_chart, ← ContinuousLinearEquiv.image_closure, r_closure_pos]
          ext f
          constructor
          · rintro ⟨q, hq, rfl⟩
            refine ⟨⟨q, hq.2, rfl⟩, ?_⟩
            change r_chart X q ∈ restrictedHyperplane J r'
            rw [hker]
            exact (hev q).trans (hq.1 aT (by simp))
          · rintro ⟨⟨q, hq, rfl⟩, hqP⟩
            refine ⟨q, ⟨?_, hq⟩, rfl⟩
            intro i hi
            have hi' : i = aT := hi
            subst i
            change r_chart X q ∈ restrictedHyperplane J r' at hqP
            rw [hker] at hqP
            exact (hev q).symm.trans hqP
        · rw [hface, r_region_chart]
          have hd1 : r_dim (r_chart X '' r_cface ({aT} : Set T)) =
              r_dim (r_cface ({aT} : Set T)) := r_dim_image _ _
          have hd2 : r_dim (r_chart X '' r_pos T) = r_dim (r_pos T) := r_dim_image _ _
          rw [hd1, hd2, r_dim_cface, r_dim_pos]
          letI := Fintype.ofFinite T
          letI := Fintype.ofFinite {i : T // i ∉ ({aT} : Set T)}
          have hcard := Fintype.card_subtype_compl (fun i : T => i ∈ ({aT} : Set T))
          have hone : Fintype.card {i : T // i ∈ ({aT} : Set T)} = 1 := by
            simp
          rw [hone] at hcard
          have hle := Fintype.card_subtype_le (fun i : T => i ∈ ({aT} : Set T))
          rw [hone] at hle
          simp only [Nat.card_eq_fintype_card]
          omega
      dsimp only
      have htop : TopologicalSpace.induced
          (fun f : relativeSubspace J => dualCoordinates f.val)
          (inferInstance : TopologicalSpace (S → ℝ)) =
          (inferInstance : TopologicalSpace (relativeSubspace J)) := induced_compose.symm
      rw [htop]
      intro x y I K hx hy
      constructor
      · rintro ⟨hne, F, hFx, hFy⟩
        have hAW := AdjacentWallFormula M J
        dsimp only at hAW
        rw [htop] at hAW
        have h := hAW x y I K hx hy F hne hFx hFy
        obtain ⟨a, b, ha, hb, _, _, _, _, _, _, _, hD, hD', hcross, _⟩ := h
        exact ⟨a, ha, hD, hcross⟩
      · rintro ⟨a, ha, hD, hcross⟩
        let forward := SimpleWallCrossings S M.Group M M.toCoxeterSystem I a ha hD
        have hyval : y = x * forward.1 := (congrArg Prod.fst hcross).symm
        have hKval : K = forward.2.1 := (congrArg Prod.snd hcross).symm
        subst y K
        let L := forward.2.1
        have hlabel := c_actual_label M.toCoxeterSystem J I x a ha hD hx
        have hopen := c_actual_open_enlarged_facets M J I x a ha hD
        let D := c_component (M := M) I a
        let ν := c_selectedOpposition M.toCoxeterSystem I a hD
        let aD : D := ⟨a, Set.mem_insert a I, Relation.ReflTransGen.refl⟩
        let b : S := ν aD
        have hb : b ∉ L := hopen.2.1
        have hL : L = insert a I \ {b} := rfl
        let X : RawFacetLabel M J := ⟨I, x, r_coset_conj M J I x hx.1⟩
        let Y : RawFacetLabel M J := ⟨L, x * forward.1,
          r_coset_conj M J L (x * forward.1) hlabel.1⟩
        have hwallX := facet_wall X a ha
        have hwallY := facet_wall Y b hb
        have hequal : r_region M J (x * forward.1) (insert b L) =
            r_region M J x (insert a I) := hopen.2.2.2
        have hne : r_region M J x I ≠ r_region M J (x * forward.1) L := by
          intro heq
          let q : {i : S // i ∉ L} → ℝ := fun _ => 1
          let f := r_chart Y q
          have hf : f ∈ r_region M J (x * forward.1) L := by
            rw [r_region_chart Y]
            exact ⟨q, fun _ => zero_lt_one, rfl⟩
          have hfX : f ∈ r_region M J x I := heq ▸ hf
          obtain ⟨g, hg, heg⟩ := hfX
          let gY := ((r_coords L).symm q).val
          have hegY : dualAction M (x * forward.1) gY = f.val := rfl
          have hgEq : g = dualAction M forward.1 gY := by
            calc
              g = dualAction M x⁻¹ (dualAction M x g) := (Representation.inv_self_apply _ _ _).symm
              _ = dualAction M x⁻¹ (dualAction M (x * forward.1) gY) :=
                congrArg _ (heg.trans hegY.symm)
              _ = dualAction M forward.1 gY := by
                rw [map_mul, mul_apply_eq_comp, Representation.inv_self_apply]
          have hc := c_actual_certificate M.toCoxeterSystem I a ha hD
          have hop := full_flat_opposite_evaluation M I D aD ha
            (fun _ hi => hi.1)
            (c_selectedLongest M.toCoxeterSystem D hD D (fun _ h => h))
            (c_selectedLongest M.toCoxeterSystem D hD (D \ {a}) Set.sdiff_subset)
            ν hc.2.2.1 hc.2.2.2.2.1
            (c_selectedLongest M.toCoxeterSystem D hD (D \ {a}) Set.sdiff_subset).property
            gY (by change gY ∈ relativeSubspace L; exact ((r_coords L).symm q).property)
          have hgYa : gY (simpleRoot b) = 1 := r_coords_symm_apply L q ⟨b, hb⟩
          have hpos := hg.2 a ha
          change 0 < g (simpleRoot a) at hpos
          change dualAction M forward.1 gY (simpleRoot a) = -gY (simpleRoot b) at hop
          rw [hgEq, hop, hgYa] at hpos
          norm_num at hpos
        refine ⟨hne, closure (r_region M J x (insert a I)), hwallX, ?_⟩
        rw [← hequal]
        exact hwallY
    dsimp only
    intro A B
    have h := exactAdjacency A.val.1 B.val.1 A.val.2 B.val.2 A.property B.property
    constructor
    · intro hab
      obtain ⟨a, ha, hD, he⟩ := h.mp hab
      exact ⟨⟨(A, a), ha, hD⟩, rfl, he⟩
    · rintro ⟨s, hs, he⟩
      apply h.mpr
      subst A
      exact ⟨s.val.2, s.property.1, s.property.2, he⟩

  let W := CoxeterMatrix.Group M
  let cs := CoxeterMatrix.toCoxeterSystem M
  let Obj := { I : Set S // ∃ g : W,
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g))
      (CoxeterSystem.parabolic cs I) = CoxeterSystem.parabolic cs J }
  let Label := { p : W × Set S //
    Set.image (fun u : W => u * p.1) (CoxeterSystem.parabolic cs J : Set W) =
      Set.image (fun u : W => p.1 * u) (CoxeterSystem.parabolic cs p.2 : Set W) ∧
    CoxeterSystem.IsMinimalCosetRep cs p.2 p.1 }
  letI : CategoryTheory.Groupoid Obj := BrinkHowlettGroupoid cs J
  letI : CategoryTheory.Groupoid Label := UniversalWallGroupoid cs J
  let N := ArtinNormalisers.Artin.coxeterNormalizerQuotient M J
  let Norm := ArtinNormalisers.Theorem18.CoxeterNormalizer M J
  let quotientMap : Norm → N := QuotientGroup.mk'
    ((ArtinNormalisers.Artin.coxeterParabolic M J).subgroupOf Norm)
  change Nonempty Label ∧
    (∀ A B : Label, Nonempty ((UniversalWallGroupoid cs J).Hom A B)) ∧
    (∀ A : Label, Subsingleton ((UniversalWallGroupoid cs J).Hom A A)) ∧
    ∃ F : CategoryTheory.Functor Label Obj,
      (∀ A : Label, (F.obj A).val = A.val.2) ∧
      (∀ (A B : Label) (f : (UniversalWallGroupoid cs J).Hom A B),
        (F.map f).val = f.val) ∧
      ArtinNormalisers.Chamber3.IsCoveringFunctor F ∧
      Function.Surjective F.obj ∧
      ∃ deck : Subgroup (Equiv.Perm Label),
        (∀ σ : Equiv.Perm Label, σ ∈ deck ↔
          (∀ A : Label, (σ A).val.2 = A.val.2) ∧
          (∀ A B : Label,
            (σ A).val.1⁻¹ * (σ B).val.1 = A.val.1⁻¹ * B.val.1)) ∧
        ∃ e : MulEquiv N deck,
          (∀ (n : N) (A : Label), (e n).val A = A → n = 1) ∧
          (∀ (g : Norm) (A : Label), ∃ u : W,
            u ∈ CoxeterSystem.parabolic cs A.val.2 ∧
            ((e (quotientMap g)).val A).val.1 = g.val * A.val.1 * u) ∧
          (∀ A B : Label,
            F.obj A = F.obj B ↔ ∃ n : N, (e n).val A = B) ∧
          (let UpstairsArrow := Σ A : Label, Σ B : Label,
              (UniversalWallGroupoid cs J).Hom A B
           let BaseArrow := Σ I : Obj, Σ K : Obj,
              (BrinkHowlettGroupoid cs J).Hom I K
           let arrowMap : UpstairsArrow → BaseArrow := fun p =>
              ⟨F.obj p.1, F.obj p.2.1, F.map p.2.2⟩
           Function.Surjective arrowMap ∧
           ∀ p q : UpstairsArrow,
             arrowMap p = arrowMap q ↔ ∃ n : N,
               (e n).val p.1 = q.1 ∧ (e n).val p.2.1 = q.2.1) ∧
          (∀ finiteRank : Finite S,
            letI : Finite S := finiteRank
            let Θ := ArtinNormalisers.Theorem18.relativeSubspace J
            letI : TopologicalSpace Θ := TopologicalSpace.induced
              (fun f : Θ => ArtinNormalisers.Theorem18.dualCoordinates f.val)
              (inferInstance : TopologicalSpace (S → Real))
            let data := RelativeCone M J
            let coneInterior : Set Θ := data.2.1
            let arrangement : Set (Submodule Real Θ) := data.2.2.2.2.2
            let complement : Set Θ := { f | f ∈ coneInterior ∧
              ∀ H : Submodule Real Θ, H ∈ arrangement → f ∉ (H : Set Θ) }
            let Chamber := { C : Set Θ // ∃ f : Θ,
              f ∈ complement ∧ C = connectedComponentIn complement f }
            let face : Set S → Set (ArtinNormalisers.Theorem18.Dual S) := fun I =>
              { f | f ∈ ArtinNormalisers.Theorem18.relativeSubspace I ∧
                ∀ i : S, i ∉ I → 0 < ArtinNormalisers.Theorem18.dualCoordinates f i }
            let region : Label → Set Θ := fun A =>
              { f | ∃ g : ArtinNormalisers.Theorem18.Dual S,
                g ∈ face A.val.2 ∧ ArtinNormalisers.Theorem18.dualAction M A.val.1 g = f.val }
            let affineDimension : Set Θ → Nat := fun C =>
              Module.finrank Real (AffineSubspace.direction (affineSpan Real C))
            let wall : Set Θ → Set Θ → Prop := fun C H =>
              Set.Nonempty H ∧ ∃ P : Submodule Real Θ, P ∈ arrangement ∧
                H = closure C ∩ (P : Set Θ) ∧ affineDimension H + 1 = affineDimension C
            let adjacent : Label → Label → Prop := fun A B =>
              region A ≠ region B ∧ ∃ H : Set Θ, wall (region A) H ∧ wall (region B) H
            let component : Set S → S → Set S := fun I a =>
              { b | b ∈ Set.insert a I ∧ Relation.ReflTransGen
                (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧
                  i ≠ j ∧ M i j ≠ 2) a b }
            let Step := { p : Label × S // p.2 ∉ p.1.val.2 ∧
              Finite (CoxeterSystem.parabolic cs (component p.1.val.2 p.2)) }
            let crossing := fun s : Step =>
              SimpleWallCrossings S W M cs s.val.1.val.2 s.val.2 s.property.1 s.property.2
            (∃ c : Equiv Label Chamber, ∀ A : Label, (c A).val = region A) ∧
            (∀ (n : N) (A : Label),
              Set.image (ArtinNormalisers.Theorem18.quotientRepresentation M J n) (region A) =
                region ((e n).val A)) ∧
            (∀ A B : Label, adjacent A B ↔
              ∃ s : Step, s.val.1 = A ∧ (crossing s).2.2 A.val.1 = B.val) ∧
            (∀ (A B : Label) (s : Step), s.val.1 = A →
              (crossing s).2.2 A.val.1 = B.val →
              ∀ f : (UniversalWallGroupoid cs J).Hom A B,
                (F.map f).val = (crossing s).1) ∧
            (∀ (A B : Label) (f : (UniversalWallGroupoid cs J).Hom A B),
              ∃ es : List Step,
                List.foldr
                  (fun s tail P => P = s.val.1.val ∧
                    tail ((crossing s).2.2 s.val.1.val.1))
                  (fun P => P = B.val) es A.val ∧
                List.prod (List.map (fun s => (crossing s).1) es) = f.val ∧
                List.prod (List.map (fun s => (crossing s).1) es) = (F.map f).val) ∧
            (∀ (I K : Obj) (w : (BrinkHowlettGroupoid cs J).Hom I K),
              ∃ (A B : Label) (es : List Step),
                F.obj A = I ∧ F.obj B = K ∧
                List.foldr
                  (fun s tail P => P = s.val.1.val ∧
                    tail ((crossing s).2.2 s.val.1.val.1))
                  (fun P => P = B.val) es A.val ∧
                List.prod (List.map (fun s => (crossing s).1) es) = w.val))
  let F := projection cs J
  have hFsurj := projection_surjective cs J
  have hFcover := projection_covering cs J
  let a := Classical.choose (algebraicAction M J)
  obtain ⟨a_snd, a_displacement, deck, hdeck, e, he, hfree, hrep, hfibre⟩ := strictDeck M J
  have quotientFibres
      (a : N →* Equiv.Perm (Label))
      (a_snd : ∀ (n : N) (A : Label), (a n A).val.2 = A.val.2)
      (a_disp : ∀ (n : N) (A B : Label),
        (a n A).val.1⁻¹ * (a n B).val.1 = A.val.1⁻¹ * B.val.1)
      (a_orbit : ∀ A B : Label,
        (∃ n : N, a n A = B) ↔ A.val.2 = B.val.2) :
      (∀ A B : Label,
        F.obj A = F.obj B ↔
          ∃ n : N, a n A = B) ∧
      (let UpstairsArrow := Σ A : Label, Σ B : Label,
          (UniversalWallGroupoid cs J).Hom A B
       let BaseArrow := Σ I : Obj, Σ K : Obj,
          (BrinkHowlettGroupoid cs J).Hom I K
       let arrowMap : UpstairsArrow → BaseArrow := fun p =>
         ⟨F.obj p.1, F.obj p.2.1,
           F.map p.2.2⟩
       Function.Surjective arrowMap ∧
       ∀ p q : UpstairsArrow,
         arrowMap p = arrowMap q ↔
           ∃ n : N, a n p.1 = q.1 ∧ a n p.2.1 = q.2.1) := by
    let UpstairsArrow := Σ A : Label, Σ B : Label,
      (UniversalWallGroupoid cs J).Hom A B
    let BaseArrow := Σ I : Obj, Σ K : Obj,
      (BrinkHowlettGroupoid cs J).Hom I K
    let arrowMap : UpstairsArrow → BaseArrow := fun p =>
      ⟨F.obj p.1, F.obj p.2.1,
        F.map p.2.2⟩
    /- Local implementation of Theorem 4.7 (printed pp.16–17), also Theorem 1.3
       (printed p.2), not an original standalone article statement.
       https://arxiv.org/pdf/2509.21915#page=16
       https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-thm-universal-brink-howlett-cover-artin-tits-normalisers
       Portal steps 3.1 and 4.2 inspire the lifting and quotient-fibre arguments.
       Proof-method detail: total arrows remain dependent Sigma triples. Equality
       is proved by transporting both endpoint equalities before subtype
       extensionality; equality of group labels alone is never substituted for
       equality of total arrows. No rank, sphericality or topology premise. -/
    have baseArrow_ext (p q : BaseArrow)
        (hs : p.1 = q.1) (ht : p.2.1 = q.2.1)
        (hv : p.2.2.val = q.2.2.val) : p = q := by
      rcases p with ⟨I, K, f⟩
      rcases q with ⟨I', K', g⟩
      dsimp only at hs ht hv
      cases hs
      cases ht
      have hf : f = g := Subtype.ext hv
      cases hf
      rfl

    have arrowMap_eq_iff (p q : UpstairsArrow) :
        arrowMap p = arrowMap q ↔
          p.1.val.2 = q.1.val.2 ∧ p.2.1.val.2 = q.2.1.val.2 ∧
          p.1.val.1⁻¹ * p.2.1.val.1 = q.1.val.1⁻¹ * q.2.1.val.1 := by
      constructor
      · intro h
        have hs := congrArg (fun r : BaseArrow => r.1.val) h
        have ht := congrArg (fun r : BaseArrow => r.2.1.val) h
        have hv := congrArg (fun r : BaseArrow => r.2.2.val) h
        change p.2.2.val = q.2.2.val at hv
        rw [p.2.2.property, q.2.2.property] at hv
        exact ⟨hs, ht, hv⟩
      · rintro ⟨hs, ht, hv⟩
        apply baseArrow_ext
        · exact Subtype.ext hs
        · exact Subtype.ext ht
        · change p.2.2.val = q.2.2.val
          rw [p.2.2.property, q.2.2.property]
          exact hv

    /- Portal step 3.1: lift the source object and then the complete outgoing
       arrow. The equality of outgoing Sigma pairs is retained by congrArg. -/
    have arrowMap_surjective : Function.Surjective (arrowMap) := by
      rintro ⟨I, K, w⟩
      obtain ⟨A, rfl⟩ := hFsurj I
      obtain ⟨⟨B, f⟩, hf⟩ := (hFcover A).2 ⟨K, w⟩
      refine ⟨⟨A, B, f⟩, ?_⟩
      exact congrArg (fun r : ArtinNormalisers.Chamber3.Outgoing (Obj)
        (F.obj A) =>
          (⟨F.obj A, r.1, r.2⟩ : BaseArrow)) hf

    constructor
    · intro A B
      constructor
      · intro h
        apply (a_orbit A B).mpr
        exact congrArg (fun I : Obj => I.val) h
      · intro h
        exact Subtype.ext ((a_orbit A B).mp h)
    constructor
    · exact arrowMap_surjective
    · intro p q
      constructor
      · intro h
        obtain ⟨hs, ht, hd⟩ := (arrowMap_eq_iff p q).mp h
        obtain ⟨n, hn⟩ := (a_orbit p.1 q.1).mpr hs
        refine ⟨n, hn, ?_⟩
        apply Subtype.ext
        apply Prod.ext
        · have hh := a_disp n p.1 p.2.1
          rw [hn] at hh
          exact mul_left_cancel (hh.trans hd)
        · exact (a_snd n p.2.1).trans ht
      · rintro ⟨n, hs, ht⟩
        apply (arrowMap_eq_iff p q).mpr
        refine ⟨(a_snd n p.1).symm.trans
          (congrArg (fun A : Label => A.val.2) hs),
          (a_snd n p.2.1).symm.trans
          (congrArg (fun A : Label => A.val.2) ht), ?_⟩
        have hh := a_disp n p.1 p.2.1
        have hsx := congrArg (fun A : Label => A.val.1) hs
        have htx := congrArg (fun A : Label => A.val.1) ht
        rw [hsx, htx] at hh
        exact hh.symm


  have ha_orbit : ∀ A B : Label, (∃ n : N, a n A = B) ↔ A.val.2 = B.val.2 :=
    (Classical.choose_spec (algebraicAction M J)).2.1
  obtain ⟨hobjFibres, harrowFibres⟩ := quotientFibres a a_snd a_displacement ha_orbit
  refine ⟨upstairs_nonempty cs J, upstairs_connected cs J, (fun A => upstairs_thin cs J A A),
    F, projection_obj_val cs J, projection_map_val cs J, hFcover, hFsurj,
    deck, hdeck, e, hfree, hrep, ?_, ?_, ?_⟩
  · intro A B
    simpa only [he] using hobjFibres A B
  · simpa only [he] using harrowFibres
  · intro finiteRank
    letI : Finite S := finiteRank
    have remainingGeometry : (
    let W := CoxeterMatrix.Group M
    let cs := CoxeterMatrix.toCoxeterSystem M
    let Obj := { I : Set S // ∃ g : W,
      Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g))
        (CoxeterSystem.parabolic cs I) = CoxeterSystem.parabolic cs J }
    let Label := { p : W × Set S //
      Set.image (fun u : W => u * p.1) (CoxeterSystem.parabolic cs J : Set W) =
        Set.image (fun u : W => p.1 * u) (CoxeterSystem.parabolic cs p.2 : Set W) ∧
      CoxeterSystem.IsMinimalCosetRep cs p.2 p.1 }
    letI : CategoryTheory.Groupoid Obj := BrinkHowlettGroupoid cs J
    letI : CategoryTheory.Groupoid Label := UniversalWallGroupoid cs J
    let N := ArtinNormalisers.Artin.coxeterNormalizerQuotient M J
    let Norm := ArtinNormalisers.Theorem18.CoxeterNormalizer M J
    let quotientMap : Norm → N := QuotientGroup.mk'
      ((ArtinNormalisers.Artin.coxeterParabolic M J).subgroupOf Norm)
    let F := projection cs J
    let action := Classical.choose (algebraicAction M J)
    let Θ := ArtinNormalisers.Theorem18.relativeSubspace J
    letI : TopologicalSpace Θ := TopologicalSpace.induced
      (fun f : Θ => ArtinNormalisers.Theorem18.dualCoordinates f.val)
      (inferInstance : TopologicalSpace (S → Real))
    let data := RelativeCone M J
    let coneInterior : Set Θ := data.2.1
    let arrangement : Set (Submodule Real Θ) := data.2.2.2.2.2
    let complement : Set Θ := { f | f ∈ coneInterior ∧
      ∀ H : Submodule Real Θ, H ∈ arrangement → f ∉ (H : Set Θ) }
    let Chamber := { C : Set Θ // ∃ f : Θ,
      f ∈ complement ∧ C = connectedComponentIn complement f }
    let face : Set S → Set (ArtinNormalisers.Theorem18.Dual S) := fun I =>
      { f | f ∈ ArtinNormalisers.Theorem18.relativeSubspace I ∧
        ∀ i : S, i ∉ I → 0 < ArtinNormalisers.Theorem18.dualCoordinates f i }
    let region : Label → Set Θ := fun A =>
      { f | ∃ g : ArtinNormalisers.Theorem18.Dual S,
        g ∈ face A.val.2 ∧ ArtinNormalisers.Theorem18.dualAction M A.val.1 g = f.val }
    let affineDimension : Set Θ → Nat := fun C =>
      Module.finrank Real (AffineSubspace.direction (affineSpan Real C))
    let wall : Set Θ → Set Θ → Prop := fun C H =>
      Set.Nonempty H ∧ ∃ P : Submodule Real Θ, P ∈ arrangement ∧
        H = closure C ∩ (P : Set Θ) ∧ affineDimension H + 1 = affineDimension C
    let adjacent : Label → Label → Prop := fun A B =>
      region A ≠ region B ∧ ∃ H : Set Θ, wall (region A) H ∧ wall (region B) H
    let component : Set S → S → Set S := fun I a =>
      { b | b ∈ Set.insert a I ∧ Relation.ReflTransGen
        (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧
          i ≠ j ∧ M i j ≠ 2) a b }
    let Step := { p : Label × S // p.2 ∉ p.1.val.2 ∧
      Finite (CoxeterSystem.parabolic cs (component p.1.val.2 p.2)) }
    let crossing := fun s : Step =>
      SimpleWallCrossings S W M cs s.val.1.val.2 s.val.2 s.property.1 s.property.2
    (∃ c : Equiv Label Chamber, ∀ A : Label, (c A).val = region A) ∧
    (∀ (n : N) (A : Label),
      Set.image (ArtinNormalisers.Theorem18.quotientRepresentation M J n) (region A) =
        region (action n A)) ∧
    (∀ (A B : Label) (s : Step), s.val.1 = A →
      (crossing s).2.2 A.val.1 = B.val →
      ∀ f : (UniversalWallGroupoid cs J).Hom A B,
        (F.map f).val = (crossing s).1) ∧
    (∀ (A B : Label) (f : (UniversalWallGroupoid cs J).Hom A B),
      ∃ es : List Step,
        List.foldr
          (fun s tail P => P = s.val.1.val ∧
            tail ((crossing s).2.2 s.val.1.val.1))
          (fun P => P = B.val) es A.val ∧
        List.prod (List.map (fun s => (crossing s).1) es) = f.val ∧
        List.prod (List.map (fun s => (crossing s).1) es) = (F.map f).val) ∧
    (∀ (I K : Obj) (w : (BrinkHowlettGroupoid cs J).Hom I K),
      ∃ (A B : Label) (es : List Step),
        F.obj A = I ∧ F.obj B = K ∧
        List.foldr
          (fun s tail P => P = s.val.1.val ∧
            tail ((crossing s).2.2 s.val.1.val.1))
          (fun P => P = B.val) es A.val ∧
        List.prod (List.map (fun s => (crossing s).1) es) = w.val)
    ) := by
      classical
      let W := CoxeterMatrix.Group M
      let cs := CoxeterMatrix.toCoxeterSystem M
      let Obj := { I : Set S // ∃ g : W,
        Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g))
          (CoxeterSystem.parabolic cs I) = CoxeterSystem.parabolic cs J }
      let Label := { p : W × Set S //
        Set.image (fun u : W => u * p.1) (CoxeterSystem.parabolic cs J : Set W) =
          Set.image (fun u : W => p.1 * u) (CoxeterSystem.parabolic cs p.2 : Set W) ∧
        CoxeterSystem.IsMinimalCosetRep cs p.2 p.1 }
      letI : CategoryTheory.Groupoid Obj := BrinkHowlettGroupoid cs J
      letI : CategoryTheory.Groupoid Label := UniversalWallGroupoid cs J
      let N := ArtinNormalisers.Artin.coxeterNormalizerQuotient M J
      let Norm := ArtinNormalisers.Theorem18.CoxeterNormalizer M J
      let quotientMap : Norm → N := QuotientGroup.mk'
        ((ArtinNormalisers.Artin.coxeterParabolic M J).subgroupOf Norm)
      let F := projection cs J
      let action := Classical.choose (algebraicAction M J)
      let Θ := ArtinNormalisers.Theorem18.relativeSubspace J
      letI : TopologicalSpace Θ := TopologicalSpace.induced
        (fun f : Θ => ArtinNormalisers.Theorem18.dualCoordinates f.val)
        (inferInstance : TopologicalSpace (S → Real))
      let data := RelativeCone M J
      let coneInterior : Set Θ := data.2.1
      let arrangement : Set (Submodule Real Θ) := data.2.2.2.2.2
      let complement : Set Θ := { f | f ∈ coneInterior ∧
        ∀ H : Submodule Real Θ, H ∈ arrangement → f ∉ (H : Set Θ) }
      let Chamber := { C : Set Θ // ∃ f : Θ,
        f ∈ complement ∧ C = connectedComponentIn complement f }
      let face : Set S → Set (ArtinNormalisers.Theorem18.Dual S) := fun I =>
        { f | f ∈ ArtinNormalisers.Theorem18.relativeSubspace I ∧
          ∀ i : S, i ∉ I → 0 < ArtinNormalisers.Theorem18.dualCoordinates f i }
      let region : Label → Set Θ := fun A =>
        { f | ∃ g : ArtinNormalisers.Theorem18.Dual S,
          g ∈ face A.val.2 ∧ ArtinNormalisers.Theorem18.dualAction M A.val.1 g = f.val }
      let affineDimension : Set Θ → Nat := fun C =>
        Module.finrank Real (AffineSubspace.direction (affineSpan Real C))
      let wall : Set Θ → Set Θ → Prop := fun C H =>
        Set.Nonempty H ∧ ∃ P : Submodule Real Θ, P ∈ arrangement ∧
          H = closure C ∩ (P : Set Θ) ∧ affineDimension H + 1 = affineDimension C
      let adjacent : Label → Label → Prop := fun A B =>
        region A ≠ region B ∧ ∃ H : Set Θ, wall (region A) H ∧ wall (region B) H
      let component : Set S → S → Set S := fun I a =>
        { b | b ∈ Set.insert a I ∧ Relation.ReflTransGen
          (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧
            i ≠ j ∧ M i j ≠ 2) a b }
      let Step := { p : Label × S // p.2 ∉ p.1.val.2 ∧
        Finite (CoxeterSystem.parabolic cs (component p.1.val.2 p.2)) }
      let crossing := fun s : Step =>
        SimpleWallCrossings S W M cs s.val.1.val.2 s.val.2 s.property.1 s.property.2
      dsimp only
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
      have chamberLabelling : (∀ (M : CoxeterMatrix S) (J : Set S),
        let Θ := ArtinNormalisers.Theorem18.relativeSubspace J
        letI : TopologicalSpace Θ := TopologicalSpace.induced
          (fun f : Θ => ArtinNormalisers.Theorem18.dualCoordinates f.val)
          (inferInstance : TopologicalSpace (S → Real))
        let data := RelativeCone M J
        let coneInterior : Set Θ := data.2.1
        let arrangement : Set (Submodule Real Θ) := data.2.2.2.2.2
        let complement : Set Θ := { f | f ∈ coneInterior ∧
          ∀ H : Submodule Real Θ, H ∈ arrangement → f ∉ (H : Set Θ) }
        let chambers : Set (Set Θ) := { C | ∃ f : Θ,
          f ∈ complement ∧ C = connectedComponentIn complement f }
        let labels : Set (CoxeterMatrix.Group M × Set S) := { p |
          Set.image (fun u : CoxeterMatrix.Group M => u * p.1)
            (CoxeterSystem.parabolic (CoxeterMatrix.toCoxeterSystem M) J : Set (CoxeterMatrix.Group M)) =
          Set.image (fun u : CoxeterMatrix.Group M => p.1 * u)
            (CoxeterSystem.parabolic (CoxeterMatrix.toCoxeterSystem M) p.2 : Set (CoxeterMatrix.Group M)) ∧
          CoxeterSystem.IsMinimalCosetRep (CoxeterMatrix.toCoxeterSystem M) p.2 p.1 }
        let face : Set S → Set (ArtinNormalisers.Theorem18.Dual S) := fun I =>
          { f | f ∈ ArtinNormalisers.Theorem18.relativeSubspace I ∧
            ∀ i : S, i ∉ I → 0 < ArtinNormalisers.Theorem18.dualCoordinates f i }
        let labelRegion : (CoxeterMatrix.Group M × Set S) → Set Θ := fun p =>
          { f | ∃ g : ArtinNormalisers.Theorem18.Dual S,
            g ∈ face p.2 ∧ ArtinNormalisers.Theorem18.dualAction M p.1 g = f.val }
        Set.BijOn labelRegion labels chambers) :=
      (by
        classical
        intro M J
        let Θ := ArtinNormalisers.Theorem18.relativeSubspace J
        let W := CoxeterMatrix.Group M
        let cs := CoxeterMatrix.toCoxeterSystem M
        let U : Set Θ := interior ((RelativeCone M J).1)
        let regular : Set Θ := {f | ArtinNormalisers.Landmark1.realRelativeRegular M J f}
        let R := @ArtinNormalisers.Chamber3.translatedFacet S M J
        -- Portal steps 1.1--1.2 identify the geometric and algebraic conventions.
        -- We reconstruct the required labelling input instead of assuming the
        -- unformalized independent supplier F3. Finite rank is the user's geometric
        -- convention; neither the Coxeter group nor its parabolic is assumed finite.
        -- Source: https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-thm-chamber-labelling-artin-tits-normalisers
        -- These local implementation lemmas belong to the proof of Theorem 3.9,
        -- printed pp. 9--10, and have no claimed standalone article attribution.
        -- No independent reading of the Iyama--Wemyss proof is claimed.
        -- All four supplied helper audits recommend retaining these blocks unchanged;
        -- their advice is not used as an assumed mathematical dependency.
        -- Defect source: https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects
        -- Finding pdf-prop36-ambient-ball-inference, PDF p. 9, second proof paragraph:
        -- m12=infinity, m13=m23=3, J={1,2}, u=(0,0,1) gives ambient hyperplanes
        -- accumulating nearby. Disposition: no ambient-ball inference is used.
        -- The report does not identify Theorem 3.9's statement as defective.
        let labels : Set (W × Set S) := { p |
          Set.image (fun u : W => u * p.1) (cs.parabolic J : Set W) =
          Set.image (fun u : W => p.1 * u) (cs.parabolic p.2 : Set W) ∧
          cs.IsMinimalCosetRep p.2 p.1 }
        let region : W × Set S → Set Θ := fun p => { f |
          ∃ g : ArtinNormalisers.Theorem18.Dual S,
            g ∈ ArtinNormalisers.Chamber3.standardFacet M p.2 ∧
            ArtinNormalisers.Theorem18.dualAction M p.1 g = f.val }
        let A := (RelativeCone M J).2.2.2.2.2
        let complement : Set Θ := {f | f ∈ U ∧ ∀ H, H ∈ A → f ∉ (H : Set Θ)}
        -- Step 1.1: the existing subtype topology is the requested coordinate topology.
        have htop : TopologicalSpace.induced
            (fun f : Θ => ArtinNormalisers.Theorem18.dualCoordinates f.val)
            (inferInstance : TopologicalSpace (S → Real)) =
            (inferInstance : TopologicalSpace Θ) := by
          exact induced_compose.symm
        have hU : (RelativeCone M J).2.1 = U := by
          change @interior Θ (TopologicalSpace.induced
            (fun f : Θ => ArtinNormalisers.Theorem18.dualCoordinates f.val)
            (inferInstance : TopologicalSpace (S → Real))) _ = _
          rw [htop]
          rfl
        dsimp only
        rw [htop, hU]
        change Set.BijOn region labels { C | ∃ f : Θ, f ∈ complement ∧
          C = connectedComponentIn complement f }
        have hregular (f : Θ) : (∀ H, H ∈ A → f ∉ (H : Set Θ)) ↔ f ∈ regular := by
          constructor
          · intro hf r hr hz
            have hroot : r ∈ cs.geometricRoots := hr.1
            rcases cs.pos_or_neg_of_mem_geometricRoots hroot with hp | hn
            · exact hf _ ⟨r, ⟨hr, hp⟩, rfl⟩ hz
            · have hnr : -r ∈ ArtinNormalisers.Theorem18.retainedRoots M J := by
                refine ⟨?_, ?_⟩
                · exact cs.neg_mem_geometricRoots_iff.mpr hroot
                · obtain ⟨g, hg⟩ := hr.2
                  exact ⟨g, by simpa only [map_neg, neg_ne_zero] using hg⟩
              exact hf _ ⟨-r, ⟨hnr, neg_pos.mpr hn⟩, rfl⟩ (by
                change f.val (-r) = 0
                rw [map_neg, hz, neg_zero])
          · intro hf H hH hz
            obtain ⟨r, hr, rfl⟩ := hH
            exact hf r hr.1 hz
        -- Departure from applying F3: prove the stabilizer assertion locally.
        -- Cone membership supplies a dominant translate, so the existing
        -- finite-group regular-point stabilizer theorem is unnecessary.
        have hstab (f : Θ) (hf : f ∈ regular)
            (u : W) (hu : ArtinNormalisers.Landmark1.IsDominant
              (ArtinNormalisers.Theorem18.dualAction M u f.val)) (g : W) :
            ArtinNormalisers.Theorem18.dualAction M g f.val = f.val ↔
            g ∈ ArtinNormalisers.Artin.coxeterParabolic M J := by
          constructor
          · intro hg
            let P : Subgroup W := {
              carrier := {w | ∀ q : Θ, ArtinNormalisers.Theorem18.dualAction M w q.val = q.val}
              one_mem' := by intro q; simp
              mul_mem' := by
                intro v w hv hw q
                rw [map_mul, mul_apply_eq_comp, hw q, hv q]
              inv_mem' := by
                intro v hv q
                have h := congrArg (ArtinNormalisers.Theorem18.dualAction M v⁻¹) (hv q)
                simpa only [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel,
                  map_one, one_apply_eq_self] using h.symm }
            let ψ := ArtinNormalisers.Theorem18.dualAction M u f.val
            have hconj : ArtinNormalisers.Theorem18.dualAction M (u * g * u⁻¹) ψ = ψ := by
              dsimp only [ψ]
              simp only [map_mul, mul_apply_eq_comp]
              rw [Representation.inv_self_apply, hg]
            have hpar := (ArtinNormalisers.Landmark1.dominant_fixed_iff M hu _).mp hconj
            have hle : ArtinNormalisers.Artin.coxeterParabolic M
                (ArtinNormalisers.Landmark1.zeroIndices ψ) ≤
                P.comap (MulAut.conj u⁻¹).toMonoidHom := by
              change Subgroup.closure _ ≤ _
              apply (Subgroup.closure_le _).mpr
              rintro _ ⟨i, hi, rfl⟩
              have hz : f.val (ArtinNormalisers.Theorem18.root M u⁻¹ i) = 0 := hi
              have hann : ∀ q : Θ, q.val (ArtinNormalisers.Theorem18.root M u⁻¹ i) = 0 := by
                intro q
                by_contra hq
                exact hf _ ⟨⟨u⁻¹, i, rfl⟩, q, hq⟩ hz
              intro q
              have hs : ArtinNormalisers.Theorem18.dualAction M (M.simple i)
                  (ArtinNormalisers.Theorem18.dualAction M u q.val) =
                  ArtinNormalisers.Theorem18.dualAction M u q.val :=
                (ArtinNormalisers.Theorem18.dualAction_simple_fixed_iff M i _).mpr (hann q)
              have h := congrArg (ArtinNormalisers.Theorem18.dualAction M u⁻¹) hs
              change ArtinNormalisers.Theorem18.dualAction M
                (u⁻¹ * M.simple i * (u⁻¹)⁻¹) q.val = q.val
              simpa only [inv_inv, ← mul_apply_eq_comp, ← map_mul, inv_mul_cancel,
                mul_assoc, map_one, one_apply_eq_self] using h
            have hgflat := hle hpar
            change ∀ q : Θ, ArtinNormalisers.Theorem18.dualAction M
              (u⁻¹ * (u * g * u⁻¹) * (u⁻¹)⁻¹) q.val = q.val at hgflat
            have he : u⁻¹ * (u * g * u⁻¹) * (u⁻¹)⁻¹ = g := by group
            rw [he] at hgflat
            exact (ArtinNormalisers.Landmark1.pointwise_flat_fixed_iff M J g).mp hgflat
          · exact fun hg => (ArtinNormalisers.Theorem18.mem_relativeSubspace_iff_fixed M J f.val).mp
              f.property g hg
        have hRsub (L : ArtinNormalisers.Chamber3.RawFacetLabel M J) : R L ⊆ complement := by
          have hcone : R L ⊆ (RelativeCone M J).1 := by
            intro f hf
            obtain ⟨g, hg, he⟩ := (ArtinNormalisers.Chamber3.mem_translatedFacet_iff L f).mp hf
            exact ⟨L.representative, g, ArtinNormalisers.Chamber3.standardFacet_isDominant M hg, he⟩
          have hinterior : R L ⊆ U :=
            interior_maximal hcone (ArtinNormalisers.Chamber3.isOpen_translatedFacet L)
          intro f hf
          exact ⟨hinterior hf, (hregular f).mpr
            (ArtinNormalisers.Chamber3.realRelativeRegular_of_mem_translatedFacet L hf)⟩
        have hcover (f : Θ) (hf : f ∈ complement) :
            ∃ L : ArtinNormalisers.Chamber3.RawFacetLabel M J, f ∈ R L := by
          obtain ⟨w, g, hg, he⟩ := interior_subset hf.1
          let u := w⁻¹
          have hu : ArtinNormalisers.Landmark1.IsDominant
              (ArtinNormalisers.Theorem18.dualAction M u f.val) := by
            rw [← he, Representation.inv_self_apply]
            exact hg
          let ψ := ArtinNormalisers.Theorem18.dualAction M u f.val
          let K := ArtinNormalisers.Landmark1.zeroIndices ψ
          have hψ : ψ ∈ ArtinNormalisers.Chamber3.standardFacet M K :=
            ArtinNormalisers.Chamber3.mem_standardFacet_zeroIndices hu
          have hconj : (ArtinNormalisers.Artin.coxeterParabolic M K).map
              (MulAut.conj u⁻¹).toMonoidHom = ArtinNormalisers.Artin.coxeterParabolic M J := by
            ext v
            rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
            rw [← ArtinNormalisers.Landmark1.dominant_fixed_iff M hu,
              ← hstab f ((hregular f).mp hf.2) u hu v]
            simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, inv_mul_cancel, mul_one] using
              ArtinNormalisers.Chamber3.dualAction_stabilizer_conjugate M u f.val (u * v * u⁻¹)
          refine ⟨⟨K, u⁻¹, hconj⟩, ?_⟩
          apply (ArtinNormalisers.Chamber3.mem_translatedFacet_iff _ f).mpr
          refine ⟨ψ, hψ, ?_⟩
          exact Representation.inv_self_apply _ u f.val
        have hcomponent (L : ArtinNormalisers.Chamber3.RawFacetLabel M J)
            {f : Θ} (hf : f ∈ R L) : connectedComponentIn complement f = R L := by
          exact ArtinNormalisers.Chamber3.connectedComponentIn_eq_of_open_partition R complement
            (fun L => ArtinNormalisers.Chamber3.isOpen_translatedFacet L)
            (fun L => (ArtinNormalisers.Chamber3.convex_translatedFacet L).isPreconnected)
            hRsub hcover ArtinNormalisers.Chamber3.translatedFacet_eq_of_intersection L hf
        -- Step 1.2: match literal coset equality to conjugated-parabolic labels,
        -- and remove right-parabolic ambiguity using minimum representatives.
        have hcoset (x : W) (I : Set S) :
            Set.image (fun u : W => u * x) (cs.parabolic J : Set W) =
              Set.image (fun u : W => x * u) (cs.parabolic I : Set W) ↔
            (ArtinNormalisers.Artin.coxeterParabolic M I).map
              (MulAut.conj x).toMonoidHom = ArtinNormalisers.Artin.coxeterParabolic M J := by
          constructor
          · intro h
            ext v
            constructor
            · rintro ⟨u, hu, huv⟩
              change x * u * x⁻¹ = v at huv
              have hm : x * u ∈ Set.image (fun t : W => t * x) (cs.parabolic J : Set W) :=
                h.symm ▸ (Set.mem_image_of_mem (fun t : W => x * t) hu)
              obtain ⟨t, ht, he⟩ := hm
              have hev : t = v := by rw [← huv, ← he]; group
              exact hev ▸ ht
            · intro hv
              have hm : v * x ∈ Set.image (fun t : W => x * t) (cs.parabolic I : Set W) :=
                h ▸ (Set.mem_image_of_mem (fun t : W => t * x) hv)
              obtain ⟨t, ht, he⟩ := hm
              refine ⟨t, ht, ?_⟩
              change x * t = v * x at he
              change x * t * x⁻¹ = v
              rw [he]
              group
          · intro h
            apply Set.Subset.antisymm
            · rintro _ ⟨v, hv, rfl⟩
              change v ∈ ArtinNormalisers.Artin.coxeterParabolic M J at hv
              rw [← h, Subgroup.mem_map_equiv, MulAut.conj_symm_apply] at hv
              refine ⟨x⁻¹ * v * x, hv, ?_⟩
              group
            · rintro _ ⟨v, hv, rfl⟩
              have hm : x * v * x⁻¹ ∈ ArtinNormalisers.Artin.coxeterParabolic M J := by
                rw [← h]
                exact ⟨v, hv, rfl⟩
              refine ⟨x * v * x⁻¹, hm, ?_⟩
              group
        have hregion (L : ArtinNormalisers.Chamber3.RawFacetLabel M J) :
            region (L.representative, L.indices) = R L := by
          ext f
          exact (ArtinNormalisers.Chamber3.mem_translatedFacet_iff L f).symm
        have hlabelraw (p : W × Set S) (hp : p ∈ labels) :
            ∃ L : ArtinNormalisers.Chamber3.RawFacetLabel M J,
              L.representative = p.1 ∧ L.indices = p.2 ∧ region p = R L := by
          let L : ArtinNormalisers.Chamber3.RawFacetLabel M J :=
            ⟨p.2, p.1, (hcoset p.1 p.2).mp hp.1⟩
          exact ⟨L, rfl, rfl, hregion L⟩
        have hrawlabel (L : ArtinNormalisers.Chamber3.RawFacetLabel M J) :
            ∃ p ∈ labels, region p = R L := by
          let d := cs.minimalCosetRep L.indices L.representative
          have hd : (ArtinNormalisers.Artin.coxeterParabolic M L.indices).map
              (MulAut.conj d).toMonoidHom = ArtinNormalisers.Artin.coxeterParabolic M J :=
            ArtinNormalisers.Chamber3.minimalCosetRep_transports_parabolic cs L.parabolic_conjugacy
          let K : ArtinNormalisers.Chamber3.RawFacetLabel M J := ⟨L.indices, d, hd⟩
          refine ⟨(d, L.indices), ⟨(hcoset d L.indices).mpr hd,
            cs.isMinimalCosetRep_minimalCosetRep L.indices L.representative⟩, ?_⟩
          exact (hregion K).trans
            (ArtinNormalisers.Chamber3.translatedFacet_eq_of_indices_coset L K rfl
              (cs.inv_mul_minimalCosetRep_mem L.indices L.representative)).symm
        -- Step 2.1: prove the bijection from the open connected partition rather
        -- than applying F3. Point witnesses exclude spurious empty components;
        -- empty S and J = Set.univ require no extra hypothesis.
        refine ⟨?_, ?_, ?_⟩
        · intro p hp
          obtain ⟨L, _, _, he⟩ := hlabelraw p hp
          obtain ⟨f, hf⟩ := ArtinNormalisers.Chamber3.translatedFacet_nonempty L
          exact ⟨f, hRsub L hf, he.trans (hcomponent L hf).symm⟩
        · intro p hp q hq he
          obtain ⟨L, hLx, hLI, hL⟩ := hlabelraw p hp
          obtain ⟨K, hKx, hKI, hK⟩ := hlabelraw q hq
          have hLK : R L = R K := hL.symm.trans (he.trans hK)
          obtain ⟨hI, hc⟩ := (ArtinNormalisers.Chamber3.translatedFacet_eq_iff L K).mp hLK
          have hidx : p.2 = q.2 := hLI.symm.trans (hI.trans hKI)
          have hc' : p.1⁻¹ * q.1 ∈ cs.parabolic p.2 := by
            simpa only [hLx, hKx, hLI, ArtinNormalisers.Artin.coxeterParabolic_eq] using hc
          exact Prod.ext (hp.2.eq_of_inv_mul_mem cs (hidx.symm ▸ hq.2) hc') hidx
        · rintro C ⟨f, hf, rfl⟩
          obtain ⟨L, hL⟩ := hcover f hf
          obtain ⟨p, hp, he⟩ := hrawlabel L
          exact ⟨p, hp, he.trans (hcomponent L hL).symm⟩)
      have chamber_bijection : ∃ c : Equiv Label Chamber, ∀ A : Label, (c A).val = region A := by
        -- Covering step 1.2: turn the completed BijOn into an equivalence of subtypes.
        have h := chamberLabelling M J
        let cfun : Label → Chamber := fun A => ⟨region A, h.1 A.property⟩
        have hinj : Function.Injective cfun := by
          intro A B he
          exact Subtype.ext (h.2.1 A.property B.property (congrArg Subtype.val he))
        have hsurj : Function.Surjective cfun := by
          intro C
          obtain ⟨p, hp, he⟩ := h.2.2 C.property
          exact ⟨⟨p, hp⟩, Subtype.ext he⟩
        exact ⟨Equiv.ofBijective cfun ⟨hinj, hsurj⟩, fun A => rfl⟩
      have covariance : ∀ (n : N) (A : Label),
          Set.image (ArtinNormalisers.Theorem18.quotientRepresentation M J n) (region A) =
            region (action n A) := by
        -- Covering step 3.2: extract checked covariance for ANY representative formula.
        exact checkedRegionCovariance action (Classical.choose_spec (algebraicAction M J)).1
      have crossing_projection : ∀ (A B : Label) (s : Step), s.val.1 = A →
          (crossing s).2.2 A.val.1 = B.val →
          ∀ f : (UniversalWallGroupoid cs J).Hom A B, (F.map f).val = (crossing s).1 := by
        -- Covering step 1.2: literal target equality suffices for cancellation.
        intro A B s _ hs f
        have he : A.val.1 * (crossing s).1 = B.val.1 := congrArg Prod.fst hs
        change f.val = (crossing s).1
        rw [f.property, ← he, inv_mul_cancel_left]
      have upstairs_generation : ∀ (A B : Label) (f : (UniversalWallGroupoid cs J).Hom A B),
          ∃ es : List Step,
            List.foldr
              (fun s tail P => P = s.val.1.val ∧ tail ((crossing s).2.2 s.val.1.val.1))
              (fun P => P = B.val) es A.val ∧
            List.prod (List.map (fun s => (crossing s).1) es) = f.val ∧
            List.prod (List.map (fun s => (crossing s).1) es) = (F.map f).val := by
        -- Proposition 4.4 / covering step 6.1: reuse the source-tagged list, including [].
        intro A B f
        obtain ⟨es, hp, he, _⟩ := UniversalGenerators M J A B
        exact ⟨es, hp, he.trans f.property.symm, he.trans f.property.symm⟩
      have downstairs_generation : ∀ (I K : Obj) (w : (BrinkHowlettGroupoid cs J).Hom I K),
          ∃ (A B : Label) (es : List Step),
            F.obj A = I ∧ F.obj B = K ∧
            List.foldr
              (fun s tail P => P = s.val.1.val ∧ tail ((crossing s).2.2 s.val.1.val.1))
              (fun P => P = B.val) es A.val ∧
            List.prod (List.map (fun s => (crossing s).1) es) = w.val := by
        -- Covering step 6.1: preserve the actual source and target tags under lifting.
        intro I K w
        obtain ⟨A, hA⟩ := projection_surjective cs J I
        subst I
        obtain ⟨⟨B, f⟩, hf⟩ := (projection_covering cs J A).2 ⟨K, w⟩
        have hB : F.obj B = K := congrArg Sigma.fst hf
        have hw : (F.map f).val = w.val := congrArg (fun t => t.2.val) hf
        obtain ⟨es, hp, _, he⟩ := upstairs_generation A B f
        exact ⟨A, B, es, rfl, hB, hp, he.trans hw⟩
      exact ⟨chamber_bijection, covariance, crossing_projection, upstairs_generation, downstairs_generation⟩

    obtain ⟨h1, h2, h4, h5, h6⟩ := remainingGeometry
    refine ⟨h1, ?_, checkedGeometricAdjacency M J, h4, h5, h6⟩
    simpa only [he] using h2
)
