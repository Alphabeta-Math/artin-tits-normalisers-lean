import Mathlib
import ArtinDeligne
import Proofs.ChamberLabelling
import Proofs.BrinkHowlettGroupoid
import Proofs.UniversalWallGroupoid

set_option maxHeartbeats 2000000

theorem ChamberMorphismCorrespondence : (∀ {S W : Type*} [Finite S] [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S),
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
        f.val = w.val)) :=
(by
  /- Proposition 4.6, printed p.16; Alphabeta numbered proof:
     https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-prop-chambers-morphisms-artin-tits-normalisers
     The local algebra blocks below reuse the completed implementation in
     theorems13-14/Proofs/FiniteWallPaths.lean, lines 2292-2443, read-only.
     They are implementation lemmas, not additional standalone article results.
     The finite-rank hypothesis of the accepted endpoint is retained. -/
  intro S W finiteS groupW M cs J
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
