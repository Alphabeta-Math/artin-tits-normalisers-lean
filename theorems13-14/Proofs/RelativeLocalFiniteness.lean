import Mathlib
import ArtinDeligne
import Proofs.RelativeCone

theorem RelativeLocalFiniteness : (∀ {S : Type*} [Finite S] (M : CoxeterMatrix S) (J : Set S),
  letI : Fintype S := Fintype.ofFinite S
  let Θ := ArtinNormalisers.Theorem18.relativeSubspace J
  letI : TopologicalSpace Θ := TopologicalSpace.induced
    (fun f : Θ => ArtinNormalisers.Theorem18.dualCoordinates f.val)
    (inferInstance : TopologicalSpace (S → Real))
  let data := RelativeCone M J
  let cone : Set Θ := data.1
  let coneInterior : Set Θ := data.2.1
  let arrangement : Set (Submodule Real Θ) := data.2.2.2.2.2
  let ball : Θ → Real → Set Θ := fun u r =>
    { v | Finset.sum Finset.univ (fun i : S =>
        (ArtinNormalisers.Theorem18.dualCoordinates v.val i -
         ArtinNormalisers.Theorem18.dualCoordinates u.val i) ^ 2) < r ^ 2 }
  (∀ u : Θ, u ∈ coneInterior → ∃ r : Real, 0 < r ∧
    ball u r ⊆ cone ∧
    Set.Finite { H : Submodule Real Θ | H ∈ arrangement ∧
      Set.Nonempty (ball u r ∩ (H : Set Θ)) }) ∧
  (∀ u : Θ, u ∈ coneInterior → ∃ U : Set Θ,
    IsOpen U ∧ u ∈ U ∧ U ⊆ coneInterior ∧
    Set.Finite { H : Submodule Real Θ | H ∈ arrangement ∧
      Set.Nonempty ((H : Set Θ) ∩ coneInterior) ∧
      Set.Nonempty (U ∩ (H : Set Θ)) })) :=
(by
  /- Proposition 3.6, printed p.9, https://arxiv.org/pdf/2509.21915#page=9.
     Numbered inspiration: local-finiteness 1.1 and 2.1,
     https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-prop-relative-local-finiteness-artin-tits-normalisers
     and finite-relative-ball 1.1--2.1,
     https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-author-b319c70a2611-finite-relative-ball.
     All supporting arguments below are local have blocks, proved here.
     They have no separate standalone article attribution.

     Literature defects, exact report:
     https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects
     Finding pdf-lemma35-boundary-inferences: Lemma 3.5 proof p.8 claims a
     nonempty set of negative simple evaluations for an arbitrary nontrivial
     closed-chamber representative. Rank one, g=0, w=s, f(alpha)=1 makes
     that set empty. We use only negative evaluation => negative transformed
     root, and prove inversion finiteness directly by generator induction.
     Finding pdf-prop36-ambient-ball-inference: Proposition 3.6 proof p.9,
     second paragraph claims an ambient ball avoiding root hyperplanes
     missing u. For m12=infinity, m13=m23=3, J={1,2}, u=(0,0,1), the
     cone points (1-4n,1+4n,4n^2)/(4n^2) approach u on such hyperplanes.
     We instead construct a relative ball using finite vertex separation.
     Neither finding refutes the retained proposition. Finite rank is the
     explicit user-directed portal convention, not a reported statement
     defect; neither the Coxeter group nor W_J is assumed finite.

     Helper advice supplied the mathematical decomposition, but its cited
     temporary Lean files were absent in this session. The integrated local
     proofs were reconstructed and compiled here, without importing those
     unavailable helpers. Reading covered the relevant portal entries,
     article pp.8--9, these report findings and imported source context.
     Reused the two supplied prerequisite reports' actual bounded search
     findings, not their unfinished reading. No full transitive-source
     review is claimed. Fresh GitHub dist_pi_lt_iff search found its Pi.lean
     declaration; actual use was checked at the pinned mathlib revision. -/
  classical
  intro S inst M J
  letI : Fintype S := Fintype.ofFinite S
  let Θ := ArtinNormalisers.Theorem18.relativeSubspace J
  letI : TopologicalSpace Θ := TopologicalSpace.induced
    (fun f : Θ => ArtinNormalisers.Theorem18.dualCoordinates f.val)
    (inferInstance : TopologicalSpace (S → Real))
  let cone : Set Θ := (RelativeCone M J).1
  let arrangement : Set (Submodule Real Θ) := (RelativeCone M J).2.2.2.2.2
  let ball : Θ → Real → Set Θ := fun u r =>
    { v | Finset.sum Finset.univ (fun i : S =>
        (ArtinNormalisers.Theorem18.dualCoordinates v.val i -
         ArtinNormalisers.Theorem18.dualCoordinates u.val i) ^ 2) < r ^ 2 }
  change
    (∀ u : Θ, u ∈ interior cone → ∃ r : Real, 0 < r ∧
      ball u r ⊆ cone ∧
      Set.Finite { H : Submodule Real Θ | H ∈ arrangement ∧
        Set.Nonempty (ball u r ∩ (H : Set Θ)) }) ∧
    (∀ u : Θ, u ∈ interior cone → ∃ U : Set Θ,
      IsOpen U ∧ u ∈ U ∧ U ⊆ interior cone ∧
      Set.Finite { H : Submodule Real Θ | H ∈ arrangement ∧
        Set.Nonempty ((H : Set Θ) ∩ interior cone) ∧
        Set.Nonempty (U ∩ (H : Set Θ)) })

  /- Separation supplier 1.2 and 2.1:
     https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-finite-separation-artin-tits-normalisers
     We need only finiteness, so replace the inversion-cardinality input
     by N(w*s_i) subset s_i N(w) union {alpha_i}. No rank hypothesis
     enters this algebraic argument. -/
  have finiteInv (cs : CoxeterSystem M (CoxeterMatrix.Group M)) (w : CoxeterMatrix.Group M) :
      Set.Finite {α | α ∈ cs.geometricRoots ∧ 0 < α ∧ cs.geometricRepresentation w α < 0} := by
    classical
    induction w using cs.simple_induction_right with
    | one =>
      have he : {α | α ∈ cs.geometricRoots ∧ 0 < α ∧ cs.geometricRepresentation (1 : CoxeterMatrix.Group M) α < 0} = ∅ := by
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

  have dominant_nonneg {f : ArtinNormalisers.Theorem18.Dual S} (hf : ArtinNormalisers.Landmark1.IsDominant f) {α : ArtinNormalisers.Theorem18.Vector S}
      (hα : 0 ≤ α) : 0 ≤ f α := by
    have h := ArtinNormalisers.Landmark1.evaluation_nonpos_of_nonpos hf (neg_nonpos.mpr hα)
    simpa only [map_neg, neg_nonpos] using h

  have finiteNegative (f : ArtinNormalisers.Theorem18.Dual S)
      (hf : ∃ (w : M.Group) (g : ArtinNormalisers.Theorem18.Dual S), ArtinNormalisers.Landmark1.IsDominant g ∧ ArtinNormalisers.Theorem18.dualAction M w g = f) :
      Set.Finite {α | α ∈ M.toCoxeterSystem.geometricRoots ∧ 0 < α ∧ f α < 0} := by
    obtain ⟨w, g, hg, rfl⟩ := hf
    apply (finiteInv M.toCoxeterSystem w⁻¹).subset
    rintro α ⟨hα, hp, hn⟩
    refine ⟨hα, hp, ?_⟩
    have hroot := (M.toCoxeterSystem.geometricRepresentation_apply_mem_geometricRoots_iff w⁻¹).mpr hα
    rcases M.toCoxeterSystem.pos_or_neg_of_mem_geometricRoots hroot with hpos | hneg
    · exact False.elim ((not_lt_of_ge (dominant_nonneg hg hpos.le)) hn)
    · exact hneg

  have finiteSeparators (f g : ArtinNormalisers.Theorem18.Dual S)
      (hf : ∃ (w : M.Group) (h : ArtinNormalisers.Theorem18.Dual S), ArtinNormalisers.Landmark1.IsDominant h ∧ ArtinNormalisers.Theorem18.dualAction M w h = f)
      (hg : ∃ (w : M.Group) (h : ArtinNormalisers.Theorem18.Dual S), ArtinNormalisers.Landmark1.IsDominant h ∧ ArtinNormalisers.Theorem18.dualAction M w h = g) :
      Set.Finite {H : Submodule ℝ (ArtinNormalisers.Theorem18.relativeSubspace J) | ∃ α : ArtinNormalisers.Theorem18.Vector S,
        α ∈ M.toCoxeterSystem.geometricRoots ∧ 0 < α ∧
        H = ArtinNormalisers.Theorem18.restrictedHyperplane J α ∧ f α * g α < 0} := by
    apply (((finiteNegative f hf).union (finiteNegative g hg)).image
      (ArtinNormalisers.Theorem18.restrictedHyperplane J)).subset
    rintro H ⟨α, hα, hp, rfl, hneg⟩
    refine ⟨α, ?_, rfl⟩
    rcases mul_neg_iff.mp hneg with h | h
    · exact Or.inr ⟨hα, hp, h.2⟩
    · exact Or.inl ⟨hα, hp, h.1⟩

  /- Hyperplane-vertex-separation 2.2 and 3.1:
     https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-author-b319c70a2611-hyperplane-vertex-separation
     Maximize the absolute functional coefficient. Each squared coordinate
     is bounded by their sum; the absolute evaluation is bounded by the
     sum of absolute products. We use n+1 in the denominator, n=card S,
     so n*r<epsilon without a separate zero-dimensional division. -/
  have coeff_bound (a c : S → ℝ) (ε : ℝ)
      (hε : 0 < ε) (ha : ∃ i, a i ≠ 0)
      (hc : ∑ i, (c i)^2 < (ε / (Fintype.card S + 1))^2) :
      ∃ i, (∑ j, c j * a j)^2 < ε^2 * (a i)^2 := by
    classical
    obtain ⟨k, hk⟩ := ha
    have hne : (Finset.univ : Finset S).Nonempty := ⟨k, Finset.mem_univ k⟩
    obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ (fun j => |a j|) hne
    have hA : 0 < |a i| := lt_of_lt_of_le (abs_pos.mpr hk) (hmax k (Finset.mem_univ k))
    let r : ℝ := ε / (Fintype.card S + 1)
    have hden : (0 : ℝ) < Fintype.card S + 1 := by positivity
    have hr : 0 < r := div_pos hε hden
    have hnr : (Fintype.card S : ℝ) * r < ε := by
      have he : r * (Fintype.card S + 1) = ε := div_mul_cancel₀ ε (ne_of_gt hden)
      nlinarith
    have hci (j : S) : |c j| ≤ r := by
      have hsq : (c j)^2 ≤ ∑ k, (c k)^2 := Finset.single_le_sum (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
      exact le_of_lt (abs_lt_of_sq_lt_sq (lt_of_le_of_lt hsq hc) (le_of_lt hr))
    have hsum : |∑ j, c j * a j| < ε * |a i| := by
      calc
        |∑ j, c j * a j| ≤ ∑ j, |c j * a j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j : S, r * |a i| := by
          apply Finset.sum_le_sum
          intro j _
          rw [abs_mul]
          exact mul_le_mul (hci j) (hmax j (Finset.mem_univ j)) (abs_nonneg _) hr.le
        _ = (Fintype.card S : ℝ) * r * |a i| := by simp [mul_assoc]
        _ < ε * |a i| := mul_lt_mul_of_pos_right hnr hA
    refine ⟨i, ?_⟩
    have hsq := (sq_lt_sq₀ (abs_nonneg (∑ j, c j * a j)) (le_of_lt (mul_pos hε hA))).mpr hsum
    simpa only [sq_abs, mul_pow] using hsq

  /- Finite-relative-ball 1.1; coordinate-vertices 1.1 and 2.1:
     https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-author-b319c70a2611-coordinate-vertices
     Departure: use the ambient simple-coordinate directions outside J,
     with zero directions on J, instead of constructing an orthonormal
     basis of Theta. An open sup-norm coordinate ball supplies vertices;
     the returned ball still has exactly the required square-sum formula.
     Finite-product topology agrees with the induced topology by its
     definition. For empty S or Theta=0, retention cannot supply a nonzero
     coefficient, so the hyperplane branch below is impossible. -/
  have hball : ∀ u : Θ, u ∈ interior cone → ∃ r : Real, 0 < r ∧
      ball u r ⊆ cone ∧
      Set.Finite { H : Submodule Real Θ | H ∈ arrangement ∧
        Set.Nonempty (ball u r ∩ (H : Set Θ)) } := by
    classical
    letI : Fintype S := Fintype.ofFinite S
    let Θ := ArtinNormalisers.Theorem18.relativeSubspace J
    letI : TopologicalSpace Θ := TopologicalSpace.induced
      (fun f : Θ => ArtinNormalisers.Theorem18.dualCoordinates f.val) (inferInstance : TopologicalSpace (S → ℝ))
    let coords : Θ → S → ℝ := fun f => ArtinNormalisers.Theorem18.dualCoordinates f.val
    let cone : Set Θ := (RelativeCone M J).1
    let ball : Θ → ℝ → Set Θ := fun u r => {v | ∑ i : S, (coords v i - coords u i)^2 < r^2}
    change ∀ u : Θ, u ∈ interior cone → ∃ r : ℝ, 0 < r ∧ ball u r ⊆ cone ∧
      Set.Finite {H : Submodule ℝ Θ | H ∈ (RelativeCone M J).2.2.2.2.2 ∧ (ball u r ∩ (H : Set Θ)).Nonempty}
    intro u hu
    obtain ⟨O, hO, hpre⟩ := isOpen_induced_iff.mp (isOpen_interior : IsOpen (interior cone))
    have huO : coords u ∈ O := by rw [← hpre] at hu; exact hu
    obtain ⟨R, hR, hRO⟩ := Metric.isOpen_iff.mp hO (coords u) huO
    let ε : ℝ := R / 2
    have hε : 0 < ε := half_pos hR
    have hεR : ε < R := by dsimp [ε]; linarith
    let r : ℝ := ε / (Fintype.card S + 1)
    have hden : (0 : ℝ) < Fintype.card S + 1 := by positivity
    have hr : 0 < r := div_pos hε hden
    have hrε : r ≤ ε := div_le_self hε.le (by have : (0 : ℝ) ≤ Fintype.card S := Nat.cast_nonneg _; linarith)
    have hsmall : ∀ v ∈ ball u r, ∀ i, |coords v i - coords u i| < r := by
      intro v hv i
      have hs : (coords v i - coords u i)^2 ≤ ∑ j, (coords v j - coords u j)^2 :=
        Finset.single_le_sum (f := fun j => (coords v j - coords u j)^2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      exact abs_lt_of_sq_lt_sq (lt_of_le_of_lt hs hv) hr.le
    have hsub : ball u r ⊆ cone := by
      intro v hv
      apply interior_subset
      rw [← hpre]
      apply hRO
      apply (dist_pi_lt_iff hR).mpr
      intro i
      rw [Real.dist_eq]
      exact lt_of_lt_of_le (hsmall v hv i) (hrε.trans hεR.le)
    let direction : S → Θ := fun i =>
      if hi : i ∈ J then 0 else
        ⟨Finsupp.lapply i, by
          intro j hj
          have hji : j ≠ i := fun he => hi (he ▸ hj)
          simp [ArtinNormalisers.Theorem18.simpleRoot, hji]⟩
    have hdir (i : S) (α : ArtinNormalisers.Theorem18.Vector S) : (direction i).val α = if i ∈ J then 0 else α i := by
      dsimp [direction]
      split <;> simp
    have hdircoords (i j : S) : coords (direction i) j =
        if i ∈ J then 0 else if j = i then 1 else 0 := by
      change (direction i).val (ArtinNormalisers.Theorem18.simpleRoot j) = _
      rw [hdir]
      simp only [ArtinNormalisers.Theorem18.simpleRoot, Finsupp.single_apply]
    let plus : S → Θ := fun i => u + ε • direction i
    let minus : S → Θ := fun i => u - ε • direction i
    have hvertices (i : S) : plus i ∈ cone ∧ minus i ∈ cone := by
      have hv : ∀ s : ℝ, |s| = ε → u + s • direction i ∈ cone := by
        intro s hs
        apply interior_subset
        rw [← hpre]
        apply hRO
        apply (dist_pi_lt_iff hR).mpr
        intro j
        rw [Real.dist_eq]
        change |ArtinNormalisers.Theorem18.dualCoordinates (u.val + s • (direction i).val) j - ArtinNormalisers.Theorem18.dualCoordinates u.val j| < R
        simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
        change |s * coords (direction i) j| < R
        rw [hdircoords]
        split_ifs <;> simp_all only [mul_zero, abs_zero, mul_one]
      exact ⟨hv ε (abs_of_pos hε), by
        change u - ε • direction i ∈ cone
        change u + -(ε • direction i) ∈ cone
        exact (congrArg (fun z : Θ => u + z ∈ cone) (neg_smul ε (direction i))).mp
          (hv (-ε) (by simp [abs_of_pos hε]))⟩
    have heval (f : Θ) (α : ArtinNormalisers.Theorem18.Vector S) : f.val α = ∑ i, coords f i * α i := by
      have he := (ArtinNormalisers.Theorem18.dualCoordinates (I := S)).symm_apply_apply f.val
      conv_lhs => rw [← he]
      change (Finsupp.linearCombination ℝ (coords f)) α = _
      rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype]
      · apply Finset.sum_congr rfl
        intro i _
        exact mul_comm _ _
      · intro i
        simp
    have hmask (f : Θ) (α : ArtinNormalisers.Theorem18.Vector S) :
        f.val α = ∑ i, coords f i * (if i ∈ J then 0 else α i) := by
      rw [heval]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ J
      · have hz : coords f i = 0 := f.property i hi
        simp [hi, hz]
      · simp [hi]
    have hsep (α : ArtinNormalisers.Theorem18.Vector S) (hα : α ∈ ArtinNormalisers.Theorem18.retainedRoots M J)
        (x : Θ) (hx : x ∈ ball u r) (hzero : x.val α = 0) :
        ∃ i, (plus i).val α * (minus i).val α < 0 := by
      let a : S → ℝ := fun i => if i ∈ J then 0 else α i
      have ha : ∃ i, a i ≠ 0 := by
        obtain ⟨f, hf⟩ := hα.2
        by_contra hn
        push Not at hn
        apply hf
        rw [hmask]
        change (∑ i, coords f i * a i) = 0
        simp [hn]
      obtain ⟨i, hi⟩ := coeff_bound a (fun j => coords u j - coords x j) ε hε ha (by
        have he : (∑ j, (coords u j - coords x j)^2) = ∑ j, (coords x j - coords u j)^2 := by
          apply Finset.sum_congr rfl
          intro j _
          ring
        rw [he]
        exact hx)
      have hsum : ∑ j, (coords u j - coords x j) * a j = u.val α := by
        simp_rw [sub_mul]
        rw [Finset.sum_sub_distrib]
        change (∑ j, coords u j * (if j ∈ J then 0 else α j)) -
          (∑ j, coords x j * (if j ∈ J then 0 else α j)) = _
        rw [← hmask, ← hmask, hzero, sub_zero]
      rw [hsum] at hi
      refine ⟨i, ?_⟩
      have hp : (plus i).val α = u.val α + ε * a i := by
        change (u.val + ε • (direction i).val) α = _
        simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hdir]
        rfl
      have hm : (minus i).val α = u.val α - ε * a i := by
        change (u.val - ε • (direction i).val) α = _
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, hdir]
        rfl
      rw [hp, hm]
      nlinarith
    /- Finite-relative-ball 2.1: finite separating roots give finite images
       of restricted kernels. No injectivity is assumed: coincident traces
       are counted once. Restricted and ambient evaluation agree by rfl. -/
    have hfin (i : S) : Set.Finite {H : Submodule ℝ Θ | ∃ α : ArtinNormalisers.Theorem18.Vector S,
        α ∈ M.toCoxeterSystem.geometricRoots ∧ 0 < α ∧ H = ArtinNormalisers.Theorem18.restrictedHyperplane J α ∧
        (plus i).val α * (minus i).val α < 0} :=
      finiteSeparators (plus i).val (minus i).val (hvertices i).1 (hvertices i).2
    refine ⟨r, hr, hsub, ?_⟩
    apply (Set.finite_iUnion hfin).subset
    rintro H ⟨⟨α, hα, rfl⟩, x, hx, hxH⟩
    obtain ⟨i, hi⟩ := hsep α hα.1 x hx hxH
    exact Set.mem_iUnion.mpr ⟨i, α, hα.1.1, hα.2, rfl, hi⟩
  refine ⟨hball, ?_⟩
  intro u hu
  obtain ⟨r, hr, hsub, hfin⟩ := hball u hu
  /- Step 2.1: establish openness in the specified induced topology. -/
  have hcoords : Continuous (fun f : Θ =>
      ArtinNormalisers.Theorem18.dualCoordinates f.val) := continuous_induced_dom
  have hopen : IsOpen (ball u r) := by
    apply isOpen_lt _ continuous_const
    exact continuous_finsetSum Finset.univ (fun i _ =>
      (((continuous_apply i).comp hcoords).sub continuous_const).pow 2)
  have hself : u ∈ ball u r := by
    change (∑ i : S, (_ - _) ^ 2) < r ^ 2
    simpa only [sub_self, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] using
      (sq_pos_of_pos hr)
  /- Step 2.1: an open subset of the cone lies in its interior. Portal
     step 1.2's convexity proof is unnecessary for the translated endpoint,
     which does not assert convexity. -/
  have hinside : ball u r ⊆ interior cone := interior_maximal hsub hopen
  refine ⟨ball u r, hopen, hself, hinside, ?_⟩
  /- Restriction to hyperplanes meeting the interior preserves finiteness. -/
  exact hfin.subset (fun H hH => ⟨hH.1, hH.2.2⟩))
