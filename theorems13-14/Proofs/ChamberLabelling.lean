import Mathlib
import ArtinDeligne
import Proofs.RelativeCone
import Proofs.RelativeLocalFiniteness

theorem ChamberLabelling : (∀ {S : Type*} [Finite S] (M : CoxeterMatrix S) (J : Set S),
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
  intro S _ M J
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
