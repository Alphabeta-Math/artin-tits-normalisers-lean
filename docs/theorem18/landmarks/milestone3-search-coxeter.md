# Landmark 3: actual Coxeter chambers and wall crossings

Source inspection on 2026-11-14. Parent snapshot: `b793bf9dd4c5c9637d8dde51c6a635f849b943c4`. This inventory contains proposed new statements and inspected supplier statements; it is not a build, axiom audit, or kernel-replay acceptance record. No mathematical source, vendor, cache, or configuration was changed in this pass.

## Decision and first authoring targets

Use the existing geometric representation and actual restricted arrangement. Native proofs from pinned mathlib and the already accepted Sign provider are the shortest compatible route. The searches below found useful proof patterns, but no ready theorem identifies these restricted Coxeter chambers with atomic ribbon galleries for every finite Coxeter group.

Author these statements in this order. The names below are **proposed**, not existing APIs.

1. **Uniqueness of a dominant orbit representative**, with arbitrary `I : Type*`, no finite-group assumption:

   ```lean
   theorem dominant_action_unique (M : CoxeterMatrix I) {φ : Dual I}
       (hφ : IsDominant φ) (w : M.Group)
       (hwφ : IsDominant (dualAction M w φ)) :
       dualAction M w φ = φ
   ```

   This is a direct extension of the proof of `Landmark1.dominant_fixed_iff`. Set `ψ = dualAction M w φ`; a left descent `i` of `w` makes `ρ(w⁻¹) αᵢ` negative. Dominance of `φ` gives `ψ αᵢ ≤ 0`, dominance of `ψ` gives equality, so the simple reflection fixes `ψ`. Apply induction to `sᵢ*w`. The existing `dominant_fixed_iff` then gives `w ∈ W_(zeroIndices φ)`. This avoids the crystallographic restriction of the inspected upstream uniqueness theorem.

2. **Sign cells are the actual connected chambers**. On `E := relativeSubspace J`, define

   ```lean
   realRegularSet M J := {φ : E | Landmark1.realRelativeRegular M J φ}
   sameRootSigns M J (φ ψ : E) :=
     ∀ r ∈ retainedRoots M J, (0 < φ.val r ↔ 0 < ψ.val r)
   ```

   For regular `φ`, prove

   ```lean
   connectedComponentIn (realRegularSet M J) φ =
     {ψ | ψ ∈ realRegularSet M J ∧ sameRootSigns M J φ ψ}
   ```

   The right side is an intersection of strict linear half-spaces, hence convex. A component has constant evaluation sign by `IsPreconnected.mapsTo_Ioi_or_Iio` (or `lt_of_ne`/`gt_of_ne`). Convexity gives the reverse component inclusion. This statement does not need finiteness; openness and finite enumeration do. Use the actual subtype topology and `continuous_evaluation`, rather than importing a second normed model. Then obtain open, convex, path-connected chambers in spherical type; closure is the associated weak sign cell, by a segment from a point of the nonempty strict cell.

3. **Standard facets and their transported versions**. Define

   ```lean
   standardFacet J : Set (Dual I) :=
     {φ | (∀ i ∈ J, φ (simpleRoot i) = 0) ∧
       ∀ i ∉ J, 0 < φ (simpleRoot i)}
   ```

   Prove its canonical point is `canonicalDominant J`, its image in `relativeSubspace J` is nonempty/open/convex, and every point there is `realRelativeRegular`. For the last assertion use the Sign root dichotomy: a positive root is coordinatewise nonnegative; a retained root has a nonzero coefficient outside `J`; a strict positive evaluation there makes the finite sum strictly positive. Negative roots follow by negation. The coefficient-support/annihilator equivalence is a genuine small bridge still to author.

   For `[Finite M.Group]`, `exists_dominant_dualAction` and point-stabilizer conjugation show every actual regular point is in a transported standard facet `dualAction M w '' standardFacet K` with `w * W_K * w⁻¹ = W_J`. Prove that such a facet is a full sign cell, hence a chamber; orbit uniqueness gives uniqueness modulo its pointwise parabolic stabilizer. Do not equate the conjugacy class of subsets with all subsets of the same cardinality.

4. **The elementary geometric wall**, with `a ∉ J`, `T = insert a J`, `K = parabolicTwistImage M T J`, and `x = Artin.projection M (elementaryMu M J a)`. In the fixed flat `Θ_J`, prove that `standardFacet J` and `dualAction M x '' standardFacet K` are distinct adjacent chambers, with common wall flat `Θ_T`. A useful first local lemma is:

   ```lean
   ∀ r ∈ retainedRoots M J,
     canonicalDominant T r = 0 →
       restrictedHyperplane J r = restrictedHyperplane J (simpleRoot a)
   ```

   Indeed the root-sign dichotomy and zero evaluation at `canonicalDominant T` force its support into `T`; on `Θ_J` its evaluation is its `a` coefficient times evaluation at `αₐ`. Retention makes that coefficient nonzero. Thus this point lies on exactly one *distinct* restricted hyperplane. Prove codimension one by the coordinate model, closure incidence for both facets, and their distinction. This supplies genuine adjacency without assuming it as a ribbon axiom. Distinction needs the actual nonparabolic/minimal representative fact for `x`; it is an explicit proof obligation, not a consequence merely of Artin degree positivity.

5. **Gallery distance and geodesicity**, after the preceding geometric facts. Define separating hyperplanes as actual distinct elements of `restrictedArrangement M J` on which two chamber signs differ. Prove adjacency changes exactly one such sign, gallery length is bounded below by their number, and a suitable generic segment gives a gallery crossing each separator once. Then establish the relative inversion/separation formula for transported facets, so the existing length-additive pair-lcm atomic words become actual geodesic galleries. `AtomicCoxeter` alone does not supply this conclusion. In particular, do not identify one atomic edge with Coxeter length one: its weight is `ℓ(π μ)`, which can be larger than one.

All five stages retain arbitrary index universes. Obtain `Finite I` from `Geometry.finite_index M`, then use `Fintype.ofFinite` locally where finite intersections/sums are needed. Avoid `I : Type` restrictions and unnecessary reindexing of geometry. For `J = univ`, `Θ_J = 0`, there are no retained hyperplanes and exactly one chamber; there are no outside atomic labels. For `J = ∅` these definitions recover the ordinary dual chamber arrangement. The rank-zero case is included.

## Existing actual models and accepted local inputs

Inspected the complete relevant parent files, not just their descriptions:

* `ArtinNormalisers/Theorem18/Geometry.lean`: `Vector I := I →₀ ℝ`; `Dual I := Module.Dual ℝ (Vector I)`; topology induced by `dualCoordinatesHomeomorph : Dual I ≃ₜ (I → ℝ)`. `relativeSubspace J` is the submodule annihilating the selected simple roots. `root M w i := M.toCoxeterSystem.geometricRepresentation w (simpleRoot i)`. `roots M` consists of these actual orbit roots; `retainedRoots M J` additionally requires a nonzero restriction to the flat. `restrictedHyperplane J r` is the kernel of that restriction and `restrictedArrangement M J` its image over retained roots, so repeated/proportional roots give one actual hyperplane. `Complement M J` is the subtype of pairs of real flat points on no `H × H`. `finite_index`, `roots_finite`, `retainedRoots_finite`, and openness of the actual complement are already proved under `[Finite M.Group]`.
* `ArtinNormalisers/Theorem18/NormalizerAction.lean`: `dualAction M : Representation ℝ M.Group (Dual I)` satisfies `dualAction M w φ v = φ (ρ(w⁻¹) v)`. `mem_relativeSubspace_iff_fixed` identifies the flat with the pointwise fixed space of the actual generated parabolic. The actual normalizer quotient acts through `quotientRepresentation` on the flat and `quotientComplementAction` on the complement; continuity is proved in the coordinate topology. `OrbitSpace` is the actual orbit-relation quotient with quotient topology.
* `landmarks/ArtinLandmarks/Dominant.lean`: `IsDominant φ := ∀ i, 0 ≤ φ (simpleRoot i)`; `zeroIndices φ := {i | φ (simpleRoot i) = 0}`. Literal key conclusion:

  ```lean
  dominant_fixed_iff (hφ : IsDominant φ) (w : M.Group) :
    dualAction M w φ = φ ↔
      w ∈ Artin.coxeterParabolic M (zeroIndices φ)
  ```

  Also `canonicalDominant_fixed_iff` and `pointwise_flat_fixed_iff` for every `J`, with no finite-group assumption.
* `landmarks/ArtinLandmarks/RegularStabilizer.lean`: under `[Finite M.Group]`,

  ```lean
  exists_dominant_dualAction (φ : Dual I) :
    ∃ u, IsDominant (dualAction M u φ)
  realRelativeRegular M J (φ : relativeSubspace J) : Prop :=
    ∀ r ∈ retainedRoots M J, φ.val r ≠ 0
  realRelativeRegular_fixed_iff φ hφ g :
    dualAction M g φ.val = φ.val ↔ g ∈ Artin.coxeterParabolic M J
  ```

* `landmarks/ArtinLandmarks/Covering.lean` proves actual complement-pair stabilizers, free quotient action, actual orbit covering, and its fundamental-group short exact sequence. It defines no real chamber, facet, crossing, or gallery.
* `ribbons/ArtinRibbons/AtomicCoxeter.lean`: `projection_positiveToParent`, `projection_parentSimpleLift`, `degree_eq_coxeterLength_of_simple`, `elementaryMu_degree_eq_coxeterLength`, and

  ```lean
  AtomicWord.coxeter_length_additive_of_simple (p : AtomicWord M X Y)
      (h : ∃ w, p.eval = positiveToParent M (positiveSimpleLift M w)) :
    M.toCoxeterSystem.length (Artin.projection M p.eval) = p.coxeterWeight
  AtomicWord.pairLcm_coxeter_length_additive p a b
      (he : p.eval = pairRibbonLcm M X.indices a b) :
    M.toCoxeterSystem.length (Artin.projection M p.eval) = p.coxeterWeight
  ```

  Here `coxeterWeight` is the sum of the Coxeter lengths of the traversed elementary projections. `AtomicWord.length` counts atomic edges and is a different quantity. `RibbonLcm.pairRibbonLcm_weakPrefix_join` already proves the algebraic weak-prefix join for the two longest-element ratios; no upstream weak-order geometry needs to be invented as a hypothesis.

**Action convention.** An actual ribbon `r : J → K` conjugates `W_J` to `W_K` by `x⁻¹ W_J x`, for `x = π(r)`. Consequently the target chamber drawn in the *source* flat is `x · C_K ⊆ Θ_J`. Appending `s : K → L` gives `x y · C_L`, agreeing with `AtomicWord.eval` putting the first traversed label on the left. Neither this convention nor geometric equivariance should be silently inverted.

## Pinned supplier inspection

Mathlib pin: `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`, inspected at `/tmp/artin-mathlib-audit`. TauCeti accepted pin: `62bbc0596dc3539d488232e4e924a338548ea0a9`, inspected at `/tmp/lemma28-full-search/tauceti`. The accepted geometric Sign closure is already available locally under the relocated `ArtinLandmarkVendor.Geometric.Sign` import; it must not be duplicated or replaced for this task.

### Directly useful mathlib APIs

`Mathlib/Topology/Connected/Basic.lean` contains the following literal generic statements (usual topology variables suppressed):

```lean
IsPreconnected.mapsTo_Ioi_or_Iio (hs : IsPreconnected s)
    (hf : ContinuousOn f s) (hfb : ∀ x ∈ s, f x ≠ b) :
  Set.MapsTo f s (Set.Ioi b) ∨ Set.MapsTo f s (Set.Iio b)
IsPreconnected.lt_of_ne (hs : IsPreconnected s) (hf : ContinuousOn f s)
    (hfb : ∀ x ∈ s, f x ≠ b) (hfx : ∃ x ∈ s, b < f x)
    (hx : x ∈ s) : b < f x
IsPreconnected.subset_connectedComponentIn (hs : IsPreconnected s)
    (hxs : x ∈ s) (hsF : s ⊆ F) : s ⊆ connectedComponentIn F x
```

Also `connectedComponentIn_subset`, `isPreconnected_connectedComponentIn`, `ContinuousOn.image_connectedComponentIn_subset`. `Mathlib/Analysis/Convex/Basic.lean` has `convex_iInter`, `convex_halfSpace_lt`, `convex_halfSpace_gt` and affine/linear preimages of convex intervals. `Mathlib/Analysis/Convex/PathConnected.lean` has

```lean
Convex.isPathConnected (hconv : Convex ℝ s) (hne : s.Nonempty) : IsPathConnected s
Convex.isPreconnected (h : Convex ℝ s) : IsPreconnected s
```

These work on real topological vector spaces; no norm or integral lattice is needed for the native chamber proofs. `Mathlib/GroupTheory/Coxeter/Inversion.lean` supplies `IsReflection`, left/right inversions, inversion sequences and nodup of both sequences for a reduced word; it does not identify these with actual separating geometric hyperplanes. `Length.lean` supplies reduced expressions, prefix/tail reducedness, descent criteria, `length_inv`, and multiplication bounds. These are algebraic inputs only.

### TauCeti Sign: compatible and already accepted

`TauCeti/GroupTheory/Coxeter/Geometric/Sign.lean`, namespace `CoxeterSystem`, arbitrary `I : Type*`, group `W`, `cs : CoxeterSystem M W`:

```lean
geometricRepresentation_single_pos_iff (w : W) (i : I) :
  0 < cs.geometricRepresentation w (Finsupp.single i 1) ↔ ¬cs.IsRightDescent w i
geometricRepresentation_single_neg_iff (w : W) (i : I) :
  cs.geometricRepresentation w (Finsupp.single i 1) < 0 ↔ cs.IsRightDescent w i
pos_or_neg_of_mem_geometricRoots (hv : v ∈ cs.geometricRoots) : 0 < v ∨ v < 0
```

`geometricRoots` is literally `{v | ∃ w i, ρ(w)(single i 1) = v}`; its positivity is the coordinatewise Finsupp order. Root invariance, negation invariance, norm one, simple-reflection preservation of other positive roots, and faithful representation are also proved. This is the correct noncrystallographic supplier.

`Geometric/Transport.lean` gives `mapDomain_geometricRepresentation`, `geometricRepresentation_reindex`, and `geometricRepresentation_reindexGroupEquiv_symm`; those are optional transport APIs if a finite-index equivalence is needed. They do not construct chamber geometry.

### TauCeti RootPairing chambers: conclusions inspected, extra hypotheses incompatible

`LinearAlgebra/RootSystem/Chamber.lean` defines `RootPairing.IsRegularWeight P x := ∀ i, P.coroot' i x ≠ 0`, `dominantChamber P b := {x | ∀ i ∈ b.support, 0 ≤ P.coroot' i x}`, and its strict version. `exists_mem_dominantChamber_of_finite_weylGroup` concludes `∃ w : P.weylGroup, w • x ∈ dominantChamber P b`, but its section assumes `[Finite ι] [P.IsCrystallographic] [P.IsReduced]` in addition to ordered-ring/module conditions and finite Weyl group.

`LinearAlgebra/RootSystem/FundamentalDomain.lean` proves

```lean
smul_eq_self_of_smul_mem_dominantChamber (w : P.weylGroup)
    (hx : x ∈ dominantChamber P b) (hw : w • x ∈ dominantChamber P b) : w • x = x
```

The section assumes `[LinearOrder R] [IsStrictOrderedRing R] [Finite ι] [P.IsCrystallographic] [P.IsReduced] [P.flip.IsReduced]`. `Weyl/Chamber.lean` similarly proves disjointness, bijection with Weyl group, finite-group coverage of regular weights, and

```lean
existsUnique_mem_openWeylChamber_of_finite_weylGroup
    (hx : IsRegularWeight P x) : ∃! w : P.weylGroup, x ∈ openWeylChamber P b w
```

under the same crystallographic/reduced conditions. These conclusions are not directly usable for arbitrary spherical `M` including `H₃`, `H₄`, and `I₂(m)`. No conversion from the actual Finsupp representation to such a crystallographic root pairing is available or possible uniformly. Reuse their mathematical patterns by a fresh Coxeter Sign proof, not their hypotheses as an asserted global instance.

`Analysis/Convex/SimplicialComplex/Arrangement.lean` proves finite simplicial subdivision respecting affine sign choices; it does not define the Coxeter chamber/galleries required here.

## Fresh GitHub checks and source candidates

GitHub code queries used actual `.lean` hits, not READMEs: `"Coxeter" "chamber"`, `"hyperplane" "chamber"`, `"wall" "Coxeter"`, and `"gallery" "hyperplane"`, excluding already inspected mirrors as needed. Search results are a bounded search, not a proof that no other formalization exists. JSON and downloaded source candidates are staged only under `/tmp/artin-landmark3-search/`.

* **TauCeti remote HEAD** was freshly pinned as `130523811f55c80f533e6024e190b945755f93c5`. The recursive source tree has no additional generic Coxeter chamber/gallery module. Downloaded HEAD versions of Sign, RootSystem/Chamber, Weyl/Chamber, and FundamentalDomain are **byte-identical** to the accepted `62bbc...` pin. SHA256 respectively: `fa162d417fcd0e91ec061056ac696119ee263c3fba15e4f22540016202596bf1`, `4b6c0bbedb541a75ffe025769f17784c935152c1b297ee6dfdfd9c54b6381461`, `7d219ec841ebf53055b9065dd65f7850e27eac40919fb8f50e810bb5b5d8fb83`, `a88d6cc37c7b7c190309e2bc2c9ed2a700201a11b61625de3082f3346ae7be77`. No pin upgrade is justified for these APIs.
* **`slef/lean-unfoldings`**, inspected commit `4b549dc5d3bee5d7bf0b6ac4abb3e19701e15f67`, source `Unfoldings/Geometry/AffineArrangement.lean` (9,524 bytes). Namespace `Unfoldings.AffineArrangement`; with `[NormedAddCommGroup E] [NormedSpace ℝ E]`, defines

  ```lean
  signed (f : E →ᵃ[ℝ] ℝ) (positive : Bool) := if positive then f else -f
  chamber (f : ι → E →ᵃ[ℝ] ℝ) (signs : ι → Bool) :=
    {x | ∀ i, 0 < signed (f i) (signs i) x}
  closedChamber ... := {x | ∀ i, 0 ≤ signed (f i) (signs i) x}
  ```

  `convex_chamber` drops both finite-dimensionality and finite-index assumptions. `closure_chamber f signs (nonempty : (chamber f signs).Nonempty) : closure (chamber f signs) = closedChamber f signs` assumes finite-dimensional real normed space, but drops `[Finite ι]`. `isOpen_chamber`, `dense_regular`, and `interior_closedChamber` use finite dimension and finite family. Direct imports are four mathlib modules: `Analysis.Normed.Affine.AddTorsorBases`, `Analysis.Convex.Topology`, `Topology.Connected.Basic`, `Topology.Baire.Lemmas`. The related `ArrangementBoundary.lean` concerns regular closed sets with finite hyperplane-supported boundary, not Coxeter galleries. **License not identified:** source has no license header and GitHub license API returned 404. Therefore do not vendor/copy this source without resolving permission. It is currently proof-pattern evidence only. No compatibility build, axiom audit or replay was attempted. Native equivalents require no second norm topology and are short.
* **`AxiomMath/CFSG`**, inspected commit `5437cdc31389dd9aeaa5c2a9465a4e164f8dea33`, Apache-2.0. `CFSG/Monster/B/Geometry/ChamberModel.lean` (10,598 bytes) assumes an abstract `IsWeylDistanceBuilding cs δ`. It defines `IsChamberModel cs δ X f := Function.Bijective f ∧ ∀ x y i, (δ x y = cs.simple i ↔ x ≠ y ∧ X.adj i (f x) (f y))`. Its theorem `IsChamberModel.length_le` concludes `cs.length (δ x y) ≤ γ.length` for a gallery in `X`, **given** that building axiom and model identification. It neither constructs the actual real arrangement nor proves that its adjacency is the proposed Coxeter distance. Using this as the missing chamber identification would assume the bridge. No vendoring/build proposed.
* **`dzackgarza/lean-categories`**, inspected commit `064b5cfdae80fd27c7af1b0c9a7a8bbc5547e55b`, `LeanCategories/Lattices/Valued/WeylChambers.lean` (88,793 bytes). `chamberOf L t x := connectedComponentIn (weylRegularLocus L t) x`; the regular locus lies in a Lorentzian positive-cone sheet and avoids mirrors of negative reflective integral lattice roots. It proves sign constancy, `chamberOf_eq_of_pos_mul`, `convex_chamberOf` with `(integralSignature L).1 = 1`, and `chamberOf_eq_iff_mirrorSeparating_eq_empty`. This is a different lattice/root/cone model. The all-finite-Coxeter comparison is absent. GitHub license API returned 404; no supplier acceptance or verbatim reuse.
* **`yuma-mizuno-lean/Mei`**, inspected commit `318d6e772bda1bfb3780c46cc18f209b5c0dbafb`, Apache-2.0. `Mei/Geometry/Convex/PolyhedralComplex/RegularLocus.lean` (9,781 bytes) uses `C : FinitePolyhedralComplex h`, where `{i : N →+ V}` and `h : TauCeti.Toric.IsIntegralLattice i`. It proves `singularSupport_walls_eq_support_codimensionAtLeast_two (hC : C.support = univ)` and generic regular-locus/wall-path facts for a finite integral polyhedral complex. A finite Coxeter restricted arrangement complex with this integral structure has not been constructed; noncrystallographic reflection geometry cannot be silently replaced by a rational fan. The generic wall-path arguments may suggest a later independent abstraction, but this is not a direct supplier for the current model.
* Other hits were Weyl/root-system mirrors, special cluster/lattice developments, or unrelated uses of “chamber”. The `"gallery" "hyperplane"` query did not reveal a directly applicable Coxeter arrangement gallery theorem. Earlier known `nickgou-nuke/info-geometry-lean` commit `a392af178af1fe2bcba2ba39eb405700c6ee103c` appears again for geometric representation code, not new chamber identification.

None of these fresh candidates has passed a project compatibility build, transitive axiom audit, or independent kernel replay in this task. The immediate authoring decision is to keep the existing representation and prove the listed bridges using accepted suppliers, before any Deligne/Salvetti/fundamental-groupoid comparison.
