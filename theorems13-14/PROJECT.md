# Project

## RelativeCone: Tits cone intersection and relative arrangement

Prerequisite; compiled and axiom-checked.

### Article

For J ⊆ Γ₀, let Θ_J = {f ∈ V*: f(α_j)=0 for every j∈J}. Define Cone(J)=Cone∩Θ_J, taking its interior in Θ_J. Define Φ^J={α∈Φ: Θ_J is not contained in H_α}=Φ\Φ_J and H^J={H_α∩Θ_J: α∈Φ^J_+}, counting coincident traces once.

[§3.1, printed p. 7, equations (3.1)–(3.3); §1.1.2, printed p. 2.](https://arxiv.org/pdf/2509.21915#page=7)

### Alphabeta Math

The same relative cone, roots and distinct hyperplane traces, explicitly using finite Γ₀ and the induced coordinate Euclidean topology. Neither W nor W_J is required to be finite.

[Definition and Source notes of def-relative-cone-artin-tits-normalisers.](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-def-relative-cone-artin-tits-normalisers)

### Lean translation

Translation source: portal. Explicit user direction selects the finite-rank definition at https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-def-relative-cone-artin-tits-normalisers. The report at https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects was checked and does not identify this definition as defective. Finite rank is user-directed, not a reported correction; neither W nor W_J is assumed finite. Components are Cone(J), its interior in the induced coordinate Euclidean topology on Θ_J, Φ^J, Φ^J_+, Φ^J_-, and the set of distinct restricted hyperplanes. [Defect report](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects).

```lean
def RelativeCone : ∀ {S : Type*} [Finite S] (M : CoxeterMatrix S) (J : Set S), let Θ := ArtinNormalisers.Theorem18.relativeSubspace J; let V := ArtinNormalisers.Theorem18.Vector S; Set Θ × Set Θ × Set V × Set V × Set V × Set (Submodule Real Θ) := fun {S} _ M J =>
  let Θ := ArtinNormalisers.Theorem18.relativeSubspace J
  let V := ArtinNormalisers.Theorem18.Vector S
  letI : TopologicalSpace Θ :=
    TopologicalSpace.induced
      (fun f : Θ => ArtinNormalisers.Theorem18.dualCoordinates f.val)
      (inferInstance : TopologicalSpace (S → Real))
  let titsCone : Set (ArtinNormalisers.Theorem18.Dual S) :=
    { f | ∃ (w : CoxeterMatrix.Group M) (g : ArtinNormalisers.Theorem18.Dual S),
        ArtinNormalisers.Landmark1.IsDominant g ∧
        ArtinNormalisers.Theorem18.dualAction M w g = f }
  let cone : Set Θ := { f | f.val ∈ titsCone }
  let relativeRoots : Set V := ArtinNormalisers.Theorem18.retainedRoots M J
  let positiveRelativeRoots : Set V := { r | r ∈ relativeRoots ∧ 0 < r }
  let negativeRelativeRoots : Set V := { r | r ∈ relativeRoots ∧ r < 0 }
  let arrangement : Set (Submodule Real Θ) :=
    Set.image (ArtinNormalisers.Theorem18.restrictedHyperplane J) positiveRelativeRoots
  (cone, interior cone, relativeRoots, positiveRelativeRoots, negativeRelativeRoots, arrangement)
```

Immediate internal dependencies: none.

Existing repository dependencies: none.

Immediate external dependencies: existing-vector, existing-dual, existing-relative-subspace, existing-dual-coordinates, existing-retained-roots, existing-restricted-hyperplane, existing-dual-action, existing-dominant, mathlib-coxeter-group, mathlib-induced-topology, mathlib-interior, mathlib-set-image, relative-cone-mathlib-infrastructure, relative-cone-lean-infrastructure (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [translation](translations/RelativeCone.json), [proof](Proofs/RelativeCone.lean), [compilation evidence](evidence/RelativeCone-compile.json).

## RelativeLocalFiniteness: Local finiteness in the relative interior

Prerequisite; compiled and axiom-checked.

### Article

Every u∈Cone(J)° belongs to an open ball in Cone(J) meeting only finitely many members of H^J. Consequently (Cone(J)°,H^J) is locally finite.

[Proposition 3.6, printed p. 9; Remark 3.7 distinguishes this from ambient local finiteness.](https://arxiv.org/pdf/2509.21915#page=9)

### Alphabeta Math

For finite Γ₀ and arbitrary J, every point of the relative interior has a relative Euclidean ball contained in Cone(J) meeting finitely many distinct relative hyperplanes. No spherical-type hypothesis is imposed.

[Statement and Facts & Assumptions of prop-relative-local-finiteness-artin-tits-normalisers.](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-prop-relative-local-finiteness-artin-tits-normalisers)

### Lean translation

Translation source: portal. Explicit user direction selects the finite-rank geometric endpoint at https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-prop-relative-local-finiteness-artin-tits-normalisers. The report at https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects, finding pdf-prop36-ambient-ball-inference, identifies a defective ambient-ball inference in the proof and explicitly preserves the proposition’s relative local-finiteness conclusion. Its correction uses a relative Euclidean ball in Θ_J contained in Cone(J), meeting finitely many distinct restricted hyperplanes. Finite rank is user-directed, not a reported statement correction; neither W nor W_J is required finite. The coordinate-square formula specifies Euclidean balls, and the second conjunct expresses local finiteness of the interior arrangement restricted to hyperplanes meeting the interior. [Defect report](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects).

```lean
theorem RelativeLocalFiniteness : ∀ {S : Type*} [Finite S] (M : CoxeterMatrix S) (J : Set S),
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
      Set.Nonempty (U ∩ (H : Set Θ)) })
```

Immediate internal dependencies: RelativeCone.

Existing repository dependencies: none.

Immediate external dependencies: rlf-root-signs, rlf-dominant, rlf-coordinate-geometry, rlf-dual-action, rlf-geometric-action, rlf-mathlib, rlf-lean-core (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [translation](translations/RelativeLocalFiniteness.json), [proof](Proofs/RelativeLocalFiniteness.lean), [compilation evidence](evidence/RelativeLocalFiniteness-compile.json).

## ChamberLabelling: Minimal coset labels classify relative chambers

Prerequisite; compiled and axiom-checked.

### Article

The map (x,I)↦xC_I bijects the chambers of (Cone(J)°,H^J) with Cham(J)={(x,I): W_Jx=xW_I and x has minimum length in xW_I}. Here C_I={f∈Θ_I: f(α_i)>0 for i∉I}.

[Theorem 3.9 and equation (3.10), printed pp. 9–10; equation (3.2), printed p. 7.](https://arxiv.org/pdf/2509.21915#page=9)

### Alphabeta Math

The same chamber-labelling bijection under the finite-rank geometric convention, for arbitrary Coxeter type and arbitrary J. The algebraic label set itself is available at arbitrary rank.

[Statement, Facts & Assumptions and Source notes of thm-chamber-labelling-artin-tits-normalisers.](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-thm-chamber-labelling-artin-tits-normalisers)

### Lean translation

Translation source: portal. Explicit user direction selects the finite-rank geometric endpoint at https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-thm-chamber-labelling-artin-tits-normalisers, using the induced coordinate Euclidean topology on Θ_J. The report at https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects was checked and does not identify Theorem 3.9’s statement as defective. Finite rank is user-directed, not a reported correction. Coxeter type and J are arbitrary; neither W nor W_J is required finite. The algebraic label conditions retain their arbitrary-rank meaning. [Defect report](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects).

```lean
theorem ChamberLabelling : ∀ {S : Type*} [Finite S] (M : CoxeterMatrix S) (J : Set S),
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
  Set.BijOn labelRegion labels chambers
```

Immediate internal dependencies: RelativeCone, RelativeLocalFiniteness.

Existing repository dependencies: none.

Immediate external dependencies: cl-project-1, cl-project-2, cl-project-3, cl-project-4, cl-project-5, cl-project-6, cl-project-7, cl-project-8, cl-project-9, cl-project-10, cl-project-11, cl-project-12, cl-project-13, cl-mathlib, cl-lean-core (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [translation](translations/ChamberLabelling.json), [proof](Proofs/ChamberLabelling.lean), [compilation evidence](evidence/ChamberLabelling-compile.json).

## SimpleWallCrossings: Elementary crossing elements from spherical components

Prerequisite; compiled and axiom-checked.

### Article

For a∉I, let D=[I,a] be the component containing a in the diagram induced on I∪{a}. When W_D is finite, define v_{a,I}=w_{D\{a}}w_D, K=(I∪{a})\{ι_D(a)}, and ω_{a,I}(x,I)=(xv_{a,I},K). The opposition permutation satisfies w_Dα_i=−α_{ι_D(i)}. Finiteness is required of W_D, not of W_I or W_{I∪{a}}.

[Notation 3.13 and equations (3.14)–(3.15), printed p. 10; Notation 2.5 and equation (2.6), printed p. 5.](https://arxiv.org/pdf/2509.21915#page=10)

### Alphabeta Math

The same component-based construction on algebraic labels. Its definition initially gives a pair in W×P(Γ₀); preservation of chamber labels and geometric adjacency require subsequent results.

[Definition of def-simple-wall-crossing-artin-tits-normalisers.](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-def-simple-wall-crossing-artin-tits-normalisers)

### Lean translation

Translation source: article. The report rejects a separate auxiliary root characterization on p. 10; this endpoint uses the retained longest-element definition and the portal construction. [Defect report](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects).

```lean
def SimpleWallCrossings : ∀ (S : Type _) (W : Type _) [Group W] (M : CoxeterMatrix S) (cs : CoxeterSystem M W) (I : Set S) (a : S) (_ha : a ∉ I), let D : Set S := {b | b ∈ Set.insert a I ∧ Relation.ReflTransGen (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b}; Finite (CoxeterSystem.parabolic cs D) → W × Set S × (W → W × Set S) := fun S W _inst M cs I a _ha =>
  let D : Set S := {b | b ∈ Set.insert a I ∧ Relation.ReflTransGen (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b}
  fun hD =>
    letI : Finite (CoxeterSystem.parabolic cs D) := hD
    let longest : (L : Set S) → L ⊆ D → W := fun L hL =>
      letI : Finite (CoxeterSystem.parabolic cs L) :=
        Finite.of_injective
          (fun w : CoxeterSystem.parabolic cs L => (⟨(w : W), (CoxeterSystem.parabolic_mono cs hL) w.property⟩ : CoxeterSystem.parabolic cs D))
          (fun _ _ h => Subtype.ext (congrArg (fun z : CoxeterSystem.parabolic cs D => (z : W)) h))
      (Classical.choose (Finite.exists_max (fun w : CoxeterSystem.parabolic cs L => CoxeterSystem.length cs (w : W)))).val
    let wD := longest D (fun _ h => h)
    let opposition : Equiv D D :=
      @Classical.epsilon (Equiv D D) ⟨Equiv.refl D⟩ (fun e => ∀ i : D, CoxeterSystem.geometricRepresentation cs wD (Finsupp.single (i : S) (1 : Real)) = -Finsupp.single (e i : S) (1 : Real))
    let aD : D := ⟨a, ⟨Set.mem_insert a I, Relation.ReflTransGen.refl⟩⟩
    let v := longest (D \ {a}) Set.sdiff_subset * wD
    let K : Set S := Set.insert a I \ {(opposition aD : S)}
    (v, K, fun x => (x * v, K))
```

Immediate internal dependencies: none.

Existing repository dependencies: none.

Immediate external dependencies: parabolic, parabolic-mono, geometric-representation, coxeter-length, finite-injection, finite-maximum, equiv-refl, simple-root, component-path, insert-membership, difference-subset, choose, epsilon, subtype-ext, congr-arg (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [translation](translations/SimpleWallCrossings.json), [proof](Proofs/SimpleWallCrossings.lean), [compilation evidence](evidence/SimpleWallCrossings-compile.json).

## AdjacentWallFormula: Adjacent chambers and inverse elementary crossings

Prerequisite; compiled and axiom-checked.

### Article

For adjacent chambers (x,I),(y,K), the common wall has unique describing indices a∉I and a′∉K, with I∪{a}=K∪{a′}. Their crossing components coincide and are spherical. The crossings satisfy ω_{a,I}(x,I)=(y,K), ω_{a′,K}(y,K)=(x,I), and v_{a,I}v_{a′,K}=v_{a′,K}v_{a,I}=1.

[Proposition 3.17 and following sentence, printed p. 11.](https://arxiv.org/pdf/2509.21915#page=11)

### Alphabeta Math

In finite rank, the common closed wall is the closure of xC_{I∪{a}} and of yC_{K∪{a′}}. The describing indices, finite crossing components, prescribed opposite labels and inverse products have the stated properties. Neither W_I nor W_{I∪{a}} is assumed finite.

[Statement and Source notes of prop-adjacent-wall-formula-artin-tits-normalisers.](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-prop-adjacent-wall-formula-artin-tits-normalisers)

### Lean translation

Translation source: portal. The report at https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects identifies Proposition 3.17’s statement wording in finding pdf-adjacency-uniqueness-wording. Its exact correction is: “State uniqueness for the indices describing the specified common wall, then list the subset equality among their properties.” This translates the corrected endpoint at https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-prop-adjacent-wall-formula-artin-tits-normalisers. Closures use the induced coordinate Euclidean topology on Θ_J; adjacency means distinct chambers sharing a closed wall of affine codimension one. Finite rank follows explicit user direction for geometric items, not a reported rank defect. Coxeter type and J remain arbitrary; neither W, W_I nor W_{I∪{a}} is assumed finite. [Defect report](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects).

```lean
theorem AdjacentWallFormula : ∀ {S : Type*} [Finite S] (M : CoxeterMatrix S) (J : Set S),
  let W := CoxeterMatrix.Group M
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
    ∀ F : Set Θ, region x I ≠ region y K → wall (region x I) F → wall (region y K) F →
    ∃ (a a' : S) (ha : a ∉ I) (ha' : a' ∉ K),
      F = closure (region x (Set.insert a I)) ∧
      F = closure (region y (Set.insert a' K)) ∧
      (∀ c : S, c ∉ I → F = closure (region x (Set.insert c I)) → c = a) ∧
      (∀ c : S, c ∉ K → F = closure (region y (Set.insert c K)) → c = a') ∧
      Set.insert a I = Set.insert a' K ∧
      component I a = component K a' ∧
      CoxeterSystem.parabolic cs (component I a) = CoxeterSystem.parabolic cs (component K a') ∧
      ∃ (hD : Finite (CoxeterSystem.parabolic cs (component I a)))
        (hD' : Finite (CoxeterSystem.parabolic cs (component K a'))),
        let forward := SimpleWallCrossings S W M cs I a ha hD
        let reverse := SimpleWallCrossings S W M cs K a' ha' hD'
        forward.2.2 x = (y, K) ∧ reverse.2.2 y = (x, I) ∧
        K = Set.insert a I \ {a'} ∧ I = Set.insert a' K \ {a} ∧
        forward.1 * reverse.1 = (1 : W) ∧ reverse.1 * forward.1 = (1 : W)
```

Immediate internal dependencies: ChamberLabelling, SimpleWallCrossings.

Existing repository dependencies: none.

Immediate external dependencies: awf-complete-project, awf-complete-mathlib, awf-complete-lean (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [translation](translations/AdjacentWallFormula.json), [proof](Proofs/AdjacentWallFormula.lean), [compilation evidence](evidence/AdjacentWallFormula-compile.json).

## FiniteWallPaths: Finite crossing paths connect relative chambers

Prerequisite; compiled and axiom-checked.

### Article

Any two chambers are related by a finite sequence of simple wall crossings.

[Lemma 3.20(3) and Remark 3.22, printed p. 11; Remark 3.8, printed p. 9.](https://arxiv.org/pdf/2509.21915#page=11)

### Alphabeta Math

For a finite-rank Coxeter system and arbitrary J, any two relative chambers are joined by finitely many component-based simple crossings. The empty sequence is allowed for equal endpoints.

[Statement and Facts & Assumptions of lem-finite-wall-path-artin-tits-normalisers.](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-finite-wall-path-artin-tits-normalisers)

### Lean translation

Translation source: portal. Explicit user direction selects the finite-rank geometric statement at https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-finite-wall-path-artin-tits-normalisers. The supplied defect report was checked and does not identify Lemma 3.20(3) or Remark 3.22 as defective statements. Finite rank is user-directed, not a reported correction. Label is Cham(J), identified with relative chambers by ChamberLabelling. Every intermediate label remains a chamber, and each step is the prescribed component-based SimpleWallCrossings map. Relation.ReflTransGen allows any finite sequence, including zero crossings for equal endpoints. Coxeter type and J remain arbitrary; finiteness is required only of each crossing component, not of W, W_J or W_{I∪{a}}. [Defect report](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects).

```lean
theorem FiniteWallPaths : ∀ {S : Type*} [Finite S] (M : CoxeterMatrix S) (J : Set S),
  let W := CoxeterMatrix.Group M
  let cs := CoxeterMatrix.toCoxeterSystem M
  let Label := { p : W × Set S //
    Set.image (fun u : W => u * p.1) (CoxeterSystem.parabolic cs J : Set W) =
      Set.image (fun u : W => p.1 * u) (CoxeterSystem.parabolic cs p.2 : Set W) ∧
    CoxeterSystem.IsMinimalCosetRep cs p.2 p.1 }
  let component : Set S → S → Set S := fun I a =>
    { b | b ∈ Set.insert a I ∧ Relation.ReflTransGen
      (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b }
  let crossing : Label → Label → Prop := fun p q =>
    ∃ (a : S) (ha : a ∉ p.val.2)
      (hD : Finite (CoxeterSystem.parabolic cs (component p.val.2 a))),
      (SimpleWallCrossings S W M cs p.val.2 a ha hD).2.2 p.val.1 = q.val
  ∀ p q : Label, Relation.ReflTransGen crossing p q
```

Immediate internal dependencies: RelativeLocalFiniteness, ChamberLabelling, AdjacentWallFormula.

Existing repository dependencies: none.

Immediate external dependencies: fwp-project-positive-transport, fwp-project-root-signs, fwp-project-geometric, fwp-project-parabolic, fwp-mathlib, fwp-lean-core, fwp-embedded-project, fwp-embedded-mathlib, fwp-embedded-lean (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [translation](translations/FiniteWallPaths.json), [proof](Proofs/FiniteWallPaths.lean), [compilation evidence](evidence/FiniteWallPaths-compile.json).

## NormaliserChamberAction: Free normaliser-quotient action on chamber labels

Prerequisite; compiled and axiom-checked.

### Article

For ḡ∈N(W,J)=Norm_W(W_J)/W_J and any representative g, let y be the minimum-length element of gxW_I. Then ḡ·(x,I)=(y,I). Labels with the same second component form one orbit; the action is free and commutes with each defined adjacent crossing ω_{a,I}, preserving its index.

[Lemma 3.24(1)–(4), printed p. 12; underlying linear action in Lemma 3.23, printed p. 12.](https://arxiv.org/pdf/2509.21915#page=12)

### Alphabeta Math

The same free action, fibre-orbit description and crossing equivariance in the finite-rank relative chamber geometry, without requiring W or W_J finite.

[Statement and Facts & Assumptions of lem-normaliser-chamber-action-artin-tits-normalisers.](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-normaliser-chamber-action-artin-tits-normalisers)

### Lean translation

Translation source: portal. Explicit user direction selects the finite-rank geometric endpoint at https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-normaliser-chamber-action-artin-tits-normalisers. The report at https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects was checked and does not identify Lemma 3.24 as defective. Its finding pdf-d4-normaliser-freeness concerns the later D₄ example and explicitly does not refute this lemma. Finite rank is user-directed, not a reported correction. The acting group is Norm_W(W_J)/W_J, with its induced contragredient action on chambers. Closures use the induced coordinate Euclidean topology on Θ_J. Coxeter type and J remain arbitrary; neither W nor W_J is required finite. [Defect report](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects).

```lean
theorem NormaliserChamberAction : ∀ {S : Type*} [Finite S] (M : CoxeterMatrix S) (J : Set S),
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
          (action g q).val)
```

Immediate internal dependencies: RelativeCone, ChamberLabelling, AdjacentWallFormula.

Existing repository dependencies: none.

Immediate external dependencies: nca-round1-lean, nca-round1-mathlib, nca-round1-project-parabolic, nca-round1-project-transport, nca-complete-project, nca-complete-mathlib, nca-complete-lean (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [translation](translations/NormaliserChamberAction.json), [proof](Proofs/NormaliserChamberAction.lean), [compilation evidence](evidence/NormaliserChamberAction-compile.json).

## GeodesicAdditivity: Geodesicity equals Coxeter-length additivity

Prerequisite; compiled and axiom-checked.

### Article

For a chamber path p with consecutive crossing elements v₁,…,v_m and product v_p, p is geodesic if and only if ℓ(v_p)=Σ_i ℓ(v_i). Geodesic means having the minimum number of crossings between its endpoints.

[Proposition 3.29, printed pp. 13–14; path and geodesic conventions in §3.4, printed p. 13.](https://arxiv.org/pdf/2509.21915#page=13)

### Alphabeta Math

The same equivalence for finite-rank relative chamber paths, including the one-chamber path with empty product and sum. Its suppliers include the length/half-space criterion and translation between relative arrangements.

[Statement and Facts & Assumptions of prop-geodesic-additivity-artin-tits-normalisers.](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-prop-geodesic-additivity-artin-tits-normalisers)

### Lean translation

Translation source: portal. Explicit user direction selects the finite-rank geometric endpoint at https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-prop-geodesic-additivity-artin-tits-normalisers. The supplied defect report was checked in full and does not identify Proposition 3.29's statement as defective. Finite rank is user-directed, not a reported correction; Coxeter type and J remain arbitrary, with no finiteness assumption on W or W_J. Labels represent relative chambers via ChamberLabelling, and Step records the prescribed adjacent crossing via SimpleWallCrossings and AdjacentWallFormula. The path predicate enforces consecutive endpoints, and geodesicity explicitly minimizes the number of crossings among all paths with those endpoints. An empty crossing list represents a one-chamber path, with identity product and zero sum. [Defect report](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects).

```lean
theorem GeodesicAdditivity : ∀ {S : Type*} [Finite S] (M : CoxeterMatrix S) (J : Set S),
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
        List.sum (List.map (fun e => CoxeterSystem.length cs (crossing e).1) es))
```

Immediate internal dependencies: RelativeLocalFiniteness, ChamberLabelling, AdjacentWallFormula.

Existing repository dependencies: none.

Immediate external dependencies: ga-conditional-mathlib, ga-conditional-lean, ga-conditional-project, ga-complete-project-artinchambers-positivetransport, ga-complete-project-artinchambers-weakinversions, ga-complete-project-artinlandmarkvendor-geometric-sign, ga-complete-lean-init-bindernamehint, ga-complete-lean-init-bycases, ga-complete-lean-init-classical, ga-complete-lean-init-core, ga-complete-lean-init-data-cast, ga-complete-lean-init-data-function, ga-complete-lean-init-data-int-basic, ga-complete-lean-init-data-int-lemmas, ga-complete-lean-init-data-int-order, ga-complete-lean-init-data-list-basic, ga-complete-lean-init-data-list-lemmas, ga-complete-lean-init-data-list-takedrop, ga-complete-lean-init-data-nat-basic, ga-complete-lean-init-data-nezero, ga-complete-lean-init-data-order-lemmas, ga-complete-lean-init-data-zero, ga-complete-lean-init-ext, ga-complete-lean-init-omega-coeffs, ga-complete-lean-init-omega-constraint, ga-complete-lean-init-omega-int, ga-complete-lean-init-omega-linearcombo, ga-complete-lean-init-prelude, ga-complete-lean-init-proplemmas, ga-complete-lean-init-simplemmas, ga-complete-mathlib-mathlib-algebra-algebra-basic, ga-complete-mathlib-mathlib-algebra-algebra-defs, ga-complete-mathlib-mathlib-algebra-bigoperators-finsupp-basic, ga-complete-mathlib-mathlib-algebra-bigoperators-group-finset-basic, ga-complete-mathlib-mathlib-algebra-bigoperators-group-finset-defs, ga-complete-mathlib-mathlib-algebra-bigoperators-group-finset-piecewise, ga-complete-mathlib-mathlib-algebra-bigoperators-pi, ga-complete-mathlib-mathlib-algebra-charp-defs, ga-complete-mathlib-mathlib-algebra-charzero-defs, ga-complete-mathlib-mathlib-algebra-field-defs, ga-complete-mathlib-mathlib-algebra-group-basic, ga-complete-mathlib-mathlib-algebra-group-commute-defs, ga-complete-mathlib-mathlib-algebra-group-defs, ga-complete-mathlib-mathlib-algebra-group-divinvmonoid, ga-complete-mathlib-mathlib-algebra-group-end, ga-complete-mathlib-mathlib-algebra-group-equiv-defs, ga-complete-mathlib-mathlib-algebra-group-finsupp, ga-complete-mathlib-mathlib-algebra-group-hom-defs, ga-complete-mathlib-mathlib-algebra-group-int-defs, ga-complete-mathlib-mathlib-algebra-group-isapply, ga-complete-mathlib-mathlib-algebra-group-monoid, ga-complete-mathlib-mathlib-algebra-group-nat-defs, ga-complete-mathlib-mathlib-algebra-group-pi-basic, ga-complete-mathlib-mathlib-algebra-group-semiconj-defs, ga-complete-mathlib-mathlib-algebra-group-semigroup, ga-complete-mathlib-mathlib-algebra-group-subgroup-defs, ga-complete-mathlib-mathlib-algebra-group-subgroup-lattice, ga-complete-mathlib-mathlib-algebra-group-subgroup-map, ga-complete-mathlib-mathlib-algebra-group-submonoid-defs, ga-complete-mathlib-mathlib-algebra-group-subsemigroup-defs, ga-complete-mathlib-mathlib-algebra-groupwithzero-action-defs, ga-complete-mathlib-mathlib-algebra-groupwithzero-basic, ga-complete-mathlib-mathlib-algebra-groupwithzero-defs, ga-complete-mathlib-mathlib-algebra-groupwithzero-nat, ga-complete-mathlib-mathlib-algebra-groupwithzero-units-basic, ga-complete-mathlib-mathlib-algebra-module-defs, ga-complete-mathlib-mathlib-algebra-module-linearmap-defs, ga-complete-mathlib-mathlib-algebra-module-linearmap-end, ga-complete-mathlib-mathlib-algebra-module-submodule-basic, ga-complete-mathlib-mathlib-algebra-module-submodule-defs, ga-complete-mathlib-mathlib-algebra-module-submodule-eqlocus, ga-complete-mathlib-mathlib-algebra-module-submodule-ker, ga-complete-mathlib-mathlib-algebra-module-submodule-map, ga-complete-mathlib-mathlib-algebra-nezero, ga-complete-mathlib-mathlib-algebra-order-archimedean-real-basic, ga-complete-mathlib-mathlib-algebra-order-bigoperators-group-finset, ga-complete-mathlib-mathlib-algebra-order-floor-defs, ga-complete-mathlib-mathlib-algebra-order-group-defs, ga-complete-mathlib-mathlib-algebra-order-group-unbundled-basic, ga-complete-mathlib-mathlib-algebra-order-groupwithzero-basic, ga-complete-mathlib-mathlib-algebra-order-groupwithzero-defs, ga-complete-mathlib-mathlib-algebra-order-module-defs, ga-complete-mathlib-mathlib-algebra-order-monoid-defs, ga-complete-mathlib-mathlib-algebra-order-monoid-unbundled-basic, ga-complete-mathlib-mathlib-algebra-order-monoid-unbundled-defs, ga-complete-mathlib-mathlib-algebra-order-ring-defs, ga-complete-mathlib-mathlib-algebra-order-star-basic, ga-complete-mathlib-mathlib-algebra-order-star-real, ga-complete-mathlib-mathlib-algebra-ring-defs, ga-complete-mathlib-mathlib-algebra-ring-hom-defs, ga-complete-mathlib-mathlib-algebra-ring-int-defs, ga-complete-mathlib-mathlib-algebra-ring-nat, ga-complete-mathlib-mathlib-algebra-torsor-defs, ga-complete-mathlib-mathlib-analysis-complex-trigonometric, ga-complete-mathlib-mathlib-analysis-normed-field-basic, ga-complete-mathlib-mathlib-analysis-normed-ring-basic, ga-complete-mathlib-mathlib-analysis-rclike-basic, ga-complete-mathlib-mathlib-analysis-specialfunctions-trigonometric-basic, ga-complete-mathlib-mathlib-basic-existsunique, ga-complete-mathlib-mathlib-basic-finite-defs, ga-complete-mathlib-mathlib-basic-finite-prod, ga-complete-mathlib-mathlib-basic-funlike-basic, ga-complete-mathlib-mathlib-basic-funlike-equiv, ga-complete-mathlib-mathlib-basic-isempty-defs, ga-complete-mathlib-mathlib-basic-real-basic, ga-complete-mathlib-mathlib-basic-real-star, ga-complete-mathlib-mathlib-basic-setlike-basic, ga-complete-mathlib-mathlib-basic-unique, ga-complete-mathlib-mathlib-categorytheory-category-basic, ga-complete-mathlib-mathlib-categorytheory-groupoid, ga-complete-mathlib-mathlib-combinatorics-quiver-basic, ga-complete-mathlib-mathlib-data-finset-defs, ga-complete-mathlib-mathlib-data-finsupp-defs, ga-complete-mathlib-mathlib-data-finsupp-order, ga-complete-mathlib-mathlib-data-finsupp-pointwise, ga-complete-mathlib-mathlib-data-finsupp-smul, ga-complete-mathlib-mathlib-data-finsupp-smulwithzero, ga-complete-mathlib-mathlib-data-finsupp-single, ga-complete-mathlib-mathlib-data-fintype-basic, ga-complete-mathlib-mathlib-data-fintype-card, ga-complete-mathlib-mathlib-data-fintype-equivfin, ga-complete-mathlib-mathlib-data-fintype-lattice, ga-complete-mathlib-mathlib-data-int-cast-defs, ga-complete-mathlib-mathlib-data-list-induction, ga-complete-mathlib-mathlib-data-nat-basic, ga-complete-mathlib-mathlib-data-nat-cast-defs, ga-complete-mathlib-mathlib-data-nat-cast-order-basic, ga-complete-mathlib-mathlib-data-nat-init, ga-complete-mathlib-mathlib-data-set-basic, ga-complete-mathlib-mathlib-data-set-booleanalgebra, ga-complete-mathlib-mathlib-data-set-card, ga-complete-mathlib-mathlib-data-set-coesort, ga-complete-mathlib-mathlib-data-set-defs, ga-complete-mathlib-mathlib-data-set-disjoint, ga-complete-mathlib-mathlib-data-set-finite-basic, ga-complete-mathlib-mathlib-data-set-finite-lattice, ga-complete-mathlib-mathlib-data-set-finite-powerset, ga-complete-mathlib-mathlib-data-set-finite-range, ga-complete-mathlib-mathlib-data-set-image, ga-complete-mathlib-mathlib-data-set-insert, ga-complete-mathlib-mathlib-data-set-operations, ga-complete-mathlib-mathlib-grouptheory-coxeter-basic, ga-complete-mathlib-mathlib-grouptheory-coxeter-length, ga-complete-mathlib-mathlib-grouptheory-coxeter-matrix, ga-complete-mathlib-mathlib-grouptheory-groupaction-hom, ga-complete-mathlib-mathlib-grouptheory-groupaction-ring, ga-complete-mathlib-mathlib-grouptheory-presentedgroup, ga-complete-mathlib-mathlib-linearalgebra-bilinearmap, ga-complete-mathlib-mathlib-linearalgebra-finsupp-defs, ga-complete-mathlib-mathlib-linearalgebra-span-defs, ga-complete-mathlib-mathlib-logic-equiv-defs, ga-complete-mathlib-mathlib-logic-function-basic, ga-complete-mathlib-mathlib-logic-relation, ga-complete-mathlib-mathlib-order-basic, ga-complete-mathlib-mathlib-order-booleanalgebra-set, ga-complete-mathlib-mathlib-order-boundedorder-basic, ga-complete-mathlib-mathlib-order-completebooleanalgebra, ga-complete-mathlib-mathlib-order-completepartialorder, ga-complete-mathlib-mathlib-order-defs-lattice, ga-complete-mathlib-mathlib-order-defs-linearorder, ga-complete-mathlib-mathlib-order-defs-partialorder, ga-complete-mathlib-mathlib-order-disjoint, ga-complete-mathlib-mathlib-order-lattice, ga-complete-mathlib-mathlib-order-preorder-finsupp, ga-complete-mathlib-mathlib-order-relclasses, ga-complete-mathlib-mathlib-order-setnotation, ga-complete-mathlib-mathlib-representationtheory-basic, ga-complete-mathlib-mathlib-settheory-cardinal-finite, ga-complete-mathlib-mathlib-tactic-abel, ga-complete-mathlib-mathlib-tactic-canceldenoms-core, ga-complete-mathlib-mathlib-tactic-group, ga-complete-mathlib-mathlib-tactic-linarith-lemmas, ga-complete-mathlib-mathlib-tactic-linarith-preprocessing, ga-complete-mathlib-mathlib-tactic-normnum-basic, ga-complete-mathlib-mathlib-tactic-normnum-eq, ga-complete-mathlib-mathlib-tactic-normnum-ineq, ga-complete-mathlib-mathlib-tactic-normnum-inv, ga-complete-mathlib-mathlib-tactic-normnum-result, ga-complete-mathlib-mathlib-tactic-push, ga-complete-mathlib-mathlib-tactic-ring-basic, ga-complete-mathlib-mathlib-tactic-ring-common, ga-complete-project-tauceti-grouptheory-coxeter-basic, ga-complete-project-tauceti-grouptheory-coxeter-geometric-basic, ga-complete-project-tauceti-grouptheory-coxeter-parabolic (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [translation](translations/GeodesicAdditivity.json), [proof](Proofs/GeodesicAdditivity.lean), [compilation evidence](evidence/GeodesicAdditivity-compile.json).

## BrinkHowlettGroupoid: Brink–Howlett groupoid with the article's composition convention

Prerequisite; compiled and axiom-checked.

### Article

Fix a Coxeter diagram Γ, its Coxeter group W and J⊆Γ₀. An associate I of J has W_I conjugate to W_J. The groupoid BH(J) has these associates as objects and Hom_BH(I,K)={x∈W: x{α_k:k∈K}={α_i:i∈I}}. If x:I→K and y:K→L, their left-to-right composite is xy:I→L.

[§4.1, definition preceding Remark 4.1, printed p. 15; associates in Definition 2.7, printed p. 5.](https://arxiv.org/pdf/2509.21915#page=15)

### Alphabeta Math

The same small connected groupoid, with arrows tagged by source and target and multiplication read left to right. No finite-rank or spherical-type restriction is imposed.

[Definition of def-brink-howlett-artin-tits-normalisers.](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-def-brink-howlett-artin-tits-normalisers)

### Lean translation

Translation source: article. The report does not identify this endpoint statement as defective. [Defect report](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects).

```lean
def BrinkHowlettGroupoid : ∀ {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S), CategoryTheory.Groupoid { I : Set S // ∃ w : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj w)) (CoxeterSystem.parabolic cs I) = CoxeterSystem.parabolic cs J } := by
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
  }
```

Immediate internal dependencies: none.

Existing repository dependencies: none.

Immediate external dependencies: existing-geometric-representation, existing-parabolic, mathlib-groupoid, mathlib-single, mathlib-image, mathlib-image-image, mathlib-image-id, mathlib-map-mul, mathlib-map-one, mathlib-mul-apply, mathlib-one-apply, mathlib-representation-inverse, mathlib-one-mul, mathlib-mul-one, mathlib-mul-assoc, mathlib-inv-mul, mathlib-mul-inv, lean-subtype-ext, lean-congrarg, mathlib-subgroup-map, mathlib-conjugation, mathlib-equiv-hom (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [translation](translations/BrinkHowlettGroupoid.json), [proof](Proofs/BrinkHowlettGroupoid.lean), [compilation evidence](evidence/BrinkHowlettGroupoid-compile.json).

## ElementaryWallMorphism: Elementary crossings are Brink–Howlett arrows

Prerequisite; compiled and axiom-checked.

### Article

If I is an associate of J, a∉I and W_[I,a] is finite, then v_{a,I}∈Hom_BH(I,(I∪{a})\{ι_[I,a](a)}).

[Lemma 4.2, printed p. 15.](https://arxiv.org/pdf/2509.21915#page=15)

### Alphabeta Math

At arbitrary rank, the prescribed target K is an associate of J and v_{a,I}{α_k:k∈K}={α_i:i∈I}. Only the crossing component is required to be spherical.

[Statement of lem-wall-is-morphism-artin-tits-normalisers.](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-wall-is-morphism-artin-tits-normalisers)

### Lean translation

Translation source: article. The report does not identify this endpoint statement as defective. [Defect report](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects).

```lean
theorem ElementaryWallMorphism : ∀ {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J I : Set S) (hI : ∃ w : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj w)) (CoxeterSystem.parabolic cs I) = CoxeterSystem.parabolic cs J) (a : S) (ha : a ∉ I), let D : Set S := {b | b ∈ Set.insert a I ∧ Relation.ReflTransGen (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b}; ∀ hD : Finite (CoxeterSystem.parabolic cs D), let crossing := SimpleWallCrossings S W M cs I a ha hD; ∃ hK : ∃ w : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj w)) (CoxeterSystem.parabolic cs crossing.2.1) = CoxeterSystem.parabolic cs J, ∃ f : (BrinkHowlettGroupoid cs J).Hom ⟨I, hI⟩ ⟨crossing.2.1, hK⟩, f.val = crossing.1
```

Immediate internal dependencies: SimpleWallCrossings, BrinkHowlettGroupoid.

Existing repository dependencies: none.

Immediate external dependencies: parabolic-api, geometric-api, root-sign-api, commuting-simple, coxeter-word-api, coxeter-length-api, finite-max, finite-subgroup, mathlib-routine-declarations, lean-core-declarations (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [translation](translations/ElementaryWallMorphism.json), [proof](Proofs/ElementaryWallMorphism.lean), [compilation evidence](evidence/ElementaryWallMorphism-compile.json).

## UniversalWallGroupoid: Singleton-arrow groupoid on chamber labels

Prerequisite; compiled and axiom-checked.

### Article

The groupoid BH̃(J) has objects Cham(J), with Hom((x,I),(y,K)) the singleton labelled x⁻¹y. Composition multiplies labels on the right. For adjacent chambers its arrow is labelled by their elementary crossing element.

[Definition 4.3 and following paragraph, printed p. 15.](https://arxiv.org/pdf/2509.21915#page=15)

### Alphabeta Math

The algebraic singleton-arrow construction applies at arbitrary rank, retaining endpoint tags. Its geometric chamber and adjacent-crossing interpretation additionally uses finite rank, without assuming W, W_I or W_{I∪{a}} finite.

[Definition of def-universal-wall-groupoid-artin-tits-normalisers.](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-def-universal-wall-groupoid-artin-tits-normalisers)

### Lean translation

Translation source: portal. Explicit user direction selects the finite-rank geometric interpretation at https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-def-universal-wall-groupoid-artin-tits-normalisers while retaining its arbitrary-rank algebraic construction. The report at https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects was checked and does not identify Definition 4.3 as defective. Objects are precisely the algebraic chamber labels; singleton arrows retain endpoint tags and compose by left-to-right multiplication. Under the finite-rank geometric identification supplied by ChamberLabelling, AdjacentWallFormula gives y = x * v, so the defined arrow label x⁻¹ * y is the elementary crossing v. Finite rank applies only to that geometric interpretation; no finiteness of W, W_I or W_{I∪{a}} is imposed. [Defect report](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects).

```lean
def UniversalWallGroupoid : ∀ {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S), CategoryTheory.Groupoid { p : W × Set S // Set.image (fun u : W => u * p.1) (CoxeterSystem.parabolic cs J : Set W) = Set.image (fun u : W => p.1 * u) (CoxeterSystem.parabolic cs p.2 : Set W) ∧ CoxeterSystem.IsMinimalCosetRep cs p.2 p.1 } := fun {S W} _inst {M} cs J => {
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
```

Immediate internal dependencies: ChamberLabelling, AdjacentWallFormula.

Existing repository dependencies: none.

Immediate external dependencies: uwg-project, uwg-mathlib, uwg-core (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [translation](translations/UniversalWallGroupoid.json), [proof](Proofs/UniversalWallGroupoid.lean), [compilation evidence](evidence/UniversalWallGroupoid-compile.json).

## UniversalGenerators: Adjacent crossings generate the universal wall groupoid

Prerequisite; compiled and axiom-checked.

### Article

For any chamber labels (x,I),(y,K), there is a finite crossing path p between them whose product v_p equals x⁻¹y. Thus the adjacent-crossing arrows generate BH̃(J). The path need not be unique.

[Proposition 4.4, printed p. 16.](https://arxiv.org/pdf/2509.21915#page=16)

### Alphabeta Math

The same factorization through finite paths in the finite-rank relative-interior arrangement, with endpoint-tagged arrows and the zero-crossing case included.

[Statement of prop-universal-generators-artin-tits-normalisers.](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-prop-universal-generators-artin-tits-normalisers)

### Lean translation

Translation source: portal. Explicit user direction selects the finite-rank geometric endpoint at https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-prop-universal-generators-artin-tits-normalisers. The report at https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects was read and does not identify Proposition 4.4's statement as defective; finite rank is user-directed, not a reported correction. Label is Cham(J), geometrically identified with relative-interior chambers by ChamberLabelling. The finite list records source-tagged simple crossings, and the endpoint-threading condition enforces their composability through chamber labels. Their ordered product equals x⁻¹y and is the sole label in the endpoint-tagged hom-set of UniversalWallGroupoid. The empty list permits the zero-crossing path; path uniqueness is not asserted. Coxeter type and J remain arbitrary, with only individual crossing components required spherical. This geometric endpoint does not restrict the arbitrary-rank algebraic groupoid construction or covering statement. [Defect report](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects).

```lean
theorem UniversalGenerators : ∀ {S : Type*} [Finite S] (M : CoxeterMatrix S) (J : Set S),
  let W := CoxeterMatrix.Group M
  let cs := CoxeterMatrix.toCoxeterSystem M
  let Label := { p : W × Set S //
    Set.image (fun u : W => u * p.1) (CoxeterSystem.parabolic cs J : Set W) =
      Set.image (fun u : W => p.1 * u) (CoxeterSystem.parabolic cs p.2 : Set W) ∧
    CoxeterSystem.IsMinimalCosetRep cs p.2 p.1 }
  let component : Set S → S → Set S := fun I a =>
    { b | b ∈ Set.insert a I ∧ Relation.ReflTransGen
      (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b }
  let Atom := { e : Label × S // e.2 ∉ e.1.val.2 ∧
    Finite (CoxeterSystem.parabolic cs (component e.1.val.2 e.2)) }
  let crossing := fun e : Atom =>
    SimpleWallCrossings S W M cs e.val.1.val.2 e.val.2 e.property.1 e.property.2
  ∀ A B : Label, ∃ es : List Atom,
    List.foldr
      (fun e tail P => P = e.val.1.val ∧ tail ((crossing e).2.2 e.val.1.val.1))
      (fun P => P = B.val) es A.val ∧
    List.prod (List.map (fun e => (crossing e).1) es) = A.val.1⁻¹ * B.val.1 ∧
    Set.range (fun f : (UniversalWallGroupoid cs J).Hom A B => f.val) =
      {List.prod (List.map (fun e => (crossing e).1) es)}
```

Immediate internal dependencies: FiniteWallPaths, UniversalWallGroupoid, SimpleWallCrossings.

Existing repository dependencies: none.

Immediate external dependencies: ug-project, ug-mathlib, ug-core (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [translation](translations/UniversalGenerators.json), [proof](Proofs/UniversalGenerators.lean), [compilation evidence](evidence/UniversalGenerators-compile.json).

## ChamberMorphismCorrespondence: Chamber labels and prescribed-source arrow lifting

Prerequisite; compiled and axiom-checked.

### Article

For associates I,K of J: (1) chamber labels (x,I),(y,K) satisfy x⁻¹y∈Hom_BH(I,K); (2) if w∈Hom_BH(I,K) and (x,I)∈Cham(J), then (xw,K)∈Cham(J), and w labels the arrow upstairs from (x,I) to (xw,K).

[Proposition 4.6(1)–(2), printed p. 16.](https://arxiv.org/pdf/2509.21915#page=16)

### Alphabeta Math

The same assertions are stated with finite-rank hypotheses and geometric chamber identification. The main covering entry separately supplies an arbitrary-rank algebraic correspondence using canonical simple systems.

[Statement and Source notes of prop-chambers-morphisms-artin-tits-normalisers.](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-prop-chambers-morphisms-artin-tits-normalisers)

### Lean translation

Translation source: portal. Explicit user direction selects the finite-rank geometric endpoint at https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-prop-chambers-morphisms-artin-tits-normalisers. The report at https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects was checked: finding pdf-prop46-left-descent-typo replaces ℓ(ys_j)<ℓ(y) by ℓ(s_jy)<ℓ(y) in the proof and explicitly does not refute Proposition 4.6. Finite rank follows user direction, not a reported statement defect. The label predicate defines Cham(J), identified with geometric chambers by ChamberLabelling. Both assertions preserve arrow orientation, including the unique upstairs arrow from (x,I) to (xw,K) labelled w. Neither W nor W_J is assumed finite; the separate arbitrary-rank algebraic covering endpoint remains unrestricted. The type expression elaborated successfully with the supplied prerequisite definitions. [Defect report](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects).

```lean
theorem ChamberMorphismCorrespondence : ∀ {S W : Type*} [Finite S] [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S),
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
```

Immediate internal dependencies: ChamberLabelling, BrinkHowlettGroupoid, UniversalWallGroupoid.

Existing repository dependencies: none.

Immediate external dependencies: cmc-transport, cmc-sign, cmc-geometric, cmc-parabolic, cmc-mathlib, cmc-lean, cmc-final-artinchambers-positivetransport, cmc-final-artinlandmarkvendor-geometric-sign, cmc-final-init-core, cmc-final-init-data-int-basic, cmc-final-init-data-nat-basic, cmc-final-init-data-nezero, cmc-final-init-data-zero, cmc-final-init-prelude, cmc-final-init-simplemmas, cmc-final-mathlib-algebra-group-basic, cmc-final-mathlib-algebra-group-defs, cmc-final-mathlib-algebra-group-divinvmonoid, cmc-final-mathlib-algebra-group-end, cmc-final-mathlib-algebra-group-equiv-defs, cmc-final-mathlib-algebra-group-finsupp, cmc-final-mathlib-algebra-group-hom-defs, cmc-final-mathlib-algebra-group-int-defs, cmc-final-mathlib-algebra-group-isapply, cmc-final-mathlib-algebra-group-monoid, cmc-final-mathlib-algebra-group-semigroup, cmc-final-mathlib-algebra-group-subgroup-defs, cmc-final-mathlib-algebra-group-subgroup-lattice, cmc-final-mathlib-algebra-group-subgroup-map, cmc-final-mathlib-algebra-groupwithzero-action-defs, cmc-final-mathlib-algebra-groupwithzero-defs, cmc-final-mathlib-algebra-module-defs, cmc-final-mathlib-algebra-module-linearmap-defs, cmc-final-mathlib-algebra-module-linearmap-end, cmc-final-mathlib-algebra-order-archimedean-real-basic, cmc-final-mathlib-algebra-order-floor-defs, cmc-final-mathlib-algebra-order-group-defs, cmc-final-mathlib-algebra-ring-defs, cmc-final-mathlib-algebra-ring-hom-defs, cmc-final-mathlib-algebra-ring-nat, cmc-final-mathlib-basic-existsunique, cmc-final-mathlib-basic-finite-defs, cmc-final-mathlib-basic-funlike-basic, cmc-final-mathlib-basic-real-basic, cmc-final-mathlib-basic-setlike-basic, cmc-final-mathlib-categorytheory-category-basic, cmc-final-mathlib-categorytheory-groupoid, cmc-final-mathlib-combinatorics-quiver-basic, cmc-final-mathlib-data-finsupp-defs, cmc-final-mathlib-data-finsupp-smul, cmc-final-mathlib-data-finsupp-smulwithzero, cmc-final-mathlib-data-finsupp-single, cmc-final-mathlib-data-int-cast-defs, cmc-final-mathlib-data-nat-cast-defs, cmc-final-mathlib-data-nat-init, cmc-final-mathlib-data-set-defs, cmc-final-mathlib-data-set-image, cmc-final-mathlib-data-set-operations, cmc-final-mathlib-grouptheory-coxeter-basic, cmc-final-mathlib-grouptheory-coxeter-length, cmc-final-mathlib-grouptheory-coxeter-matrix, cmc-final-mathlib-grouptheory-groupaction-hom, cmc-final-mathlib-grouptheory-groupaction-ring, cmc-final-mathlib-linearalgebra-bilinearmap, cmc-final-mathlib-order-basic, cmc-final-mathlib-order-defs-lattice, cmc-final-mathlib-order-defs-partialorder, cmc-final-mathlib-order-lattice, cmc-final-mathlib-order-preorder-finsupp, cmc-final-mathlib-representationtheory-basic, cmc-final-mathlib-tactic-group, cmc-final-mathlib-tactic-linarith-lemmas, cmc-final-mathlib-tactic-normnum-basic, cmc-final-mathlib-tactic-normnum-ineq, cmc-final-mathlib-tactic-normnum-result, cmc-final-mathlib-tactic-ring-basic, cmc-final-mathlib-tactic-ring-common, cmc-final-tauceti-grouptheory-coxeter-geometric-basic, cmc-final-tauceti-grouptheory-coxeter-parabolic (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [translation](translations/ChamberMorphismCorrespondence.json), [proof](Proofs/ChamberMorphismCorrespondence.lean), [compilation evidence](evidence/ChamberMorphismCorrespondence-compile.json).

## UniversalBrinkHowlettCover: Theorem 1.3 / 4.7: universal covering, wall crossings and deck quotient

Main theorem; compiled and axiom-checked.

### Article

Let Γ be a Coxeter diagram with Coxeter group W and J⊆Γ₀. The functor F:BH̃(J)→BH(J), defined by F(x,I)=I and F(x⁻¹y)=x⁻¹y, is a universal groupoid covering with Deck(F)≅N(W,J). Preserve also Theorem 1.3's geometric content: its upstairs objects are the chambers of (Cone(J)°,H^J), its generating morphisms are simple crossings between adjacent chambers, and BH(J) is obtained as the N(W,J)-quotient of BH̃(J). No spherical-type restriction on W or W_J is stated.

[Theorem 1.3 and following paragraph, printed p. 2; Theorem 4.7, printed pp. 16–17; Definition 4.3, printed p. 15; Proposition 4.4, printed p. 16.](https://arxiv.org/pdf/2509.21915#page=2)

### Alphabeta Math

At arbitrary rank, the algebraic label groupoid covers BH(J) universally, has deck group N(W,J), and has quotient isomorphic to BH(J). Its geometric chamber identification, adjacent-generator interpretation and generation assertion explicitly use finite rank. Neither W nor W_J is required finite. This scope distinction remains explicit and is not substituted for the original requested statement.

[Statement, External input and Source notes of thm-universal-brink-howlett-cover-artin-tits-normalisers.](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-thm-universal-brink-howlett-cover-artin-tits-normalisers)

### Lean translation

Translation source: portal. Explicit user direction selects the finite-rank geometric endpoint at https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-thm-universal-brink-howlett-cover-artin-tits-normalisers while retaining arbitrary rank for the algebraic covering, deck group and quotient. The full report at https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects was checked and does not identify Theorems 1.3/4.7 as defective statements. Finding pdf-prop46-left-descent-typo concerns a prerequisite proof, not this theorem’s statement. Finite rank is user-directed, not a reported correction; neither W nor W_J is required finite. Universality is expressed by the covering condition and nonempty connected upstairs groupoid with trivial vertex groups. Singleton hom-sets identify strict deck automorphisms with the specified label-preserving object permutations. The quotient is expressed by surjective object and total-arrow maps whose fibres are exactly the normaliser-quotient orbits, acting diagonally on arrow endpoints. The geometric clause identifies actual chambers, adjacent generators, the induced normaliser action and generation upstairs and downstairs. The covering API reuses ArtinNormalisers.Chamber3.IsCoveringFunctor, chambers/ArtinChambers/GroupoidCover.lean:34, at commit 8668c70d25e6c5d63c313bac756052f9c83ee7f0, unchanged at inspected HEAD 1bdd7a76d6447fe84bc46aab09120f20292bf334. The type elaborated with ArtinDeligne and the supplied prerequisite definitions. [Defect report](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects).

```lean
theorem UniversalBrinkHowlettCover : ∀ {S : Type*} (M : CoxeterMatrix S) (J : Set S),
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
              List.prod (List.map (fun s => (crossing s).1) es) = w.val))
```

Immediate internal dependencies: BrinkHowlettGroupoid, UniversalWallGroupoid, UniversalGenerators, ChamberMorphismCorrespondence, NormaliserChamberAction.

Existing repository dependencies: none.

Immediate external dependencies: ubhc-round1-project, ubhc-round1-mathlib, ubhc-round1-core, ubhc-final-artinchambers-chamberlabels, ubhc-final-artinchambers-dominant, ubhc-final-artinchambers-facettransport, ubhc-final-artinchambers-groupoidcover, ubhc-final-artinchambers-positivetransport, ubhc-final-artinchambers-regularcriterion, ubhc-final-artinlandmarkvendor-geometric-sign, ubhc-final-artinlandmarks-dominant, ubhc-final-artinlandmarks-regularstabilizer, ubhc-final-artinnormalisers-artin-basic, ubhc-final-artinnormalisers-artin-exactsequence, ubhc-final-artinnormalisers-artin-normalizerlift, ubhc-final-artinnormalisers-theorem18-geometry, ubhc-final-artinnormalisers-theorem18-normalizeraction, ubhc-final-init-classical, ubhc-final-init-core, ubhc-final-init-data-cast, ubhc-final-init-data-function, ubhc-final-init-data-int-basic, ubhc-final-init-data-int-lemmas, ubhc-final-init-data-int-order, ubhc-final-init-data-list-basic, ubhc-final-init-data-list-lemmas, ubhc-final-init-data-list-takedrop, ubhc-final-init-data-nat-basic, ubhc-final-init-data-nezero, ubhc-final-init-data-order-lemmas, ubhc-final-init-data-zero, ubhc-final-init-ext, ubhc-final-init-omega-coeffs, ubhc-final-init-omega-constraint, ubhc-final-init-omega-int, ubhc-final-init-omega-linearcombo, ubhc-final-init-prelude, ubhc-final-init-proplemmas, ubhc-final-init-simplemmas, ubhc-final-mathlib-algebra-algebra-basic, ubhc-final-mathlib-algebra-algebra-defs, ubhc-final-mathlib-algebra-bigoperators-finsupp-basic, ubhc-final-mathlib-algebra-bigoperators-group-finset-basic, ubhc-final-mathlib-algebra-bigoperators-group-finset-defs, ubhc-final-mathlib-algebra-bigoperators-group-finset-piecewise, ubhc-final-mathlib-algebra-bigoperators-pi, ubhc-final-mathlib-algebra-charzero-defs, ubhc-final-mathlib-algebra-field-defs, ubhc-final-mathlib-algebra-group-action-defs, ubhc-final-mathlib-algebra-group-basic, ubhc-final-mathlib-algebra-group-commute-defs, ubhc-final-mathlib-algebra-group-defs, ubhc-final-mathlib-algebra-group-divinvmonoid, ubhc-final-mathlib-algebra-group-end, ubhc-final-mathlib-algebra-group-equiv-defs, ubhc-final-mathlib-algebra-group-finsupp, ubhc-final-mathlib-algebra-group-hom-defs, ubhc-final-mathlib-algebra-group-int-defs, ubhc-final-mathlib-algebra-group-isapply, ubhc-final-mathlib-algebra-group-monoid, ubhc-final-mathlib-algebra-group-nat-defs, ubhc-final-mathlib-algebra-group-pi-basic, ubhc-final-mathlib-algebra-group-semiconj-defs, ubhc-final-mathlib-algebra-group-semigroup, ubhc-final-mathlib-algebra-group-subgroup-basic, ubhc-final-mathlib-algebra-group-subgroup-defs, ubhc-final-mathlib-algebra-group-subgroup-ker, ubhc-final-mathlib-algebra-group-subgroup-lattice, ubhc-final-mathlib-algebra-group-subgroup-map, ubhc-final-mathlib-algebra-group-submonoid-defs, ubhc-final-mathlib-algebra-group-subsemigroup-defs, ubhc-final-mathlib-algebra-groupwithzero-action-defs, ubhc-final-mathlib-algebra-groupwithzero-defs, ubhc-final-mathlib-algebra-module-defs, ubhc-final-mathlib-algebra-module-equiv-defs, ubhc-final-mathlib-algebra-module-linearmap-defs, ubhc-final-mathlib-algebra-module-linearmap-end, ubhc-final-mathlib-algebra-module-pi, ubhc-final-mathlib-algebra-module-submodule-defs, ubhc-final-mathlib-algebra-module-submodule-lattice, ubhc-final-mathlib-algebra-module-submodule-map, ubhc-final-mathlib-algebra-nezero, ubhc-final-mathlib-algebra-notation-defs, ubhc-final-mathlib-algebra-notation-pi-defs, ubhc-final-mathlib-algebra-order-archimedean-real-basic, ubhc-final-mathlib-algebra-order-bigoperators-group-finset, ubhc-final-mathlib-algebra-order-field-basic, ubhc-final-mathlib-algebra-order-floor-defs, ubhc-final-mathlib-algebra-order-group-defs, ubhc-final-mathlib-algebra-order-group-unbundled-basic, ubhc-final-mathlib-algebra-order-groupwithzero-basic, ubhc-final-mathlib-algebra-order-groupwithzero-defs, ubhc-final-mathlib-algebra-order-monoid-defs, ubhc-final-mathlib-algebra-order-monoid-unbundled-basic, ubhc-final-mathlib-algebra-order-monoid-unbundled-defs, ubhc-final-mathlib-algebra-order-ring-defs, ubhc-final-mathlib-algebra-order-zeroleone, ubhc-final-mathlib-algebra-quotient, ubhc-final-mathlib-algebra-ring-comptypeclasses, ubhc-final-mathlib-algebra-ring-defs, ubhc-final-mathlib-algebra-ring-hom-defs, ubhc-final-mathlib-algebra-ring-int-defs, ubhc-final-mathlib-algebra-ring-nat, ubhc-final-mathlib-algebra-torsor-defs, ubhc-final-mathlib-analysis-complex-trigonometric, ubhc-final-mathlib-analysis-convex-pathconnected, ubhc-final-mathlib-analysis-innerproductspace-basic, ubhc-final-mathlib-analysis-innerproductspace-defs, ubhc-final-mathlib-analysis-normed-affine-addtorsorbases, ubhc-final-mathlib-analysis-normed-field-basic, ubhc-final-mathlib-analysis-normed-group-addtorsor, ubhc-final-mathlib-analysis-normed-group-constructions, ubhc-final-mathlib-analysis-normed-group-defs, ubhc-final-mathlib-analysis-normed-group-real, ubhc-final-mathlib-analysis-normed-module-basic, ubhc-final-mathlib-analysis-normed-order-lattice, ubhc-final-mathlib-analysis-normed-ring-basic, ubhc-final-mathlib-analysis-rclike-basic, ubhc-final-mathlib-analysis-specialfunctions-trigonometric-basic, ubhc-final-mathlib-basic-existsunique, ubhc-final-mathlib-basic-finite-defs, ubhc-final-mathlib-basic-funlike-basic, ubhc-final-mathlib-basic-funlike-equiv, ubhc-final-mathlib-basic-isempty-defs, ubhc-final-mathlib-basic-real-basic, ubhc-final-mathlib-basic-setlike-basic, ubhc-final-mathlib-basic-unique, ubhc-final-mathlib-categorytheory-category-basic, ubhc-final-mathlib-categorytheory-functor-basic, ubhc-final-mathlib-categorytheory-groupoid, ubhc-final-mathlib-combinatorics-quiver-basic, ubhc-final-mathlib-data-finset-defs, ubhc-final-mathlib-data-finsupp-defs, ubhc-final-mathlib-data-finsupp-order, ubhc-final-mathlib-data-finsupp-pointwise, ubhc-final-mathlib-data-finsupp-smul, ubhc-final-mathlib-data-finsupp-smulwithzero, ubhc-final-mathlib-data-finsupp-single, ubhc-final-mathlib-data-fintype-basic, ubhc-final-mathlib-data-fintype-card, ubhc-final-mathlib-data-fintype-equivfin, ubhc-final-mathlib-data-fintype-lattice, ubhc-final-mathlib-data-int-cast-defs, ubhc-final-mathlib-data-list-induction, ubhc-final-mathlib-data-nat-basic, ubhc-final-mathlib-data-nat-cast-defs, ubhc-final-mathlib-data-nat-init, ubhc-final-mathlib-data-set-basic, ubhc-final-mathlib-data-set-coesort, ubhc-final-mathlib-data-set-defs, ubhc-final-mathlib-data-set-finite-basic, ubhc-final-mathlib-data-set-image, ubhc-final-mathlib-data-set-insert, ubhc-final-mathlib-data-set-operations, ubhc-final-mathlib-data-subtype, ubhc-final-mathlib-grouptheory-coset-defs, ubhc-final-mathlib-grouptheory-coxeter-basic, ubhc-final-mathlib-grouptheory-coxeter-length, ubhc-final-mathlib-grouptheory-coxeter-matrix, ubhc-final-mathlib-grouptheory-groupaction-hom, ubhc-final-mathlib-grouptheory-groupaction-ring, ubhc-final-mathlib-grouptheory-presentedgroup, ubhc-final-mathlib-grouptheory-quotientgroup-defs, ubhc-final-mathlib-linearalgebra-affinespace-affinemap, ubhc-final-mathlib-linearalgebra-affinespace-affinesubspace-basic, ubhc-final-mathlib-linearalgebra-affinespace-affinesubspace-defs, ubhc-final-mathlib-linearalgebra-affinespace-combination, ubhc-final-mathlib-linearalgebra-bilinearmap, ubhc-final-mathlib-linearalgebra-dfinsupp, ubhc-final-mathlib-linearalgebra-dimension-constructions, ubhc-final-mathlib-linearalgebra-dimension-finrank, ubhc-final-mathlib-linearalgebra-freemodule-strongrankcondition, ubhc-final-mathlib-linearalgebra-span-defs, ubhc-final-mathlib-logic-equiv-defs, ubhc-final-mathlib-logic-function-basic, ubhc-final-mathlib-logic-relation, ubhc-final-mathlib-order-basic, ubhc-final-mathlib-order-booleanalgebra-set, ubhc-final-mathlib-order-boundedorder-basic, ubhc-final-mathlib-order-completelattice-defs, ubhc-final-mathlib-order-defs-lattice, ubhc-final-mathlib-order-defs-linearorder, ubhc-final-mathlib-order-defs-partialorder, ubhc-final-mathlib-order-interval-set-defs, ubhc-final-mathlib-order-lattice, ubhc-final-mathlib-order-notation, ubhc-final-mathlib-order-preorder-finsupp, ubhc-final-mathlib-order-relclasses, ubhc-final-mathlib-order-setnotation, ubhc-final-mathlib-representationtheory-basic, ubhc-final-mathlib-settheory-cardinal-finite, ubhc-final-mathlib-tactic-group, ubhc-final-mathlib-tactic-linarith-lemmas, ubhc-final-mathlib-tactic-normnum-basic, ubhc-final-mathlib-tactic-normnum-eq, ubhc-final-mathlib-tactic-normnum-ineq, ubhc-final-mathlib-tactic-normnum-result, ubhc-final-mathlib-tactic-ring-basic, ubhc-final-mathlib-tactic-ring-common, ubhc-final-mathlib-topology-algebra-group-defs, ubhc-final-mathlib-topology-algebra-module-basic, ubhc-final-mathlib-topology-algebra-module-equiv-basic, ubhc-final-mathlib-topology-algebra-mulaction, ubhc-final-mathlib-topology-basic, ubhc-final-mathlib-topology-closure, ubhc-final-mathlib-topology-connected-basic, ubhc-final-mathlib-topology-constructions, ubhc-final-mathlib-topology-continuous, ubhc-final-mathlib-topology-defs-basic, ubhc-final-mathlib-topology-defs-induced, ubhc-final-mathlib-topology-gdelta-metrizablespace, ubhc-final-mathlib-topology-homeomorph-defs, ubhc-final-mathlib-topology-metricspace-basic, ubhc-final-mathlib-topology-metricspace-defs, ubhc-final-mathlib-topology-metricspace-pseudo-defs, ubhc-final-mathlib-topology-metricspace-pseudo-lemmas, ubhc-final-mathlib-topology-metrizable-uniformity, ubhc-final-mathlib-topology-nhdswithin, ubhc-final-mathlib-topology-order, ubhc-final-mathlib-topology-order-denselyordered, ubhc-final-mathlib-topology-order-orderclosed, ubhc-final-mathlib-topology-separation-basic, ubhc-final-mathlib-topology-separation-gdelta, ubhc-final-mathlib-topology-separation-regular, ubhc-final-mathlib-topology-uniformspace-defs, ubhc-final-tauceti-grouptheory-coxeter-basic, ubhc-final-tauceti-grouptheory-coxeter-geometric-basic, ubhc-final-tauceti-grouptheory-coxeter-parabolic (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [translation](translations/UniversalBrinkHowlettCover.json), [proof](Proofs/UniversalBrinkHowlettCover.lean), [compilation evidence](evidence/UniversalBrinkHowlettCover-compile.json).

## StandardExpressions: Length-additive elementary expressions

Prerequisite; compiled and axiom-checked.

### Article

For w∈Hom_BH(I,K), a standard expression is a finite composable product w=v_{a₁,I₁}⋯v_{a_m,I_m}, starting at I and ending at K, with ℓ(w)=Σ_iℓ(v_{a_i,I_i}). Its expression length is m. Existence and independence of the expression are subsequent assertions, not assumptions of this definition.

[Definition 4.9, printed p. 17.](https://arxiv.org/pdf/2509.21915#page=17)

### Alphabeta Math

The same definition at arbitrary rank. Each elementary factor requires its crossing component spherical. The empty expression represents an identity. The notation ℓ_BH(w) is introduced only after existence and invariance of factor count are established.

[Definition and Source notes of def-standard-expressions-artin-tits-normalisers.](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-def-standard-expressions-artin-tits-normalisers)

### Lean translation

Translation source: article. The report does not identify this endpoint statement as defective. [Defect report](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects).

```lean
def StandardExpressions : ∀ {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) (I K : { L : Set S // ∃ g : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (CoxeterSystem.parabolic cs L) = CoxeterSystem.parabolic cs J }) (w : (BrinkHowlettGroupoid cs J).Hom I K), Type _ := fun {S W} _inst {M} cs J I K w =>
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
      List.sum (List.map (fun e => CoxeterSystem.length cs (crossing e).1) es) }
```

Immediate internal dependencies: BrinkHowlettGroupoid, SimpleWallCrossings, ElementaryWallMorphism.

Existing repository dependencies: none.

Immediate external dependencies: standard-expressions-parabolic, standard-expressions-root-action, standard-expressions-mathlib, standard-expressions-lean-core (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [translation](translations/StandardExpressions.json), [proof](Proofs/StandardExpressions.lean), [compilation evidence](evidence/StandardExpressions-compile.json).

## StandardGeodesicCorrespondence: Standard expressions lift to geodesic paths

Prerequisite; compiled and axiom-checked.

### Article

A composable sequence of simple wall crossings is a geodesic path exactly when its product is a standard expression in BH. Every w∈Hom_BH(I,K) has a standard expression; its lift from (x,I) ends at (xw,K).

[Lemma 4.10 and equations (4.11)–(4.12), printed p. 18.](https://arxiv.org/pdf/2509.21915#page=18)

### Alphabeta Math

In finite rank, each standard expression has a unique geodesic lift from any prescribed chamber of its source type. For specified crossings, target-source compatibility is required. The empty expression corresponds to a one-chamber path. This geometric supplier alone does not establish arbitrary-rank existence.

[Statement and Facts & Assumptions of lem-standard-geodesic-artin-tits-normalisers.](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-standard-geodesic-artin-tits-normalisers)

### Lean translation

Translation source: portal. Explicit user direction selects the finite-rank geometric endpoint at https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-standard-geodesic-artin-tits-normalisers. The full report at https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects was checked and does not identify Lemma 4.10 or equations (4.11)–(4.12) as defective statements. Finite rank is user-directed, not a reported correction; neither W nor W_J is assumed finite. Specified records each crossing's source chamber; path enforces exact target-source compatibility through the chamber labels identified geometrically by ChamberLabelling and AdjacentWallFormula. Geodesicity minimizes crossing count. The statement preserves the standard-expression equivalence, unique geodesic lift from each prescribed source with endpoint (xw,K), existence of standard expressions in this finite-rank supplier, and the empty-expression convention. The separate arbitrary-rank algebraic covering and StandardFactorCount endpoints remain unrestricted. The type elaborated successfully with ArtinDeligne and the supplied prerequisite definitions. [Defect report](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects).

```lean
theorem StandardGeodesicCorrespondence : ∀ {S W : Type*} [Finite S] [Group W] {M : CoxeterMatrix S}
  (cs : CoxeterSystem M W) (J : Set S),
  let Obj := { I : Set S // ∃ g : W,
    Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g))
      (CoxeterSystem.parabolic cs I) = CoxeterSystem.parabolic cs J }
  let label : W → Set S → Prop := fun x I =>
    Set.image (fun u : W => u * x) (CoxeterSystem.parabolic cs J : Set W) =
      Set.image (fun u : W => x * u) (CoxeterSystem.parabolic cs I : Set W) ∧
    CoxeterSystem.IsMinimalCosetRep cs I x
  let component : Set S → S → Set S := fun I a =>
    { b | b ∈ Set.insert a I ∧ Relation.ReflTransGen
      (fun i j : S => i ∈ Set.insert a I ∧ j ∈ Set.insert a I ∧ i ≠ j ∧ M i j ≠ 2) a b }
  let Atom := { p : Obj × S // p.2 ∉ p.1.val ∧
    Finite (CoxeterSystem.parabolic cs (component p.1.val p.2)) }
  let crossing := fun e : Atom =>
    SimpleWallCrossings S W M cs e.val.1.val e.val.2 e.property.1 e.property.2
  let Specified := { p : W × Atom // label p.1 p.2.val.1.val }
  let word : List Specified → List Atom := fun es => List.map (fun e => e.val.2) es
  let path : List Specified → (W × Set S) → (W × Set S) → Prop := fun es A B =>
    label A.1 A.2 ∧ label B.1 B.2 ∧
    List.foldr
      (fun e tail P => P = (e.val.1, e.val.2.val.1.val) ∧
        tail ((crossing e.val.2).2.2 e.val.1))
      (fun P => P = B) es A
  let geodesic : List Specified → (W × Set S) → (W × Set S) → Prop := fun es A B =>
    path es A B ∧ ∀ fs : List Specified, path fs A B → List.length es ≤ List.length fs
  (∀ (I K : Obj) (x y : W) (es : List Specified),
    geodesic es (x, I.val) (y, K.val) ↔
      path es (x, I.val) (y, K.val) ∧
      ∃ (w : (BrinkHowlettGroupoid cs J).Hom I K)
        (e : StandardExpressions cs J I K w),
        w.val = x⁻¹ * y ∧ e.val = word es) ∧
  (∀ (I K : Obj) (w : (BrinkHowlettGroupoid cs J).Hom I K)
    (e : StandardExpressions cs J I K w) (x : W), label x I.val →
    ∃! es : List Specified,
      word es = e.val ∧ geodesic es (x, I.val) (x * w.val, K.val)) ∧
  (∀ (I K : Obj) (w : (BrinkHowlettGroupoid cs J).Hom I K),
    Nonempty (StandardExpressions cs J I K w)) ∧
  (∀ (I : Obj) (x : W), label x I.val →
    path List.nil (x, I.val) (x, I.val) ∧
    geodesic List.nil (x, I.val) (x, I.val) ∧ word List.nil = List.nil)
```

Immediate internal dependencies: StandardExpressions, GeodesicAdditivity, UniversalBrinkHowlettCover, UniversalGenerators, ChamberMorphismCorrespondence.

Existing repository dependencies: none.

Immediate external dependencies: sgc-direct-project-artinchambers-weakinversions, sgc-direct-project-artinlandmarkvendor-geometric-sign, sgc-direct-lean-init-bindernamehint, sgc-direct-lean-init-classical, sgc-direct-lean-init-core, sgc-direct-lean-init-data-cast, sgc-direct-lean-init-data-function, sgc-direct-lean-init-data-int-basic, sgc-direct-lean-init-data-int-lemmas, sgc-direct-lean-init-data-int-order, sgc-direct-lean-init-data-list-basic, sgc-direct-lean-init-data-list-lemmas, sgc-direct-lean-init-data-list-takedrop, sgc-direct-lean-init-data-nat-basic, sgc-direct-lean-init-data-nezero, sgc-direct-lean-init-data-order-lemmas, sgc-direct-lean-init-data-zero, sgc-direct-lean-init-ext, sgc-direct-lean-init-omega-coeffs, sgc-direct-lean-init-omega-constraint, sgc-direct-lean-init-omega-int, sgc-direct-lean-init-omega-linearcombo, sgc-direct-lean-init-prelude, sgc-direct-lean-init-proplemmas, sgc-direct-lean-init-simplemmas, sgc-direct-mathlib-mathlib-algebra-algebra-basic, sgc-direct-mathlib-mathlib-algebra-algebra-defs, sgc-direct-mathlib-mathlib-algebra-bigoperators-finsupp-basic, sgc-direct-mathlib-mathlib-algebra-bigoperators-group-finset-basic, sgc-direct-mathlib-mathlib-algebra-bigoperators-group-finset-defs, sgc-direct-mathlib-mathlib-algebra-bigoperators-group-finset-piecewise, sgc-direct-mathlib-mathlib-algebra-bigoperators-pi, sgc-direct-mathlib-mathlib-algebra-charp-defs, sgc-direct-mathlib-mathlib-algebra-charzero-defs, sgc-direct-mathlib-mathlib-algebra-field-defs, sgc-direct-mathlib-mathlib-algebra-group-basic, sgc-direct-mathlib-mathlib-algebra-group-commute-defs, sgc-direct-mathlib-mathlib-algebra-group-defs, sgc-direct-mathlib-mathlib-algebra-group-divinvmonoid, sgc-direct-mathlib-mathlib-algebra-group-end, sgc-direct-mathlib-mathlib-algebra-group-equiv-defs, sgc-direct-mathlib-mathlib-algebra-group-finsupp, sgc-direct-mathlib-mathlib-algebra-group-hom-defs, sgc-direct-mathlib-mathlib-algebra-group-isapply, sgc-direct-mathlib-mathlib-algebra-group-monoid, sgc-direct-mathlib-mathlib-algebra-group-nat-defs, sgc-direct-mathlib-mathlib-algebra-group-pi-basic, sgc-direct-mathlib-mathlib-algebra-group-semigroup, sgc-direct-mathlib-mathlib-algebra-group-subgroup-defs, sgc-direct-mathlib-mathlib-algebra-group-subgroup-lattice, sgc-direct-mathlib-mathlib-algebra-group-subgroup-map, sgc-direct-mathlib-mathlib-algebra-group-submonoid-defs, sgc-direct-mathlib-mathlib-algebra-group-subsemigroup-defs, sgc-direct-mathlib-mathlib-algebra-groupwithzero-action-defs, sgc-direct-mathlib-mathlib-algebra-groupwithzero-basic, sgc-direct-mathlib-mathlib-algebra-groupwithzero-defs, sgc-direct-mathlib-mathlib-algebra-groupwithzero-nat, sgc-direct-mathlib-mathlib-algebra-groupwithzero-units-basic, sgc-direct-mathlib-mathlib-algebra-module-defs, sgc-direct-mathlib-mathlib-algebra-module-linearmap-defs, sgc-direct-mathlib-mathlib-algebra-module-linearmap-end, sgc-direct-mathlib-mathlib-algebra-module-submodule-basic, sgc-direct-mathlib-mathlib-algebra-module-submodule-defs, sgc-direct-mathlib-mathlib-algebra-module-submodule-eqlocus, sgc-direct-mathlib-mathlib-algebra-module-submodule-ker, sgc-direct-mathlib-mathlib-algebra-module-submodule-map, sgc-direct-mathlib-mathlib-algebra-nezero, sgc-direct-mathlib-mathlib-algebra-order-archimedean-real-basic, sgc-direct-mathlib-mathlib-algebra-order-bigoperators-group-finset, sgc-direct-mathlib-mathlib-algebra-order-floor-defs, sgc-direct-mathlib-mathlib-algebra-order-group-unbundled-basic, sgc-direct-mathlib-mathlib-algebra-order-groupwithzero-basic, sgc-direct-mathlib-mathlib-algebra-order-groupwithzero-defs, sgc-direct-mathlib-mathlib-algebra-order-module-defs, sgc-direct-mathlib-mathlib-algebra-order-monoid-defs, sgc-direct-mathlib-mathlib-algebra-order-monoid-unbundled-basic, sgc-direct-mathlib-mathlib-algebra-order-monoid-unbundled-defs, sgc-direct-mathlib-mathlib-algebra-order-ring-defs, sgc-direct-mathlib-mathlib-algebra-order-star-basic, sgc-direct-mathlib-mathlib-algebra-order-star-real, sgc-direct-mathlib-mathlib-algebra-ring-defs, sgc-direct-mathlib-mathlib-algebra-ring-hom-defs, sgc-direct-mathlib-mathlib-algebra-ring-int-defs, sgc-direct-mathlib-mathlib-algebra-ring-nat, sgc-direct-mathlib-mathlib-algebra-torsor-defs, sgc-direct-mathlib-mathlib-analysis-complex-trigonometric, sgc-direct-mathlib-mathlib-analysis-normed-field-basic, sgc-direct-mathlib-mathlib-analysis-normed-ring-basic, sgc-direct-mathlib-mathlib-analysis-rclike-basic, sgc-direct-mathlib-mathlib-analysis-specialfunctions-trigonometric-basic, sgc-direct-mathlib-mathlib-basic-existsunique, sgc-direct-mathlib-mathlib-basic-finite-defs, sgc-direct-mathlib-mathlib-basic-finite-prod, sgc-direct-mathlib-mathlib-basic-funlike-basic, sgc-direct-mathlib-mathlib-basic-funlike-equiv, sgc-direct-mathlib-mathlib-basic-isempty-defs, sgc-direct-mathlib-mathlib-basic-real-basic, sgc-direct-mathlib-mathlib-basic-real-star, sgc-direct-mathlib-mathlib-basic-setlike-basic, sgc-direct-mathlib-mathlib-basic-unique, sgc-direct-mathlib-mathlib-categorytheory-category-basic, sgc-direct-mathlib-mathlib-categorytheory-groupoid, sgc-direct-mathlib-mathlib-combinatorics-quiver-basic, sgc-direct-mathlib-mathlib-data-finset-defs, sgc-direct-mathlib-mathlib-data-finsupp-defs, sgc-direct-mathlib-mathlib-data-finsupp-order, sgc-direct-mathlib-mathlib-data-finsupp-pointwise, sgc-direct-mathlib-mathlib-data-finsupp-smul, sgc-direct-mathlib-mathlib-data-finsupp-smulwithzero, sgc-direct-mathlib-mathlib-data-finsupp-single, sgc-direct-mathlib-mathlib-data-fintype-basic, sgc-direct-mathlib-mathlib-data-fintype-card, sgc-direct-mathlib-mathlib-data-fintype-equivfin, sgc-direct-mathlib-mathlib-data-fintype-lattice, sgc-direct-mathlib-mathlib-data-int-cast-defs, sgc-direct-mathlib-mathlib-data-list-induction, sgc-direct-mathlib-mathlib-data-nat-basic, sgc-direct-mathlib-mathlib-data-nat-cast-defs, sgc-direct-mathlib-mathlib-data-nat-cast-order-basic, sgc-direct-mathlib-mathlib-data-nat-init, sgc-direct-mathlib-mathlib-data-set-basic, sgc-direct-mathlib-mathlib-data-set-booleanalgebra, sgc-direct-mathlib-mathlib-data-set-card, sgc-direct-mathlib-mathlib-data-set-coesort, sgc-direct-mathlib-mathlib-data-set-defs, sgc-direct-mathlib-mathlib-data-set-disjoint, sgc-direct-mathlib-mathlib-data-set-finite-basic, sgc-direct-mathlib-mathlib-data-set-finite-lattice, sgc-direct-mathlib-mathlib-data-set-finite-powerset, sgc-direct-mathlib-mathlib-data-set-finite-range, sgc-direct-mathlib-mathlib-data-set-image, sgc-direct-mathlib-mathlib-data-set-insert, sgc-direct-mathlib-mathlib-data-set-operations, sgc-direct-mathlib-mathlib-grouptheory-coxeter-basic, sgc-direct-mathlib-mathlib-grouptheory-coxeter-length, sgc-direct-mathlib-mathlib-grouptheory-coxeter-matrix, sgc-direct-mathlib-mathlib-grouptheory-groupaction-hom, sgc-direct-mathlib-mathlib-grouptheory-groupaction-ring, sgc-direct-mathlib-mathlib-linearalgebra-bilinearmap, sgc-direct-mathlib-mathlib-linearalgebra-finsupp-defs, sgc-direct-mathlib-mathlib-linearalgebra-span-defs, sgc-direct-mathlib-mathlib-logic-equiv-defs, sgc-direct-mathlib-mathlib-logic-function-basic, sgc-direct-mathlib-mathlib-logic-relation, sgc-direct-mathlib-mathlib-order-basic, sgc-direct-mathlib-mathlib-order-booleanalgebra-set, sgc-direct-mathlib-mathlib-order-boundedorder-basic, sgc-direct-mathlib-mathlib-order-completebooleanalgebra, sgc-direct-mathlib-mathlib-order-completepartialorder, sgc-direct-mathlib-mathlib-order-defs-lattice, sgc-direct-mathlib-mathlib-order-defs-linearorder, sgc-direct-mathlib-mathlib-order-defs-partialorder, sgc-direct-mathlib-mathlib-order-disjoint, sgc-direct-mathlib-mathlib-order-lattice, sgc-direct-mathlib-mathlib-order-preorder-finsupp, sgc-direct-mathlib-mathlib-order-relclasses, sgc-direct-mathlib-mathlib-order-setnotation, sgc-direct-mathlib-mathlib-representationtheory-basic, sgc-direct-mathlib-mathlib-settheory-cardinal-finite, sgc-direct-mathlib-mathlib-tactic-abel, sgc-direct-mathlib-mathlib-tactic-canceldenoms-core, sgc-direct-mathlib-mathlib-tactic-linarith-lemmas, sgc-direct-mathlib-mathlib-tactic-linarith-preprocessing, sgc-direct-mathlib-mathlib-tactic-normnum-basic, sgc-direct-mathlib-mathlib-tactic-normnum-eq, sgc-direct-mathlib-mathlib-tactic-normnum-ineq, sgc-direct-mathlib-mathlib-tactic-normnum-inv, sgc-direct-mathlib-mathlib-tactic-normnum-result, sgc-direct-mathlib-mathlib-tactic-push, sgc-direct-mathlib-mathlib-tactic-ring-basic, sgc-direct-mathlib-mathlib-tactic-ring-common, sgc-direct-project-tauceti-grouptheory-coxeter-basic, sgc-direct-project-tauceti-grouptheory-coxeter-geometric-basic, sgc-direct-project-tauceti-grouptheory-coxeter-parabolic (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [translation](translations/StandardGeodesicCorrespondence.json), [proof](Proofs/StandardGeodesicCorrespondence.lean), [compilation evidence](evidence/StandardGeodesicCorrespondence-compile.json).

## StandardFactorCount: Arbitrary-rank existence and parallel-class factor count

Prerequisite; compiled and axiom-checked.

### Article

No standalone article statement gives the parallel-class formula selected here. This is a portal helper supporting existence of standard expressions and invariance of their factor count; the parent article assertions are Lemma 4.10 and Corollary 4.13.

[Parent results: Lemma 4.10 and Corollary 4.13, printed p. 18. The formula m=|C(w)| is not attributed to an article lemma.](https://arxiv.org/pdf/2509.21915#page=18)

### Alphabeta Math

Every article morphism w has a standard expression. If an expression has m factors, then m=|C(w)|, using the opposite root-action arrow with the same label. Here C(w) is the finite set of real parallel classes contained in its positive inversion set. Its declared algebraic suppliers allow arbitrary rank.

[Statement and Facts & Assumptions of lem-author-b19d43a8e520-bh-standard-factor-count; source references are empty, so article attribution is only through the stated parent results.](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-author-b19d43a8e520-bh-standard-factor-count)

### Lean translation

Translation source: article. The report does not identify this endpoint statement as defective. [Defect report](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects).

```lean
theorem StandardFactorCount : ∀ {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) (I K : { L : Set S // ∃ g : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (CoxeterSystem.parabolic cs L) = CoxeterSystem.parabolic cs J }) (w : (BrinkHowlettGroupoid cs J).Hom I K), let roots : Set (Finsupp S Real) := CoxeterSystem.geometricRoots cs; let act := CoxeterSystem.geometricRepresentation cs; let parallelClass : Finsupp S Real → Set (Finsupp S Real) := fun α => { β | β ∈ roots ∧ ∀ L, ∀ f : (BrinkHowlettGroupoid cs J).Hom L I, (0 < act f.val α ↔ 0 < act f.val β) }; let realRoot : Finsupp S Real → Prop := fun α => α ∈ roots ∧ ∃ L, ∃ f : (BrinkHowlettGroupoid cs J).Hom L I, ¬ (0 < α ↔ 0 < act f.val α); let inversions : Set (Finsupp S Real) := { α | α ∈ roots ∧ 0 < α } ∩ Set.image (act w.val) { α | α ∈ roots ∧ α < 0 }; let classes : Set (Set (Finsupp S Real)) := { c | (∃ α, realRoot α ∧ c = parallelClass α) ∧ c ⊆ inversions }; Nonempty (StandardExpressions cs J I K w) ∧ Set.Finite classes ∧ ∀ e : StandardExpressions cs J I K w, List.length e.val = Nat.card { c : Set (Finsupp S Real) // c ∈ classes }
```

Immediate internal dependencies: BrinkHowlettGroupoid, StandardExpressions.

Existing repository dependencies: none.

Immediate external dependencies: sfc-final-project-1, sfc-final-project-2, sfc-final-project-3, sfc-final-project-4, sfc-final-project-5, sfc-final-mathlib, sfc-final-init (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [translation](translations/StandardFactorCount.json), [proof](Proofs/StandardFactorCount.lean), [compilation evidence](evidence/StandardFactorCount-compile.json).

## GeneratorsAndStandardLength: Elementary generation and invariance of standard length

Prerequisite; compiled and axiom-checked.

### Article

BH(J) is generated by v_{a,I} for associates I and a∉I with W_[I,a] finite. Any two standard expressions of the same morphism, with the same source, have the same number of factors.

[Corollary 4.13(1)–(2), printed p. 18.](https://arxiv.org/pdf/2509.21915#page=18)

### Alphabeta Math

The same generation and equal-factor-count assertions. Its current proof suppliers use the arbitrary-rank StandardFactorCount endpoint rather than relying on finite-rank chamber geometry.

[Statement and Source notes of cor-brink-howlett-generators-length-artin-tits-normalisers.](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-cor-brink-howlett-generators-length-artin-tits-normalisers)

### Lean translation

Translation source: article. The report does not identify this endpoint statement as defective. [Defect report](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects).

```lean
theorem GeneratorsAndStandardLength : ∀ {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S),
  let Obj := { L : Set S // ∃ g : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (CoxeterSystem.parabolic cs L) = CoxeterSystem.parabolic cs J }
  let component : Set S → S → Set S := fun L a =>
    { b | b ∈ Set.insert a L ∧ Relation.ReflTransGen
      (fun i j : S => i ∈ Set.insert a L ∧ j ∈ Set.insert a L ∧ i ≠ j ∧ M i j ≠ 2) a b }
  let Atom := { p : Obj × S // p.2 ∉ p.1.val ∧ Finite (CoxeterSystem.parabolic cs (component p.1.val p.2)) }
  let crossing := fun e : Atom => SimpleWallCrossings S W M cs e.val.1.val e.val.2 e.property.1 e.property.2
  (∀ (I K : Obj) (w : (BrinkHowlettGroupoid cs J).Hom I K),
    ∃ es : List Atom,
      List.foldr
        (fun e tail L => L = e.val.1.val ∧ tail (crossing e).2.1)
        (fun L => L = K.val) es I.val ∧
      List.prod (List.map (fun e => (crossing e).1) es) = w.val) ∧
  (∀ (I K : Obj) (w : (BrinkHowlettGroupoid cs J).Hom I K)
    (e f : StandardExpressions cs J I K w), List.length e.val = List.length f.val)
```

Immediate internal dependencies: StandardExpressions, StandardFactorCount.

Existing repository dependencies: none.

Immediate external dependencies: gsl-parabolic, gsl-root-action, gsl-mathlib, gsl-core (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [translation](translations/GeneratorsAndStandardLength.json), [proof](Proofs/GeneratorsAndStandardLength.lean), [compilation evidence](evidence/GeneratorsAndStandardLength-compile.json).

## FiniteRelativeLongest: Finite relative longest element inside an arbitrary system

Prerequisite; compiled and axiom-checked.

### Article

No standalone article lemma states this full construction and inversion-set formula. It is a portal helper for Lemma 4.15: finite Φ_{I∪{a,b}}\Φ_I allows construction inside the union of the components meeting {a,b}, without making I or the ambient system spherical.

[Parent result: Lemma 4.15 and equation (4.16), printed p. 19; related inverse characterization in Remark 4.17, printed p. 19.](https://arxiv.org/pdf/2509.21915#page=19)

### Alphabeta Math

At arbitrary rank, let a,b∉I be distinct, T=I∪{a,b}, and Φ_T\Φ_I finite. Let D be the union of components of T meeting {a,b}. Then W_D is finite. For r=w_Dw_{D∩I}, rΠ_I=Π_K for an associate K⊆T; q=r⁻¹ is an article morphism I→K and N(q)=Φ_T⁺\Φ_I⁺, where N(x)=Φ⁺∩xΦ⁻.

[Statement and External input of lem-author-a7d202611130-finite-relative-longest.](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-author-a7d202611130-finite-relative-longest)

### Lean translation

Translation source: article. The report does not identify this endpoint statement as defective. [Defect report](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects).

```lean
theorem FiniteRelativeLongest : ∀ {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (I : Set S) (a b : S), a ∉ I → b ∉ I → a ≠ b → let T : Set S := Set.insert a (Set.insert b I); let parabolicRoots : Set S → Set (Finsupp S Real) := fun L => {α | ∃ w : W, w ∈ CoxeterSystem.parabolic cs L ∧ ∃ i : S, i ∈ L ∧ CoxeterSystem.geometricRepresentation cs w (Finsupp.single i (1 : Real)) = α}; let simpleRoots : Set S → Set (Finsupp S Real) := fun L => Set.image (fun i : S => Finsupp.single i (1 : Real)) L; let positiveRoots : Set (Finsupp S Real) := {α | α ∈ CoxeterSystem.geometricRoots cs ∧ 0 < α}; let negativeRoots : Set (Finsupp S Real) := {α | α ∈ CoxeterSystem.geometricRoots cs ∧ α < 0}; let D : Set S := {i | i ∈ T ∧ (Relation.ReflTransGen (fun j k : S => j ∈ T ∧ k ∈ T ∧ j ≠ k ∧ M j k ≠ 2) a i ∨ Relation.ReflTransGen (fun j k : S => j ∈ T ∧ k ∈ T ∧ j ≠ k ∧ M j k ≠ 2) b i)}; Set.Finite (parabolicRoots T \ parabolicRoots I) → Finite (CoxeterSystem.parabolic cs D) ∧ ∃ wD : CoxeterSystem.parabolic cs D, ∃ wDI : CoxeterSystem.parabolic cs (D ∩ I), (∀ u : CoxeterSystem.parabolic cs D, CoxeterSystem.length cs (u : W) ≤ CoxeterSystem.length cs (wD : W)) ∧ (∀ u : CoxeterSystem.parabolic cs (D ∩ I), CoxeterSystem.length cs (u : W) ≤ CoxeterSystem.length cs (wDI : W)) ∧ (let r : W := (wD : W) * (wDI : W); let q : W := r⁻¹; ∃ K : Set S, K ⊆ T ∧ (∃ g : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (CoxeterSystem.parabolic cs K) = CoxeterSystem.parabolic cs I) ∧ Set.image (CoxeterSystem.geometricRepresentation cs r) (simpleRoots I) = simpleRoots K ∧ Set.image (CoxeterSystem.geometricRepresentation cs q) (simpleRoots K) = simpleRoots I ∧ positiveRoots ∩ Set.image (CoxeterSystem.geometricRepresentation cs q) negativeRoots = (parabolicRoots T ∩ positiveRoots) \ (parabolicRoots I ∩ positiveRoots))
```

Immediate internal dependencies: BrinkHowlettGroupoid.

Existing repository dependencies: none.

Immediate external dependencies: frl-final-cuvsny-project-1, frl-final-cuvsny-project-2, frl-final-cuvsny-project-3, frl-final-cuvsny-project-4, frl-final-cuvsny-project-5, frl-final-cuvsny-mathlib-inventory, frl-final-cuvsny-lean-inventory (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [translation](translations/FiniteRelativeLongest.json), [proof](Proofs/FiniteRelativeLongest.lean), [compilation evidence](evidence/FiniteRelativeLongest-compile.json).

## TwoGeneratorMinimal: Minimal common prefix and its two standard expressions

Prerequisite; compiled and axiom-checked.

### Article

Let I be an associate of J and a,b∉I distinct, with |Φ_{I∪{a,b}}\Φ_I|<∞. There is an associate K and v_{a,b,I}:I→K left-divisible by v_{a,I},v_{b,I}, with exactly two standard expressions of equal factor count, starting respectively with these generators. Every BH morphism from I having both generators as length-additive left divisors has v_{a,b,I} as a left divisor. Thus this common multiple is minimal for left divisibility and standard-expression length.

[Lemma 4.15(1)–(2) and equation (4.16), printed p. 19.](https://arxiv.org/pdf/2509.21915#page=19)

### Alphabeta Math

The same theorem with its finite relative-root hypothesis retained. It chooses v_{a,b,I}=(w_Dw_{D∩I})⁻¹ using FiniteRelativeLongest. The declared supporting endpoints separately establish elementary prefixes, simultaneous-prefix minimality and exactly two standard words.

[Statement and Source notes of lem-two-generator-minimal-artin-tits-normalisers.](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-lem-two-generator-minimal-artin-tits-normalisers)

### Lean translation

Translation source: article. The report does not identify this endpoint statement as defective. [Defect report](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects).

```lean
theorem TwoGeneratorMinimal : ∀ {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S),
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
      (∀ (K' : Obj) (w : (BrinkHowlettGroupoid cs J).Hom I K'), leftDiv va w.val → leftDiv vb w.val → leftDiv q.val w.val ∧ ∀ e : StandardExpressions cs J I K' w, List.length ea.val ≤ List.length e.val)
```

Immediate internal dependencies: StandardExpressions, FiniteRelativeLongest, StandardFactorCount, GeneratorsAndStandardLength.

Existing repository dependencies: none.

Immediate external dependencies: tgm-1, tgm-2, tgm-3, tgm-4, tgm-5, tgm-mathlib, tgm-init, tgm-aesop (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [translation](translations/TwoGeneratorMinimal.json), [proof](Proofs/TwoGeneratorMinimal.lean), [compilation evidence](evidence/TwoGeneratorMinimal-compile.json).

## AtomicBraidRelations: Atomic braid relations and contextual replacements

Prerequisite; compiled and axiom-checked.

### Article

Under Lemma 4.15's hypotheses, equating the two standard expressions of v_{a,b,I} in (4.16) is an atomic braid relation.

[Definition 4.18, Lemma 4.15 and equation (4.16), printed p. 19.](https://arxiv.org/pdf/2509.21915#page=19)

### Alphabeta Math

For distinct a,b outside an associate I with finite Φ_{I∪{a,b}}\Φ_I, the equality of the two supplied standard expressions defines the atomic braid relation. In the main theorem a move replaces either side inside a composable expression, retaining the surrounding factors.

[Definition of def-atomic-braid-artin-tits-normalisers; contextual use in the Statement of thm-atomic-matsumoto-artin-tits-normalisers.](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-def-atomic-braid-artin-tits-normalisers)

### Lean translation

Translation source: article. The report does not identify this endpoint statement as defective. [Defect report](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects).

```lean
def AtomicBraidRelations : ∀ {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S),
  let Obj := { L : Set S // ∃ g : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (CoxeterSystem.parabolic cs L) = CoxeterSystem.parabolic cs J }
  let component : Set S → S → Set S := fun L a =>
    { b | b ∈ Set.insert a L ∧ Relation.ReflTransGen
      (fun i j : S => i ∈ Set.insert a L ∧ j ∈ Set.insert a L ∧ i ≠ j ∧ M i j ≠ 2) a b }
  let Atom := { p : Obj × S // p.2 ∉ p.1.val ∧ Finite (CoxeterSystem.parabolic cs (component p.1.val p.2)) }
  List Atom → List Atom → Prop := fun {S W} _inst {M} cs J =>
  let Obj := { L : Set S // ∃ g : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (CoxeterSystem.parabolic cs L) = CoxeterSystem.parabolic cs J }
  let component : Set S → S → Set S := fun L a =>
    { b | b ∈ Set.insert a L ∧ Relation.ReflTransGen
      (fun i j : S => i ∈ Set.insert a L ∧ j ∈ Set.insert a L ∧ i ≠ j ∧ M i j ≠ 2) a b }
  let Atom := { p : Obj × S // p.2 ∉ p.1.val ∧ Finite (CoxeterSystem.parabolic cs (component p.1.val p.2)) }
  let crossing := fun e : Atom => SimpleWallCrossings S W M cs e.val.1.val e.val.2 e.property.1 e.property.2
  let composable : List Atom → Set S → Set S → Prop := fun es L K =>
    List.foldr
      (fun e tail N => N = e.val.1.val ∧ tail (crossing e).2.1)
      (fun N => N = K) es L
  let parabolicRoots : Set S → Set (Finsupp S Real) := fun L =>
    { α | ∃ u : W, u ∈ CoxeterSystem.parabolic cs L ∧ ∃ i : S, i ∈ L ∧
      CoxeterSystem.geometricRepresentation cs u (Finsupp.single i (1 : Real)) = α }
  let braid : List Atom → List Atom → Prop := fun u v =>
    ∃ (L : Obj) (a b : S) (ha : a ∉ L.val) (hb : b ∉ L.val)
      (hab : a ≠ b)
      (hfin : Set.Finite (parabolicRoots (Set.insert a (Set.insert b L.val)) \ parabolicRoots L.val)),
      let h0 := TwoGeneratorMinimal cs J L a b ha hb hab hfin
      let hDa := Classical.choose h0
      let h1 := Classical.choose_spec h0
      let hDb := Classical.choose h1
      let h2 := Classical.choose_spec h1
      let K := Classical.choose h2
      let h3 := Classical.choose_spec h2
      let q := Classical.choose h3
      let h4 := Classical.choose_spec h3
      let ea := Classical.choose h4
      let eb := Classical.choose (Classical.choose_spec h4)
      (u = ea.val ∧ v = eb.val) ∨ (u = eb.val ∧ v = ea.val)
  fun es fs =>
    ∃ pre u v post : List Atom,
      braid u v ∧
      es = pre ++ u ++ post ∧
      fs = pre ++ v ++ post ∧
      ∃ L K : Obj, composable es L.val K.val ∧ composable fs L.val K.val
```

Immediate internal dependencies: StandardExpressions, TwoGeneratorMinimal.

Existing repository dependencies: none.

Immediate external dependencies: abr-parabolic, abr-action, abr-mathlib, abr-core (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [translation](translations/AtomicBraidRelations.json), [proof](Proofs/AtomicBraidRelations.lean), [compilation evidence](evidence/AtomicBraidRelations-compile.json).

## AtomicMatsumoto: Theorem 1.4 / 4.21: Atomic Matsumoto

Main theorem; compiled and axiom-checked.

### Article

Let Γ be a Coxeter diagram, J⊆Γ₀, BH(J) its Brink–Howlett groupoid, and I,K associates of J. Any two standard expressions of w∈Hom_BH(I,K) are related by a sequence of atomic braid relations. Preserve the arbitrary-Coxeter-type scope: neither W, W_J, nor the enlarged parabolics W_{I∪{a}} are globally assumed finite. Standard expressions and atomic braid relations have exactly the meanings of Definitions 4.9 and 4.18.

[Theorem 1.4, printed p. 3; Theorem 4.21 and Remark 4.22, printed p. 20; Definitions 4.9 and 4.18, printed pp. 17 and 19.](https://arxiv.org/pdf/2509.21915#page=20)

### Alphabeta Math

For a Coxeter system without rank or type restriction, arbitrary J and associates I,K, any two finite length-additive elementary expressions of the same morphism w:I→K are connected by finitely many atomic braid relations. The finite relative-root condition needed for a two-generator relation is derived from the common prefixes; it is not added as a hypothesis of the main theorem.

[Statement, Facts & Assumptions and External input of thm-atomic-matsumoto-artin-tits-normalisers.](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/item-thm-atomic-matsumoto-artin-tits-normalisers)

### Lean translation

Translation source: article. The report does not identify this endpoint statement as defective. [Defect report](https://alphabetamath.cc/research-portal/artin-tits-normalisers-2509-21915/prerequisite-omissions-and-potential-defects).

```lean
theorem AtomicMatsumoto : ∀ {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S) (I K : { L : Set S // ∃ g : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj g)) (CoxeterSystem.parabolic cs L) = CoxeterSystem.parabolic cs J }) (w : (BrinkHowlettGroupoid cs J).Hom I K) (e f : StandardExpressions cs J I K w), Relation.ReflTransGen (AtomicBraidRelations cs J) e.val f.val
```

Immediate internal dependencies: StandardExpressions, StandardFactorCount, GeneratorsAndStandardLength, TwoGeneratorMinimal, AtomicBraidRelations.

Existing repository dependencies: none.

Immediate external dependencies: am-conditional-mathlib, am-conditional-core, am-conditional-project, am-final-artinchambers-weakinversions, am-final-artinlandmarkvendor-geometric-sign, am-final-tauceti-grouptheory-coxeter-basic, am-final-tauceti-grouptheory-coxeter-geometric-basic, am-final-tauceti-grouptheory-coxeter-parabolic, am-final-mathlib, am-final-init (see [ledger](EXTERNAL_PROOFS.md)); mathlib is imported as the base library.

Files: [translation](translations/AtomicMatsumoto.json), [proof](Proofs/AtomicMatsumoto.lean), [compilation evidence](evidence/AtomicMatsumoto-compile.json).
