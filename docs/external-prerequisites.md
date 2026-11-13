# External Lean prerequisite search for the Lemma 2.8 kernel milestone

Research date: 2026-11-14. Scope: the generalized kernel theorem in
`formalizations/artin-normalisers/`, as specified in `PLAN.md`; no external
proof has been imported or copied, and no project proof was edited in this
search.

## Decision

No additional external prerequisite was found that should be added to this
milestone. The relevant normalizer/quotient foundations are already in the
pinned mathlib. The external projects below contain related constructions,
but their inspected declarations either specialize to a different mathematical
problem or simply wrap existing mathlib results. Adding them would create
version and dependency work without supplying a missing proof.

This is a bounded search result, not a claim that no equivalent theorem exists
anywhere on GitHub. No external proof is accepted as formally verified here:
the rejected candidates were not compiled, their transitive axioms were not
audited, and their kernel declarations were not replayed. Source inspection,
README claims, CI badges, and `#check` would not suffice for acceptance.

## Baseline and exact missing step

Read the repository's `CLAUDE.md` and `README.md`, the complete local
`research/lean-lemma28/PLAN.md`, and the three current proof modules
`NormalizerMap.lean`, `QuotientMap.lean`, and `Kernel.lean` before searching.
The package pins Lean `v4.36.0-rc2` and mathlib
`65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`.

The target has arbitrary groups, arbitrary `f : G →* H`, and arbitrary
`A : Subgroup G`. It identifies the kernel of the map
`N_G(A)/A → N_H(A.map f)/(A.map f)` with the quotient image of
`ker f ∩ N_G(A)`, and provides representatives in `ker f`. It requires no
surjectivity hypothesis and no finite-index, matrix, modular, or Coxeter data.

At the pinned mathlib revision:

- [`Subgroup.le_normalizer_map`](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Group/Subgroup/Basic.lean#L477)
  states `(normalizer A).map f ≤ normalizer (A.map f)`.
- [`Subgroup.normal_in_normalizer`](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/Algebra/Group/Subgroup/Basic.lean#L508)
  supplies normality of `A.subgroupOf (normalizer A)`.
- [`QuotientGroup.ker_map`](https://github.com/leanprover-community/mathlib4/blob/65d730f7150f21fdfa32f3e73a3f549c1f96a0e9/Mathlib/GroupTheory/QuotientGroup/Defs.lean#L333)
  states, for normal `N ≤ G`, normal `M ≤ H`, and
  `h : N ≤ M.comap f`,
  `(QuotientGroup.map N M f h).ker = (M.comap f).map (QuotientGroup.mk' N)`.

Thus even the general induced-quotient kernel supplier is present already.
For the current problem, instantiate its ambient groups with the two
normalizers and its homomorphism with `normalizerMap f A`. The remaining
identification is the elementary adjustment of a representative `g` by
`a⁻¹`, choosing `a ∈ A` with `f a = f g`. It is precisely the local
`quotientMap_mem_ker_iff` argument. A candidate would be useful if it supplied
this exact general identification without extra assumptions or substantial
translation overhead. None inspected did.

These baseline declarations were read in the actual local pinned mathlib
source, not inferred from current online documentation. Their compilation,
axiom audit, and kernel replay belong to the root package verification; this
search does not independently certify that verification.

## F-Najman/normalizer-lean

Repository: [normalizer-lean](https://github.com/F-Najman/normalizer-lean).
Inspected checkout SHA: `1f4c27ec11da475383f69e6f82e2837a0cb54fd0`.
This is Lean 4, pinned to `leanprover/lean4:v4.35.0-rc3`; its manifest fixes
mathlib to `c55e6e786f49471c72fbddbec5415808896aec1e` (input tag
`v4.35.0-rc3`). The repository's `LICENSE` is Apache-2.0. No code was copied.

Inspected the normalizer/quotient definitions, `B0.lean`'s map and kernel
argument, `GenMain.lean`'s corresponding general congruence-subgroup
constructions, and search matches across the project's Lean sources.

Relevant exact declarations/conclusions:

1. [`NormalizerLean.BG`](https://github.com/F-Najman/normalizer-lean/blob/1f4c27ec11da475383f69e6f82e2837a0cb54fd0/NormalizerLean/Defs.lean#L247)
   abbreviates `NormG Γ ⧸ Γ.subgroupOf (NormG Γ)` for
   `Γ : Subgroup SL(2, ℝ)`, with `NormG Γ` abbreviating its normalizer.
   Its following normality instance is exactly
   `Subgroup.normal_in_normalizer`. This could package the codomain quotient
   only after specializing our arbitrary groups to real special linear
   groups; its entire useful content is already in mathlib.

2. [`NormalizerLean.B0_equiv'`](https://github.com/F-Najman/normalizer-lean/blob/1f4c27ec11da475383f69e6f82e2837a0cb54fd0/NormalizerDelta/B0.lean#L334)
   has parameters `(N : ℕ) [NeZero N]` and concludes

   ```lean
   ∃ φ : Norm0Q N →* B N, Function.Surjective φ ∧
     φ.ker = (Gamma0Q N ⊔ Subgroup.center (GLPos (Fin 2) ℚ)).subgroupOf (Norm0Q N) ∧
     ∀ g : Norm0Q N, (φ g).IsClassOf (normSL g)
   ```
   Here `phi0` is the composition of a quotient projection with `psi0`,
   which restricts determinant normalization of positive rational matrices
   into `SL(2, ℝ)`. Its source is a normalizer, not a normalizer quotient.
   Its kernel is a congruence subgroup joined with scalar matrices; it is
   not the arbitrary-homomorphism kernel statement needed here. Its kernel
   proof uses `QuotientGroup.eq_one_iff` and a specialized matrix-membership
   theorem. The quotient API it uses is already in mathlib.

3. [`NormalizerLean.BQ_equiv_BG'`](https://github.com/F-Najman/normalizer-lean/blob/1f4c27ec11da475383f69e6f82e2837a0cb54fd0/NormalizerDelta/GenMain.lean#L139)
   assumes `{N : ℕ}`, `hN0 : NeZero N`,
   `{Γ : Subgroup SL(2, ℤ)}`, `Γ(N) ≤ Γ`, and `-1 ∈ Γ`. It concludes the
   existence of a surjective
   `φ : NormGQ (Γ.map toGLPosQ) →* BG (toR Γ)` whose kernel is
   `(Γ.map toGLPosQ ⊔ Subgroup.center (GLPos (Fin 2) ℚ)).subgroupOf
   (NormGQ (Γ.map toGLPosQ))`, together with the representative formula
   `(φ g).IsClassOf (normSL g)`. This extends the preceding matrix result,
   not the arbitrary groups or arbitrary homomorphism in our theorem.

4. [`NormalizerLean.BG_GammaH_equiv'`](https://github.com/F-Najman/normalizer-lean/blob/1f4c27ec11da475383f69e6f82e2837a0cb54fd0/NormalizerDelta/GenMain.lean#L60)
   assumes `{N : ℕ} [NeZero N]`, `{H : Subgroup SL(2, ZMod N)}`, and

   ```lean
   ∀ p : ℕ, p.Prime → p ∣ N →
     ¬ IsBorelMod H p ∨ IsSplitMod H (p ^ N.factorization p)
   ```
   and concludes the existence of a multiplicative equivalence
   `BG (toR (GammaH N H)) ≃* QH H` with its reduction-modulo-`N`
   representative formula. Here `QH H = NormH H ⧸ H.subgroupOf (NormH H)`.
   Its proof computes a specialized map's kernel and invokes mathlib's
   `quotientMulEquivOfEq` and `quotientKerEquivOfSurjective`. It does not
   expose a reusable generic kernel-image lemma.

Direct-use decision: reject as a dependency for this milestone. These are
substantive modular-curve theorems, but no instantiation yields our arbitrary
groups/homomorphism, and their generic quotient constructions duplicate
existing mathlib. No compilation is warranted merely to confirm a result we
would not use. Formal correctness remains unverified by this search. The
repository's advertised theorem count/no-`sorry`/axiom claims were not used as
evidence. Its `Challenge` targets deliberately contain holes according to
`lakefile.toml`; those statement fixtures must not be confused with proofs.

## Arthur742Ramos/GraphCoveringTheory

Repository: [GraphCoveringTheory](https://github.com/Arthur742Ramos/GraphCoveringTheory).
Inspected checkout SHA: `c918a72c5170503c98fd66a0f3116b7bfcd1250c`.
Lean `v4.32.0`; mathlib manifest SHA
`81a5d257c8e410db227a6665ed08f64fea08e997` (input `v4.32.0`).
Repository license: Apache-2.0.

Read the complete
[`GraphCoveringTheory/Deck.lean`](https://github.com/Arthur742Ramos/GraphCoveringTheory/blob/c918a72c5170503c98fd66a0f3116b7bfcd1250c/GraphCoveringTheory/Deck.lean).
Its exact endpoint is the noncomputable definition
`GraphCoveringTheory.quotientDeckGroupEquiv (G : Type u) [Group G]
(H : Subgroup G) [H.Normal] [Fintype (G ⧸ H)] :
G ⧸ H ≃* SchreierDeckGroup G H`, with a finite-index variant.
It identifies automorphisms of a finite regular Schreier action with a group
quotient; supporting lemmas prove injectivity and surjectivity of a right
translation action. Imports are `GraphCoveringTheory.IndexFormula` and
`Mathlib.CategoryTheory.Action.Concrete`.

Direct-use decision: reject. It has a normality and finite-quotient setting,
no ambient homomorphism `f`, no map between two normalizer quotients, and no
required kernel-image equality. Specializing it to the subgroup in a
normalizer would additionally require finite index, absent in our statement,
and would produce an unrelated deck-group equivalence. Formal correctness
was not independently checked; no build/audit/replay was run.

## SauersML/group-approximation

Repository: [group-approximation](https://github.com/SauersML/group-approximation).
Inspected checkout SHA: `b4cbab68177c23556f0db49f8a45a431729f6e23`.
Lean `v4.32.0`; manifest mathlib SHA
`81a5d257c8e410db227a6665ed08f64fea08e997` (input `v4.32.0`).
Repository license: Apache-2.0. The large repository was searched only for
relevant group-kernel/quotient/normalizer declarations; this is not a review
of its headline mathematical claims or its entire source tree.

Inspected these nearby declarations:

- [`GroupApproximation.Full.LVHopf.ker_comp_mk'`](https://github.com/SauersML/group-approximation/blob/b4cbab68177c23556f0db49f8a45a431729f6e23/GroupApproximation/Manuscript/SimpleKazhdanSofic/Full/LVHopf/FiveTerm.lean#L35):
  for `(f : F →* G) (N : Subgroup G) [N.Normal]`,
  `((QuotientGroup.mk' N).comp f).ker = N.comap f`.
  Its proof consists of rewriting with mathlib's `MonoidHom.comap_ker` and
  `QuotientGroup.ker_mk'`. The nearby `map_ker_comp_mk'` adds surjectivity
  of `f` and concludes that this kernel's image under `f` is `N`, by
  mathlib's `Subgroup.map_comap_eq_self_of_surjective`.
- [`GroupApproximation.TypeA2.fg_of_fg_map_of_fg_inf_ker`](https://github.com/SauersML/group-approximation/blob/b4cbab68177c23556f0db49f8a45a431729f6e23/GroupApproximation/TypeA2/Extension.lean#L45):
  for `{A : Subgroup G}`,
  `(π : G →* H)`, `(hmap : (A.map π).FG)`, and
  `(hker : (A ⊓ π.ker).FG)`, it concludes `A.FG`. Its representative
  adjustment resembles the elementary step in our proof, but its result
  concerns finite generation, not an induced quotient's kernel.

Direct-use decision: reject. The kernel-composition wrapper supplies no
new prerequisite beyond pinned mathlib; the finite-generation theorem does
not imply our target. Its substantial import closure is unnecessary.
No build, axiom audit, or kernel replay was performed, so neither statement
is accepted as an externally verified proof.

## Coxeter developments and Lean 3 hits

The existing reference checkout `/tmp/artin-lean-coxeter-audit` was inspected
without modification. [`mlyean/lean-coxeter`](https://github.com/mlyean/lean-coxeter)
is at `8d36c58a038cc0642a46cf5165a1b0660348f105`, on Lean `v4.35.0`, with
mathlib manifest SHA `56a005855ea17e0b0958f73ec801ae140b0a1679`
(input `v4.35.0`), and Apache-2.0 licensing. Read its pinned version/license
files, the strong exchange statement/proof, and the geometric representation
file's initial definitions; searched the Lean sources for normalizer or
quotient-kernel results, obtaining no matches.

For example,
[`Coxeter.strong_exchange`](https://github.com/mlyean/lean-coxeter/blob/8d36c58a038cc0642a46cf5165a1b0660348f105/Coxeter/StrongExchange.lean#L51)
has ambient `{W : Type*} [CoxeterGroup W]` and, for
`{ω : List (B W)} {t : W}` and
`h : cs.IsLeftInversion (cs.wordProd ω) t`, concludes
`∃ i < ω.length, t * cs.wordProd ω = cs.wordProd (ω.eraseIdx i)`.
This is a word/inversion theorem, not a missing supplier for the arbitrary
groups/homomorphism kernel theorem. No Coxeter dependency is used by the
milestone's mathematical argument. It may warrant a separate audit for a
future article-specific Artin–Coxeter lifting/surjectivity formalization;
that problem is outside this milestone. No build, axiom audit, or kernel
replay was run for this repository here.

Search results also included mathlib3 quotient/coset sources and a project
advertising Lean 3.49.1 (`mariainesdff/norm_extensions_journal_submission`).
These are not accepted as reusable Lean 4 code; no Lean 3 theorem was silently
treated as an available Lean 4 declaration. They did not warrant a compatibility
port for already available quotient foundations.

## Search and verification record

Used public web search targeting GitHub, followed by read-only shallow Git
clones and local `rg`/source inspection. Query families included:

- `github Lean normalizer-lean F-Najman`
- `github Lean4 normalizer quotient kernel subgroup`
- `github Lean "QuotientGroup" "normalizer" -repo:leanprover-community/mathlib4`
- `site:github.com "QuotientGroup.ker_map" -leanprover-community/mathlib4 -mathlib4_docs`
- `site:github.com "normalizer" "quotient_map" lean`
- `site:github.com Lean4 group homomorphism quotient theorem normalizer`

The clones were isolated in `/tmp/lemma28-normalizer-lean`,
`/tmp/lemma28-graph-covering`, and `/tmp/lemma28-group-approximation`.
Recorded SHAs came from actual `git rev-parse HEAD`; versions and licenses
came from actual tracked files. No `lake update`, cache operation, dependency
installation, toolchain installation, or compilation was run. No shared
package state was changed.

No candidate passed the direct-use screen, so there is no proposed candidate
verification command or dependency migration for the root to execute. If a
later candidate does pass that screen, acceptance still requires a source-bound
build under agreed pinned dependencies, inspection of the elaborated complete
statement/definitions, transitive axiom checks excluding `sorryAx` and custom
axioms, and fresh kernel replay. None of these steps is asserted to have
occurred for the rejected external candidates here.

No mathematical error was established in the inspected external passages.
Unsuitability as a supplier and an unverified build are not allegations of
false mathematics. No consulted-paper defect or counterexample is asserted
by this report.
