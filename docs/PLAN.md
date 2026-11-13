# Lean formalization plan: kernel argument of Lemma 2.8

Source: Garnier, Heng, Licata and Yacobi, *Normalisers of parabolic subgroups of Artin–Tits groups and Tits cone intersections*, arXiv:2509.21915v3, PDF page 6, Lemma 2.8. This plan records the end-to-end proposal requested by the owner and its implementation scope.

## Target and scope

Formalize the following standalone algebraic theorem. For a group homomorphism `f : G →* H`, a subgroup `A ≤ G`, and `B = f(A)`, write `N = N_G(A)` and `M = N_H(B)`. The restriction `N → M` induces `bar_f : N/A → M/B`. If `q : N → N/A` is the quotient projection, then

`ker(bar_f) = q((ker f) ∩ N)`.

Here the intersections and quotients use actual subgroup embeddings in the correct ambient groups. Also prove that kernel membership is equivalent to the existence of a representative in `ker f`. This recovers the kernel argument of Lemma 2.8 after substituting the article's Artin–Coxeter projection and standard parabolic subgroup. It does not establish the article-specific construction of that projection, the identification of its parabolic image, or the terminal surjectivity in the full short exact sequence. No surjectivity assumption is needed for the general kernel theorem.

The kernel argument is the first milestone, rather than a formalization of the article's full main theorem. The full Lemma 2.8 needs an Artin–Coxeter normalizer-lifting argument; surjectivity of an ambient homomorphism alone does not imply surjectivity on normalizer quotients.

## Feasibility and existing prerequisites

Clone `https://github.com/leanprover-community/mathlib4.git` for reference. The inspected snapshot is `65d730f7150f21fdfa32f3e73a3f549c1f96a0e9`, using `leanprover/lean4:v4.36.0-rc2`. Reuse mathlib as a pinned dependency in a separate Lake package; do not modify its source.

Existing source APIs include `Subgroup.normalizer`, `Subgroup.map`, `Subgroup.subgroupOf`, `Subgroup.normal_in_normalizer`, `Subgroup.le_normalizer_map`, `QuotientGroup.mk'`, `QuotientGroup.map`, `QuotientGroup.ker_map` and `QuotientGroup.quotientKerEquivRange`. Check actual signatures with compiled probes before use. Most of the target is an application of existing algebra; recreating foundations would waste effort.

Mathlib's Coxeter library supplies presentations, words, length and inversions, but the inspected source still lists ordinary Matsumoto's theorem as unfinished. `https://github.com/mlyean/lean-coxeter` supplies geometric representation, strong exchange and Bruhat-order infrastructure; the inspected revision `8d36c58a038cc0642a46cf5165a1b0660348f105` uses Lean/mathlib 4.35.0. It is a possible later dependency, not needed for this milestone. Other advanced external formalizations require statement, dependency and compatibility audits before reuse.

Rough planning estimates: the kernel theorem is a few focused days including setup and review; full Lemma 2.8 may take weeks or longer; atomic Matsumoto and the main relative K(pi,1) theorem are substantial research projects. These are estimates, not measured agent benchmarks. Measure actual pilot usage before expanding scope; no dollar estimate is asserted without actual model billing rates.

## Software and package setup

On Windows use WSL for the checkout and tools, with VS Code's WSL support and official `leanprover.lean4` extension. Install Git, curl and elan from `https://elan.lean-lang.org/elan-init.sh`. Elan selects the pinned Lean toolchain; Lake comes with Lean. No GPU or separate paid theorem prover is needed. GitHub CLI is optional for uploading releases and downloading Actions logs.

The implementation lives at `formalizations/artin-normalisers/` in this repository, keeping source, plan and evidence reviewable together. It is an independent Lake package with its own `lean-toolchain`, `lakefile.toml`, committed `lake-manifest.json`, and ignored `.lake/` cache. This is an intentional packaging adaptation of the proposed separate proof repository; it avoids creating a second repository without need.

Run `lake update mathlib`, then `lake exe cache get`, then build the package. Cache downloads avoid rebuilding the whole of mathlib. Freeze the dependency versions throughout this milestone.

## Module and documentation layout

- `ArtinNormalisers/NormalizerMap.lean`: normalizer restriction and compatibility.
- `ArtinNormalisers/QuotientMap.lean`: quotient construction and representative formula.
- `ArtinNormalisers/Kernel.lean`: kernel equality and representative characterization.
- `ArtinNormalisers.lean`: imports every proof module.
- `Audit.lean`: prints all public statements and their transitive axiom dependencies, with an enforced allowlist where supported.
- `README.md`: exact scope, commands, correspondence to the article and limitations.
- `research/lean-lemma28/reviews/`: independent statement/translation reviews.
- `evidence/`: real build, audit and recheck records, version information and source hashes.

Small modules may be combined if doing so reduces duplication without losing the reviewable statement boundaries. Every authored module must be imported by the root build target.

## Independent statement review

Use separate GPT-6.1 Sol agents with high reasoning, explicitly requested by the owner. Each reviewer independently reads the original article and derives the expected statement. Reviewers must not rely on another review's verdict. Review exact final source and signatures, including every helper statement and definition, before closeout.

Check normalizers' ambient groups, subgroup embeddings, quotient equality, kernels, existential representatives, all implicit parameters and typeclass assumptions. Reject vacuous hypotheses, altered maps, a missing bridge to the informal statement, or an assumption equivalent to the desired conclusion. Use `autoImplicit false`. Record source reading limits and bind final review to file SHA-256 hashes. If scientific source changes follow review, recheck the changed definitions/statements and affected consumers.

Keep final definitions and signatures fixed while authoring proofs, except for a scientifically justified, explicitly re-reviewed correction. Compilation cannot establish that a theorem means what the article intended.

## Proof-generation workflow

Use GPT-6.1 Sol/high authors with concise bullet prompts. Supply the source passage, approved statement, dependency map and numbered informal proof. Prefer existing mathlib declarations and explicit intermediate `have` steps. Never invent a theorem name or report compilation that was not run.

1. Show that `f` sends `N_G(A)` into `N_H(f(A))`.
2. Construct its restricted group homomorphism.
3. Embed `A` and `B` into the normalizers and use their normality there.
4. Descend to the quotient homomorphism and prove its representative formula.
5. For a kernel coset represented by `g`, use `f(g) ∈ f(A)` to choose `a ∈ A` with `f(a) = f(g)`.
6. Prove that `g * a⁻¹` belongs to the normalizer and kernel, and represents the same coset.
7. Prove the reverse inclusion and subgroup equality.
8. Define the article-style image subgroup and prove the existential representative characterization.

Compile each substantial step using `lake env lean FILE.lean` and `lake build MODULE`. Feed actual diagnostics back to the author. Reconsider decomposition/API choices after repeated unsuccessful attempts. Do not add hypotheses to make the proof compile. No `sorry`, `admit`, custom mathematical axioms, or unproved external citations are acceptable in final proof dependencies.

## Verification and evidence

Lean checks proof terms during elaboration/kernel checking; executable machine-code generation is not the essential verification. A successful build alone does not rule out admitted proofs or custom axioms.

Require all of:

1. Root package build covering every authored module.
2. Compilation of the audit file, with actual displayed statements.
3. Transitive axiom checks for every exported theorem, allowing only a subset of `propext`, `Classical.choice`, `Quot.sound`.
4. Kernel replay of compiled declarations with the pinned toolchain's supported checker. Determine the actual installed command and options; do not assume an untested command exists.
5. Independent semantic reviews of the exact final statements and definitions.
6. A fresh build of project outputs while retaining the pinned mathlib cache, recorded with exit statuses and unmodified diagnostics.

Record tool versions, toolchain, Lake manifest, mathlib revision, SHA-256 hashes of all project inputs, exact commands and exit statuses. Use `lake clean artin-normalisers` to clean only the project: bare `lake clean` deletes dependency outputs too. Use `set -euo pipefail` when piping compiler output through `tee`; a successful logger must not hide a failed proof check. Never label partial or failed evidence as passing. Do not copy `.lake/` or trust unbound binaries as proof evidence.

The standalone package is not a serving-content item frontier, so mathematical item-layout tools and unrelated workflow gates are not applicable. This work does not reopen or rewrite the completed article research run.

## GitHub and archival workflow

Save sources and review documents in Git. A reviewed source commit must be identified in the evidence, or the exact input tree must be hash-bound before the final commit. Do not create a circular evidence hash by hashing a file that contains its own hash.

Provide scoped GitHub Actions that build this Lake package and audit/recheck it on a fresh runner, using the pinned mathlib cache. `leanprover/lean-action` supports build, `leanchecker` and axiom-audit features. Pin action revisions for archival reproducibility. Preserve failed logs as failures. Upload version/hash/axiom/recheck artifacts and retain the Actions build logs for the exact commit. Artifact retention is finite; copy successful records into a tagged release for long-term evidence when publishing is authorized.

The release title should identify the kernel argument underlying Lemma 2.8, not the full lemma or main theorem. Record its source revision, theorem names, CI URL, build/audit/rechecker statuses and remaining scope limits. The owner's instruction to follow this end-to-end plan includes saving proof and compilation evidence to GitHub: commit and push the scoped implementation to this repository's existing origin and run its scoped CI. Do not create a separate repository or publish Research portal content. Preserve immutable source commits and their CI artifacts; a separate named release is optional archival packaging rather than a scientific prerequisite.

## Completion criteria

The requested milestone is complete only when the exact generalized kernel theorem and article-style representative characterization compile without proof holes, pass transitive axiom and kernel replay checks, have independent accepted final translation reviews, and have reproducible source-bound records committed with the code. Report any tool or scientific limits honestly. The full Artin–Coxeter application and surjectivity remain a later milestone.
