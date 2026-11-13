# Landmark 1: independent review B

Reviewer: **GPT-6.1 Sol/high**, independent of reviewer A. Final verdict: **accept-landmark1**, at the exact source/configuration/provider/parent-record hashes below and in `landmark1-b.json`. Scope is only the first landmark: real regular stabilizers, freeness of the actual complex complement's normalizer-quotient action, the actual orbit covering, and its geometric fundamental-group exact sequence with raw endpoint target `Qᵐᵒᵖ`. **Landmark 1 is proved; full Theorem 1.8 remains unproved.**

I reread all frozen statements, definitions, instances and proof bodies in `ArtinLandmarks/Dominant.lean`, `RegularStabilizer.lean`, and `Covering.lean`, the final aggregate, both new provider sources, their retained originals/provenance, and the relevant pinned mathlib quotient-covering theorem. I inspected root's actual final elaborated-type/axiom log and audit source. I did not consult reviewer A, edit code/config/vendor/cache/evidence, or run Lean/audit/kernel replay. Root owns those executions. Only this review and its companion JSON were written.

## Source correspondence and intended theorem

The original article, arXiv:2509.21915v3, PDF p. 12 Lemma 3.23 identifies the relative-flat action and its parabolic kernel; PDF p. 13, equation (3.26) and the paragraph before (3.28), uses the actual restricted complex complement and says its normalizer quotient action is free/properly discontinuous, giving the geometric short exact sequence. This landmark supplies an explicit proof of the real/complex stabilizer and covering steps underlying that paragraph. It does not supply Theorem 6.7's comparison to Artin normalizers or Corollary 6.14's asphericity.

My original-source reading is the extracted PDF text recorded in `docs/theorem18/reviews/statement-b.md`, covering the definitions, finite-type Theorem 1.8 and Section 6 comparisons. I do not claim a fresh rendered-PDF inspection, full rereading of the original cited literature, or any proof that those comparisons/asphericity have now been formalized.

Let `M:CoxeterMatrix I`, `W=M.Group`, `J:Set I`, and assume `[Finite W]` for the finite-type landmark. Retain the already reviewed actual dual representation `Θ`, flat `Θ_J`, proper restricted root arrangement, pair-complement `X`, actual group `Q=N_W(W_J)/W_J`, actual continuous diagonal action, orbit quotient `Y=X/Q` and orbit map `c`. The intended statements are:

1. For a real `φ∈Θ_J` avoiding every retained restricted root hyperplane, its **full ambient** Coxeter stabilizer is `W_J`.
2. Every actual pair-complement point has a real linear combination of its coordinates satisfying that real regularity condition. Thus the full ambient stabilizer of both coordinates is `W_J`.
3. The induced actual `Q` action on `X` is free. Its actual orbit map is a quotient covering, hence a regular covering with the given deck action.
4. For **every** basepoint `p:X`, the actual induced map and raw endpoint monodromy give

   `1 → π₁(X,p) → π₁(Y,c(p)) → Qᵐᵒᵖ → 1`.

No stabilizer, freeness, covering or short-exactness hypothesis may be assumed to obtain these particular conclusions. The original finite-type restriction, arbitrary `J`, arbitrary basepoint and zero/full-rank cases must remain intact. The opposite-group target is intentional under mathlib's endomorphism multiplication convention, not the article's untransported algebraic target `Q`.

## Independent mathematical check

For a dominant functional `φ` (nonnegative on every simple root), finite support gives `φ(v)≤0` for any coordinatewise nonpositive vector `v`. If `u≠1` fixes `φ`, choose a left descent `i` of `u`. The actual root-sign theorem makes `ρ(u⁻¹)α_i` negative. Thus `φ(α_i)=φ(ρ(u⁻¹)α_i)≤0`, while dominance gives the reverse inequality, so the coordinate vanishes. The simple reflection `s_i` therefore fixes `φ`, and `s_i u` is shorter and still fixes it. Length induction places `u` in the generated parabolic on the zero coordinates. Conversely, those simple reflections and hence their generated parabolic fix `φ`. This works in arbitrary Coxeter type: finite support replaces any unjustified infinite sum.

The dual functional having coordinates zero on `J` and one elsewhere is legitimate even for infinite `I`, since it is in the algebraic dual of a finitely supported vector space. It is dominant with zero set exactly `J`. Consequently the **pointwise** stabilizer of the whole relative flat is precisely `W_J`, without assuming the element normalizes `W_J`.

For finite `W`, the actual positive root set is finite and consists of distinct vectors, not repeated orbit labels. A simple reflection permutes all positive roots other than its own, and sends its simple root to its negative. Therefore, for the positive-root vector sum `S`, `s_i S=S−2α_i`. Choose `u` maximizing `(u·φ)(S)` over finite `W`. Maximality relative to `s_i u` gives `(u·φ)(α_i)≥0` for every `i`. Thus every dual orbit has a dominant representative. This argument uses no longest element, root-lattice integrality, crystallographic condition, positive-definite-form assumption, or unproved Tits-cone chamber decomposition.

If a real relative regular point `φ` is fixed by `g`, move it to the dominant `ψ=u·φ`. Its stabilizer conjugate belongs to the parabolic on `zeroIndices ψ`. For every zero-coordinate simple root, the pullback root `β=ρ(u⁻¹)α_i` vanishes at `φ`. Because `β` is an actual root and `φ` avoids every root retained by the flat, `β` must annihilate the **entire flat**. Therefore the conjugated-back simple reflection fixes the entire flat. Closure under the generated parabolic shows `g` fixes the flat pointwise, hence `g∈W_J` by the preceding theorem. The reverse direction follows from actual parabolic flat-triviality. This is a genuine proof of the full ambient stabilizer statement, not a circular normalizer assumption.

At a complex pair `p=(x,y)` outside every `H×H`, for each retained root at least one coefficient `x(r),y(r)` is nonzero. Its coefficient functional `(a,b)↦a x(r)+b y(r)` on `ℝ²` is nonzero. A finite family of proper real linear kernels cannot cover `ℝ²`, so choose `(a,b)` making every retained evaluation nonzero. The real flat element `a x+b y` is regular. Any ambient Coxeter element fixing both coordinates fixes this combination and therefore belongs to `W_J`. Quotienting the actual normalizer by that subgroup proves the actual action free.

The parent complement is Hausdorff in its actual dual-coordinate/product/subspace topology. Finite `W` implies finite `I`; the finite product-coordinate dual is locally compact, the relative flat is closed, and the complement is open in a product of such flats. Hence the actual complement is locally compact. The existing finite-group proper-discontinuity theorem, the newly proved free action, actual translate continuity, Hausdorffness and local compactness meet the **actual** pinned mathlib quotient-covering theorem's hypotheses. Its orbit map is exactly the existing orbit quotient projection. Finally, the parent path-connectedness theorem and generic covering exactness give the actual based geometric short exact sequence.

Every step is mathematically sound on source inspection. No concrete mathematical repair is required for the frozen landmark source.

## Final declaration inventory

All project names below have namespace `ArtinNormalisers.Landmark1`. There are exactly 32 explicit declarations, including the two private logical helpers and named instances. I independently parsed the final source names/paths and checked them against all 32 rows of `landmarks/source-inventory.json`. Each listed declaration is accepted individually. The 40 project constants in the audit also include compiler-generated proof/equation declarations.

| Module and declarations | Semantic judgment |
| --- | --- |
| `Dominant`: `IsDominant`, `zeroIndices` | Accept: actual nonnegative simple-root coordinates and their actual zero-index set. |
| `Dominant`: `evaluation_nonpos_of_nonpos` | Accept: finite-support dual evaluation preserves the required inequality. No finite-index assumption or meaningless infinite summation. |
| `Dominant`: `dominant_fixed_iff` | Accept: equivalence with membership in the generated zero-coordinate parabolic; length-induction proof discharges the stabilizer claim. |
| `Dominant`: `canonicalDominant`, `canonicalDominant_apply_simpleRoot`, `canonicalDominant_isDominant`, `zeroIndices_canonicalDominant`, `canonicalDominant_mem_relativeSubspace`, `canonicalDominant_fixed_iff` | Accept individually: genuine dual-basis construction, coordinate equations, relative-flat membership and exactly the intended stabilizer. |
| `Dominant`: `pointwise_flat_fixed_iff` | Accept: full ambient pointwise-flat stabilizer equals `W_J` in arbitrary Coxeter type. No normalizer restriction hidden in the quantifier. |
| `RegularStabilizer`: `positiveRoots`, `positiveRoots_finite`, `positiveRootSum`, private `roots_eq_geometricRoots` | Accept individually: actual positive roots in the same Finsupp order, finite distinct-vector sum under finite `W`, and literal equality of parent/provider orbit definitions. |
| `RegularStabilizer`: `geometricReflection_positiveRootSum` | Accept: exact `S−2α_i` identity, using the provider's actual bijection on positive roots except the simple root; no multiplicity error. |
| `RegularStabilizer`: `exists_dominant_dualAction` | Accept: maximum over the actual finite `W` and correct `s_i u` contragredient evaluation. |
| `RegularStabilizer`: `realRelativeRegular`, private `flatPointwiseStabilizer` | Accept: actual avoidance condition and genuine subgroup of ambient `W` fixing the whole actual flat. |
| `RegularStabilizer`: `realRelativeRegular_fixed_iff` | Accept: full stabilizer equivalence proved by dominance, actual root pullback, regularity and subgroup closure. Applies to any ambient `g`, not merely normalizer elements. |
| `Covering`: `coefficientEvaluation`, `exists_regular_linearCombination` | Accept: actual nonzero coefficient forms and finite-family avoidance proof. No assumed regular combination; empty retained family allowed. |
| `Covering`: `complement_pair_stabilizer_iff` | Accept: full ambient stabilizer of the actual real and imaginary coordinates equals the generated parabolic. |
| `Covering`: `quotientComplement_smul_fixed_iff`, `quotientComplementIsCancelSMul` | Accept: freeness of the existing actual normalizer quotient action, by actual quotient representatives and identity criterion. |
| `Covering`: `complementT2Space`, `complementLocallyCompactSpace` | Accept: actual inherited topology, finite-rank derivation and closed/open subspace transfers. The final instance explicitly uses the actual complement subtype topology, preserving the reviewed parent definition. |
| `Covering`: `isQuotientCoveringMap_orbitProjection`, `isCoveringMap_orbitProjection` | Accept: invokes the real quotient-covering theorem with newly proved free action, genuine proper-discontinuity/continuity and local topology. No desired covering is an input assumption. |
| `Covering`: `orbitFundamentalGroupMap`, `orbitMonodromy`, `orbitFundamentalGroup_shortExact` | Accept: literal induced map of the actual orbit projection, raw endpoint-label homomorphism to actual `Qᵐᵒᵖ`, and injection/range-kernel/surjectivity for every actual basepoint. |

At preliminary review the aggregate did not yet import the three new project modules; I notified root. This integration concern is now resolved: the frozen aggregate publicly imports `ArtinLandmarks.Covering`, which imports `RegularStabilizer` and then `Dominant`. It therefore includes all 32 reviewed declarations and both new provider modules through the actual import chain. The final root's work-in-progress comments accurately restrict the completion claim to landmark 1. The preliminary incomplete aggregate is not treated as the accepted source.

## New provider: actual reading, usefulness and relocation

I read both complete local source files: 155 lines of `Geometric/RankTwo.lean` and 273 lines of `Geometric/Sign.lean`, including all proof bodies. Their mathematical declarations remain in the original `CoxeterMatrix`/`CoxeterSystem` namespaces and use the actual parent Coxeter presentation/system, not a surrogate class assuming signs, dominant representatives, stabilizers or freeness.

`RankTwo` defines `dihedralCoeff` by actual Chebyshev evaluation, proves its recurrence and sine-quotient form for finite entries and linear form for entry zero, and proves coefficient nonnegativity up to the correct braid bound. Its alternating-word formula and nonnegativity theorem do not require finite rank or finite group. The infinite-entry and diagonal cases are handled explicitly; strict `k<M_ij` in the rank-two nonnegative root theorem is correct. These are genuine inputs to the root-sign proof, not an assumption of the sign theorem.

`Sign` proves the rank-two no-right-descent case, then inducts on Coxeter length through the actual rank-two parabolic factorization to obtain the nonnegative root assertion. Nonzero representation images make it strict positivity; multiplication by a right-descending simple reflection gives the negative case. Thus `geometricRepresentation_single_neg_iff` used in `dominant_fixed_iff` is the actual sign/length theorem with the correct **right** descent convention; left descents are converted through inversion. It also proves actual root stability, positive/negative dichotomy, norm-one self-pairing, and that a simple reflection bijects the positive roots other than its own. The latter result is exactly what the positive-root sum argument needs. Faithfulness is proved as a consequence, not assumed. There is no finite or crystallographic condition hidden in these generic suppliers.

I independently checked the preserved originals against `git show` blobs at revision `62bbc0596dc3539d488232e4e924a338548ea0a9` in the existing `/tmp/full28-tauceti` checkout, and independently checked their recorded hashes. I then compared the local files byte-for-byte to the originals after applying the recorded patch: RankTwo is unchanged; Sign differs **only** by replacing its one RankTwo import path with `ArtinLandmarkVendor.Geometric.RankTwo`. Original namespace/statement/proof bytes and headers are otherwise unchanged. This is an actual checked mechanical relocation, not a provider-doc assertion. I also independently rehashed all 33 parent vendor files against the two parent provenance maps; all remain unchanged.

The upstream/project mathlib revisions differ, so new-module compatibility is supported by root's actual pinned build/audit evidence, separately from my source/byte checks. I have not run or inferred a Lean check merely from upstream provenance. The frozen provider provenance now points to hash-bound statement reviews and actual verification records rather than claiming acceptance from provenance alone. Its mathematical source bytes are unchanged. No mathematical defect in these consulted source statements was found.

## Conventions, degeneracies and remaining scope

The covering sequence ends in raw `Qᵐᵒᵖ`, as explicitly defined by the pinned endpoint-monodromy construction. It does not claim the algebraic Artin quotient comparison, the right-square equation with the canonical projection to `Q`, or an unnoticed `op:Q→Qᵐᵒᵖ` homomorphism. A future comparison must still provide the explicit inverse/opposite transport and compatible equations. This landmark has no asphericity premise or conclusion.

`J=I` gives the zero flat, no retained roots, singleton complement, `W_J=W`, trivial `Q`, and a legitimate trivial covering/sequence. The coefficient-avoidance argument does not insist on nonzero dimension or nonempty retained roots. `J=∅` recovers the ordinary full reflection complement and free finite Coxeter action; real regular points have trivial stabilizer. Rank zero is included. Every final based theorem takes an arbitrary point of the **actual** complement and its actual quotient image, with no chamber-basepoint restriction. These checks do not prove the later fundamental-group identification or contractibility/asphericity.

## Final elaborated types and execution provenance

I read `/tmp/landmark1-pre-review-audit-v2.log` and `landmarks/LandmarkAudit.lean`. The log prints the literal final statements for dominant stabilizers, pointwise-flat stabilizers, the finite-type dominant-orbit result, full ambient real/pair stabilizers, actual quotient freeness, actual quotient-covering map and based geometric short exactness. The printed final exactness type has only `{I}`, `(M)`, `(J)`, `[Finite M.Group]`, and the arbitrary actual basepoint `(p:Complement M J)` before its injection/range-kernel/surjectivity conclusions. There is no assumed desired stabilizer, action freeness, covering, comparison or asphericity premise.

The same inspected log reports **40 new project constants and 763 supplier constants**, with only `propext`, `Classical.choice`, and `Quot.sound` permitted; the final theorem's printed axioms are exactly those three. The audit source selects declarations by defining module, covering private helpers and both relocated provider namespaces, and rejects empty selections. Root reports audit exit zero over the expected **38 modules**: three new project modules, two relocated providers and 33 unchanged parent suppliers. Root also reports `lake build ArtinLandmarks` exited zero. I did not execute those commands myself, and no independent reviewer kernel-replay execution is claimed.

Root reports the initial audit counter-type inference error was retained and fixed only by explicit `Nat` annotations in the audit; it did not change scientific source. I inspected the final audit's explicit natural-number counters and the final log. This is verification-tool integration history, not a mathematical literature defect or a proof-source repair.

The parent package remains a dependency at path `..`; the new library has its own configuration and applies `autoImplicit=true` only to `ArtinLandmarkVendor`, while its project option remains false. My independent hash checks bind all four final project files, all three landmark configuration files, both relocated supplier files, the supplier provenance and the referenced parent verification record. I also verify the preserved upstream files, exact import-only relocation, and unchanged parent inputs as recorded below. Actual fresh build/audit/replay closeout remains root-owned; this independent receipt is its mathematical/input-review prerequisite, not a claim to have run that closeout myself.

## Frozen byte binding

Project hashes, with paths relative to the parent repository:

| Path | SHA256 |
| --- | --- |
| `landmarks/ArtinLandmarks.lean` | `1be1ffb1e3042d4e7973c8cac884b524f2f4e1af09c3f6672558690ceeb2b1f4` |
| `landmarks/ArtinLandmarks/Covering.lean` | `5c700e4c42bdb72e81c4a7499ebab13d1d742bd1e98058446057c12eb389cd94` |
| `landmarks/ArtinLandmarks/Dominant.lean` | `408a97cc6f49b5868d5eafc6aae733b8ae26a1d314b26c81235f5bf493339da4` |
| `landmarks/ArtinLandmarks/RegularStabilizer.lean` | `aeeee397f0fe48325c9f62eee8607e80a1836cb123dc9a022cd8d954c92fd93f` |

Configuration hashes: `landmarks/lean-toolchain` = `11c697aebe5b539d74f5069e497a588e7dfab1c4eeb74313f28357e351c55ca3`; `landmarks/lakefile.toml` = `391a36c1e67ff796ab7487d7e2100eb52b7532c71a1eab2f6bed73839f3839a0`; `landmarks/lake-manifest.json` = `a8415b907a1da8ff6c0a0c936fef67eb0f3315213afff0d1963653b72a8c5679`.

Relocated-provider hashes: `ArtinLandmarkVendor/Geometric/RankTwo.lean` = `53d4bcbfb2dd83abf8a4adb53091c982e191ca3a69be95e751e20306e26591f3`; `ArtinLandmarkVendor/Geometric/Sign.lean` = `c0b7e5f1e0bfa9aa67a1df7b5cc11e65625987089e9909f0366b88068d58bc09`. Preserved original Sign hash is `fa162d417fcd0e91ec061056ac696119ee263c3fba15e4f22540016202596bf1`; preserved RankTwo hash equals its relocated hash. The exact recorded import substitution reconciles them.

Supplier provenance hash: `5d30ae8493968f7fb58bbaa7e78514a0afc15501d62abd940061906c3483581a`. Referenced parent verification path: `docs/theorem18/github-evidence/run-43492004104/lean-theorem18-foundations-verification.json`; hash: `79f91cb45e5ada75c39968f29b93cc228d0fd38914903cb432c1b8664a332b1d`. The companion receipt uses the exact current inventory maps, independently recomputed rather than copied without checking.

I independently rehashed **all 65 inputs** recorded in that parent verification JSON and checked each against its recorded digest; all match. I also checked its `ok:true` value. This confirms preservation of those recorded parent files, including their source/configuration bindings; it does not relabel the earlier parent's prerequisite-only result as full Theorem 1.8 completion.

Final decision: **accept-landmark1**. `landmark_1_proved` is **true**; `full_theorem_1_8_proved` is **false**. All 32 explicit declarations and the first landmark's literal geometric conclusion are accepted at these bytes. The other roadmap landmarks, compatible Artin/fundamental-group comparison and actual asphericity remain outside this result.
