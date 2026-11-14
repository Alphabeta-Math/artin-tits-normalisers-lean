# Landmark 4: independent exact-sequence and convention contract B

Reviewer: **GPT-6.1 Sol/high** (`gpt-6.1-sol`, reasoning effort `high`). Status: **preauthoring semantic contract only; no M4 source accepted**. Full Theorem 1.8 and arrangement asphericity remain unproved. The repository HEAD read for this task is `1aa55a9ee5f13c9e3a8e64b4aec4675c0435a9c0`.

I independently reread the original arXiv:2509.21915v3 extracted text of Theorem 6.7, its proof, Remark 6.12 and formula (6.13), on PDF pp.26–27, together with the adjacent reverse-positive-crossing footnote. This was actual extracted-paper reading, not a new visual PDF inspection. I reread the actual M1 covering/exact-sequence API, algebraic Lemma 2.8, M2 canonical reduced-loop quotient/projection API, M3 actual comparison square and all-signed deck-label endpoints, and the relevant pinned mathlib fundamental-group, conjugation, opposite-equivalence and monodromy definitions. I did not consult review A. No Lean build/audit/replay or new source search was executed; no frozen mathematics/configuration/evidence/cache files were changed. Only this contract was written.

## Exact source target

For every actual Coxeter matrix `M : CoxeterMatrix I`, arbitrary universe `I : Type u`, `[Finite M.Group]`, every `J : Set I` and **every actual point** `x : Theorem18.Complement M J`, prove an isomorphism of the following short exact sequences with **identity on the same existing Q**:

```
1 → P                 --i--> N                 --f--> Q → 1
    | ΦP,x                   | ΦN,x                 | id
1 → FundamentalGroup X x --j_x--> FundamentalGroup Y (p x) --μ_x--> Q → 1
```

Here:

- `X = Theorem18.Complement M J`, with its existing actual topology.
- `Y = Theorem18.OrbitSpace M J` and `p = Theorem18.orbitProjection M J`.
- `N = Artin.normalizerQuotient M J = N_A(A_J)/A_J`.
- `P = Artin.pureNormalizerImage M J`, the existing quotient **image** of the actual ambient pure Artin subgroup intersected with the actual Artin normalizer. It must not be replaced by the entire pure Artin group, a differently defined pure normalizer, or a new type defined to equal the desired fundamental group.
- `i = Artin.pureNormalizerInclusion M J` and `f = Artin.normalizerQuotientMap M J`, the original canonical homomorphisms.
- `Q = Artin.coxeterNormalizerQuotient M J = N_W(W_J)/W_J`, without an automorphic relabeling.
- `j_x = Landmark1.orbitFundamentalGroupMap M J x`, induced by the actual continuous p.
- `μ_x` is the explicitly corrected monodromy below, derived from the existing raw `Landmark1.orbitMonodromy M J x`.

The equivalences `ΦP,x` and `ΦN,x` must be genuine `MulEquiv`s between these exact groups. Both squares are equations of homomorphisms:

```
j_x.comp ΦP,x.toMonoidHom = ΦN,x.toMonoidHom.comp i
μ_x.comp ΦN,x.toMonoidHom = f.
```

The upper exactness is the proved algebraic Lemma 2.8. The lower exactness must retain the actual covering-induced injection and endpoint monodromy: injectivity of j, `range j = ker μ` and surjectivity of μ. Inverting the opposite convention changes neither its kernel nor surjectivity, but those identifications must be proved, not silently coerced. A final conjunction of these facts or a well-defined commuting short-exact-sequence structure is acceptable; two unrelated group isomorphisms are insufficient.

There is no extra proper/nonempty J, positive rank/dimension, irreducibility, crystallographic restriction, simply connected complement, or assumed normalizer/fundamental-group comparison. Empty/full J, rank zero and reducible finite Coxeter systems remain part of the final theorem. M4 proves the based comparison in Theorem 6.7, not Corollary 6.14’s higher-homotopy assertion.

## The two opposite corrections, derived from literal definitions

Mathlib defines `FundamentalGroup X x` to be the categorical `End` group at `mk x`. Its literal multiplication is

```
(p * q).asHom = q.asHom.trans p.asHom.
```

For actual reduced ribbon labels, traversal composition first β then γ has label `β*γ`. Categorical End multiplication therefore identifies the actual reduced ribbon vertex group with `Rᵐᵒᵖ`, where `R = Ribbon2.reducedRibbonLoops M ⟨J⟩` carries ordinary Artin multiplication. Any End/label equivalence used here must be for the **actual reduced associate component**. The older `endEquivRibbonLoopsOpposite` API on the larger positive-transporter groupoid R′ cannot be substituted for it.

Let `k : R ≃* N` be M2’s existing canonical `reducedRibbonNormalizerQuotientEquiv`. Its underlying map is the actual quotient restriction; `f ∘ k = ρ`, where `ρ : R →* Q` is the existing `reducedRibbonCoxeterProjection`.

At the actual preferred chamber `C0 = standardActualChamber M J`, let `x0` be M3’s actual canonical chamber basepoint and `y0=p x0`. The natural **positive-label** vertex map of the actual M3 equivalence has type

```
Φ+ : Rᵐᵒᵖ ≃* FundamentalGroup Y y0.
```

It sends `op r` to the M3 image of the actual ribbon loop labeled r. M3’s all-signed endpoint theorem and strict actual covering square should give

```
rawMonodromy_x0 (Φ+ (op r)) = op (ρ r).
```

This is the correct raw compatibility: raw endpoint monodromy has codomain `Qᵐᵒᵖ`, not Q. The proof must use actual outgoing lifting and exact endpoint labels, not just equality of abstract finite deck-group cardinalities or existence of a group isomorphism.

For any group G, `MulEquiv.inv' G : G ≃* Gᵐᵒᵖ` is the genuine inversion-to-opposite equivalence `g ↦ op(g⁻¹)`. Its inverse sends `op g` to `g⁻¹`. In general plain `op`/`unop` are not multiplicative equivalences and inversion is not an endomorphism of a noncommutative group. Finite W and finite Q do **not** imply commutativity.

The proposed normalized maps are mathematically correct:

```
ΦN,x0(a) = Φ+ (op ((k.symm a)⁻¹))
μ_x(γ)   = ((rawMonodromy_x γ).unop)⁻¹.
```

Thus `ΦN,x0` is the composition `k.symm`, `MulEquiv.inv' R`, and Φ+. The corrected monodromy is `(MulEquiv.inv' Q).symm` after the actual raw monodromy. Both are genuine homomorphisms, and

```
rawMonodromy_x0 (ΦN,x0(a)) = op ((f a)⁻¹)
μ_x0 (ΦN,x0(a)) = f a.
```

These formulas explicitly explain why the diagram commutes with **identity on Q**. Inverting only one side or forgetting `Qᵐᵒᵖ` would change the asserted formula. A raw diagram may instead retain `Qᵐᵒᵖ`, but then its upper terminal homomorphism must explicitly be `(MulEquiv.inv' Q).toMonoidHom.comp f`; it cannot be advertised as the unchanged Q diagram without the conversion.

This convention translation is how the natural vertex-group chain of Remark 6.12 is represented using mathlib’s End convention and the project’s ordinary Artin-label groups. Do not claim that the normalized ordinary-group map sends r to its **positive** ribbon-image path: its formula uses the group inverse label. The inverse is the actual groupoid inverse of a whole signed ribbon loop, not the other directed positive crossing. The paper’s reverse-positive-crossing footnote remains in force.

## Preferred basepoint must come from the strict M3 square

The actual ribbon-to-orbit equivalence’s value at the J-object is identified with `mk (p x0)` by M3’s strict square evaluated at the actual standard chamber. Use that **actual object equality** and its `eqToIso`/`mapOfEq` transport to obtain Φ+ on the desired based groups. The component-ribbon J-object and the chosen standard interval object also require their proved actual index equalities.

An arbitrary counit/path isomorphism from an equivalence may insert a loop and alter deck labels by conjugation. It must not replace the object equality fixed by the strict square. M3’s actual equivalence is not strictly bijective on all objects of the complement’s fundamental groupoid; use its actual full faithfulness for vertex groups and explicit equality transports where the strict square supplies them.

## Every basepoint: transport along one complement path and its projection

First prove the generic paired-basepoint-change identities for the actual quotient cover. Given a **single actual path**

```
γ : Path x0 x,
η = γ.map continuous_p : Path (p x0) (p x),
```

write `Tγ` and `Tη` for mathlib’s `FundamentalGroup.fundamentalGroupMulEquivOfPath` on these exact paths. Its literal categorical conjugation sends a loop β to the traversal class

```
γ.symm ⋆ β ⋆ γ
```

at the new basepoint. The required equations are

```
j_x ∘ Tγ = Tη ∘ j_x0
rawMonodromy_x ∘ Tη = rawMonodromy_x0
μ_x ∘ Tη = μ_x0.
```

The first is actual continuous-map naturality. For the second, if β lifts from x0 to `q • x0`, lift the conjugated loop from x by following γ backwards, that lift of β, then the actual translated path `q • γ`. Its endpoint is **q • x**, so its raw deck label is exactly q. This proves the formula without any commutativity assumption and without a conjugation of the target Q. The third follows through the fixed inversion equivalence.

The same-fiber variant illustrates the danger: mathlib explicitly proves that replacing a fiber basepoint e by `g • e` while keeping a base loop fixed conjugates the raw label by g. Paired transport along γ and its actual projected path compensates for this; choosing unrelated paths upstairs/downstairs does not. No target-Q conjugation should appear in the final all-basepoint square. If an intermediate proof changes a fiber representative, its conjugation must be derived and cancelled explicitly.

Now define

```
ΦN,x = Tη ∘ ΦN,x0
ΦP,x = Tγ ∘ ΦP,x0,
```

or construct ΦP,x by the unique lifting method below and prove it equals that transport. The two squares then follow from the paired identities. Actual path connectedness of X was already proved and supplies γ for each x. It is acceptable to choose such a path noncomputably after proving the path-parametrized statements. The theorem does not require a path-independent canonical isomorphism: different choices may change the based group isomorphisms by compatible inner transports, while the terminal map remains the same actual Q. A statement only at x0 does not satisfy Theorem 6.7’s all-basepoint scope.

## The pure equivalence can be constructed by unique lifting

A direct separate vertex-group identification for P is unnecessary if the compatible middle equivalence and actual exactness are proved. This is a legitimate route, not an assumption of the desired pure comparison.

Fix x and the already constructed middle equivalence `α=ΦN,x` with `μ_x ∘ α=f`. For each `a:P`, algebraic exactness gives `f(i a)=1`, so `α(i a)` lies in `ker μ_x = range j_x`. M1 supplies actual j_x injectivity, hence there exists **exactly one** `z:FundamentalGroup X x` with

```
j_x z = α (i a).
```

Choose that unique z to define ΦP,x. Prove multiplication and identity by applying the injective j_x. Injectivity follows from injectivity of j_x, α and the original inclusion. For surjectivity, given z let `n=α.symm(j_x z)`; lower exactness/right-square compatibility gives `f n=1`, and the already proved equality `ker f=P` makes n an element of the existing `pureNormalizerImage`. Its image is z by injectivity of j_x. This yields a genuine `MulEquiv` and the left square, with uniqueness among homomorphisms/equivalences making that square commute.

A generic helper may assume injection, range/kernel equalities and a compatible middle equivalence. Its **actual M,J,x instance** must discharge every assumption using M1, Lemma 2.8 and the explicitly constructed middle map; no isomorphism/lift/comparison conclusion may be a final field or parameter. Preserve P’s independent ambient-intersection/image definition and use its proved kernel equality, rather than redefine P as `ker μ` or `FundamentalGroup X x`.

## Final review/acceptance gate

The final M4 bundle must expose the actual named middle/pure equivalences for every x, both homomorphism squares, the raw/inversion-corrected convention and lower exactness. Preferred-point formulas through actual reduced ribbon labels and paired path-change naturality must be proved, not merely described. It may use M1–M3’s already proved actual covering/equivalence/projection results. It must not assume π1 identification, endpoint compatibility, basepoint-change invariance, desired comparison maps or simply connectedness as undeclared extra final inputs.

Before acceptance, independently review every actual final definition/statement/type context and the critical proof chains; bind exact project/configuration/provider/context/tooling hashes and immutable inventory; inspect real build, complete canonical/physical declaration and transitive-axiom coverage, and exact-module kernel replay evidence. Do not claim an old-context source read, imported olean, technical success flag or citation proves a new semantic statement. Frozen earlier reviews and accepted sources remain immutable. No M4 acceptance or full Theorem 1.8 claim is issued by this contract.
