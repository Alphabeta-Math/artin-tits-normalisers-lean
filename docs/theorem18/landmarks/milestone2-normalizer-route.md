# Milestone 2: stripping a normalizer to a reduced ribbon

Status: mathematical dependency route, 2026-11-14. This document contains no
new compiled Lean result and does not certify a candidate supplier. The goal
is the actual splitting `N_A(A_J) = A_J ⋊ R_J`, where `R_J` consists of actual
Artin-group values of signed paths in the outside-ribbon groupoid. Defining
`R_J` by a desired factorization property would not establish this goal.

## Sources actually read

I read §5, PDF pp.21–22, of Garnier–Heng–Licata–Yacobi,
arXiv:2509.21915v3, in the frozen article extraction. Definition 5.1 uses
`A_I⁺ β = β A_K⁺`, so a ribbon `β:I→K` satisfies
`β⁻¹ A_I⁺ β = A_K⁺`. Definition 5.5 generates the reduced groupoid using
only `μ_{a,I}=Δ_I⁻¹Δ_{I+a}`, `a∉I`; Theorem 5.6 requires the resulting
vertex group, not the whole monoid transporter.

For the cited earlier result I downloaded and read the original preprint
[arXiv:math/0202174v1](https://arxiv.org/pdf/math/0202174v1), particularly
Lemma 1.2 and the paragraph following it, Proposition 2.1 and its proof,
Theorem 0.5's proof, Lemmas 4.1–4.2 and Propositions 4.3–4.4 with their
proofs. I visually inspected PDF pp.7 and 12. Its PDF SHA256 is
`f07d83a6d95743bf171a3f41820a65959bcae0097e4601d6ec8df9423bc4cd48`.
I have not compared this preprint with the 2003 journal version; findings
about its proof text below apply to the inspected preprint.

I also read Godelle's
[arXiv:0811.0751v1](https://arxiv.org/pdf/0811.0751v1), Definition 3.12,
Example 3.14, the defining paragraph of §4.2, Lemmas 4.11 and 4.17,
Theorem 4.14, and the complete statement and proof of Theorem 4.25 on PDF
p.28. I visually inspected that page. This frozen PDF has SHA256
`011d804c75d960d1bf9cdc3a1562c412ab6fb328dec026d175ab1f56fd16f17c`.
Its general theorem assumes a monoidal Garside structure **with a
ν-structure**. Gcd/lcm availability alone is not that additional structure.

## A finite-type route requiring no general ribbon-category theorem

Work in the actual positive Artin monoid `A⁺`, embedded in the actual Artin
group `A`. Let `P_J⁺` mean positive elements supported on `J`, and
`A_J=⟨σ_j:j∈J⟩` the actual subgroup. Write `deg` for homogeneous positive
length. A left divisor is a prefix: `a≼b` means `b=a c`.

1. **Make the normalizer positive.** Put `Ω=Δ_S²`. The longest-lift
   conjugation formula proves `Ω` central. Every group element has the form
   `g=p Ω⁻ⁿ` with `p∈A⁺` and `n≥0`. If `g∈N_A(A_J)`, then `p` also
   normalizes `A_J`. This keeps the target subset equal to `J` and avoids an
   unnecessary associate-rank argument.

2. **Strip both sides using degree only.** Among decompositions
   `p=a r b`, `a,b∈P_J⁺`, maximize `deg(a)+deg(b)`. The set is nonempty
   and bounded by `deg(p)`. A selected atom prefix or suffix of `r` would
   increase this maximum. Thus no `σ_j`, `j∈J`, left-divides or
   right-divides `r`. Since `a,b∈A_J`, the element `r` still normalizes
   `A_J`. This step does not require a greatest-head theorem or assert that
   either `a` or `b` preserves `P_J⁺` by conjugation.

3. **The decisive fraction-support lemma.** If `c,z∈A⁺` have left gcd
   `1` and `c⁻¹z∈A_J`, then `c,z∈P_J⁺`. This must be proved, not inferred
   from ambient surjectivity. A minimal proof is described below.

4. **Show the stripped conjugator permutes atoms.** For `j∈J`, choose
   `d=gcd_left(r,σ_j r)` and write `r=d c`, `σ_j r=d z`. Cancellation
   proves `gcd_left(c,z)=1`, and
   `r⁻¹σ_j r=c⁻¹z∈A_J`. Step 3 places `c,z` in `P_J⁺`.
   The absence of a selected suffix of `r` forces `c=1`. Homogeneous
   exponent sum gives `deg(z)=1`, so `z=σ_k` for some `k∈J`.
   Conjugation is injective on the distinct selected atoms. Since `J` is
   finite, this injection of `J` into itself is onto. Consequently
   `r⁻¹P_J⁺r=P_J⁺`. The argument applies to the stripped `r`, not to the
   original positive normalizer `p`.

5. **Factor a positive reduced transporter by outside ribbons.** More
   generally suppose `q:I→K` permutes the selected atoms and no selected
   source atom prefixes `q`. If `q≠1`, choose an atom `σ_a≼q`; then `a∉I`.
   The transporter identity gives `Δ_I q=q Δ_K`, so both `Δ_I` and
   `σ_a` divide `Δ_I q`. Their left lcm is `Δ_{I+a}`. Hence
   `Δ_I μ_{a,I}=Δ_{I+a}≼Δ_I q`, and cancellation gives `μ_{a,I}≼q`.
   Write `q=μ_{a,I}q'`. The elementary endpoint relation makes `q'` a
   transporter from the new object to `K`. A selected prefix of `q'`
   transports across `μ_{a,I}` to a selected source prefix of `q`, so it
   cannot occur. Positive degree decreases strictly. Induction produces
   an actual path of outside `μ` generators.

Steps 1–5 prove that the positive numerator of a normalizer, after a
parabolic factor, is an actual reduced ribbon loop. Completing the group
factorization requires absorbing the denominator `Ωⁿ` and proving the
intersection with `A_J` trivial. The coordinated
`milestone2-mathematical-route.md` develops the reduced cofinal loops
`δ_I=Δ_I⁻¹Δ_S` and `c_I=δ_I δ_{ι(I)}=Δ_I⁻²Δ_S²` for that purpose.
This document does not treat that unfinished formalization as a theorem.

## How to prove fraction support from smaller monoid facts

The following argument replaces an appeal to an unimplemented greedy normal
form or an unproved parabolic embedding.

* Positive braid relations preserve support, and support of a product is the
  union of supports. Therefore every positive factor, on either side, of
  an element of `P_J⁺` also lies in `P_J⁺`.
* Show that fractions `a⁻¹b`, `a,b∈P_J⁺`, form a subgroup of `A`, using
  common left multiples inside `P_J⁺`. This subgroup contains the selected
  generators and is contained in their generated subgroup; hence it is
  exactly the actual `A_J`. No separately presented parabolic group needs
  to be identified with its image for this argument.
* Given `h∈A_J`, choose such a fraction and cancel its ambient left gcd.
  Support closure places its gcd and both residual factors in `P_J⁺`.
  The residual pair is left-coprime.
* Left-coprime positive fractions are unique. For
  `c⁻¹z=a⁻¹b`, choose a common **left** multiple `d c=e a` of the
  denominators; injectivity of `A⁺→A` also gives `d z=e b`.
  Left gcd commutes with multiplication on the left. If both pairs are
  coprime, the gcd of these two displayed positive elements is both `d`
  and `e`; hence `d=e`. Cancellation gives `c=a` and `z=b`.

Thus the canonical coprime pair for a parabolic group element is supported
on `J`. The right-fraction version follows by reversal. Both versions are
needed by the proposed final trivial-intersection argument.

## Candidate Lean suppliers and actual limits

I inspected the following source bodies under
`/tmp/lemma28-full-search/openai-math/lean/OAI/Topology/ArtinGroups/`.
No build, transitive axiom audit, kernel replay or equivalence with this
repository's TauCeti Artin model was performed in this task.

| Source | Actual usable content | Remaining work |
| --- | --- | --- |
| `Cancellation/SphericalPositiveCancelMonoid.lean` | `spherical_positiveToArtin_injective`; left and right positive fractions | Uses OAI's actual presentations, which still require a proved transport to this repository's model; some declarations require `[Fintype S] [LinearOrder S]`. |
| `Harmonic/PositiveLiftSimple.lean` | `positive_fraction_longest` writes `g` as a positive word times a negative power of the longest-lift square; centrality proved immediately before it | Transport the longest lift and the actual group homomorphism; retain its precise negative exponent. |
| `Harmonic/PositivePrefixMulLeft.lean` | `positive_greatest_common_left_divisor`, assuming concrete cancellation and a longest Coxeter element | Build those inputs and the model bridge; author coprime-fraction uniqueness/support. |
| `Harmonic/PositiveReverseHom.lean` | Actual positive reversal and `positive_greatest_common_right_divisor` | Reuse after the same bridge; right-fraction saturation is not already the named theorem. |
| `Harmonic/PositiveDegreeSublevelFinite.lean` | Positive degree bounds; `positive_lcm_of_common_multiple` from concrete gcd and a common multiple | Prove the exact parabolic `Δ` lcm identifications, not only existence. |
| `ParabolicIntersections/PositiveSupport.lean` | Actual support homomorphism, product-union law, and a word supported on a specified subset | Derive divisor closure and the actual parabolic fraction-support theorem. |
| `ParabolicIntersections/PositiveTransport.lean` | Reindexing positive presentations and finite positive cancellation | Its name does not denote ribbon transport or the normalizer splitting. |

The smallest substantial missing chain is: presentation/model bridge;
positive divisor support and internal Ore; uniqueness and support of reduced
fractions; longest-lift/parabolic lcm identities; actual elementary endpoint
relations; positive reduced-ribbon induction; cofinal reduced denominators;
and trivial intersection. The normalizer splitting itself is not an
acceptable assumed input in that chain.

## Confirmed source-text issues and corrections

These findings concern consulted prerequisite sources, not the theorem's
truth and not the original 2025 article's defect report.

1. **Godelle, math/0202174v1, PDF p.7, proof of Proposition 2.1:** it
   writes `g=hΔ_S^{2n}` with `n∈N`, `h∈A⁺`, for arbitrary `g`.
   Taking `g=σ_s⁻¹` gives total exponent sum `−1` on the left and a
   nonnegative sum on the right. The required representation is
   `g=hΔ_S^{−2n}` (or an unrestricted even integer exponent).
   Disposition: confirmed sign error in the inspected preprint, corrected
   in step 1. The journal version has not been checked.

2. **Same preprint, PDF p.12, proof of Proposition 4.4:** it invokes
   Lemma 3.4 to write `g_1=Δ_X^n g_1'` with `g_1'` `X`-reduced for
   arbitrary `X`. Lemma 3.4 assumes indecomposability. For spherical
   commuting `S=X={s,t}`, take the coprime ribbon pair `g_1=s`, `g_2=1`.
   Here `Δ_X=st`; no `n≥0` gives this claimed reduced remainder.
   Disposition: confirmed overgeneralized proof step, not a counterexample
   to the splitting. Strip componentwise Garside factors or use step 2's
   unrestricted parabolic factors. The journal version has not been checked.

3. **Godelle, 0811.0751v1, PDF p.28, proof of Theorem 4.25(ii):** after
   establishing `r_1⁻¹ x r_1∈A_Z⁺` for `x∈X`, the next two displayed
   conjugations use `r_1 A_X⁺ r_1⁻¹`. The compatible conclusion is
   `r_1⁻¹ A_X⁺ r_1=A_Z⁺`, matching the Hom-set convention in the theorem.
   Disposition: confirmed orientation typo, corrected throughout this route.
   It does not change the theorem or justify discarding its fraction-support
   and positive-ribbon prerequisites.

Finally, a positive normalizer need not preserve its positive parabolic:
in spherical type `A₂`, let `J=S={s,t}` and `p=σ_s`. This positive element
normalizes the whole group. If `σ_s σ_t σ_s⁻¹` were positive, homogeneous
degree `1` would make it one of `σ_s,σ_t`; its Coxeter projection is the
third reflection in `S₃`, so neither is possible. The stripping argument is
essential before asserting a positive-monoid transporter.
