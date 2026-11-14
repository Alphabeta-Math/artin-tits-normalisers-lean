# Landmark 3: independent source finding A — Lemma 3.5 boundary choice

Reviewer: **GPT-6.1 Sol/high** (`gpt-6.1-sol`, reasoning effort `high`).
Date: 2026-11-14. This is a source-check note, not a publication, portal
update, formal proof receipt or allegation that Lemma 3.5 is false.

**Disposition: unresolved as an attribution of a substantive source defect.**
The proposed rank-one example verifies that two general implications do not
follow from an arbitrary closed-chamber representative. The first implication
has an important additional local scope in the actual proof, however, and
a legitimate refinement of the freely chosen representative or an omitted
early case handles the second. The lemma has an immediate direct repair
using the one-way implication actually needed. Thus this evidence warrants
an explicit proof-choice clarification, not a confirmed false lemma or an
unqualified “article error” finding.

## Exact source and full claim

Source: Garnier–Heng–Licata–Yacobi, arXiv:2509.21915v3, **PDF page 8,
Lemma 3.5 and its complete proof**. The statement is:

> Let f,g ∈ Cone. Then the number of hyperplanes in H separating f and g
> is finite.

Immediately before the lemma, separation means the two points belong to
different components of `Cone \ H`; an endpoint on H is not separated
from the other endpoint by H.

The proof explicitly defines

```
Cbar := disjoint_union_(K ⊆ Γ₀) C_K,
```

as the **closure** of the open chamber `C=C_∅` in Cone. It then says:

> Since Cbar is a fundamental domain for the action of W, we may assume
> without loss of generality that f ∈ Cbar and g ∈ w Cbar for some w ∈ W.

After fixing `h∈(f,g)` and considering a positive-root hyperplane meeting
that open segment exactly at h, it says:

> Recall that g ∈ w Cbar. It follows that g(α)<0 if and only if
> w⁻¹·α ∈ Φ⁻.

Later, in the induction on ℓ(w), it says:

> We may now assume that w is nontrivial, so that g ∈ w Cbar ≠ Cbar.
> In particular, the following set is non-empty:
> I := {i∈Γ₀ | g(α_i)<0}.

I checked the full original page image, not only text extraction, because
the extraction drops several overbars. I also visually checked PDF pages
4 and 7 and read the surrounding background on pp.4–5 and the beginning
of §3. The source distinguishes the open chamber C from its closure;
C_K is the face with zero evaluations on K and strictly positive evaluations
outside K. No rule in those inspected definitions or the complete lemma
proof specifies w to have minimal length among the closed chambers containing
g, nor to be a minimal representative for g's facet stabilizer. The source
introduces explicit minimal-representative conditions elsewhere, but that
is not a local convention stated for this w.

Frozen files actually inspected:

- `article.pdf`: SHA-256
  `7a18b3e54c6edce92d8256afe6eae4da0d0483b58f3654a338e90a6b745f83da`.
- `article.txt`: SHA-256
  `d98828d0f8f7d179ca8437bc6d98b7f8f7f50ae94012fdca1243cb4024390876`.
- `pages/page-8.png`: SHA-256
  `d98d7809ce29660fe76dfda99e923e2b3c6be87fbcaef3cfa68f96c356f92496`.

All paths are under the existing sibling-workflow directory
`.research-workflow/artin-tits-normalisers-2509-21915-20261113/`.

## Rank-one evidence and its exact scope

Use finite type A₁. Write a dual vector by its coordinate `t=φ(α)`. Then

```
W={1,s},    s·α=−α,    s·t=−t,
Φ⁺={α},    C=(0,∞),    Cbar=[0,∞),
s Cbar=(−∞,0],         Cone=ℝ.
f=1,       g=0,        w=s.
```

This meets the lemma's entire initial setup: f,g∈Cone, f∈Cbar,
g∈w Cbar, f≠g, and w is nontrivial of length one. Yet

```
w⁻¹·α=−α ∈ Φ⁻,       g(α)=0,
I={i | g(α_i)<0}=∅.
```

Consequently:

1. Under **only** `g∈w Cbar`, the implication
   `w⁻¹α∈Φ⁻ ⇒ g(α)<0` is false. Evaluation of a negative root at a point
   of the closed chamber can be zero.
2. For an arbitrary such w, `w≠1` and the fact that `w Cbar` differs from
   Cbar as a set do not imply I is nonempty. Different closed chambers can
   share g. In this example their intersection contains 0.

The first observation must **not** be promoted to a counterexample to the
proof's full preceding local situation. Here the sole root hyperplane is
`H_α={0}`, whereas `(f,g)=(0,1)`, so there is **no** interior h with
`H_α∩(f,g)={h}`. For a hyperplane actually meeting the open segment exactly
once, the proof has already derived `f(α)>0` and `g(α)<0`. The disputed
biconditional then has a true left side and only its valid forward
implication is needed for the inversion-set bound. The rank-one example
is therefore outside that local h/α hypothesis. It only disproves an
unrestricted reading of the sentence's claimed justification.

The second observation is genuinely inside the stated initial induction
setup if w is taken as an arbitrary witness. But the proof is free to choose
a better witness: in this example w=1 also works. Alternatively, since
both f and g lie in Cbar, the no-separator case is already immediate. Thus
the example shows a missing choice/early-case qualification in that reading;
it does not show no valid choice exists.

The conclusion of Lemma 3.5 is true in this example: H_α contains g,
so it separates neither endpoint pair. There are zero separating hyperplanes.
No counterexample to the lemma has been found.

## Correction that avoids both issues completely

There is a direct proof using the same standard facts already invoked in
the source, without the intersection-point induction or minimality of w.
Normalize f∈Cbar and choose **any** w with g∈w Cbar. Put h=w⁻¹·g∈Cbar.
For every positive root α,

```
g(α)<0  ⇒  w⁻¹·α∈Φ⁻.
```

Indeed `g(α)=h(w⁻¹·α)`, and a positive root has nonnegative evaluation
on Cbar, so `w⁻¹α∈Φ⁺` would contradict the strict negative evaluation.
The reverse implication is unnecessary and need not hold.

Now let H be any hyperplane separating f and g. Choose a positive root α
with H=H_α. Because f∈Cbar, f(α)≥0; because H strictly separates f and g,
actually f(α)>0 and g(α)<0. Therefore α belongs to the finite inversion set

```
N(w⁻¹) = {α∈Φ⁺ | w⁻¹·α∈Φ⁻},     |N(w⁻¹)|=ℓ(w⁻¹).
```

It follows directly that

```
{H∈H | H separates f and g} ⊆ {H_α | α∈N(w⁻¹)}.
```

The right side is the image of a finite set, so is finite. Repeated roots
or hyperplane labels do not cause a problem: only inclusion in a finite
image is used. This proves precisely the lemma's claimed conclusion for
an arbitrary w witness, including boundary points and f=g. It uses the
same standard root-sign dichotomy, dominant evaluation and finite inversion
set/length theorem cited in the original proof; it is an ordinary
mathematical derivation, **not a new Lean-verified proof**.

Another possible editorial repair is to choose w of smallest length among
all witnesses `g∈w Cbar`. A minimum exists because Coxeter length is natural
valued. Then if g∈Cbar, w=1 has smaller or equal length, so nontrivial w
forces a negative simple evaluation. Recovering a full unrestricted strict
biconditional from that choice additionally uses the standard minimal-coset
positivity/root-support facts for the face containing `w⁻¹g`; those facts
must be stated/proved if this alternative route is formalized. I do not
silently insert that stronger choice into the printed text. The direct
one-way finite-image argument above avoids this extra dependency.

## Final disposition and reading limits

The original notation really is closed-chamber notation and the inspected
local context contains no explicit minimal-w instruction. The rank-one
calculations are verified elementary mathematics. Nevertheless:

- The first proposed counterexample fails the local interior-hyperplane
  hypothesis of the paragraph using the inversion-set bound.
- The freely chosen witness can legitimately be refined to remove the
  second problem, or the proof can handle `g∈Cbar` before the induction
  step. Whether the authors intended such an implicit refinement is
  unresolved by the source text.
- The lemma itself has the direct valid proof above. This is not evidence
  against Proposition 3.6, Theorem 1.8, or the article's conclusions.

Accordingly I record **a boundary-representative proof clarification with
unresolved attribution/severity**, not an independently confirmed substantive
article defect. I have not contacted authors, changed a portal, published
an attribution, inspected another article version, or checked Vinberg [31]
Lemma 9 or every cited root-system proof. No theorem from this source note
has been compiled or kernel-replayed. This note was produced independently
of reviewer B and only this owned Markdown file was written.

The present formalization's finite-W route obtains finiteness of the actual
root/restricted-hyperplane family directly and does not consume Lemma 3.5
or this induction. This source clarification introduces no new premise,
proof repair or accepted change to the frozen Landmark 1/2 development,
and is not a blocker to that separate finite-type route.
