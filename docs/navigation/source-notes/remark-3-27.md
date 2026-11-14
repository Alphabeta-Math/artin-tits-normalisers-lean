# Remark 3.27: finite CW scope

Status: confirmed scope error in the original article under the usual meaning of a **finite CW complex** (finitely many cells). This is an independently checked classical counterexample, not an additional Lean formalization or a prerequisite used by the verified finite-type proof.

The source is Garnier–Heng–Licata–Yacobi, [arXiv:2509.21915v3, Remark 3.27, printed/PDF p. 13](https://arxiv.org/pdf/2509.21915v3#page=13), immediately after equation **(3.26)**. It asserts that local finiteness of the arrangement in an open convex cone gives a complement with a “finite CW-model.” Section 3 is not restricted to spherical type; §2.2, p. 4, explicitly reserves that restriction for §§5–6.

The unrestricted finiteness conclusion fails for the allowed rank-two Coxeter system with $m_{st}=\infty$ and $J=\varnothing$. Its actual complement is homeomorphic to an open quadrant times $\mathbb C\setminus\mathbb Z$, and therefore has infinitely many independent first-homology classes. Restricting the finiteness assertion to spherical type avoids this counterexample. The local-finiteness hypothesis alone permits infinitely many cells.

## Counterexample under the complete source hypotheses

Use the standard real geometric representation with basis $\alpha_s,\alpha_t$ and bilinear form

$$B(\alpha_s,\alpha_s)=B(\alpha_t,\alpha_t)=1,\qquad B(\alpha_s,\alpha_t)=-1.$$

Set $\delta=\alpha_s+\alpha_t$. The reflection formulas are

$$s\alpha_s=-\alpha_s,\quad s\alpha_t=\alpha_t+2\alpha_s,
\qquad t\alpha_s=\alpha_s+2\alpha_t,\quad t\alpha_t=-\alpha_t.$$

Thus $\delta$ is fixed and the full real-root set is

$$\Phi=\{\pm(\alpha_s+n\delta):n\in\mathbb Z\}.$$

The two simple-root orbits supply the two parities; the displayed set is stable under both reflections, so this includes every real root and no additional root is required.

For a real dual point write $a=\varphi(\alpha_s)$ and $d=\varphi(\delta)$. The closed fundamental chamber satisfies $a\ge0$ and $d-a\ge0$. For $d>0$ its ratio $a/d$ lies in $[0,1]$; the dual reflections send this ratio to $-a/d$ and $2-a/d$. Their translates tile the real line. The source's Tits cone, the union of translates of this closed chamber, is consequently

$$\operatorname{Cone}=\{\varphi:\varphi(\delta)>0\}\cup\{0\},\qquad
\operatorname{Cone}^{\circ}=\{\varphi:\varphi(\delta)>0\}.$$

Taking $J=\varnothing$ recovers this full arrangement, as stated in the article. Every root hyperplane occurs. The arrangement is locally finite in the open cone: on any compact subset, $d$ has a positive lower bound and $|a|$ has an upper bound, so $a+nd=0$ is possible for only finitely many integers $n$.

Now use the actual two-cone complement of equation (3.26), rather than substituting an unrestricted complexification. For $z=x+iy$ set

$$d=z(\delta),\qquad u=\frac{z(\alpha_s)}{z(\delta)}.$$

Both real factors lie in the open Tits cone precisely when $\Re d>0$ and $\Im d>0$. A root vanishes at $z$ precisely when $u$ is an integer. There is an explicit homeomorphism

$$X_{\varnothing}^{\mathbb C}\ \cong\ Q\times(\mathbb C\setminus\mathbb Z),
\qquad Q=\{d\in\mathbb C:\Re d>0,\ \Im d>0\},$$

whose inverse is $z(\alpha_s)=du$ and $z(\alpha_t)=d(1-u)$. The quadrant $Q$ is nonempty and convex.

For each integer $n$, let $\gamma_n(\theta)=n+\tfrac14e^{2\pi i\theta}$ be a meridian in $\mathbb C\setminus\mathbb Z$. For each integer $k$, the map $u\mapsto u-k$ to $\mathbb C^{\times}$ induces a winding-number homomorphism on first homology. It takes $[\gamma_n]$ to $1$ for $k=n$ and to $0$ otherwise. The meridian classes are therefore an infinite linearly independent family over $\mathbb Z$.

A finite CW complex has finitely generated first integral homology. Homotopy equivalence preserves homology, so this complement cannot have a finite CW model.

## Effect on the verified results

The [verified Theorem 1.8](../index.md) assumes the actual Coxeter group is finite. Its proof constructs the required higher-homotopy comparison directly and uses no unrestricted finite-CW assertion. The finite-type setting of Corollary 6.14 and Remark 6.15 is unaffected by this infinite-dihedral example. The Lean project asserts the documented K(G,1) predicate; a finite-CW strengthening is outside its claimed scope.

This assessment checks the article's finiteness inference directly. Paris [29]'s complete Salvetti comparison proof was not reread for this note. The example is compatible with an infinite Salvetti CW model.

The [independent assessment](remark-3-27-independent-assessment.md) records the second source check, exact representation calculation, reading limits, and original source locators. The original PDF/text identities are retained in the [attribution atlas](../data/attribution/README.md).
