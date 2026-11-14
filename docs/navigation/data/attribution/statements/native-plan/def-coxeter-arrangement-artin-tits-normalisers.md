For the geometry in this item, let the vertex set $\Gamma_0$ be finite. This is the finite-rank Coxeter-graph convention of Iyama–Wemyss, §§1.1–1.3; the Coxeter group $W$ may be infinite. Use the geometric representation, roots and algebraic dual $\Theta=V^*$ of [[def-coxeter-data-artin-tits-normalisers]], specialized to this finite vertex set, and the finite-rank realization of [[def-real-coxeter-interface-artin-tits-prerequisites]].

The coordinate map $\Theta\longrightarrow\mathbb R^{\Gamma_0}$, $f\longmapsto(f(\alpha_i))_{i\in\Gamma_0}$, is a linear isomorphism. Give $\Theta$ its transported Euclidean topology, as in [[def-arrangement-topology-interface-artin-tits-prerequisites]]. For a subset $A\subseteq\Theta$, its closure $\overline A$ consists of points every open neighbourhood of which meets $A$; its interior $A^\circ$ is the union of open subsets contained in $A$.

For each root $\alpha\in\Phi$ define the reflecting hyperplane and the set of distinct such hyperplanes by
$$H_\alpha=\{f\in\Theta:f(\alpha)=0\},\qquad\mathcal H=\{H_\alpha:\alpha\in\Phi\}.$$
Define the open fundamental chamber and its closure by
$$C=\{f\in\Theta:f(\alpha_i)>0\text{ for every }i\in\Gamma_0\},\qquad\overline C=\{f\in\Theta:f(\alpha_i)\geq0\text{ for every }i\in\Gamma_0\}.$$
The Tits cone and its interior in $\Theta$ are
$$\mathrm{Cone}=\bigcup_{w\in W}w\overline C,\qquad\mathrm{Cone}^\circ=\operatorname{int}_{\Theta}(\mathrm{Cone}).$$
The notation $w\overline C$ uses the contragredient action: $wf=f\circ\rho(w)^{-1}$. The family $\mathcal H$ is a set, so coincident hyperplanes are included only once.