Let $E$ be a finite-dimensional real vector space with the Euclidean topology supplied by linear coordinates. Let $T\subseteq E$ be nonempty, open and convex, and let $\mathcal A$ be a locally finite arrangement in $T$: its members are linear hyperplanes meeting $T$, and every point of $T$ has a neighbourhood meeting only finitely many members. Define the complement

$$M(T,\mathcal A)=(T\times T)\setminus\bigcup_{H\in\mathcal A}(H\times H).$$

Give $T\times T$ the product topology and $M(T,\mathcal A)$ its subspace topology: its open sets are intersections of $M(T,\mathcal A)$ with open subsets of $T\times T$.

When $T=E$, put $E_{\mathbb C}=\mathbb C\otimes_{\mathbb R}E$ and identify $(x,y)$ with $1\otimes x+i\otimes y$, also written $x+iy$. For each $H\in\mathcal A$, its complexification inside $E_{\mathbb C}$ means $H_{\mathbb C}=\operatorname{span}_{\mathbb C}\{1\otimes h:h\in H\}$. Under this identification the complement is $E_{\mathbb C}\setminus\bigcup_{H\in\mathcal A}H_{\mathbb C}$.

Suppose a group $G$ acts on $E$ by invertible real-linear maps and each $g\in G$ preserves $T$ and permutes $\mathcal A$. The action convention is $ex=x$ and $(gh)x=g(hx)$. The diagonal action on $T\times T$ is $g\cdot(x,y)=(gx,gy)$; its restriction to the complement is the diagonal action on $M(T,\mathcal A)$.

A homeomorphism is a continuous bijection with continuous inverse. A covering-space action is an action by homeomorphisms for which every point has an open neighbourhood $U$ satisfying $gU\cap U=\varnothing$ for every nonidentity $g$. Setwise preservation alone does not assert this condition or path connectedness. Path connectedness means that for any $p,q\in M(T,\mathcal A)$ there is a continuous map $\gamma:[0,1]\to M(T,\mathcal A)$ with $\gamma(0)=p$ and $\gamma(1)=q$, where $[0,1]$ has its usual subspace topology from $\mathbb R$.