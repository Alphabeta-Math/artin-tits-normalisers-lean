Let $(W,S)$ be a Coxeter system with finite $W$, and let $J\subseteq S$. Use the finite-dimensional relative space $E=\Theta_J$, its finite set $\mathcal H^J$ of distinct linear hyperplanes, and the relative complexified complement $\mathcal X_J^{\mathbb C}$ from [def-relative-complement-artin-tits-normalisers](item-def-relative-complement-artin-tits-normalisers). Thus $\mathcal X_J^{\mathbb C}$ consists of $x+iy$ with $x,y\in E$ and no $H\in\mathcal H^J$ containing both $x$ and $y$. The arrangement has ambient domain $E$; its chambers are the connected components of $E\setminus\bigcup_{H\in\mathcal H^J}H$, and adjacent chambers are distinct chambers sharing a wall, as in [def-chambers-walls-artin-tits-normalisers](item-def-chambers-walls-artin-tits-normalisers).

For $H\in\mathcal H^J$ and a chamber $C$, let $D_H(C)$ be the open half-space bounded by $H$ that contains $C$: if $a:E\to\mathbb R$ is a nonzero linear functional with kernel $H$, it is either $\{v:a(v)>0\}$ or $\{v:a(v)<0\}$, according to which contains $C$. Define

$$X_C=\{x+iy\in\mathcal X_J^{\mathbb C}:\text{ for every }H\in\mathcal H^J,\ x\in H\Rightarrow y\in D_H(C)\}.$$

Let $C,C'$ be adjacent, and let $H_0$ be their unique separating hyperplane. Define

$$X_{C,C'}=\{x+iy\in\mathcal X_J^{\mathbb C}:x\in D_{H_0}(C),\ \text{and for every }H\in\mathcal H^J,\ x\in H\Rightarrow y\in D_H(C)\cap D_H(C')\}.$$

Define $X_{C',C}$ by interchanging $C$ and $C'$ in this formula. These are subsets of $\mathcal X_J^{\mathbb C}$ with its subspace topology.