Let $E$ be a real vector space equipped with a specified topology, and give each subset of $E$ the subspace topology: its open sets are its intersections with open subsets of $E$. In the finite-dimensional setting one may use the Euclidean topology described in the arrangement interface. A subset $T\subseteq E$ is convex when $(1-t)x+ty\in T$ for all $x,y\in T$ and $0\leq t\leq1$. A linear hyperplane is a linear subspace $H\subseteq E$ of codimension one, meaning that $E/H$ has dimension one.

A hyperplane arrangement $(T,\mathcal H)$ consists of a convex subset $T\subseteq E$ and a set $\mathcal H$ of linear hyperplanes in $E$, possibly infinite, such that $H\cap T\ne\varnothing$ for every $H\in\mathcal H$.

For a convex subset $T'\subseteq T$, the restriction to $T'$ is the arrangement $(T',\mathcal H_{T'})$, where $\mathcal H_{T'}=\{H\in\mathcal H:H\cap T'\ne\varnothing\}$. It is also denoted $(T',\mathcal H)$ when the restriction of the hyperplane set is understood.

The arrangement is locally finite if, for every $x\in T$, there is an open set $U$ in the subspace topology on $T$ with $x\in U$ such that $U$ meets only finitely many distinct members of $\mathcal H$.