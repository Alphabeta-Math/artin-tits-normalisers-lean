# Where Lemma 2.8 enters the article's main results

In [arXiv:2509.21915v3](https://arxiv.org/abs/2509.21915v3), Lemma 2.8 supplies
the algebraic short exact sequence

`1 → N(P,J) → N(A,J) → N(W,J) → 1`.

It is used directly in **Theorem 6.7**, which identifies this sequence with
the fundamental-group sequence of the normal covering
`X_J^C → X_J^C / N(W,J)` for spherical type. The paragraph immediately before
Theorem 6.7 explicitly explains that Theorem 6.7 together with Corollary 6.14
proves the introduction's **Theorem 1.8**, the main relative `K(pi,1)` theorem.

Thus the dependency is:

```text
Lemma 2.8 → Theorem 6.7 → Theorem 1.8
                           ↑
                    Corollary 6.14
```

This repository currently verifies the full algebraic Lemma 2.8 for the standard
Artin presentation. It does not claim a formal proof of Theorem 6.7, Corollary
6.14, Theorem 1.8, or the separate topological/presentation identification.
