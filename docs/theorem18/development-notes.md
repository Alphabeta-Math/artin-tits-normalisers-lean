# Development failures and limits

These are implementation/verification issues, not findings against the article.
No mathematical error in Theorem 1.8 was established by this work.

1. The first build of the new unchanged TauCeti topology closure failed
   because this package set `autoImplicit = false` globally, while upstream
   uses the default inference of undeclared source-basepoint variables.
   `TauCeti.AlgebraicTopology.FundamentalGroup.Basic` consequently reported
   unknown `a₀` and elaboration-error placeholders. That failed build was not
   accepted. The correction scopes upstream's `autoImplicit = true` to the
   `TauCeti` Lake library, retaining `false` for project proofs. No upstream
   source was patched. A subsequent build succeeded, and the final audit
   explicitly prints the inferred `{a₀ : A}` and its subsingleton-source-π₁
   hypothesis. The original failed command was observed directly; a complete
   standalone raw log of that first attempt was not saved.
2. The first root aggregate put a module docstring before its imports, which
   Lean rejects. Moving imports to the module header fixed the syntax. This
   failure had no accepted proof artifact.
3. A first enlarged audit used three names from a supplier that was only
   privately imported by another module. Its checks failed with unknown
   identifiers, despite the later audit command also printing a count. The
   process exit was **1**, so the count was not a passing certificate. The
   authentic failed output is retained in
   `evidence/theorem18-development/audit-private-import-failure.log`.
   Directly importing that supplier fixed visibility. The final harness goes
   further and directly imports every one of the 33 supplier modules; the
   driver requires exact defining-module coverage of all 33 suppliers and
   all four new project modules. Both independent reviewers identified the
   original visibility failure before final acceptance.

All mathematical source/proof validity claims refer to the subsequent
successful hash-bound verification records, not these failed attempts.
Kernel replay uses the official checker one module at a time, relative to
its imported mathlib environment; it is neither a second kernel nor a fresh
replay of the entire mathlib library. The earlier rc2 aggregate-checker crash
remains documented in the historical Lemma 2.8 records.

GitHub code-search requests reached an API rate limit during the bounded
search. Known repositories were then inspected using pinned local Git trees
and exact source reads. An absent result in that search is not a proof that
no formalization exists elsewhere. The ordinary Salvetti candidate was not
imported, built or accepted as an arrangement-comparison supplier; its
different actual domain and missing comparison are recorded in
`search-openai.md`.
