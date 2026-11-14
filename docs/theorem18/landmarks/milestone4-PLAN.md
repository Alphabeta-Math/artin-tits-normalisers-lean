# Landmark 4: compatible normalizer and fundamental-group exact sequences

Status: landmark 4 is mathematically accepted after both independent final
reviews and the complete local build/audit/replay battery. Clean final-mode
GitHub CI and permanent archival closeout are pending. Deligne asphericity
and full Theorem 1.8 remain unproved. See [report](milestone4-REPORT.md).

## Exact target and source

Formalize Theorem 6.7 and the actual-map content of Remark 6.12 in
Garnier–Heng–Licata–Yacobi, arXiv:2509.21915v3, PDF pp.26–27. For every
Coxeter matrix M with finite actual Coxeter group and every J, construct
multiplicative equivalences from the existing pure normalizer image and
Artin normalizer quotient to the actual fundamental groups of Complement M J
and OrbitSpace M J. Prove both squares commute with the actual inclusion,
actual covering-induced homomorphism, canonical Artin–Coxeter quotient map
and actual endpoint monodromy, using identity on the same Coxeter quotient.
Prove both actual rows short exact at every actual complement basepoint.
No simply-connectedness, universal-cover assumption, asphericity or target
comparison is allowed as an unproved input.

## Conventions and proof order

1. Inspect exact existing GitHub proofs, including pinned mathlib/TauCeti and
   other repositories. Maintain full pins, file/declaration names, hypotheses,
   licenses, modifications, actual reading and verification limits. Use a
   minimal new supplier cohort only where it genuinely saves a relevant proof;
   search candidates are not accepted proof inputs.
2. Identify the vertex End of the actual reduced J-associate ribbon component
   with reduced ribbon loops in the correct opposite group. The larger
   RibbonObject groupoid is insufficient. Use the actual M2 normalizer quotient
   equivalence and M3 actual groupoid equivalence, transporting the literal
   basepoint equality provided by the strictly commuting square.
3. Preserve the natural positive-label comparison into the opposite of
   mathlib's fundamental group. For ordinary mathlib fundamental groups use
   the actual inverse ribbon label. Normalize raw endpoint monodromy Qop→Q
   by op(q)↦q⁻¹, a multiplicative equivalence. Plain op/unop or inversion
   within a noncommutative group is not silently treated as a homomorphism.
4. Prove endpoint monodromy on actual lifted path classes, instantiate the M3
   signed endpoint formula, and prove the middle/right square with identity
   on the same Q. In the standard mathlib convention the raw label is
   op((canonical projection a)⁻¹); the normalized label is the canonical
   projection a itself.
5. Transport the comparison from the standard chamber point to every x using
   an actual upstairs path θ and its actual projected path downstairs.
   Prove both covering-map and monodromy basepoint naturality. Independent
   downstairs path choices may conjugate quotient labels and are not used.
6. Construct the pure comparison from the proved compatible middle map and
   actual kernel/image exactness. Its inclusion square is proved from the
   actual induced maps. Bundle both equivalences, both commuting squares
   and both actual short exact rows as Theorem 6.7's full formal statement.
7. Obtain two independent GPT-6.1 Sol/high semantic/source-correspondence
   reviews of every final statement. Compile, audit every declaration and
   physical occurrence, reject proof holes/custom axioms, and replay every
   new scientific module. Commit/push and preserve a clean CI artifact,
   full logs, source bindings and permanent compilation evidence.

## Package, source record and preservation

The independent sequences/ Lake package inherits chambers/, ribbons/,
landmarks/ and the parent package with identical Lean and nine Git pins.
All previous accepted scientific/configuration/review inputs remain frozen;
new proof sources, audits, reviews and evidence are separate. The source
register in docs/provenance/ must retain all previous immutable graphs and
add this milestone's exact proof dependencies and publication bindings.

Independent initial source contracts are milestone4-contract-a.md and
milestone4-contract-b.md. Missing formal helpers are established mathematics
to formalize, not open problems or defects of the original article. All
consulted-literature findings retain exact sources, evidence and dispositions.

Landmark 5 remains the separate finite central simplicial-arrangement and
Deligne asphericity obligation. Completing this landmark does not complete
Theorem 1.8 or either K(π,1) conclusion.
