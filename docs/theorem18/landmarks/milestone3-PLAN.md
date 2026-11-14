# Landmark 3: actual equivariant geometric groupoid comparison

Status: mathematically accepted after both final independent main reviews and
the passed complete local technical build/audit/replay battery. The 42
scientific modules and aggregate compile and remain frozen. Final-mode
verification and fresh clean CI remain pending. Landmarks 4 and 5 and full
Theorem 1.8 remain unproved. The
[report](milestone3-REPORT.md) records the evidence and proof boundaries.

The independent `chambers/` Lake package requires the unchanged landmark/ribbon
packages and their exact inherited Lean/mathlib pins. Its final theorem is
`ArtinNormalisers.Chamber3.landmark_3`, for every `M : CoxeterMatrix I` with
`[Finite M.Group]` and every `J : Set I`, including rank zero and empty/full
parabolics.

## Implemented proof contract

The interval groupoid on the actual restricted real chambers is equivariantly
equivalent to `FundamentalGroupoid (Theorem18.Complement M J)`. The actual
signed ribbon covering targets the `J`-associate component of the independently
defined reduced ribbon groupoid. That component is equivalent to the actual
orbit space's fundamental groupoid, with a strict covering square. Both action
cocones satisfy the ordinary groupoid orbit-colimit property. Every signed
ribbon endpoint has the actual Coxeter projection label in the same
`N_W(W_J)/W_J`.

The implemented presentation has positive generators for **all ordered pairs**
of actual chambers and self/`ChamberBetween` relations. A dictionary with the
article's literal adjacent-gallery presentation is not asserted. Opposite
positive arrows remain separate, and no transitivity on all chambers is
assumed. The geometric comparison itself is proved directly, not assumed.
Source motivation remains arXiv:2509.21915v3, Sections 3/4/6, especially
Lemma 6.6 and Proposition 6.3; see also the original
[independent contract](milestone3-contract-a.md).

## Completed scientific dependency order

1. Actual continuous restricted-root evaluations, strict sign chambers and
   real regular components; an actual homeomorphism to the existing relative
   complement, with inherited topology.
2. Actual open chamber tubes and their covering property; explicit two-stage
   contractions of tubes and finite-overlap components.
3. Acceptance of the pinned nine-new-module TauCeti Čech/open-cover groupoid
   van Kampen closure, including continuous-map naturality. Its build, audit,
   replay and independent supplier reviews are separately recorded.
4. The interval groupoid and its universal property; actual tube connectors
   and gluing prove its equivalence with the genuine fundamental groupoid.
5. Actual Coxeter facet/chamber labels, minimal positive transport and
   Between compatibility; complete chosen-lcm relations give signed ribbon
   lifting and uniqueness on outgoing arrows, hence the actual ribbon cover.
6. Strict equivariance for canonical actual chamber points and all arrows;
   literal object surjectivity and orbit fibers for both actual covers.
7. Generic invariant-functor descent and comparison of quotient covers,
   instantiated on these actual objects; the downstairs equivalence, strict
   square, separate orbit-colimit proofs and all-signed Coxeter endpoint formula.

No final comparison or universal property is stored as an assumed target
field. Ambient Coxeter weighted length is not the restricted wall count.
This route does not require a new simpliciality or asphericity hypothesis.

## Review acceptance and remaining closeout gates

Both independent final reviews accepted Landmark 3. The
[root acceptance receipt](milestone3-root-acceptance.json) validates their
exact bindings and the passed technical evidence; the frozen inventory retains
its historical candidate status. This is mathematical acceptance, not a claim
of fresh clean CI or full Theorem 1.8.

1. Run final verification against both final reviews and the frozen root-owned
   source inventory. Preserve the passed complete technical battery and
   record the final receipt, with exact source/context/tool bindings.
2. Preserve a fresh clean CI compilation record after the authorized commit/push.
   Do not infer CI success from a local build or from earlier landmarks.
3. Close the remaining verification/CI gates when these records pass, then proceed sequentially
   to Landmark 4. The based exact sequences and Deligne asphericity remain
   separate obligations, not consequences silently added to this closeout.

Reproduction commands and the limitations of technical versus final mode are
in the [report](milestone3-REPORT.md#verification-checkpoint-and-reproduction).

## Source and literature records

The central [GitHub source register](../../provenance/GITHUB-PROOF-SOURCES.md)
records pins, licenses, copied proofs, import-only relocations and verification
separately from inspected candidates. Older accepted dependencies are preserved;
the new supplier cohort adds nine modules and 232 physical/canonical declarations.

The [Lemma 3.5 note](milestone3-source-findings-a.md) retains an unresolved
boundary-representative clarification and its exact counterexample limits,
without claiming an original-article defect. The finite-type proof does not
use the disputed induction. Earlier prerequisite findings and reading limits
remain in the [Milestone 2 report](milestone2-REPORT.md#consulted-source-findings-retained).

Missing formal proofs are established mathematics to formalize, not open
problems or defects of the article. Landmark 4's group-level exact-sequence
comparisons and landmark 5's asphericity remain separate obligations.
