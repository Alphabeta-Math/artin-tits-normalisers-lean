# Theorem 1.8 formalization plan

Source: Garnier–Heng–Licata–Yacobi, arXiv:2509.21915v3, Theorem 1.8,
proved through Theorem 6.7 and Corollary 6.14. Target repository:
<https://github.com/lazyinspirit/artin-tits-normalisers-lean>.

**The full theorem is not yet proved.** The algebraic Lemma 2.8 is complete;
it supplies only the algebraic row of the theorem's comparison diagram.
This plan keeps the entire original conclusion, including both geometric
fundamental groups, both compatible maps and both asphericity assertions.

## Exact target and search

Use the actual standard representation and its contragredient on the dual.
For arbitrary `J` and finite `M.Group`, define the actual relative flat
`Θ_J`, remove precisely the proper restricted root hyperplanes in real and
imaginary coordinates, and form the actual topological orbit quotient by
`N_W(W_J)/W_J`. The formal spaces must be defined independently of the desired
fundamental groups. A nerve or a classifying space can replace them only
after a proved geometric comparison.

The independently prepared [statement contracts](reviews/) and
[mathematical route](mathematical-route.md) specify the full target, source
locators and multiplication/basepoint conventions. The bounded GitHub search
is recorded in [TauCeti/mathlib search](search-tauceti-mathlib.md) and
[ordinary Salvetti search](search-openai.md). In particular, ordinary Coxeter
Salvetti results are not directly applicable to the restricted arrangement;
its normalizer quotient need not be a Coxeter reflection group.

## Implementation order

1. **Actual geometry.** Construct the free real root space, actual dual and
   its dual-basis coordinate homeomorphism, relative flat, orbit roots,
   proper restricted hyperplanes and real-pair complement. Derive finite
   rank/root finiteness from finite Coxeter group and prove openness.
2. **Actual action and topology.** Identify the flat with the parabolic-fixed
   subspace. Restrict the contragredient action to the normalizer and descend
   through the actual parabolic quotient. Prove complement preservation,
   continuity, nonemptiness and path connectedness. Construct the actual
   orbit quotient with its quotient topology.
3. **Verified generic suppliers.** Reuse pinned mathlib covering monodromy
   and injectivity. Import only the unchanged pinned TauCeti closure needed
   for actual higher-homotopy groups, asphericity and covering transfer.
   Build against our pins, inspect elaborated hypotheses, audit every
   project/provider declaration transitively, and replay each module.
   Monodromy currently has explicit target `Qᵐᵒᵖ`; eventual comparison must
   prove the source convention transport and compatibility over identity
   on `Q`.
4. **Finite reflection chambers and freeness.** Prove the restricted
   arrangement's actual chamber identification and simpliciality, and
   regular-point stabilizers. Deduce freeness on the complex complement
   using a generic real linear combination of its coordinates, then obtain
   the regular covering from the actual quotient map. Finiteness alone
   supplies proper discontinuity, not freeness.
5. **Ribbon algebra.** Develop positive Artin/Garside theory and the reduced
   ribbon groupoid. Prove the vertex-group identification with the existing
   presentation-defined normalizer quotient, and the complete relations
   required to compare chamber paths. Do not assume this identification.
6. **Geometric groupoid comparison.** Construct the arrangement Deligne
   groupoid and prove its equivariant comparison with the fundamental
   groupoid of the actual complement (or prove an equivalent Salvetti
   homotopy comparison). Positive crossings in the reverse direction are
   separate arrows, not inverses.
7. **Compatible sequences.** Compare the ribbon/chamber covering with the
   actual topological covering, identify its monodromy with the canonical
   Artin-to-Coxeter normalizer projection, and prove both squares commute.
   Transport both identifications using the same basepoint path, for every
   point of the actual complement.
8. **Asphericity.** Prove Deligne's finite central simplicial arrangement
   theorem, or an equivalent contractibility result with a proved comparison
   to the actual universal cover, and apply it to this arrangement. Transfer
   asphericity to the actual orbit quotient and combine it with the two
   proved fundamental-group identifications.
9. **Final verification/publication.** Obtain independent GPT-6.1 Sol/high
   reviews of all exact statements and dependency applications; compile,
   audit transitive axioms, replay modules, archive commands/logs/input
   hashes and GitHub CI, and publish the actual final theorem only when all
   eight stages have unconditional proofs.

## Current boundary

The initial implementation addresses stages 1–3. Stages 4–8 are still
substantial missing formal proofs. They are established mathematics to
formalize, not hypotheses that can be inserted into an advertised completed
Theorem 1.8, and not open problems or defects in the article.

The optional `ArtinTheorem18` target and its verification record are kept
separate from the completed `ArtinNormalisersFull` target. Its evidence
explicitly sets `full_theorem_1_8_proved` to `false`; successful prerequisite
compilation must never be reported as a proof of the main theorem.
