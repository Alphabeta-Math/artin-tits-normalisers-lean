# Useful endpoint declarations

All names below are in `OAI.HarmonicArtin`. The exact source/parent
presentation comparison is not part of this vendor snapshot.

- `PositiveArtin M` is `PresentedMonoid (positiveBraidRelations M)`.
  `positiveToArtin M` maps its canonical generators into the actual
  `PresentedGroup (braidRelators M)`. Defined in `Coxeter.PositiveBraidRelations`.
- `positiveSimpleLift`, its word degree and Coxeter projection formulas
  are in `Harmonic.PositiveDegreeHom`.
- `positiveSimpleLift_mul`, `positive_simple_factors`,
  `positive_fundamental_left_divisor_iff`, and
  `positive_fundamental_right_divisor_iff` are in `Harmonic.PositiveSimpleLiftMul`.
  They require finite indexing and explicit length-additivity/longest-element
  hypotheses as stated, rather than embedding as a premise.
- `positivePrefix_simple_iff` in `Harmonic.PositivePrefix` identifies
  positive left divisibility of reduced lifts with the length-defined
  Coxeter `CoxeterExchange.WeakPrefix`.
- `spherical_positiveToAmbient_injective` and
  `spherical_positive_words_reflect` are in `Harmonic.ProbePositiveWordMonoid`.
- `sphericalPositiveCancelMonoid`, `spherical_positiveToArtin_injective`,
  and `spherical_positive_monoid_fractions` are in
  `Cancellation.SphericalPositiveCancelMonoid`.
- `spherical_positive_cancel_left`, `spherical_positive_head`,
  `spherical_positive_gcd_left`, and `spherical_positive_gcd_right` are in
  `Cancellation.SphericalPositiveCancelLeft`.
- `spherical_positive_common_multiple` and `spherical_positive_lcm_left`
  are in `Harmonic.SphericalPositiveCommonMultiple`. The lcm is supplied by
  an existence statement with its full universal property.

`positive_longest_descent_prefix` in `Harmonic.RestrictionHomRange` requires
`[Fintype S]` for `S : Type*`, a set `J` and a Coxeter element `w` with all
selected simple reflections as left descents. It returns a longest element
`q` of the restricted Coxeter group such that the positive lift of
`restrictionHom M J q` left-divides the positive lift of `w`. This module
also proves the actual restriction-hom range equality, longest descent
factorization and sphericality from a common descent set. It does not
assume the desired Delta lcm or a normalizer conclusion.

The spherical endpoints use `[Fintype S] [LinearOrder S]`, `S : Type`, a
subset `T : Set S` and `hT : IsSpherical M T`. Their positive monoid is on
`restrictedMatrix M T`, not definitionally the parent monoid. The fractions
endpoint omits the ambient linear order. No spherical embedding or
normalizer conclusion is assumed at these endpoints.

`positiveLift_longest_conjugate`, `positiveLift_longest_square_central`,
and `positive_fraction_longest` in `Harmonic.PositiveLiftSimple` give
Delta algebra in the presented group. There is no named monoid Delta-power
cofinality theorem here; deriving one needs the actual embedding and
reflection of the group identities. There is no coprime-tail/ribbon
factorization, complete ribbon presentation or Theorem 5.6 decomposition
in this selected closure.

All endpoints have been compiled against the project pins, but transitive
axiom audit, kernel replay and independent statement/diff acceptance remain
pending. Do not interpret a name or this index as proof acceptance.
