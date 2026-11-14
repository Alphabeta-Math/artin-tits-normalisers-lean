import ArtinDeligne

/-! Literal endpoint guards: no comparison, asphericity or contractibility
premises are permitted in these examples. The source is reviewed and frozen
with the scientific inventory; these are checks, not new assumptions. -/
set_option autoImplicit false

open ArtinNormalisers ArtinNormalisers.Theorem18 ArtinNormalisers.Deligne5

noncomputable section

universe u
variable {I : Type u} (M : CoxeterMatrix I) [Finite M.Group] (J : Set I)

example : C(Asphericity5.ComplementUniversalCover M J,
    GarsideWeights M (⟨J⟩ : Ribbon2.RibbonObject M)) := actualGarsideForward M J
example : ((actualGarsideReturn M J).comp (actualGarsideForward M J)).Homotopy
    (ContinuousMap.id (Asphericity5.ComplementUniversalCover M J)) :=
  actualUniversalCoverComparisonHomotopy M J
example (q : Asphericity5.ComplementUniversalCover M J) :
    TauCeti.IsAspherical (Asphericity5.ComplementUniversalCover M J) q :=
  actualUniversalCover_isAspherical M J q
example (x : Complement M J) : TauCeti.IsAspherical (Complement M J) x :=
  actualComplement_isAspherical M J x
example (y : OrbitSpace M J) : TauCeti.IsAspherical (OrbitSpace M J) y :=
  actualOrbit_isAspherical M J y
example (x : Complement M J) : TauCeti.IsEilenbergMacLaneSpaceOne
    (Artin.pureNormalizerImage M J) (Complement M J) x := actualComplement_isKpi1 M J x
example (y : OrbitSpace M J) : TauCeti.IsEilenbergMacLaneSpaceOne
    (Artin.normalizerQuotient M J) (OrbitSpace M J) y := corollary_6_14 M J y
example (x : Complement M J) : actualNormalizerDiagrams M J x ∧
    TauCeti.IsEilenbergMacLaneSpaceOne (Artin.pureNormalizerImage M J) (Complement M J) x ∧
    TauCeti.IsEilenbergMacLaneSpaceOne (Artin.normalizerQuotient M J)
      (OrbitSpace M J) (orbitProjection M J x) := theorem_1_8 M J x
#check ArtinNormalisers.Deligne5.theorem_1_8_all_basepoints
#print ArtinNormalisers.Deligne5.actualUniversalCoverComparisonHomotopy
#print ArtinNormalisers.Deligne5.actualUniversalCover_isAspherical
#print ArtinNormalisers.Deligne5.theorem_1_8
#print ArtinNormalisers.Deligne5.theorem_1_8_all_basepoints
