import ArtinRibbons.NormalizerSplitting

/-!
# The canonical Coxeter projection on actual reduced ribbon loops

The map is obtained by projecting the actual Artin labels to the actual
Coxeter normalizer and then taking its actual parabolic quotient. The
normalizer identification intertwines it with the already proved algebraic
quotient projection. No geometric monodromy comparison is assumed here.
-/

namespace ArtinNormalisers.Ribbon2

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group]

/-- Project actual reduced ribbon labels to the actual Coxeter normalizer. -/
def reducedRibbonCoxeterNormalizerMap (X : RibbonObject M) :
    reducedRibbonLoops M X →*
      Subgroup.normalizer (Artin.coxeterParabolic M X.indices : Set M.Group) where
  toFun r := ⟨Artin.projection M r.val, by
    rw [← Artin.map_parabolic M X.indices]
    exact (normalizerMap (Artin.projection M) (Artin.parabolic M X.indices)
      (reducedRibbonLoopsToNormalizer M X r)).property⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' r s := Subtype.ext (map_mul _ r.val s.val)

@[simp] theorem reducedRibbonCoxeterNormalizerMap_value (X : RibbonObject M)
    (r : reducedRibbonLoops M X) :
    (reducedRibbonCoxeterNormalizerMap M X r : M.Group) = Artin.projection M r.val := rfl

/-- The normalizer-quotient class of the actual Coxeter projection of a ribbon. -/
def reducedRibbonCoxeterProjection (X : RibbonObject M) :
    reducedRibbonLoops M X →* Artin.coxeterNormalizerQuotient M X.indices :=
  (QuotientGroup.mk' ((Artin.coxeterParabolic M X.indices).subgroupOf
    (Subgroup.normalizer (Artin.coxeterParabolic M X.indices : Set M.Group)))).comp
      (reducedRibbonCoxeterNormalizerMap M X)

/-- The canonical normalizer isomorphism preserves the original Coxeter
projection, with identity on the same Coxeter normalizer quotient. -/
theorem reducedRibbon_projection_compatible (X : RibbonObject M) :
    (Artin.normalizerQuotientMap M X.indices).comp
        (reducedRibbonNormalizerQuotientEquiv M X).toMonoidHom =
      reducedRibbonCoxeterProjection M X := by
  ext r
  change Artin.normalizerQuotientMap M X.indices
      (QuotientGroup.mk' ((Artin.parabolic M X.indices).subgroupOf
        (Subgroup.normalizer (Artin.parabolic M X.indices : Set (Artin.Group M))))
        (reducedRibbonLoopsToNormalizer M X r)) = _
  rw [Artin.normalizerQuotientMap_mk]
  rfl

end ArtinNormalisers.Ribbon2
