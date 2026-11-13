module

public import ArtinNormalisers.NormalizerMap

set_option autoImplicit false

@[expose] public section

namespace ArtinNormalisers

variable {G H : Type*} [Group G] [Group H]

/-- The induced homomorphism on normalizers modulo the original subgroups. -/
def quotientMap (f : G →* H) (A : Subgroup G) :
    (Subgroup.normalizer (A : Set G)) ⧸ A.subgroupOf (Subgroup.normalizer (A : Set G)) →*
      (Subgroup.normalizer (A.map f : Set H)) ⧸ (A.map f).subgroupOf (Subgroup.normalizer (A.map f : Set H)) :=
  QuotientGroup.map _ _ (normalizerMap f A) (normalizerMap_maps_subgroup f A)

/-- Evaluation of the induced map on any chosen representative. -/
@[simp]
theorem quotientMap_mk (f : G →* H) (A : Subgroup G) (n : (Subgroup.normalizer (A : Set G))) :
    quotientMap f A (QuotientGroup.mk' (A.subgroupOf (Subgroup.normalizer (A : Set G))) n) =
      QuotientGroup.mk' ((A.map f).subgroupOf (Subgroup.normalizer (A.map f : Set H)))
        (normalizerMap f A n) := rfl

end ArtinNormalisers
