module

public import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit false

@[expose] public section

namespace ArtinNormalisers

variable {G H : Type*} [Group G] [Group H]

/-- Restrict a homomorphism to the normalizer of a subgroup and its image. -/
def normalizerMap (f : G →* H) (A : Subgroup G) :
    (Subgroup.normalizer (A : Set G)) →* (Subgroup.normalizer (A.map f : Set H)) where
  toFun n := ⟨f n, A.le_normalizer_map f (Subgroup.mem_map.mpr ⟨n, n.property, rfl⟩)⟩
  map_one' := Subtype.ext (f.map_one)
  map_mul' x y := Subtype.ext (f.map_mul x y)

@[simp]
theorem normalizerMap_apply (f : G →* H) (A : Subgroup G) (n : (Subgroup.normalizer (A : Set G))) :
    (normalizerMap f A n : H) = f n := rfl

/-- The subgroup embedded in its normalizer maps into the image subgroup. -/
theorem normalizerMap_maps_subgroup (f : G →* H) (A : Subgroup G) :
    A.subgroupOf (Subgroup.normalizer (A : Set G)) ≤
      ((A.map f).subgroupOf (Subgroup.normalizer (A.map f : Set H))).comap (normalizerMap f A) := by
  intro n hn
  exact Subgroup.mem_map.mpr ⟨n, hn, rfl⟩

end ArtinNormalisers
