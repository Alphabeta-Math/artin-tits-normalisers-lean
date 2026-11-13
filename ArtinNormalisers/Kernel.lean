module

public import ArtinNormalisers.QuotientMap

set_option autoImplicit false

@[expose] public section

namespace ArtinNormalisers

variable {G H : Type*} [Group G] [Group H]

/-- A kernel coset has a representative in the kernel of the original map. -/
theorem quotientMap_mem_ker_iff (f : G →* H) (A : Subgroup G)
    (x : (Subgroup.normalizer (A : Set G)) ⧸ A.subgroupOf (Subgroup.normalizer (A : Set G))) :
    x ∈ (quotientMap f A).ker ↔
      ∃ n : (Subgroup.normalizer (A : Set G)), QuotientGroup.mk' (A.subgroupOf (Subgroup.normalizer (A : Set G))) n = x ∧
        f (n : G) = 1 := by
  constructor
  · intro hx
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (A.subgroupOf (Subgroup.normalizer (A : Set G))) x
    have hg : f (g : G) ∈ A.map f := by
      apply (QuotientGroup.eq_one_iff
        (N := (A.map f).subgroupOf (Subgroup.normalizer (A.map f : Set H)))
        (normalizerMap f A g)).mp
      exact hx
    obtain ⟨a, ha, hfa⟩ := Subgroup.mem_map.mp hg
    let aN : (Subgroup.normalizer (A : Set G)) := ⟨a, A.le_normalizer ha⟩
    have haC : aN ∈ A.subgroupOf (Subgroup.normalizer (A : Set G)) := ha
    have hqa : QuotientGroup.mk' (A.subgroupOf (Subgroup.normalizer (A : Set G))) aN = 1 :=
      (QuotientGroup.eq_one_iff aN).mpr haC
    refine ⟨g * aN⁻¹, ?_, ?_⟩
    · rw [map_mul, map_inv, hqa, inv_one, mul_one]
    · change f ((g : G) * a⁻¹) = 1
      rw [map_mul, map_inv, hfa, mul_inv_cancel]
  · rintro ⟨n, rfl, hn⟩
    change quotientMap f A (QuotientGroup.mk' (A.subgroupOf (Subgroup.normalizer (A : Set G))) n) = 1
    rw [quotientMap_mk]
    apply (QuotientGroup.eq_one_iff (normalizerMap f A n)).mpr
    change f (n : G) ∈ A.map f
    rw [hn]
    exact (A.map f).one_mem

/-- The kernel is the quotient image of the original kernel inside the normalizer. -/
theorem kernel_eq_image (f : G →* H) (A : Subgroup G) :
    (quotientMap f A).ker =
      (f.ker.subgroupOf (Subgroup.normalizer (A : Set G))).map
        (QuotientGroup.mk' (A.subgroupOf (Subgroup.normalizer (A : Set G)))) := by
  ext x
  rw [quotientMap_mem_ker_iff, Subgroup.mem_map]
  constructor
  · rintro ⟨n, hq, hn⟩
    exact ⟨n, hn, hq⟩
  · rintro ⟨n, hn, hq⟩
    exact ⟨n, hq, hn⟩

/-- Send the ambient intersection of kernel and normalizer into the normalizer quotient. -/
def articleKernelMap (f : G →* H) (A : Subgroup G) :
    ↥(f.ker ⊓ (Subgroup.normalizer (A : Set G))) →*
      (Subgroup.normalizer (A : Set G)) ⧸ A.subgroupOf (Subgroup.normalizer (A : Set G)) :=
  (QuotientGroup.mk' (A.subgroupOf (Subgroup.normalizer (A : Set G)))).comp
    { toFun := fun n => ⟨n, n.property.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

/-- The article's image `q ((ker f) ∩ N_G(A))`, with the ambient intersection explicit. -/
def articleKernelImage (f : G →* H) (A : Subgroup G) :
    Subgroup ((Subgroup.normalizer (A : Set G)) ⧸ A.subgroupOf (Subgroup.normalizer (A : Set G))) :=
  (articleKernelMap f A).range

/-- The ambient-intersection image agrees with the image of the subgroup in the normalizer. -/
theorem articleKernelImage_eq (f : G →* H) (A : Subgroup G) :
    articleKernelImage f A =
      (f.ker.subgroupOf (Subgroup.normalizer (A : Set G))).map
        (QuotientGroup.mk' (A.subgroupOf (Subgroup.normalizer (A : Set G)))) := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    exact Subgroup.mem_map.mpr ⟨⟨n, n.property.2⟩, n.property.1, rfl⟩
  · intro hx
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
    exact ⟨⟨n, hn, n.property⟩, rfl⟩

/-- The kernel in the article's ambient-intersection notation. -/
theorem kernel_eq_articleKernelImage (f : G →* H) (A : Subgroup G) :
    (quotientMap f A).ker = articleKernelImage f A := by
  rw [articleKernelImage_eq, kernel_eq_image]

end ArtinNormalisers
