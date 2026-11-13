module

public import ArtinNormalisers.Artin.NormalizerLift
public import ArtinNormalisers.Kernel

/-!
# The full algebraic normalizer exact sequence

The groups here are the canonical presentation-defined Artin and Coxeter
groups. For an arbitrary set of indices, the actual Artin--Coxeter projection
induces a surjection on the normalizer quotients. Its kernel is the image of
the intersection of the pure Artin group with the Artin normalizer. In
particular the first arrow is the inclusion of this image subgroup.
-/

@[expose] public section

namespace ArtinNormalisers

variable {G H : Type*} [_root_.Group G] [_root_.Group H]

abbrev normalizerQuotientOf (A : Subgroup G) :=
  (Subgroup.normalizer (A : Set G)) ⧸
    A.subgroupOf (Subgroup.normalizer (A : Set G))

/-- Transport the standard induced map along the proved equality of its
image subgroup with a specified target subgroup. -/
def quotientMapTo (f : G →* H) (A : Subgroup G) (B : Subgroup H)
    (h : A.map f = B) : normalizerQuotientOf A →* normalizerQuotientOf B := by
  subst B
  exact quotientMap f A

theorem quotientMapTo_mk (f : G →* H) (A : Subgroup G) (B : Subgroup H)
    (h : A.map f = B) (n : Subgroup.normalizer (A : Set G)) :
    quotientMapTo f A B h
        (QuotientGroup.mk' (A.subgroupOf (Subgroup.normalizer (A : Set G))) n) =
      QuotientGroup.mk' (B.subgroupOf (Subgroup.normalizer (B : Set H)))
        ⟨f n, by rw [← h]; exact (normalizerMap f A n).property⟩ := by
  subst B
  rfl

theorem quotientMapTo_kernel (f : G →* H) (A : Subgroup G)
    (B : Subgroup H) (h : A.map f = B) :
    (quotientMapTo f A B h).ker = articleKernelImage f A := by
  subst B
  exact kernel_eq_articleKernelImage f A

namespace Artin

variable {I : Type*} (M : CoxeterMatrix I) (J : Set I)

/-- The normalizer of the actual standard Artin parabolic, modulo that
parabolic subgroup. -/
abbrev normalizerQuotient := normalizerQuotientOf (parabolic M J)

/-- The normalizer of the actual standard Coxeter parabolic, modulo that
parabolic subgroup. -/
abbrev coxeterNormalizerQuotient := normalizerQuotientOf (coxeterParabolic M J)

/-- The homomorphism induced by the canonical Artin--Coxeter projection.
The target is the quotient by the Coxeter parabolic itself, using the proved
equality `map_parabolic` rather than an assumed image identification. -/
def normalizerQuotientMap : normalizerQuotient M J →* coxeterNormalizerQuotient M J :=
  quotientMapTo (projection M) (parabolic M J) (coxeterParabolic M J)
    (map_parabolic M J)

/-- The induced map sends an Artin normalizer representative to its Coxeter
projection. -/
@[simp]
theorem normalizerQuotientMap_mk
    (n : Subgroup.normalizer (parabolic M J : Set (Group M))) :
    normalizerQuotientMap M J
        (QuotientGroup.mk'
          ((parabolic M J).subgroupOf (Subgroup.normalizer (parabolic M J : Set (Group M)))) n) =
      QuotientGroup.mk'
        ((coxeterParabolic M J).subgroupOf
          (Subgroup.normalizer (coxeterParabolic M J : Set M.Group)))
        ⟨projection M n, by
          rw [← map_parabolic M J]
          exact (normalizerMap (projection M) (parabolic M J) n).property⟩ :=
  quotientMapTo_mk (projection M) (parabolic M J) (coxeterParabolic M J)
    (map_parabolic M J) n

/-- The article's `N(P,J)`: the quotient image of the ambient intersection
`pure M ⊓ normalizer (parabolic M J)`. -/
def pureNormalizerImage : Subgroup (normalizerQuotient M J) :=
  articleKernelImage (projection M) (parabolic M J)

/-- Explicitly identify the source with the image of the ambient pure
intersection under the quotient projection. -/
theorem pureNormalizerImage_eq_range :
    pureNormalizerImage M J =
      (articleKernelMap (projection M) (parabolic M J)).range := rfl

/-- The first arrow of the sequence is inclusion of the image subgroup. -/
def pureNormalizerInclusion : pureNormalizerImage M J →* normalizerQuotient M J :=
  (pureNormalizerImage M J).subtype

theorem pureNormalizerInclusion_injective :
    Function.Injective (pureNormalizerInclusion M J) :=
  (pureNormalizerImage M J).subtype_injective

/-- Exactness at the Artin normalizer quotient. -/
theorem normalizerQuotientMap_kernel :
    (normalizerQuotientMap M J).ker = pureNormalizerImage M J :=
  quotientMapTo_kernel (projection M) (parabolic M J) (coxeterParabolic M J)
    (map_parabolic M J)

theorem pureNormalizerInclusion_range :
    (pureNormalizerInclusion M J).range = (normalizerQuotientMap M J).ker := by
  rw [normalizerQuotientMap_kernel]
  exact (pureNormalizerImage M J).range_subtype

/-- Terminal surjectivity follows from the proved lift of every Coxeter
normalizer element to the actual Artin normalizer. -/
theorem normalizerQuotientMap_surjective :
    Function.Surjective (normalizerQuotientMap M J) := by
  intro x
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective
    ((coxeterParabolic M J).subgroupOf
      (Subgroup.normalizer (coxeterParabolic M J : Set M.Group))) x
  obtain ⟨a, ha, hpa⟩ := exists_normalizer_lift M J w.property
  refine ⟨QuotientGroup.mk'
    ((parabolic M J).subgroupOf
      (Subgroup.normalizer (parabolic M J : Set (Group M)))) ⟨a, ha⟩, ?_⟩
  rw [normalizerQuotientMap_mk]
  congr 1
  exact Subtype.ext hpa

/-- **Lemma 2.8, algebraic form.** For every Coxeter matrix and every set of
indices, the canonical projection gives the short exact sequence
`1 → N(P,J) → N_A(A_J)/A_J → N_W(W_J)/W_J → 1`.
Here short exactness means injectivity of the subgroup inclusion, equality of
its range with the kernel, and surjectivity of the quotient homomorphism.
There are no finiteness, sphericality, or normalizer-surjectivity premises. -/
theorem lemma_2_8 :
    Function.Injective (pureNormalizerInclusion M J) ∧
      (pureNormalizerInclusion M J).range = (normalizerQuotientMap M J).ker ∧
        Function.Surjective (normalizerQuotientMap M J) :=
  ⟨pureNormalizerInclusion_injective M J, pureNormalizerInclusion_range M J,
    normalizerQuotientMap_surjective M J⟩

end Artin
end ArtinNormalisers
