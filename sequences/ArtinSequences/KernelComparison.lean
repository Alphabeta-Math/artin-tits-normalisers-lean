module

public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Comparing the kernels in a compatible middle-group equivalence

An actual multiplicative equivalence commuting with maps to the same target
identifies their kernels. If an injective homomorphism realizes the second
kernel as its range, this gives an equivalence from the first kernel to its
domain, with the actual inclusion square. The subgroup variant transports
an explicitly proved equality with the first kernel.

All four type universes are independent. There are no finiteness or terminal
surjectivity assumptions. These generic algebraic hypotheses are intended
to be instantiated with the actual projection and covering maps; they do
not assume a fundamental-group comparison for an arrangement.
-/

set_option autoImplicit false

@[expose] public section

namespace ArtinNormalisers.Sequence4

universe uA uB uH uQ

variable {A : Type uA} {B : Type uB} {H : Type uH} {Q : Type uQ}
  [Group A] [Group B] [Group H] [MulOneClass Q]

/-- A compatible actual middle equivalence maps the first kernel exactly
onto the second kernel. -/
theorem map_kernel_of_compatible (E : A ≃* B) (ρA : A →* Q) (ρB : B →* Q)
    (hcomm : ρB.comp E.toMonoidHom = ρA) :
    ρA.ker.map E.toMonoidHom = ρB.ker := by
  ext b
  constructor
  · rintro ⟨a, ha, rfl⟩
    change ρA a = 1 at ha
    change ρB (E a) = 1
    exact (congrArg (fun f : A →* Q => f a) hcomm).trans ha
  · intro hb
    change ρB b = 1 at hb
    refine ⟨E.symm b, ?_, E.apply_symm_apply b⟩
    change ρA (E.symm b) = 1
    have hc := congrArg (fun f : A →* Q => f (E.symm b)) hcomm
    change ρB (E (E.symm b)) = ρA (E.symm b) at hc
    rw [E.apply_symm_apply] at hc
    exact hc.symm.trans hb

/-- Restrict the actual middle equivalence, using the proved kernel image. -/
def kernelEquivOfCompatible (E : A ≃* B) (ρA : A →* Q) (ρB : B →* Q)
    (hcomm : ρB.comp E.toMonoidHom = ρA) : ρA.ker ≃* ρB.ker :=
  (E.subgroupMap ρA.ker).trans
    (MulEquiv.subgroupCongr (map_kernel_of_compatible E ρA ρB hcomm))

@[simp]
theorem kernelEquivOfCompatible_apply (E : A ≃* B) (ρA : A →* Q) (ρB : B →* Q)
    (hcomm : ρB.comp E.toMonoidHom = ρA) (a : ρA.ker) :
    (kernelEquivOfCompatible E ρA ρB hcomm a : B) = E a := rfl

/-- An injective homomorphism with the proved kernel range is equivalent
to that kernel. Its inverse is constructed by mathlib's range equivalence. -/
noncomputable def rangeEquivKernel (ρB : B →* Q) (j : H →* B)
    (hj : Function.Injective j) (hrange : j.range = ρB.ker) : H ≃* ρB.ker :=
  (MonoidHom.ofInjective hj).trans (MulEquiv.subgroupCongr hrange)

@[simp]
theorem rangeEquivKernel_apply (ρB : B →* Q) (j : H →* B)
    (hj : Function.Injective j) (hrange : j.range = ρB.ker) (h : H) :
    (rangeEquivKernel ρB j hj hrange h : B) = j h := rfl

/-- The first kernel is canonically compared to the domain of the actual
injective homomorphism realizing the second kernel. -/
noncomputable def kernelComparison (E : A ≃* B) (ρA : A →* Q) (ρB : B →* Q)
    (hcomm : ρB.comp E.toMonoidHom = ρA) (j : H →* B)
    (hj : Function.Injective j) (hrange : j.range = ρB.ker) : ρA.ker ≃* H :=
  (kernelEquivOfCompatible E ρA ρB hcomm).trans (rangeEquivKernel ρB j hj hrange).symm

/-- The comparison square holds on the actual ambient group elements. -/
theorem kernelComparison_apply (E : A ≃* B) (ρA : A →* Q) (ρB : B →* Q)
    (hcomm : ρB.comp E.toMonoidHom = ρA) (j : H →* B)
    (hj : Function.Injective j) (hrange : j.range = ρB.ker) (a : ρA.ker) :
    j (kernelComparison E ρA ρB hcomm j hj hrange a) = E a := by
  let F := rangeEquivKernel ρB j hj hrange
  let b := kernelEquivOfCompatible E ρA ρB hcomm a
  calc
    j (kernelComparison E ρA ρB hcomm j hj hrange a) = (F (F.symm b) : B) := rfl
    _ = (b : B) := congrArg Subtype.val (F.apply_symm_apply b)
    _ = E a := rfl

theorem kernelComparison_square (E : A ≃* B) (ρA : A →* Q) (ρB : B →* Q)
    (hcomm : ρB.comp E.toMonoidHom = ρA) (j : H →* B)
    (hj : Function.Injective j) (hrange : j.range = ρB.ker) :
    j.comp (kernelComparison E ρA ρB hcomm j hj hrange).toMonoidHom =
      E.toMonoidHom.comp ρA.ker.subtype := by
  apply MonoidHom.ext
  intro a
  exact kernelComparison_apply E ρA ρB hcomm j hj hrange a

theorem kernelComparison_symm_apply (E : A ≃* B) (ρA : A →* Q) (ρB : B →* Q)
    (hcomm : ρB.comp E.toMonoidHom = ρA) (j : H →* B)
    (hj : Function.Injective j) (hrange : j.range = ρB.ker) (h : H) :
    ((kernelComparison E ρA ρB hcomm j hj hrange).symm h : A) = E.symm (j h) := by
  apply E.injective
  rw [E.apply_symm_apply]
  have he := kernelComparison_apply E ρA ρB hcomm j hj hrange
    ((kernelComparison E ρA ρB hcomm j hj hrange).symm h)
  rw [MulEquiv.apply_symm_apply] at he
  exact he.symm

/-- Transport through an actual subgroup equality, suitable for a pure
normalizer image that has already been proved equal to the first kernel. -/
noncomputable def subgroupKernelComparison (E : A ≃* B) (ρA : A →* Q) (ρB : B →* Q)
    (hcomm : ρB.comp E.toMonoidHom = ρA) (j : H →* B)
    (hj : Function.Injective j) (hrange : j.range = ρB.ker)
    (K : Subgroup A) (hK : K = ρA.ker) : K ≃* H :=
  (MulEquiv.subgroupCongr hK).trans (kernelComparison E ρA ρB hcomm j hj hrange)

theorem subgroupKernelComparison_apply (E : A ≃* B) (ρA : A →* Q) (ρB : B →* Q)
    (hcomm : ρB.comp E.toMonoidHom = ρA) (j : H →* B)
    (hj : Function.Injective j) (hrange : j.range = ρB.ker)
    (K : Subgroup A) (hK : K = ρA.ker) (a : K) :
    j (subgroupKernelComparison E ρA ρB hcomm j hj hrange K hK a) = E a :=
  kernelComparison_apply E ρA ρB hcomm j hj hrange (MulEquiv.subgroupCongr hK a)

theorem subgroupKernelComparison_square (E : A ≃* B) (ρA : A →* Q) (ρB : B →* Q)
    (hcomm : ρB.comp E.toMonoidHom = ρA) (j : H →* B)
    (hj : Function.Injective j) (hrange : j.range = ρB.ker)
    (K : Subgroup A) (hK : K = ρA.ker) :
    j.comp (subgroupKernelComparison E ρA ρB hcomm j hj hrange K hK).toMonoidHom =
      E.toMonoidHom.comp K.subtype := by
  apply MonoidHom.ext
  intro a
  exact subgroupKernelComparison_apply E ρA ρB hcomm j hj hrange K hK a

theorem subgroupKernelComparison_symm_apply (E : A ≃* B) (ρA : A →* Q) (ρB : B →* Q)
    (hcomm : ρB.comp E.toMonoidHom = ρA) (j : H →* B)
    (hj : Function.Injective j) (hrange : j.range = ρB.ker)
    (K : Subgroup A) (hK : K = ρA.ker) (h : H) :
    ((subgroupKernelComparison E ρA ρB hcomm j hj hrange K hK).symm h : A) =
      E.symm (j h) :=
  kernelComparison_symm_apply E ρA ρB hcomm j hj hrange h

/-- The commuting inclusion square uniquely determines the comparison,
so no unspecified automorphism of the pure term remains. -/
theorem subgroupKernelComparison_unique (E : A ≃* B) (ρA : A →* Q) (ρB : B →* Q)
    (hcomm : ρB.comp E.toMonoidHom = ρA) (j : H →* B)
    (hj : Function.Injective j) (hrange : j.range = ρB.ker)
    (K : Subgroup A) (hK : K = ρA.ker) (F : K ≃* H)
    (hF : j.comp F.toMonoidHom = E.toMonoidHom.comp K.subtype) :
    F = subgroupKernelComparison E ρA ρB hcomm j hj hrange K hK := by
  apply MulEquiv.ext
  intro a
  apply hj
  exact (congrArg (fun f : K →* B => f a) hF).trans
    (subgroupKernelComparison_apply E ρA ρB hcomm j hj hrange K hK a).symm

end ArtinNormalisers.Sequence4
