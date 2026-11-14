module

public import ArtinAsphericity.FlatCoordinates
public import ArtinAsphericity.ConvexCover
public import ArtinHomotopyVendor.Topology.LocalEquiconnection
public import Mathlib.Topology.Metrizable.Uniformity

/-!
# A metric and a genuine local connector on the original complement

The compatible metric uses the existing complementary simple-root coordinates.
The connector domain consists of pairs in a common member of the finite open
sign-cell cover. Its connector is literal straight interpolation in the actual
ambient relative flat. This supplies local geometry, not asphericity.
-/

set_option maxHeartbeats 400000

@[expose] public section

namespace ArtinNormalisers.Homotopy5

open Theorem18 Chamber3 Asphericity5 Topology TopologicalSpace

variable {I : Type*}

/-- Metrizability of the original subspace topology, including zero-dimensional flats. -/
theorem complementMetrizableSpace (M : CoxeterMatrix I) [Finite M.Group] (J : Set I) :
    MetrizableSpace (Complement M J) := by
  let : Finite I := finite_index M
  let : MetrizableSpace (relativeSubspace J) :=
    (flatComplementCoordinates J).toHomeomorph.isEmbedding.metrizableSpace
  change MetrizableSpace ↥(complementSet M J)
  infer_instance

/-- A chosen metric compatible with the already specified original topology. -/
@[instance_reducible]
noncomputable def complementMetricSpace (M : CoxeterMatrix I) [Finite M.Group] (J : Set I) :
    MetricSpace (Complement M J) := by
  letI := complementMetrizableSpace M J
  exact TopologicalSpace.metrizableSpaceMetric (Complement M J)

/-- This choice of metric retains, definitionally, the actual complement topology. -/
theorem complementMetricSpace_topology (M : CoxeterMatrix I) [Finite M.Group] (J : Set I) :
    (complementMetricSpace M J).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace (Complement M J)) := rfl

/-- Pairs sharing a genuine convex sign-cell cover member. -/
noncomputable def actualConnectorDomain (M : CoxeterMatrix I) (J : Set I) :
    Set (Complement M J × Complement M J) :=
  ⋃ σ : RelativeRoot M J → Fin 4,
    actualConvexCoverSet M J σ ×ˢ actualConvexCoverSet M J σ

theorem isOpen_actualConnectorDomain (M : CoxeterMatrix I) [Finite M.Group] (J : Set I) :
    IsOpen (actualConnectorDomain M J) :=
  isOpen_iUnion fun σ =>
    (isOpen_actualConvexCoverSet M J σ).prod (isOpen_actualConvexCoverSet M J σ)

theorem diagonal_mem_actualConnectorDomain (M : CoxeterMatrix I) (J : Set I)
    (x : Complement M J) : (x, x) ∈ actualConnectorDomain M J := by
  obtain ⟨σ, hσ⟩ := exists_mem_actualConvexCoverSet M J x
  exact Set.mem_iUnion.mpr ⟨σ, hσ, hσ⟩

section Generic

variable {E H : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [ContinuousAdd E] [ContinuousSMul ℝ E]

/-- Pairs in one convex cell of a generic linear-form complement. -/
def convexConnectorDomain (ℓ : H → E →L[ℝ] ℝ) :
    Set (ComplexComplement ℓ × ComplexComplement ℓ) :=
  ⋃ σ : H → Fin 4, convexCoverSet ℓ σ ×ˢ convexCoverSet ℓ σ

/-- Straight interpolation on its genuine shared-cell domain. -/
def convexConnector (ℓ : H → E →L[ℝ] ℝ) :
    C(convexConnectorDomain ℓ × unitInterval, ComplexComplement ℓ) where
  toFun z := ⟨(1 - (z.2 : ℝ)) • z.1.val.1.val + (z.2 : ℝ) • z.1.val.2.val, by
    obtain ⟨σ, hx, hy⟩ := Set.mem_iUnion.mp z.1.property
    exact convexCell_subset_complexComplementSet ℓ σ
      (convex_convexCell ℓ σ hx hy (sub_nonneg.mpr z.2.property.2)
        z.2.property.1 (sub_add_cancel 1 (z.2 : ℝ)))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop

/-- The local geometry is proved for actual linear-form complements. -/
def convexLocalEquiconnection [Finite H] (ℓ : H → E →L[ℝ] ℝ) :
    LocalEquiconnection (ComplexComplement ℓ) where
  domain := convexConnectorDomain ℓ
  isOpen_domain := isOpen_iUnion fun σ =>
    (isOpen_convexCoverSet ℓ σ).prod (isOpen_convexCoverSet ℓ σ)
  diagonal_mem x := by
    obtain ⟨σ, hx⟩ := exists_mem_convexCoverSet ℓ x
    exact Set.mem_iUnion.mpr ⟨σ, hx, hx⟩
  connector := convexConnector ℓ
  connector_zero p := by apply Subtype.ext; simp [convexConnector]
  connector_one p := by apply Subtype.ext; simp [convexConnector]
  connector_diagonal x t := by
    apply Subtype.ext
    change (1 - (t : ℝ)) • x.val + (t : ℝ) • x.val = x.val
    rw [← add_smul, sub_add_cancel, one_smul]

@[simp]
theorem convexLocalEquiconnection_connector_val [Finite H] (ℓ : H → E →L[ℝ] ℝ)
    (p : (convexLocalEquiconnection ℓ).domain) (t : unitInterval) :
    ((convexLocalEquiconnection ℓ).connector (p, t)).val =
      (1 - (t : ℝ)) • p.val.1.val + (t : ℝ) • p.val.2.val := rfl

theorem convexCover_isConnectorConvex [Finite H] (ℓ : H → E →L[ℝ] ℝ)
    (σ : H → Fin 4) : (convexLocalEquiconnection ℓ).IsConvex (convexCoverSet ℓ σ) where
  pair_mem {_x _y} hx hy := Set.mem_iUnion.mpr ⟨σ, hx, hy⟩
  connector_mem {_x _y} hx hy t :=
    convex_convexCell ℓ σ hx hy (sub_nonneg.mpr t.property.2)
      t.property.1 (sub_add_cancel 1 (t : ℝ))

end Generic

section Transport

variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]

/-- Transport genuine local connector data through an actual homeomorphism. -/
def pullbackLocalEquiconnection (h : A ≃ₜ B) (F : LocalEquiconnection B) :
    LocalEquiconnection A where
  domain := (fun p : A × A => (h p.1, h p.2)) ⁻¹' F.domain
  isOpen_domain := F.isOpen_domain.preimage
    ((h.continuous.comp continuous_fst).prodMk (h.continuous.comp continuous_snd))
  diagonal_mem x := F.diagonal_mem (h x)
  connector :=
    { toFun := fun z => h.symm (F.connector (⟨(h z.1.val.1, h z.1.val.2), z.1.property⟩, z.2))
      continuous_toFun := by fun_prop }
  connector_zero p := by simp [F.connector_zero]
  connector_one p := by simp [F.connector_one]
  connector_diagonal x t := by simp [F.connector_diagonal]

theorem isConvex_pullbackLocalEquiconnection (h : A ≃ₜ B)
    (F : LocalEquiconnection B) {V : Set B} (hV : F.IsConvex V) :
    (pullbackLocalEquiconnection h F).IsConvex (h ⁻¹' V) where
  pair_mem {_x _y} hx hy := hV.pair_mem hx hy
  connector_mem {_x _y} hx hy t := by
    change h (h.symm (F.connector (⟨_, hV.pair_mem hx hy⟩, t))) ∈ V
    rw [h.apply_symm_apply]
    exact hV.connector_mem hx hy t

end Transport

/-- Genuine local equiconnection on the original complement, transported through
its already proved coordinate-identity homeomorphism. -/
noncomputable def actualLocalEquiconnection (M : CoxeterMatrix I) [Finite M.Group]
    (J : Set I) : LocalEquiconnection (Complement M J) :=
  pullbackLocalEquiconnection (actualComplementHomeomorph M J)
    (convexLocalEquiconnection (E := relativeSubspace J) (actualForms M J))

/-- Its domain is precisely the original shared-sign-cell domain. -/
theorem actualLocalEquiconnection_domain (M : CoxeterMatrix I) [Finite M.Group]
    (J : Set I) : (actualLocalEquiconnection M J).domain = actualConnectorDomain M J := by
  ext p
  simp only [actualLocalEquiconnection, pullbackLocalEquiconnection, convexLocalEquiconnection,
    convexConnectorDomain, actualConnectorDomain, actualConvexCoverSet,
    Set.mem_preimage, Set.mem_iUnion, Set.mem_prod]

/-- Every actual finite open cover member is convex for the actual connector. -/
theorem actualConvexCover_isConnectorConvex (M : CoxeterMatrix I) [Finite M.Group]
    (J : Set I) (σ : RelativeRoot M J → Fin 4) :
    (actualLocalEquiconnection M J).IsConvex (actualConvexCoverSet M J σ) := by
  change (pullbackLocalEquiconnection (actualComplementHomeomorph M J)
    (convexLocalEquiconnection (E := relativeSubspace J) (actualForms M J))).IsConvex
      ((actualComplementHomeomorph M J) ⁻¹'
        convexCoverSet (E := relativeSubspace J) (actualForms M J) σ)
  exact isConvex_pullbackLocalEquiconnection (actualComplementHomeomorph M J)
    (convexLocalEquiconnection (E := relativeSubspace J) (actualForms M J))
    (convexCover_isConnectorConvex (E := relativeSubspace J) (actualForms M J) σ)

/-- The transported connector has exactly the original ambient straight-line values. -/
theorem actualLocalEquiconnection_connector_val (M : CoxeterMatrix I) [Finite M.Group]
    (J : Set I) (p : (actualLocalEquiconnection M J).domain) (t : unitInterval) :
    ((actualLocalEquiconnection M J).connector (p, t)).val =
      (1 - (t : ℝ)) • p.val.1.val + (t : ℝ) • p.val.2.val := by
  have hi (z : ComplexComplement (E := relativeSubspace J) (actualForms M J)) :
      ((actualComplementHomeomorph M J).symm z).val = z.val := by
    simpa only [Homeomorph.apply_symm_apply] using
      (actualComplementHomeomorph_val M J ((actualComplementHomeomorph M J).symm z)).symm
  change ((actualComplementHomeomorph M J).symm _).val = _
  rw [hi]
  rw [convexLocalEquiconnection_connector_val, actualComplementHomeomorph_val,
    actualComplementHomeomorph_val]

end ArtinNormalisers.Homotopy5
