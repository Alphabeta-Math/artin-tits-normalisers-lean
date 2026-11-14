module

public import ArtinDeligneVendor.Topology.Realization.SimplexFaceGluing
public import Mathlib.Topology.Maps.Proper.Basic

/-! Arbitrary-parameter boundary-track gluing along the genuine finite simplex
face cover. Properness establishes the required product quotient property. -/

@[expose] public section
set_option autoImplicit false

namespace ArtinNormalisers.Deligne5

open Convexity Topology
open scoped unitInterval

universe u v

/-- The finite compact face cover remains a genuine quotient after product
with an arbitrary parameter space. Properness, not an unrestricted claim
about products of quotient maps, proves this assertion. -/
theorem isQuotientMap_parameterized_simplexFaceCylinderCover
    (X : Type u) [TopologicalSpace X] (d : ℕ) :
    IsQuotientMap (Prod.map (id : X → X) (StdSimplex.simplexFaceCylinderCover d)) := by
  have hp := (isProperMap_id (X := X)).prodMap (StdSimplex.simplexFaceCylinderCover d).continuous.isProperMap
  exact hp.isClosedMap.isQuotientMap hp.continuous
    (Function.surjective_id.prodMap (StdSimplex.simplexFaceCylinderCover_surjective d))

/-- Actual face tracks glue continuously with their whole arbitrary parameter
and time coordinates, under equality on geometric overlaps. -/
theorem exists_parameterized_simplex_boundary_track
    {X : Type u} {Z : Type v} [TopologicalSpace X] [TopologicalSpace Z] (d : ℕ)
    (H : Fin (d + 2) → C(X × (StdSimplex ℝ (Fin (d + 1)) × I), Z))
    (hcompat : ∀ (i j : Fin (d + 2)) (p : X)
      (x y : StdSimplex ℝ (Fin (d + 1))) (t : I),
      x.map i.succAbove = y.map j.succAbove → H i (p, (x, t)) = H j (p, (y, t))) :
    ∃ B : C(X × (StdSimplex.boundary (d + 1) × I), Z),
      ∀ (i : Fin (d + 2)) (p : X) (x : StdSimplex ℝ (Fin (d + 1))) (t : I),
        B (p, (StdSimplex.simplexBoundaryFace d i x, t)) = H i (p, (x, t)) := by
  let G₀ : C(Fin (d + 2) × (X × (StdSimplex ℝ (Fin (d + 1)) × I)), Z) :=
    ⟨fun p ↦ H p.1 p.2, continuous_prod_of_discrete_left.mpr (fun i ↦ (H i).continuous)⟩
  let G : C(X × (Fin (d + 2) × (StdSimplex ℝ (Fin (d + 1)) × I)), Z) :=
    G₀.comp ⟨fun p ↦ (p.2.1, (p.1, p.2.2)), by fun_prop⟩
  let q : C(X × (Fin (d + 2) × (StdSimplex ℝ (Fin (d + 1)) × I)),
      X × (StdSimplex.boundary (d + 1) × I)) :=
    ⟨Prod.map id (StdSimplex.simplexFaceCylinderCover d),
      continuous_id.prodMap (StdSimplex.simplexFaceCylinderCover d).continuous⟩
  have hG : Function.FactorsThrough G q := by
    rintro ⟨p, i, x, t⟩ ⟨r, j, y, s⟩ h
    have hpr : p = r := congrArg Prod.fst h
    subst r
    have hts : t = s := congrArg (fun z ↦ z.2.2) h
    subst s
    exact hcompat i j p x y t (congrArg (fun z ↦ z.2.1.val) h)
  let hq : IsQuotientMap q := isQuotientMap_parameterized_simplexFaceCylinderCover X d
  let B := hq.lift G hG
  refine ⟨B, fun i p x t ↦ ?_⟩
  exact ContinuousMap.congr_fun (hq.lift_comp G hG) (p, i, x, t)


/-- The same genuine gluing theorem in the conventional homotopy product
parenthesization. No restriction is imposed on the parameter space. -/
theorem exists_parameterized_simplex_boundary_track_assoc
    {X : Type u} {Z : Type v} [TopologicalSpace X] [TopologicalSpace Z] (d : ℕ)
    (H : Fin (d + 2) → C((X × StdSimplex ℝ (Fin (d + 1))) × I, Z))
    (hcompat : ∀ (i j : Fin (d + 2)) (p : X)
      (x y : StdSimplex ℝ (Fin (d + 1))) (t : I),
      x.map i.succAbove = y.map j.succAbove → H i ((p, x), t) = H j ((p, y), t)) :
    ∃ B : C((X × StdSimplex.boundary (d + 1)) × I, Z),
      ∀ (i : Fin (d + 2)) (p : X) (x : StdSimplex ℝ (Fin (d + 1))) (t : I),
        B ((p, StdSimplex.simplexBoundaryFace d i x), t) = H i ((p, x), t) := by
  let H' : Fin (d + 2) → C(X × (StdSimplex ℝ (Fin (d + 1)) × I), Z) :=
    fun i => ⟨fun p => H i ((p.1, p.2.1), p.2.2), by fun_prop⟩
  obtain ⟨B, hB⟩ := exists_parameterized_simplex_boundary_track d H' hcompat
  refine ⟨⟨fun p => B (p.1.1, (p.1.2, p.2)), by fun_prop⟩, ?_⟩
  exact hB

end ArtinNormalisers.Deligne5
