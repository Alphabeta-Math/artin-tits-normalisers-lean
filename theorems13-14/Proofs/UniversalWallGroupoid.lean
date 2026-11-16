import Mathlib
import ArtinDeligne
import Proofs.ChamberLabelling
import Proofs.AdjacentWallFormula

set_option maxHeartbeats 2000000

noncomputable def UniversalWallGroupoid : (∀ {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S), CategoryTheory.Groupoid { p : W × Set S // Set.image (fun u : W => u * p.1) (CoxeterSystem.parabolic cs J : Set W) = Set.image (fun u : W => p.1 * u) (CoxeterSystem.parabolic cs p.2 : Set W) ∧ CoxeterSystem.IsMinimalCosetRep cs p.2 p.1 }) :=
(fun {S W} _inst {M} cs J => {
  Hom := fun A B => { w : W // w = A.val.1⁻¹ * B.val.1 }
  id := fun A => ⟨1, (inv_mul_cancel A.val.1).symm⟩
  comp := fun {A B C} f g => ⟨f.val * g.val, by
    rw [f.property, g.property]
    simp only [mul_assoc, mul_inv_cancel_left]⟩
  id_comp := fun f => Subtype.ext (one_mul f.val)
  comp_id := fun f => Subtype.ext (mul_one f.val)
  assoc := fun f g h => Subtype.ext (mul_assoc f.val g.val h.val)
  inv := fun {A B} f => ⟨f.val⁻¹, by
    rw [f.property, mul_inv_rev, inv_inv]⟩
  inv_comp := fun f => Subtype.ext (inv_mul_cancel f.val)
  comp_inv := fun f => Subtype.ext (mul_inv_cancel f.val)
})
