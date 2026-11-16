import Mathlib
import ArtinDeligne


noncomputable def BrinkHowlettGroupoid : (∀ {S W : Type*} [Group W] {M : CoxeterMatrix S} (cs : CoxeterSystem M W) (J : Set S), CategoryTheory.Groupoid { I : Set S // ∃ w : W, Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj w)) (CoxeterSystem.parabolic cs I) = CoxeterSystem.parabolic cs J }) :=
(by
  intro S W inst M cs J
  let roots : Set S → Set (Finsupp S Real) :=
    fun I => Set.image (fun i : S => Finsupp.single i (1 : Real)) I
  exact {
    Hom := fun I K => { w : W //
      Set.image (CoxeterSystem.geometricRepresentation cs w) (roots K.val) = roots I.val }
    id := fun I => ⟨1, by simp⟩
    comp := fun {I K L} x y => ⟨x.val * y.val, by
      calc
        Set.image (CoxeterSystem.geometricRepresentation cs (x.val * y.val)) (roots L.val)
            = Set.image (CoxeterSystem.geometricRepresentation cs x.val)
                (Set.image (CoxeterSystem.geometricRepresentation cs y.val) (roots L.val)) := by
                  simp only [map_mul, mul_apply_eq_comp, Set.image_image]
        _ = roots I.val := by rw [y.property, x.property]⟩
    id_comp := fun x => Subtype.ext (one_mul x.val)
    comp_id := fun x => Subtype.ext (mul_one x.val)
    assoc := fun x y z => Subtype.ext (mul_assoc x.val y.val z.val)
    inv := fun {I K} x => ⟨x.val⁻¹, by
      calc
        Set.image (CoxeterSystem.geometricRepresentation cs x.val⁻¹) (roots I.val)
            = Set.image (CoxeterSystem.geometricRepresentation cs x.val⁻¹)
                (Set.image (CoxeterSystem.geometricRepresentation cs x.val) (roots K.val)) :=
                  congrArg (Set.image (CoxeterSystem.geometricRepresentation cs x.val⁻¹)) x.property.symm
        _ = roots K.val := by
          simp only [Set.image_image, Representation.inv_self_apply, Set.image_id']⟩
    inv_comp := fun x => Subtype.ext (inv_mul_cancel x.val)
    comp_inv := fun x => Subtype.ext (mul_inv_cancel x.val)
  })
