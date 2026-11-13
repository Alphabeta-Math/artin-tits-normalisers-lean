import ArtinRibbons.RibbonRelations
import ArtinRibbons.CofinalRibbons

/-!
# Groupoid-valued universal property of the fixed ribbon lcm relations

Only the chosen pair-lcm words are required to agree in the target. Equality
of arbitrary positive evaluations and the extension to actual signed arrows
are consequences of positive completeness and the proved cofinal loops.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Ribbon2

open CategoryTheory

universe u v

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group]
variable (C : Type u) [Groupoid.{v} C]

/-- Images of objects and all actual outside atomic labels. -/
structure RibbonGeneratorData where
  obj : RibbonObject M → C
  atom : ∀ (X : RibbonObject M) (a : I), a ∉ X.indices →
    (obj X ⟶ obj (atomicNext M X a))

/-- Actual positive fraction data, whose existence is already proved. -/
structure ActualRibbonFraction (X Y : RibbonObject M) (β : Artin.Group M) where
  power : ℕ
  numerator : Artin.Group M
  positive : PositiveReducedArrow M X Y numerator
  value_eq : β = numerator * (cofinalLoop M Y.indices ^ power)⁻¹

noncomputable def chooseRibbonFraction {X Y : RibbonObject M} {β : Artin.Group M}
    (h : ReducedArrow M X Y β) : ActualRibbonFraction M X Y β := by
  let hf := h.positive_fraction M
  exact ⟨Classical.choose hf, Classical.choose (Classical.choose_spec hf),
    (Classical.choose_spec (Classical.choose_spec hf)).1,
    (Classical.choose_spec (Classical.choose_spec hf)).2⟩

/-- The actual generated subgroupoid with its inherited groupoid structure. -/
abbrev ActualReducedRibbonGroupoid := (reducedRibbonSubgroupoid M).objs

/-- Every original object occurs in the actual generated subgroupoid. -/
def actualRibbonObject (X : RibbonObject M) : ActualReducedRibbonGroupoid M :=
  ⟨X, ⟨𝟙 X, ReducedArrow.identity X⟩⟩

/-- An actual generated arrow, with no change of its Artin label. -/
def actualReducedHom {X Y : RibbonObject M} {β : Artin.Group M}
    (h : ReducedArrow M X Y β) : actualRibbonObject M X ⟶ actualRibbonObject M Y :=
  ⟨⟨β, h.isRibbon⟩, h⟩

@[simp] theorem actualReducedHom_comp {X Y Z : RibbonObject M} {β γ : Artin.Group M}
    (hβ : ReducedArrow M X Y β) (hγ : ReducedArrow M Y Z γ) :
    actualReducedHom M (.comp hβ hγ) = actualReducedHom M hβ ≫ actualReducedHom M hγ := rfl

@[simp] theorem actualReducedHom_identity (X : RibbonObject M) :
    actualReducedHom M (.identity X) = 𝟙 (actualRibbonObject M X) := rfl

theorem actualReducedHom_inverse {X Y : RibbonObject M} {β : Artin.Group M}
    (h : ReducedArrow M X Y β) :
    actualReducedHom M (.inverse h) = inv (actualReducedHom M h) := by
  apply IsIso.eq_inv_of_hom_inv_id
  apply Subtype.ext
  apply Subtype.ext
  exact mul_inv_cancel β

/-- The canonical actual arrow for an outside atomic label. -/
noncomputable def actualAtomicHom (X : RibbonObject M) (a : I) (ha : a ∉ X.indices) :
    actualRibbonObject M X ⟶ actualRibbonObject M (atomicNext M X a) :=
  actualReducedHom M (.elementary a ha (elementaryMu_isRibbon M X.indices a))

namespace RibbonGeneratorData

variable {M C} (D : RibbonGeneratorData M C)

/-- Evaluate a composable atomic word in the target groupoid. -/
noncomputable def wordImage {X Y : RibbonObject M} : AtomicWord M X Y → (D.obj X ⟶ D.obj Y)
  | .nil X => 𝟙 (D.obj X)
  | @AtomicWord.cons _ _ _ X Y a ha tail => D.atom X a ha ≫ wordImage tail

@[simp] theorem wordImage_nil (X : RibbonObject M) :
    D.wordImage (AtomicWord.nil X) = 𝟙 (D.obj X) := rfl

@[simp] theorem wordImage_cons {X Y : RibbonObject M} (a : I) (ha : a ∉ X.indices)
    (p : AtomicWord M (atomicNext M X a) Y) :
    D.wordImage (.cons a ha p) = D.atom X a ha ≫ D.wordImage p := rfl

@[simp] theorem wordImage_append {X Y Z : RibbonObject M} (p : AtomicWord M X Y)
    (q : AtomicWord M Y Z) : D.wordImage (p.append q) = D.wordImage p ≫ D.wordImage q := by
  induction p with
  | nil X => simp
  | cons a ha p ih => simp only [AtomicWord.cons_append, wordImage_cons, ih, Category.assoc]

/-- The only primitive relations imposed on a target assignment. -/
def RespectsLcm : Prop :=
  ∀ (X : RibbonObject M) (a b : I) (ha : a ∉ X.indices) (hb : b ∉ X.indices) (hab : a ≠ b),
    D.wordImage (.cons a ha (chosenLcmLeftTail M X a b ha hb hab)) =
      D.wordImage (.cons b hb (chosenLcmRightTail M X a b ha hb hab))

theorem wordImage_eq_of_relation (hD : D.RespectsLcm)
    {X Y : RibbonObject M} {p q : AtomicWord M X Y} (h : AtomicRelation M p q) :
    D.wordImage p = D.wordImage q := by
  induction h with
  | refl p => rfl
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | lcm X a b ha hb hab => exact hD X a b ha hb hab
  | precontext p h ih => simp only [wordImage_append, ih]
  | postcontext h r ih => simp only [wordImage_append, ih]

theorem wordImage_eq_of_eval_eq (hD : D.RespectsLcm)
    {X Y : RibbonObject M} (p q : AtomicWord M X Y) (he : p.eval = q.eval) :
    D.wordImage p = D.wordImage q :=
  D.wordImage_eq_of_relation hD (atomicRelation_of_eval_eq M p q he)

/-- The image of an actual positive generated arrow, using its proved word existence. -/
noncomputable def positiveImage {X Y : RibbonObject M} {p : Artin.Group M}
    (hp : PositiveReducedArrow M X Y p) : D.obj X ⟶ D.obj Y :=
  D.wordImage (hp.atomicWord M)

theorem positiveImage_eq_wordImage (hD : D.RespectsLcm)
    {X Y : RibbonObject M} {p : Artin.Group M} (hp : PositiveReducedArrow M X Y p)
    (w : AtomicWord M X Y) (hw : w.eval = p) : D.positiveImage hp = D.wordImage w :=
  D.wordImage_eq_of_eval_eq hD _ _ ((hp.atomicWord_eval M).trans hw.symm)

theorem positiveImage_congr {X Y : RibbonObject M} {p q : Artin.Group M}
    (hp : PositiveReducedArrow M X Y p) (hq : PositiveReducedArrow M X Y q)
    (he : p = q) : D.positiveImage hp = D.positiveImage hq := by
  cases he
  rfl

@[simp] theorem positiveImage_identity (hD : D.RespectsLcm) (X : RibbonObject M) :
    D.positiveImage (PositiveReducedArrow.identity (M := M) X) = 𝟙 (D.obj X) :=
  D.positiveImage_eq_wordImage hD _ (.nil X) rfl

theorem positiveImage_comp (hD : D.RespectsLcm)
    {X Y Z : RibbonObject M} {p q : Artin.Group M}
    (hp : PositiveReducedArrow M X Y p) (hq : PositiveReducedArrow M Y Z q) :
    D.positiveImage (PositiveReducedArrow.comp hp hq) =
      D.positiveImage hp ≫ D.positiveImage hq := by
  have he : ((hp.atomicWord M).append (hq.atomicWord M)).eval = p * q := by
    rw [AtomicWord.eval_append, hp.atomicWord_eval, hq.atomicWord_eval]
  exact (D.positiveImage_eq_wordImage hD _ _ he).trans (D.wordImage_append _ _)

/-- The image of a concrete denominator loop power. -/
noncomputable def loopImage (X : RibbonObject M) (n : ℕ) : D.obj X ⟶ D.obj X :=
  D.positiveImage (positive_cofinalLoop_pow M X n)

@[simp] theorem loopImage_zero (hD : D.RespectsLcm) (X : RibbonObject M) :
    D.loopImage X 0 = 𝟙 (D.obj X) := by
  exact (D.positiveImage_congr _ (.identity X) (pow_zero _)).trans
    (D.positiveImage_identity hD X)

theorem loopImage_add (hD : D.RespectsLcm) (X : RibbonObject M) (n m : ℕ) :
    D.loopImage X (n + m) = D.loopImage X n ≫ D.loopImage X m := by
  exact (D.positiveImage_congr _
    (.comp (positive_cofinalLoop_pow M X n) (positive_cofinalLoop_pow M X m))
    (pow_add _ n m)).trans (D.positiveImage_comp hD _ _)

theorem positiveImage_loop_naturality (hD : D.RespectsLcm)
    {X Y : RibbonObject M} {p : Artin.Group M}
    (hp : PositiveReducedArrow M X Y p) (n : ℕ) :
    D.positiveImage hp ≫ D.loopImage Y n = D.loopImage X n ≫ D.positiveImage hp := by
  have he := IsRibbon.cofinalLoop_pow_mul M hp.isRibbon n
  have hf := D.positiveImage_congr
    (.comp hp (positive_cofinalLoop_pow M Y n))
    (.comp (positive_cofinalLoop_pow M X n) hp) he
  calc
    _ = D.positiveImage (.comp hp (positive_cofinalLoop_pow M Y n)) :=
      (D.positiveImage_comp hD hp _).symm
    _ = D.positiveImage (.comp (positive_cofinalLoop_pow M X n) hp) := hf
    _ = _ := D.positiveImage_comp hD _ hp

/-- Image of an actual positive numerator divided by a concrete target-loop power. -/
noncomputable def fractionImage {X Y : RibbonObject M} {p : Artin.Group M}
    (hp : PositiveReducedArrow M X Y p) (n : ℕ) : D.obj X ⟶ D.obj Y :=
  D.positiveImage hp ≫ inv (D.loopImage Y n)

theorem fractionImage_expand (hD : D.RespectsLcm)
    {X Y : RibbonObject M} {p : Artin.Group M}
    (hp : PositiveReducedArrow M X Y p) (n m : ℕ) :
    D.fractionImage hp n =
      (D.positiveImage hp ≫ D.loopImage Y m) ≫ inv (D.loopImage Y (n + m)) := by
  simp only [fractionImage, loopImage_add D hD, IsIso.inv_comp, Category.assoc,
    IsIso.hom_inv_id_assoc]

theorem fractionImage_eq (hD : D.RespectsLcm)
    {X Y : RibbonObject M} {p q : Artin.Group M}
    (hp : PositiveReducedArrow M X Y p) (hq : PositiveReducedArrow M X Y q) (n m : ℕ)
    (he : p * (cofinalLoop M Y.indices ^ n)⁻¹ =
      q * (cofinalLoop M Y.indices ^ m)⁻¹) :
    D.fractionImage hp n = D.fractionImage hq m := by
  have hcross : p * cofinalLoop M Y.indices ^ m = q * cofinalLoop M Y.indices ^ n := by
    calc
      _ = (p * (cofinalLoop M Y.indices ^ n)⁻¹) *
          cofinalLoop M Y.indices ^ (n + m) := by rw [pow_add]; group
      _ = (q * (cofinalLoop M Y.indices ^ m)⁻¹) *
          cofinalLoop M Y.indices ^ (m + n) := by rw [he, Nat.add_comm n m]
      _ = _ := by rw [pow_add]; group
  have him := D.positiveImage_congr
    (.comp hp (positive_cofinalLoop_pow M Y m))
    (.comp hq (positive_cofinalLoop_pow M Y n)) hcross
  have him' : D.positiveImage hp ≫ D.loopImage Y m =
      D.positiveImage hq ≫ D.loopImage Y n := by
    calc
      _ = D.positiveImage (.comp hp (positive_cofinalLoop_pow M Y m)) :=
        (D.positiveImage_comp hD hp _).symm
      _ = D.positiveImage (.comp hq (positive_cofinalLoop_pow M Y n)) := him
      _ = _ := D.positiveImage_comp hD hq _
  rw [D.fractionImage_expand hD hp n m, D.fractionImage_expand hD hq m n,
    him', Nat.add_comm m n]

/-- An actual signed generated arrow has an image in the target groupoid. -/
noncomputable def signedImage {X Y : RibbonObject M} {β : Artin.Group M}
    (h : ReducedArrow M X Y β) : D.obj X ⟶ D.obj Y :=
  D.fractionImage (chooseRibbonFraction M h).positive (chooseRibbonFraction M h).power

theorem signedImage_congr {X Y : RibbonObject M} {β γ : Artin.Group M}
    (hβ : ReducedArrow M X Y β) (hγ : ReducedArrow M X Y γ) (he : β = γ) :
    D.signedImage hβ = D.signedImage hγ := by
  cases he
  rfl

theorem signedImage_eq_fraction (hD : D.RespectsLcm)
    {X Y : RibbonObject M} {β p : Artin.Group M} (h : ReducedArrow M X Y β)
    (hp : PositiveReducedArrow M X Y p) (n : ℕ)
    (he : β = p * (cofinalLoop M Y.indices ^ n)⁻¹) :
    D.signedImage h = D.fractionImage hp n :=
  D.fractionImage_eq hD _ hp _ n ((chooseRibbonFraction M h).value_eq.symm.trans he)

theorem signedImage_eq_positive (hD : D.RespectsLcm)
    {X Y : RibbonObject M} {p : Artin.Group M} (h : ReducedArrow M X Y p)
    (hp : PositiveReducedArrow M X Y p) : D.signedImage h = D.positiveImage hp := by
  rw [D.signedImage_eq_fraction hD h hp 0 (by simp)]
  simp only [fractionImage, loopImage_zero D hD, IsIso.inv_id, Category.comp_id]

@[simp] theorem signedImage_identity (hD : D.RespectsLcm) (X : RibbonObject M) :
    D.signedImage (ReducedArrow.identity (M := M) X) = 𝟙 (D.obj X) :=
  (D.signedImage_eq_positive hD _ (.identity X)).trans (D.positiveImage_identity hD X)

theorem positiveImage_loop_inverse_naturality (hD : D.RespectsLcm)
    {X Y : RibbonObject M} {p : Artin.Group M}
    (hp : PositiveReducedArrow M X Y p) (n : ℕ) :
    inv (D.loopImage X n) ≫ D.positiveImage hp =
      D.positiveImage hp ≫ inv (D.loopImage Y n) := by
  apply (IsIso.inv_comp_eq (D.loopImage X n)).mpr
  calc
    D.positiveImage hp = (D.positiveImage hp ≫ D.loopImage Y n) ≫ inv (D.loopImage Y n) := by simp
    _ = (D.loopImage X n ≫ D.positiveImage hp) ≫ inv (D.loopImage Y n) := by
      rw [D.positiveImage_loop_naturality hD hp n]
    _ = _ := Category.assoc _ _ _

theorem signedImage_comp (hD : D.RespectsLcm)
    {X Y Z : RibbonObject M} {β γ : Artin.Group M}
    (hβ : ReducedArrow M X Y β) (hγ : ReducedArrow M Y Z γ) :
    D.signedImage (.comp hβ hγ) = D.signedImage hβ ≫ D.signedImage hγ := by
  let f := chooseRibbonFraction M hβ
  let g := chooseRibbonFraction M hγ
  have hmove : (cofinalLoop M Y.indices ^ f.power)⁻¹ * g.numerator =
      g.numerator * (cofinalLoop M Z.indices ^ f.power)⁻¹ := by
    have hn := IsRibbon.cofinalLoop_pow_mul M g.positive.isRibbon f.power
    calc
      _ = (cofinalLoop M Y.indices ^ f.power)⁻¹ *
          (g.numerator * cofinalLoop M Z.indices ^ f.power) *
            (cofinalLoop M Z.indices ^ f.power)⁻¹ := by group
      _ = (cofinalLoop M Y.indices ^ f.power)⁻¹ *
          (cofinalLoop M Y.indices ^ f.power * g.numerator) *
            (cofinalLoop M Z.indices ^ f.power)⁻¹ := by rw [hn]
      _ = _ := by group
  have he : β * γ = (f.numerator * g.numerator) *
      (cofinalLoop M Z.indices ^ (g.power + f.power))⁻¹ := by
    calc
      β * γ = (f.numerator * (cofinalLoop M Y.indices ^ f.power)⁻¹) *
          (g.numerator * (cofinalLoop M Z.indices ^ g.power)⁻¹) :=
        congrArg₂ (· * ·) f.value_eq g.value_eq
      _ = f.numerator * ((cofinalLoop M Y.indices ^ f.power)⁻¹ * g.numerator) *
          (cofinalLoop M Z.indices ^ g.power)⁻¹ := by group
      _ = f.numerator * (g.numerator * (cofinalLoop M Z.indices ^ f.power)⁻¹) *
          (cofinalLoop M Z.indices ^ g.power)⁻¹ := by rw [hmove]
      _ = _ := by simp only [pow_add, mul_inv_rev, mul_assoc]
  rw [D.signedImage_eq_fraction hD (.comp hβ hγ) (.comp f.positive g.positive) _ he,
    D.signedImage_eq_fraction hD hβ f.positive _ f.value_eq,
    D.signedImage_eq_fraction hD hγ g.positive _ g.value_eq]
  unfold fractionImage
  rw [D.positiveImage_comp hD f.positive g.positive]
  simp only [loopImage_add D hD, IsIso.inv_comp]
  have hi := congrArg
    (fun t => D.positiveImage f.positive ≫ t ≫ inv (D.loopImage Z g.power))
    (D.positiveImage_loop_inverse_naturality hD g.positive f.power)
  simpa only [Category.assoc] using hi.symm

theorem signedImage_inverse (hD : D.RespectsLcm)
    {X Y : RibbonObject M} {β : Artin.Group M} (h : ReducedArrow M X Y β) :
    D.signedImage (.inverse h) = inv (D.signedImage h) := by
  apply IsIso.eq_inv_of_hom_inv_id
  rw [← D.signedImage_comp hD h (.inverse h)]
  exact (D.signedImage_congr _ (.identity X) (mul_inv_cancel β)).trans
    (D.signedImage_identity hD X)

/-- The genuine functor on the actual reduced ribbon subgroupoid. -/
noncomputable def extensionFunctor (hD : D.RespectsLcm) : ActualReducedRibbonGroupoid M ⥤ C where
  obj X := D.obj X.val
  map f := D.signedImage f.property
  map_id X := D.signedImage_identity hD X.val
  map_comp f g := D.signedImage_comp hD f.property g.property

theorem extensionFunctor_positive (hD : D.RespectsLcm)
    {X Y : RibbonObject M} {p : Artin.Group M} (hp : PositiveReducedArrow M X Y p) :
    (D.extensionFunctor hD).map (actualReducedHom M hp.toReducedArrow) = D.positiveImage hp :=
  D.signedImage_eq_positive hD hp.toReducedArrow hp

theorem extensionFunctor_word (hD : D.RespectsLcm)
    {X Y : RibbonObject M} (p : AtomicWord M X Y) :
    (D.extensionFunctor hD).map (actualReducedHom M p.toPositiveReducedArrow.toReducedArrow) =
      D.wordImage p :=
  (D.extensionFunctor_positive hD p.toPositiveReducedArrow).trans
    (D.positiveImage_eq_wordImage hD _ p rfl)

/-- Every assigned atomic image is the image of its actual generated arrow. -/
theorem extensionFunctor_atom (hD : D.RespectsLcm)
    (X : RibbonObject M) (a : I) (ha : a ∉ X.indices) :
    (D.extensionFunctor hD).map (actualAtomicHom M X a ha) = D.atom X a ha := by
  have hp : PositiveReducedArrow M X (atomicNext M X a) (elementaryMu M X.indices a) :=
    .elementary a ha (elementaryMu_isRibbon M X.indices a)
  change D.signedImage hp.toReducedArrow = _
  rw [D.signedImage_eq_positive hD hp.toReducedArrow hp,
    D.positiveImage_eq_wordImage hD hp (.cons a ha (.nil _)) (by simp)]
  simp

/-- Uniqueness is among genuine functors on the actual subgroupoid. Object
maps are specified literally; heterogeneous generator equalities only account
for the supplied equality of object functions. -/
theorem extensionFunctor_unique (hD : D.RespectsLcm)
    (F : ActualReducedRibbonGroupoid M ⥤ C)
    (hobj : F.obj = fun X => D.obj X.val)
    (hatom : ∀ (X : RibbonObject M) (a : I) (ha : a ∉ X.indices),
      HEq (F.map (actualAtomicHom M X a ha)) (D.atom X a ha)) :
    F = D.extensionFunctor hD := by
  cases F with
  | mk fobj fmap fid fcomp =>
    dsimp only at hobj
    subst fobj
    let F : ActualReducedRibbonGroupoid M ⥤ C :=
      { obj := fun X => D.obj X.val
        map := fmap
        map_id := fid
        map_comp := fcomp }
    change F = D.extensionFunctor hD
    have hatom' (X : RibbonObject M) (a : I) (ha : a ∉ X.indices) :
        F.map (actualAtomicHom M X a ha) = D.atom X a ha := eq_of_heq (hatom X a ha)
    have hword : ∀ {X Y : RibbonObject M} (p : AtomicWord M X Y),
        F.map (actualReducedHom M p.toPositiveReducedArrow.toReducedArrow) = D.wordImage p := by
      intro X Y p
      induction p with
      | nil X => exact F.map_id (actualRibbonObject M X)
      | @cons X Y a ha p ih =>
        change F.map (actualAtomicHom M X a ha ≫
          actualReducedHom M p.toPositiveReducedArrow.toReducedArrow) = _
        rw [F.map_comp, hatom', ih, D.wordImage_cons]
        rfl
    have hpositive : ∀ {X Y : RibbonObject M} {p : Artin.Group M}
        (hp : PositiveReducedArrow M X Y p),
        F.map (actualReducedHom M hp.toReducedArrow) = D.positiveImage hp := by
      intro X Y p hp
      let w := hp.atomicWord M
      have he : actualReducedHom M hp.toReducedArrow =
          actualReducedHom M w.toPositiveReducedArrow.toReducedArrow := by
        apply Subtype.ext
        apply Subtype.ext
        exact (hp.atomicWord_eval M).symm
      rw [he]
      exact hword w
    apply CategoryTheory.Functor.hext (F := F) (G := D.extensionFunctor hD) (fun _ => rfl)
    intro X Y f
    apply heq_of_eq
    rcases X with ⟨X, hX⟩
    rcases Y with ⟨Y, hY⟩
    change actualRibbonObject M X ⟶ actualRibbonObject M Y at f
    let h : ReducedArrow M X Y f.val.val := f.property
    let a := chooseRibbonFraction M h
    have hhom : f = actualReducedHom M a.positive.toReducedArrow ≫
        inv (actualReducedHom M (positive_cofinalLoop_pow M Y a.power).toReducedArrow) := by
      rw [← actualReducedHom_inverse, ← actualReducedHom_comp]
      apply Subtype.ext
      apply Subtype.ext
      exact a.value_eq
    change F.map f = D.signedImage h
    conv_lhs => rw [hhom, F.map_comp, F.map_inv]
    simp only [hpositive a.positive, hpositive (positive_cofinalLoop_pow M Y a.power)]
    rfl

/-- The fixed chosen pair-lcm relations present the actual generated
groupoid in the universal groupoid-valued sense. -/
theorem exists_unique_extension (hD : D.RespectsLcm) :
    ∃! F : ActualReducedRibbonGroupoid M ⥤ C,
      F.obj = (fun X => D.obj X.val) ∧
      ∀ (X : RibbonObject M) (a : I) (ha : a ∉ X.indices),
        HEq (F.map (actualAtomicHom M X a ha)) (D.atom X a ha) := by
  refine ⟨D.extensionFunctor hD, ⟨rfl, ?_⟩, ?_⟩
  · intro X a ha
    exact heq_of_eq (D.extensionFunctor_atom hD X a ha)
  · intro F hF
    exact D.extensionFunctor_unique hD F hF.1 hF.2

end RibbonGeneratorData

end ArtinNormalisers.Ribbon2
