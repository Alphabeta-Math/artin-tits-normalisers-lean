import ArtinNormalisers.Artin.Basic
import OAI.Topology.ArtinGroups.DeligneDefinitions
import OAI.Topology.ArtinGroups.Coxeter.AltList

/-! # The canonical bridge between the two actual Artin presentations -/

namespace ArtinNormalisers.Ribbon2


variable {I : Type*}

/-- Starting at the first index agrees with mathlib's ending convention after
swapping the two indices exactly in odd length. No word reversal is applied
to group multiplication. -/
theorem altList_eq_alternatingWord (i j : I) (n : ℕ) :
    OAI.HarmonicArtin.CoxeterExchange.altList i j n = if Even n then CoxeterSystem.alternatingWord i j n
      else CoxeterSystem.alternatingWord j i n := by
  induction n generalizing i j with
  | zero => simp [OAI.HarmonicArtin.CoxeterExchange.altList, CoxeterSystem.alternatingWord]
  | succ n ih =>
    rw [OAI.HarmonicArtin.CoxeterExchange.altList_succ, ih]
    by_cases hn : Even n <;>
      simp [Nat.even_add_one, hn, CoxeterSystem.alternatingWord_succ']

/-- Evaluation of OAI's free alternating word; proved locally to avoid
importing the unrelated fusion development with the upstream helper. -/
theorem alternating_lift_prod {G : Type*} [Group G] (f : I → G) (i j : I) (n : ℕ) :
    FreeGroup.lift f (OAI.HarmonicArtin.alternating i j n) = ((OAI.HarmonicArtin.CoxeterExchange.altList i j n).map f).prod := by
  induction n generalizing i j with
  | zero => simp [OAI.HarmonicArtin.alternating, OAI.HarmonicArtin.CoxeterExchange.altList]
  | succ n ih =>
    simp only [OAI.HarmonicArtin.alternating, map_mul, FreeGroup.lift_apply_of, OAI.HarmonicArtin.CoxeterExchange.altList_succ,
      List.map_cons, List.prod_cons, ih]

private theorem alternating_eq_prod (i j : I) (n : ℕ) :
    OAI.HarmonicArtin.alternating i j n = ((OAI.HarmonicArtin.CoxeterExchange.altList i j n).map FreeGroup.of).prod := by
  induction n generalizing i j with
  | zero => rfl
  | succ n ih => simp only [OAI.HarmonicArtin.alternating, OAI.HarmonicArtin.CoxeterExchange.altList_succ, List.map_cons, List.prod_cons, ih]

private theorem relator_eq (M : CoxeterMatrix I) (i j : I) :
    OAI.HarmonicArtin.alternating i j (M i j) * (OAI.HarmonicArtin.alternating j i (M i j))⁻¹ =
      if Even (M i j) then TauCeti.artinRelation M i j else TauCeti.artinRelation M j i := by
  simp only [alternating_eq_prod, altList_eq_alternatingWord,
    TauCeti.artinRelation, CoxeterSystem.braidWord, M.symmetric j i]
  split <;> rfl

/-- The two presentations have exactly the same relator set. Odd matrix
entries exchange the ordered pair, and even entries keep it. -/
theorem braidRelators_eq (M : CoxeterMatrix I) :
    OAI.HarmonicArtin.braidRelators M = TauCeti.artinRelationsSet M := by
  apply Set.Subset.antisymm
  · rintro r ⟨⟨i, j⟩, rfl⟩
    change OAI.HarmonicArtin.alternating i j (M i j) * (OAI.HarmonicArtin.alternating j i (M i j))⁻¹ ∈ _
    rw [relator_eq]
    split
    · exact TauCeti.artinRelation_mem_artinRelationsSet M i j
    · exact TauCeti.artinRelation_mem_artinRelationsSet M j i
  · rintro r ⟨⟨i, j⟩, rfl⟩
    by_cases hm : Even (M i j)
    · refine ⟨(i, j), ?_⟩
      change OAI.HarmonicArtin.alternating i j (M i j) * (OAI.HarmonicArtin.alternating j i (M i j))⁻¹ =
        TauCeti.artinRelation M i j
      rw [relator_eq, ite_eq_left hm]
    · refine ⟨(j, i), ?_⟩
      change OAI.HarmonicArtin.alternating j i (M j i) * (OAI.HarmonicArtin.alternating i j (M j i))⁻¹ =
        TauCeti.artinRelation M i j
      rw [relator_eq]
      simp only [M.symmetric j i, hm, ite_false]

private theorem lift_of_eq_mk (rels : Set (FreeGroup I)) :
    FreeGroup.lift (PresentedGroup.of : I → PresentedGroup rels) = PresentedGroup.mk rels := by
  apply FreeGroup.ext_hom
  intro i
  rfl

private theorem toParent_relations (M : CoxeterMatrix I) (r : FreeGroup I)
    (hr : r ∈ OAI.HarmonicArtin.braidRelators M) : FreeGroup.lift (Artin.generator M) r = 1 := by
  rw [braidRelators_eq M] at hr
  change FreeGroup.lift (PresentedGroup.of : I → PresentedGroup _) r = 1
  rw [lift_of_eq_mk]
  exact PresentedGroup.one_of_mem hr

private theorem fromParent_relations (M : CoxeterMatrix I) (r : FreeGroup I)
    (hr : r ∈ TauCeti.artinRelationsSet M) : FreeGroup.lift (OAI.HarmonicArtin.generator M) r = 1 := by
  rw [← braidRelators_eq M] at hr
  change FreeGroup.lift (PresentedGroup.of : I → PresentedGroup _) r = 1
  rw [lift_of_eq_mk]
  exact PresentedGroup.one_of_mem hr

def toParent (M : CoxeterMatrix I) : OAI.HarmonicArtin.Artin M →* Artin.Group M :=
  PresentedGroup.toGroup (toParent_relations M)

def fromParent (M : CoxeterMatrix I) : Artin.Group M →* OAI.HarmonicArtin.Artin M :=
  PresentedGroup.toGroup (fromParent_relations M)

@[simp] theorem toParent_generator (M : CoxeterMatrix I) (i : I) :
    toParent M (OAI.HarmonicArtin.generator M i) = Artin.generator M i := PresentedGroup.toGroup.of _

@[simp] theorem fromParent_generator (M : CoxeterMatrix I) (i : I) :
    fromParent M (Artin.generator M i) = OAI.HarmonicArtin.generator M i := PresentedGroup.toGroup.of _

/-- The canonical equivalence sends every standard generator to the same
standard generator. Its inverse is another proved presentation homomorphism. -/
def presentationEquiv (M : CoxeterMatrix I) : OAI.HarmonicArtin.Artin M ≃* Artin.Group M :=
  MonoidHom.toMulEquiv (toParent M) (fromParent M)
    (by
      apply PresentedGroup.ext
      intro i
      change fromParent M (toParent M (OAI.HarmonicArtin.generator M i)) = OAI.HarmonicArtin.generator M i
      simp)
    (by
      apply PresentedGroup.ext
      intro i
      change toParent M (fromParent M (Artin.generator M i)) = Artin.generator M i
      simp)

@[simp] theorem presentationEquiv_generator (M : CoxeterMatrix I) (i : I) :
    presentationEquiv M (OAI.HarmonicArtin.generator M i) = Artin.generator M i := toParent_generator M i

@[simp] theorem presentationEquiv_symm_generator (M : CoxeterMatrix I) (i : I) :
    (presentationEquiv M).symm (Artin.generator M i) = OAI.HarmonicArtin.generator M i := fromParent_generator M i

@[simp] theorem presentationEquiv_word (M : CoxeterMatrix I) (w : List I) :
    presentationEquiv M (OAI.HarmonicArtin.wordArtin M w) = Artin.wordProd M w := by
  simp [OAI.HarmonicArtin.wordArtin, Artin.wordProd, map_list_prod, List.map_map, Function.comp_def]

theorem presentationEquiv_parabolic (M : CoxeterMatrix I) (J : Set I) :
    (OAI.HarmonicArtin.artinParabolic M J).map (presentationEquiv M).toMonoidHom =
      Artin.parabolic M J := by
  rw [OAI.HarmonicArtin.artinParabolic, MonoidHom.map_closure, Artin.parabolic, Set.image_image]
  congr 1

private theorem coxeter_relations (M : CoxeterMatrix I) (r : FreeGroup I)
    (hr : r ∈ OAI.HarmonicArtin.braidRelators M) : FreeGroup.lift M.simple r = 1 := by
  have he : FreeGroup.lift M.simple =
      (Artin.projection M).comp (PresentedGroup.mk (TauCeti.artinRelationsSet M)) := by
    apply FreeGroup.ext_hom
    intro i
    exact (Artin.projection_generator M i).symm
  rw [he, MonoidHom.comp_apply]
  rw [braidRelators_eq M] at hr
  rw [PresentedGroup.one_of_mem hr, map_one]

/-- The actual Coxeter projection from the OAI presentation, constructed
directly without importing the large upstream `ArtinCoxeter` closure. -/
def oaiProjection (M : CoxeterMatrix I) : OAI.HarmonicArtin.Artin M →* M.Group :=
  PresentedGroup.toGroup (coxeter_relations M)

@[simp] theorem oaiProjection_generator (M : CoxeterMatrix I) (i : I) :
    oaiProjection M (OAI.HarmonicArtin.generator M i) = M.simple i := PresentedGroup.toGroup.of _

theorem projection_presentationEquiv (M : CoxeterMatrix I) :
    (Artin.projection M).comp (presentationEquiv M).toMonoidHom = oaiProjection M := by
  apply PresentedGroup.ext
  intro i
  change Artin.projection M (presentationEquiv M (OAI.HarmonicArtin.generator M i)) = oaiProjection M (OAI.HarmonicArtin.generator M i)
  simp

end ArtinNormalisers.Ribbon2
