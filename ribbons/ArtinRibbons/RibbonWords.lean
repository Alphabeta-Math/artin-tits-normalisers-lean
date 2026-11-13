import ArtinRibbons.PositiveRibbons

/-!
# Concrete positive atomic ribbon words

These are finite composable paths of actual outside elementary ribbons.
Every step has the canonical endpoint proved in `Fundamental`; evaluation
is multiplication of the actual Artin labels, in traversal order.
-/

set_option autoImplicit false

namespace ArtinNormalisers.Ribbon2

variable {I : Type*} (M : CoxeterMatrix I) [Finite M.Group]

/-- The proved endpoint of an elementary step from `X`. -/
noncomputable def atomicNext (X : RibbonObject M) (a : I) : RibbonObject M :=
  ⟨parabolicTwistImage M (insert a X.indices) X.indices⟩

/-- A Type-valued composable word, retaining every outside atomic label. -/
inductive AtomicWord : RibbonObject M → RibbonObject M → Type _
  | nil (X) : AtomicWord X X
  | cons {X Y} (a : I) (ha : a ∉ X.indices)
      (tail : AtomicWord (atomicNext M X a) Y) : AtomicWord X Y

namespace AtomicWord

variable {M}

/-- Actual Artin evaluation, with the first traversed label on the left. -/
noncomputable def eval {X Y : RibbonObject M} : AtomicWord M X Y → Artin.Group M
  | .nil _ => 1
  | .cons a _ tail => elementaryMu M X.indices a * tail.eval

@[simp] theorem eval_nil (X : RibbonObject M) : (nil X : AtomicWord M X X).eval = 1 := rfl

@[simp] theorem eval_cons {X Y : RibbonObject M} (a : I) (ha : a ∉ X.indices)
    (tail : AtomicWord M (atomicNext M X a) Y) :
    (cons a ha tail).eval = elementaryMu M X.indices a * tail.eval := rfl

/-- Concatenate composable atomic paths. -/
noncomputable def append {X Y Z : RibbonObject M} :
    AtomicWord M X Y → AtomicWord M Y Z → AtomicWord M X Z
  | .nil _, q => q
  | .cons a ha p, q => .cons a ha (p.append q)

@[simp] theorem nil_append {X Y : RibbonObject M} (p : AtomicWord M X Y) :
    (nil X).append p = p := rfl

@[simp] theorem cons_append {X Y Z : RibbonObject M} (a : I) (ha : a ∉ X.indices)
    (p : AtomicWord M (atomicNext M X a) Y) (q : AtomicWord M Y Z) :
    (cons a ha p).append q = cons a ha (p.append q) := rfl

@[simp] theorem append_nil {X Y : RibbonObject M} (p : AtomicWord M X Y) :
    p.append (nil Y) = p := by
  induction p with
  | nil X => rfl
  | cons a ha p ih => exact congrArg (cons a ha) ih

theorem append_assoc {X Y Z T : RibbonObject M} (p : AtomicWord M X Y)
    (q : AtomicWord M Y Z) (r : AtomicWord M Z T) :
    (p.append q).append r = p.append (q.append r) := by
  induction p with
  | nil X => rfl
  | cons a ha p ih => exact congrArg (cons a ha) (ih q)

@[simp] theorem eval_append {X Y Z : RibbonObject M} (p : AtomicWord M X Y)
    (q : AtomicWord M Y Z) : (p.append q).eval = p.eval * q.eval := by
  induction p with
  | nil X => exact (one_mul _).symm
  | cons a ha p ih => simp only [cons_append, eval_cons, ih, mul_assoc]

/-- Number of atomic steps; this is separate from the Artin exponent sum. -/
noncomputable def length {X Y : RibbonObject M} : AtomicWord M X Y → ℕ
  | .nil _ => 0
  | .cons _ _ tail => tail.length + 1

@[simp] theorem length_nil (X : RibbonObject M) : (nil X : AtomicWord M X X).length = 0 := rfl

@[simp] theorem length_cons {X Y : RibbonObject M} (a : I) (ha : a ∉ X.indices)
    (tail : AtomicWord M (atomicNext M X a) Y) :
    (cons a ha tail).length = tail.length + 1 := rfl

@[simp] theorem length_append {X Y Z : RibbonObject M} (p : AtomicWord M X Y)
    (q : AtomicWord M Y Z) : (p.append q).length = p.length + q.length := by
  induction p with
  | nil X => exact (Nat.zero_add _).symm
  | cons a ha p ih => simp only [cons_append, length_cons, ih]; omega

theorem toPositiveReducedArrow {X Y : RibbonObject M} (p : AtomicWord M X Y) :
    PositiveReducedArrow M X Y p.eval := by
  induction p with
  | nil X => exact .identity X
  | @cons X Y a ha p ih =>
    exact .comp (.elementary a ha (elementaryMu_isRibbon M X.indices a)) ih

theorem positive {X Y : RibbonObject M} (p : AtomicWord M X Y) :
    p.eval ∈ actualPositiveParabolic M Set.univ := p.toPositiveReducedArrow.positive

theorem isRibbon {X Y : RibbonObject M} (p : AtomicWord M X Y) :
    IsRibbon M X Y p.eval := p.toPositiveReducedArrow.isRibbon

theorem leftReduced {X Y : RibbonObject M} (p : AtomicWord M X Y) :
    IsLeftParabolicallyReduced M X.indices p.eval := p.toPositiveReducedArrow.leftReduced

theorem degree_nonneg {X Y : RibbonObject M} (p : AtomicWord M X Y) :
    0 ≤ degree M p.eval := degree_nonneg_of_mem_actualPositiveParabolic M Set.univ p.positive

theorem degree_tail_lt {X Y : RibbonObject M} (a : I) (ha : a ∉ X.indices)
    (p : AtomicWord M (atomicNext M X a) Y) :
    (degree M p.eval).toNat < (degree M (cons a ha p).eval).toNat := by
  have hp := p.degree_nonneg
  have hμ := elementaryMu_degree_pos M X.indices a ha
  rw [eval_cons, degree_mul]
  omega

theorem cons_eval_ne_one {X Y : RibbonObject M} (a : I) (ha : a ∉ X.indices)
    (p : AtomicWord M (atomicNext M X a) Y) : (cons a ha p).eval ≠ 1 := by
  intro he
  have hd := congrArg (degree M) he
  have hμ := elementaryMu_degree_pos M X.indices a ha
  have hp := p.degree_nonneg
  rw [eval_cons, degree_mul, degree_one] at hd
  omega

end AtomicWord

theorem positiveReducedArrow_iff_exists_atomicWord {X Y : RibbonObject M} {r : Artin.Group M} :
    PositiveReducedArrow M X Y r ↔ ∃ p : AtomicWord M X Y, p.eval = r := by
  constructor
  · intro h
    induction h with
    | identity X => exact ⟨.nil X, rfl⟩
    | @elementary X Y a ha hr =>
      have hY : Y = atomicNext M X a :=
        congrArg (fun J : Set I => (⟨J⟩ : RibbonObject M))
          (isRibbon_target_indices_unique M hr (elementaryMu_isRibbon M X.indices a))
      subst Y
      exact ⟨.cons a ha (.nil _), by simp⟩
    | comp hβ hγ ihβ ihγ =>
      obtain ⟨p, hp⟩ := ihβ
      obtain ⟨q, hq⟩ := ihγ
      exact ⟨p.append q, by rw [AtomicWord.eval_append, hp, hq]⟩
  · rintro ⟨p, rfl⟩
    exact p.toPositiveReducedArrow

/-- Select a concrete word only after proving actual positive generation. -/
noncomputable def PositiveReducedArrow.atomicWord {X Y : RibbonObject M} {r : Artin.Group M}
    (h : PositiveReducedArrow M X Y r) : AtomicWord M X Y :=
  Classical.choose ((positiveReducedArrow_iff_exists_atomicWord M).mp h)

theorem PositiveReducedArrow.atomicWord_eval {X Y : RibbonObject M} {r : Artin.Group M}
    (h : PositiveReducedArrow M X Y r) : (h.atomicWord M).eval = r :=
  Classical.choose_spec ((positiveReducedArrow_iff_exists_atomicWord M).mp h)

end ArtinNormalisers.Ribbon2
