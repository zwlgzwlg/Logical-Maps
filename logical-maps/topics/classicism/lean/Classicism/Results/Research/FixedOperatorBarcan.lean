import Classicism.Background.Box5

/-!
# Fixed operators and relational Barcan

Shallow C derivations for the fixed-operator test in
`writeups/signature-strong-possibility-and-relational-barcan-incompatible.md`.
The signature Strong Possibility argument, the finite witness and the unique
selection obstruction are due to the parallel research group of OpenAI Codex
(GPT-6), prompted by Daniel Kodsi, 27 November 2026. Its original
`FixedOperators.lean` supplies the unique-instance calculation and the
general function-equality and predicate-name steps below. This consolidation
also derives the pure tester's Barcan contradiction from its distinctness-
preserving possibility. The existence of that possibility uses the separate
Maximalist model argument. The NKB quantifier result uses Prior's argument
in the library's `s5Op_barcan`.
-/

namespace Classicism.FixedOperatorBarcan
open Classicism.P Classicism.Paper

/-- The unboxed Boolean equations in the fixed-operator test. -/
def BooleanInvolution (f : Prop → Prop) : Prop :=
  (∀ p : Prop, f (¬ p) = ¬ f p) ∧
  (∀ p q : Prop, f (p ∧ q) = (f p ∧ f q)) ∧
  (∀ p : Prop, f (f p) = p)

theorem preserves_false (f : Prop → Prop) (h : BooleanInvolution f) :
    f False = False :=
  calc
    f False = f (True ∧ ¬ True) := congrArg f (and_not_self_eq True).symm
    _ = (f True ∧ f (¬ True)) := h.2.1 _ _
    _ = (f True ∧ ¬ f True) := congrArg (And (f True)) (h.1 True)
    _ = False := and_not_self_eq _

theorem preserves_true (f : Prop → Prop) (h : BooleanInvolution f) :
    f True = True :=
  calc
    f True = f (¬ False) := congrArg f not_false_eq.symm
    _ = ¬ f False := h.1 False
    _ = ¬ False := congrArg Not (preserves_false f h)
    _ = True := not_false_eq

theorem law_n (f : Prop → Prop) (h : BooleanInvolution f) :
    ∀ p : Prop, □ p → f p := fun p hp => by
  change p = True at hp
  rw [hp, preserves_true f h]
  trivial

theorem law_k (f : Prop → Prop) (h : BooleanInvolution f) :
    ∀ p q : Prop, f (p → q) → f p → f q := by
  intro p q hi hp
  have hab : (f p ∧ ¬ f q) = ¬ f (p → q) := calc
    (f p ∧ ¬ f q) = (f p ∧ f (¬ q)) := congrArg (And (f p)) (h.1 q).symm
    _ = f (p ∧ ¬ q) := (h.2.1 _ _).symm
    _ = f (¬ (p → q)) := congrArg f (not_imp_eq p q).symm
    _ = ¬ f (p → q) := h.1 _
  exact (em (f q)).elim id fun hn => (hab.mp ⟨hp, hn⟩ hi).elim

theorem law_b (f : Prop → Prop) (h : BooleanInvolution f) :
    ∀ p : Prop, p → f (¬ f (¬ p)) := by
  intro p hp
  rw [h.1 p, not_not_eq, h.2.2]
  exact hp

/-- Prior's NKB argument applies without any assumption of ordinary Barcan. -/
theorem s5_of_involution (f : Prop → Prop) (h : □ (BooleanInvolution f)) : S5Op f :=
  ⟨modal_K _ _ (nec% (law_n f)) h, modal_K _ _ (nec% (law_k f)) h,
   modal_K _ _ (nec% (law_b f)) h⟩

theorem preserves_all_iff {σ : Type} [Ty σ] (f : Prop → Prop)
    (R : σ → Prop) (h : □ (BooleanInvolution f)) :
    f (∀ x, R x) ↔ ∀ x, f (R x) :=
  let s := s5_of_involution f h
  ⟨fun hall x => box_elim s.2.1 _ _
    (box_elim s.1 _ (nec% (fun (allR : ∀ z, R z) => allR x))) hall,
   s5Op_barcan f s R⟩

/-- Commutation with object-language quantification as a proposition identity. -/
theorem preserves_all {σ : Type} [Ty σ] (f : Prop → Prop)
    (R : σ → Prop) (h : □ (BooleanInvolution f)) :
    f (∀ x, R x) = ∀ x, f (R x) :=
  modalized_fregean _ _
    (modal_K _ _ (nec% (preserves_all_iff f R)) (modal_four _ h))

theorem preserves_eq_iff {σ : Type} [Ty σ] (f : Prop → Prop) (x y : σ)
    (h : □ (BooleanInvolution f)) : f (x = y) ↔ x = y := by
  let s := s5_of_involution f h
  constructor
  · intro he
    exact (em (x = y)).elim id fun hn => by
      have hne := box5_of_ne x y hn f s
      exact (((box_elim h).1 (x = y)).mp hne he).elim
  · intro he
    exact box5_of_eq x y he f s

/-- Equality at any input type is fixed as a whole proposition. -/
theorem preserves_eq {σ : Type} [Ty σ] (f : Prop → Prop) (x y : σ)
    (h : □ (BooleanInvolution f)) : f (x = y) = (x = y) :=
  modalized_fregean _ _
    (modal_K _ _ (nec% (preserves_eq_iff f x y)) (modal_four _ h))

/-- The arrow step of the type induction when both component types are relational. -/
def conjugate {σ τ : Type} [Rel σ] [Rel τ] (i : σ → σ) (o : τ → τ)
    (Y : σ → τ) : σ → τ := fun x => o (Y (i x))

theorem conjugate_involutive {σ τ : Type} [Rel σ] [Rel τ] (i : σ → σ) (o : τ → τ)
    (Y : σ → τ) (hi : □ (∀ x, i (i x) = x)) (ho : □ (∀ y, o (o y) = y)) :
    conjugate i o (conjugate i o Y) = Y :=
  modalized_functionality _ _ (modal_K _ _ (modal_K _ _
    (nec% (fun (left : ∀ x, i (i x) = x) (right : ∀ y, o (o y) = y) (x : σ) =>
      (show conjugate i o (conjugate i o Y) x = Y x from
        (right (Y (i (i x)))).trans (congrArg Y (left x))))) hi) ho)

/-- At individual input the action is the identity; no operator e → e is formed. -/
theorem individual_arrow_involutive {τ : Type} [Rel τ] (o : τ → τ)
    (Y : e → τ) (ho : □ (∀ y, o (o y) = y)) :
    (fun x => o (o (Y x))) = Y :=
  modalized_functionality _ _ (modal_K _ _
    (nec% (fun (right : ∀ y, o (o y) = y) (x : e) => right (Y x))) ho)

/-- From the parallel group's fixed-operator proof: BF at the input type
    is enough for this pair of pointwise identical functions. -/
theorem barcan_function_equality {σ τ : Type} [Ty σ] [Rel τ] (X Y : σ → τ)
    (bf : Barcan σ) (fixed : ∀ x, X x = Y x) : X = Y :=
  modalized_functionality X Y (bf (fun x => X x = Y x)
    (fun x => necessity_of_identity _ _ (fixed x)))

/-- Current fixing lifts through one individual argument. Repeating this rule
    handles all finite first-order arities with the same unboxed BF premise. -/
theorem fixed_individual_arrow {τ : Type} [Rel τ] (o : τ → τ) (Y : e → τ)
    (bf : Barcan e) (fixed : ∀ x, o (Y x) = Y x) :
    (fun x => o (Y x)) = Y :=
  barcan_function_equality _ _ bf fixed

theorem fixes_predicate_name {σ : Type} [Ty σ] (f : Prop → Prop) (Y : σ → Prop)
    (bf : Barcan σ) (fixed : ∀ p : Prop, f p = p) : (fun x => f (Y x)) = Y :=
  barcan_function_equality _ _ bf (fun x => fixed (Y x))

/-- Distinctness-preserving possibility supplies a return to any current truth. -/
theorem possible_return (p q : Prop) (h : DiaNe p) (hq : q) : ◇ (p ∧ ◇ q) :=
  (em (◇ (p ∧ ◇ q))).elim id fun hn =>
    (h ⟨q, hq, modal_K _ _
      (nec% (fun (neg : ¬ (p ∧ ◇ q)) (d : ◇ q) (hp : p) => neg ⟨hp, d⟩))
      (box_not_of_not_dia _ hn)⟩).elim

/-- Reflect a universal identity without imposing Barcan at its input type. -/
theorem reflects_forall_eq {σ τ : Type} [Ty σ] [Rel τ] (p : Prop) (L R : σ → τ)
    (h : DiaNe p) (bound : □ (p → ∀ x, L x = R x)) : ∀ x, L x = R x := by
  intro x
  apply (em (L x = R x)).elim id
  intro hn
  have both := possible_return p (L x ≠ R x) h hn
  have bad : □ (¬ (p ∧ ◇ (L x ≠ R x))) := modal_K _ _
    (nec% (fun (hb : p → ∀ y, L y = R y) =>
      (show ¬ (p ∧ ◇ (L x ≠ R x)) from fun pair =>
        ne_of_dia_ne (L x) (R x) pair.2 (hb pair.1 x)))) bound
  exact (not_dia_of_box_not _ bad both).elim

/-- The witness pattern of the fixed-operator construction refutes one BF instance. -/
theorem not_barcan_of_possible_tester {σ : Type} [Ty σ] (C : σ → Prop)
    (h : DiaNe ((∀ x, C x = True) ∧ C ≠ fun _ => True)) : ¬ Barcan σ := by
  let p := (∀ x, C x = True) ∧ C ≠ fun _ => True
  have each : ∀ x, C x = True := reflects_forall_eq p C (fun _ => True) h
    (nec% (fun (hp : (∀ x, C x = True) ∧ C ≠ fun _ => True) => hp.1))
  intro bf
  have allC := bf C each
  have eqC : C = fun _ => True := intensionality C (fun _ => True)
    (modal_K _ _
      (nec% (fun (allC : ∀ x, C x) (x : σ) =>
        (show C x ↔ True from ⟨fun _ => trivial, fun _ => allC x⟩))) allC)
  have noEq : ◇ (C ≠ fun _ => True) := dia_mono _ _
    (nec% (fun (hp : (∀ x, C x = True) ∧ C ≠ fun _ => True) => hp.2))
    (dia_of_not_boxNe_neg _ h)
  exact ne_of_dia_ne C (fun _ => True) noEq eqC

/-- The pure guard common to the Barcan and selection tests. -/
def fixedGuard (f : Prop → Prop) : Prop :=
  □ (BooleanInvolution f) ∧ (∀ p, f p = p) ∧ □ (Barcan e)

/-- The exact closed operator test from the first-order-signature argument. -/
def fixedTester (Y : Prop → Prop) : Prop :=
  ∀ f : Prop → Prop, fixedGuard f → conjugate f f Y = Y

/-- The remaining premise is precisely the model-theoretic witness in the write-up. -/
theorem fixed_tester_refutes_operator_barcan
    (h : DiaNe ((∀ Y, fixedTester Y = True) ∧ fixedTester ≠ fun _ => True)) :
    ¬ Barcan (Prop → Prop) :=
  not_barcan_of_possible_tester fixedTester h

/-- An operator and its double conjugate are identical under the boxed guard. -/
theorem double_conjugation (f Y : Prop → Prop) (hb : □ (BooleanInvolution f)) :
    conjugate f f (conjugate f f Y) = Y :=
  let inv := modal_K _ _
    (nec% (fun (law : BooleanInvolution f) => law.2.2)) hb
  conjugate_involutive f f Y inv inv

/-- The parallel group's selection lemma. A fixed property cannot select a
    moved instance uniquely when the involution fixes every current scalar. -/
theorem fixed_unique_instance (f Y : Prop → Prop) (G : (Prop → Prop) → Prop)
    (hb : □ (BooleanInvolution f)) (hs : ∀ p : Prop, f p = p)
    (hg : conjugate (conjugate f f) f G = G)
    (hy : G Y) (hu : ∀ Z, G Z → Z = Y) : conjugate f f Y = Y := by
  have step : f (G (conjugate f f (conjugate f f Y))) = G (conjugate f f Y) :=
    congrFun hg (conjugate f f Y)
  have agree : G Y = G (conjugate f f Y) :=
    (hs (G Y)).symm.trans
      ((congrArg (fun Z => f (G Z)) (double_conjugation f Y hb)).symm.trans step)
  exact hu _ (agree.mp hy)

/-- A property fixed by every guarded conjugation has only fixed operators
    as uniquely selected current instances. -/
theorem fixed_selector_passes_tester (G : (Prop → Prop) → Prop) (Y : Prop → Prop)
    (hg : ∀ f, fixedGuard f → conjugate (conjugate f f) f G = G)
    (hy : G Y) (hu : ∀ Z, G Z → Z = Y) : fixedTester Y :=
  fun f guard => fixed_unique_instance f Y G guard.1 guard.2.1 (hg f guard) hy hu

end Classicism.FixedOperatorBarcan
