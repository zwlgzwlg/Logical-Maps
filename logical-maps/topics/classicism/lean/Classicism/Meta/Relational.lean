import Classicism.Meta.Denotation
import Classicism.Mirror

/-!
# The relational operations, in the object language

The paper writes the Boolean operations, coextension, and the pointwise box at every
relational type with a type subscript, `∧_τ`, `¬_τ`, and defines each by recursion on the
type: at `t` it is the propositional operation, at `σ → ρ` it is the operation at `ρ`
applied pointwise. The strict layer carries these as the class `SRel`, with an instance
per shape of type. In the object language they are what they are in the paper,
**functions on terms defined by recursion on the type**: `andR τ X Y` is `X ∧_τ Y`.

This is purpose four of the metalogical layer doing work. The shallow layer could not
recurse on the structure of a type, because there a type was a Lean type and the
relational types a class; here a relational type is an inductive, and the recursion is
ordinary.

The bridge to the strict layer is `instSRelDenote`, which equips the standard reading of
each relational type with its `SRel` instance by the same recursion, and one lemma per
operation, proved by induction on the type, saying that reading `andR τ X Y` back gives
`SRel.and` of the readings. These are what let the quoter handle a strict statement with a
parameter `[SRel τ]`: the operations at the type variable `τ` become `andR τ'` and the
rest, and reflection, no longer `rfl`, is these lemmas.
-/

namespace Classicism.Meta

variable {Sig : Signature}

namespace Term

/-! ### The operations, by recursion on the type -/

/-- `constR τ p` is the constant relation `λz̄. p` at `τ`. -/
def constR : ∀ (τ : RTy) {Γ : Ctx}, Formula Sig Γ → Term Sig Γ τ
  | .t, _, p => p
  | .arr _ ρ, _, p => .lam (constR ρ p.weaken)

/-- `negR τ X` is `¬_τ X`, pointwise negation. -/
def negR : ∀ (τ : RTy) {Γ : Ctx}, Term Sig Γ τ → Term Sig Γ τ
  | .t, _, X => neg X
  | .arr _ ρ, _, X => .lam (negR ρ (.app X.weaken v0))

/-- `andR τ X Y` is `X ∧_τ Y`. -/
def andR : ∀ (τ : RTy) {Γ : Ctx}, Term Sig Γ τ → Term Sig Γ τ → Term Sig Γ τ
  | .t, _, X, Y => conj X Y
  | .arr _ ρ, _, X, Y => .lam (andR ρ (.app X.weaken v0) (.app Y.weaken v0))

/-- `orR τ X Y` is `X ∨_τ Y`. -/
def orR : ∀ (τ : RTy) {Γ : Ctx}, Term Sig Γ τ → Term Sig Γ τ → Term Sig Γ τ
  | .t, _, X, Y => disj X Y
  | .arr _ ρ, _, X, Y => .lam (orR ρ (.app X.weaken v0) (.app Y.weaken v0))

/-- `coextR τ X Y` is `∀z̄. X z̄ ↔ Y z̄`, coextensiveness. -/
def coextR : ∀ (τ : RTy) {Γ : Ctx}, Term Sig Γ τ → Term Sig Γ τ → Formula Sig Γ
  | .t, _, X, Y => iff X Y
  | .arr _ ρ, _, X, Y => forall' (coextR ρ (.app X.weaken v0) (.app Y.weaken v0))

/-- `boxR τ X` is `λz̄. □(X z̄)`, the pointwise box. -/
def boxR : ∀ (τ : RTy) {Γ : Ctx}, Term Sig Γ τ → Term Sig Γ τ
  | .t, _, X => box X
  | .arr _ ρ, _, X => .lam (boxR ρ (.app X.weaken v0))

/-- `boxImpR τ X Y` is `∀z̄. X z̄ → Y z̄`, pointwise implication. -/
def boxImpR : ∀ (τ : RTy) {Γ : Ctx}, Term Sig Γ τ → Term Sig Γ τ → Formula Sig Γ
  | .t, _, X, Y => imp X Y
  | .arr _ ρ, _, X, Y => forall' (boxImpR ρ (.app X.weaken v0) (.app Y.weaken v0))

/-- `⊤_τ`. -/
abbrev topR (τ : RTy) {Γ : Ctx} : Term Sig Γ τ := constR τ top
/-- `⊥_τ`. -/
abbrev botR (τ : RTy) {Γ : Ctx} : Term Sig Γ τ := constR τ bot
/-- `X ≤_τ Y`, the algebraic order: `Y = X ∨_τ Y`. -/
abbrev leR (τ : RTy) {Γ : Ctx} (X Y : Term Sig Γ τ) : Formula Sig Γ := eq' Y (orR τ X Y)

end Term

/-! ### The standard reading carries the strict layer's instances -/

/-- The `SRel` instance on the reading of a relational type, by recursion on the type:
`instSRelProp` at `t`, `instSRelArrow` at an arrow. -/
instance instSRelDenote (D : Type) : ∀ τ : RTy, Classicism.Strict.SRel (RTy.denote D τ)
  | .t => Classicism.Strict.instSRelProp
  | .arr _ ρ => @Classicism.Strict.instSRelArrow _ _ ⟨()⟩ (instSRelDenote D ρ)

/-- Likewise `SOrder`. -/
instance instSOrderDenote (D : Type) : ∀ τ : RTy,
    @Classicism.Strict.SOrder (RTy.denote D τ) (instSRelDenote D τ)
  | .t => Classicism.Strict.instSOrderProp
  | .arr _ ρ => @Classicism.Strict.instSOrderArrow _ _ ⟨()⟩ (instSRelDenote D ρ) (instSOrderDenote D ρ)

/-- Two universal statements with pointwise-identical bodies are identical. -/
theorem forall_congr_eq {α : Sort _} {p q : α → Prop} (h : ∀ x, p x = q x) : (∀ x, p x) = ∀ x, q x :=
  congrArg (fun r => ∀ x, r x) (funext h)

/-! ### Reading each operation back gives the strict layer's -/

namespace Term

open Classicism.Strict

theorem denote_constR (I : Interp Sig) : ∀ (τ : RTy) {Γ : Ctx} (p : Formula Sig Γ) (env : Env I.D Γ),
    (constR τ p).denote I env = @SRel.constP _ (instSRelDenote I.D τ) (p.denote I env)
  | .t, _, _, _ => rfl
  | .arr _ ρ, _, p, env => by
    show (fun x => (constR ρ p.weaken).denote I (.cons x env)) = _
    funext x
    rw [denote_constR I ρ, Formula.denote_weaken]
    rfl

theorem denote_negR (I : Interp Sig) : ∀ (τ : RTy) {Γ : Ctx} (X : Term Sig Γ τ) (env : Env I.D Γ),
    (negR τ X).denote I env = @SRel.neg _ (instSRelDenote I.D τ) (X.denote I env)
  | .t, _, _, _ => rfl
  | .arr _ ρ, _, X, env => by
    show (fun x => (negR ρ (.app X.weaken v0)).denote I (.cons x env)) = _
    funext x
    rw [denote_negR I ρ]
    show SRel.neg (X.weaken.denote I (.cons x env) x) = _
    rw [Term.denote_weaken]
    rfl

theorem denote_andR (I : Interp Sig) : ∀ (τ : RTy) {Γ : Ctx} (X Y : Term Sig Γ τ) (env : Env I.D Γ),
    (andR τ X Y).denote I env = @SRel.and _ (instSRelDenote I.D τ) (X.denote I env) (Y.denote I env)
  | .t, _, _, _, _ => rfl
  | .arr _ ρ, _, X, Y, env => by
    show (fun x => (andR ρ (.app X.weaken v0) (.app Y.weaken v0)).denote I (.cons x env)) = _
    funext x
    rw [denote_andR I ρ]
    show SRel.and (X.weaken.denote I (.cons x env) x) (Y.weaken.denote I (.cons x env) x) = _
    rw [Term.denote_weaken, Term.denote_weaken]
    rfl

theorem denote_orR (I : Interp Sig) : ∀ (τ : RTy) {Γ : Ctx} (X Y : Term Sig Γ τ) (env : Env I.D Γ),
    (orR τ X Y).denote I env = @SRel.or _ (instSRelDenote I.D τ) (X.denote I env) (Y.denote I env)
  | .t, _, _, _, _ => rfl
  | .arr _ ρ, _, X, Y, env => by
    show (fun x => (orR ρ (.app X.weaken v0) (.app Y.weaken v0)).denote I (.cons x env)) = _
    funext x
    rw [denote_orR I ρ]
    show SRel.or (X.weaken.denote I (.cons x env) x) (Y.weaken.denote I (.cons x env) x) = _
    rw [Term.denote_weaken, Term.denote_weaken]
    rfl

theorem denote_coextR (I : Interp Sig) : ∀ (τ : RTy) {Γ : Ctx} (X Y : Term Sig Γ τ) (env : Env I.D Γ),
    ((coextR τ X Y).denote I env : Prop) = @SRel.coext _ (instSRelDenote I.D τ) (X.denote I env) (Y.denote I env)
  | .t, _, _, _, _ => rfl
  | .arr _ ρ, _, X, Y, env => by
    show (∀ x, (coextR ρ (.app X.weaken v0) (.app Y.weaken v0)).denote I (.cons x env))
      = ∀ z, SRel.coext (X.denote I env z) (Y.denote I env z)
    apply forall_congr_eq
    intro x
    rw [denote_coextR I ρ]
    show SRel.coext (X.weaken.denote I (.cons x env) x) (Y.weaken.denote I (.cons x env) x) = _
    rw [Term.denote_weaken, Term.denote_weaken]

theorem denote_boxR (I : Interp Sig) : ∀ (τ : RTy) {Γ : Ctx} (X : Term Sig Γ τ) (env : Env I.D Γ),
    (boxR τ X).denote I env = @SRel.boxAt _ (instSRelDenote I.D τ) (X.denote I env)
  | .t, _, _, _ => rfl
  | .arr _ ρ, _, X, env => by
    show (fun x => (boxR ρ (.app X.weaken v0)).denote I (.cons x env)) = _
    funext x
    rw [denote_boxR I ρ]
    show SRel.boxAt (X.weaken.denote I (.cons x env) x) = _
    rw [Term.denote_weaken]
    rfl

theorem denote_boxImpR (I : Interp Sig) : ∀ (τ : RTy) {Γ : Ctx} (X Y : Term Sig Γ τ) (env : Env I.D Γ),
    ((boxImpR τ X Y).denote I env : Prop) = @SRel.boxImp _ (instSRelDenote I.D τ) (X.denote I env) (Y.denote I env)
  | .t, _, _, _, _ => rfl
  | .arr _ ρ, _, X, Y, env => by
    show (∀ x, (boxImpR ρ (.app X.weaken v0) (.app Y.weaken v0)).denote I (.cons x env))
      = ∀ z, SRel.boxImp (X.denote I env z) (Y.denote I env z)
    apply forall_congr_eq
    intro x
    rw [denote_boxImpR I ρ]
    show SRel.boxImp (X.weaken.denote I (.cons x env) x) (Y.weaken.denote I (.cons x env) x) = _
    rw [Term.denote_weaken, Term.denote_weaken]

end Term

end Classicism.Meta
