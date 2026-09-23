import Classicism.Meta.Denotation
import Classicism.Mirror

/-!
# The relational operations, in the object language

The paper writes the Boolean operations, coextension, and the pointwise box at every
relational type with a type subscript, `∧_τ`, `¬_τ`, and defines each by recursion on the
type: at `t` it is the propositional operation, at `σ → ρ` it is the operation at `ρ`
applied pointwise. The strict layer carries these as the class `SRel`, with an instance
per shape of type. In the object language they are **constants of the syntax with an
unfolding rule**, `Term.andR ρ` and the rest of `Term.lean`, the recursive definition
read as the δ-rule of conversion (`Conversion.lean`): `∧_t ≡ ∧`, and
`∧_{σ→ρ} ≡ λX Y z. X z ∧_ρ Y z`.

Constants rather than functions defined by recursion on the type, which is what they
were first: a function stuck at a type *variable* is not a node of the syntax, so
renaming and substitution could not pass through it, and no derivation could mention
`∧_τ` for `τ` a variable — which is exactly what a derivation by induction on the type
must do. As constants they are what the paper's subscripted symbols are, and their
recursion is a matter of conversion, not of the syntax.

Their reading (`Denotation.lean`) is the same recursion on the Lean side. The bridge to
the strict layer is `instSRelDenote`, which equips the standard reading of each relational
type with its `SRel` instance by that recursion, and one lemma per operation, proved by
induction on the type, saying that reading `∧_τ` back gives `SRel.and`. These are what
let the quoter handle a strict statement with a parameter `[SRel τ]`: the operations at
the type variable `τ` become `andR τ'` and the rest, and reflection, no longer `rfl`, is
these lemmas.
-/

namespace Classicism.Meta

variable {Sig : Signature}

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

/-! ### Reading each operation back gives the strict layer's -/

open Classicism.Strict

/-- The recursions of `Denotation.lean` are the strict layer's operations, by induction
on the type. Stated on the recursions themselves, `RTy.andD` and the rest, since that
is what unfolding `Term.denote` at `andR τ` leaves. -/
theorem RTy.constD_eq (D : Type) : ∀ τ : RTy, RTy.constD D τ = @SRel.constP _ (instSRelDenote D τ)
  | .t => rfl
  | .arr _ ρ => by
    funext p z
    exact congrFun (RTy.constD_eq D ρ) p

theorem RTy.negD_eq (D : Type) : ∀ τ : RTy, RTy.negD D τ = @SRel.neg _ (instSRelDenote D τ)
  | .t => rfl
  | .arr _ ρ => by
    funext X z
    exact congrFun (RTy.negD_eq D ρ) (X z)

theorem RTy.andD_eq (D : Type) : ∀ τ : RTy, RTy.andD D τ = @SRel.and _ (instSRelDenote D τ)
  | .t => rfl
  | .arr _ ρ => by
    funext X Y z
    exact congrFun (congrFun (RTy.andD_eq D ρ) (X z)) (Y z)

theorem RTy.orD_eq (D : Type) : ∀ τ : RTy, RTy.orD D τ = @SRel.or _ (instSRelDenote D τ)
  | .t => rfl
  | .arr _ ρ => by
    funext X Y z
    exact congrFun (congrFun (RTy.orD_eq D ρ) (X z)) (Y z)

theorem RTy.coextD_eq (D : Type) : ∀ τ : RTy, RTy.coextD D τ = @SRel.coext _ (instSRelDenote D τ)
  | .t => rfl
  | .arr _ ρ => by
    funext X Y
    exact congrArg (fun r => ∀ z, r z) (funext fun z => congrFun (congrFun (RTy.coextD_eq D ρ) (X z)) (Y z))

theorem RTy.boxD_eq (D : Type) : ∀ τ : RTy, RTy.boxD D τ = @SRel.boxAt _ (instSRelDenote D τ)
  | .t => rfl
  | .arr _ ρ => by
    funext X z
    exact congrFun (RTy.boxD_eq D ρ) (X z)

theorem RTy.boxImpD_eq (D : Type) : ∀ τ : RTy, RTy.boxImpD D τ = @SRel.boxImp _ (instSRelDenote D τ)
  | .t => rfl
  | .arr _ ρ => by
    funext X Y
    exact congrArg (fun r => ∀ z, r z) (funext fun z => congrFun (congrFun (RTy.boxImpD_eq D ρ) (X z)) (Y z))

namespace Term

variable (I : Interp Sig) {Γ : Ctx} (τ : RTy) (env : Env I.D Γ)

theorem denote_constR : (Term.constR (Sig := Sig) τ).denote I env = @SRel.constP _ (instSRelDenote I.D τ) :=
  RTy.constD_eq I.D τ
theorem denote_negR : (Term.negR (Sig := Sig) τ).denote I env = @SRel.neg _ (instSRelDenote I.D τ) :=
  RTy.negD_eq I.D τ
theorem denote_andR : (Term.andR (Sig := Sig) τ).denote I env = @SRel.and _ (instSRelDenote I.D τ) :=
  RTy.andD_eq I.D τ
theorem denote_orR : (Term.orR (Sig := Sig) τ).denote I env = @SRel.or _ (instSRelDenote I.D τ) :=
  RTy.orD_eq I.D τ
theorem denote_coextR : (Term.coextR (Sig := Sig) τ).denote I env = @SRel.coext _ (instSRelDenote I.D τ) :=
  RTy.coextD_eq I.D τ
theorem denote_boxR : (Term.boxR (Sig := Sig) τ).denote I env = @SRel.boxAt _ (instSRelDenote I.D τ) :=
  RTy.boxD_eq I.D τ
theorem denote_boxImpR : (Term.boxImpR (Sig := Sig) τ).denote I env = @SRel.boxImp _ (instSRelDenote I.D τ) :=
  RTy.boxImpD_eq I.D τ

end Term

end Classicism.Meta
