/-!
# The metalogical layer: types of the relational type system

This is the first module of the **metalogical layer**, in which the terms of the paper's
object language, their derivations, and their models are objects of Lean, so that
metalogical statements can be made about them: that a schema implies a schema, that a
closed pure sentence is a theorem, that a sentence holds in a model. The shallow and
strict layers state and prove object-language theorems *in* Lean; this layer states
theorems *about* the object language, and is related to the other two by a denotation
that reads its terms as Lean propositions.

The types are the relational type system `R` (Classicism, §1.1): two base types, `e` and
`t`, and `σ → τ` for a type `σ` and a *relational* type `τ`, a relational type being one
that ends in `t`. The definition is the mutual one of Dorr's *Elimination*, Appendix A:
types and terminals, with terminals subsumed under types.

Only these two base types: the type system is fixed, not parametrized by a set of base
types, and nonlogical vocabulary enters through a signature of constants instead.
-/

namespace Classicism.Meta

mutual
  /-- A type of `R`: the type `e` of individuals, or a relational type. -/
  inductive Ty : Type
    | e : Ty
    | rel : RTy → Ty
  /-- A relational type, one ending in `t`: `t` itself, or `σ → ρ` for a type `σ` and a
  relational type `ρ`. -/
  inductive RTy : Type
    | t : RTy
    /-- `σ → ρ`, for a type `σ` and a relational type `ρ`. -/
    | arr : Ty → RTy → RTy
end

/-- `σ ⇒ ρ` is the relational type `σ → ρ`; right-associative, as arrows are. -/
infixr:60 " ⇒ " => RTy.arr

instance : Coe RTy Ty := ⟨Ty.rel⟩

/-- The type `t` of propositions, as a type. -/
abbrev Ty.t : Ty := Ty.rel RTy.t

mutual
  /-- Decidable equality on types. -/
  def Ty.beq : Ty → Ty → Bool
    | .e, .e => true
    | .rel ρ, .rel ρ' => RTy.beq ρ ρ'
    | _, _ => false
  /-- Decidable equality on relational types. -/
  def RTy.beq : RTy → RTy → Bool
    | .t, .t => true
    | .arr σ ρ, .arr σ' ρ' => Ty.beq σ σ' && RTy.beq ρ ρ'
    | _, _ => false
end

mutual
  theorem Ty.eq_of_beq : ∀ {σ σ' : Ty}, Ty.beq σ σ' = true → σ = σ'
    | .e, .e, _ => rfl
    | .rel _, .rel _, h => congrArg Ty.rel (RTy.eq_of_beq h)
  theorem RTy.eq_of_beq : ∀ {ρ ρ' : RTy}, RTy.beq ρ ρ' = true → ρ = ρ'
    | .t, .t, _ => rfl
    | .arr _ _, .arr _ _, h => by
      simp only [RTy.beq, Bool.and_eq_true] at h
      rw [Ty.eq_of_beq h.1, RTy.eq_of_beq h.2]
end

mutual
  theorem Ty.beq_self : ∀ σ : Ty, Ty.beq σ σ = true
    | .e => rfl
    | .rel ρ => RTy.beq_self ρ
  theorem RTy.beq_self : ∀ ρ : RTy, RTy.beq ρ ρ = true
    | .t => rfl
    | .arr σ ρ => by simp only [RTy.beq, Bool.and_eq_true]; exact ⟨Ty.beq_self σ, RTy.beq_self ρ⟩
end

instance : DecidableEq Ty := fun σ σ' =>
  if h : Ty.beq σ σ' = true then isTrue (Ty.eq_of_beq h)
  else isFalse fun e => h (e ▸ Ty.beq_self σ)

instance : DecidableEq RTy := fun ρ ρ' =>
  if h : RTy.beq ρ ρ' = true then isTrue (RTy.eq_of_beq h)
  else isFalse fun e => h (e ▸ RTy.beq_self ρ)

theorem Ty.rel_injective {ρ ρ' : RTy} (h : Ty.rel ρ = Ty.rel ρ') : ρ = ρ' :=
  Ty.rel.inj h

/-- The arity of a relational type: `t` has arity `0`, `σ → ρ` one more than `ρ`. -/
def RTy.arity : RTy → Nat
  | .t => 0
  | .arr _ ρ => ρ.arity + 1

/-- The argument types of a relational type, in order. -/
def RTy.args : RTy → List Ty
  | .t => []
  | .arr σ ρ => σ :: ρ.args

/-- The relational type with the given argument types: `σ₁ → … → σₙ → t`. -/
def RTy.ofArgs : List Ty → RTy
  | [] => .t
  | σ :: σs => .arr σ (ofArgs σs)

theorem RTy.ofArgs_args : ∀ ρ : RTy, RTy.ofArgs ρ.args = ρ
  | .t => rfl
  | .arr σ ρ => by simp [RTy.args, RTy.ofArgs, RTy.ofArgs_args ρ]

/-- Induction on a relational type alone, the mutual motive on `Ty` being trivial: a
property of relational types that holds at `t` and passes from `ρ` to `σ → ρ` holds of
all of them. This is the induction on the structure of types that the shallow layer
cannot perform, where `Rel` is a class and not a code. -/
theorem RTy.induction {motive : RTy → Prop} (t : motive .t)
    (arr : ∀ σ ρ, motive ρ → motive (.arr σ ρ)) : ∀ ρ, motive ρ :=
  fun ρ => RTy.rec (motive_1 := fun _ => True) (motive_2 := motive)
    trivial (fun _ _ => trivial) t (fun σ ρ _ ih => arr σ ρ ih) ρ

/-- Every type of `R` is `e` or `σ₁ → … → σₙ → t`; this is the case split the shallow
layer could not perform, since there `Rel` is a class and not a code. -/
theorem Ty.cases (σ : Ty) : σ = Ty.e ∨ ∃ σs : List Ty, σ = Ty.rel (RTy.ofArgs σs) := by
  cases σ with
  | e => exact Or.inl rfl
  | rel ρ => exact Or.inr ⟨ρ.args, by rw [RTy.ofArgs_args]⟩

end Classicism.Meta
