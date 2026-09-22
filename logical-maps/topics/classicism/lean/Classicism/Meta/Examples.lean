import Classicism.Meta.Conversion

/-!
# Examples for the syntax

Small checks that the definitions compute as intended: a β-step reduces by `rfl`, the
paper's abbreviations have the types they should, and purity is decided.
-/

namespace Classicism.Meta.Examples

open Term

/-- A signature with one constant, `Wise : e → t`. -/
def sig₁ : Signature := ⟨Unit, fun _ => Ty.e ⇒ RTy.t⟩

/-- `λx. Wise x`, applied to a variable `y : e`, reduces to `Wise y`. -/
example (y : Var [Ty.e] Ty.e) :
    (Term.lam (Sig := sig₁) (.app (.const ()) (.var .zero))).app (.var y)
      ≡ .app (.const ()) (.var y) := by
  have := Conv.beta (Sig := sig₁) (Γ := [Ty.e]) (.app (.const ()) (.var .zero)) (.var y)
  simpa [Term.instantiate, Term.subst, Sub.cons, Sub.id] using this

/-- `∀x. Wise x → Wise x` is a sentence over `sig₁`, and is not pure. -/
def wiseSelf : Sentence sig₁ :=
  forall' (imp (.app (.const ()) (.var .zero)) (.app (.const ()) (.var .zero)))

example : wiseSelf.pure = false := by decide

/-- `⊤` and `□⊤` are pure sentences over any signature. -/
example : (top : Sentence sig₁).pure = true := by decide
example : (box top : Sentence Signature.pure).pure = true := by decide

/-- The η rule at a constant. -/
example : Term.lam (Sig := sig₁) (Γ := []) (.app (Term.const ()).weaken (.var .zero))
    ≡ .const () :=
  Conv.eta _

/-- Every type is `e` or ends in `t`; here `e → t → t` has argument types `[e, t]`. -/
example : (Ty.e ⇒ RTy.t ⇒ RTy.t).args = [Ty.e, Ty.t] := rfl

end Classicism.Meta.Examples
