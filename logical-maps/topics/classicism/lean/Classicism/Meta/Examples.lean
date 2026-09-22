import Classicism.Meta.Axioms

/-!
# Examples for the syntax

Small checks that the definitions compute as intended: a β-step reduces by `rfl`, the
paper's abbreviations have the types they should, purity is decided, and a few
derivations go through, among them the axioms as theorems and Existence at a relational
type from a closed term.
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

/-! ### Derivations -/

open Derivable in
/-- `⊤` is a theorem of `C⁻`, being an instance of excluded middle. -/
example : C.TheoremMinus (Sig := Signature.pure) top := Derivable.top

/-- Each axiom is a theorem of its theory. -/
example : C.TheoremMinus (Sig := Signature.pure) C.commutativity_and :=
  Derivable.axiom .commutativity_and
example : C.Theorem (Sig := Signature.pure) C.existence_e := Derivable.axiom .existence_e
example : C.TheoremMinus (Sig := sig₁) (C.identity_identity Ty.e) :=
  Derivable.axiom (.identity_identity _)

open Derivable in
/-- In a context with a variable, `∀F` yields `∃F`: UI at the variable, then EG. -/
example {Ax : AxiomSet sig₁} {σ : Ty} (F : Term sig₁ [σ] (σ ⇒ RTy.t)) :
    Derivable Ax [Term.app (.all σ) F] (.app (.ex σ) F) :=
  exI v0 (allE hyp₀ v0)

open Derivable in
/-- Existence at a relational type is a theorem of `C⁻`, the witness being the closed
term `λx. ⊤`: `Ref` at it, β, then EG. No such derivation exists at `e`, where the empty
context has no term, which is why Existence at `e` is an axiom of `C` and not of `C⁻`. -/
example {σ : Ty} :
    C.TheoremMinus (Sig := Signature.pure) (exists' (σ := σ ⇒ RTy.t) (eq' v0 v0)) :=
  exI (lam top) (conv (refl (lam top)) (Conv.symm (Conv.beta _ _)))

open Derivable in
/-- Symmetry of `∧`, from a hypothesis. -/
example {Ax : AxiomSet sig₁} (p q : Formula sig₁ []) :
    Derivable Ax [conj p q] (conj q p) :=
  andI (andE₂ hyp₀) (andE₁ hyp₀)

end Classicism.Meta.Examples
