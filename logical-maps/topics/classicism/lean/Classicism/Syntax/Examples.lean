import Classicism.Semantics.Relational

/-!
# Examples for the syntax

Small checks that the definitions compute as intended: a β-step reduces by `rfl`, the
paper's abbreviations have the types they should, purity is decided, and a few
derivations go through, among them the axioms as theorems and Existence at a relational
type from a closed term. The last group is the **reflection** check: a sentence read back
through the denotation is, by `rfl`, the Lean proposition the strict layer writes.
-/

namespace Classicism.Meta.Examples

open Term

/-- A signature with one constant, `Wise : e → t`. -/
def sig₁ : Signature := ⟨Unit, fun _ => Ty.e ⇒ RTy.t⟩

/-- `λx. Wise x`, applied to a variable `y : e`, reduces to `Wise y`. -/
example (y : Var [Ty.e] Ty.e) :
    (Term.lam (Sig := sig₁) (.app (.const ()) (.var .zero))).app (.var y)
      ≡ .app (.const ()) (.var y) := by
  -- the substitution evaluates: the two sides are definitionally equal
  exact Conv.beta (Sig := sig₁) (Γ := [Ty.e]) (.app (.const ()) (.var .zero)) (.var y)

/-- `∀x. Wise x → Wise x` is a sentence over `sig₁`, and is not pure. -/
def wiseSelf : Sentence sig₁ :=
  forall' (Term.imp (.app (.const ()) (.var .zero)) (.app (.const ()) (.var .zero)))

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

/-- The logical axiom is a theorem of `C`. -/
example : C.Theorem (Sig := Signature.pure) C.existence_e := Derivable.axiom rfl

open Derivable in
/-- **Commutativity of `∧`, by Subst**: `p ∧ q ⊢ q ∧ p` and back, each on its own, and the
identity `(λpq. p ∧ q) = (λpq. p ∧ q)` by `Ref`; then the right-hand `p ∧ q`, the hole
under two abstractions, becomes `q ∧ p`. This is how each of the eleven identities is a
theorem of `C⁻`. -/
example : C.TheoremMinus (Sig := Signature.pure) C.commutativity_and :=
  subst (P := conj v1 v0) (Q := conj v0 v1)
    (Hole.appR (.app (.eq _) (lam (lam (conj v1 v0)))) (Hole.lam (Hole.lam Hole.hole)))
    (andI (andE₂ hyp₀) (andE₁ hyp₀)) (andI (andE₂ hyp₀) (andE₁ hyp₀)) (refl _)

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

/-! ### Reflection: the denotation reads back the strict layer's own propositions

These are the checks the translator's quotations will be held to. `⌜p⌝` is written by
hand here; each `rfl` says that reading it in the standard interpretation gives exactly
the proposition `p` of the strict layer. -/

/-- The standard interpretation of the pure language over a domain. -/
abbrev std (D : Type) : Interp Signature.pure := Interp.ofDomain D

/-- `⊤`, read back, is the sentence it abbreviates, `(∀p. p) ∨ ¬(∀p. p)`, and that is `True`. -/
example (D : Type) : Sentence.holds (std D) top = ((∀ p : Prop, p) ∨ ¬ ∀ p : Prop, p) := rfl
example (D : Type) : Sentence.holds (std D) top = True := top_eq

/-- `⊥` likewise. -/
example (D : Type) : Sentence.holds (std D) bot = ((∀ p : Prop, p) ∧ ¬ ∀ p : Prop, p) := rfl

/-- `□⊤`, read back, is `⊤ = ⊤` in that reading. -/
example (D : Type) : Sentence.holds (std D) (box top)
    = (((∀ p : Prop, p) ∨ ¬ ∀ p : Prop, p) = ((∀ p : Prop, p) ∨ ¬ ∀ p : Prop, p)) := rfl

/-- The paper's `→` reads back as the strict layer's `imp`. -/
example (D : Type) (p q : Sentence Signature.pure) :
    Sentence.holds (std D) (Term.imp p q)
      = Classicism.imp (Sentence.holds (std D) p) (Sentence.holds (std D) q) :=
  rfl

/-- Commutativity of `∧`, read back, is the statement of the shallow identity
`Classicism.Identities.commutativity_and`. -/
example (D : Type) :
    Sentence.holds (std D) C.commutativity_and = ((fun p q : Prop => p ∧ q) = (fun p q => q ∧ p)) :=
  rfl

/-- Absorption-∨∀ at `e`, read back, is the Lean axiom's statement at `D`. -/
example (D : Type) :
    Sentence.holds (std D) (C.absorption_or_forall Ty.e)
      = ((fun (X : D → Prop) y => X y ∨ ∀ x, X x) = (fun X y => X y)) :=
  rfl

/-- Existence at `e`, read back, over the naturals. -/
example : Sentence.holds (std Nat) C.existence_e = ∃ x : Nat, x = x := rfl

/-- And soundness makes such readings theorems: `⊤` holds over any domain. -/
example (D : Type) : Sentence.holds (std D) top :=
  C.TheoremMinus.holds (std D) Derivable.top

end Classicism.Meta.Examples
