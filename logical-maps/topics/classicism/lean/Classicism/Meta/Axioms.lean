import Classicism.Meta.Derivation

/-!
# Classicism, as an axiom set

The eleven closed identities of Figures 2 and 3, as sentences of the object language, and
Classicism as the theory they axiomatize: `C.Derivable Δ p` is `Derivable C.axioms Δ p`.
These are the same eleven that `Classicism/Axiomatization.lean` states as Lean axioms and
that the strict layer proves everything from, now written in de Bruijn syntax; in each,
`v0` is the innermost bound variable, `v1` the next out, `v2` the next.

## `C` and `C⁻`

A derivation in context `Γ` may use the variables of `Γ`, and a closed derivation has
none. So from no hypotheses in the empty context nothing of type `e` is ever available,
and `∃x:e. x = x` is not derivable from the eleven identities alone: the system of
`Classicism/Meta/Derivation.lean` is existentially neutral at `e`, the paper's `H⁻`
(Classicism, nn. 12–13), where `H` assumes every type inhabited. At every relational type
a closed term exists, `λx. ⊤`, so Existence there is derivable. This is the same line the
shallow layer draws with the axiom `e_exists`: `C⁻` is the eleven, and `C` adds Existence
at `e`.
-/

namespace Classicism.Meta

variable {Sig : Signature}

namespace Term

/-- Short names for the three innermost variables. -/
abbrev v0 {Γ : Ctx} {σ : Ty} : Term Sig (σ :: Γ) σ := .var .zero
@[inherit_doc v0] abbrev v1 {Γ : Ctx} {σ τ : Ty} : Term Sig (τ :: σ :: Γ) σ := .var (.succ .zero)
@[inherit_doc v0] abbrev v2 {Γ : Ctx} {σ τ υ : Ty} : Term Sig (υ :: τ :: σ :: Γ) σ :=
  .var (.succ (.succ .zero))

end Term

namespace C

open Term

/-! ### The six Boolean Identities, Figure 2 -/

/-- `(λpq. p ∧ q) = (λpq. q ∧ p)`. -/
def commutativity_and : Sentence Sig :=
  eq' (lam (lam (conj v1 v0))) (lam (lam (conj v0 v1)))
/-- `(λpq. p ∨ q) = (λpq. q ∨ p)`. -/
def commutativity_or : Sentence Sig :=
  eq' (lam (lam (disj v1 v0))) (lam (lam (disj v0 v1)))
/-- `(λpqr. p ∧ (q ∨ r)) = (λpqr. (p ∧ q) ∨ (p ∧ r))`. -/
def distribution_and_or : Sentence Sig :=
  eq' (lam (lam (lam (conj v2 (disj v1 v0)))))
      (lam (lam (lam (disj (conj v2 v1) (conj v2 v0)))))
/-- `(λpqr. p ∨ (q ∧ r)) = (λpqr. (p ∨ q) ∧ (p ∨ r))`. -/
def distribution_or_and : Sentence Sig :=
  eq' (lam (lam (lam (disj v2 (conj v1 v0)))))
      (lam (lam (lam (conj (disj v2 v1) (disj v2 v0)))))
/-- `(λpq. p ∧ (q ∨ ¬q)) = (λpq. p)`. -/
def dissolution_and_or : Sentence Sig :=
  eq' (lam (lam (conj v1 (disj v0 (neg v0))))) (lam (lam (v1 : Term Sig [Ty.t, Ty.t] Ty.t)))
/-- `(λpq. p ∨ (q ∧ ¬q)) = (λpq. p)`. -/
def dissolution_or_and : Sentence Sig :=
  eq' (lam (lam (disj v1 (conj v0 (neg v0))))) (lam (lam (v1 : Term Sig [Ty.t, Ty.t] Ty.t)))

/-! ### The five Classicist Identities, Figure 3, at a type `σ` -/

/-- The Identity Identity: `(λyz. y = z) = (λyz. ∀X. Xy ↔ Xz)`. -/
def identity_identity (σ : Ty) : Sentence Sig :=
  eq' (lam (lam (eq' (v1 : Term Sig [σ, σ] σ) v0)))
      (lam (lam (forall' (σ := σ ⇒ RTy.t) (iff (app v0 v2) (app v0 v1)))))
/-- Absorption-∨∀: `(λXy. Xy ∨ ∀X) = (λXy. Xy)`. -/
def absorption_or_forall (σ : Ty) : Sentence Sig :=
  eq' (lam (lam (disj (app (v1 : Term Sig [σ, σ ⇒ RTy.t] (σ ⇒ RTy.t)) v0) (app (all σ) v1))))
      (lam (lam (app (v1 : Term Sig [σ, σ ⇒ RTy.t] (σ ⇒ RTy.t)) v0)))
/-- Distribution-∨∀: `(λXp. p ∨ ∀X) = (λXp. ∀y. p ∨ Xy)`. -/
def distribution_or_forall (σ : Ty) : Sentence Sig :=
  eq' (lam (lam (disj (v0 : Term Sig [Ty.t, σ ⇒ RTy.t] Ty.t) (app (all σ) v1))))
      (lam (lam (forall' (σ := σ) (disj v1 (app (v2 : Term Sig [σ, Ty.t, σ ⇒ RTy.t] (σ ⇒ RTy.t)) v0)))))
/-- Absorption-∧∃: `(λXy. Xy ∧ ∃X) = (λXy. Xy)`. -/
def absorption_and_exists (σ : Ty) : Sentence Sig :=
  eq' (lam (lam (conj (app (v1 : Term Sig [σ, σ ⇒ RTy.t] (σ ⇒ RTy.t)) v0) (app (ex σ) v1))))
      (lam (lam (app (v1 : Term Sig [σ, σ ⇒ RTy.t] (σ ⇒ RTy.t)) v0)))
/-- Distribution-∧∃: `(λXp. p ∧ ∃X) = (λXp. ∃y. p ∧ Xy)`. -/
def distribution_and_exists (σ : Ty) : Sentence Sig :=
  eq' (lam (lam (conj (v0 : Term Sig [Ty.t, σ ⇒ RTy.t] Ty.t) (app (ex σ) v1))))
      (lam (lam (exists' (σ := σ) (conj v1 (app (v2 : Term Sig [σ, Ty.t, σ ⇒ RTy.t] (σ ⇒ RTy.t)) v0)))))

/-- Existence at `e`: `∃x:e. x = x`. -/
def existence_e : Sentence Sig := exists' (σ := Ty.e) (eq' v0 v0)

/-- The axioms of `C⁻`: the eleven identities, the Classicist ones at every type. -/
inductive axiomsMinus : AxiomSet Sig
  | commutativity_and : axiomsMinus commutativity_and
  | commutativity_or : axiomsMinus commutativity_or
  | distribution_and_or : axiomsMinus distribution_and_or
  | distribution_or_and : axiomsMinus distribution_or_and
  | dissolution_and_or : axiomsMinus dissolution_and_or
  | dissolution_or_and : axiomsMinus dissolution_or_and
  | identity_identity (σ : Ty) : axiomsMinus (identity_identity σ)
  | absorption_or_forall (σ : Ty) : axiomsMinus (absorption_or_forall σ)
  | distribution_or_forall (σ : Ty) : axiomsMinus (distribution_or_forall σ)
  | absorption_and_exists (σ : Ty) : axiomsMinus (absorption_and_exists σ)
  | distribution_and_exists (σ : Ty) : axiomsMinus (distribution_and_exists σ)

/-- The axioms of `C`: those of `C⁻` and Existence at `e`. -/
inductive axioms : AxiomSet Sig
  | minus {a : Sentence Sig} : axiomsMinus a → axioms a
  | existence_e : axioms existence_e

/-- Derivability in Classicism. -/
abbrev Derivable {Γ : Ctx} (Δ : List (Formula Sig Γ)) (p : Formula Sig Γ) : Prop :=
  Meta.Derivable axioms Δ p
/-- Derivability in `C⁻`. -/
abbrev DerivableMinus {Γ : Ctx} (Δ : List (Formula Sig Γ)) (p : Formula Sig Γ) : Prop :=
  Meta.Derivable axiomsMinus Δ p
/-- A theorem of Classicism. -/
abbrev Theorem (p : Sentence Sig) : Prop := Meta.Theorem axioms p
/-- A theorem of `C⁻`. -/
abbrev TheoremMinus (p : Sentence Sig) : Prop := Meta.Theorem axiomsMinus p

theorem Derivable.of_minus {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ}
    (h : DerivableMinus Δ p) : Derivable Δ p :=
  Meta.Derivable.mono (fun _ h => axioms.minus h) h

end C

/-! ### Citing an axiom in the empty context -/

theorem Ren.ofEmpty_eq_id : (Ren.ofEmpty : Ren [] []) = Ren.id := by
  funext σ v; exact nomatch v

@[simp] theorem Term.close_nil {σ : Ty} (a : Term Sig [] σ) : a.close = a := by
  rw [Term.close, Ren.ofEmpty_eq_id, Term.rename_id]

/-- An axiom is a theorem. -/
theorem Derivable.axiom {Ax : AxiomSet Sig} {a : Sentence Sig} (h : Ax a) : Theorem Ax a := by
  have := Derivable.ax (Δ := ([] : List (Formula Sig []))) h
  rwa [Term.close_nil] at this

end Classicism.Meta
