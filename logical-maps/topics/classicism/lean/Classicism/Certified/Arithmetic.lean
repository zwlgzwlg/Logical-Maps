import Classicism.Tools.QuoteTerm
import Classicism.Cardinality
import Classicism.Certified.Signatures

/-!
# The arithmetical sentences, and Necessity of Arithmetic

Goodsell's *Arithmetic is Necessary*, Definitions 3–8, as the map's Background states them,
with the paper's `ν`, `0` and successor taken to be `(e → t) → t`, `𝟎_e` and `Suc_e`:

- the shallow vocabulary, `Arith.zero`, `Arith.suc`, `Arith.N` (`ℕ`, the finite
  cardinalities of individuals), `Arith.Sum` and `Arith.Prod`, quoted into closed pure terms
  by `#classicism_quote_term`, each with its reflection checked; and from them `arithI`,
  `I := ◇I*`, possibly zero is not a successor and successor is injective on numbers;
- the **arithmetical formulas** (`AForm k`, in `k` free number variables): atomic `ℕt`,
  `Sum(t, t', t'')`, `Prod(t, t', t'')` and `t = t'`, whose terms are variables, `𝟎_e` and
  successors (`ATerm k`), closed under `¬`, `∨`, `∧` and `∀v ∈ ℕ`; read as formulas of the
  pure language by `AForm.toTerm`;
- **Necessity of Arithmetic**: `□(I → A) ∨ □(I → ¬A)` for each arithmetical sentence `A`
  (`AxiomSet.necessityOfArithmetic`), the map's `necessity-of-arithmetic` at every
  signature by `ofPure`.
-/


namespace Classicism.Arith

/-- The type of the numbers, `ν := (e → t) → t`. -/
abbrev ν : Type := (e → Prop) → Prop

/-- `𝟎_e`. -/
def zero : ν := ZeroCard e
/-- `Suc_e`. -/
def suc : ν → ν := SucCard
/-- `ℕ`: the finite cardinalities of individuals. -/
def N : ν → Prop := FiniteCardinality

/-- `Sum(m, n, o)`. -/
def Sum : ν → ν → ν → Prop := fun m n o =>
  ∀ R : ν → ν → Prop, R zero m → (∀ i j, N i → N j → R i j → R (suc i) (suc j)) → R n o

/-- `Prod(m, n, o)`. -/
def Prod : ν → ν → ν → Prop := fun m n o =>
  ∀ R : ν → ν → Prop, R zero zero →
    (∀ i j k, N i → N j → N k → R i j → Sum m j k → R (suc i) k) → R n o


end Classicism.Arith

#classicism_quote_term Classicism.Arith.zero Classicism.Arith.suc Classicism.Arith.N
  Classicism.Arith.Sum Classicism.Arith.Prod

noncomputable section

namespace Classicism.Meta

/-- The type `ν` of the object language. -/
abbrev Ty.nu : Ty := .rel (.arr (.rel (.arr .e .t)) .t)

/-- The context of `k` number variables. -/
abbrev numCtx (k : Nat) : Ctx := List.replicate k Ty.nu

/-- The `i`-th of `k` number variables, innermost first. -/
noncomputable def numVar : ∀ {k : Nat}, Fin k → Var (numCtx k) Ty.nu
  | _ + 1, ⟨0, _⟩ => .zero
  | _ + 1, ⟨i + 1, h⟩ => .succ (numVar ⟨i, Nat.lt_of_succ_lt_succ h⟩)

/-- Terms of arithmetic in `k` free variables: variables, `𝟎_e` and successors. -/
inductive ATerm (k : Nat)
  | var : Fin k → ATerm k
  | zero : ATerm k
  | suc : ATerm k → ATerm k

/-- Formulas of arithmetic in `k` free variables (Goodsell, Definitions 3–8). -/
inductive AForm : Nat → Type
  | nat {k} : ATerm k → AForm k
  | sum {k} : ATerm k → ATerm k → ATerm k → AForm k
  | prod {k} : ATerm k → ATerm k → ATerm k → AForm k
  | eq {k} : ATerm k → ATerm k → AForm k
  | neg {k} : AForm k → AForm k
  | disj {k} : AForm k → AForm k → AForm k
  | conj {k} : AForm k → AForm k → AForm k
  /-- `∀v ∈ ℕ. φ`. -/
  | all {k} : AForm (k + 1) → AForm k

/-- An arithmetical term as a term of the pure language. -/
noncomputable def ATerm.toTerm {k : Nat} : ATerm k → Term Signature.pure (numCtx k) Ty.nu
  | .var i => .var (numVar i)
  | .zero => Arith.zero.term.close
  | .suc t => .app Arith.suc.term.close t.toTerm

/-- An arithmetical formula as a formula of the pure language. -/
noncomputable def AForm.toTerm : ∀ {k : Nat}, AForm k → Formula Signature.pure (numCtx k)
  | _, .nat t => .app Arith.N.term.close t.toTerm
  | _, .sum t u v => .app (.app (.app Arith.Sum.term.close t.toTerm) u.toTerm) v.toTerm
  | _, .prod t u v => .app (.app (.app Arith.Prod.term.close t.toTerm) u.toTerm) v.toTerm
  | _, .eq t u => Term.eq' t.toTerm u.toTerm
  | _, .neg φ => Term.neg φ.toTerm
  | _, .disj φ ψ => Term.disj φ.toTerm ψ.toTerm
  | _, .conj φ ψ => Term.conj φ.toTerm ψ.toTerm
  | _, .all φ => Term.forall' (Term.imp (.app Arith.N.term.close (.var .zero)) φ.toTerm)

/-- `I := ◇I*`, `I* := ∀m n ∈ ℕ. 𝟎_e ≠ Suc_e m ∧ (Suc_e m = Suc_e n → m = n)`: possibly zero is
not a successor and successor is injective on numbers. Built from the quoted terms. -/
noncomputable def arithI : Sentence Signature.pure :=
  let m : Term Signature.pure [Ty.nu, Ty.nu] Ty.nu := .var (.succ .zero)
  let n : Term Signature.pure [Ty.nu, Ty.nu] Ty.nu := .var .zero
  let s (t : Term Signature.pure [Ty.nu, Ty.nu] Ty.nu) := Term.app Arith.suc.term.close t
  let N (t : Term Signature.pure [Ty.nu, Ty.nu] Ty.nu) := Term.app Arith.N.term.close t
  Term.dia (Term.forall' (Term.forall' (Term.imp (N m) (Term.imp (N n)
    (Term.conj (Term.neg (Term.eq' Arith.zero.term.close (s m)))
      (Term.imp (Term.eq' (s m) (s n)) (Term.eq' m n)))))))

namespace AxiomSet

/-- **Necessity of Arithmetic**, in the pure language: `□(I → A) ∨ □(I → ¬A)` for each
arithmetical sentence `A`. -/
def necessityOfArithmetic : AxiomSet Signature.pure := fun a =>
  ∃ A : AForm 0, a = Term.disj (Term.box (Term.imp arithI A.toTerm))
    (Term.box (Term.imp arithI (Term.neg A.toTerm)))

end AxiomSet

/-! ### The arithmetical sentences are in the paper's language, and No Pure Contingency
gives Necessity of Arithmetic -/

theorem closedTypes_close {σ : Ty} {Γ : Ctx} (t : Term Signature.pure [] σ) (h : t.closedTypes = true) :
    (t.close : Term Signature.pure Γ σ).closedTypes = true := by
  rw [Term.closedTypes_rename]; exact h

theorem ATerm.closedTypes_toTerm : ∀ {k : Nat} (t : ATerm k), t.toTerm.closedTypes = true
  | _, .var _ => rfl
  | _, .zero => by
    show (Arith.zero.term.close : Term Signature.pure _ _).closedTypes = true
    exact closedTypes_close _ rfl
  | _, .suc t => by
    show (Term.app Arith.suc.term.close t.toTerm).closedTypes = true
    simp only [Term.closedTypes, closedTypes_close _ (rfl : Arith.suc.term.closedTypes = true),
      ATerm.closedTypes_toTerm t, Bool.and_self]

theorem AForm.closedTypes_toTerm : ∀ {k : Nat} (φ : AForm k), φ.toTerm.closedTypes = true
  | _, .nat t => by
    show (Term.app Arith.N.term.close t.toTerm).closedTypes = true
    simp only [Term.closedTypes, closedTypes_close _ (rfl : Arith.N.term.closedTypes = true),
      ATerm.closedTypes_toTerm t, Bool.and_self]
  | _, .sum t u v => by
    show (Term.app (Term.app (Term.app Arith.Sum.term.close t.toTerm) u.toTerm) v.toTerm).closedTypes = true
    simp only [Term.closedTypes, closedTypes_close _ (rfl : Arith.Sum.term.closedTypes = true),
      ATerm.closedTypes_toTerm, Bool.and_self]
  | _, .prod t u v => by
    show (Term.app (Term.app (Term.app Arith.Prod.term.close t.toTerm) u.toTerm) v.toTerm).closedTypes = true
    simp only [Term.closedTypes, closedTypes_close _ (rfl : Arith.Prod.term.closedTypes = true),
      ATerm.closedTypes_toTerm, Bool.and_self]
  | _, .eq t u => by
    show (Term.eq' t.toTerm u.toTerm).closedTypes = true
    simp [Term.closedTypes, ATerm.closedTypes_toTerm]
  | _, .neg φ => by
    show (Term.neg φ.toTerm).closedTypes = true
    simp [Term.closedTypes, AForm.closedTypes_toTerm φ]
  | _, .disj φ ψ => by
    show (Term.disj φ.toTerm ψ.toTerm).closedTypes = true
    simp [Term.closedTypes, AForm.closedTypes_toTerm φ, AForm.closedTypes_toTerm ψ]
  | _, .conj φ ψ => by
    show (Term.conj φ.toTerm ψ.toTerm).closedTypes = true
    simp [Term.closedTypes, AForm.closedTypes_toTerm φ, AForm.closedTypes_toTerm ψ]
  | _, .all φ => by
    show (Term.forall' (Term.imp (Term.app Arith.N.term.close (Term.var .zero)) φ.toTerm)).closedTypes = true
    simp [Term.closedTypes, closedTypes_close _ (rfl : Arith.N.term.closedTypes = true),
      AForm.closedTypes_toTerm φ]

theorem arithI_closedTypes : arithI.closedTypes = true := rfl

open AxiomSet in
/-- **No Pure Contingency gives Necessity of Arithmetic**: `I → A` and `I → ¬A` are closed pure
sentences, so each is necessary if true; and by excluded middle on `A` one of them is true. -/
theorem npc_entails_necessityOfArithmetic :
    noContingency Signature.pure ⟹ necessityOfArithmetic := by
  rintro _ ⟨A, rfl⟩
  have hA := A.closedTypes_toTerm
  have nc : ∀ p : Sentence Signature.pure, p.closedTypes = true →
      Theorem (C.axioms ∪ noContingency Signature.pure) (Term.imp p (Term.box p)) := fun p hp =>
    Theorem.ax ⟨by simp [Term.closedTypes, hp], p, rfl⟩
  have h1 := nc (Term.imp arithI A.toTerm) (by simp [Term.closedTypes, hA, arithI_closedTypes])
  have h2 := nc (Term.imp arithI (Term.neg A.toTerm))
    (by simp [Term.closedTypes, hA, arithI_closedTypes])
  refine Derivable.orE (Derivable.em A.toTerm) ?_ ?_
  · exact Derivable.orI₁ (Derivable.impE (Derivable.weaken₁ h1)
      (Derivable.impI (Derivable.hyp (by simp))))
  · exact Derivable.orI₂ (Derivable.impE (Derivable.weaken₁ h2)
      (Derivable.impI (Derivable.hyp (by simp))))

end Classicism.Meta

end
