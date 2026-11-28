import Classicism.Syntax.Axioms
import Classicism.Syntax.Blocks

/-! The Russell–Myhill witness at an arbitrary relation type. -/

namespace Classicism.Meta.Diagonal

open Term

variable {Sig : Signature}

/-- The Russell predicate attached to a closed operator. -/
def russell {s : RTy} (q : Term Sig [] (((s : Ty) ⇒ RTy.t) ⇒ s)) :
    Term Sig [] ((s : Ty) ⇒ RTy.t) :=
  .lam (exists' (conj (eq' (.app q.close v0) v1) (neg (.app v0 v1))))

private theorem subst_close {σ : Ty} {Γ Δ : Ctx} (q : Term Sig [] σ) (s : Sub Sig Γ Δ) :
    q.close.subst s = q.close := by
  rw [Term.close, Term.subst_rename, Term.close, Term.rename_eq_subst]
  congr 1
  funext τ v; cases v

private theorem closed_weaken {σ τ : Ty} (q : Term Sig [] σ) :
    q.weaken (τ := τ) = q.close := by
  unfold Term.weaken Term.close

  apply congrArg (fun r => q.rename r)
  funext σ v; cases v

private theorem russell_beta {s : RTy} (q : Term Sig [] (((s : Ty) ⇒ RTy.t) ⇒ s))
    (x : Term Sig [] s) :
    (.app (russell q) x) ≡
      exists' (conj (eq' (.app q.close v0) x.close) (neg (.app v0 x.close))) := by
  apply Conv.trans (Conv.beta _ x)
  apply Conv.of_eq
  simp [instantiate, exists', conj, eq', neg, subst_close, closed_weaken]

private theorem matrix_beta {s : RTy} (q : Term Sig [] (((s : Ty) ⇒ RTy.t) ⇒ s))
    (x : Term Sig [] s) (f : Term Sig [] ((s : Ty) ⇒ RTy.t)) :
    (.app (.lam (conj (eq' (.app q.close v0) x.close) (neg (.app v0 x.close)))) f) ≡
      conj (eq' (.app q f) x) (neg (.app f x)) := by
  apply Conv.trans (Conv.beta _ f)
  apply Conv.of_eq
  simp [instantiate, conj, eq', neg, subst_close]

/-- Russell's witness is a theorem in the native derivation calculus at every signature. -/
theorem russell_self {s : RTy} (q : Term Sig [] (((s : Ty) ⇒ RTy.t) ⇒ s))
    {Ax : AxiomSet Sig} {Δ : List (Sentence Sig)} :
    Derivable Ax Δ (.app (russell q) (.app q (russell q))) := by
  let r := russell q
  let x := Term.app q r
  let p := Term.app r x
  change Derivable Ax Δ p
  apply Derivable.orE (.em p) (.hyp List.mem_cons_self)
  apply Derivable.conv _ (Conv.symm (russell_beta q x))
  apply Derivable.exI r
  apply Derivable.conv _ (Conv.symm (matrix_beta q x r))
  exact Derivable.andI (.refl x) (.hyp List.mem_cons_self)

end Classicism.Meta.Diagonal
