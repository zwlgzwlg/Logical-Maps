import Classicism.Syntax.PossibilityPlus

/-!
# The Infinity schemas

The **Infinity schema** at a type `σ`: there are arbitrarily many pairwise distinct entities
of the type, one sentence for each positive integer `n`,

    ∃x₁ … xₙ. ⋀_{i<j} xᵢ ≠ xⱼ        (n ≥ 1)

(Classicism, §2.3, n. 47). The map records it at `e` and at `t`; the quantified Axioms of
Infinity, which imply it, are principles of the shallow layer (`Principles.lean`).
-/

namespace Classicism.Meta.AxiomSet

variable (Sig : Signature)

/-- The Infinity schema at `σ`: `∃x₁ … xₙ. ⋀_{i<j} xᵢ ≠ xⱼ` for each `n ≥ 1`. -/
def infinitySchema (σ : Ty) : AxiomSet Sig := fun a =>
  ∃ n : Nat, 1 ≤ n ∧
    a = Term.existsBlock (List.replicate n σ) (Term.distinct n (Terms.vars _ []))

/-- `infinity-e`: the Infinity schema at `e`. -/
def infinityE : AxiomSet Sig := infinitySchema Sig Ty.e

/-- `infinity-t`: the Infinity schema at `t`. -/
def infinityT : AxiomSet Sig := infinitySchema Sig Ty.t

end Classicism.Meta.AxiomSet
