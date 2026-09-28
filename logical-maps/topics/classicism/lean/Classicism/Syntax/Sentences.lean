import Classicism.Syntax.Term

/-!
# Sentences the model theory checks

The map's type-indexed principles as closed sentences of the object language, written
once for the criteria the semantics states about them: `ND_σ`, `BF_σ`, the Fregean
Axiom, and Boolean Completeness. Each is a sentence over any signature.
-/

namespace Classicism.Meta

open Term

variable {Sig : Signature}

namespace Sentence

/-- `ND_σ`: `∀x y. x ≠ y → □(x ≠ y)`. -/
def nd (σ : Ty) : Sentence Sig :=
  forall' (σ := σ) (forall' (σ := σ) (imp (neg (eq' v1 v0)) (box (neg (eq' v1 v0)))))

/-- `BF_σ`: `∀X. (∀x. □Xx) → □∀x. Xx`. -/
def bf (σ : Ty) : Sentence Sig :=
  forall' (σ := σ ⇒ RTy.t)
    (imp (forall' (σ := σ) (box (app v1 v0))) (box (forall' (σ := σ) (app v1 v0))))

/-- The Fregean Axiom: `∀p q. (p ↔ q) → p = q`. -/
def fregean : Sentence Sig :=
  forall' (σ := Ty.rel .t) (forall' (σ := Ty.rel .t) (imp (iff v1 v0) (eq' v1 v0)))

/-- Boolean Completeness at `ρ`: `∀X ∃y ∀z. (∀u. Xu → z ≤ u) ↔ z ≤ y`, every property of
type `ρ → t` has a greatest lower bound, with `≤` as `leR`. The quoted
`P.BooleanCompleteness` is this sentence (`bc_quoted_eq`). -/
def bc (ρ : RTy) : Sentence Sig :=
  forall' (σ := Ty.rel (ρ ⇒ RTy.t)) (exists' (σ := ρ) (forall' (σ := ρ)
    (iff (forall' (σ := ρ) (imp (app (.var (.succ (.succ (.succ .zero)))) v0) (leR ρ v1 v0)))
      (leR ρ v0 v1))))

end Sentence

end Classicism.Meta
