import Classicism.Syntax.Term

/-!
# Sentences the model theory checks

The map's type-indexed principles as closed sentences of the object language, written
once for the criteria the semantics states about them: `ND_σ`, `BF_σ` and the Fregean
Axiom. Each is a sentence over any signature.
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

end Sentence

end Classicism.Meta
