import Classicism.Order

/-!
# Lattice predicates

The map's Background defines, at a relational type `τ` with the algebraic order `≤_τ`,

    Atom_τ(y) := ∀z. (z ≤_τ y ∧ z ≠ y) ↔ z ≤_τ ¬_τ z

so that an atom is non-bottom (`z ≤ ¬z` says `z = ⊥`) and has no non-bottom strict lower
bound (*Classicism*, §2.2, pp. 23–24). The predicate needs only `Rel τ`, since the order is
the algebraic one; its pointwise reading is through `Order.le_iff`.
-/

namespace Classicism

variable {τ : Type} [Rel τ]

/-- `Atom_τ(y) := ∀z. (z ≤ y ∧ z ≠ y) ↔ z ≤ ¬z`. -/
def Atom (y : τ) : Prop := ∀ z : τ, (Rel.le z y ∧ z ≠ y) ↔ Rel.le z (Rel.neg z)

/-- An atom is not below its own negation: it is not `⊥`. -/
theorem not_le_neg_of_atom {y : τ} (h : Atom y) : ¬ Rel.le y (Rel.neg y) :=
  fun hy => ((h y).2 hy).2 rfl

end Classicism
