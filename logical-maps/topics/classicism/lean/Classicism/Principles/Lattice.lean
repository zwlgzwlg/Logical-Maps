import Classicism.Paper
import Classicism.Comprehension
import Classicism.Lattice
import Classicism.Cardinality

/-!
# Principles of the map's category `lattice`

Atomicity, Boolean Completeness and Countable Boolean Completeness, Actuality, Actual
Profile, Vicinity and the Strong Leibniz Biconditionals, with their boxed forms: what the
order `≤_τ` at a relational type is like. See `Classicism/Principles.lean` for how a
principle is stated and where its forms go.
-/

namespace Classicism.P
open Classicism.Paper

/-! ## Atomicity -/

/-- `atomicity-r` at `τ`: `∀x. x ≤ ¬x ∨ ∃y. Atom(y) ∧ y ≤ x`, every non-bottom entity has
an atom below it. -/
def Atomicity (τ : Type) [Rel τ] : Prop :=
  ∀ x : τ, x ≤ ¬ x ∨ ∃ y : τ, Atom y ∧ y ≤ x
/-- `necessary-atomicity-r` at `τ`: the instance boxed. -/
def NecAtomicity (τ : Type) [Rel τ] : Prop := □ (Atomicity τ)

/-! ## Boolean Completeness -/

/-- `boolean-completeness-r` at `τ`: `∀X. ∃y. GLB_τ(y, X)`, every property of entities
of the type has a greatest lower bound. -/
def BooleanCompleteness (τ : Type) [Rel τ] : Prop := ∀ X : τ → Prop, ∃ y : τ, GLB y X
/-- Boolean Completeness, its LUB form: `∀X. ∃y. LUB_τ(y, X)`, every property of entities
of the type has a least upper bound. Equivalent to the official form, at each type
(`Results/Forms.lean`). -/
def BooleanCompletenessLUB (τ : Type) [Rel τ] : Prop := ∀ X : τ → Prop, ∃ y : τ, LUB y X
/-- `necessary-boolean-completeness-r` at `τ`: the instance boxed. -/
def NecBooleanCompleteness (τ : Type) [Rel τ] : Prop := □ (BooleanCompleteness τ)

/-- `countable-boolean-completeness-r` at `τ`: every countable property of entities of the
type has a least upper bound. -/
def CountableBooleanCompleteness (τ : Type) [Rel τ] : Prop :=
  ∀ X : τ → Prop, Ctbl X → ∃ y : τ, LUB y X

/-! ## Actuality, Actual Profile and Vicinity -/

/-- `actuality`: `∃p. p ∧ ∀q. q → p ≤ q`, there is a true proposition that entails every
truth — a true atom, an actual world. -/
def Actuality : Prop := ∃ p : Prop, p ∧ ∀ q : Prop, q → p ≤ q
/-- `necessary-actuality`: Actuality boxed. -/
def NecActuality : Prop := □ Actuality

/-- `actual-profile-r` at `σ`, for one argument: `∀x. ∃Y. Yx ∧ ∀Z. Zx → Y ≤ Z`, every
individual of the type has a true property entailing every property it has. The map's
principle is over finite argument tuples; this is the unary instance, and its nullary
instance is Actuality itself. -/
def ActualProfile (σ : Type) [Ty σ] : Prop :=
  ∀ x : σ, ∃ Y : σ → Prop, Y x ∧ ∀ Z : σ → Prop, Z x → Y ≤ Z

/-- `vicinity`: `∃p. p ∧ ∀q. q → p ≤ ◇q`, a true proposition entails the possibility of
each truth. -/
def Vicinity : Prop := ∃ p : Prop, p ∧ ∀ q : Prop, q → p ≤ ◇ q
/-- `necessary-vicinity`: Vicinity boxed. -/
def NecVicinity : Prop := □ Vicinity

/-! ## The Strong Leibniz Biconditionals -/

/-- `SWorld_τ(W) := ◇_τ W ∧ □∀Y. W ≤ Y ∨ W ≤ ¬Y`, with `◇_τ W := W ≠ ⊥_τ` (Bacon §8.2). -/
def SWorld {τ : Type} [Rel τ] (W : τ) : Prop :=
  W ≠ ⊥ ∧ □ (∀ Y : τ, W ≤ Y ∨ W ≤ ¬ Y)
/-- `strong-leibniz-r` at `τ`: every possible entity is entailed by a strong world. -/
def StrongLeibniz (τ : Type) [Rel τ] : Prop :=
  ∀ X : τ, X ≠ ⊥ → ∃ W : τ, SWorld W ∧ W ≤ X
/-- `necessary-strong-leibniz-r` at `τ`. -/
def NecStrongLeibniz (τ : Type) [Rel τ] : Prop := □ (StrongLeibniz τ)

end Classicism.P
