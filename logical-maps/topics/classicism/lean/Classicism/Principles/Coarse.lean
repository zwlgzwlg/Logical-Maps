import Classicism.Paper
import Classicism.Comprehension
import Classicism.Lattice

/-!
# Principles of the map's category `coarse`

The modal principles `B` and `5`, the Necessity of Distinctness, the Barcan Formula and
Tractarianism, with their boxed forms. See `Classicism/Principles.lean` for how a principle
is stated and where its forms go.

The scope `Classicism.Paper` is not opened here. These principles are about `t` and the
types of individuals, where its symbols would change nothing, except Tractarianism, whose
`≤` at `Prop` is `entails` (`Core.lean`): inside the scope it would be `Rel.le`, the same
relation by definition but a different constant, and the principle's quoted sentence would
change with it.
-/

namespace Classicism.P

/-! ## `B` and `5` -/

/-- `modal-five`: `∀p. ◇p → □◇p`. -/
def ModalFive : Prop := ∀ p : Prop, ◇ p → □ ◇ p
/-- `modal-b`: `∀p. p → □◇p`. -/
def ModalB : Prop := ∀ p : Prop, p → □ ◇ p
/-- `necessary-modal-b`: `B` boxed. -/
def NecModalB : Prop := □ ModalB
/-- `necessary-modal-five`: `5` boxed. -/
def NecModalFive : Prop := □ ModalFive

/-! ## The Necessity of Distinctness -/

/-- `distinctness-necessary-r` (ND) at `σ`: `∀xy. x ≠ y → □(x ≠ y)`. -/
def NecessityOfDistinctness (σ : Type) [Ty σ] : Prop := ∀ x y : σ, x ≠ y → □ (x ≠ y)
/-- `necessary-distinctness-necessary-r`: □ND at `σ`. -/
def NecNecessityOfDistinctness (σ : Type) [Ty σ] : Prop := □ (NecessityOfDistinctness σ)

/-! ## The Barcan Formula -/

/-- `barcan-r` (BF) at `σ`: `∀X. (∀x. □Xx) → □(∀x. Xx)`. -/
def Barcan (σ : Type) [Ty σ] : Prop := ∀ X : σ → Prop, (∀ x, □ (X x)) → □ (∀ x, X x)
/-- `necessary-barcan-r`: □BF at `σ`. -/
def NecBarcan (σ : Type) [Ty σ] : Prop := □ (Barcan σ)

/-! ## Tractarianism -/

/-- `tractarianism-r` at `σ`: `∀pX. (∀x. p ≤ Xx) → p ≤ ∀x. Xx`. -/
def Tractarianism (σ : Type) [Ty σ] : Prop :=
  ∀ (p : Prop) (X : σ → Prop), (∀ x, p ≤ X x) → p ≤ (∀ x, X x)
/-- `necessary-tractarianism-r` at `σ`. -/
def NecTractarianism (σ : Type) [Ty σ] : Prop := □ (Tractarianism σ)

end Classicism.P
