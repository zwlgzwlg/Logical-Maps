import Classicism.Paper
import Classicism.Comprehension
import Classicism.Lattice

/-!
# Principles of the map's category `base`

Theorems of Classicism among the map's principles: the modal logic `K`, `T`, `4` of the
defined box, the Necessity of Identity, the Converse Barcan Formula, Existence, Broad
Necessitism, and the coarse-grainedness principles every model of `C` satisfies,
Intensionality and its corollaries. See `Classicism/Principles.lean` for how a principle is
stated and where its forms go.
-/

namespace Classicism.P

/-! ## Modal principles, at type `t` -/

/-- `modal-k`: `∀pq. □(p→q) → (□p → □q)`. -/
def ModalK : Prop := ∀ p q : Prop, □ (p → q) → □ p → □ q
/-- `modal-t`: `∀p. □p → p`. -/
def ModalT : Prop := ∀ p : Prop, □ p → p
/-- `modal-four`: `∀p. □p → □□p`. -/
def ModalFour : Prop := ∀ p : Prop, □ p → □ □ p
/-- `modalized-fregean`: `∀pq. □(p↔q) → p = q`. -/
def ModalizedFregean : Prop := ∀ p q : Prop, □ (p ↔ q) → p = q

/-! ## Coarse-grainedness principles of `C`, at a type -/

/-- `intensionality-r` at the relational type `τ`: `□(∀z̄. X[z̄] ↔ Y[z̄]) → X = Y`. -/
def Intensionality (τ : Type) [Rel τ] : Prop := ∀ X Y : τ, □ (coext X Y) → X = Y
/-- `modalized-functionality-r` at `σ → τ`: `□(∀z. Xz = Yz) → X = Y`. -/
def ModalizedFunctionality (σ τ : Type) [Ty σ] [Rel τ] : Prop :=
  ∀ X Y : σ → τ, □ (∀ z, X z = Y z) → X = Y
/-- `identity-necessary-r` (NI) at `σ`: `∀xy. x = y → □(x = y)`. -/
def NecessityOfIdentity (σ : Type) [Ty σ] : Prop := ∀ x y : σ, x = y → □ (x = y)
/-- `converse-barcan-r` (CBF) at `σ`: `∀X. □(∀x. Xx) → ∀x. □Xx`. -/
def ConverseBarcan (σ : Type) [Ty σ] : Prop := ∀ X : σ → Prop, □ (∀ x, X x) → ∀ x, □ (X x)
/-- `existence-r` at `σ`: `∃x^σ. x = x`. The type system has two shapes of type, `e` and
the relational types; `Existence e` is the axiom `e_exists`, and `Existence τ` for
relational `τ` is a theorem of `C⁻`. The two instances are the two records' proofs. -/
def Existence (σ : Type) [Ty σ] : Prop := ∃ x : σ, x = x
/-- `broad-necessitism-r` at `σ`: `∀x. □∃y. y = x`. -/
def BroadNecessitism (σ : Type) [Ty σ] : Prop := ∀ x : σ, □ (∃ y : σ, y = x)

end Classicism.P
