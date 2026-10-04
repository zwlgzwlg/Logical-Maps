import Classicism.Principles.Coarse
import Classicism.Principles.Lattice

/-!
# Principles of the map's category `instances`

Principles stated at type `t` that the map keeps beside their versions at every type: each
is the instance at `Prop` of a principle of another category, and Atomlessness. See
`Classicism/Principles.lean` for how a principle is stated and where its forms go.
-/

namespace Classicism.P
open Classicism.Paper

/-- `distinctness-necessary-t`: ND at type `t`. -/
def NecessityOfDistinctnessT : Prop := NecessityOfDistinctness Prop
/-- `necessary-distinctness-necessary-t`: □ND at type `t`. -/
def NecNecessityOfDistinctnessT : Prop := □ NecessityOfDistinctnessT

/-- `barcan-t`: BF at type `t`. -/
def BarcanT : Prop := Barcan Prop
/-- `necessary-barcan-t`: □BF at type `t`. -/
def NecBarcanT : Prop := □ BarcanT

/-- `atomicity-t`: Atomicity at type `t`. -/
def AtomicityT : Prop := Atomicity Prop

/-- `atomlessness`: `∀p. ◇p → ∃q. ◇q ∧ q ≤ p ∧ q ≠ p`, every possible proposition has a
possible proposition strictly below it. -/
def Atomlessness : Prop := ∀ p : Prop, ◇ p → ∃ q : Prop, ◇ q ∧ q ≤ p ∧ q ≠ p

/-- `boolean-completeness-t`: Boolean Completeness at type `t`. -/
def BooleanCompletenessT : Prop := BooleanCompleteness Prop

/-- `strong-leibniz-t`. -/
def StrongLeibnizT : Prop := StrongLeibniz Prop
/-- `necessary-strong-leibniz-t`. -/
def NecStrongLeibnizT : Prop := □ StrongLeibnizT

end Classicism.P
