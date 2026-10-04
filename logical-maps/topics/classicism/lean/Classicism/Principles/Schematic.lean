import Classicism.Paper
import Classicism.Comprehension
import Classicism.Lattice

/-!
# Principles of the map's category `schematic`

The one principle of this category with a shallow statement, the Distinctness-Preserving
Collapse of §2.6. The others are sentence schemas, defined in the object language
(`Syntax/SentenceSchemas.lean` and its neighbours). See `Classicism/Principles.lean` for
how a principle is stated and where its forms go.
-/

namespace Classicism.P

/-- `□_≠p := ∃q. q ∧ □(◇q → p)`, the distinctness-preserving necessity (Classicism, §2.6). -/
def BoxNe (p : Prop) : Prop := ∃ q : Prop, q ∧ □ (◇ q → p)
/-- `distinctness-preserving-collapse`: `∀p. p → □_≠p`. -/
def DistinctnessPreservingCollapse : Prop := ∀ p : Prop, p → BoxNe p

end Classicism.P
