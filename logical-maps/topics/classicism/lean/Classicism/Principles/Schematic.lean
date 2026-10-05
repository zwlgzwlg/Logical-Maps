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
/-- `◇_≠p := ¬□_≠¬p`, its dual possibility. -/
def DiaNe (p : Prop) : Prop := ¬ BoxNe (¬ p)

/-- `distinctness-preserving-collapse`: `∀p. p → □_≠p`. -/
def DistinctnessPreservingCollapse : Prop := ∀ p : Prop, p → BoxNe p
/-- `distinctness-preserving-collapse`, form `dual`: `∀p. ◇_≠p → p`. -/
def DistinctnessPreservingCollapseDual : Prop := ∀ p : Prop, DiaNe p → p

/-- `distinctness-preserving-collapse` to its dual form: the collapse at `¬p`, contraposed. -/
theorem DistinctnessPreservingCollapse.to_dual :
    DistinctnessPreservingCollapse → DistinctnessPreservingCollapseDual := fun c p h =>
  (em p).elim (fun hp => hp) fun hn => absurd (c (¬ p) hn) h

/-- `distinctness-preserving-collapse` from its dual form: the dual at `¬p`, contraposed,
with `¬¬p = p`. -/
theorem DistinctnessPreservingCollapse.of_dual :
    DistinctnessPreservingCollapseDual → DistinctnessPreservingCollapse := fun d p hp =>
  (em (BoxNe p)).elim (fun h => h) fun hn =>
    absurd hp (d (¬ p) (by show ¬ BoxNe (¬ ¬ p); rw [not_not_eq]; exact hn))

end Classicism.P
