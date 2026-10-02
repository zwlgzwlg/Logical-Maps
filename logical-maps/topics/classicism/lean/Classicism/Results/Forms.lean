import Classicism.Paper
import Classicism.Principles

/-!
# Equivalent forms of the principles

A principle of the map has one official form and may have others, equivalent to it: the
LUB form of Boolean Completeness beside its GLB form, the list form of a principle stated
for one argument type, a dual. This file proves the equivalences that need a shallow proof,
one section per principle, each direction a record certified like those of
`Results/Records.lean` (the audits run over this module too). A form's definition sits
beside the official one in `Principles.lean`; its certificate, at the statement the map
generates for the equivalence, is in `Map.lean`.

The list forms are not here: they are defined by vectorization, one direction is by
inclusion and the other by an induction on the list (`Results/Lists.lean`).
-/

namespace Classicism.Proofs
open Classicism.P Classicism.Paper

/-! ## Boolean Completeness: the GLB and LUB forms

At any relational type, every property having a greatest lower bound and every property
having a least upper bound come to the same thing: the least upper bound of `X` is the
greatest lower bound of its upper bounds, and the greatest lower bound of `X` the least
upper bound of its lower bounds (`lub_of_glb_ubs`, `glb_of_lub_lbs`, in `Lattice.lean`). -/

section booleanCompleteness
variable {τ : Type} [Rel τ] [Order τ] [Pointwise τ]

/-- Boolean Completeness, from its official (GLB) form to its LUB form. -/
theorem boolean_completeness_implies_lub_form :
    BooleanCompleteness τ → BooleanCompletenessLUB τ := fun bc X =>
  (bc (λ z ↦ UB z X)).elim fun y hy => ⟨y, lub_of_glb_ubs X y hy⟩

/-- Boolean Completeness, from its LUB form to its official (GLB) form. -/
theorem lub_form_implies_boolean_completeness :
    BooleanCompletenessLUB τ → BooleanCompleteness τ := fun bc X =>
  (bc (λ z ↦ LB z X)).elim fun y hy => ⟨y, glb_of_lub_lbs X y hy⟩

end booleanCompleteness

end Classicism.Proofs
