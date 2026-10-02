import Classicism.Paper
import Classicism.Principles
import Classicism.Pointwise

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
upper bound of its lower bounds. Only the order is used, reflexive and transitive. -/

section booleanCompleteness
variable {τ : Type} [Rel τ] [Order τ] [Pointwise τ]

/-- `≤` is reflexive at a relational type: `X ⊆ X` under the box. -/
theorem le_refl_rel (x : τ) : x ≤ x :=
  (le_iff _ _).2 (nec% (boxImp_refl x))

/-- `≤` is transitive at a relational type: `⊆` is, under the box. -/
theorem le_trans_rel (x y z : τ) (h₁ : x ≤ y) (h₂ : y ≤ z) : x ≤ z :=
  (le_iff _ _).2 (modal_K _ _ (modal_K _ _ (nec% (boxImp_trans x y z))
    ((le_iff _ _).1 h₁)) ((le_iff _ _).1 h₂))

/-- The greatest lower bound of the upper bounds of `X` is a least upper bound of `X`. -/
theorem lub_of_glb_ubs (X : τ → Prop) (y : τ) (hy : GLB y (λ z ↦ UB z X)) : LUB y X :=
  fun z => ⟨fun hz => (hy y).2 (le_refl_rel y) z hz,
    fun hyz x hx => le_trans_rel x y z ((hy x).1 fun w hw => hw x hx) hyz⟩

/-- The least upper bound of the lower bounds of `X` is a greatest lower bound of `X`. -/
theorem glb_of_lub_lbs (X : τ → Prop) (y : τ) (hy : LUB y (λ z ↦ LB z X)) : GLB y X :=
  fun z => ⟨fun hz => (hy y).2 (le_refl_rel y) z hz,
    fun hzy x hx => le_trans_rel z y x hzy ((hy x).1 fun w hw => hw x hx)⟩

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
