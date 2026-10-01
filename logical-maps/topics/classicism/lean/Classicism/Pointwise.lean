import Classicism.Paper
import Classicism.Order

/-!
# Pointwise reasoning at a relational type

The paper reasons at a relational type `τ = σ₁ → ⋯ → σₙ → t` by writing tuples: `Y ≤ X`
is `□∀ȳ. Y[ȳ] → X[ȳ]`, and a step such as "`(w ∧ ȳ = x̄) → Xȳ` follows from `w → Xx̄` by
Leibniz's law" is propositional reasoning about the values at a tuple. The shallow layer
has no tuples: `Rel τ` supplies the pointwise operations `∧_τ`, `¬_τ`, `const_τ` and the
pointwise implication `boxImp` (`∀ȳ. X[ȳ] → Y[ȳ]`, unboxed) as *data*, and only the three
laws Intensionality needs. At a concrete type such as `σ → t` the operations unfold and
Lean's own tactics do the propositional reasoning; at a type *variable* `τ` nothing can be
said about them.

This class says what can be said: the pointwise implication is a preorder under which
`∧_τ` is a meet, `X ∧_τ ¬_τ X` is below everything, the constant relation at a
proposition is above everything when the proposition holds and below everything when it
fails, and coextension is implication both ways. These are the rules of natural deduction
read pointwise, and every "by Leibniz's law" and "under the box" of a proof at a
relational type is a short chain of them. The list is a basis, not a catalogue; a law
that is a consequence of these goes below as a theorem, and a law that is not can be
added as a field.

As with `Order`, the class is the shallow layer's way of stating a fact that is proved by
recursion on the structure of the type: the `Prop` instance is the base case and the
arrow instance the step. Its strict mirror is `SPointwise` in `Classicism/Mirror.lean`,
and the translator derives each law for every object type by induction on the type.
-/

namespace Classicism
open Paper

/-- The pointwise laws at a relational type. -/
class Pointwise (τ : Type) [Rel τ] : Type where
  /-- `X ⊑ X`. -/
  boxImp_refl : ∀ X : τ, X ⊆ X
  /-- `X ⊑ Y → Y ⊑ Z → X ⊑ Z`. -/
  boxImp_trans : ∀ X Y Z : τ, X ⊆ Y → Y ⊆ Z → X ⊆ Z
  /-- `Z ⊑ X → Z ⊑ Y → Z ⊑ X ∧_τ Y`. -/
  boxImp_and : ∀ X Y Z : τ, Z ⊆ X → Z ⊆ Y → Z ⊆ (X ∧ Y)
  /-- `X ∧_τ Y ⊑ X`. -/
  boxImp_and_left : ∀ X Y : τ, (X ∧ Y) ⊆ X
  /-- `X ∧_τ Y ⊑ Y`. -/
  boxImp_and_right : ∀ X Y : τ, (X ∧ Y) ⊆ Y
  /-- `X ∧_τ ¬_τ X ⊑ Y`: a contradiction at a tuple yields anything there. -/
  boxImp_and_neg : ∀ X Y : τ, (X ∧ ¬ X) ⊆ Y
  /-- `p → X ⊑ const_τ p`. -/
  boxImp_constP : ∀ (X : τ) (p : Prop), p → X ⊆ constP p
  /-- `¬p → const_τ p ⊑ X`. -/
  boxImp_of_constP : ∀ (X : τ) (p : Prop), ¬ p → constP p ⊆ X
  /-- `X ⊑ Y → Y ⊑ X → X ≡ Y`. -/
  coext_of_boxImp : ∀ X Y : τ, X ⊆ Y → Y ⊆ X → X ≡ Y
  /-- `X ≡ Y → X ⊑ Y`. -/
  boxImp_of_coext : ∀ X Y : τ, X ≡ Y → X ⊆ Y
  /-- `X ≡ Y → Y ⊑ X`. -/
  boxImp_of_coext' : ∀ X Y : τ, X ≡ Y → Y ⊆ X
  -- The modal laws, added 28 September for the results at every arity
  -- (`Results/Arity.lean`): each is a fact about `□` at `t`, read pointwise.
  /-- `□(X ⊑ Y) → ⊤ ⊑ □(¬X ∨ Y)`: the converse Barcan formula, pointwise. -/
  top_boxAt_of_box : ∀ X Y : τ, □ (boxImp X Y) → boxImp (Rel.top τ) (boxAt (Rel.or (Rel.neg X) Y))
  /-- `□X ⊑ □□X`: 4, pointwise. -/
  boxAt_four : ∀ X : τ, boxImp (boxAt X) (boxAt (boxAt X))
  /-- If every `q` is `□(¬w ∨ q)` exactly when true, `X` is coextensive with `λx̄. □(¬w ∨ X[x̄])`. -/
  coext_boxAt_actual : ∀ (X : τ) (w : Prop), (∀ q : Prop, q ↔ □ (¬ w ∨ q)) →
    coext X (boxAt (Rel.or (Rel.neg (constP w)) X))
  /-- `□X ⊑ X`: T, pointwise. -/
  boxAt_T : ∀ X : τ, boxImp (boxAt X) X
  /-- If every truth is necessary, `X ⊑ □X`. -/
  boxImp_boxAt_of_all : ∀ X : τ, (∀ p : Prop, p → □ p) → boxImp X (boxAt X)
  /-- With `B`, where `Y` fails and `□(Y → □Y)`, `Y` fails necessarily: `¬Y ⊑ □¬Y`. -/
  neg_boxImp_boxAt_of_b : ∀ Y : τ, (∀ p : Prop, p → □ ◇ p) →
    boxImp (Rel.top τ) (boxAt (Rel.or (Rel.neg Y) (boxAt Y))) → boxImp (Rel.neg Y) (boxAt (Rel.neg Y))

export Pointwise (boxImp_refl boxImp_trans boxImp_and boxImp_and_left boxImp_and_right
  boxImp_and_neg boxImp_constP boxImp_of_constP coext_of_boxImp boxImp_of_coext
  boxImp_of_coext' top_boxAt_of_box boxAt_four
  coext_boxAt_actual boxAt_T boxImp_boxAt_of_all neg_boxImp_boxAt_of_b)

/-! ### Type `t`

Each law is a propositional fact about `p → q`, `p ∧ q`, `¬p`, `p ↔ q`. They are stated
as theorems of their own so that the strict mirror can take its laws from their
transforms. -/

theorem boxImp_refl_prop (X : Prop) : X ⊆ X := fun h => h
theorem boxImp_trans_prop (X Y Z : Prop) : X ⊆ Y → Y ⊆ Z → X ⊆ Z :=
  fun h₁ h₂ h => h₂ (h₁ h)
theorem boxImp_and_prop (X Y Z : Prop) : Z ⊆ X → Z ⊆ Y → Z ⊆ Rel.and X Y :=
  fun h₁ h₂ h => ⟨h₁ h, h₂ h⟩
theorem boxImp_and_left_prop (X Y : Prop) : Rel.and X Y ⊆ X := fun h => h.1
theorem boxImp_and_right_prop (X Y : Prop) : Rel.and X Y ⊆ Y := fun h => h.2
theorem boxImp_and_neg_prop (X Y : Prop) : (Rel.and X (Rel.neg X)) ⊆ Y :=
  fun h => absurd h.1 h.2
theorem boxImp_constP_prop (X : Prop) (p : Prop) : p → X ⊆ constP p := fun hp _ => hp
theorem boxImp_of_constP_prop (X : Prop) (p : Prop) : ¬ p → constP p ⊆ X :=
  fun hn hp => absurd hp hn
theorem coext_of_boxImp_prop (X Y : Prop) : X ⊆ Y → Y ⊆ X → X ≡ Y :=
  fun h₁ h₂ => ⟨h₁, h₂⟩
theorem boxImp_of_coext_prop (X Y : Prop) : X ≡ Y → X ⊆ Y := fun h => h.1
theorem boxImp_of_coext'_prop (X Y : Prop) : X ≡ Y → Y ⊆ X := fun h => h.2

theorem not_or_of_imp (x y : Prop) : (x → y) → ¬ x ∨ y :=
  fun h => (em x).elim (fun hx => Or.inr (h hx)) (fun hn => Or.inl hn)

theorem top_boxAt_of_box_prop (X Y : Prop) :
    □ (X ⊆ Y) → Rel.top Prop ⊆ boxAt (Rel.or (Rel.neg X) Y) :=
  fun h _ => modal_K _ _ (nec% (not_or_of_imp X Y)) h
theorem boxAt_four_prop (X : Prop) : boxAt X ⊆ boxAt (boxAt X) := modal_four X
theorem coext_boxAt_actual_prop (X w : Prop) : (∀ q : Prop, q ↔ □ (¬ w ∨ q)) →
    X ≡ boxAt (Rel.or (Rel.neg (constP w)) X) := fun h => h X
theorem neg_of_dia_neg_persist (y : Prop) : ◇ (¬ y) → (¬ y ∨ □ y) → ¬ y :=
  fun hd h => Or.elim h (fun hn => hn) (fun hb => (hd (by rw [hb]; exact not_true_eq)).elim)
theorem boxAt_T_prop (X : Prop) : boxAt X ⊆ X := fun h => box_elim h
theorem boxImp_boxAt_of_all_prop (X : Prop) : (∀ p : Prop, p → □ p) → X ⊆ boxAt X :=
  fun h hx => h X hx
theorem neg_boxImp_boxAt_of_b_prop (Y : Prop) : (∀ p : Prop, p → □ ◇ p) →
    Rel.top Prop ⊆ boxAt (Rel.or (Rel.neg Y) (boxAt Y)) → Rel.neg Y ⊆ boxAt (Rel.neg Y) :=
  fun b h hny => modal_K _ _ (modal_K _ _ (nec% (neg_of_dia_neg_persist Y)) (b _ hny)) (h trivial)

instance instPointwiseProp : Pointwise Prop where
  boxImp_refl := boxImp_refl_prop
  boxImp_trans := boxImp_trans_prop
  boxImp_and := boxImp_and_prop
  boxImp_and_left := boxImp_and_left_prop
  boxImp_and_right := boxImp_and_right_prop
  boxImp_and_neg := boxImp_and_neg_prop
  boxImp_constP := boxImp_constP_prop
  boxImp_of_constP := boxImp_of_constP_prop
  coext_of_boxImp := coext_of_boxImp_prop
  boxImp_of_coext := boxImp_of_coext_prop
  boxImp_of_coext' := boxImp_of_coext'_prop
  top_boxAt_of_box := top_boxAt_of_box_prop
  boxAt_four := boxAt_four_prop
  coext_boxAt_actual := coext_boxAt_actual_prop
  boxAt_T := boxAt_T_prop
  boxImp_boxAt_of_all := boxImp_boxAt_of_all_prop
  neg_boxImp_boxAt_of_b := neg_boxImp_boxAt_of_b_prop

/-! ### Relational function types

At `σ → τ` the operations are pointwise and `boxImp X Y` is `∀z. X z ⊑ Y z`, so each law is
the law at `τ` under a `∀`. -/

section arrow
variable {σ τ : Type} [Ty σ] [Rel τ] [Pointwise τ]

theorem boxImp_refl_arrow (X : σ → τ) : X ⊆ X := fun z => boxImp_refl (X z)
theorem boxImp_trans_arrow (X Y Z : σ → τ) : X ⊆ Y → Y ⊆ Z → X ⊆ Z :=
  fun h₁ h₂ z => boxImp_trans (X z) (Y z) (Z z) (h₁ z) (h₂ z)
theorem boxImp_and_arrow (X Y Z : σ → τ) :
    Z ⊆ X → Z ⊆ Y → Z ⊆ (X ∧ Y) :=
  fun h₁ h₂ z => boxImp_and (X z) (Y z) (Z z) (h₁ z) (h₂ z)
theorem boxImp_and_left_arrow (X Y : σ → τ) : (X ∧ Y) ⊆ X :=
  fun z => boxImp_and_left (X z) (Y z)
theorem boxImp_and_right_arrow (X Y : σ → τ) : (X ∧ Y) ⊆ Y :=
  fun z => boxImp_and_right (X z) (Y z)
theorem boxImp_and_neg_arrow (X Y : σ → τ) : (X ∧ ¬ X) ⊆ Y :=
  fun z => boxImp_and_neg (X z) (Y z)
theorem boxImp_constP_arrow (X : σ → τ) (p : Prop) : p → X ⊆ constP p :=
  fun hp z => boxImp_constP (X z) p hp
theorem boxImp_of_constP_arrow (X : σ → τ) (p : Prop) : ¬ p → constP p ⊆ X :=
  fun hn z => boxImp_of_constP (X z) p hn
theorem coext_of_boxImp_arrow (X Y : σ → τ) : X ⊆ Y → Y ⊆ X → X ≡ Y :=
  fun h₁ h₂ z => coext_of_boxImp (X z) (Y z) (h₁ z) (h₂ z)
theorem boxImp_of_coext_arrow (X Y : σ → τ) : X ≡ Y → X ⊆ Y :=
  fun h z => boxImp_of_coext (X z) (Y z) (h z)
theorem boxImp_of_coext'_arrow (X Y : σ → τ) : X ≡ Y → Y ⊆ X :=
  fun h z => boxImp_of_coext' (X z) (Y z) (h z)

theorem top_boxAt_of_box_arrow (X Y : σ → τ) :
    □ (X ⊆ Y) → Rel.top (σ → τ) ⊆ boxAt (Rel.or (Rel.neg X) Y) :=
  fun h z => top_boxAt_of_box (X z) (Y z) (converse_barcan (λ z ↦ X z ⊆ Y z) h z)
theorem boxAt_four_arrow (X : σ → τ) : boxAt X ⊆ boxAt (boxAt X) := fun z => boxAt_four (X z)
theorem coext_boxAt_actual_arrow (X : σ → τ) (w : Prop) : (∀ q : Prop, q ↔ □ (¬ w ∨ q)) →
    X ≡ boxAt (Rel.or (Rel.neg (constP w)) X) := fun h z => coext_boxAt_actual (X z) w h
theorem boxAt_T_arrow (X : σ → τ) : boxAt X ⊆ X := fun z => boxAt_T (X z)
theorem boxImp_boxAt_of_all_arrow (X : σ → τ) : (∀ p : Prop, p → □ p) → X ⊆ boxAt X :=
  fun h z => boxImp_boxAt_of_all (X z) h
theorem neg_boxImp_boxAt_of_b_arrow (Y : σ → τ) : (∀ p : Prop, p → □ ◇ p) →
    Rel.top (σ → τ) ⊆ boxAt (Rel.or (Rel.neg Y) (boxAt Y)) → Rel.neg Y ⊆ boxAt (Rel.neg Y) :=
  fun b h z => neg_boxImp_boxAt_of_b (Y z) b (h z)

instance instPointwiseArrow : Pointwise (σ → τ) where
  boxImp_refl := boxImp_refl_arrow
  boxImp_trans := boxImp_trans_arrow
  boxImp_and := boxImp_and_arrow
  boxImp_and_left := boxImp_and_left_arrow
  boxImp_and_right := boxImp_and_right_arrow
  boxImp_and_neg := boxImp_and_neg_arrow
  boxImp_constP := boxImp_constP_arrow
  boxImp_of_constP := boxImp_of_constP_arrow
  coext_of_boxImp := coext_of_boxImp_arrow
  boxImp_of_coext := boxImp_of_coext_arrow
  boxImp_of_coext' := boxImp_of_coext'_arrow
  top_boxAt_of_box := top_boxAt_of_box_arrow
  boxAt_four := boxAt_four_arrow
  coext_boxAt_actual := coext_boxAt_actual_arrow
  boxAt_T := boxAt_T_arrow
  boxImp_boxAt_of_all := boxImp_boxAt_of_all_arrow
  neg_boxImp_boxAt_of_b := neg_boxImp_boxAt_of_b_arrow

end arrow

/-! ### Consequences, at any relational type -/

section consequences
variable {τ : Type} [Rel τ] [Pointwise τ]

/-- `Z ⊑ X ∧_τ Y → Z ⊑ X`. -/
theorem boxImp_and_elim_left (X Y Z : τ) : Z ⊆ (X ∧ Y) → Z ⊆ X :=
  fun h => boxImp_trans Z (X ∧ Y) X h (boxImp_and_left X Y)

/-- `Z ⊑ X ∧_τ Y → Z ⊑ Y`. -/
theorem boxImp_and_elim_right (X Y Z : τ) : Z ⊆ (X ∧ Y) → Z ⊆ Y :=
  fun h => boxImp_trans Z (X ∧ Y) Y h (boxImp_and_right X Y)

/-- `X ⊑ ¬_τ X → X ⊑ Y`: what is below its own negation is below everything. -/
theorem boxImp_of_boxImp_neg (X Y : τ) : X ⊆ ¬ X → X ⊆ Y :=
  fun h => boxImp_trans X (X ∧ ¬ X) Y
    (boxImp_and X (¬ X) X (boxImp_refl X) h) (boxImp_and_neg X Y)

/-- `X ⊑ Y → Y ⊑ ¬_τ Y → X ⊑ ¬_τ X`. -/
theorem boxImp_neg_of_boxImp (X Y : τ) :
    X ⊆ Y → Y ⊆ ¬ Y → X ⊆ ¬ X :=
  fun h₁ h₂ => boxImp_trans X (Y ∧ ¬ Y) (¬ X)
    (boxImp_and Y (¬ Y) X h₁ (boxImp_trans X Y (¬ Y) h₁ h₂))
    (boxImp_and_neg Y (¬ X))

/-- `p → X ⊑ X ∧_τ const_τ p`. -/
theorem boxImp_and_constP_self (X : τ) (p : Prop) : p → X ⊆ (X ∧ constP p) :=
  fun hp => boxImp_and X (constP p) X (boxImp_refl X) (boxImp_constP X p hp)

/-- `¬p → X ∧_τ const_τ p ⊑ Y`. -/
theorem boxImp_of_and_constP (X Y : τ) (p : Prop) : ¬ p → (X ∧ constP p) ⊆ Y :=
  fun hn => boxImp_trans (X ∧ constP p) (constP p) Y
    (boxImp_and_right X (constP p)) (boxImp_of_constP Y p hn)

/-- `p → X ∧_τ const_τ p ⊑ ¬_τ (X ∧_τ const_τ p) → X ⊑ ¬_τ X`. -/
theorem boxImp_neg_of_and_constP (X : τ) (p : Prop) :
    p → (X ∧ constP p) ⊆ (¬ (X ∧ constP p)) → X ⊆ ¬ X :=
  fun hp h => boxImp_neg_of_boxImp X (X ∧ constP p) (boxImp_and_constP_self X p hp) h

end consequences

end Classicism
