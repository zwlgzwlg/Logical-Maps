import Classicism.Paper
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
open Paper

variable {τ : Type} [Rel τ]

/-- `Atom_τ(y) := ∀z. (z ≤ y ∧ z ≠ y) ↔ z ≤ ¬z`. -/
def Atom (y : τ) : Prop := ∀ z : τ, (z ≤ y ∧ z ≠ y) ↔ z ≤ ¬ z

/-- An atom is not below its own negation: it is not `⊥`. -/
theorem not_le_neg_of_atom {y : τ} (h : Atom y) : ¬ y ≤ ¬ y :=
  fun hy => ((h y).2 hy).2 rfl

/-! ### Bounds

The Background's `LB_τ(y, X) := ∀z. Xz → y ≤ z` and `GLB_τ(y, X) := ∀z. LB(z, X) ↔ z ≤ y`,
and the dual pair with `UB` and `LUB`, in which some of the map's proofs state Boolean
Completeness. -/

/-- `LB_τ(y, X) := ∀z. Xz → y ≤ z`. -/
def LB (y : τ) (X : τ → Prop) : Prop := ∀ z : τ, X z → y ≤ z
/-- `GLB_τ(y, X) := ∀z. LB(z, X) ↔ z ≤ y`. -/
def GLB (y : τ) (X : τ → Prop) : Prop := ∀ z : τ, LB z X ↔ z ≤ y
/-- `UB_τ(y, X) := ∀z. Xz → z ≤ y`. -/
def UB (y : τ) (X : τ → Prop) : Prop := ∀ z : τ, X z → z ≤ y
/-- `LUB_τ(y, X) := ∀z. UB(z, X) ↔ y ≤ z`. -/
def LUB (y : τ) (X : τ → Prop) : Prop := ∀ z : τ, UB z X ↔ y ≤ z

/-- `w` is an actual world: a truth that entails every truth, `w ∧ ∀q. q → w ≤ q`.
Actuality says there is one. -/
def ActualWorld (w : Prop) : Prop := w ∧ ∀ q : Prop, q → w ≤ q

/-! ### The order at `t`

`p ≤ q` is the identity `q = (p ∨ q)`, so these are the Boolean identities of
`Booleanism.lean` read as facts about the order: reflexivity, transitivity and
antisymmetry, the bounds, meets and joins, and the passage through the box by `NI` and
`K` (`le_iff_prop`). Each is a closed lemma, so that a metalogical proof can necessitate
it. -/

section prop

theorem le_refl_prop (p : Prop) : p ≤ p := (or_self_eq p).symm

theorem le_trans_prop (p q r : Prop) (h₁ : p ≤ q) (h₂ : q ≤ r) : p ≤ r := by
  have h₁' : q = (p ∨ q) := h₁
  have h₂' : r = (q ∨ r) := h₂
  show r = (p ∨ r)
  calc r = (q ∨ r) := h₂'
    _ = ((p ∨ q) ∨ r) := by conv => lhs; rw [h₁']
    _ = (p ∨ (q ∨ r)) := or_assoc_eq p q r
    _ = (p ∨ r) := by rw [← h₂']

theorem le_antisymm_prop (p q : Prop) (h₁ : p ≤ q) (h₂ : q ≤ p) : p = q := by
  show p = q
  calc p = (q ∨ p) := h₂
    _ = (p ∨ q) := or_comm_eq q p
    _ = q := h₁.symm

theorem bot_le_prop (p : Prop) : False ≤ p := (false_or_eq p).symm
theorem le_top_prop (p : Prop) : p ≤ True := (or_true_eq p).symm

theorem le_or_left_prop (p q : Prop) : p ≤ (p ∨ q) := by
  show (p ∨ q) = (p ∨ (p ∨ q))
  rw [← or_assoc_eq, or_self_eq]

theorem le_or_right_prop (p q : Prop) : q ≤ (p ∨ q) := by
  show (p ∨ q) = (q ∨ (p ∨ q))
  rw [or_comm_eq p q, ← or_assoc_eq, or_self_eq]

theorem and_le_left_prop (p q : Prop) : (p ∧ q) ≤ p := by
  show p = ((p ∧ q) ∨ p)
  rw [or_comm_eq, or_and_absorb_eq]

theorem and_le_right_prop (p q : Prop) : (p ∧ q) ≤ q := by
  show q = ((p ∧ q) ∨ q)
  rw [or_comm_eq, and_comm_eq, or_and_absorb_eq]

/-- `p ≤ q` and `p ≤ r` give `p ≤ q ∧ r`, through the box. -/
theorem le_and_prop_aux (p q r : Prop) : (p → q) → (p → r) → (p → q ∧ r) :=
  fun h₁ h₂ hp => ⟨h₁ hp, h₂ hp⟩

theorem le_and_prop (p q r : Prop) (h₁ : p ≤ q) (h₂ : p ≤ r) : p ≤ (q ∧ r) :=
  (le_iff_prop _ _).2 (modal_K _ _ (modal_K _ _ (nec% (le_and_prop_aux p q r))
    ((le_iff_prop _ _).1 h₁)) ((le_iff_prop _ _).1 h₂))

/-- `p ≤ ¬p` says `p = ⊥`. -/
theorem eq_false_of_le_neg (p : Prop) (h : p ≤ ¬ p) : p = False := by
  have h' : (¬ p) = True := by
    show (¬ p) = True
    calc (¬ p) = (p ∨ ¬ p) := h
      _ = True := em_eq p
  calc p = ¬ ¬ p := (not_not_eq p).symm
    _ = ¬ True := by rw [h']
    _ = False := not_true_eq

theorem le_neg_of_eq_false (p : Prop) (h : p = False) : p ≤ ¬ p := by
  show (¬ p) = (p ∨ ¬ p)
  rw [h, not_false_eq, false_or_eq]

/-- `p ≤ q` is an identity, so it is necessary when true. -/
theorem box_le_prop (p q : Prop) (h : p ≤ q) : □ (p ≤ q) := necessity_of_identity _ _ h

/-- `p ≤ q` gives `p → q`. -/
theorem imp_of_le_prop (p q : Prop) (h : p ≤ q) (hp : p) : q := h.mpr (Or.inl hp)

/-- `p ≤ q` gives `p ≤ q ∨ r`, and `p ≤ r → q` is `p ≤ ¬r ∨ q`. -/
theorem le_or_of_le_left_prop (p q r : Prop) (h : p ≤ q) : p ≤ (q ∨ r) :=
  le_trans_prop _ _ _ h (le_or_left_prop q r)

/-! ### Atoms at `t` -/

/-- An atom at `t` decides every proposition: `w ≤ q` or `w ≤ ¬q`. Take `z := w ∧ q`,
which is below `w`: either it is `w`, so `w ≤ q`, or it is `⊥`, so `w ∧ q = ⊥` and
`w ≤ ¬q`. -/
theorem atom_le_or_le_neg (w q : Prop) (hw : Atom w) : w ≤ q ∨ w ≤ ¬ q :=
  (em (Rel.and w q = w)).elim
    (fun h => Or.inl (by
      have : (w ∧ q) ≤ q := and_le_right_prop w q
      rw [show (w ∧ q) = w from h] at this
      exact this))
    (fun h => Or.inr (by
      have hbot : (w ∧ q) = False := eq_false_of_le_neg _ ((hw (Rel.and w q)).1 ⟨and_le_left_prop w q, h⟩)
      show (¬ q) = (w ∨ ¬ q)
      calc (¬ q) = (¬ q ∨ False) := (or_false_eq (¬ q)).symm
        _ = (¬ q ∨ (w ∧ q)) := by rw [hbot]
        _ = ((¬ q ∨ w) ∧ (¬ q ∨ q)) := or_and_distrib_eq (¬ q) w q
        _ = ((¬ q ∨ w) ∧ True) := by rw [or_comm_eq (¬ q) q, em_eq]
        _ = (¬ q ∨ w) := and_true_eq _
        _ = (w ∨ ¬ q) := or_comm_eq _ _))

end prop

end Classicism
