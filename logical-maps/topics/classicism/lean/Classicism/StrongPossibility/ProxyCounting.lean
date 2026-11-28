import Classicism.StrongPossibility.ProxyTerms
import Mathlib.Data.Finset.Card

namespace Classicism.Meta.ProxyDiagonal
open CategoryTheory Intensional Term
variable {Sig : Signature} {C : Type} [SmallCategory C]
variable (A : Premodel Sig C) (M : A.IsModel)

def Here {W : C} (p : Intension A.inner (Ty.e ⇒ RTy.t) W) (x : A.Dom W .e) : Prop :=
  (⟨W, (x, PUnit.unit), 𝟙 W⟩ : Tuple A.inner (Ty.e ⇒ RTy.t) W) ∈ p

/-- Extensional definition of a finite current set, valid on infinite ambient carriers. -/
def Size {α : Type} (n : Nat) (P : α → Prop) : Prop :=
  ∃ t : Finset α, t.card = n ∧ ∀ x, x ∈ t ↔ P x

theorem size_zero_iff {α : Type} (P : α → Prop) :
    Size 0 P ↔ ∀ x, ¬P x := by
  classical
  constructor
  · rintro ⟨s, hc, hs⟩ x hx
    have : s = ∅ := Finset.card_eq_zero.mp hc
    simpa [this] using (hs x).mpr hx
  · intro hn
    exact ⟨∅, rfl, by simp [hn]⟩

theorem size_succ_iff {α : Type} (n : Nat) (P : α → Prop) :
    Size (n+1) P ↔ ∃ x, P x ∧ Size n (fun y => P y ∧ y ≠ x) := by
  classical
  constructor
  · rintro ⟨t, ht, hs⟩
    have hpos : 0 < t.card := by omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
    exact ⟨x, (hs x).mp hx, t.erase x, by rw [Finset.card_erase_of_mem hx, ht]; omega,
      fun y => by simp [hs, and_comm]⟩
  · rintro ⟨x, hx, t, ht, hs⟩
    have hxt : x ∉ t := by simp [hs]
    refine ⟨insert x t, by rw [Finset.card_insert_of_notMem hxt, ht], fun y => ?_⟩
    by_cases he : y = x
    · subst y; simp [hx]
    · simp [he, hs]

include M in

theorem holds_exactly {W : C} (h : A.W₀ ⟶ W) (n : Nat) {Γ : Ctx}
    (g : IEnv (A.Dom W) Γ) (p : Term Sig Γ (Ty.e ⇒ RTy.t)) :
    A.Holds h (exactly n p) g ↔ Size n (Here A (A.sem h p g)) := by
  induction n generalizing Γ with
  | zero =>
    rw [exactly, A.holds_forall M, size_zero_iff]
    apply forall_congr'; intro a
    rw [A.holds_neg M, A.holds_app _ _ _ _ (a' := a) rfl, A.sem_weaken]
    rfl
  | succ n ih =>
    rw [exactly, A.holds_exists M, size_succ_iff]
    apply exists_congr; intro x
    rw [A.holds_conj M, A.holds_app _ _ _ _ (a' := x) rfl, A.sem_weaken, ih]
    apply and_congr_right; intro _
    apply iff_of_eq
    apply congrArg (Size n)
    funext y
    apply propext
    unfold Here
    rw [Premodel.mem_sem_lam, Category.comp_id, A.push_id]
    change A.Holds h _ (.cons y (.cons x g)) ↔ _
    rw [A.holds_conj M, A.holds_neg M, A.holds_eq M,
      A.holds_app _ _ _ _ (a' := y) rfl, A.sem_weaken, A.sem_weaken]
    rfl

end Classicism.Meta.ProxyDiagonal
