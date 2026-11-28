import Classicism.Results.Records.Box5
import Classicism.Tools.QuoteTerm
import Classicism.Tools.Translate

/-! A unary Russell–Myhill operator for the two-layer construction. The diagonal has
type `e → Prop`. Its individual marker is a parameter bound by the endpoint sentence. -/

namespace Classicism.Proofs.UnarySP

open Classicism.P Classicism.Paper

abbrev Unary := e → Prop
abbrev Tester := Unary → Prop
abbrev Family := e → Tester → Unary

def russell (Q : Family) (b : e) (p : Unary) : Prop :=
  ∃ F : Tester, Q b F = p ∧ ¬ F p

def diagonal (Q : Family) (b : e) : Unary := Q b (russell Q b)

def guarded (Q : Family) (g : Prop) : Prop :=
  ∀ (b : e) (F : Tester), Q b F = diagonal Q b → □ (g → F (diagonal Q b))

/-- If the diagonal had no rejecting witness, its own tester would be one. -/
theorem russell_witness (Q : Family) (b : e) : russell Q b (diagonal Q b) :=
  (em (russell Q b (diagonal Q b))).elim id fun h =>
    False.elim (h ⟨russell Q b, rfl, h⟩)

/-- A strongly possible implication between identities holds here. The premise
persists to the visit. If the conclusion fails here, its disequality can be
restored after the visit, so the conclusion still fails at the visit. -/
theorem reflect_identity_implication {σ τ : Type} [Ty σ] [Ty τ] (x y : σ) (u v : τ)
    (visit : DiaNe (x = y → u = v)) (same : x = y) : u = v := by
  apply (em (u = v)).elim id
  intro distinct
  exact (visit ⟨u ≠ v, distinct, modal_K _ _ (nec% (fun (h : x = y)
    (possible : ◇ (u ≠ v)) (clause : x = y → u = v) =>
      ne_of_dia_ne u v possible (clause h))) (necessity_of_identity x y same)⟩).elim

/-- Each instance of the guarded law is an implication between identities:
the boxed conclusion is an identity with truth. Thus the whole law reflects. -/
theorem reflect_guarded (Q : Family) (g : Prop) : DiaNe (guarded Q g) → guarded Q g :=
  fun visit b F => reflect_identity_implication _ _ _ True
    (diaNe_mono _ _ (nec% (fun (endpoint : guarded Q g) => endpoint b F)) visit)

/-- At a world satisfying the guard, the law says that every tester which
names the diagonal accepts it. The Russell witness names it and rejects it. -/
theorem guarded_excludes (Q : Family) (g : Prop) : guarded Q g → ¬ g :=
  fun law hg => e_exists.elim fun b _ => (russell_witness Q b).elim fun F h =>
    h.2 ((box_elim (law b F h.1)) hg)

theorem excludes_guard (Q : Family) (g : Prop) : DiaNe (guarded Q g) → ¬ g :=
  fun visit => guarded_excludes Q g (reflect_guarded Q g visit)

/-! The pure operator used in the second licence reads the old diagonal
from the sizes of the fibres above the old individuals. -/

/-- Above the old layer, this equivalence identifies the copies of each individual. -/
def sameFibre (a b x y : e) : Prop := □ (a = b → x = y)

/-- A distinct individual occupies the same fibre as x. -/
def hasTwin (a b x : e) : Prop := ∃ y : e, ¬ x = y ∧ sameFibre a b x y

/-- A singleton fibre records truth and a doubleton records falsity. -/
def code (a b : e) (p : Unary) : Prop :=
  p = (fun x => ◇ (p x)) ∧
    □ (¬ a = b → ∀ x : e, ¬ hasTwin a b x ↔ ◇ (a = b ∧ p x))

def operator : Family := fun b F a =>
  ◇ (¬ a = b ∧ ∃ p : Unary, code a b p ∧ ◇ (a = b ∧ ¬ F p))

/-- Every output is fixed by ordinary possibility, including after transport. -/
theorem operator_fixed (b : e) (F : Tester) :
    operator b F = fun x => ◇ (operator b F x) :=
  equiv% (fun x => Iff.intro (dia_intro (operator b F x)) (dia_dia _))

end Classicism.Proofs.UnarySP

#classicism_quote_term Classicism.Proofs.UnarySP.sameFibre Classicism.Proofs.UnarySP.hasTwin
#classicism_quote_term Classicism.Proofs.UnarySP.code
#classicism_quote_term Classicism.Proofs.UnarySP.operator Classicism.Proofs.UnarySP.guarded

/-- The quoted guard law specialized to the closed unary operator. -/
noncomputable def Classicism.Proofs.UnarySP.guardedLaw.term :=
  Classicism.Meta.Term.apply Classicism.Proofs.UnarySP.guarded.term Classicism.Proofs.UnarySP.operator.term
#classicism_derive Classicism.Proofs.UnarySP.operator_fixed
#classicism_derive Classicism.Proofs.UnarySP.russell_witness Classicism.Proofs.UnarySP.reflect_identity_implication
#classicism_derive Classicism.Proofs.UnarySP.reflect_guarded Classicism.Proofs.UnarySP.guarded_excludes
#classicism_derive Classicism.Proofs.UnarySP.excludes_guard
