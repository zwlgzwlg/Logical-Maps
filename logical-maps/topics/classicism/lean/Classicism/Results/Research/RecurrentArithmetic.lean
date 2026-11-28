import Classicism.Results.Research.RecurrentCells
import Classicism.Results.Research.GuardedArithmetic

/-!
# One scalar join decides every arithmetic sentence throughout the guarded points

This combines the parallel lab's recurrent-cell join theorem with Goodsell's guarded
formula induction. The cell label and all existential witnesses are object-language
entities. The assertion that a particular pure guard is consistent and the final
incompleteness argument are mathematical parts of the accompanying write-up.
-/

namespace Classicism.RecurrentArithmetic
open Classicism.P Classicism.Paper Classicism.Proofs.RecurrentCells

/-- The guard includes Peano and the numerical recurrence conditions. Its cell family
has a single join at the point where this predicate is asserted. -/
def joinedGuard (σ : Type) [Ty σ] (G : Prop) : Prop :=
  ∃ (A s : Prop) (J : Arith.ν σ → Prop),
    G = guard (IStar σ ∧ A) J ∧ LUB s (family G J)

theorem join_inputs {σ : Type} [Ty σ] (G : Prop) (h : joinedGuard σ G) :
    (□ (G → IStar σ)) ∧
    (∀ X : Arith.ν σ → Prop, (∀ n, Arith.N σ n → □ (G → X n)) →
      □ (G → ∀ n, Arith.N σ n → X n)) :=
  h.elim fun A h => h.elim fun s h => h.elim fun J h =>
    Eq.mpr (congrArg (fun g : Prop => (□ (g → IStar σ)) ∧
      (∀ X : Arith.ν σ → Prop, (∀ n, Arith.N σ n → □ (g → X n)) →
        □ (g → ∀ n, Arith.N σ n → X n))) h.1)
    ⟨nec% (fun hg : guard (IStar σ ∧ A) J => (box_elim hg).1.1),
     fun X hx => guarded_numerical_barcan_of_join (IStar σ ∧ A) s J X
       (Eq.mp (congrArg (fun g : Prop => LUB s (family g J)) h.1) h.2) hx⟩

theorem join_inputs_rel {σ : Type} [Ty σ] (G I : Prop) (N : Arith.ν σ → Prop) (K : Prop → Prop)
    (eI : I = IStar σ) (eN : N = Arith.N σ) (eK : K = joinedGuard σ) (h : K G) :
    (□ (G → I)) ∧ (∀ X : Arith.ν σ → Prop, (∀ n, N n → □ (G → X n)) →
      □ (G → ∀ n, N n → X n)) :=
  eI ▸ eN ▸ join_inputs G (eK ▸ h)

end Classicism.RecurrentArithmetic

#classicism_quote_term Classicism.RecurrentArithmetic.joinedGuard
#classicism_derive Classicism.RecurrentArithmetic.join_inputs_rel

namespace Classicism.Meta.RecurrentArithmetic
open Classicism.Meta.GuardedArithmetic Classicism.RecurrentArithmetic

/-- A single scalar least upper bound for a Peano guard's recurrent labels decides the
sign of every native arithmetic sentence throughout that guard. -/
theorem one_join_decides_arithmetic (σ : Ty) (G : Sentence Signature.pure) (A : AForm 0) :
    Theorem C.axiomsMinus (Term.imp (Term.app (joinedGuard.term σ) G)
      (decision G (A.toTerm σ))) := by
  apply Derivable.impI
  let Δ := [Term.app (joinedGuard.term σ) G]
  have hc := @Derivable.allEBlock Signature.pure C.axiomsMinus [_, _, _, _] [] Δ _
    (.ofTheorem (join_inputs_rel.derivable σ))
    (.cons G (.cons (IStar.term σ) (.cons (Arith.N.term σ) (.cons (joinedGuard.term σ) .nil))))
  have h := Derivable.impE (Derivable.impE (Derivable.impE (Derivable.impE hc (.refl _))
    (.refl _)) (.refl _)) Derivable.hyp₀
  have hp : Derivable C.axiomsMinus Δ (guardedPeano σ G) := .andE₁ h
  have hb := Derivable.andE₂ h
  have hbf : Derivable C.axiomsMinus Δ (guardedBarcan σ G) := by
    change Derivable _ Δ (Term.forall' (σ := Ty.nu σ ⇒ .t) (Term.imp
      (Term.forall' (σ := Ty.nu σ) (Term.imp (Nt σ Term.v0)
        (Term.box (Term.imp G.weaken.weaken (Term.app Term.v1 Term.v0)))))
      (Term.box (Term.imp G.weaken (Term.forall' (σ := Ty.nu σ)
        (Term.imp (Nt σ Term.v0) (Term.app Term.v1 Term.v0))))))) at hb
    rw [← Term.close_nil G] at hb
    simp only [Term.weaken, Term.close_rename] at hb
    exact hb
  have hdec := Derivable.weaken (sentence_agreement σ G A) (Δ' := Δ) (by simp)
  exact Derivable.impE (Derivable.impE hdec hbf) hp

end Classicism.Meta.RecurrentArithmetic
