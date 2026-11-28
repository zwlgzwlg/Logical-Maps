import Classicism.Results.Research.RecurrentArithmetic
import Classicism.Results.SentenceSchemas.Incompatibilities

/-!
# The guarded arithmetic fork in pure Maximalism

The two consistency premises below isolate the ordinary partition-model and Rosser
arguments. Once they are supplied for a single closed guard and sentence, the native
Possibility schema is inconsistent with the map's local Boolean Completeness at `t`.
-/

namespace Classicism.RecurrentArithmetic
open Classicism.P Classicism.Paper Classicism.Proofs.RecurrentCells

def guardFor (σ : Type) [Ty σ] (A : Prop) (J : Arith.ν σ → Prop) := guard (IStar σ ∧ A) J

theorem bc_gives_join {σ : Type} [Ty σ] (K : Prop → Prop)
    (H : Prop → (Arith.ν σ → Prop) → Prop) (A : Prop) (J : Arith.ν σ → Prop)
    (eK : K = joinedGuard σ) (eH : H = guardFor σ) (bc : BooleanCompletenessT) : K (H A J) :=
  eK ▸ eH ▸ (BooleanCompletenessT.to_lub bc (family (guardFor σ A J) J)).elim
    (fun s hs => (⟨A, s, J, rfl, hs⟩ : joinedGuard σ (guardFor σ A J)))

theorem fork_contradiction (g p : Prop) (d : (□ (g → p)) ∨ (□ (g → ¬ p)))
    (pos : ◇ (g ∧ p)) (neg : ◇ (g ∧ ¬ p)) : False :=
  d.elim (fun h => box_not_dia_contra (g ∧ ¬ p)
    (modal_K _ _ (nec% (fun (f : g → p) (z : g ∧ ¬ p) => z.2 (f z.1))) h) neg)
    (fun h => box_not_dia_contra (g ∧ p)
      (modal_K _ _ (nec% (fun (f : g → ¬ p) (z : g ∧ p) => f z.1 z.2)) h) pos)

end Classicism.RecurrentArithmetic

#classicism_quote_term Classicism.RecurrentArithmetic.guardFor
#classicism_derive Classicism.RecurrentArithmetic.bc_gives_join Classicism.RecurrentArithmetic.fork_contradiction

namespace Classicism.Meta.RecurrentArithmetic
open AxiomSet Classicism.RecurrentArithmetic

noncomputable abbrev namedGuard (σ : Ty) (a : Sentence Signature.pure)
    (J : Term Signature.pure [] (Ty.nu σ ⇒ .t)) : Sentence Signature.pure :=
  Term.app (Term.app (guardFor.term σ) a) J

/-- Goodsell's two arithmetically opposite possibilities provide the only semantic
premises. At the source the proof uses the native, unboxed scalar completeness axiom. -/
theorem possibility_bc_inconsistent_of_guarded_fork (σ : Ty) (a : Sentence Signature.pure)
    (J : Term Signature.pure [] (Ty.nu σ ⇒ .t)) (A : AForm 0)
    (cp : (Term.conj (namedGuard σ a J) (A.toTerm σ)).closedTypes = true)
    (cn : (Term.conj (namedGuard σ a J) (Term.neg (A.toTerm σ))).closedTypes = true)
    (pos : Consistent (empty ∪ single (Term.conj (namedGuard σ a J) (A.toTerm σ))))
    (neg : Consistent (empty ∪ single (Term.conj (namedGuard σ a J) (Term.neg (A.toTerm σ))))) :
    ¬ Consistent (possibility (empty : AxiomSet Signature.pure) ∪ P.BooleanCompletenessT.schema) := by
  intro consistent
  apply consistent
  let T := C.axioms ∪ (possibility (empty : AxiomSet Signature.pure) ∪ P.BooleanCompletenessT.schema)
  let G := namedGuard σ a J
  have hp : Theorem T (Term.dia (Term.conj G (A.toTerm σ))) :=
    Theorem.ax (Or.inl (possibility_mem cp pos))
  have hn : Theorem T (Term.dia (Term.conj G (Term.neg (A.toTerm σ)))) :=
    Theorem.ax (Or.inl (possibility_mem cn neg))
  have hb : Theorem T P.BooleanCompletenessT.quoted := Theorem.ax (Or.inr rfl)
  have h := @Derivable.allEBlock Signature.pure T [_, _, _, _] [] [] _
    (Theorem.ofCMinus (bc_gives_join.derivable σ))
    (.cons (joinedGuard.term σ) (.cons (guardFor.term σ) (.cons a (.cons J .nil))))
  have hj : Theorem T (Term.app (joinedGuard.term σ) G) :=
    .impE (.impE (.impE h (.refl _)) (.refl _)) hb
  have hd := Theorem.mp (Theorem.ofCMinus (one_join_decides_arithmetic σ G A)) hj
  exact .notE hn (.impE (.impE (.allE₂β (Theorem.ofCMinus fork_contradiction.derivable)
    G (A.toTerm σ)) hd) hp)

end Classicism.Meta.RecurrentArithmetic
