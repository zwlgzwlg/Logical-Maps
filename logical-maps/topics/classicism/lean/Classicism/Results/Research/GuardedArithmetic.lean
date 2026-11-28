import Classicism.Results.SentenceSchemas.ArithmeticMeta
import Classicism.Results.Research.GuardedArithmeticAtoms

/-!
# Agreement of arithmetic across the points satisfying a guard

Goodsell's formula induction applied to the guarded numerical Barcan premise of the
recurrent-cell argument. The two alternatives are evaluated at the source; no accessibility
between different guarded points is required.
-/

namespace Classicism.GuardedArithmetic

open Classicism.P

def agrees (G p : Prop) := (□ (G → p)) ∨ (□ (G → ¬ p))

theorem neg_step (G p : Prop) (hp : agrees G p) : agrees G (¬ p) :=
  hp.elim (fun h => Or.inr (modal_K _ _ (nec% (fun (f : G → p) (g : G) (n : ¬ p) =>
    n (f g))) h)) Or.inl

theorem conj_step (G p q : Prop) (hp : agrees G p) (hq : agrees G q) : agrees G (p ∧ q) :=
  hp.elim (fun a => hq.elim (fun b => Or.inl (modal_K _ _ (modal_K _ _
      (nec% (fun (f : G → p) (h : G → q) (g : G) => (⟨f g, h g⟩ : p ∧ q))) a) b))
    (fun b => Or.inr (modal_K _ _
      (nec% (fun (h : G → ¬ q) (g : G) (pq : p ∧ q) => h g pq.2)) b)))
    (fun a => Or.inr (modal_K _ _
      (nec% (fun (f : G → ¬ p) (g : G) (pq : p ∧ q) => f g pq.1)) a))

theorem disj_step (G p q : Prop) (hp : agrees G p) (hq : agrees G q) : agrees G (p ∨ q) :=
  hp.elim (fun a => Or.inl (modal_K _ _
    (nec% (fun (f : G → p) (g : G) => (Or.inl (f g) : p ∨ q))) a))
    (fun a => hq.elim (fun b => Or.inl (modal_K _ _
      (nec% (fun (h : G → q) (g : G) => (Or.inr (h g) : p ∨ q))) b))
      (fun b => Or.inr (modal_K _ _ (modal_K _ _
        (nec% (fun (f : G → ¬ p) (h : G → ¬ q) (g : G) (z : p ∨ q) => z.elim (f g) (h g))) a) b)))

variable {σ : Type} [Ty σ]

set_option linter.unusedSectionVars false in
theorem all_step (G : Prop) (N X : Arith.ν σ → Prop)
    (bf : ∀ Y : Arith.ν σ → Prop, (∀ n, N n → □ (G → Y n)) → □ (G → ∀ n, N n → Y n))
    (persistent : ∀ n, N n → □ (N n))
    (ih : ∀ n, N n → agrees G (X n)) : agrees G (∀ n, N n → X n) :=
  (em (∀ n, N n → □ (G → X n))).elim (fun h => Or.inl (bf X h))
    (fun hn => (em (∃ n, N n ∧ ¬ □ (G → X n))).elim
      (fun he => he.elim fun n h => (ih n h.1).elim (fun e => (h.2 e).elim)
        (fun neg => Or.inr (modal_K _ _ (modal_K _ _
          (nec% (fun (nn : N n) (f : G → ¬ X n) (g : G) (v : ∀ n, N n → X n) =>
            f g (v n nn))) (persistent n h.1)) neg)))
      (fun he => (hn fun n nn => (em (□ (G → X n))).elim id
        fun hn' => (he ⟨n, nn, hn'⟩).elim).elim))

end Classicism.GuardedArithmetic

#classicism_derive Classicism.GuardedArithmetic.neg_step Classicism.GuardedArithmetic.conj_step
  Classicism.GuardedArithmetic.disj_step Classicism.GuardedArithmetic.all_step

noncomputable section
namespace Classicism.Meta.GuardedArithmetic

open Classicism.GuardedArithmetic

/-- Root premises carried under the arithmetic binders. Only the new variable's numberhood
is added at each binder. The premises themselves stay local. -/
def hypotheses (σ : Ty) (Δ : List (Sentence Signature.pure)) :
    (k : Nat) → List (Formula Signature.pure (numCtx σ k))
  | 0 => Δ
  | k+1 => Nt σ (.var .zero) :: Hyps.weaken (hypotheses σ Δ k)

theorem root_hyp {σ : Ty} {Δ : List (Sentence Signature.pure)} {p : Sentence Signature.pure}
    (h : p ∈ Δ) (k : Nat) : Derivable C.axiomsMinus (hypotheses σ Δ k) p.close := by
  induction k with
  | zero => simpa [hypotheses] using (Derivable.hyp h : Derivable C.axiomsMinus Δ p)
  | succ k ih =>
    have hw := Derivable.rename (Ren.shift (σ := Ty.nu σ)) ih
    rw [Term.close_rename] at hw
    exact Derivable.weaken₁ hw

theorem variable_number {σ : Ty} {Δ : List (Sentence Signature.pure)} : ∀ {k : Nat} (i : Fin k),
    Derivable C.axiomsMinus (hypotheses σ Δ k) (Nt σ (.var (numVar σ i)))
  | k+1, ⟨0, _⟩ => Derivable.hyp₀
  | k+1, ⟨i+1, hi⟩ => by
    have h := Derivable.rename (Ren.shift (σ := Ty.nu σ))
      (variable_number (σ := σ) (Δ := Δ) ⟨i, Nat.lt_of_succ_lt_succ hi⟩)
    unfold Nt at h
    rw [Term.rename_app, Term.rename_var, Term.close_rename] at h
    exact Derivable.weaken₁ h

theorem term_number {σ : Ty} {Δ : List (Sentence Signature.pure)} : ∀ {k : Nat} (t : ATerm k),
    Derivable C.axiomsMinus (hypotheses σ Δ k) (Nt σ (t.toTerm σ))
  | _, .var i => variable_number i
  | _, .zero => .impE (.impE (.allE₂β (.ofTheorem (arith_N_zero_rel.derivable σ))
      (Arith.N.term σ).close (Arith.zero.term σ).close) (.refl _)) (.refl _)
  | _, .suc t => .impE (.impE (.impE (.allE₃β (.ofTheorem (arith_N_suc_rel.derivable σ))
      (Arith.N.term σ).close (Arith.suc.term σ).close (t.toTerm σ))
      (.refl _)) (.refl _)) (term_number t)

abbrev decision {Γ : Ctx} (g p : Formula Signature.pure Γ) :=
  Term.disj (Term.box (Term.imp g p)) (Term.box (Term.imp g (Term.neg p)))

abbrev guardedPeano (σ : Ty) (G : Sentence Signature.pure) :=
  Term.box (Term.imp G (IStar.term σ))

abbrev guardedBarcan (σ : Ty) (G : Sentence Signature.pure) : Sentence Signature.pure :=
  Term.forall' (σ := Ty.nu σ ⇒ .t) (Term.imp
    (Term.forall' (σ := Ty.nu σ) (Term.imp (Nt σ Term.v0)
      (Term.box (Term.imp G.close (Term.app Term.v1 Term.v0)))))
    (Term.box (Term.imp G.close (Term.forall' (σ := Ty.nu σ)
      (Term.imp (Nt σ Term.v0) (Term.app Term.v1 Term.v0))))))

abbrev premises (σ : Ty) (G : Sentence Signature.pure) := [guardedPeano σ G, guardedBarcan σ G]

local infixr:67 " ::: " => Terms.cons

theorem peano_at (σ : Ty) (G : Sentence Signature.pure) (k : Nat) :
    Derivable C.axiomsMinus (hypotheses σ (premises σ G) k)
      (Term.box (Term.imp G.close (IStar.term σ).close)) :=
  root_hyp (p := guardedPeano σ G) (List.mem_cons_self ..) k

theorem number_atom (σ : Ty) (G : Sentence Signature.pure) {k : Nat} (t : ATerm k) :
    Derivable C.axiomsMinus (hypotheses σ (premises σ G) k)
      (decision G.close ((AForm.nat t).toTerm σ)) :=
  .impE (.impE (.allE₃β (.ofTheorem (number_agreement.derivable σ))
    G.close (Arith.N.term σ).close (t.toTerm σ)) (.refl _)) (term_number t)

theorem equality_atom (σ : Ty) (G : Sentence Signature.pure) {k : Nat} (t u : ATerm k) :
    Derivable C.axiomsMinus (hypotheses σ (premises σ G) k)
      (decision G.close ((AForm.eq t u).toTerm σ)) := by
  have h := @Derivable.allEBlock Signature.pure C.axiomsMinus [_, _, _, _, _] _
    (hypotheses σ (premises σ G) k) _
    (.ofTheorem (equality_rel.derivable σ))
    (G.close ::: (IStar.term σ).close ::: (Arith.N.term σ).close ::: t.toTerm σ ::: u.toTerm σ ::: .nil)
  exact .impE (.impE (.impE (.impE (.impE h (.refl _)) (.refl _))
    (peano_at σ G k)) (term_number t)) (term_number u)

theorem sum_atom (σ : Ty) (G : Sentence Signature.pure) {k : Nat} (t u v : ATerm k) :
    Derivable C.axiomsMinus (hypotheses σ (premises σ G) k)
      (decision G.close ((AForm.sum t u v).toTerm σ)) := by
  have h := @Derivable.allEBlock Signature.pure C.axiomsMinus [_, _, _, _, _, _, _] _
    (hypotheses σ (premises σ G) k) _ (.ofTheorem (sum_rel.derivable σ))
    (G.close ::: (IStar.term σ).close ::: (Arith.N.term σ).close ::: (Arith.Sum.term σ).close :::
      t.toTerm σ ::: u.toTerm σ ::: v.toTerm σ ::: .nil)
  exact .impE (.impE (.impE (.impE (.impE (.impE (.impE h (.refl _)) (.refl _)) (.refl _))
    (peano_at σ G k)) (term_number t)) (term_number u)) (term_number v)

theorem prod_atom (σ : Ty) (G : Sentence Signature.pure) {k : Nat} (t u v : ATerm k) :
    Derivable C.axiomsMinus (hypotheses σ (premises σ G) k)
      (decision G.close ((AForm.prod t u v).toTerm σ)) := by
  have h := @Derivable.allEBlock Signature.pure C.axiomsMinus [_, _, _, _, _, _, _] _
    (hypotheses σ (premises σ G) k) _ (.ofTheorem (prod_rel.derivable σ))
    (G.close ::: (IStar.term σ).close ::: (Arith.N.term σ).close ::: (Arith.Prod.term σ).close :::
      t.toTerm σ ::: u.toTerm σ ::: v.toTerm σ ::: .nil)
  exact .impE (.impE (.impE (.impE (.impE (.impE (.impE h (.refl _)) (.refl _)) (.refl _))
    (peano_at σ G k)) (term_number t)) (term_number u)) (term_number v)

theorem decision_conv {Γ : Ctx} {g g' p p' : Formula Signature.pure Γ}
    (hg : g ≡ g') (hp : p ≡ p') : decision g p ≡ decision g' p' := by
  repeat' first | exact hg | exact hp | exact Conv.refl _ | apply Conv.app_congr

theorem arithmetic_agreement (σ : Ty) (G : Sentence Signature.pure) : ∀ {k : Nat} (A : AForm k),
    Derivable C.axiomsMinus (hypotheses σ (premises σ G) k)
      (decision G.close (A.toTerm σ))
  | _, .nat t => number_atom σ G t
  | _, .eq t u => equality_atom σ G t u
  | _, .sum t u v => sum_atom σ G t u v
  | _, .prod t u v => prod_atom σ G t u v
  | _, .neg A =>
    .impE (.allE₂β (.ofTheorem neg_step.derivable) G.close (A.toTerm σ)) (arithmetic_agreement σ G A)
  | _, .conj A B =>
    .impE (.impE (.allE₃β (.ofTheorem conj_step.derivable) G.close (A.toTerm σ) (B.toTerm σ))
      (arithmetic_agreement σ G A)) (arithmetic_agreement σ G B)
  | _, .disj A B =>
    .impE (.impE (.allE₃β (.ofTheorem disj_step.derivable) G.close (A.toTerm σ) (B.toTerm σ))
      (arithmetic_agreement σ G A)) (arithmetic_agreement σ G B)
  | k, .all A => by
    let Δ := hypotheses σ (premises σ G) k
    have h := @Derivable.allEBlock Signature.pure C.axiomsMinus [_, _, _] _ Δ _
      (.ofTheorem (all_step.derivable σ))
      (G.close ::: (Arith.N.term σ).close ::: Term.lam (A.toTerm σ) ::: .nil)
    have hbf := root_hyp (σ := σ) (Δ := premises σ G) (p := guardedBarcan σ G) (by simp [premises]) k
    have hp : Derivable C.axiomsMinus Δ _ :=
      Derivable.impE (Derivable.allEβ (.ofTheorem (persistence_rel.derivable σ)) (Arith.N.term σ).close)
        (.refl _)
    have ih := Derivable.allI (Derivable.impI (arithmetic_agreement σ G A))
    apply Derivable.conv
    · apply Derivable.impE (Derivable.impE (Derivable.impE h ?_) hp)
      · apply Derivable.conv ih
        apply Conv.app_congr (Conv.refl _)
        apply Conv.lam_congr
        apply Conv.app_congr (Conv.refl _)
        change decision G.close (A.toTerm σ) ≡
          decision (G.close.weaken) (Term.app (Term.lam (A.toTerm σ)).weaken Term.v0)
        apply decision_conv
        · unfold Term.weaken
          rw [Term.close_rename]
          exact Conv.refl _
        · exact (Conv.app_lam_weaken_var _).symm
      · change Derivable _ Δ (Term.forall' (σ := Ty.nu σ ⇒ .t) (Term.imp
          (Term.forall' (σ := Ty.nu σ) (Term.imp (Nt σ Term.v0)
            (Term.box (Term.imp G.close.weaken.weaken (Term.app Term.v1 Term.v0)))))
          (Term.box (Term.imp G.close.weaken
            (Term.forall' (σ := Ty.nu σ) (Term.imp (Nt σ Term.v0) (Term.app Term.v1 Term.v0)))))))
        change Derivable _ Δ (Term.forall' (σ := Ty.nu σ ⇒ .t) (Term.imp
          (Term.forall' (σ := Ty.nu σ) (Term.imp (Nt σ Term.v0)
            (Term.box (Term.imp (G.close.rename (Ren.lift (Ren.lift Ren.ofEmpty)))
              (Term.app Term.v1 Term.v0)))))
          (Term.box (Term.imp (G.close.rename (Ren.lift Ren.ofEmpty))
            (Term.forall' (σ := Ty.nu σ) (Term.imp (Nt σ Term.v0) (Term.app Term.v1 Term.v0))))))) at hbf
        simp only [Term.weaken, Term.close_rename] at hbf ⊢
        exact hbf
    · apply decision_conv (Conv.refl _)
      apply Conv.app_congr (Conv.refl _)
      apply Conv.lam_congr
      apply Conv.app_congr (Conv.refl _)
      exact Conv.app_lam_weaken_var _

/-- Any arithmetic sentence has one sign throughout all the reachable guarded points. -/
theorem sentence_agreement (σ : Ty) (G : Sentence Signature.pure) (A : AForm 0) :
    Theorem C.axiomsMinus (Term.imp (guardedBarcan σ G)
      (Term.imp (guardedPeano σ G) (decision G (A.toTerm σ)))) := by
  apply Derivable.impI
  apply Derivable.impI
  simpa [hypotheses, premises] using arithmetic_agreement σ G A

end Classicism.Meta.GuardedArithmetic
end
