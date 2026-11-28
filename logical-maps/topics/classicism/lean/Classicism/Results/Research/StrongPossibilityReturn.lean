import Classicism.Results.Other.Meta
import Classicism.Certified.Atoms
import Classicism.Models.CoalescedInterpretations
import Classicism.Coalesced.DistinguishedDefinable

namespace Classicism.Proofs.StrongPossibilityReturn

open Classicism.P Classicism.Paper

abbrev Probe := e → e → e → e → e → e → Prop
abbrev Operator := (Probe → Prop) → Probe

def russell (Q : Operator) (p : Probe) : Prop :=
  ∃ F : Probe → Prop, Q F = p ∧ ¬ F p

def diagonal (Q : Operator) : Probe := Q (russell Q)

def endpoint (Q : Operator) : Prop :=
  StrongActuality ∧ ∀ F : Probe → Prop, Q F = diagonal Q →
    □ (¬ StrongActuality → F (diagonal Q) = True)

theorem russell_witness (Q : Operator) : russell Q (diagonal Q) :=
  (em (russell Q (diagonal Q))).elim id fun h =>
    False.elim (h ⟨russell Q, rfl, h⟩)

theorem excluded_return (Q : Operator) (F : Probe → Prop)
    (h : □ (¬ StrongActuality → F (diagonal Q) = True)) :
    ¬ ◇ (¬ StrongActuality ∧ ¬ F (diagonal Q)) :=
  not_dia_of_box_not _ (modal_K _ _ (nec% (fun
    (r : ¬ StrongActuality → F (diagonal Q) = True)
    (c : ¬ StrongActuality ∧ ¬ F (diagonal Q)) =>
      c.2 ((r c.1).symm ▸ trivial))) h)

theorem excludes_endpoint (Q : Operator) (F : Probe → Prop) (h : Q F = diagonal Q)
    (g : ◇ (¬ StrongActuality ∧ ¬ F (diagonal Q))) : ¬ endpoint Q :=
  fun ep => excluded_return Q F (ep.2 F h) g

theorem diaNe_endpoint_requires_strongActuality (Q : Operator) :
    DiaNe (endpoint Q) → ¬ ¬ StrongActuality := fun pos nsa =>
  (russell_witness Q).elim fun F h => pos
    ⟨¬ StrongActuality ∧ ¬ F (diagonal Q), ⟨nsa, h.2⟩,
      modal_K _ _ (nec% (excludes_endpoint Q F))
        (necessity_of_identity (Q F) (diagonal Q) h.1)⟩

theorem atomlessness_excludes_decider (a : Prop)
    (hd : ∀ p : Prop, a ≤ p ∨ a ≤ ¬ p) (ha : ◇ a) : ¬ Atomlessness :=
  fun hl => not_atom_of_atomlessness hl a (atom_of_decides a ⟨ha, hd⟩)

theorem diaNe_atomlessness_excludes_strongActuality : DiaNe Atomlessness → ¬ StrongActuality :=
  fun pos sa => sa.elim fun a ha =>
    pos ⟨a, ha.1, modal_K _ _ (nec% (atomlessness_excludes_decider a)) ha.2⟩

theorem incompatible_visits (Q : Operator) :
    DiaNe (endpoint Q) → DiaNe Atomlessness → False :=
  fun h a => diaNe_endpoint_requires_strongActuality Q h (diaNe_atomlessness_excludes_strongActuality a)

/-- Local B lets each ordinarily possible sentence pass every return test. -/
theorem lift_possibility (p : Prop) : ModalB → ◇ p → DiaNe p :=
  fun b hp ⟨q, hq, h⟩ => not_dia_of_box_not p (modal_K _ _ h (b q hq)) hp

theorem recover_modal_b (lift : ∀ p : Prop, ◇ p → DiaNe p) : ModalB :=
  fun q hq => (em (□ ◇ q)).elim id fun failure =>
    False.elim (lift (¬ ◇ q) (dia_not_of_not_box (◇ q) failure)
      ⟨q, hq, nec% (fun (possible : ◇ q) (impossible : ¬ ◇ q) => impossible possible)⟩)

theorem modal_b_iff_lift : ModalB ↔ ∀ p : Prop, ◇ p → DiaNe p :=
  ⟨fun b p => lift_possibility p b, recover_modal_b⟩

theorem incompatible_ordinary_visits (Q : Operator) :
    ◇ (endpoint Q) → ◇ Atomlessness → ¬ ModalB :=
  fun he ha b => incompatible_visits Q (lift_possibility _ b he) (lift_possibility _ b ha)

def guarded (b : Prop) (Q : Operator) : Prop :=
  ∀ F : Probe → Prop, Q F = diagonal Q → □ (b → F (diagonal Q) = True)

theorem guarded_obstruction (Q : Operator) (b : Prop) (F : Probe → Prop) (he : Q F = diagonal Q)
    (possible : ◇ (b ∧ ¬ F (diagonal Q))) (visit : guarded b Q) : False :=
  not_dia_of_box_not _ (modal_K _ _ (nec% (fun
    (r : b → F (diagonal Q) = True) (c : b ∧ ¬ F (diagonal Q)) =>
      c.2 ((r c.1).symm ▸ trivial))) (visit F he)) possible

theorem excludes_guard (Q : Operator) (b : Prop) : DiaNe (guarded b Q) → ¬ b :=
  fun visit hb => (russell_witness Q).elim fun F h => visit
    ⟨b ∧ ¬ F (diagonal Q), ⟨hb, h.2⟩, modal_K _ _ (nec% (guarded_obstruction Q b F))
      (necessity_of_identity (Q F) (diagonal Q) h.1)⟩

theorem incompatible_guards (Q : Operator) (b : Prop) :
    DiaNe (guarded b Q) → DiaNe (guarded (¬ b) Q) → False :=
  fun hp hn => excludes_guard Q (¬ b) hn (excludes_guard Q b hp)

end Classicism.Proofs.StrongPossibilityReturn

#classicism_derive Classicism.Proofs.StrongPossibilityReturn.russell_witness
#classicism_derive Classicism.Proofs.StrongPossibilityReturn.excluded_return
#classicism_derive Classicism.Proofs.StrongPossibilityReturn.excludes_endpoint
#classicism_derive Classicism.Proofs.StrongPossibilityReturn.diaNe_endpoint_requires_strongActuality
#classicism_derive Classicism.Proofs.StrongPossibilityReturn.atomlessness_excludes_decider
#classicism_derive Classicism.Proofs.StrongPossibilityReturn.diaNe_atomlessness_excludes_strongActuality
#classicism_derive Classicism.Proofs.StrongPossibilityReturn.incompatible_visits
#classicism_derive Classicism.Proofs.StrongPossibilityReturn.lift_possibility
#classicism_derive Classicism.Proofs.StrongPossibilityReturn.recover_modal_b
#classicism_derive Classicism.Proofs.StrongPossibilityReturn.modal_b_iff_lift
#classicism_derive Classicism.Proofs.StrongPossibilityReturn.incompatible_ordinary_visits

#classicism_derive Classicism.Proofs.StrongPossibilityReturn.guarded_obstruction
#classicism_derive Classicism.Proofs.StrongPossibilityReturn.excludes_guard
#classicism_derive Classicism.Proofs.StrongPossibilityReturn.incompatible_guards

set_option compiler.extract_closed false
noncomputable section
namespace Classicism.Meta.StrongPossibilityReturn

open Term
open Classicism.Proofs.StrongPossibilityReturn

abbrev probe : RTy := Ty.e ⇒ Ty.e ⇒ Ty.e ⇒ Ty.e ⇒ Ty.e ⇒ Ty.e ⇒ RTy.t
abbrev predicate : RTy := Ty.rel probe ⇒ RTy.t
abbrev operator : RTy := Ty.rel predicate ⇒ probe

variable {Sig : Signature} {Γ Δ : Ctx}

def rho (q : Term Sig Γ operator) : Term Sig Γ predicate :=
  .lam (exists' (conj (eq' (.app q.weaken.weaken v0) v1) (neg (.app v0 v1))))

def diag (q : Term Sig Γ operator) : Term Sig Γ probe := .app q (rho q)

def positive (q : Term Sig Γ operator) : Formula Sig (Ty.rel predicate :: Γ) :=
  eq' (.app q.weaken v0) (diag q.weaken)

def negative (q : Term Sig Γ operator) : Formula Sig (Ty.rel predicate :: Γ) :=
  eq' (.app v0 (diag q.weaken)) top

noncomputable def strongActuality : Sentence Sig := ofPure P.StrongActuality.quoted

noncomputable def atomlessness : Sentence Sig := ofPure P.Atomlessness.quoted

def psi (q : Term Sig Γ operator) : Formula Sig Γ :=
  conj strongActuality.close (forall' (Term.imp (positive q)
    (box (Term.imp (neg strongActuality.close) (negative q)))))

def guardedPsi (b : Formula Sig Γ) (q : Term Sig Γ operator) : Formula Sig Γ :=
  forall' (Term.imp (positive q) (box (Term.imp b.weaken (negative q))))

private theorem subst_weaken (s : Sub Sig Γ Δ) (a : Term Sig Γ τ) :
    (a.weaken (τ := σ)).subst (Sub.lift s) = (a.subst s).weaken := by
  simp only [weaken, rename_subst, subst_rename]
  rfl

private theorem subst_rho (s : Sub Sig Γ Δ) (q : Term Sig Γ operator) :
    (rho q).subst s = rho (q.subst s) := by
  simp only [rho, exists', conj, eq', neg, subst_app, subst_lam, subst_weaken]
  rfl

private theorem subst_diag (s : Sub Sig Γ Δ) (q : Term Sig Γ operator) :
    (diag q).subst s = diag (q.subst s) := by
  simp only [diag, subst_app, subst_rho]

theorem positive_instantiate (q : Term Sig [] operator) (f : Term Sig [] predicate) :
    (positive q).instantiate f = eq' (.app q f) (diag q) := by
  simp only [positive, instantiate, eq', subst_app, subst_diag, instantiate_weaken]
  rfl

theorem negative_instantiate (q : Term Sig [] operator) (f : Term Sig [] predicate) :
    (negative q).instantiate f = eq' (.app f (diag q)) top := by
  simp only [negative, instantiate, eq', top, subst_app, subst_lam, subst_diag, instantiate_weaken]
  rfl

private theorem subst_diaNe (s : Sub Sig Γ Δ) (p : Formula Sig Γ) :
    (diaNe p).subst s = diaNe (p.subst s) := by
  simp only [diaNe, exists', conj, box, Term.imp, dia, neg, eq', disj, top, bot, forall',
    subst_app, subst_lam, subst_weaken]
  rfl

private theorem subst_close (s : Sub Sig Γ Δ) (p : Term Sig [] τ) :
    (p.close (Γ := Γ)).subst s = p.close := by
  unfold close
  rw [subst_rename, rename_eq_subst]
  exact congrArg (fun k : Sub Sig [] Δ => p.subst k) (by funext τ v; exact nomatch v)

private theorem close_nil (p : Term Sig [] τ) : p.close (Γ := []) = p := by
  have he : (Ren.ofEmpty : Ren [] []) = Ren.id := by funext τ v; exact nomatch v
  rw [close, he, rename_id]

private theorem subst_psi (s : Sub Sig Γ Δ) (q : Term Sig Γ operator) :
    (psi q).subst s = psi (q.subst s) := by
  simp only [psi, positive, negative, conj, forall', Term.imp, disj, eq', neg, box, top,
    subst_close, subst_app, subst_lam, subst_weaken, subst_diag]
  rfl

/-- The native derivation of the two incompatible visits, instantiated at any closed operator
in any signature. -/
theorem incompatible_instances (q : Term Sig [] operator) :
    C.TheoremMinus (Term.imp (diaNe (psi q)) (neg (diaNe atomlessness))) := by
  have h := Derivable.allEβ (C.TheoremMinus.ofPure (Sig := Sig) incompatible_visits.derivable) q
  change C.TheoremMinus ((Term.imp (diaNe (psi (v0 : Term Sig [Ty.rel operator] operator)))
    (neg (diaNe atomlessness.close))).instantiate q) at h
  simpa only [instantiate, Term.imp, disj, neg, subst_app, subst_or, subst_not,
    subst_diaNe, subst_psi, subst_close, v0, subst_var, Sub.cons_zero, close_nil] using h

theorem inconsistent_of_licenses (q : Term Sig [] operator) (hclosed : (psi q).closedTypes = true)
    (hp : AxiomSet.Consistent (AxiomSet.maximalist ∪ AxiomSet.single (psi q)))
    (ha : AxiomSet.Consistent (AxiomSet.maximalist ∪ AxiomSet.single (atomlessness (Sig := Sig)))) :
    ¬ AxiomSet.Consistent (AxiomSet.strongPossibility Sig) := fun hc => hc <| by
  have hs : AxiomSet.strongPossibility Sig (diaNe (psi q)) :=
    ⟨by simpa [Term.diaNe, Term.closedTypes_rename] using hclosed, _, hp, rfl⟩
  have hat : AxiomSet.strongPossibility Sig (diaNe (atomlessness (Sig := Sig))) :=
    ⟨rfl, _, ha, rfl⟩
  exact Derivable.notE (Theorem.ax hat)
    (Theorem.mp (Theorem.ofCMinus (incompatible_instances q)) (Theorem.ax hs))

private theorem subst_guarded (s : Sub Sig Γ Δ) (b : Formula Sig Γ) (q : Term Sig Γ operator) :
    (guardedPsi b q).subst s = guardedPsi (b.subst s) (q.subst s) := by
  simp only [guardedPsi, positive, negative, forall', Term.imp, disj, eq', neg, box, top,
    subst_app, subst_lam, subst_weaken, subst_diag]
  rfl

theorem incompatible_guard_instances (q : Term Sig [] operator) (b : Sentence Sig) :
    C.TheoremMinus (Term.imp (diaNe (guardedPsi b q)) (neg (diaNe (guardedPsi (neg b) q)))) := by
  have h := Derivable.allEβ (C.TheoremMinus.ofPure (Sig := Sig) incompatible_guards.derivable) q
  change C.TheoremMinus ((forall' (Term.imp (diaNe (guardedPsi v0 v1))
    (neg (diaNe (guardedPsi (neg v0) v1))))).instantiate q) at h
  simp only [instantiate, forall', subst_app, subst_lam, subst_all] at h
  have h' := Derivable.allEβ h b
  simpa only [instantiate, Term.imp, disj, neg, subst_app, subst_or, subst_not,
    subst_diaNe, subst_guarded, v0, v1, subst_var, Sub.lift_zero, Sub.lift_succ,
    Sub.cons_zero, Sub.cons_succ, instantiate_weaken] using h'

theorem inconsistent_of_two_licenses (q : Term Sig [] operator) (b : Sentence Sig)
    (hp : AxiomSet.strongPossibility Sig (diaNe (guardedPsi b q)))
    (hn : AxiomSet.strongPossibility Sig (diaNe (guardedPsi (neg b) q))) :
    ¬ AxiomSet.Consistent (AxiomSet.strongPossibility Sig) := fun hc => hc <|
  Derivable.notE (Theorem.ax hn)
    (Theorem.mp (Theorem.ofCMinus (incompatible_guard_instances q b)) (Theorem.ax hp))

section DescriptorModel

open CategoryTheory Intensional Coalesced DistinguishedDefinable

variable {ι : Type} {C : ι → Type} [∀ i, SmallCategory (C i)]
  {A : ∀ i, Premodel Sig (C i)}
  (ne : Nonempty (names (Sig := Sig) .e))
  (I : ∀ c : Sig.Const, (action A).D (Sig.typeOf c))
  (namesAgree : TransportsConstants (action A) I)
  (models : ∀ i, (A i).IsModel)

local notation "V" => RootAction.coalescedSum (action A) (inclusion A) ne I

/-- The proof supplied by the private predecessor, expressed on the same
distinguished family used to build the descriptor root. -/
def TermSeparation (q : Term Sig [] operator) : Prop :=
  ∀ f : Term Sig [] predicate,
    (∀ k, (A k).HoldsSentence ((positive q).instantiate f)) →
    ∀ k, (A k).HoldsSentence ((negative q).instantiate f)

-- Every base descriptor continues to denote the transported entity on the whole old cone.
private theorem descriptor_after (σ : Ty) (x : (action A).D σ)
    {k : ι} {z : C k} (h : (A k).W₀ ⟶ z) :
    (A k).Incl σ z ((action A).tr σ (k := k) h x) = (A k).sem h (descriptor A σ x) .nil := by
  have ht := (action A).tr_map σ h (dist A k) x
  change (action A).tr σ (k := k) (𝟙 _ ≫ h) x = _ at ht
  rw [Category.id_comp] at ht
  rw [ht, (A k).Incl_map, ← descriptor_at]
  simpa only [Category.id_comp, Premodel.push, IEnv.map] using
    ((A k).sem_push (𝟙 _) (descriptor A σ x) .nil h).symm

include namesAgree models in
theorem holds_descriptor_exit (p : Formula Sig [Ty.rel predicate])
    (x : (action A).D (Ty.rel predicate)) {k : ι} {z : C k} (h : (A k).W₀ ⟶ z) :
    (V).Holds (CoalescedSum.arr (baseArrows A) (x := ⟨k,z⟩) h) p
      (.cons ((action A).tr _ (k := k) h x) .nil) ↔
    (A k).Holds h (p.instantiate (descriptor A _ x)) .nil := by
  let g : IEnv ((A k).Dom z) [Ty.rel predicate] := .cons ((action A).tr _ (k := k) h x) .nil
  refine ((action A).holds_arr (inclusion A) ne I (k := k) h p g).trans ?_
  have eh := (A k).rebase_sem_congr (funext fun c => tr_eq_map namesAgree c h) (𝟙 z) p g
  refine (Set.ext_iff.mp eh ⟨z, PUnit.unit, 𝟙 z⟩).trans ?_
  have base := (A k).holds_truncate h (𝟙 z) p g
  rw [Category.comp_id] at base
  refine base.trans ?_
  unfold Premodel.Holds
  rw [(A k).sem_instantiate (models k) h p (descriptor A _ x) .nil (descriptor_after _ x h)]

private theorem closed_eq_persists {T : Type} [SmallCategory T] (P : Premodel Sig T)
    (m : P.IsModel) {τ : Ty} {u v : Term Sig [] τ} {z : T} (h : P.W₀ ⟶ z)
    (heq : P.HoldsSentence (eq' u v)) : P.Holds h (eq' u v) .nil := by
  have e := (P.holds_eq m _ _ _ _).mp heq
  have shifted := congrArg (Outer.map P.inner τ h) e
  rw [← P.sem_push (𝟙 _) u .nil h, ← P.sem_push (𝟙 _) v .nil h, Category.id_comp] at shifted
  exact (P.holds_eq m _ _ _ _).mpr shifted

include namesAgree models in
theorem descriptor_guarded_endpoint (m : (V).IsModel) (q : Term Sig [] operator) (b : Sentence Sig)
    (sep : TermSeparation (A := A) q) (off : ¬ (V).HoldsSentence b) :
    (V).HoldsSentence (guardedPsi b q) := by
  rw [Premodel.HoldsSentence, guardedPsi, (V).holds_forall m]
  intro x
  rw [(V).holds_imp m, (V).holds_box m]
  intro hx
  have hpos : ∀ k, (A k).HoldsSentence ((positive q).instantiate (descriptor A _ x)) := by
    intro k
    apply (holds_descriptor_exit ne I namesAgree models (positive q) x (dist A k)).mp
    have rootEq := ((V).holds_eq m _ _ _ _).1 hx
    let h := CoalescedSum.arr (baseArrows A) (x := ⟨k,(A k).W₀⟩) (dist A k)
    have nat := congrArg (Outer.map (V).inner _ h) rootEq
    rw [← (V).sem_push, ← (V).sem_push, Category.id_comp] at nat
    exact ((V).holds_eq m _ _ _ _).2 nat
  intro site h
  rw [(V).holds_imp m]
  intro hb
  cases site with
  | root =>
    cases h
    exact False.elim (off (((V).holds_weaken _ _ _ _).1 hb))
  | of site =>
    rcases site with ⟨k,z⟩
    rw [Category.id_comp]
    apply (holds_descriptor_exit ne I namesAgree models (negative q) x h).mpr
    exact closed_eq_persists (A k) (models k) h (sep _ hpos k)

end DescriptorModel
end Classicism.Meta.StrongPossibilityReturn
