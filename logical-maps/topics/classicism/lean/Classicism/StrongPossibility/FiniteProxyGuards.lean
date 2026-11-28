import Classicism.StrongPossibility.FiniteMaxSupport
import Classicism.Results.Research.StrongPossibilityLicences
import Classicism.StrongPossibility.ProxyCanonical
import Classicism.Results.SentenceSchemas.SeparatedStructure

/-! The two diagonal return guards commute with restriction to any set of
names containing the single relational name they mention. -/

namespace Classicism.Meta.FiniteMaxSupport

open Term Coalesced DescriptorColours StrongPossibilityReturn

variable {Sig : Signature} {ρ : RTy}

/-- Use either sign of the current row test on the public relation. -/
def rowGuard (s : Bool) (c : Sig.Const) (h : Sig.typeOf c = .rel ρ) : Sentence Sig :=
  if s then emptyRow c h else Term.neg (emptyRow c h)

/-- A closed ordinary Maximalism licence over a single public symbol. -/
def endpoint (s : Bool) (c : Sig.Const) (h : Sig.typeOf c = .rel ρ) : Sentence Sig :=
  guardedPsi (rowGuard s c h) ProxyDiagonal.Q

private theorem narrow_constAt (U : Set Sig.Const) {Γ : Ctx} {σ : Ty}
    (c : Sig.Const) (h : Sig.typeOf c = σ) (m : c ∈ U) (hc) :
    narrow U (constAt (Γ := Γ) c h) hc =
      constAt (Sig := marked U) (.inl ⟨c,m⟩) h := by
  subst σ
  rfl

private theorem narrow_rename (U : Set Sig.Const) {Γ Δ : Ctx} {σ : Ty}
    (t : Term Sig Γ σ) (r : Ren Γ Δ) (hr : (t.rename r).consts ⊆ U) :
    narrow U (t.rename r) hr =
      (narrow U t (by simpa only [Term.consts_rename] using hr)).rename r := by
  induction t generalizing Δ with
  | app f a hf ha =>
    exact congrArg₂ Term.app (hf r _) (ha r _)
  | lam b ih =>
    exact congrArg Term.lam (ih (Ren.lift r) _)
  | _ => rfl

private theorem narrow_Q (U : Set Sig.Const) (hq) :
    narrow U (ProxyDiagonal.Q (Sig := Sig)) hq = ProxyDiagonal.Q := by
  simpa only [ProxyDiagonal.ofPure_Q] using
    (narrow_ofPure (Sig := Sig) U (ProxyDiagonal.Q (Sig := Signature.pure))
      (by simpa only [ProxyDiagonal.ofPure_Q] using hq))

private theorem narrow_emptyRow (U : Set Sig.Const) (c : Sig.Const)
    (h : Sig.typeOf c = .rel ρ) (m : c ∈ U) (hp) :
    narrow U (emptyRow c h) hp = emptyRow (Sig := marked U) (.inl ⟨c,m⟩) h := by
  have t := narrow_constAt (Γ := []) U c h m
    (show (constAt (Γ := []) c h).consts ⊆ U by simpa only [constAt_consts, Set.singleton_subset_iff] using m)
  exact congrArg (fun x => Term.app (Term.app (Term.inclR ρ) x) (Term.app (Term.negR ρ) x)) t

private theorem narrow_guardedPsi (U : Set Sig.Const) {Γ : Ctx} (b : Formula Sig Γ)
    (q : Term Sig Γ operator) (hb : b.consts ⊆ U) (hq : q.consts ⊆ U) (hp) :
    narrow U (guardedPsi b q) hp = guardedPsi (narrow U b hb) (narrow U q hq) := by
  simp only [guardedPsi, positive, negative, diag, rho, forall', Term.imp, disj,
    conj, Term.neg, box, eq', exists', weaken, top, v0, v1, narrow]
  repeat' erw [narrow_rename]

private theorem Q_support (U : Set Sig.Const) : (ProxyDiagonal.Q (Sig := Sig)).consts ⊆ U := by
  rw [← ProxyDiagonal.ofPure_Q, Term.consts_ofPure]
  exact Set.empty_subset _

theorem narrow_endpoint (U : Set Sig.Const) (s : Bool) (c : Sig.Const)
    (h : Sig.typeOf c = .rel ρ) (m : c ∈ U) (hc) :
    narrow U (endpoint s c h) hc = endpoint (Sig := marked U) s (.inl ⟨c,m⟩) h := by
  have he : (emptyRow c h).consts ⊆ U := by
    simp [emptyRow, Term.consts, constAt_consts, m]
  have hb : (rowGuard s c h).consts ⊆ U := by
    cases s <;> simpa [rowGuard, Term.neg, Term.consts] using he
  apply (narrow_guardedPsi U _ _ hb (Q_support U) hc).trans
  apply congrArg₂ guardedPsi _ (narrow_Q U _)
  cases s
  · exact congrArg Term.neg (narrow_emptyRow U c h m he)
  · exact narrow_emptyRow U c h m he

end Classicism.Meta.FiniteMaxSupport
