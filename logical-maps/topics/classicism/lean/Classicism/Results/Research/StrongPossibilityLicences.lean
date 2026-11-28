import Classicism.Coalesced.DescriptorColours
import Classicism.Results.Research.StrongPossibilityReturn

/-! Two ordinary-Maximalism licences for the diagonal return.  The term-separation
hypothesis is the semantic statement supplied by the private predecessor construction. -/

namespace Classicism.Meta.StrongPossibilityLicences

open CategoryTheory Intensional Coalesced DescriptorColours StrongPossibilityReturn Term

variable {Sig : Signature}

theorem closed_guarded {Γ : Ctx} {b : Formula Sig Γ} {q : Term Sig Γ operator}
    (hb : b.closedTypes = true) (hq : q.closedTypes = true) :
    (guardedPsi b q).closedTypes = true := by
  simp [guardedPsi, positive, negative, diag, rho, Term.closedTypes, weaken,
    closedTypes_rename, hb, hq, v0, v1, probe, predicate, operator]

theorem licensed {b : Sentence Sig} {q : Term Sig [] operator}
    (hc : b.closedTypes = true) (hq : q.closedTypes = true)
    (H : AxiomSet.Consistent (AxiomSet.maximalist ∪ AxiomSet.single (guardedPsi b q))) :
    AxiomSet.strongPossibility Sig (diaNe (guardedPsi b q)) :=
  ⟨by simpa [Term.diaNe, closedTypes_rename] using closed_guarded hc hq, _, H, rfl⟩

section Named

variable [Countable Sig.Const] (hS : Sig.Closed)
  (hn : Nonempty (DistinguishedDefinable.names (Sig := Sig) .e))
  (q : Term Sig [] operator) (hq : q.closedTypes = true)
  (sep : TermSeparation (A := canonicalFamily Sig) q)

include hS hn sep in
theorem named_endpoint (colour : Bool) (b : Sentence Sig)
    (off : ¬ (model (canonicalFamily Sig) hn colour).HoldsSentence b) :
    AxiomSet.Consistent (AxiomSet.maximalist ∪ AxiomSet.single (guardedPsi b q)) :=
  licence hS hn colour
    (descriptor_guarded_endpoint hn _ (transports _ colour) canonicalFamily_isModel
      (isModel _ hn canonicalFamily_isModel colour) q b sep off)

include hS hn sep in
theorem named_licences (c : Sig.Const) {ρ : RTy} (h : Sig.typeOf c = .rel ρ) :
    AxiomSet.Consistent (AxiomSet.maximalist ∪ AxiomSet.single (guardedPsi (emptyRow c h) q)) ∧
    AxiomSet.Consistent (AxiomSet.maximalist ∪ AxiomSet.single (guardedPsi (neg (emptyRow c h)) q)) := by
  have hc : (Ty.rel ρ).Closed := by rw [← h]; exact hS c
  constructor
  · apply named_endpoint hS hn q sep true _
    intro H
    exact Bool.noConfusion ((holds_emptyRow _ hn canonicalFamily_isModel true c h hc).1 H)
  · apply named_endpoint hS hn q sep false _
    intro H
    exact ((model (canonicalFamily Sig) hn false).holds_neg
        (isModel _ hn canonicalFamily_isModel false) _ _ _).1 H <|
      (holds_emptyRow _ hn canonicalFamily_isModel false c h hc).2 rfl

include hS hn hq sep in
theorem named_inconsistent (c : Sig.Const) {ρ : RTy} (h : Sig.typeOf c = .rel ρ) :
    ¬ AxiomSet.Consistent (AxiomSet.strongPossibility Sig) := by
  have hc : (Ty.rel ρ).Closed := by rw [← h]; exact hS c
  have he := closed_emptyRow h hc
  obtain ⟨pos, neg⟩ := named_licences hS hn q sep c h
  exact inconsistent_of_two_licenses q (emptyRow c h)
    (licensed he hq pos) (licensed (by simpa using he) hq neg)

end Named

end Classicism.Meta.StrongPossibilityLicences
