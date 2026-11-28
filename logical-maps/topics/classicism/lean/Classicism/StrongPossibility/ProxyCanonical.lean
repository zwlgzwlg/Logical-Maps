import Classicism.Results.Research.StrongPossibilityReturn
import Classicism.Results.Research.StrongPossibilityLicences
import Classicism.StrongPossibility.ProxySeparation
import Classicism.StrongPossibility.ProxyCanonicalCore

namespace Classicism.Meta.ProxyDiagonal

open CategoryTheory Intensional Coalesced Completeness Term

noncomputable section
variable {Sig : Signature}

private theorem twice_weaken {σ τ υ : Ty} (p : Term Sig [] σ) :
    p.weaken.weaken (τ := τ) = p.close (Γ := τ :: υ :: []) := by
  unfold weaken close
  rw [rename_rename]
  congr 1
  funext α a; cases a

theorem return_rho (q : Term Sig [] StrongPossibilityReturn.operator) : StrongPossibilityReturn.rho q = russell q := by
  unfold StrongPossibilityReturn.rho russell
  rw [twice_weaken]

theorem return_diag : StrongPossibilityReturn.diag (Q (Sig := Sig)) = d := by
  change Term.app Q (StrongPossibilityReturn.rho _) = Term.app Q (russell Q)
  rw [return_rho]

set_option maxRecDepth 25000 in
set_option maxHeartbeats 1400000 in
theorem ofPure_Q : Term.ofPure (Sig := Sig) (Q (Sig := Signature.pure)) = Q := rfl

set_option maxRecDepth 25000 in
set_option maxHeartbeats 1400000 in
theorem Q_closedTypes : (Q (Sig := Sig)).closedTypes = true := rfl

/-- The private predecessor entails precisely the universally quantified
canonical descriptor condition used in the two-return argument. -/
theorem canonical_proxy_separation [Countable Sig.Const] (build : Predecessors Sig) :
    StrongPossibilityReturn.TermSeparation (A := canonicalFamily Sig) Q := by
  intro f hp w
  rw [StrongPossibilityReturn.negative_instantiate, return_diag]
  apply canonical_diag build f _ w
  intro k
  have H := hp k
  rw [StrongPossibilityReturn.positive_instantiate, return_diag] at H
  exact H

theorem named_from_predecessors [Countable Sig.Const] (hS : Sig.Closed)
    (hn : Nonempty (DistinguishedDefinable.names (Sig := Sig) .e)) (build : Predecessors Sig)
    (c : Sig.Const) {ρ : RTy} (hc : Sig.typeOf c = .rel ρ) :
    ¬AxiomSet.Consistent (AxiomSet.strongPossibility Sig) :=
  StrongPossibilityLicences.named_inconsistent hS hn Q Q_closedTypes
    (canonical_proxy_separation build) c hc

end
end Classicism.Meta.ProxyDiagonal
