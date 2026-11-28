import Classicism.StrongPossibility.Permanent
import Classicism.StrongPossibility.FiniteMaxSupport
import Classicism.StrongPossibility.UnaryLicences

namespace Classicism.Proofs.UnarySP
open Classicism.P Classicism.Paper

/-- Name the guard law as a function so the quoted theorem applies to its
ordinary application in every ambient signature. -/
theorem permanent_returns (Q : Family) (H : Prop → Prop) (same : H = guarded Q) :
    DiaNe permanent → DiaNe (H permanent) → False :=
  same.symm ▸ permanent_contradiction Q

end Classicism.Proofs.UnarySP
#classicism_derive Classicism.Proofs.UnarySP.permanent_returns

namespace Classicism.Meta.UnarySP
open Term FiniteMaxSupport Classicism.Proofs.UnarySP

/-- A fixed pure licence in every finite marked language transfers to every
closed-type signature, even if it has no individual names of its own. -/
theorem pure_licence_of_finite {Sig : Signature} (hS : Sig.Closed) (p : Sentence Signature.pure)
    (localCon : ∀ (T : Signature) [Finite T.Const], T.Closed →
      Nonempty (Coalesced.DistinguishedDefinable.names (Sig := T) .e) →
      AxiomSet.Consistent (AxiomSet.maximalist ∪ AxiomSet.single (ofPure (Sig := T) p))) :
    AxiomSet.Consistent (AxiomSet.maximalist ∪ AxiomSet.single (ofPure (Sig := Sig) p)) := by
  apply consistent_max_of_finite hS _ ∅ Set.finite_empty
  intro U hU _ hp
  rw [narrow_ofPure U p hp]
  let _ : Finite (marked U).Const := marked_finite hU
  exact localCon (marked U) (marked_closed hS U) ⟨⟨.inr (),rfl⟩⟩

private theorem return_law (q : Term Signature.pure [] StrongPossibility.UnaryReading.Family)
    (law : Term Signature.pure [] (Ty.t ⇒ RTy.t)) :
    C.Theorem (Term.imp (eq' law (Term.apply guarded.term q))
      (Term.imp (diaNe permanent.term) (neg (diaNe (.app law permanent.term))))) :=
  Derivable.allE₂β permanent_returns.derivable q law

/-- The sole two licences needed for Strong Possibility are K and H(K). -/
theorem inconsistent_of_permanent_licences {Sig : Signature}
    (pos : AxiomSet.Consistent (AxiomSet.maximalist ∪
      AxiomSet.single (ofPure (Sig := Sig) permanent.term)))
    (guard : AxiomSet.Consistent (AxiomSet.maximalist ∪
      AxiomSet.single (guardedAt (ofPure (Sig := Sig) permanent.term)))) :
    ¬ AxiomSet.Consistent (AxiomSet.strongPossibility Sig) := by
  have pureLaw := Theorem.mp (return_law operator.term guardedLaw.term) (Derivable.refl guardedLaw.term)
  have clause : C.Theorem (Term.imp (diaNe (ofPure (Sig := Sig) permanent.term))
      (neg (diaNe (guardedAt (ofPure permanent.term))))) := C.Theorem.ofPure pureLaw
  have hp : AxiomSet.strongPossibility Sig (diaNe (ofPure permanent.term)) := ⟨rfl,_,pos,rfl⟩
  have hg : AxiomSet.strongPossibility Sig (diaNe (guardedAt (ofPure permanent.term))) :=
    ⟨rfl,_,guard,rfl⟩
  exact fun hc => hc <| Derivable.notE (Theorem.ax hg)
    (Theorem.mp (Theorem.ofC clause) (Theorem.ax hp))

end Classicism.Meta.UnarySP
