import Classicism.StrongPossibility.PermanentReturns
import Classicism.StrongPossibility.UnaryUniformPositive
import Classicism.StrongPossibility.UnaryUniformNegative

/-! Both Strong Possibility statements follow from the same two pure licences.
Finite support permits arbitrarily large closed-type signatures, including
signatures with no public names. -/

namespace Classicism.Meta.UnarySP

open Term Classicism.Proofs.UnarySP

theorem inconsistent_in_closed_signature {Sig : Signature} (hS : Sig.Closed) :
    ¬ AxiomSet.Consistent (AxiomSet.strongPossibility Sig) := by
  apply inconsistent_of_permanent_licences
  · exact pure_licence_of_finite hS permanent.term fun _ _ closed named =>
      permanent_licence closed named
  · exact pure_licence_of_finite hS (.app guardedLaw.term permanent.term)
      fun _ _ closed named => guarded_permanent_licence closed named

theorem inconsistent_in_admitted_signature {Sig : Signature} (hs : Sig.Admitted) :
    ¬ AxiomSet.Consistent (AxiomSet.strongPossibility Sig) :=
  inconsistent_in_closed_signature hs.1

end Classicism.Meta.UnarySP
