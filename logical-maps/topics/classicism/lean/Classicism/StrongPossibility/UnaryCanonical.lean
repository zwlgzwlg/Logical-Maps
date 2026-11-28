import Classicism.StrongPossibility.UnaryReading
import Classicism.Completeness.CanonicalTransfer
import Classicism.Syntax.Russell
import Classicism.Coalesced.DistinguishedDefinable
import Classicism.Coalesced.Complete

/-! Turning a unary predecessor construction into separation on a whole canonical
family. The individual parameter and the candidate descriptor remain fixed after
repointing at a later world. -/

namespace Classicism.Meta.StrongPossibility.UnaryCanonical

open CategoryTheory Intensional Coalesced Completeness Term UnaryReading

variable {Sig : Signature}

abbrev qAt (b : Term Sig [] Ty.e) : Term Sig [] ((Tester : Ty) ⇒ S) := .app op b
abbrev rhoAt (b : Term Sig [] Ty.e) : Term Sig [] Tester := Diagonal.russell (qAt b)
abbrev diagAt (b : Term Sig [] Ty.e) : Term Sig [] S := .app (qAt b) (rhoAt b)

/-- A failed truth at an old point produces a genuine model refuting the identity. -/
def Predecessors (Sig : Signature) : Prop :=
  ∀ {C : Type} [SmallCategory C] (O : Premodel Sig C), O.IsModel →
    O.HoldsAx AxiomSet.varExistence →
    ∀ (n : DistinguishedDefinable.names (Sig := Sig) .e) (f : Term Sig [] Tester),
      ¬ O.HoldsSentence (.app f (diagAt (constAt n.1 n.2))) →
      ∃ (D : Type) (_ : SmallCategory D) (B : Premodel Sig D),
        B.IsModel ∧ B.HoldsAx AxiomSet.varExistence ∧
        ¬ B.HoldsSentence (eq' (.app (qAt (constAt n.1 n.2)) f) (diagAt (constAt n.1 n.2)))

/-- If an identity holds at every canonical point, the descriptor accepts its
diagonal at every continuation of every canonical point. -/
theorem canonical_separation [Countable Sig.Const] (build : Predecessors Sig)
    (n : DistinguishedDefinable.names (Sig := Sig) .e) (f : Term Sig [] Tester)
    (pos : ∀ w, (canonicalFamily Sig w).HoldsSentence
      (eq' (.app (qAt (constAt n.1 n.2)) f) (diagAt (constAt n.1 n.2)))) :
    ∀ w, (canonicalFamily Sig w).HoldsSentence
      (box (.app f (diagAt (constAt n.1 n.2)))) := by
  refine Canonical.box_of_countermodels _ _ ?_ pos
  intro C _ O M vars fail
  exact build O M vars n f fail

end Classicism.Meta.StrongPossibility.UnaryCanonical
