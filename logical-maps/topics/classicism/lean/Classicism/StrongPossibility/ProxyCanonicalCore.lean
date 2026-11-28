import Classicism.Completeness.CanonicalTransfer
import Classicism.StrongPossibility.ProxyVarExistence
import Classicism.StrongPossibility.ProxyTerms
import Classicism.Coalesced.Complete

namespace Classicism.Meta.ProxyDiagonal
open CategoryTheory Intensional Coalesced Completeness Term

noncomputable section
variable {Sig : Signature}

/-- Untyped model transfer used by the canonical descriptor argument. No closed-type
restriction is imposed on the marked term's *internal* syntax. -/
def Predecessors (Sig : Signature) : Prop :=
  ∀ {C : Type} [SmallCategory C] (O : Premodel Sig C), O.IsModel →
    O.HoldsAx AxiomSet.varExistence → Nonempty (O.Dom O.W₀ .e) →
    ∀ f : Term Sig [] Tester, ¬O.HoldsSentence (.app f d) →
      ∃ (D : Type) (_ : SmallCategory D) (B : Premodel Sig D),
        B.IsModel ∧ B.HoldsAx AxiomSet.varExistence ∧ ¬B.HoldsSentence (eq' (.app Q f) d)

variable [Countable Sig.Const]

theorem canonical_vars (w : World Sig) : (canonicalFamily Sig w).HoldsAx AxiomSet.varExistence :=
  Canonical.holds_varExistence w

/-- Canonicalize any sentence of the *full* Lean signature whenever the input model
contains witnesses at each schematic type variable. -/
theorem canonical_refutation {C : Type} [SmallCategory C] (B : Premodel Sig C) (M : B.IsModel)
    (hv : B.HoldsAx AxiomSet.varExistence) (p : Sentence Sig) (hp : ¬B.HoldsSentence p) :
    ∃ w : World Sig, ¬ (canonicalFamily Sig w).HoldsSentence p :=
  Canonical.refutes_of_countermodel B M hv p hp

/-- A universal canonical identity Qf=d forces the truth of f(d) at ALL addresses of
every canonical base point. -/
theorem canonical_diag (build : Predecessors Sig) (f : Term Sig [] Tester)
    (pos : ∀ w : World Sig, (canonicalFamily Sig w).HoldsSentence (eq' (.app Q f) d)) :
    ∀ w : World Sig, (canonicalFamily Sig w).HoldsSentence (box (.app f d)) := by
  refine Canonical.box_of_countermodels _ _ ?_ pos
  intro C _ O M vars fail
  exact build O M vars (O.nonempty_e O.W₀) f fail

end
end Classicism.Meta.ProxyDiagonal
