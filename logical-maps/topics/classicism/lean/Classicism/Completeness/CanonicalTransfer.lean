import Classicism.Completeness.Completeness
import Classicism.Semantics.VariableExistence
import Classicism.Semantics.IntensionalTheory

/-! Refutation and repointing for the canonical model with variable witnesses. -/

namespace Classicism.Meta.Completeness.Canonical
open CategoryTheory Intensional Term

variable {Sig : Signature} [Countable Sig.Const]

theorem holds_varExistence (w : World Sig) : (premodel w).HoldsAx AxiomSet.varExistence := by
  intro a ha
  obtain ⟨i,rfl⟩ := ha
  exact (Canonical.holdsSentence_iff w _).2 (w.exists_self_mem (.var i))

/-- Canonicalize any sentence of the *full* Lean signature whenever the input model
contains witnesses at each schematic type variable. -/
theorem refutes_of_countermodel {C : Type} [SmallCategory C] (B : Premodel Sig C) (M : B.IsModel)
    (hv : B.HoldsAx AxiomSet.varExistence) (p : Sentence Sig) (hp : ¬B.HoldsSentence p) :
    ∃ w : World Sig, ¬ (premodel w).HoldsSentence p := by
  have hneg := (B.holdsSentence_neg M p).2 hp
  have hc := AxiomSet.Consistent.of_model B M (B.holdsAx_union (B.holdsAx_single hneg) hv)
  obtain ⟨w, hw⟩ := exists_world_of_varExistence hc
  refine ⟨w, ((premodel w).holdsSentence_neg (Canonical.isModel w) p).1 ?_⟩
  exact (Canonical.holdsSentence_iff w _).2 (hw _ ⟨neg p, rfl, rfl⟩)

/-- If every countermodel to q yields a countermodel to p, universal canonical
truth of p forces q at every continuation of every canonical point. -/
theorem box_of_countermodels (p q : Sentence Sig)
    (build : ∀ {C : Type} [SmallCategory C] (O : Premodel Sig C), O.IsModel →
      O.HoldsAx AxiomSet.varExistence → ¬ O.HoldsSentence q →
      ∃ (D : Type) (_ : SmallCategory D) (B : Premodel Sig D),
        B.IsModel ∧ B.HoldsAx AxiomSet.varExistence ∧ ¬ B.HoldsSentence p)
    (pos : ∀ w : World Sig, (premodel w).HoldsSentence p) :
    ∀ w : World Sig, (premodel w).HoldsSentence (box q) := by
  intro w
  let O := premodel w
  have M : O.IsModel := isModel w
  apply (O.box_iff_truncate M q).mpr
  intro V h
  by_contra fail
  obtain ⟨D, instD, B, MB, vars, rejects⟩ :=
    build (O.truncate h) (O.isModel_truncate h M)
      (O.holdsAx_varExistence_truncate M (holds_varExistence w) h) fail
  obtain ⟨v, hv⟩ := refutes_of_countermodel B MB vars p rejects
  exact hv (pos v)

end Classicism.Meta.Completeness.Canonical
