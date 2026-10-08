import Classicism.Results.SentenceSchemas.Incompatibilities
import Classicism.Models.PairInjCollapse

/-!
# Possibility excludes `□`Rigid Power

`possibility-and-necessary-rigid-power-incompatible` (Cian Dorr, 8 October 2026): Rigid Power
fails at `e → t` in the finite-support model of the pair-preserving injections and collapses
(`Monoids.PairInjCol.not_rigidPower`), so its negation there is consistent with `C`, and
Possibility makes it possible, against `□`Rigid Power (`possibility_box_inconsistent`).
-/

namespace Classicism.Meta

open AxiomSet Intensional

theorem not_rigidPower_consistent : Consistent (single (Term.neg (P.RigidPower.quoted (.arr .e .t)))) :=
  Consistent.of_model (MonoidModel.model Monoids.pairInjCol) (MonoidModel.model_isModel _)
    (Premodel.holdsAx_single _ ((Premodel.holdsSentence_neg _ (MonoidModel.model_isModel _) _).2
      Monoids.PairInjCol.not_rigidPower))

/-- `possibility-and-necessary-rigid-power-incompatible`, through the `e → t` instance. -/
theorem possibility_necRigidPower_inconsistent :
    ¬ Consistent (possibility (empty : AxiomSet Signature.pure) ∪ P.NecRigidPower.schema) := fun hc =>
  possibility_box_inconsistent (Consistent.empty_union not_rigidPower_consistent) rfl
    (Consistent.mono (fun a ha => ha.elim Or.inl (fun h => Or.inr (by
      subst (h : a = Term.box (P.RigidPower.quoted (.arr .e .t))); exact ⟨.arr .e .t, by simp, rfl⟩))) hc)

end Classicism.Meta
