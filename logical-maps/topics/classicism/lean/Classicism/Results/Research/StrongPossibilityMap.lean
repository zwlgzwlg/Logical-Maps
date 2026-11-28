import Classicism.StrongPossibility.UnaryInconsistent
import Classicism.Statements

/-! Both forms of Strong Possibility use the same two pure sentences in every
closed-type signature. A named distinction can be permanent at the ordinary
descriptor root; its private copy can merge at every exit of the second root. -/

namespace Classicism.Meta.StrongPossibilityMap

/-- No theory in the pure language can consistently assert all the instances of SP. -/
theorem pure_inconsistent : ¬ AxiomSet.Consistent (AxiomSet.strongPossibility Signature.pure) :=
  UnarySP.pure_inconsistent

/-- Strong Possibility (pure) implies a contradiction in any admitted ambient signature. -/
theorem strong_possibility_r_inconsistent : Classicism.Statements.strong_possibility_r_inconsistent := by
  intro Sig _ Ax ent cons
  exact AxiomSet.not_consistent_ofPure pure_inconsistent (AxiomSet.Consistent.of_entails ent cons)

/-- The named case of the uniform closed-signature argument. -/
theorem named_inconsistent {Sig : Signature} [Countable Sig.Const] (hS : Sig.Closed)
    (_hn : Nonempty (Coalesced.DistinguishedDefinable.names (Sig := Sig) .e))
    (c : Sig.Const) {ρ : RTy} (_hc : Sig.typeOf c = .rel ρ) :
    ¬ AxiomSet.Consistent (AxiomSet.strongPossibility Sig) :=
  UnarySP.inconsistent_in_closed_signature hS

/-- Lift uniform object-theory inconsistency to the generated signature map statement. -/
theorem signature_map_of_inconsistent
    (h : ∀ {Sig : Signature}, Sig.Admitted → ¬ AxiomSet.Consistent (AxiomSet.strongPossibility Sig)) :
    Classicism.Statements.strong_possibility_signature_r_inconsistent := by
  intro Sig adm Ax ent cons
  exact h adm (AxiomSet.Consistent.of_entails ent cons)

/-- The signature-level map statement, including signatures of arbitrary cardinality
and signatures without a public individual name. -/
theorem strong_possibility_signature_r_inconsistent :
    Classicism.Statements.strong_possibility_signature_r_inconsistent :=
  signature_map_of_inconsistent UnarySP.inconsistent_in_admitted_signature

end Classicism.Meta.StrongPossibilityMap
