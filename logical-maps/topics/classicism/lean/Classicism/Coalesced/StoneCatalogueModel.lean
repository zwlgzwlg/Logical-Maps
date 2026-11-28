import Classicism.Coalesced.StonePossibilism

/-! Separate map record for the identity-loop fan on the bounded catalogue
of all Boolean algebras. Its displayed signature has one proposition name. -/

namespace Classicism.Meta.Coalesced.StoneFan.CatalogueModel

open CategoryTheory Classicism.Meta.Intensional Canonical

/-- The map's schema ranges over closed carrier types. The stronger joint
theorem checks even the additional type-variable instances of the deep syntax. -/
def revisedMP (Sig : Signature) : AxiomSet Sig := fun a =>
  ∃ σ : Ty, σ.Closed ∧ a = Term.ofPure (Classicism.StoneMP.MPAt.term σ)

private instance countableNames : Countable Signature.sigmaTop.Const := inferInstanceAs (Countable Unit)

private abbrev names := Signature.sigmaTop

noncomputable abbrev model := fan names (terminal names) (boundedSpace (ordinalCut names).out)

theorem isModel : model.IsModel :=
  (maximalist_mathematical_possibilism names Signature.sigmaTop_admitted.1).1

theorem pure_maximalism :
    model.IsModel ∧ model.HoldsAx (AxiomSet.pureVersion AxiomSet.distinctnessC) :=
  ⟨isModel, (maximalist_mathematical_possibilism names Signature.sigmaTop_admitted.1).2.2.1⟩

theorem signature_maximalism :
    model.Admitted ∧ model.IsModel ∧ model.HoldsAx (AxiomSet.distinctnessC names) :=
  ⟨Signature.sigmaTop_admitted, isModel,
   (maximalist_mathematical_possibilism names Signature.sigmaTop_admitted.1).2.1⟩

theorem mathematical_possibilism : model.IsModel ∧ model.HoldsAx (revisedMP names) :=
  ⟨isModel, fun _ ⟨σ, _, he⟩ => (maximalist_mathematical_possibilism names Signature.sigmaTop_admitted.1).2.2.2 _ ⟨σ, he⟩⟩

theorem certificate :
    ∃ (S : Signature) (_ : S.Admitted) (Ax : AxiomSet S),
      Ax.Consistent ∧ Ax.Complete ∧
      Ax.Entails (AxiomSet.pureVersion AxiomSet.distinctnessC) ∧
      Ax.Entails (AxiomSet.distinctnessC S) ∧ Ax.Entails (revisedMP S) :=
  ⟨names, Signature.sigmaTop_admitted, model.theory, model.theory_consistent isModel,
    model.theory_complete isModel, model.entails_of_holdsAx isModel pure_maximalism.2,
    model.entails_of_holdsAx isModel signature_maximalism.2.2,
    model.entails_of_holdsAx isModel mathematical_possibilism.2⟩

#print axioms certificate

end Classicism.Meta.Coalesced.StoneFan.CatalogueModel
