import Classicism.Certified.Atoms
import Classicism.Map

namespace Classicism.Proofs
open Classicism.P Classicism.Paper

variable {τ : Type} [Rel τ] [Order τ] [Pointwise τ]

theorem self_condition_decides (X : τ) (a : SelfAtomsAreAtoms τ)
    (h : □ (Instantiated X → Atom X)) : ∀ Y : τ, X ≤ Y ∨ X ≤ ¬ Y :=
  (em (X = ⊥)).elim
    (fun e Y => Or.inl (by rw [e]; exact bot_le_rel Y))
    (fun hne => decides_of_atom X (a X ⟨hne, h⟩))

theorem self_atoms_strong_at_point :
    NecSelfAtomsAreAtoms τ → SelfAtomsAreStrongAtoms τ := fun h X hx =>
  ⟨hx.1, modal_K _ _ (modal_K _ _ (nec% (self_condition_decides X)) h)
    (modal_four _ hx.2)⟩

theorem necessary_self_atoms_are_atoms_r_implies_necessary_self_atoms_are_strong_atoms_r :
    NecSelfAtomsAreAtoms τ → NecSelfAtomsAreStrongAtoms τ := fun h =>
  modal_K _ _ (nec% (self_atoms_strong_at_point (τ := τ))) (modal_four _ h)

end Classicism.Proofs

#classicism_derive Classicism.Proofs.self_condition_decides
#classicism_derive Classicism.Proofs.self_atoms_strong_at_point
#classicism_derive Classicism.Proofs.necessary_self_atoms_are_atoms_r_implies_necessary_self_atoms_are_strong_atoms_r
#classicism_entails Classicism.Proofs.necessary_self_atoms_are_atoms_r_implies_necessary_self_atoms_are_strong_atoms_r

namespace Classicism.Map

theorem necessary_self_atoms_are_atoms_r_implies_necessary_self_atoms_are_strong_atoms_r :
    ∀ {Sig : Meta.Signature} (_ : Sig.Admitted) (Ax : Meta.AxiomSet Sig),
      Meta.AxiomSet.Entails Ax P.NecSelfAtomsAreAtoms.schemaIn →
      Meta.AxiomSet.Entails Ax P.NecSelfAtomsAreStrongAtoms.schemaIn := by
  map_cert Proofs.necessary_self_atoms_are_atoms_r_implies_necessary_self_atoms_are_strong_atoms_r.entails

end Classicism.Map
