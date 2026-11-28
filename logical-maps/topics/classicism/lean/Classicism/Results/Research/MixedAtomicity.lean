import Classicism.Certified.Atoms
import Classicism.Map

namespace Classicism.Proofs
open Classicism.P Classicism.Paper

variable {τ : Type} [Rel τ] [Order τ] [Pointwise τ]

/-- Dorr's lift of a self-atom, with strong atomhood assumed only for its own instance proposition. -/
theorem satom_of_selfAtom_of_satom_instantiated (X : τ) (hX : SelfAtom X)
    (hi : SAtom (Instantiated X)) : SAtom X :=
  ⟨hX.1, modal_K _ _ (modal_K _ _ (nec% (decides_of_self_clause X)) (modal_four _ hX.2)) hi.2⟩

theorem atoms_are_self_atoms_r_and_atoms_are_strong_atoms_t_imply_atoms_are_strong_atoms_r :
    AtomsAreSelfAtoms τ → AtomsAreStrongAtomsT → AtomsAreStrongAtoms τ := fun ha hs X hX =>
  satom_of_selfAtom_of_satom_instantiated X (ha X hX) (hs _ (atom_instantiated_of_atom X hX))

theorem necessary_atoms_are_self_atoms_r_and_necessary_atoms_are_strong_atoms_t_imply_necessary_atoms_are_strong_atoms_r :
    NecAtomsAreSelfAtoms τ → NecAtomsAreStrongAtomsT → NecAtomsAreStrongAtoms τ := fun ha hs =>
  modal_K _ _ (modal_K _ _ (nec%
    (atoms_are_self_atoms_r_and_atoms_are_strong_atoms_t_imply_atoms_are_strong_atoms_r (τ := τ))) ha) hs

omit [Order τ] in
theorem instantiated_restriction_only_if (X : τ) (p : Prop) :
    Instantiated (X ∧ constP p) → p := fun hi =>
  (em p).elim id (fun hn => absurd (incl_of_and_constP X (Rel.bot τ) p hn) hi)

omit [Order τ] in
theorem instantiated_restriction_if (X : τ) (p : Prop) :
    (p → Instantiated X) → p → Instantiated (X ∧ constP p) := fun h hp =>
  instantiated_mono X _ (incl_and_constP_self X p hp) (h hp)

omit [Order τ] in
/-- Restricting a relation to a part of its instance proposition gives that part as instance proposition. -/
theorem instantiated_restriction_eq (X : τ) (p : Prop) (h : p ≤ Instantiated X) :
    Instantiated (X ∧ constP p) = p :=
  le_antisymm_prop _ _ ((le_iff_prop _ _).2 (nec% (instantiated_restriction_only_if X p)))
    ((le_iff_prop _ _).2 (modal_K _ _ (nec% (instantiated_restriction_if X p)) ((le_iff_prop _ _).1 h)))

/-- An instantiated part of a self-atom is the whole atom at that point. -/
theorem self_clause_part (X Y : τ) (hx : Instantiated X → Atom X) (h : Y ≤ X)
    (hy : Instantiated Y) : Atom Y :=
  have ha := hx (instantiated_mono Y X (box_elim ((le_iff _ _).1 h)) hy)
  (em (Y = X)).elim (fun e => e.symm ▸ ha) (fun hn => by
    have hz := eq_bot_of_le_neg_rel Y ((ha Y).1 ⟨h, hn⟩)
    rw [hz] at hy
    exact absurd hy not_instantiated_bot)

theorem self_atomicity_r_and_strong_atomicity_t_imply_strong_atomicity_r :
    SelfAtomicity τ → StrongAtomicityT → StrongAtomicity τ := fun ha hs F hF =>
  (ha F hF).elim fun X hX => (hs (Instantiated X) (instantiated_ne_false X hX.1.1)).elim fun p hp =>
    have he := instantiated_restriction_eq X p hp.2
    have hc : SAtom (Instantiated (X ∧ constP p)) := he.symm ▸ hp.1
    have hn : (X ∧ constP p) ≠ Rel.bot τ := fun e => hc.1 (by
      rw [e]
      exact eq_false_of_le_neg _ ((le_iff_prop _ _).2 (nec%
        (fun (hi : Instantiated (Rel.bot τ)) => absurd hi not_instantiated_bot))))
    have hpart : (X ∧ constP p) ≤ X := (le_iff _ _).2 (nec% (incl_and_left X (constP p)))
    have hself : SelfAtom (X ∧ constP p) := ⟨hn, modal_K _ _ (modal_K _ _
      (nec% (self_clause_part X (X ∧ constP p))) hX.1.2) (box_le_rel _ _ hpart)⟩
    ⟨_, satom_of_selfAtom_of_satom_instantiated _ hself hc, le_trans_rel _ _ _ hpart hX.2⟩

theorem necessary_self_atomicity_r_and_necessary_strong_atomicity_t_imply_necessary_strong_atomicity_r :
    NecSelfAtomicity τ → NecStrongAtomicityT → NecStrongAtomicity τ := fun ha hs =>
  modal_K _ _ (modal_K _ _ (nec%
    (self_atomicity_r_and_strong_atomicity_t_imply_strong_atomicity_r (τ := τ))) ha) hs

end Classicism.Proofs

#classicism_derive Classicism.Proofs.satom_of_selfAtom_of_satom_instantiated
#classicism_derive Classicism.Proofs.instantiated_restriction_only_if
#classicism_derive Classicism.Proofs.instantiated_restriction_if
#classicism_derive Classicism.Proofs.instantiated_restriction_eq
#classicism_derive Classicism.Proofs.self_clause_part
#classicism_derive Classicism.Proofs.atoms_are_self_atoms_r_and_atoms_are_strong_atoms_t_imply_atoms_are_strong_atoms_r
#classicism_derive Classicism.Proofs.necessary_atoms_are_self_atoms_r_and_necessary_atoms_are_strong_atoms_t_imply_necessary_atoms_are_strong_atoms_r
#classicism_derive Classicism.Proofs.self_atomicity_r_and_strong_atomicity_t_imply_strong_atomicity_r
#classicism_derive Classicism.Proofs.necessary_self_atomicity_r_and_necessary_strong_atomicity_t_imply_necessary_strong_atomicity_r

#classicism_entails Classicism.Proofs.atoms_are_self_atoms_r_and_atoms_are_strong_atoms_t_imply_atoms_are_strong_atoms_r
#classicism_entails Classicism.Proofs.necessary_atoms_are_self_atoms_r_and_necessary_atoms_are_strong_atoms_t_imply_necessary_atoms_are_strong_atoms_r
#classicism_entails Classicism.Proofs.self_atomicity_r_and_strong_atomicity_t_imply_strong_atomicity_r
#classicism_entails Classicism.Proofs.necessary_self_atomicity_r_and_necessary_strong_atomicity_t_imply_necessary_strong_atomicity_r

namespace Classicism.Map

theorem atoms_are_self_atoms_r_and_atoms_are_strong_atoms_t_imply_atoms_are_strong_atoms_r :
    ∀ {Sig : Meta.Signature} (_ : Sig.Admitted) (Ax : Meta.AxiomSet Sig),
      Meta.AxiomSet.Entails Ax P.AtomsAreSelfAtoms.schemaIn →
      Meta.AxiomSet.Entails Ax P.AtomsAreStrongAtomsT.schemaIn →
      Meta.AxiomSet.Entails Ax P.AtomsAreStrongAtoms.schemaIn := by
  map_cert Proofs.atoms_are_self_atoms_r_and_atoms_are_strong_atoms_t_imply_atoms_are_strong_atoms_r.entails

theorem necessary_atoms_are_self_atoms_r_and_necessary_atoms_are_strong_atoms_t_imply_necessary_atoms_are_strong_atoms_r :
    ∀ {Sig : Meta.Signature} (_ : Sig.Admitted) (Ax : Meta.AxiomSet Sig),
      Meta.AxiomSet.Entails Ax P.NecAtomsAreSelfAtoms.schemaIn →
      Meta.AxiomSet.Entails Ax P.NecAtomsAreStrongAtomsT.schemaIn →
      Meta.AxiomSet.Entails Ax P.NecAtomsAreStrongAtoms.schemaIn := by
  map_cert Proofs.necessary_atoms_are_self_atoms_r_and_necessary_atoms_are_strong_atoms_t_imply_necessary_atoms_are_strong_atoms_r.entails

theorem self_atomicity_r_and_strong_atomicity_t_imply_strong_atomicity_r :
    ∀ {Sig : Meta.Signature} (_ : Sig.Admitted) (Ax : Meta.AxiomSet Sig),
      Meta.AxiomSet.Entails Ax P.SelfAtomicity.schemaIn →
      Meta.AxiomSet.Entails Ax P.StrongAtomicityT.schemaIn →
      Meta.AxiomSet.Entails Ax P.StrongAtomicity.schemaIn := by
  map_cert Proofs.self_atomicity_r_and_strong_atomicity_t_imply_strong_atomicity_r.entails

theorem necessary_self_atomicity_r_and_necessary_strong_atomicity_t_imply_necessary_strong_atomicity_r :
    ∀ {Sig : Meta.Signature} (_ : Sig.Admitted) (Ax : Meta.AxiomSet Sig),
      Meta.AxiomSet.Entails Ax P.NecSelfAtomicity.schemaIn →
      Meta.AxiomSet.Entails Ax P.NecStrongAtomicityT.schemaIn →
      Meta.AxiomSet.Entails Ax P.NecStrongAtomicity.schemaIn := by
  map_cert Proofs.necessary_self_atomicity_r_and_necessary_strong_atomicity_t_imply_necessary_strong_atomicity_r.entails

end Classicism.Map
