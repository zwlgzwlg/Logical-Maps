import Classicism.Certified.Atoms
import Classicism.Map

namespace Classicism.Proofs
open Classicism.P Classicism.Paper

theorem incompatible_orders_of_possible (p q : Prop) (hp : ◇ p)
    (hn : p ≤ ¬ q) : ¬ (p ≤ q) := fun h =>
  not_le_neg_of_ne_false p hp (le_neg_of_le_both_rel p q h hn)

/-- At a true self-atom, if the recurring guard forces the positive decision, that decision holds. -/
theorem forced_self_decision_positive (a p q : Prop) (h : Instantiated p → Atom p)
    (ha : ◇ a) (hp : □ (◇ p)) (hpos : a ≤ (p ≤ q)) : p → q := fun ht =>
  have hA := h (fun hn => (hn ht).elim)
  (atom_le_or_le_neg p q hA).elim (fun hi => imp_of_le_prop _ _ hi ht) fun hn =>
    absurd (dia_mono _ _ ((le_iff_prop _ _).1 hpos) ha)
      (not_dia_of_box_not _ (modal_K _ _ (modal_K _ _
        (nec% (incompatible_orders_of_possible p q)) hp) (box_le_prop _ _ hn)))

/-- A positive order decision is an identity, so cannot coexist with a possible guard denying it. -/
theorem forced_self_decision_negative (a p q : Prop) (h : Instantiated p → Atom p)
    (ha : ◇ a) (hneg : a ≤ ¬ (p ≤ q)) : p → ¬ q := fun ht =>
  have hA := h (fun hn => (hn ht).elim)
  (atom_le_or_le_neg p q hA).elim (fun hi =>
    absurd (box_le_prop p q hi)
      ((dia_not_eq _).mp (dia_mono _ _ ((le_iff_prop _ _).1 hneg) ha)))
    (fun hn => imp_of_le_prop _ _ hn ht)

/-- A recurring decider fixes the choice for every proposition in the current domain. -/
theorem recurring_guard_decides_self (a p : Prop)
    (h : □ (Instantiated p → Atom p)) (ha : □ (◇ a)) (hp : □ (◇ p))
    (dec : ∀ t : Prop, a ≤ t ∨ a ≤ ¬ t) : ∀ q : Prop, p ≤ q ∨ p ≤ ¬ q := fun q =>
  (dec (p ≤ q)).elim
    (fun hy => Or.inl ((le_iff_prop _ _).2
      (modal_K _ _ (modal_K _ _ (modal_K _ _ (modal_K _ _
        (nec% (forced_self_decision_positive a p q)) h) ha) (modal_four _ hp)) (box_le_prop _ _ hy))))
    (fun hn => Or.inr ((le_iff_prop _ _).2
      (modal_K _ _ (modal_K _ _ (modal_K _ _
        (nec% (forced_self_decision_negative a p q)) h) ha) (box_le_prop _ _ hn))))

theorem distinctness_necessary_t_and_strong_actuality_imply_self_atoms_are_strong_atoms_t :
    NecessityOfDistinctnessT → StrongActuality → SelfAtomsAreStrongAtomsT := fun nd actual p hs =>
  actual.elim fun a ha =>
    have hrec := nd a False (dia_intro a ha.1)
    have hpos := nd p False hs.1
    ⟨hs.1, modal_K _ _ (modal_K _ _ (modal_K _ _ (modal_K _ _
      (nec% (recurring_guard_decides_self a p)) (modal_four _ hs.2)) (modal_four _ hrec))
      (modal_four _ hpos)) ha.2⟩

variable {τ : Type} [Rel τ] [Order τ] [Pointwise τ]

theorem distinctness_necessary_t_and_strong_actuality_imply_self_atoms_are_strong_atoms_r :
    NecessityOfDistinctnessT → StrongActuality → SelfAtomsAreStrongAtoms τ := fun nd actual =>
  self_atoms_are_strong_atoms_t_implies_self_atoms_are_strong_atoms_r
    (distinctness_necessary_t_and_strong_actuality_imply_self_atoms_are_strong_atoms_t nd actual)

/-- In the boxed result, propositional ND already gives the boxed modal axiom 5. -/
theorem necessary_nd_t_implies_necessary_strong_self_atoms :
    NecNecessityOfDistinctnessT → NecSelfAtomsAreStrongAtoms τ := fun nd =>
  necessary_modal_five_implies_necessary_self_atoms_are_strong_atoms_r
    (necessary_distinctness_necessary_r_implies_necessary_modal_five nd)

theorem necessary_distinctness_necessary_t_and_necessary_strong_actuality_imply_necessary_self_atoms_are_strong_atoms_r :
    NecNecessityOfDistinctnessT → NecStrongActuality → NecSelfAtomsAreStrongAtoms τ :=
  fun nd _ => necessary_nd_t_implies_necessary_strong_self_atoms nd

end Classicism.Proofs

#classicism_derive Classicism.Proofs.incompatible_orders_of_possible
#classicism_derive Classicism.Proofs.forced_self_decision_positive
#classicism_derive Classicism.Proofs.forced_self_decision_negative
#classicism_derive Classicism.Proofs.recurring_guard_decides_self
#classicism_derive Classicism.Proofs.distinctness_necessary_t_and_strong_actuality_imply_self_atoms_are_strong_atoms_t
#classicism_derive Classicism.Proofs.distinctness_necessary_t_and_strong_actuality_imply_self_atoms_are_strong_atoms_r
#classicism_derive Classicism.Proofs.necessary_nd_t_implies_necessary_strong_self_atoms
#classicism_derive Classicism.Proofs.necessary_distinctness_necessary_t_and_necessary_strong_actuality_imply_necessary_self_atoms_are_strong_atoms_r

#classicism_entails Classicism.Proofs.distinctness_necessary_t_and_strong_actuality_imply_self_atoms_are_strong_atoms_r
#classicism_entails Classicism.Proofs.necessary_distinctness_necessary_t_and_necessary_strong_actuality_imply_necessary_self_atoms_are_strong_atoms_r

namespace Classicism.Map

theorem distinctness_necessary_t_and_strong_actuality_imply_self_atoms_are_strong_atoms_r :
    ∀ {Sig : Meta.Signature} (_ : Sig.Admitted) (Ax : Meta.AxiomSet Sig),
      Meta.AxiomSet.Entails Ax P.NecessityOfDistinctnessT.schemaIn →
      Meta.AxiomSet.Entails Ax P.StrongActuality.schemaIn →
      Meta.AxiomSet.Entails Ax P.SelfAtomsAreStrongAtoms.schemaIn := by
  map_cert Proofs.distinctness_necessary_t_and_strong_actuality_imply_self_atoms_are_strong_atoms_r.entails

theorem necessary_distinctness_necessary_t_and_necessary_strong_actuality_imply_necessary_self_atoms_are_strong_atoms_r :
    ∀ {Sig : Meta.Signature} (_ : Sig.Admitted) (Ax : Meta.AxiomSet Sig),
      Meta.AxiomSet.Entails Ax P.NecNecessityOfDistinctnessT.schemaIn →
      Meta.AxiomSet.Entails Ax P.NecStrongActuality.schemaIn →
      Meta.AxiomSet.Entails Ax P.NecSelfAtomsAreStrongAtoms.schemaIn := by
  map_cert Proofs.necessary_distinctness_necessary_t_and_necessary_strong_actuality_imply_necessary_self_atoms_are_strong_atoms_r.entails

end Classicism.Map
