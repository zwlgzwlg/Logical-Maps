import Classicism.Results.Research.StrongPossibilityMap

/-! Short certificates for consequences of the two Strong Possibility inconsistency theorems.
The individual result records also give their direct mathematical arguments. -/

namespace Classicism.Map

open Meta

private theorem pure : Statements.strong_possibility_r_inconsistent :=
  StrongPossibilityMap.strong_possibility_r_inconsistent

private theorem named : Statements.strong_possibility_signature_r_inconsistent :=
  StrongPossibilityMap.strong_possibility_signature_r_inconsistent

private theorem entails_of_inconsistent {Sig : Signature} {Ax B : AxiomSet Sig}
    (h : ¬ AxiomSet.Consistent Ax) : AxiomSet.Entails Ax B :=
  fun _ _ => Derivable.botE (Classical.byContradiction h)

theorem maximalism_signature_incompatible_with_strong_possibility_pure :
    Statements.maximalism_signature_incompatible_with_strong_possibility_pure :=
  fun hs Ax _ sp => pure hs Ax sp

theorem signature_strong_possibility_and_atoms_are_strong_imply_atomlessness :
    Statements.signature_strong_possibility_and_atoms_are_strong_imply_atomlessness :=
  fun hs Ax sp _ => entails_of_inconsistent (named hs Ax sp)

theorem signature_strong_possibility_and_inextensible_comprehension_incompatible :
    Statements.signature_strong_possibility_and_inextensible_comprehension_incompatible :=
  fun hs Ax sp _ => named hs Ax sp

theorem signature_strong_possibility_and_relational_barcan_incompatible :
    Statements.signature_strong_possibility_and_relational_barcan_incompatible :=
  fun hs Ax sp _ => named hs Ax sp

theorem signature_strong_possibility_and_strong_actuality_incompatible :
    Statements.signature_strong_possibility_and_strong_actuality_incompatible :=
  fun hs Ax sp _ => named hs Ax sp

theorem signature_strong_possibility_and_tame_rigidity_imply_weakly_rigid_power :
    Statements.signature_strong_possibility_and_tame_rigidity_imply_weakly_rigid_power :=
  fun hs Ax sp _ => entails_of_inconsistent (named hs Ax sp)

theorem signature_strong_possibility_and_two_hat_implies_nd_incompatible :
    Statements.signature_strong_possibility_and_two_hat_implies_nd_incompatible :=
  fun hs Ax sp _ => named hs Ax sp

theorem signature_strong_possibility_implies_rigid_power :
    Statements.signature_strong_possibility_implies_rigid_power :=
  fun hs Ax sp => entails_of_inconsistent (named hs Ax sp)

theorem strong_possibility_and_boolean_completeness_t_incompatible :
    Statements.strong_possibility_and_boolean_completeness_t_incompatible :=
  fun hs Ax sp _ => pure hs Ax sp

theorem strong_possibility_and_inextensible_comprehension_incompatible :
    Statements.strong_possibility_and_inextensible_comprehension_incompatible :=
  fun hs Ax sp _ => pure hs Ax sp

theorem strong_possibility_and_strong_actuality_incompatible :
    Statements.strong_possibility_and_strong_actuality_incompatible :=
  fun hs Ax sp _ => pure hs Ax sp

theorem strong_possibility_and_tame_rigidity_imply_weakly_rigid_power :
    Statements.strong_possibility_and_tame_rigidity_imply_weakly_rigid_power :=
  fun hs Ax sp _ => entails_of_inconsistent (pure hs Ax sp)

theorem strong_possibility_and_witnessed_possibility_incompatible :
    Statements.strong_possibility_and_witnessed_possibility_incompatible :=
  fun hs Ax sp _ => pure hs Ax sp

theorem strong_possibility_implies_rigid_power :
    Statements.strong_possibility_implies_rigid_power :=
  fun hs Ax sp => entails_of_inconsistent (pure hs Ax sp)

theorem strong_possibility_incompatible_with_atoms_are_self_atoms_t :
    Statements.strong_possibility_incompatible_with_atoms_are_self_atoms_t :=
  fun hs Ax sp _ => pure hs Ax sp

theorem strong_possibility_incompatible_with_barcan_t :
    Statements.strong_possibility_incompatible_with_barcan_t :=
  fun hs Ax sp _ => pure hs Ax sp

theorem strong_possibility_r_implies_possibility_plus_r :
    Statements.strong_possibility_r_implies_possibility_plus_r :=
  fun hs Ax sp => entails_of_inconsistent (pure hs Ax sp)

theorem strong_possibility_signature_and_truths_are_nd_necessary_incompatible :
    Statements.strong_possibility_signature_and_truths_are_nd_necessary_incompatible :=
  fun hs Ax sp _ => named hs Ax sp

theorem strong_possibility_signature_r_implies_distinctness_signature_r :
    Statements.strong_possibility_signature_r_implies_distinctness_signature_r :=
  fun hs Ax sp => entails_of_inconsistent (named hs Ax sp)

theorem strong_possibility_signature_r_implies_possibility_plus_signature_r :
    Statements.strong_possibility_signature_r_implies_possibility_plus_signature_r :=
  fun hs Ax sp => entails_of_inconsistent (named hs Ax sp)

end Classicism.Map
