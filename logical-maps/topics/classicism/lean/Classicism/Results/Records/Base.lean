import Classicism.Paper
import Classicism.Principles

/-!
# Proofs of map records: Theorems of Classicism

The map's records with no premises: the principles of the map's category `base` are
theorems of `C`.
The conventions are in `Results/Records.lean`.
-/

namespace Classicism.Proofs
open Classicism.P Classicism.Paper

/-! ### Theorems of Classicism (records with no premises) -/

/-- `classicism-implies-modal-k`. -/
theorem classicism_implies_modal_k : ModalK := modal_K
/-- `classicism-implies-modal-t`. -/
theorem classicism_implies_modal_t : ModalT := modal_T
/-- `classicism-implies-modal-four`. -/
theorem classicism_implies_modal_four : ModalFour := modal_four
/-- `classicism-implies-modalized-fregean`. -/
theorem classicism_implies_modalized_fregean : ModalizedFregean := modalized_fregean
/-- `classicism-implies-intensionality-r`. -/
theorem classicism_implies_intensionality_r {τ : Type} [Rel τ] : Intensionality τ :=
  fun X Y => intensionality X Y
/-- `classicism-implies-modalized-functionality-r`. -/
theorem classicism_implies_modalized_functionality_r {σ τ : Type} [Ty σ] [Rel τ] :
    ModalizedFunctionality σ τ := fun X Y => modalized_functionality X Y
/-- `classicism-implies-identity-necessary-r`. -/
theorem classicism_implies_identity_necessary_r {σ : Type} [Ty σ] : NecessityOfIdentity σ :=
  fun x y => necessity_of_identity x y
/-- `classicism-implies-converse-barcan-r`. -/
theorem classicism_implies_converse_barcan_r {σ : Type} [Ty σ] : ConverseBarcan σ :=
  fun X => converse_barcan X
/-- `classicism-implies-existence-r`, the instance at `e`: the axiom `e_exists`. This is
the one record proof whose axiom report names that axiom. -/
theorem classicism_implies_existence_r_at_e : Existence e := existence_e

/-- `classicism-implies-existence-r`, the instances at relational types: a theorem of
`C⁻`, whose axiom report shows Existence there costing nothing. Together with the instance
at `e` this covers every type of `R`, which is the record. -/
theorem classicism_implies_existence_r_relational {τ : Type} [Rel τ] : Existence τ := existence_rel

/-- `classicism-implies-broad-necessitism-r`: necessitate `∀x. ∃y. y = x`, then `CBF`. -/
theorem classicism_implies_broad_necessitism_r {σ : Type} [Ty σ] : BroadNecessitism σ := fun x =>
  converse_barcan (λ x ↦ ∃ y : σ, y = x) (nec% (fun (x : σ) => (⟨x, rfl⟩ : ∃ y, y = x))) x

end Classicism.Proofs
