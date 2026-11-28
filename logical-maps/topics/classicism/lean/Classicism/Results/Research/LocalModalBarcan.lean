import Classicism.Certified.Box5

/-! # Full Barcan from two local modal conditions -/

namespace Classicism.Proofs
open Classicism.P

/-- Modal B collapses the distinctness-preserving box to the ordinary box at this point. -/
theorem box_of_boxNe_of_modal_b (b : ModalB) (p : Prop) : BoxNe p → □ p :=
  fun ⟨q, hq, h⟩ => modal_K _ _ h (b q hq)

/-- The ordinary Barcan formula at every type follows from local B and the
pointwise implication from 5-necessity to distinctness-preserving necessity. -/
theorem modal_b_and_five_implies_nd_imply_barcan {σ : Type} [Ty σ] :
    ModalB → FiveImpliesNdNecessity → Barcan σ := by
  intro b five F hF
  apply box_of_boxNe_of_modal_b b
  apply five
  apply box5_barcan
  exact fun x => boxHH_le_box5 _ (boxNe_le_boxHH _ (box_le_boxNe _ (hF x)))

end Classicism.Proofs

#classicism_derive Classicism.Proofs.modal_b_and_five_implies_nd_imply_barcan
#classicism_entails Classicism.Proofs.modal_b_and_five_implies_nd_imply_barcan
