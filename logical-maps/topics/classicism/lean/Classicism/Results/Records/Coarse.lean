import Classicism.Paper
import Classicism.Principles

/-!
# Proofs of map records: The modal principles, ND, BF and Tractarianism

Records among the principles of the map's category `coarse`: `B`, `5` and the Necessity of
Distinctness (Proposition 2.2), Tractarianism, Functionality and BF (Proposition 2.1), and
their specializations to `t` and necessitations.
The conventions are in `Results/Records.lean`.
-/

namespace Classicism.Proofs
open Classicism.P Classicism.Paper

/-! ### Modal principles (Classicism, Proposition 2.2) -/

/-- `distinctness-necessary-t-implies-modal-five`: `◇p` is `p ≠ False`, so `ND` at
type `t` applied to `p` and `False` is `5` word for word. -/
theorem distinctness_necessary_t_implies_modal_five : NecessityOfDistinctnessT → ModalFive :=
  fun nd p => nd p False

/-- `modal-five-implies-modal-b`: compose `p → ◇p` with `5`. -/
theorem modal_five_implies_modal_b : ModalFive → ModalB :=
  fun five p hp => five p (dia_intro p hp)

/-- `modal-b-implies-distinctness-necessary-r` (Prior): `B` gives `□◇(x ≠ y)`; the
necessitation of the closed lemma and `K` give `□(x ≠ y)`. -/
theorem modal_b_implies_distinctness_necessary_r {σ : Type} [Ty σ] :
    ModalB → NecessityOfDistinctness σ := by
  intro b x y hne
  exact modal_K _ _ (nec% (ne_of_dia_ne x y)) (b (x ≠ y) hne)

/-- `necessary-barcan-t-implies-barcan-t`: `T`. -/
theorem necessary_barcan_t_implies_barcan_t : NecBarcanT → BarcanT := box_elim

/-- `necessary-distinctness-necessary-t-implies-distinctness-necessary-t`: `T`. -/
theorem necessary_distinctness_necessary_t_implies_distinctness_necessary_t :
    NecNecessityOfDistinctnessT → NecessityOfDistinctnessT := box_elim

/-- `barcan-r-implies-barcan-t`: BF at type `t` is the principle's instance at `t`. -/
theorem barcan_r_implies_barcan_t : Barcan Prop → BarcanT := fun bf => bf

/-! ### Tractarianism, Functionality and BF (Classicism, Proposition 2.1, n. 27) -/

/-- `tractarianism-r-implies-barcan-r`: take `p := True`. -/
theorem tractarianism_r_implies_barcan_r {σ : Type} [Ty σ] : Tractarianism σ → Barcan σ := by
  intro tr X h
  rw [← true_entails_eq_box]
  exact tr True X (fun x => by rw [true_entails_eq_box]; exact h x)

/-- `functionality-r-implies-tractarianism-r`: Functionality at `σ → t` identifies `X`
with `λx. p ∨ Xx`; then `∀x. Xx = ∀x. p ∨ Xx = p ∨ ∀x. Xx` by Distribution-∨∀. -/
theorem functionality_r_implies_tractarianism_r {σ : Type} [Ty σ] :
    Functionality σ Prop → Tractarianism σ := by
  intro fn p X h
  have hX : X = λ x ↦ p ∨ X x := fn X (λ x ↦ p ∨ X x) h
  show (∀ x, X x) = (p ∨ ∀ x, X x)
  calc (∀ x, X x) = (∀ x, p ∨ X x) := congrArg (λ Y : σ → Prop ↦ ∀ x, Y x) hX
    _ = (p ∨ ∀ x, X x) := (or_forall_distrib_eq X p).symm

/-- `barcan-r-implies-functionality-r`: NI pointwise, BF at `σ` to box the quantifier,
then Modalized Functionality. -/
theorem barcan_r_implies_functionality_r {σ τ : Type} [Ty σ] [Rel τ] :
    Barcan σ → Functionality σ τ := by
  intro bf X Y h
  exact modalized_functionality X Y
    (bf (λ z ↦ X z = Y z) (fun z => necessity_of_identity _ _ (h z)))

/-- `distinctness-necessary-r-implies-distinctness-necessary-t`: the `t`-instance. -/
theorem distinctness_necessary_r_implies_distinctness_necessary_t :
    NecessityOfDistinctness Prop → NecessityOfDistinctnessT := fun h => h
/-- `necessary-barcan-r-implies-necessary-barcan-t`: the `t`-instance. -/
theorem necessary_barcan_r_implies_necessary_barcan_t : NecBarcan Prop → NecBarcanT := fun h => h
/-- `necessary-distinctness-necessary-r-implies-necessary-distinctness-necessary-t`. -/
theorem necessary_distinctness_necessary_r_implies_necessary_distinctness_necessary_t :
    NecNecessityOfDistinctness Prop → NecNecessityOfDistinctnessT := fun h => h
/-- `necessary-barcan-r-implies-barcan-r`: `T`. -/
theorem necessary_barcan_r_implies_barcan_r {σ : Type} [Ty σ] : NecBarcan σ → Barcan σ := box_elim
/-- `necessary-distinctness-necessary-r-implies-distinctness-necessary-r`: `T`. -/
theorem necessary_distinctness_necessary_r_implies_distinctness_necessary_r {σ : Type} [Ty σ] :
    NecNecessityOfDistinctness σ → NecessityOfDistinctness σ := box_elim
/-- `necessary-modal-b-implies-modal-b`: `T`. -/
theorem necessary_modal_b_implies_modal_b : NecModalB → ModalB := box_elim
/-- `necessary-modal-five-implies-modal-five`: `T`. -/
theorem necessary_modal_five_implies_modal_five : NecModalFive → ModalFive := box_elim
/-- `necessary-tractarianism-r-implies-tractarianism-r`: `T`. -/
theorem necessary_tractarianism_r_implies_tractarianism_r {σ : Type} [Ty σ] :
    NecTractarianism σ → Tractarianism σ := box_elim
/-- `necessary-distinctness-necessary-r-implies-necessary-modal-five`. -/
theorem necessary_distinctness_necessary_r_implies_necessary_modal_five :
    NecNecessityOfDistinctness Prop → NecModalFive :=
  modal_K _ _ (nec% distinctness_necessary_t_implies_modal_five)
/-- `necessary-modal-five-implies-necessary-modal-b`. -/
theorem necessary_modal_five_implies_necessary_modal_b : NecModalFive → NecModalB :=
  modal_K _ _ (nec% modal_five_implies_modal_b)
/-- `necessary-modal-b-implies-necessary-distinctness-necessary-r`. -/
theorem necessary_modal_b_implies_necessary_distinctness_necessary_r {σ : Type} [Ty σ] :
    NecModalB → NecNecessityOfDistinctness σ :=
  modal_K _ _ (nec% (modal_b_implies_distinctness_necessary_r (σ := σ)))
/-- `necessary-functionality-r-implies-necessary-tractarianism-r`. -/
theorem necessary_functionality_r_implies_necessary_tractarianism_r {σ : Type} [Ty σ] :
    NecFunctionality σ Prop → NecTractarianism σ :=
  modal_K _ _ (nec% (functionality_r_implies_tractarianism_r (σ := σ)))
/-- `necessary-tractarianism-r-implies-necessary-barcan-r`. -/
theorem necessary_tractarianism_r_implies_necessary_barcan_r {σ : Type} [Ty σ] :
    NecTractarianism σ → NecBarcan σ :=
  modal_K _ _ (nec% (tractarianism_r_implies_barcan_r (σ := σ)))

end Classicism.Proofs
