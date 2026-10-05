import Classicism.Paper
import Classicism.Principles

/-!
# Proofs of map records: Comprehension

Records among the comprehension principles (Classicism, §2.3; Dorr, *BC does not imply
RC*). Those whose premise is Actuality or Boolean Completeness are in `Lattice.lean`.
The conventions are in `Results/Records.lean`.
-/

namespace Classicism.Proofs
open Classicism.P Classicism.Paper

/-! ### Comprehension (Classicism, §2.3; Dorr, *BC does not imply RC*) -/

/-- `rigid-comprehension-r-implies-persistent-comprehension-r`: the first conjunct. -/
theorem rigid_comprehension_r_implies_persistent_comprehension_r {τ : Type} [Rel τ] :
    RigidComprehension τ → PersistentComprehension τ := by
  intro rc X
  obtain ⟨Y, hY, hco⟩ := rc X
  exact ⟨Y, hY.1, hco⟩

/-- `rigid-comprehension-r-implies-inextensible-comprehension-r`: the second conjunct. -/
theorem rigid_comprehension_r_implies_inextensible_comprehension_r {τ : Type} [Rel τ] :
    RigidComprehension τ → InextensibleComprehension τ := by
  intro rc X
  obtain ⟨Y, hY, hco⟩ := rc X
  exact ⟨Y, hY.2, hco⟩

/-- `rigid-comprehension-r-implies-weak-rigid-comprehension-r`: a rigid relation is
persistent by definition, and `T` strips the leading box from its inextensibility
conjunct. So the rigid coextension already witnesses the weaker principle. -/
theorem rigid_comprehension_r_implies_weak_rigid_comprehension_r {τ : Type} [Rel τ] :
    RigidComprehension τ → WeakRigidComprehension τ := by
  intro rc X
  obtain ⟨Y, hY, hco⟩ := rc X
  exact ⟨Y, weaklyRigid_of_rigid hY, hco⟩

/-- `weak-rigid-comprehension-r-implies-very-weak-rigid-comprehension-r`: `Persistent(Y)`
unpacks as `□∀x̄. Y[x̄] → □Y[x̄]`, and `T` gives weak persistence. The inextensibility
conjunct is the same in both conditions. -/
theorem weak_rigid_comprehension_r_implies_very_weak_rigid_comprehension_r {τ : Type} [Rel τ] :
    WeakRigidComprehension τ → VeryWeakRigidComprehension τ := by
  intro wrc X
  obtain ⟨Y, hY, hco⟩ := wrc X
  exact ⟨Y, veryWeaklyRigid_of_weaklyRigid hY, hco⟩

/-- `weak-rigid-comprehension-r-implies-persistent-comprehension-r`: the first conjunct
of weak rigidity is persistence itself. -/
theorem weak_rigid_comprehension_r_implies_persistent_comprehension_r {τ : Type} [Rel τ] :
    WeakRigidComprehension τ → PersistentComprehension τ := by
  intro wrc X
  obtain ⟨Y, hY, hco⟩ := wrc X
  exact ⟨Y, hY.1, hco⟩

/-- Closed lemma for the Gallin argument: a relation holding of `a` and failing of `b`
distinguishes them, by Leibniz's Law. Being closed, it may be necessitated. -/
theorem ne_of_holds_and_not_holds {σ : Type} [Ty σ] (Y : σ → Prop) (a b : σ) :
    (Y a ∧ ¬ Y b) → a ≠ b := fun ⟨hYa, hnYb⟩ hab => hnYb (hab ▸ hYa)

/-- `gallin-comprehension-implies-nd`. Apply Gallin Extensional Comprehension to
`λx^σ. x = a`, of the admitted type `σt`, and let `Y` be the coextension supplied.
Coextensiveness gives `Ya` from `a = a` and `¬Yb` from `b ≠ a`; persistence of `Y` and of
`¬Y` boxes each. The box distributes over the conjunction, and the closed lemma above
necessitates, so `K` yields `□(a ≠ b)`. The instance of the premise used is the one at
`σ → t`, for ND at `σ`. -/
theorem gallin_comprehension_implies_nd {σ : Type} [Ty σ] :
    GallinExtensionalComprehension (σ → Prop) → NecessityOfDistinctness σ := by
  intro gec a b hne
  obtain ⟨Y, hY, hnY, hco⟩ := gec (λ x : σ ↦ x = a)
  have hYa : Y a := (hco a).1 rfl
  have hnYb : ¬ Y b := fun hb => hne ((hco b).2 hb).symm
  have hbox : □ (Y a) ∧ □ (¬ Y b) :=
    ⟨weaklyPersistent_apply (weaklyPersistent_of_persistent hY) a hYa,
     weaklyPersistent_neg_apply (weaklyPersistent_of_persistent hnY) b hnYb⟩
  have hconj : □ (Y a ∧ ¬ Y b) := by rw [box_and_eq]; exact hbox
  exact modal_K _ _ (nec% (ne_of_holds_and_not_holds Y a b)) hconj

/-- `necessary-gallin-comprehension-implies-gallin-comprehension`: `T`. -/
theorem necessary_gallin_comprehension_implies_gallin_comprehension {τ : Type} [Rel τ] :
    NecGallinExtensionalComprehension τ → GallinExtensionalComprehension τ := box_elim

/-- `necessary-gallin-comprehension-implies-necessary-nd`: the last record necessitated. -/
theorem necessary_gallin_comprehension_implies_necessary_nd {σ : Type} [Ty σ] :
    NecGallinExtensionalComprehension (σ → Prop) → NecNecessityOfDistinctness σ :=
  modal_K _ _ (nec% (gallin_comprehension_implies_nd (σ := σ)))

/-- `fregean-axiom-implies-necessary-distinctness-necessary-r`: under the Fregean Axiom
what is true is `⊤`, so necessary; apply that to each distinctness and then to ND. -/
theorem fregean_axiom_implies_necessary_distinctness_necessary_r {σ : Type} [Ty σ] :
    FregeanAxiom → NecNecessityOfDistinctness σ := fun fa =>
  have box : ∀ p : Prop, p → □ p := fun p hp => fa p True ⟨fun _ => trivial, fun _ => hp⟩
  box _ (fun x y hne => box _ hne)

/-- `necessary-rigid-comprehension-r-implies-rigid-comprehension-r`: `T`. -/
theorem necessary_rigid_comprehension_r_implies_rigid_comprehension_r {τ : Type} [Rel τ] :
    NecRigidComprehension τ → RigidComprehension τ := box_elim
/-! ### Weakly Inextensible Comprehension (25–27 September) -/

/-- `inextensible-comprehension-r-implies-weakly-inextensible-comprehension-r`: `T` strips
the box of inextensibility; the same witness. -/
theorem inextensible_comprehension_r_implies_weakly_inextensible_comprehension_r
    {τ : Type} [Rel τ] : InextensibleComprehension τ → WeaklyInextensibleComprehension τ :=
  fun ic X => (ic X).elim fun Y hY => ⟨Y, weaklyInextensible_of_inextensible hY.1, hY.2⟩

/-- `weak-rigid-comprehension-r-implies-weakly-inextensible-comprehension-r`: weak
inextensibility is a conjunct of weak rigidity. -/
theorem weak_rigid_comprehension_r_implies_weakly_inextensible_comprehension_r
    {τ : Type} [Rel τ] : WeakRigidComprehension τ → WeaklyInextensibleComprehension τ :=
  fun wrc X => (wrc X).elim fun Y hY => ⟨Y, hY.1.2, hY.2⟩

/-- `necessary-weakly-inextensible-comprehension-r-implies-weakly-inextensible-comprehension-r`:
`T`. -/
theorem necessary_weakly_inextensible_comprehension_r_implies_weakly_inextensible_comprehension_r
    {τ : Type} [Rel τ] :
    NecWeaklyInextensibleComprehension τ → WeaklyInextensibleComprehension τ :=
  fun h => box_elim h


/-! ### The boxed comprehension principles, `T`, and boxing the unboxed records -/

/-- `necessary-weak-rigid-comprehension-r-implies-weak-rigid-comprehension-r`: `T`. -/
theorem necessary_weak_rigid_comprehension_r_implies_weak_rigid_comprehension_r {τ : Type} [Rel τ] :
    NecWeakRigidComprehension τ → WeakRigidComprehension τ := box_elim
/-- `necessary-persistent-comprehension-r-implies-persistent-comprehension-r`: `T`. -/
theorem necessary_persistent_comprehension_r_implies_persistent_comprehension_r {τ : Type} [Rel τ] :
    NecPersistentComprehension τ → PersistentComprehension τ := box_elim
/-- `necessary-inextensible-comprehension-r-implies-inextensible-comprehension-r`: `T`. -/
theorem necessary_inextensible_comprehension_r_implies_inextensible_comprehension_r {τ : Type} [Rel τ] :
    NecInextensibleComprehension τ → InextensibleComprehension τ := box_elim
/-- `necessary-tame-rigidity-r-implies-tame-rigidity-r`: `T`. -/
theorem necessary_tame_rigidity_r_implies_tame_rigidity_r {τ : Type} [Rel τ] :
    NecTameRigidity τ → TameRigidity τ := box_elim
/-- `necessary-rigid-power-r-implies-rigid-power-r`: `T`. -/
theorem necessary_rigid_power_r_implies_rigid_power_r {τ : Type} [Rel τ] :
    NecRigidPower τ → RigidPower τ := box_elim

/-- `necessary-rigid-comprehension-implies-necessary-weak-rigid-comprehension`: the unboxed
record, necessitated. -/
theorem necessary_rigid_comprehension_implies_necessary_weak_rigid_comprehension {τ : Type} [Rel τ] :
    NecRigidComprehension τ → NecWeakRigidComprehension τ :=
  modal_K _ _ (nec% (rigid_comprehension_r_implies_weak_rigid_comprehension_r (τ := τ)))
/-- `necessary-rigid-comprehension-implies-necessary-inextensible-comprehension`. -/
theorem necessary_rigid_comprehension_implies_necessary_inextensible_comprehension {τ : Type} [Rel τ] :
    NecRigidComprehension τ → NecInextensibleComprehension τ :=
  modal_K _ _ (nec% (rigid_comprehension_r_implies_inextensible_comprehension_r (τ := τ)))
/-- `necessary-weak-rigid-comprehension-implies-necessary-persistent-comprehension`. -/
theorem necessary_weak_rigid_comprehension_implies_necessary_persistent_comprehension {τ : Type} [Rel τ] :
    NecWeakRigidComprehension τ → NecPersistentComprehension τ :=
  modal_K _ _ (nec% (weak_rigid_comprehension_r_implies_persistent_comprehension_r (τ := τ)))
/-- `necessary-inextensible-comprehension-implies-necessary-wic`. -/
theorem necessary_inextensible_comprehension_implies_necessary_wic {τ : Type} [Rel τ] :
    NecInextensibleComprehension τ → NecWeaklyInextensibleComprehension τ :=
  modal_K _ _ (nec% (inextensible_comprehension_r_implies_weakly_inextensible_comprehension_r (τ := τ)))


/-! ### Tame Rigidity -/

/-- `tame-rigidity-and-weak-rigid-comprehension-imply-rigid-comprehension`: the weakly rigid
coextension that Weak Rigid Comprehension gives is rigid. -/
theorem tame_rigidity_and_weak_rigid_comprehension_imply_rigid_comprehension {τ : Type} [Rel τ] :
    TameRigidity τ → WeakRigidComprehension τ → RigidComprehension τ :=
  fun tr wrc X => (wrc X).elim fun Y hY => ⟨Y, tr Y hY.1, hY.2⟩

/-- `necessary-tame-rigidity-and-necessary-weak-rigid-comprehension-imply-necessary-rigid-comprehension`:
the unboxed record, necessitated. -/
theorem necessary_tame_rigidity_and_necessary_weak_rigid_comprehension_imply_necessary_rigid_comprehension
    {τ : Type} [Rel τ] :
    NecTameRigidity τ → NecWeakRigidComprehension τ → NecRigidComprehension τ := fun h₁ h₂ =>
  modal_K _ _ (modal_K _ _
    (nec% (tame_rigidity_and_weak_rigid_comprehension_imply_rigid_comprehension (τ := τ))) h₁) h₂

/-- Coextensive weakly rigid relations are identical: each is below the other by the other's
persistence and its own weak inextensibility, and `≤` is antisymmetric. -/
theorem eq_of_weaklyRigid_coext {τ : Type} [Rel τ] [Order τ] [Pointwise τ] {F G : τ}
    (hF : WeaklyRigid F) (hG : WeaklyRigid G) (h : F ≡ G) : F = G :=
  le_antisymm_rel F G
    (le_of_box_incl (hF.2 G (Pointwise.incl_trans F G (boxAt G) (Pointwise.incl_of_coext F G h)
      (box_elim hG.1))))
    (le_of_box_incl (hG.2 F (Pointwise.incl_trans G F (boxAt F) (Pointwise.incl_of_coext' F G h)
      (box_elim hF.1))))

/-- `rigid-comprehension-implies-tame-rigidity`: a weakly rigid `F` is coextensive with a rigid
`G`, which is weakly rigid, so `F = G`. -/
theorem rigid_comprehension_implies_tame_rigidity {τ : Type} [Rel τ] [Order τ] [Pointwise τ] :
    RigidComprehension τ → TameRigidity τ := fun rc F hF =>
  (rc F).elim fun G hG => (eq_of_weaklyRigid_coext hF (weaklyRigid_of_rigid hG.1) hG.2) ▸ hG.1

/-- `necessary-rigid-comprehension-implies-necessary-tame-rigidity`: the unboxed record,
necessitated. -/
theorem necessary_rigid_comprehension_implies_necessary_tame_rigidity {τ : Type} [Rel τ] [Order τ]
    [Pointwise τ] : NecRigidComprehension τ → NecTameRigidity τ :=
  modal_K _ _ (nec% (rigid_comprehension_implies_tame_rigidity (τ := τ)))

end Classicism.Proofs
