import Classicism.ModelStatements
import Classicism.Results.Consistency.Consistency

/-!
# The map's models, certified verdict by verdict

One theorem per verdict a model record proves in Lean (its `lean.verdicts`), named
`Models.<model id>.<principle id>`, whose type is the statement the map generates for it
(`Classicism/ModelStatements.lean`): that the record's Lean model is an intensional action
model, and that the principle holds in it, or fails. These are the refs `pmap lean-check`
checks, against the generated statements and the map's list of allowed axioms.

The models are those of Appendix D (`Models/`) and the two M-set models of §3
(`Semantics/IntensionalExamples.lean`), over the pure signature. A principle at every
signature, `P.X.schemaIn`, holds in such a model iff its pure schema does
(`Premodel.holdsAx_schemaIn_iff`), so each certificate cites a verdict proved in `Models/`
about a sentence of the schema. A verdict on a principle relative to a signature would need a
model of an admitted signature (the statement then also asks `Admitted`); none is here yet.

What composes these into a certificate of a whole model, the map's model statement, is
`Premodel.theory` (`Semantics/IntensionalTheory.lean`): the theory of a model of an admitted
signature is consistent, complete, and entails exactly the schemas that hold in the model.
-/

namespace Classicism.Meta.Intensional.Premodel

open CategoryTheory

variable {C : Type} [SmallCategory C] {B : Premodel Signature.pure C}

/-! ## Glue: from the verdicts as proved to the statements as generated -/

theorem verdict_holds (M : B.IsModel) {Ax : AxiomSet Signature.pure} (h : B.HoldsAx Ax) :
    B.IsModel ∧ B.HoldsAx (AxiomSet.ofPure Ax) :=
  ⟨M, (holdsAx_schemaIn_iff B Ax).2 h⟩

theorem verdict_fails (M : B.IsModel) {Ax : AxiomSet Signature.pure} (h : ¬ B.HoldsAx Ax) :
    B.IsModel ∧ ¬ B.HoldsAx (AxiomSet.ofPure Ax) :=
  ⟨M, fun h' => h ((holdsAx_schemaIn_iff B Ax).1 h')⟩

/-- A schema indexed by types holds iff its instance at each closed type does. -/
theorem holdsAx_indexed {α : Type} {Cl : α → Prop} {q : α → Sentence Signature.pure} :
    B.HoldsAx (fun a => ∃ x, Cl x ∧ a = q x) ↔ ∀ x, Cl x → B.HoldsSentence (q x) :=
  ⟨fun h x hx => h _ ⟨x, hx, rfl⟩, fun h _ ⟨x, hx, e⟩ => e ▸ h x hx⟩

/-- A schema of one sentence holds iff the sentence does. -/
theorem holdsAx_eq {q : Sentence Signature.pure} : B.HoldsAx (fun a => a = q) ↔ B.HoldsSentence q :=
  ⟨fun h => h _ rfl, fun h _ e => e ▸ h⟩

/-- A schema fails when one of its sentences does. -/
theorem not_holdsAx_of {Ax : AxiomSet Signature.pure} {a : Sentence Signature.pure} (ha : Ax a)
    (h : ¬ B.HoldsSentence a) : ¬ B.HoldsAx Ax :=
  fun H => h (H a ha)

/-- A monoid's one-object category has one object. -/
instance {M : Type} [Monoid M] : Subsingleton (SingleObj M) := inferInstanceAs (Subsingleton Unit)

/-- No Pure Contingency, in a model on one object: every model on a monoid. -/
theorem holdsAx_npc_pure [Subsingleton C] (M : B.IsModel) : B.HoldsAx (AxiomSet.noContingency _) := by
  rw [← AxiomSet.npc_pure_eq]
  exact B.holdsAx_npc M

/-- In a model on one object, a pure sentence of the paper's language that holds is necessary. -/
theorem holdsSentence_box_of_npc [Subsingleton C] (M : B.IsModel) {p : Sentence Signature.pure}
    (hc : p.closedTypes = true) (h : B.HoldsSentence p) : B.HoldsSentence (Term.box p) := by
  have hi := B.holdsAx_npc M (Term.imp p (Term.box p))
    ⟨by simp [hc], p, Term.pure_of_pureSig p, rfl⟩
  exact (B.holds_imp M _ _ _ _).1 hi h

end Classicism.Meta.Intensional.Premodel

namespace Classicism.Map.Models

open Meta Meta.Intensional Meta.Intensional.Premodel

namespace finite_support_permutations

local notation "M" => Classicism.Meta.Intensional.Perms.model_isModel

theorem distinctness_necessary_r : Statements.Models.finite_support_permutations.distinctness_necessary_r :=
  verdict_holds M <|
    holdsAx_indexed.2 fun σ _ => holdsSentence_of_box _ M (Perms.box_nd σ)

theorem necessary_distinctness_necessary_r : Statements.Models.finite_support_permutations.necessary_distinctness_necessary_r :=
  verdict_holds M <|
    holdsAx_indexed.2 fun σ _ => Perms.box_nd σ

theorem barcan_r : Statements.Models.finite_support_permutations.barcan_r :=
  verdict_holds M <|
    holdsAx_indexed.2 fun σ _ => holdsSentence_of_box _ M (Perms.box_bf σ)

theorem necessary_barcan_r : Statements.Models.finite_support_permutations.necessary_barcan_r :=
  verdict_holds M <|
    holdsAx_indexed.2 fun σ _ => Perms.box_bf σ

theorem atomlessness : Statements.Models.finite_support_permutations.atomlessness :=
  verdict_holds M <|
    holdsAx_eq.2 Perms.atomlessness

theorem no_pure_contingency_r : Statements.Models.finite_support_permutations.no_pure_contingency_r :=
  verdict_holds M <|
    holdsAx_npc_pure M

theorem actuality : Statements.Models.finite_support_permutations.actuality :=
  verdict_fails M <|
    not_holdsAx_of rfl (Perms.not_actuality)

theorem atomicity_t : Statements.Models.finite_support_permutations.atomicity_t :=
  verdict_fails M <|
    not_holdsAx_of rfl (Perms.not_atomicityT)

theorem boolean_completeness_r : Statements.Models.finite_support_permutations.boolean_completeness_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.arr .e .t, by simp, rfl⟩ (Perms.not_bc)

end finite_support_permutations

namespace finite_support_monotone_surjections

local notation "M" => Classicism.Meta.Intensional.MonoidModel.model_isModel Classicism.Meta.Intensional.Monoids.monoSurj

theorem barcan_r : Statements.Models.finite_support_monotone_surjections.barcan_r :=
  verdict_holds M <|
    holdsAx_indexed.2 fun σ _ => Monoids.MonoSurj.bf σ

theorem necessary_barcan_r : Statements.Models.finite_support_monotone_surjections.necessary_barcan_r :=
  verdict_holds M <|
    holdsAx_indexed.2 fun σ hσ => holdsSentence_box_of_npc M
      (P.Barcan.schema_closedTypes _ ⟨σ, hσ, rfl⟩) (Monoids.MonoSurj.bf σ)

theorem atomlessness : Statements.Models.finite_support_monotone_surjections.atomlessness :=
  verdict_holds M <|
    holdsAx_eq.2 Monoids.MonoSurj.atomlessness

theorem no_pure_contingency_r : Statements.Models.finite_support_monotone_surjections.no_pure_contingency_r :=
  verdict_holds M <|
    holdsAx_npc_pure M

theorem distinctness_necessary_r : Statements.Models.finite_support_monotone_surjections.distinctness_necessary_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.e, trivial, rfl⟩ (Monoids.MonoSurj.not_nd_e)

theorem necessary_distinctness_necessary_r : Statements.Models.finite_support_monotone_surjections.necessary_distinctness_necessary_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.e, trivial, rfl⟩ (fun h => Monoids.MonoSurj.not_nd_e (holdsSentence_of_box _ M h))

theorem actuality : Statements.Models.finite_support_monotone_surjections.actuality :=
  verdict_fails M <|
    not_holdsAx_of rfl (Monoids.MonoSurj.not_actuality)

theorem atomicity_t : Statements.Models.finite_support_monotone_surjections.atomicity_t :=
  verdict_fails M <|
    not_holdsAx_of rfl (Monoids.MonoSurj.not_atomicityT)

theorem boolean_completeness_r : Statements.Models.finite_support_monotone_surjections.boolean_completeness_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.arr .e .t, by simp, rfl⟩ (Monoids.MonoSurj.not_bc)

end finite_support_monotone_surjections

namespace finite_support_monotone_maps

local notation "M" => Classicism.Meta.Intensional.MonoidModel.model_isModel Classicism.Meta.Intensional.Monoids.mono

theorem atomlessness : Statements.Models.finite_support_monotone_maps.atomlessness :=
  verdict_holds M <|
    holdsAx_eq.2 Monoids.Mono.atomlessness

theorem no_pure_contingency_r : Statements.Models.finite_support_monotone_maps.no_pure_contingency_r :=
  verdict_holds M <|
    holdsAx_npc_pure M

theorem distinctness_necessary_r : Statements.Models.finite_support_monotone_maps.distinctness_necessary_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.e, trivial, rfl⟩ (Monoids.Mono.not_nd_e)

theorem necessary_distinctness_necessary_r : Statements.Models.finite_support_monotone_maps.necessary_distinctness_necessary_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.e, trivial, rfl⟩ (fun h => Monoids.Mono.not_nd_e (holdsSentence_of_box _ M h))

theorem barcan_r : Statements.Models.finite_support_monotone_maps.barcan_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.e, trivial, rfl⟩ (Monoids.Mono.not_bf_e)

theorem necessary_barcan_r : Statements.Models.finite_support_monotone_maps.necessary_barcan_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.e, trivial, rfl⟩ (fun h => Monoids.Mono.not_bf_e (holdsSentence_of_box _ M h))

theorem actuality : Statements.Models.finite_support_monotone_maps.actuality :=
  verdict_fails M <|
    not_holdsAx_of rfl (Monoids.Mono.not_actuality)

theorem atomicity_t : Statements.Models.finite_support_monotone_maps.atomicity_t :=
  verdict_fails M <|
    not_holdsAx_of rfl (Monoids.Mono.not_atomicityT)

theorem boolean_completeness_r : Statements.Models.finite_support_monotone_maps.boolean_completeness_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.arr .e .t, by simp, rfl⟩ (Monoids.Mono.not_bc)

end finite_support_monotone_maps

namespace finite_support_identity_or_collapse

local notation "M" => Classicism.Meta.Intensional.MonoidModel.model_isModel Classicism.Meta.Intensional.Monoids.mono01

theorem actuality : Statements.Models.finite_support_identity_or_collapse.actuality :=
  verdict_holds M <|
    holdsAx_eq.2 Monoids.Mono01.actuality

theorem no_pure_contingency_r : Statements.Models.finite_support_identity_or_collapse.no_pure_contingency_r :=
  verdict_holds M <|
    holdsAx_npc_pure M

theorem distinctness_necessary_r : Statements.Models.finite_support_identity_or_collapse.distinctness_necessary_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.e, trivial, rfl⟩ (Monoids.Mono01.not_nd_e)

theorem necessary_distinctness_necessary_r : Statements.Models.finite_support_identity_or_collapse.necessary_distinctness_necessary_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.e, trivial, rfl⟩ (fun h => Monoids.Mono01.not_nd_e (holdsSentence_of_box _ M h))

theorem barcan_r : Statements.Models.finite_support_identity_or_collapse.barcan_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.e, trivial, rfl⟩ (Monoids.Mono01.not_bf_e)

theorem necessary_barcan_r : Statements.Models.finite_support_identity_or_collapse.necessary_barcan_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.e, trivial, rfl⟩ (fun h => Monoids.Mono01.not_bf_e (holdsSentence_of_box _ M h))

theorem atomicity_t : Statements.Models.finite_support_identity_or_collapse.atomicity_t :=
  verdict_fails M <|
    not_holdsAx_of rfl (Monoids.Mono01.not_atomicityT)

theorem boolean_completeness_r : Statements.Models.finite_support_identity_or_collapse.boolean_completeness_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.arr .e .t, by simp, rfl⟩ (Monoids.Mono01.not_bc)

end finite_support_identity_or_collapse

namespace finite_support_identity_or_collapse_surjections

local notation "M" => Classicism.Meta.Intensional.MonoidModel.model_isModel Classicism.Meta.Intensional.Monoids.monoSurj01

theorem barcan_r : Statements.Models.finite_support_identity_or_collapse_surjections.barcan_r :=
  verdict_holds M <|
    holdsAx_indexed.2 fun σ _ => Monoids.MonoSurj01.bf σ

theorem necessary_barcan_r : Statements.Models.finite_support_identity_or_collapse_surjections.necessary_barcan_r :=
  verdict_holds M <|
    holdsAx_indexed.2 fun σ hσ => holdsSentence_box_of_npc M
      (P.Barcan.schema_closedTypes _ ⟨σ, hσ, rfl⟩) (Monoids.MonoSurj01.bf σ)

theorem actuality : Statements.Models.finite_support_identity_or_collapse_surjections.actuality :=
  verdict_holds M <|
    holdsAx_eq.2 Monoids.MonoSurj01.actuality

theorem no_pure_contingency_r : Statements.Models.finite_support_identity_or_collapse_surjections.no_pure_contingency_r :=
  verdict_holds M <|
    holdsAx_npc_pure M

theorem distinctness_necessary_r : Statements.Models.finite_support_identity_or_collapse_surjections.distinctness_necessary_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.e, trivial, rfl⟩ (Monoids.MonoSurj01.not_nd_e)

theorem necessary_distinctness_necessary_r : Statements.Models.finite_support_identity_or_collapse_surjections.necessary_distinctness_necessary_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.e, trivial, rfl⟩ (fun h => Monoids.MonoSurj01.not_nd_e (holdsSentence_of_box _ M h))

theorem atomicity_t : Statements.Models.finite_support_identity_or_collapse_surjections.atomicity_t :=
  verdict_fails M <|
    not_holdsAx_of rfl (Monoids.MonoSurj01.not_atomicityT)

theorem boolean_completeness_r : Statements.Models.finite_support_identity_or_collapse_surjections.boolean_completeness_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.arr .e .t, by simp, rfl⟩ (Monoids.MonoSurj01.not_bc)

end finite_support_identity_or_collapse_surjections

namespace finite_support_truncations

local notation "M" => Classicism.Meta.Intensional.MonoidModel.model_isModel Classicism.Meta.Intensional.Monoids.truncs

theorem atomicity_t : Statements.Models.finite_support_truncations.atomicity_t :=
  verdict_holds M <|
    holdsAx_eq.2 Monoids.Truncs.atomicityT

theorem no_pure_contingency_r : Statements.Models.finite_support_truncations.no_pure_contingency_r :=
  verdict_holds M <|
    holdsAx_npc_pure M

theorem distinctness_necessary_r : Statements.Models.finite_support_truncations.distinctness_necessary_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.e, trivial, rfl⟩ (Monoids.Truncs.not_nd_e)

theorem necessary_distinctness_necessary_r : Statements.Models.finite_support_truncations.necessary_distinctness_necessary_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.e, trivial, rfl⟩ (fun h => Monoids.Truncs.not_nd_e (holdsSentence_of_box _ M h))

theorem barcan_r : Statements.Models.finite_support_truncations.barcan_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.e, trivial, rfl⟩ (Monoids.Truncs.not_bf_e)

theorem necessary_barcan_r : Statements.Models.finite_support_truncations.necessary_barcan_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.e, trivial, rfl⟩ (fun h => Monoids.Truncs.not_bf_e (holdsSentence_of_box _ M h))

theorem actuality : Statements.Models.finite_support_truncations.actuality :=
  verdict_fails M <|
    not_holdsAx_of rfl (Monoids.Truncs.not_actuality)

theorem boolean_completeness_r : Statements.Models.finite_support_truncations.boolean_completeness_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.arr .e .t, by simp, rfl⟩ (Monoids.Truncs.not_bc)

end finite_support_truncations

namespace finite_support_dyadic_roundings

local notation "M" => Classicism.Meta.Intensional.MonoidModel.model_isModel Classicism.Meta.Intensional.Monoids.pow2

theorem actuality : Statements.Models.finite_support_dyadic_roundings.actuality :=
  verdict_holds M <|
    holdsAx_eq.2 Monoids.Pow2.actuality

theorem atomicity_t : Statements.Models.finite_support_dyadic_roundings.atomicity_t :=
  verdict_holds M <|
    holdsAx_eq.2 Monoids.Pow2.atomicityT

theorem no_pure_contingency_r : Statements.Models.finite_support_dyadic_roundings.no_pure_contingency_r :=
  verdict_holds M <|
    holdsAx_npc_pure M

theorem distinctness_necessary_r : Statements.Models.finite_support_dyadic_roundings.distinctness_necessary_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.e, trivial, rfl⟩ (Monoids.Pow2.not_nd_e)

theorem necessary_distinctness_necessary_r : Statements.Models.finite_support_dyadic_roundings.necessary_distinctness_necessary_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.e, trivial, rfl⟩ (fun h => Monoids.Pow2.not_nd_e (holdsSentence_of_box _ M h))

theorem barcan_r : Statements.Models.finite_support_dyadic_roundings.barcan_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.e, trivial, rfl⟩ (Monoids.Pow2.not_bf_e)

theorem necessary_barcan_r : Statements.Models.finite_support_dyadic_roundings.necessary_barcan_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.e, trivial, rfl⟩ (fun h => Monoids.Pow2.not_bf_e (holdsSentence_of_box _ M h))

theorem boolean_completeness_r : Statements.Models.finite_support_dyadic_roundings.boolean_completeness_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.arr .e .t, by simp, rfl⟩ (Monoids.Pow2.not_bc)

end finite_support_dyadic_roundings

namespace finite_support_truncated_shifts

local notation "M" => Classicism.Meta.Intensional.MonoidModel.model_isModel Classicism.Meta.Intensional.Monoids.shifts

theorem barcan_r : Statements.Models.finite_support_truncated_shifts.barcan_r :=
  verdict_holds M <|
    holdsAx_indexed.2 fun σ _ => Monoids.Shifts.bf σ

theorem necessary_barcan_r : Statements.Models.finite_support_truncated_shifts.necessary_barcan_r :=
  verdict_holds M <|
    holdsAx_indexed.2 fun σ hσ => holdsSentence_box_of_npc M
      (P.Barcan.schema_closedTypes _ ⟨σ, hσ, rfl⟩) (Monoids.Shifts.bf σ)

theorem actuality : Statements.Models.finite_support_truncated_shifts.actuality :=
  verdict_holds M <|
    holdsAx_eq.2 Monoids.Shifts.actuality

theorem atomicity_t : Statements.Models.finite_support_truncated_shifts.atomicity_t :=
  verdict_holds M <|
    holdsAx_eq.2 Monoids.Shifts.atomicityT

theorem no_pure_contingency_r : Statements.Models.finite_support_truncated_shifts.no_pure_contingency_r :=
  verdict_holds M <|
    holdsAx_npc_pure M

theorem distinctness_necessary_r : Statements.Models.finite_support_truncated_shifts.distinctness_necessary_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.e, trivial, rfl⟩ (Monoids.Shifts.not_nd_e)

theorem necessary_distinctness_necessary_r : Statements.Models.finite_support_truncated_shifts.necessary_distinctness_necessary_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.e, trivial, rfl⟩ (fun h => Monoids.Shifts.not_nd_e (holdsSentence_of_box _ M h))

theorem boolean_completeness_r : Statements.Models.finite_support_truncated_shifts.boolean_completeness_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.arr .e .t, by simp, rfl⟩ (Monoids.Shifts.not_bc)

end finite_support_truncated_shifts

namespace finite_support_two_object_all_maps

local notation "M" => Classicism.Meta.Intensional.ContingentBarcan.model_isModel

theorem barcan_r : Statements.Models.finite_support_two_object_all_maps.barcan_r :=
  verdict_holds M <|
    holdsAx_indexed.2 fun σ _ => ContingentBarcan.bf σ

theorem necessary_barcan_r : Statements.Models.finite_support_two_object_all_maps.necessary_barcan_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.e, trivial, rfl⟩ (ContingentBarcan.not_box_bf_e)

end finite_support_two_object_all_maps

namespace full_idempotent_monoid

local notation "M" => MSet.model_isModel Idem

theorem no_pure_contingency_r : Statements.Models.full_idempotent_monoid.no_pure_contingency_r :=
  verdict_holds M <|
    holdsAx_npc_pure M

theorem distinctness_necessary_r : Statements.Models.full_idempotent_monoid.distinctness_necessary_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.rel .t, by simp, rfl⟩ (Idem.not_nd_t)

theorem necessary_distinctness_necessary_r : Statements.Models.full_idempotent_monoid.necessary_distinctness_necessary_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.rel .t, by simp, rfl⟩ (fun h => Idem.not_nd_t (holdsSentence_of_box _ M h))

theorem distinctness_necessary_t : Statements.Models.full_idempotent_monoid.distinctness_necessary_t :=
  verdict_fails M <|
    not_holdsAx_of rfl (Idem.not_nd_t)

theorem necessary_distinctness_necessary_t : Statements.Models.full_idempotent_monoid.necessary_distinctness_necessary_t :=
  verdict_fails M <|
    not_holdsAx_of rfl (fun h => Idem.not_nd_t (holdsSentence_of_box _ M h))

theorem barcan_r : Statements.Models.full_idempotent_monoid.barcan_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.rel .t, by simp, rfl⟩ (Idem.not_bf_t)

theorem necessary_barcan_r : Statements.Models.full_idempotent_monoid.necessary_barcan_r :=
  verdict_fails M <|
    not_holdsAx_of ⟨.rel .t, by simp, rfl⟩ (fun h => Idem.not_bf_t (holdsSentence_of_box _ M h))

theorem barcan_t : Statements.Models.full_idempotent_monoid.barcan_t :=
  verdict_fails M <|
    not_holdsAx_of rfl (Idem.not_bf_t)

theorem necessary_barcan_t : Statements.Models.full_idempotent_monoid.necessary_barcan_t :=
  verdict_fails M <|
    not_holdsAx_of rfl (fun h => Idem.not_bf_t (holdsSentence_of_box _ M h))

theorem fregean_axiom : Statements.Models.full_idempotent_monoid.fregean_axiom :=
  verdict_fails M <|
    not_holdsAx_of rfl (Idem.not_fregean)

theorem necessary_fregean_axiom : Statements.Models.full_idempotent_monoid.necessary_fregean_axiom :=
  verdict_fails M <|
    not_holdsAx_of rfl (fun h => Idem.not_fregean (holdsSentence_of_box _ M h))

end full_idempotent_monoid

namespace full_involution_group

local notation "M" => MSet.model_isModel Invol

theorem distinctness_necessary_r : Statements.Models.full_involution_group.distinctness_necessary_r :=
  verdict_holds M <|
    holdsAx_indexed.2 fun σ _ => holdsSentence_of_box _ M (Invol.box_nd σ)

theorem necessary_distinctness_necessary_r : Statements.Models.full_involution_group.necessary_distinctness_necessary_r :=
  verdict_holds M <|
    holdsAx_indexed.2 fun σ _ => Invol.box_nd σ

theorem distinctness_necessary_t : Statements.Models.full_involution_group.distinctness_necessary_t :=
  verdict_holds M <|
    holdsAx_eq.2 (holdsSentence_of_box _ M (Invol.box_nd (.rel .t)))

theorem necessary_distinctness_necessary_t : Statements.Models.full_involution_group.necessary_distinctness_necessary_t :=
  verdict_holds M <|
    holdsAx_eq.2 (Invol.box_nd (.rel .t))

theorem barcan_r : Statements.Models.full_involution_group.barcan_r :=
  verdict_holds M <|
    holdsAx_indexed.2 fun σ _ => holdsSentence_of_box _ M (Invol.box_bf σ)

theorem necessary_barcan_r : Statements.Models.full_involution_group.necessary_barcan_r :=
  verdict_holds M <|
    holdsAx_indexed.2 fun σ _ => Invol.box_bf σ

theorem barcan_t : Statements.Models.full_involution_group.barcan_t :=
  verdict_holds M <|
    holdsAx_eq.2 (holdsSentence_of_box _ M (Invol.box_bf (.rel .t)))

theorem necessary_barcan_t : Statements.Models.full_involution_group.necessary_barcan_t :=
  verdict_holds M <|
    holdsAx_eq.2 (Invol.box_bf (.rel .t))

theorem no_pure_contingency_r : Statements.Models.full_involution_group.no_pure_contingency_r :=
  verdict_holds M <|
    holdsAx_npc_pure M

theorem fregean_axiom : Statements.Models.full_involution_group.fregean_axiom :=
  verdict_fails M <|
    not_holdsAx_of rfl (Invol.not_fregean)

theorem necessary_fregean_axiom : Statements.Models.full_involution_group.necessary_fregean_axiom :=
  verdict_fails M <|
    not_holdsAx_of rfl (fun h => Invol.not_fregean (holdsSentence_of_box _ M h))

end full_involution_group

end Classicism.Map.Models
