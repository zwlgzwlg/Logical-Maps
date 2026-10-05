import Classicism.MapArguments
import Classicism.MapModels

/-!
# Generated certificates: models' verdicts from the map's arguments

Written by `pmap lean classicism` from the YAML records. **Do not edit.**

Each verdict a general argument gives a model on the map, certified by applying the
argument's certificate (`MapArguments.lean`) to the model: to its proof of being a model,
and its proofs of the conditions the argument requires (its record's `lean.meets`, or its
group's).
-/

namespace Classicism.Map.Models
open Classicism

/-- `finite-support-dyadic-roundings`: Actuality holds, by `finite-support-one-object`'s argument `actual-world`. -/
theorem finite_support_dyadic_roundings.actuality : Statements.Models.finite_support_dyadic_roundings.actuality :=
  ⟨Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.pow2), Classicism.Map.Arguments.finite_support_one_object.actual_world.actuality (Classicism.Meta.Intensional.Monoids.pow2) (Classicism.Meta.Intensional.MonoidModel.actualWorldPinned_of_onePinned _ Classicism.Meta.Intensional.Monoids.Pow2.onePinned)⟩

/-- `finite-support-dyadic-roundings`: No Pure Contingency holds, by the argument `no-pure-contingency-one-object`. -/
theorem finite_support_dyadic_roundings.no_pure_contingency_r : Statements.Models.finite_support_dyadic_roundings.no_pure_contingency_r :=
  ⟨Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.pow2), Classicism.Map.Arguments.no_pure_contingency_one_object.no_pure_contingency_r (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.pow2)) (Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.pow2)) (Classicism.Meta.Intensional.MonoidModel.oneObject (Classicism.Meta.Intensional.Monoids.pow2))⟩

/-- `finite-support-identity-or-collapse-surjections`: Actuality holds, by `finite-support-one-object`'s argument `actual-world`. -/
theorem finite_support_identity_or_collapse_surjections.actuality : Statements.Models.finite_support_identity_or_collapse_surjections.actuality :=
  ⟨Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.monoSurj01), Classicism.Map.Arguments.finite_support_one_object.actual_world.actuality (Classicism.Meta.Intensional.Monoids.monoSurj01) (Classicism.Meta.Intensional.MonoidModel.actualWorldPinned_of_onePinned _ Classicism.Meta.Intensional.Monoids.MonoSurj01.onePinned)⟩

/-- `finite-support-identity-or-collapse-surjections`: Atomicity fails, by `finite-support-one-object`'s argument `collapsing-atomless`. -/
theorem finite_support_identity_or_collapse_surjections.atomicity_r : Statements.Models.finite_support_identity_or_collapse_surjections.atomicity_r :=
  ⟨Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.monoSurj01), Classicism.Map.Arguments.finite_support_one_object.collapsing_atomless.atomicity_r (Classicism.Meta.Intensional.Monoids.monoSurj01) (Classicism.Map.Meets.finite_support_identity_or_collapse_surjections.collapse_unpinned)⟩

/-- `finite-support-identity-or-collapse-surjections`: Atomicity (type t) fails, by `finite-support-one-object`'s argument `collapsing-atomless`. -/
theorem finite_support_identity_or_collapse_surjections.atomicity_t : Statements.Models.finite_support_identity_or_collapse_surjections.atomicity_t :=
  ⟨Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.monoSurj01), Classicism.Map.Arguments.finite_support_one_object.collapsing_atomless.atomicity_t (Classicism.Meta.Intensional.Monoids.monoSurj01) (Classicism.Map.Meets.finite_support_identity_or_collapse_surjections.collapse_unpinned)⟩

/-- `finite-support-identity-or-collapse-surjections`: BF holds, by the argument `barcan-d6`. -/
theorem finite_support_identity_or_collapse_surjections.barcan_r : Statements.Models.finite_support_identity_or_collapse_surjections.barcan_r :=
  ⟨Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.monoSurj01), Classicism.Map.Arguments.barcan_d6.barcan_r (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj01)) (Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.monoSurj01)) (Classicism.Meta.Intensional.MonoidModel.d6Surjective_of_surjective _ fun k => k.2.2.1)⟩

/-- `finite-support-identity-or-collapse-surjections`: No Pure Contingency holds, by the argument `no-pure-contingency-one-object`. -/
theorem finite_support_identity_or_collapse_surjections.no_pure_contingency_r : Statements.Models.finite_support_identity_or_collapse_surjections.no_pure_contingency_r :=
  ⟨Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.monoSurj01), Classicism.Map.Arguments.no_pure_contingency_one_object.no_pure_contingency_r (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj01)) (Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.monoSurj01)) (Classicism.Meta.Intensional.MonoidModel.oneObject (Classicism.Meta.Intensional.Monoids.monoSurj01))⟩

/-- `finite-support-identity-or-collapse`: Actuality holds, by `finite-support-one-object`'s argument `actual-world`. -/
theorem finite_support_identity_or_collapse.actuality : Statements.Models.finite_support_identity_or_collapse.actuality :=
  ⟨Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.mono01), Classicism.Map.Arguments.finite_support_one_object.actual_world.actuality (Classicism.Meta.Intensional.Monoids.mono01) (Classicism.Meta.Intensional.MonoidModel.actualWorldPinned_of_onePinned _ Classicism.Meta.Intensional.Monoids.Mono01.onePinned)⟩

/-- `finite-support-identity-or-collapse`: Atomicity fails, by `finite-support-one-object`'s argument `collapsing-atomless`. -/
theorem finite_support_identity_or_collapse.atomicity_r : Statements.Models.finite_support_identity_or_collapse.atomicity_r :=
  ⟨Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.mono01), Classicism.Map.Arguments.finite_support_one_object.collapsing_atomless.atomicity_r (Classicism.Meta.Intensional.Monoids.mono01) (Classicism.Map.Meets.finite_support_identity_or_collapse.collapse_unpinned)⟩

/-- `finite-support-identity-or-collapse`: Atomicity (type t) fails, by `finite-support-one-object`'s argument `collapsing-atomless`. -/
theorem finite_support_identity_or_collapse.atomicity_t : Statements.Models.finite_support_identity_or_collapse.atomicity_t :=
  ⟨Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.mono01), Classicism.Map.Arguments.finite_support_one_object.collapsing_atomless.atomicity_t (Classicism.Meta.Intensional.Monoids.mono01) (Classicism.Map.Meets.finite_support_identity_or_collapse.collapse_unpinned)⟩

/-- `finite-support-identity-or-collapse`: BF fails, by `finite-support-one-object`'s argument `barcan-positive`. -/
theorem finite_support_identity_or_collapse.barcan_r : Statements.Models.finite_support_identity_or_collapse.barcan_r :=
  ⟨Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.mono01), Classicism.Map.Arguments.finite_support_one_object.barcan_positive.barcan_r (Classicism.Meta.Intensional.Monoids.mono01) (Classicism.Map.Meets.finite_support_identity_or_collapse.positive_preserving)⟩

/-- `finite-support-identity-or-collapse`: No Pure Contingency holds, by the argument `no-pure-contingency-one-object`. -/
theorem finite_support_identity_or_collapse.no_pure_contingency_r : Statements.Models.finite_support_identity_or_collapse.no_pure_contingency_r :=
  ⟨Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.mono01), Classicism.Map.Arguments.no_pure_contingency_one_object.no_pure_contingency_r (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono01)) (Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.mono01)) (Classicism.Meta.Intensional.MonoidModel.oneObject (Classicism.Meta.Intensional.Monoids.mono01))⟩

/-- `finite-support-monotone-maps`: BF fails, by `finite-support-one-object`'s argument `barcan-positive`. -/
theorem finite_support_monotone_maps.barcan_r : Statements.Models.finite_support_monotone_maps.barcan_r :=
  ⟨Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.mono), Classicism.Map.Arguments.finite_support_one_object.barcan_positive.barcan_r (Classicism.Meta.Intensional.Monoids.mono) (Classicism.Map.Meets.finite_support_monotone_maps.positive_preserving)⟩

/-- `finite-support-monotone-maps`: No Pure Contingency holds, by the argument `no-pure-contingency-one-object`. -/
theorem finite_support_monotone_maps.no_pure_contingency_r : Statements.Models.finite_support_monotone_maps.no_pure_contingency_r :=
  ⟨Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.mono), Classicism.Map.Arguments.no_pure_contingency_one_object.no_pure_contingency_r (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono)) (Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.mono)) (Classicism.Meta.Intensional.MonoidModel.oneObject (Classicism.Meta.Intensional.Monoids.mono))⟩

/-- `finite-support-monotone-surjections`: BF holds, by the argument `barcan-d6`. -/
theorem finite_support_monotone_surjections.barcan_r : Statements.Models.finite_support_monotone_surjections.barcan_r :=
  ⟨Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.monoSurj), Classicism.Map.Arguments.barcan_d6.barcan_r (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj)) (Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.monoSurj)) (Classicism.Meta.Intensional.MonoidModel.d6Surjective_of_surjective _ fun k => k.2.2)⟩

/-- `finite-support-monotone-surjections`: No Pure Contingency holds, by the argument `no-pure-contingency-one-object`. -/
theorem finite_support_monotone_surjections.no_pure_contingency_r : Statements.Models.finite_support_monotone_surjections.no_pure_contingency_r :=
  ⟨Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.monoSurj), Classicism.Map.Arguments.no_pure_contingency_one_object.no_pure_contingency_r (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj)) (Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.monoSurj)) (Classicism.Meta.Intensional.MonoidModel.oneObject (Classicism.Meta.Intensional.Monoids.monoSurj))⟩

/-- `finite-support-permutations`: No Pure Contingency holds, by the argument `no-pure-contingency-one-object`. -/
theorem finite_support_permutations.no_pure_contingency_r : Statements.Models.finite_support_permutations.no_pure_contingency_r :=
  ⟨Classicism.Meta.Intensional.Perms.model_isModel, Classicism.Map.Arguments.no_pure_contingency_one_object.no_pure_contingency_r (Classicism.Meta.Intensional.Perms.model) (Classicism.Meta.Intensional.Perms.model_isModel) (Classicism.Meta.Intensional.MonoidModel.oneObject (Equiv.Perm ℕ))⟩

/-- `finite-support-truncated-shifts`: Actuality holds, by `finite-support-one-object`'s argument `actual-world`. -/
theorem finite_support_truncated_shifts.actuality : Statements.Models.finite_support_truncated_shifts.actuality :=
  ⟨Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.shifts), Classicism.Map.Arguments.finite_support_one_object.actual_world.actuality (Classicism.Meta.Intensional.Monoids.shifts) (Classicism.Meta.Intensional.MonoidModel.actualWorldPinned_of_onePinned _ Classicism.Meta.Intensional.Monoids.Shifts.onePinned)⟩

/-- `finite-support-truncated-shifts`: BF holds, by the argument `barcan-d6`. -/
theorem finite_support_truncated_shifts.barcan_r : Statements.Models.finite_support_truncated_shifts.barcan_r :=
  ⟨Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.shifts), Classicism.Map.Arguments.barcan_d6.barcan_r (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.shifts)) (Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.shifts)) (Classicism.Meta.Intensional.MonoidModel.d6Surjective_of_surjective _ Classicism.Meta.Intensional.Monoids.Shifts.surj)⟩

/-- `finite-support-truncated-shifts`: No Pure Contingency holds, by the argument `no-pure-contingency-one-object`. -/
theorem finite_support_truncated_shifts.no_pure_contingency_r : Statements.Models.finite_support_truncated_shifts.no_pure_contingency_r :=
  ⟨Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.shifts), Classicism.Map.Arguments.no_pure_contingency_one_object.no_pure_contingency_r (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.shifts)) (Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.shifts)) (Classicism.Meta.Intensional.MonoidModel.oneObject (Classicism.Meta.Intensional.Monoids.shifts))⟩

/-- `finite-support-truncations`: No Pure Contingency holds, by the argument `no-pure-contingency-one-object`. -/
theorem finite_support_truncations.no_pure_contingency_r : Statements.Models.finite_support_truncations.no_pure_contingency_r :=
  ⟨Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.truncs), Classicism.Map.Arguments.no_pure_contingency_one_object.no_pure_contingency_r (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.truncs)) (Classicism.Meta.Intensional.MonoidModel.model_isModel (Classicism.Meta.Intensional.Monoids.truncs)) (Classicism.Meta.Intensional.MonoidModel.oneObject (Classicism.Meta.Intensional.Monoids.truncs))⟩

/-- `full-idempotent-monoid`: Distinctness-preserving collapse holds, by the argument `dpc-isolated-actual-world`. -/
theorem full_idempotent_monoid.distinctness_preserving_collapse : Statements.Models.full_idempotent_monoid.distinctness_preserving_collapse :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Idem, Classicism.Map.Arguments.dpc_isolated_actual_world.distinctness_preserving_collapse (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem) (Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Idem) (Classicism.Map.Meets.full_idempotent_monoid.actual_world_isolated)⟩

/-- `full-idempotent-monoid`: Infinity Schema (type t) fails, by the argument `finitely-many-propositions`. -/
theorem full_idempotent_monoid.infinity_t : Statements.Models.full_idempotent_monoid.infinity_t :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Idem, Classicism.Map.Arguments.finitely_many_propositions.infinity_t (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem) (Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Idem) (Classicism.Meta.Intensional.MSet.model_full Classicism.Meta.Intensional.Idem) (Classicism.Map.Meets.mset_finitely_many_propositions Classicism.Meta.Intensional.Idem)⟩

/-- `full-idempotent-monoid`: No Pure Contingency holds, by the argument `no-pure-contingency-one-object`. -/
theorem full_idempotent_monoid.no_pure_contingency_r : Statements.Models.full_idempotent_monoid.no_pure_contingency_r :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Idem, Classicism.Map.Arguments.no_pure_contingency_one_object.no_pure_contingency_r (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem) (Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Idem) (Classicism.Meta.Intensional.Premodel.oneObject_of_subsingleton _)⟩

/-- `full-idempotent-monoid`: Infinity Schema (type e) fails, by the argument `one-individual`. -/
theorem full_idempotent_monoid.infinity_e : Statements.Models.full_idempotent_monoid.infinity_e :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Idem, Classicism.Map.Arguments.one_individual.infinity_e (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem) (Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Idem) (Classicism.Map.Meets.mset_one_individual Classicism.Meta.Intensional.Idem)⟩

/-- `full-idempotent-monoid`: Axiom of Infinity (type e) fails, by the argument `one-individual`. -/
theorem full_idempotent_monoid.axiom_of_infinity_e : Statements.Models.full_idempotent_monoid.axiom_of_infinity_e :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Idem, Classicism.Map.Arguments.one_individual.axiom_of_infinity_e (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem) (Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Idem) (Classicism.Map.Meets.mset_one_individual Classicism.Meta.Intensional.Idem)⟩

/-- `full-idempotent-monoid`: Possible Infinity (type e) fails, by the argument `one-individual`. -/
theorem full_idempotent_monoid.possible_infinity_e : Statements.Models.full_idempotent_monoid.possible_infinity_e :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Idem, Classicism.Map.Arguments.one_individual.possible_infinity_e (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem) (Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Idem) (Classicism.Map.Meets.mset_one_individual Classicism.Meta.Intensional.Idem)⟩

/-- `full-idempotent-monoid`: □Relational Choice holds, by the argument `relational-choice-full-boxed`. -/
theorem full_idempotent_monoid.necessary_relational_choice_r : Statements.Models.full_idempotent_monoid.necessary_relational_choice_r :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Idem, Classicism.Map.Arguments.relational_choice_full_boxed.necessary_relational_choice_r (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem) (Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Idem) (Classicism.Meta.Intensional.MSet.model_full Classicism.Meta.Intensional.Idem) (Classicism.Meta.Intensional.Premodel.metatheoryChoice _)⟩

/-- `full-idempotent-monoid`: Relational Choice holds, by the argument `relational-choice-full`. -/
theorem full_idempotent_monoid.relational_choice_r : Statements.Models.full_idempotent_monoid.relational_choice_r :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Idem, Classicism.Map.Arguments.relational_choice_full.relational_choice_r (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem) (Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Idem) (Classicism.Meta.Intensional.MSet.model_full Classicism.Meta.Intensional.Idem) (Classicism.Meta.Intensional.Premodel.metatheoryChoice _)⟩

/-- `full-idempotent-monoid`: Transversal Choice holds, by the argument `transversal-choice-extensionally-full`. -/
theorem full_idempotent_monoid.transversal_choice_r : Statements.Models.full_idempotent_monoid.transversal_choice_r :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Idem, Classicism.Map.Arguments.transversal_choice_extensionally_full.transversal_choice_r (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem) (Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Idem) (Classicism.Meta.Intensional.Premodel.Full.extFull _ (Classicism.Meta.Intensional.MSet.model_full Classicism.Meta.Intensional.Idem)) (Classicism.Meta.Intensional.Premodel.metatheoryChoice _)⟩

/-- `full-involution-group`: Infinity Schema (type t) fails, by the argument `finitely-many-propositions`. -/
theorem full_involution_group.infinity_t : Statements.Models.full_involution_group.infinity_t :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Invol, Classicism.Map.Arguments.finitely_many_propositions.infinity_t (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol) (Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Invol) (Classicism.Meta.Intensional.MSet.model_full Classicism.Meta.Intensional.Invol) (Classicism.Map.Meets.mset_finitely_many_propositions Classicism.Meta.Intensional.Invol)⟩

/-- `full-involution-group`: No Pure Contingency holds, by the argument `no-pure-contingency-one-object`. -/
theorem full_involution_group.no_pure_contingency_r : Statements.Models.full_involution_group.no_pure_contingency_r :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Invol, Classicism.Map.Arguments.no_pure_contingency_one_object.no_pure_contingency_r (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol) (Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Invol) (Classicism.Meta.Intensional.Premodel.oneObject_of_subsingleton _)⟩

/-- `full-involution-group`: Infinity Schema (type e) fails, by the argument `one-individual`. -/
theorem full_involution_group.infinity_e : Statements.Models.full_involution_group.infinity_e :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Invol, Classicism.Map.Arguments.one_individual.infinity_e (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol) (Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Invol) (Classicism.Map.Meets.mset_one_individual Classicism.Meta.Intensional.Invol)⟩

/-- `full-involution-group`: Axiom of Infinity (type e) fails, by the argument `one-individual`. -/
theorem full_involution_group.axiom_of_infinity_e : Statements.Models.full_involution_group.axiom_of_infinity_e :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Invol, Classicism.Map.Arguments.one_individual.axiom_of_infinity_e (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol) (Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Invol) (Classicism.Map.Meets.mset_one_individual Classicism.Meta.Intensional.Invol)⟩

/-- `full-involution-group`: Possible Infinity (type e) fails, by the argument `one-individual`. -/
theorem full_involution_group.possible_infinity_e : Statements.Models.full_involution_group.possible_infinity_e :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Invol, Classicism.Map.Arguments.one_individual.possible_infinity_e (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol) (Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Invol) (Classicism.Map.Meets.mset_one_individual Classicism.Meta.Intensional.Invol)⟩

/-- `full-involution-group`: □Relational Choice holds, by the argument `relational-choice-full-boxed`. -/
theorem full_involution_group.necessary_relational_choice_r : Statements.Models.full_involution_group.necessary_relational_choice_r :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Invol, Classicism.Map.Arguments.relational_choice_full_boxed.necessary_relational_choice_r (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol) (Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Invol) (Classicism.Meta.Intensional.MSet.model_full Classicism.Meta.Intensional.Invol) (Classicism.Meta.Intensional.Premodel.metatheoryChoice _)⟩

/-- `full-involution-group`: Relational Choice holds, by the argument `relational-choice-full`. -/
theorem full_involution_group.relational_choice_r : Statements.Models.full_involution_group.relational_choice_r :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Invol, Classicism.Map.Arguments.relational_choice_full.relational_choice_r (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol) (Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Invol) (Classicism.Meta.Intensional.MSet.model_full Classicism.Meta.Intensional.Invol) (Classicism.Meta.Intensional.Premodel.metatheoryChoice _)⟩

/-- `full-involution-group`: Transversal Choice holds, by the argument `transversal-choice-extensionally-full`. -/
theorem full_involution_group.transversal_choice_r : Statements.Models.full_involution_group.transversal_choice_r :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Invol, Classicism.Map.Arguments.transversal_choice_extensionally_full.transversal_choice_r (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol) (Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.Invol) (Classicism.Meta.Intensional.Premodel.Full.extFull _ (Classicism.Meta.Intensional.MSet.model_full Classicism.Meta.Intensional.Invol)) (Classicism.Meta.Intensional.Premodel.metatheoryChoice _)⟩

/-- `full-permutation-group-infinite-set`: No Pure Contingency holds, by the argument `no-pure-contingency-one-object`. -/
theorem full_permutation_group_infinite_set.no_pure_contingency_r : Statements.Models.full_permutation_group_infinite_set.no_pure_contingency_r :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel (Equiv.Perm ℕ), Classicism.Map.Arguments.no_pure_contingency_one_object.no_pure_contingency_r (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)) (Classicism.Meta.Intensional.MSet.model_isModel (Equiv.Perm ℕ)) (Classicism.Meta.Intensional.Premodel.oneObject_of_subsingleton _)⟩

/-- `full-permutation-group-infinite-set`: Infinity Schema (type e) fails, by the argument `one-individual`. -/
theorem full_permutation_group_infinite_set.infinity_e : Statements.Models.full_permutation_group_infinite_set.infinity_e :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel (Equiv.Perm ℕ), Classicism.Map.Arguments.one_individual.infinity_e (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)) (Classicism.Meta.Intensional.MSet.model_isModel (Equiv.Perm ℕ)) (Classicism.Map.Meets.mset_one_individual (Equiv.Perm ℕ))⟩

/-- `full-permutation-group-infinite-set`: Axiom of Infinity (type e) fails, by the argument `one-individual`. -/
theorem full_permutation_group_infinite_set.axiom_of_infinity_e : Statements.Models.full_permutation_group_infinite_set.axiom_of_infinity_e :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel (Equiv.Perm ℕ), Classicism.Map.Arguments.one_individual.axiom_of_infinity_e (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)) (Classicism.Meta.Intensional.MSet.model_isModel (Equiv.Perm ℕ)) (Classicism.Map.Meets.mset_one_individual (Equiv.Perm ℕ))⟩

/-- `full-permutation-group-infinite-set`: Possible Infinity (type e) fails, by the argument `one-individual`. -/
theorem full_permutation_group_infinite_set.possible_infinity_e : Statements.Models.full_permutation_group_infinite_set.possible_infinity_e :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel (Equiv.Perm ℕ), Classicism.Map.Arguments.one_individual.possible_infinity_e (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)) (Classicism.Meta.Intensional.MSet.model_isModel (Equiv.Perm ℕ)) (Classicism.Map.Meets.mset_one_individual (Equiv.Perm ℕ))⟩

/-- `full-permutation-group-infinite-set`: □Relational Choice holds, by the argument `relational-choice-full-boxed`. -/
theorem full_permutation_group_infinite_set.necessary_relational_choice_r : Statements.Models.full_permutation_group_infinite_set.necessary_relational_choice_r :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel (Equiv.Perm ℕ), Classicism.Map.Arguments.relational_choice_full_boxed.necessary_relational_choice_r (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)) (Classicism.Meta.Intensional.MSet.model_isModel (Equiv.Perm ℕ)) (Classicism.Meta.Intensional.MSet.model_full (Equiv.Perm ℕ)) (Classicism.Meta.Intensional.Premodel.metatheoryChoice _)⟩

/-- `full-permutation-group-infinite-set`: Relational Choice holds, by the argument `relational-choice-full`. -/
theorem full_permutation_group_infinite_set.relational_choice_r : Statements.Models.full_permutation_group_infinite_set.relational_choice_r :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel (Equiv.Perm ℕ), Classicism.Map.Arguments.relational_choice_full.relational_choice_r (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)) (Classicism.Meta.Intensional.MSet.model_isModel (Equiv.Perm ℕ)) (Classicism.Meta.Intensional.MSet.model_full (Equiv.Perm ℕ)) (Classicism.Meta.Intensional.Premodel.metatheoryChoice _)⟩

/-- `full-permutation-group-infinite-set`: Transversal Choice holds, by the argument `transversal-choice-extensionally-full`. -/
theorem full_permutation_group_infinite_set.transversal_choice_r : Statements.Models.full_permutation_group_infinite_set.transversal_choice_r :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel (Equiv.Perm ℕ), Classicism.Map.Arguments.transversal_choice_extensionally_full.transversal_choice_r (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)) (Classicism.Meta.Intensional.MSet.model_isModel (Equiv.Perm ℕ)) (Classicism.Meta.Intensional.Premodel.Full.extFull _ (Classicism.Meta.Intensional.MSet.model_full (Equiv.Perm ℕ))) (Classicism.Meta.Intensional.Premodel.metatheoryChoice _)⟩

/-- `full-surjection-monoid`: No Pure Contingency holds, by the argument `no-pure-contingency-one-object`. -/
theorem full_surjection_monoid.no_pure_contingency_r : Statements.Models.full_surjection_monoid.no_pure_contingency_r :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.FullActionModels.surj, Classicism.Map.Arguments.no_pure_contingency_one_object.no_pure_contingency_r (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj) (Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.FullActionModels.surj) (Classicism.Meta.Intensional.Premodel.oneObject_of_subsingleton _)⟩

/-- `full-surjection-monoid`: Infinity Schema (type e) fails, by the argument `one-individual`. -/
theorem full_surjection_monoid.infinity_e : Statements.Models.full_surjection_monoid.infinity_e :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.FullActionModels.surj, Classicism.Map.Arguments.one_individual.infinity_e (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj) (Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.FullActionModels.surj) (Classicism.Map.Meets.mset_one_individual Classicism.Meta.Intensional.FullActionModels.surj)⟩

/-- `full-surjection-monoid`: Axiom of Infinity (type e) fails, by the argument `one-individual`. -/
theorem full_surjection_monoid.axiom_of_infinity_e : Statements.Models.full_surjection_monoid.axiom_of_infinity_e :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.FullActionModels.surj, Classicism.Map.Arguments.one_individual.axiom_of_infinity_e (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj) (Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.FullActionModels.surj) (Classicism.Map.Meets.mset_one_individual Classicism.Meta.Intensional.FullActionModels.surj)⟩

/-- `full-surjection-monoid`: Possible Infinity (type e) fails, by the argument `one-individual`. -/
theorem full_surjection_monoid.possible_infinity_e : Statements.Models.full_surjection_monoid.possible_infinity_e :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.FullActionModels.surj, Classicism.Map.Arguments.one_individual.possible_infinity_e (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj) (Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.FullActionModels.surj) (Classicism.Map.Meets.mset_one_individual Classicism.Meta.Intensional.FullActionModels.surj)⟩

/-- `full-surjection-monoid`: □Relational Choice holds, by the argument `relational-choice-full-boxed`. -/
theorem full_surjection_monoid.necessary_relational_choice_r : Statements.Models.full_surjection_monoid.necessary_relational_choice_r :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.FullActionModels.surj, Classicism.Map.Arguments.relational_choice_full_boxed.necessary_relational_choice_r (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj) (Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.FullActionModels.surj) (Classicism.Meta.Intensional.MSet.model_full Classicism.Meta.Intensional.FullActionModels.surj) (Classicism.Meta.Intensional.Premodel.metatheoryChoice _)⟩

/-- `full-surjection-monoid`: Relational Choice holds, by the argument `relational-choice-full`. -/
theorem full_surjection_monoid.relational_choice_r : Statements.Models.full_surjection_monoid.relational_choice_r :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.FullActionModels.surj, Classicism.Map.Arguments.relational_choice_full.relational_choice_r (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj) (Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.FullActionModels.surj) (Classicism.Meta.Intensional.MSet.model_full Classicism.Meta.Intensional.FullActionModels.surj) (Classicism.Meta.Intensional.Premodel.metatheoryChoice _)⟩

/-- `full-surjection-monoid`: Transversal Choice holds, by the argument `transversal-choice-extensionally-full`. -/
theorem full_surjection_monoid.transversal_choice_r : Statements.Models.full_surjection_monoid.transversal_choice_r :=
  ⟨Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.FullActionModels.surj, Classicism.Map.Arguments.transversal_choice_extensionally_full.transversal_choice_r (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj) (Classicism.Meta.Intensional.MSet.model_isModel Classicism.Meta.Intensional.FullActionModels.surj) (Classicism.Meta.Intensional.Premodel.Full.extFull _ (Classicism.Meta.Intensional.MSet.model_full Classicism.Meta.Intensional.FullActionModels.surj)) (Classicism.Meta.Intensional.Premodel.metatheoryChoice _)⟩

/-- `full-two-object-chain`: Distinctness-preserving collapse holds, by the argument `dpc-isolated-actual-world`. -/
theorem full_two_object_chain.distinctness_preserving_collapse : Statements.Models.full_two_object_chain.distinctness_preserving_collapse :=
  ⟨Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _, Classicism.Map.Arguments.dpc_isolated_actual_world.distinctness_preserving_collapse (Classicism.Meta.Intensional.FullActionModels.chain) (Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _) (Classicism.Meta.Intensional.FullActionModels.chain_actual_world_isolated)⟩

/-- `full-two-object-chain`: Infinity Schema (type t) fails, by the argument `finitely-many-propositions`. -/
theorem full_two_object_chain.infinity_t : Statements.Models.full_two_object_chain.infinity_t :=
  ⟨Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _, Classicism.Map.Arguments.finitely_many_propositions.infinity_t (Classicism.Meta.Intensional.FullActionModels.chain) (Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _) (Classicism.Meta.Intensional.FullActionModels.unitModel_full _) (Classicism.Meta.Intensional.FullActionModels.chain_finitely_many_propositions)⟩

/-- `full-two-object-chain`: Infinity Schema (type e) fails, by the argument `one-individual`. -/
theorem full_two_object_chain.infinity_e : Statements.Models.full_two_object_chain.infinity_e :=
  ⟨Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _, Classicism.Map.Arguments.one_individual.infinity_e (Classicism.Meta.Intensional.FullActionModels.chain) (Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _) (Classicism.Meta.Intensional.FullActionModels.unitModel_one_individual _)⟩

/-- `full-two-object-chain`: Axiom of Infinity (type e) fails, by the argument `one-individual`. -/
theorem full_two_object_chain.axiom_of_infinity_e : Statements.Models.full_two_object_chain.axiom_of_infinity_e :=
  ⟨Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _, Classicism.Map.Arguments.one_individual.axiom_of_infinity_e (Classicism.Meta.Intensional.FullActionModels.chain) (Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _) (Classicism.Meta.Intensional.FullActionModels.unitModel_one_individual _)⟩

/-- `full-two-object-chain`: Possible Infinity (type e) fails, by the argument `one-individual`. -/
theorem full_two_object_chain.possible_infinity_e : Statements.Models.full_two_object_chain.possible_infinity_e :=
  ⟨Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _, Classicism.Map.Arguments.one_individual.possible_infinity_e (Classicism.Meta.Intensional.FullActionModels.chain) (Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _) (Classicism.Meta.Intensional.FullActionModels.unitModel_one_individual _)⟩

/-- `full-two-object-chain`: □Relational Choice holds, by the argument `relational-choice-full-boxed`. -/
theorem full_two_object_chain.necessary_relational_choice_r : Statements.Models.full_two_object_chain.necessary_relational_choice_r :=
  ⟨Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _, Classicism.Map.Arguments.relational_choice_full_boxed.necessary_relational_choice_r (Classicism.Meta.Intensional.FullActionModels.chain) (Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _) (Classicism.Meta.Intensional.FullActionModels.unitModel_full _) (Classicism.Meta.Intensional.Premodel.metatheoryChoice _)⟩

/-- `full-two-object-chain`: Relational Choice holds, by the argument `relational-choice-full`. -/
theorem full_two_object_chain.relational_choice_r : Statements.Models.full_two_object_chain.relational_choice_r :=
  ⟨Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _, Classicism.Map.Arguments.relational_choice_full.relational_choice_r (Classicism.Meta.Intensional.FullActionModels.chain) (Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _) (Classicism.Meta.Intensional.FullActionModels.unitModel_full _) (Classicism.Meta.Intensional.Premodel.metatheoryChoice _)⟩

/-- `full-two-object-chain`: Transversal Choice holds, by the argument `transversal-choice-extensionally-full`. -/
theorem full_two_object_chain.transversal_choice_r : Statements.Models.full_two_object_chain.transversal_choice_r :=
  ⟨Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _, Classicism.Map.Arguments.transversal_choice_extensionally_full.transversal_choice_r (Classicism.Meta.Intensional.FullActionModels.chain) (Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _) (Classicism.Meta.Intensional.Premodel.Full.extFull _ (Classicism.Meta.Intensional.FullActionModels.unitModel_full _)) (Classicism.Meta.Intensional.Premodel.metatheoryChoice _)⟩

/-- `full-two-object-retract`: Infinity Schema (type e) fails, by the argument `one-individual`. -/
theorem full_two_object_retract.infinity_e : Statements.Models.full_two_object_retract.infinity_e :=
  ⟨Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _, Classicism.Map.Arguments.one_individual.infinity_e (Classicism.Meta.Intensional.FullActionModels.retract) (Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _) (Classicism.Meta.Intensional.FullActionModels.unitModel_one_individual _)⟩

/-- `full-two-object-retract`: Axiom of Infinity (type e) fails, by the argument `one-individual`. -/
theorem full_two_object_retract.axiom_of_infinity_e : Statements.Models.full_two_object_retract.axiom_of_infinity_e :=
  ⟨Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _, Classicism.Map.Arguments.one_individual.axiom_of_infinity_e (Classicism.Meta.Intensional.FullActionModels.retract) (Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _) (Classicism.Meta.Intensional.FullActionModels.unitModel_one_individual _)⟩

/-- `full-two-object-retract`: Possible Infinity (type e) fails, by the argument `one-individual`. -/
theorem full_two_object_retract.possible_infinity_e : Statements.Models.full_two_object_retract.possible_infinity_e :=
  ⟨Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _, Classicism.Map.Arguments.one_individual.possible_infinity_e (Classicism.Meta.Intensional.FullActionModels.retract) (Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _) (Classicism.Meta.Intensional.FullActionModels.unitModel_one_individual _)⟩

/-- `full-two-object-retract`: □Relational Choice holds, by the argument `relational-choice-full-boxed`. -/
theorem full_two_object_retract.necessary_relational_choice_r : Statements.Models.full_two_object_retract.necessary_relational_choice_r :=
  ⟨Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _, Classicism.Map.Arguments.relational_choice_full_boxed.necessary_relational_choice_r (Classicism.Meta.Intensional.FullActionModels.retract) (Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _) (Classicism.Meta.Intensional.FullActionModels.unitModel_full _) (Classicism.Meta.Intensional.Premodel.metatheoryChoice _)⟩

/-- `full-two-object-retract`: Relational Choice holds, by the argument `relational-choice-full`. -/
theorem full_two_object_retract.relational_choice_r : Statements.Models.full_two_object_retract.relational_choice_r :=
  ⟨Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _, Classicism.Map.Arguments.relational_choice_full.relational_choice_r (Classicism.Meta.Intensional.FullActionModels.retract) (Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _) (Classicism.Meta.Intensional.FullActionModels.unitModel_full _) (Classicism.Meta.Intensional.Premodel.metatheoryChoice _)⟩

/-- `full-two-object-retract`: Transversal Choice holds, by the argument `transversal-choice-extensionally-full`. -/
theorem full_two_object_retract.transversal_choice_r : Statements.Models.full_two_object_retract.transversal_choice_r :=
  ⟨Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _, Classicism.Map.Arguments.transversal_choice_extensionally_full.transversal_choice_r (Classicism.Meta.Intensional.FullActionModels.retract) (Classicism.Meta.Intensional.FullActionModels.unitModel_isModel _) (Classicism.Meta.Intensional.Premodel.Full.extFull _ (Classicism.Meta.Intensional.FullActionModels.unitModel_full _)) (Classicism.Meta.Intensional.Premodel.metatheoryChoice _)⟩

end Classicism.Map.Models
