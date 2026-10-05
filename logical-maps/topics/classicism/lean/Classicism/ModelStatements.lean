import Classicism.Certified.Signatures
import Classicism.Semantics.IntensionalTheory
import Classicism.Models.Permutations
import Classicism.Models.Monoids
import Classicism.Models.ContingentBarcan
import Classicism.Semantics.IntensionalExamples
import Classicism.Models.Conditions
import Classicism.Models.FullActionModels

/-!
# Generated statements: models' verdicts

Written by `pmap lean classicism` from the YAML records. **Do not edit.**

One declaration per verdict a model record proves in Lean (its `lean.verdicts`): that
the principle holds, or fails, in the record's Lean model.
-/

namespace Classicism.Statements
open Classicism

/-- `finite-support-dyadic-roundings`: Atomicity (type t) holds. -/
def Models.finite_support_dyadic_roundings.atomicity_t : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.pow2)).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.pow2)).HoldsAx Classicism.P.AtomicityT.schemaIn

/-- `finite-support-dyadic-roundings`: ND fails. -/
def Models.finite_support_dyadic_roundings.distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.pow2)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.pow2)).HoldsAx Classicism.P.NecessityOfDistinctness.schemaIn

/-- `finite-support-dyadic-roundings`: □ND fails. -/
def Models.finite_support_dyadic_roundings.necessary_distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.pow2)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.pow2)).HoldsAx Classicism.P.NecNecessityOfDistinctness.schemaIn

/-- `finite-support-dyadic-roundings`: BF fails. -/
def Models.finite_support_dyadic_roundings.barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.pow2)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.pow2)).HoldsAx Classicism.P.Barcan.schemaIn

/-- `finite-support-dyadic-roundings`: □BF fails. -/
def Models.finite_support_dyadic_roundings.necessary_barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.pow2)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.pow2)).HoldsAx Classicism.P.NecBarcan.schemaIn

/-- `finite-support-dyadic-roundings`: Boolean Completeness fails. -/
def Models.finite_support_dyadic_roundings.boolean_completeness_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.pow2)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.pow2)).HoldsAx Classicism.P.BooleanCompleteness.schemaIn

/-- `finite-support-identity-or-collapse-surjections`: □BF holds. -/
def Models.finite_support_identity_or_collapse_surjections.necessary_barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj01)).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj01)).HoldsAx Classicism.P.NecBarcan.schemaIn

/-- `finite-support-identity-or-collapse-surjections`: ND fails. -/
def Models.finite_support_identity_or_collapse_surjections.distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj01)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj01)).HoldsAx Classicism.P.NecessityOfDistinctness.schemaIn

/-- `finite-support-identity-or-collapse-surjections`: □ND fails. -/
def Models.finite_support_identity_or_collapse_surjections.necessary_distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj01)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj01)).HoldsAx Classicism.P.NecNecessityOfDistinctness.schemaIn

/-- `finite-support-identity-or-collapse-surjections`: Boolean Completeness fails. -/
def Models.finite_support_identity_or_collapse_surjections.boolean_completeness_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj01)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj01)).HoldsAx Classicism.P.BooleanCompleteness.schemaIn

/-- `finite-support-identity-or-collapse`: ND fails. -/
def Models.finite_support_identity_or_collapse.distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono01)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono01)).HoldsAx Classicism.P.NecessityOfDistinctness.schemaIn

/-- `finite-support-identity-or-collapse`: □ND fails. -/
def Models.finite_support_identity_or_collapse.necessary_distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono01)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono01)).HoldsAx Classicism.P.NecNecessityOfDistinctness.schemaIn

/-- `finite-support-identity-or-collapse`: □BF fails. -/
def Models.finite_support_identity_or_collapse.necessary_barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono01)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono01)).HoldsAx Classicism.P.NecBarcan.schemaIn

/-- `finite-support-identity-or-collapse`: Boolean Completeness fails. -/
def Models.finite_support_identity_or_collapse.boolean_completeness_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono01)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono01)).HoldsAx Classicism.P.BooleanCompleteness.schemaIn

/-- `finite-support-monotone-maps`: Atomlessness holds. -/
def Models.finite_support_monotone_maps.atomlessness : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono)).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono)).HoldsAx Classicism.P.Atomlessness.schemaIn

/-- `finite-support-monotone-maps`: ND fails. -/
def Models.finite_support_monotone_maps.distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono)).HoldsAx Classicism.P.NecessityOfDistinctness.schemaIn

/-- `finite-support-monotone-maps`: □ND fails. -/
def Models.finite_support_monotone_maps.necessary_distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono)).HoldsAx Classicism.P.NecNecessityOfDistinctness.schemaIn

/-- `finite-support-monotone-maps`: □BF fails. -/
def Models.finite_support_monotone_maps.necessary_barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono)).HoldsAx Classicism.P.NecBarcan.schemaIn

/-- `finite-support-monotone-maps`: Actuality fails. -/
def Models.finite_support_monotone_maps.actuality : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono)).HoldsAx Classicism.P.Actuality.schemaIn

/-- `finite-support-monotone-maps`: Atomicity (type t) fails. -/
def Models.finite_support_monotone_maps.atomicity_t : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono)).HoldsAx Classicism.P.AtomicityT.schemaIn

/-- `finite-support-monotone-maps`: Boolean Completeness fails. -/
def Models.finite_support_monotone_maps.boolean_completeness_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono)).HoldsAx Classicism.P.BooleanCompleteness.schemaIn

/-- `finite-support-monotone-surjections`: □BF holds. -/
def Models.finite_support_monotone_surjections.necessary_barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj)).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj)).HoldsAx Classicism.P.NecBarcan.schemaIn

/-- `finite-support-monotone-surjections`: Atomlessness holds. -/
def Models.finite_support_monotone_surjections.atomlessness : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj)).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj)).HoldsAx Classicism.P.Atomlessness.schemaIn

/-- `finite-support-monotone-surjections`: ND fails. -/
def Models.finite_support_monotone_surjections.distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj)).HoldsAx Classicism.P.NecessityOfDistinctness.schemaIn

/-- `finite-support-monotone-surjections`: □ND fails. -/
def Models.finite_support_monotone_surjections.necessary_distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj)).HoldsAx Classicism.P.NecNecessityOfDistinctness.schemaIn

/-- `finite-support-monotone-surjections`: Actuality fails. -/
def Models.finite_support_monotone_surjections.actuality : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj)).HoldsAx Classicism.P.Actuality.schemaIn

/-- `finite-support-monotone-surjections`: Atomicity (type t) fails. -/
def Models.finite_support_monotone_surjections.atomicity_t : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj)).HoldsAx Classicism.P.AtomicityT.schemaIn

/-- `finite-support-monotone-surjections`: Boolean Completeness fails. -/
def Models.finite_support_monotone_surjections.boolean_completeness_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj)).HoldsAx Classicism.P.BooleanCompleteness.schemaIn

/-- `finite-support-permutations`: ND holds. -/
def Models.finite_support_permutations.distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.Perms.model).IsModel ∧ (Classicism.Meta.Intensional.Perms.model).HoldsAx Classicism.P.NecessityOfDistinctness.schemaIn

/-- `finite-support-permutations`: □ND holds. -/
def Models.finite_support_permutations.necessary_distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.Perms.model).IsModel ∧ (Classicism.Meta.Intensional.Perms.model).HoldsAx Classicism.P.NecNecessityOfDistinctness.schemaIn

/-- `finite-support-permutations`: BF holds. -/
def Models.finite_support_permutations.barcan_r : Prop :=
  (Classicism.Meta.Intensional.Perms.model).IsModel ∧ (Classicism.Meta.Intensional.Perms.model).HoldsAx Classicism.P.Barcan.schemaIn

/-- `finite-support-permutations`: □BF holds. -/
def Models.finite_support_permutations.necessary_barcan_r : Prop :=
  (Classicism.Meta.Intensional.Perms.model).IsModel ∧ (Classicism.Meta.Intensional.Perms.model).HoldsAx Classicism.P.NecBarcan.schemaIn

/-- `finite-support-permutations`: Atomlessness holds. -/
def Models.finite_support_permutations.atomlessness : Prop :=
  (Classicism.Meta.Intensional.Perms.model).IsModel ∧ (Classicism.Meta.Intensional.Perms.model).HoldsAx Classicism.P.Atomlessness.schemaIn

/-- `finite-support-permutations`: Actuality fails. -/
def Models.finite_support_permutations.actuality : Prop :=
  (Classicism.Meta.Intensional.Perms.model).IsModel ∧ ¬ (Classicism.Meta.Intensional.Perms.model).HoldsAx Classicism.P.Actuality.schemaIn

/-- `finite-support-permutations`: Atomicity (type t) fails. -/
def Models.finite_support_permutations.atomicity_t : Prop :=
  (Classicism.Meta.Intensional.Perms.model).IsModel ∧ ¬ (Classicism.Meta.Intensional.Perms.model).HoldsAx Classicism.P.AtomicityT.schemaIn

/-- `finite-support-permutations`: Boolean Completeness fails. -/
def Models.finite_support_permutations.boolean_completeness_r : Prop :=
  (Classicism.Meta.Intensional.Perms.model).IsModel ∧ ¬ (Classicism.Meta.Intensional.Perms.model).HoldsAx Classicism.P.BooleanCompleteness.schemaIn

/-- `finite-support-truncated-shifts`: □BF holds. -/
def Models.finite_support_truncated_shifts.necessary_barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.shifts)).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.shifts)).HoldsAx Classicism.P.NecBarcan.schemaIn

/-- `finite-support-truncated-shifts`: Atomicity (type t) holds. -/
def Models.finite_support_truncated_shifts.atomicity_t : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.shifts)).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.shifts)).HoldsAx Classicism.P.AtomicityT.schemaIn

/-- `finite-support-truncated-shifts`: ND fails. -/
def Models.finite_support_truncated_shifts.distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.shifts)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.shifts)).HoldsAx Classicism.P.NecessityOfDistinctness.schemaIn

/-- `finite-support-truncated-shifts`: □ND fails. -/
def Models.finite_support_truncated_shifts.necessary_distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.shifts)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.shifts)).HoldsAx Classicism.P.NecNecessityOfDistinctness.schemaIn

/-- `finite-support-truncated-shifts`: Boolean Completeness fails. -/
def Models.finite_support_truncated_shifts.boolean_completeness_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.shifts)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.shifts)).HoldsAx Classicism.P.BooleanCompleteness.schemaIn

/-- `finite-support-truncations`: Atomicity (type t) holds. -/
def Models.finite_support_truncations.atomicity_t : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.truncs)).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.truncs)).HoldsAx Classicism.P.AtomicityT.schemaIn

/-- `finite-support-truncations`: ND fails. -/
def Models.finite_support_truncations.distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.truncs)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.truncs)).HoldsAx Classicism.P.NecessityOfDistinctness.schemaIn

/-- `finite-support-truncations`: □ND fails. -/
def Models.finite_support_truncations.necessary_distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.truncs)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.truncs)).HoldsAx Classicism.P.NecNecessityOfDistinctness.schemaIn

/-- `finite-support-truncations`: BF fails. -/
def Models.finite_support_truncations.barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.truncs)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.truncs)).HoldsAx Classicism.P.Barcan.schemaIn

/-- `finite-support-truncations`: □BF fails. -/
def Models.finite_support_truncations.necessary_barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.truncs)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.truncs)).HoldsAx Classicism.P.NecBarcan.schemaIn

/-- `finite-support-truncations`: Actuality fails. -/
def Models.finite_support_truncations.actuality : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.truncs)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.truncs)).HoldsAx Classicism.P.Actuality.schemaIn

/-- `finite-support-truncations`: Boolean Completeness fails. -/
def Models.finite_support_truncations.boolean_completeness_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.truncs)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.truncs)).HoldsAx Classicism.P.BooleanCompleteness.schemaIn

/-- `finite-support-two-object-all-maps`: BF holds. -/
def Models.finite_support_two_object_all_maps.barcan_r : Prop :=
  (Classicism.Meta.Intensional.ContingentBarcan.model).IsModel ∧ (Classicism.Meta.Intensional.ContingentBarcan.model).HoldsAx Classicism.P.Barcan.schemaIn

/-- `finite-support-two-object-all-maps`: □BF fails. -/
def Models.finite_support_two_object_all_maps.necessary_barcan_r : Prop :=
  (Classicism.Meta.Intensional.ContingentBarcan.model).IsModel ∧ ¬ (Classicism.Meta.Intensional.ContingentBarcan.model).HoldsAx Classicism.P.NecBarcan.schemaIn

/-- `full-idempotent-monoid`: ND fails. -/
def Models.full_idempotent_monoid.distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).HoldsAx Classicism.P.NecessityOfDistinctness.schemaIn

/-- `full-idempotent-monoid`: □ND fails. -/
def Models.full_idempotent_monoid.necessary_distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).HoldsAx Classicism.P.NecNecessityOfDistinctness.schemaIn

/-- `full-idempotent-monoid`: ND (type t) fails. -/
def Models.full_idempotent_monoid.distinctness_necessary_t : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).HoldsAx Classicism.P.NecessityOfDistinctnessT.schemaIn

/-- `full-idempotent-monoid`: □ND (type t) fails. -/
def Models.full_idempotent_monoid.necessary_distinctness_necessary_t : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).HoldsAx Classicism.P.NecNecessityOfDistinctnessT.schemaIn

/-- `full-idempotent-monoid`: BF fails. -/
def Models.full_idempotent_monoid.barcan_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).HoldsAx Classicism.P.Barcan.schemaIn

/-- `full-idempotent-monoid`: □BF fails. -/
def Models.full_idempotent_monoid.necessary_barcan_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).HoldsAx Classicism.P.NecBarcan.schemaIn

/-- `full-idempotent-monoid`: BF (type t) fails. -/
def Models.full_idempotent_monoid.barcan_t : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).HoldsAx Classicism.P.BarcanT.schemaIn

/-- `full-idempotent-monoid`: □BF (type t) fails. -/
def Models.full_idempotent_monoid.necessary_barcan_t : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).HoldsAx Classicism.P.NecBarcanT.schemaIn

/-- `full-idempotent-monoid`: Fregean Axiom fails. -/
def Models.full_idempotent_monoid.fregean_axiom : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).HoldsAx Classicism.P.FregeanAxiom.schemaIn

/-- `full-idempotent-monoid`: □Fregean Axiom fails. -/
def Models.full_idempotent_monoid.necessary_fregean_axiom : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).HoldsAx Classicism.P.NecFregeanAxiom.schemaIn

/-- `full-involution-group`: ND holds. -/
def Models.full_involution_group.distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).IsModel ∧ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).HoldsAx Classicism.P.NecessityOfDistinctness.schemaIn

/-- `full-involution-group`: □ND holds. -/
def Models.full_involution_group.necessary_distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).IsModel ∧ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).HoldsAx Classicism.P.NecNecessityOfDistinctness.schemaIn

/-- `full-involution-group`: ND (type t) holds. -/
def Models.full_involution_group.distinctness_necessary_t : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).IsModel ∧ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).HoldsAx Classicism.P.NecessityOfDistinctnessT.schemaIn

/-- `full-involution-group`: □ND (type t) holds. -/
def Models.full_involution_group.necessary_distinctness_necessary_t : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).IsModel ∧ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).HoldsAx Classicism.P.NecNecessityOfDistinctnessT.schemaIn

/-- `full-involution-group`: BF holds. -/
def Models.full_involution_group.barcan_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).IsModel ∧ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).HoldsAx Classicism.P.Barcan.schemaIn

/-- `full-involution-group`: □BF holds. -/
def Models.full_involution_group.necessary_barcan_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).IsModel ∧ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).HoldsAx Classicism.P.NecBarcan.schemaIn

/-- `full-involution-group`: BF (type t) holds. -/
def Models.full_involution_group.barcan_t : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).IsModel ∧ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).HoldsAx Classicism.P.BarcanT.schemaIn

/-- `full-involution-group`: □BF (type t) holds. -/
def Models.full_involution_group.necessary_barcan_t : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).IsModel ∧ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).HoldsAx Classicism.P.NecBarcanT.schemaIn

/-- `full-involution-group`: Fregean Axiom fails. -/
def Models.full_involution_group.fregean_axiom : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).HoldsAx Classicism.P.FregeanAxiom.schemaIn

/-- `full-involution-group`: □Fregean Axiom fails. -/
def Models.full_involution_group.necessary_fregean_axiom : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).HoldsAx Classicism.P.NecFregeanAxiom.schemaIn

/-- `full-permutation-group-infinite-set`: ND holds. -/
def Models.full_permutation_group_infinite_set.distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).IsModel ∧ (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).HoldsAx Classicism.P.NecessityOfDistinctness.schemaIn

/-- `full-permutation-group-infinite-set`: □ND holds. -/
def Models.full_permutation_group_infinite_set.necessary_distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).IsModel ∧ (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).HoldsAx Classicism.P.NecNecessityOfDistinctness.schemaIn

/-- `full-permutation-group-infinite-set`: ND (type t) holds. -/
def Models.full_permutation_group_infinite_set.distinctness_necessary_t : Prop :=
  (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).IsModel ∧ (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).HoldsAx Classicism.P.NecessityOfDistinctnessT.schemaIn

/-- `full-permutation-group-infinite-set`: □ND (type t) holds. -/
def Models.full_permutation_group_infinite_set.necessary_distinctness_necessary_t : Prop :=
  (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).IsModel ∧ (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).HoldsAx Classicism.P.NecNecessityOfDistinctnessT.schemaIn

/-- `full-permutation-group-infinite-set`: BF holds. -/
def Models.full_permutation_group_infinite_set.barcan_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).IsModel ∧ (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).HoldsAx Classicism.P.Barcan.schemaIn

/-- `full-permutation-group-infinite-set`: □BF holds. -/
def Models.full_permutation_group_infinite_set.necessary_barcan_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).IsModel ∧ (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).HoldsAx Classicism.P.NecBarcan.schemaIn

/-- `full-permutation-group-infinite-set`: BF (type t) holds. -/
def Models.full_permutation_group_infinite_set.barcan_t : Prop :=
  (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).IsModel ∧ (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).HoldsAx Classicism.P.BarcanT.schemaIn

/-- `full-permutation-group-infinite-set`: □BF (type t) holds. -/
def Models.full_permutation_group_infinite_set.necessary_barcan_t : Prop :=
  (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).IsModel ∧ (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).HoldsAx Classicism.P.NecBarcanT.schemaIn

/-- `full-permutation-group-infinite-set`: Fregean Axiom fails. -/
def Models.full_permutation_group_infinite_set.fregean_axiom : Prop :=
  (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).HoldsAx Classicism.P.FregeanAxiom.schemaIn

/-- `full-permutation-group-infinite-set`: □Fregean Axiom fails. -/
def Models.full_permutation_group_infinite_set.necessary_fregean_axiom : Prop :=
  (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).HoldsAx Classicism.P.NecFregeanAxiom.schemaIn

/-- `full-surjection-monoid`: ND fails. -/
def Models.full_surjection_monoid.distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).HoldsAx Classicism.P.NecessityOfDistinctness.schemaIn

/-- `full-surjection-monoid`: □ND fails. -/
def Models.full_surjection_monoid.necessary_distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).HoldsAx Classicism.P.NecNecessityOfDistinctness.schemaIn

/-- `full-surjection-monoid`: ND (type t) fails. -/
def Models.full_surjection_monoid.distinctness_necessary_t : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).HoldsAx Classicism.P.NecessityOfDistinctnessT.schemaIn

/-- `full-surjection-monoid`: □ND (type t) fails. -/
def Models.full_surjection_monoid.necessary_distinctness_necessary_t : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).HoldsAx Classicism.P.NecNecessityOfDistinctnessT.schemaIn

/-- `full-surjection-monoid`: Fregean Axiom fails. -/
def Models.full_surjection_monoid.fregean_axiom : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).HoldsAx Classicism.P.FregeanAxiom.schemaIn

/-- `full-surjection-monoid`: □Fregean Axiom fails. -/
def Models.full_surjection_monoid.necessary_fregean_axiom : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).HoldsAx Classicism.P.NecFregeanAxiom.schemaIn

/-- `full-two-object-chain`: ND fails. -/
def Models.full_two_object_chain.distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.chain).IsModel ∧ ¬ (Classicism.Meta.Intensional.FullActionModels.chain).HoldsAx Classicism.P.NecessityOfDistinctness.schemaIn

/-- `full-two-object-chain`: □ND fails. -/
def Models.full_two_object_chain.necessary_distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.chain).IsModel ∧ ¬ (Classicism.Meta.Intensional.FullActionModels.chain).HoldsAx Classicism.P.NecNecessityOfDistinctness.schemaIn

/-- `full-two-object-chain`: ND (type t) fails. -/
def Models.full_two_object_chain.distinctness_necessary_t : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.chain).IsModel ∧ ¬ (Classicism.Meta.Intensional.FullActionModels.chain).HoldsAx Classicism.P.NecessityOfDistinctnessT.schemaIn

/-- `full-two-object-chain`: □ND (type t) fails. -/
def Models.full_two_object_chain.necessary_distinctness_necessary_t : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.chain).IsModel ∧ ¬ (Classicism.Meta.Intensional.FullActionModels.chain).HoldsAx Classicism.P.NecNecessityOfDistinctnessT.schemaIn

/-- `full-two-object-chain`: Fregean Axiom fails. -/
def Models.full_two_object_chain.fregean_axiom : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.chain).IsModel ∧ ¬ (Classicism.Meta.Intensional.FullActionModels.chain).HoldsAx Classicism.P.FregeanAxiom.schemaIn

/-- `full-two-object-chain`: □Fregean Axiom fails. -/
def Models.full_two_object_chain.necessary_fregean_axiom : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.chain).IsModel ∧ ¬ (Classicism.Meta.Intensional.FullActionModels.chain).HoldsAx Classicism.P.NecFregeanAxiom.schemaIn

/-- `full-two-object-retract`: ND holds. -/
def Models.full_two_object_retract.distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.retract).IsModel ∧ (Classicism.Meta.Intensional.FullActionModels.retract).HoldsAx Classicism.P.NecessityOfDistinctness.schemaIn

/-- `full-two-object-retract`: ND (type t) holds. -/
def Models.full_two_object_retract.distinctness_necessary_t : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.retract).IsModel ∧ (Classicism.Meta.Intensional.FullActionModels.retract).HoldsAx Classicism.P.NecessityOfDistinctnessT.schemaIn

/-- `full-two-object-retract`: BF fails. -/
def Models.full_two_object_retract.barcan_r : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.retract).IsModel ∧ ¬ (Classicism.Meta.Intensional.FullActionModels.retract).HoldsAx Classicism.P.Barcan.schemaIn

/-- `full-two-object-retract`: □BF fails. -/
def Models.full_two_object_retract.necessary_barcan_r : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.retract).IsModel ∧ ¬ (Classicism.Meta.Intensional.FullActionModels.retract).HoldsAx Classicism.P.NecBarcan.schemaIn

/-- `full-two-object-retract`: BF (type t) fails. -/
def Models.full_two_object_retract.barcan_t : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.retract).IsModel ∧ ¬ (Classicism.Meta.Intensional.FullActionModels.retract).HoldsAx Classicism.P.BarcanT.schemaIn

/-- `full-two-object-retract`: □BF (type t) fails. -/
def Models.full_two_object_retract.necessary_barcan_t : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.retract).IsModel ∧ ¬ (Classicism.Meta.Intensional.FullActionModels.retract).HoldsAx Classicism.P.NecBarcanT.schemaIn

/-- `full-two-object-retract`: Fregean Axiom fails. -/
def Models.full_two_object_retract.fregean_axiom : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.retract).IsModel ∧ ¬ (Classicism.Meta.Intensional.FullActionModels.retract).HoldsAx Classicism.P.FregeanAxiom.schemaIn

/-- `full-two-object-retract`: □Fregean Axiom fails. -/
def Models.full_two_object_retract.necessary_fregean_axiom : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.retract).IsModel ∧ ¬ (Classicism.Meta.Intensional.FullActionModels.retract).HoldsAx Classicism.P.NecFregeanAxiom.schemaIn

/-- `finite-support-dyadic-roundings`: Actuality holds. -/
def Models.finite_support_dyadic_roundings.actuality : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.pow2)).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.pow2)).HoldsAx Classicism.P.Actuality.schemaIn

/-- `finite-support-dyadic-roundings`: No Pure Contingency holds. -/
def Models.finite_support_dyadic_roundings.no_pure_contingency_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.pow2)).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.pow2)).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.noContingency)

/-- `finite-support-identity-or-collapse-surjections`: Actuality holds. -/
def Models.finite_support_identity_or_collapse_surjections.actuality : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj01)).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj01)).HoldsAx Classicism.P.Actuality.schemaIn

/-- `finite-support-identity-or-collapse-surjections`: Atomicity fails. -/
def Models.finite_support_identity_or_collapse_surjections.atomicity_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj01)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj01)).HoldsAx Classicism.P.Atomicity.schemaIn

/-- `finite-support-identity-or-collapse-surjections`: Atomicity (type t) fails. -/
def Models.finite_support_identity_or_collapse_surjections.atomicity_t : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj01)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj01)).HoldsAx Classicism.P.AtomicityT.schemaIn

/-- `finite-support-identity-or-collapse-surjections`: BF holds. -/
def Models.finite_support_identity_or_collapse_surjections.barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj01)).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj01)).HoldsAx Classicism.P.Barcan.schemaIn

/-- `finite-support-identity-or-collapse-surjections`: No Pure Contingency holds. -/
def Models.finite_support_identity_or_collapse_surjections.no_pure_contingency_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj01)).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj01)).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.noContingency)

/-- `finite-support-identity-or-collapse`: Actuality holds. -/
def Models.finite_support_identity_or_collapse.actuality : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono01)).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono01)).HoldsAx Classicism.P.Actuality.schemaIn

/-- `finite-support-identity-or-collapse`: Atomicity fails. -/
def Models.finite_support_identity_or_collapse.atomicity_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono01)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono01)).HoldsAx Classicism.P.Atomicity.schemaIn

/-- `finite-support-identity-or-collapse`: Atomicity (type t) fails. -/
def Models.finite_support_identity_or_collapse.atomicity_t : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono01)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono01)).HoldsAx Classicism.P.AtomicityT.schemaIn

/-- `finite-support-identity-or-collapse`: BF fails. -/
def Models.finite_support_identity_or_collapse.barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono01)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono01)).HoldsAx Classicism.P.Barcan.schemaIn

/-- `finite-support-identity-or-collapse`: No Pure Contingency holds. -/
def Models.finite_support_identity_or_collapse.no_pure_contingency_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono01)).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono01)).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.noContingency)

/-- `finite-support-monotone-maps`: BF fails. -/
def Models.finite_support_monotone_maps.barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono)).HoldsAx Classicism.P.Barcan.schemaIn

/-- `finite-support-monotone-maps`: No Pure Contingency holds. -/
def Models.finite_support_monotone_maps.no_pure_contingency_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono)).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.mono)).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.noContingency)

/-- `finite-support-monotone-surjections`: BF holds. -/
def Models.finite_support_monotone_surjections.barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj)).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj)).HoldsAx Classicism.P.Barcan.schemaIn

/-- `finite-support-monotone-surjections`: No Pure Contingency holds. -/
def Models.finite_support_monotone_surjections.no_pure_contingency_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj)).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.monoSurj)).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.noContingency)

/-- `finite-support-permutations`: No Pure Contingency holds. -/
def Models.finite_support_permutations.no_pure_contingency_r : Prop :=
  (Classicism.Meta.Intensional.Perms.model).IsModel ∧ (Classicism.Meta.Intensional.Perms.model).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.noContingency)

/-- `finite-support-truncated-shifts`: Actuality holds. -/
def Models.finite_support_truncated_shifts.actuality : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.shifts)).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.shifts)).HoldsAx Classicism.P.Actuality.schemaIn

/-- `finite-support-truncated-shifts`: BF holds. -/
def Models.finite_support_truncated_shifts.barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.shifts)).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.shifts)).HoldsAx Classicism.P.Barcan.schemaIn

/-- `finite-support-truncated-shifts`: No Pure Contingency holds. -/
def Models.finite_support_truncated_shifts.no_pure_contingency_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.shifts)).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.shifts)).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.noContingency)

/-- `finite-support-truncations`: No Pure Contingency holds. -/
def Models.finite_support_truncations.no_pure_contingency_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.truncs)).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model (Classicism.Meta.Intensional.Monoids.truncs)).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.noContingency)

/-- `full-idempotent-monoid`: Distinctness-preserving collapse holds. -/
def Models.full_idempotent_monoid.distinctness_preserving_collapse : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).IsModel ∧ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).HoldsAx Classicism.P.DistinctnessPreservingCollapse.schemaIn

/-- `full-idempotent-monoid`: Infinity Schema (type t) fails. -/
def Models.full_idempotent_monoid.infinity_t : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.infinityT)

/-- `full-idempotent-monoid`: No Pure Contingency holds. -/
def Models.full_idempotent_monoid.no_pure_contingency_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).IsModel ∧ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.noContingency)

/-- `full-idempotent-monoid`: Infinity Schema (type e) fails. -/
def Models.full_idempotent_monoid.infinity_e : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.infinityE)

/-- `full-idempotent-monoid`: Axiom of Infinity (type e) fails. -/
def Models.full_idempotent_monoid.axiom_of_infinity_e : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).HoldsAx Classicism.P.AxiomOfInfinityE.schemaIn

/-- `full-idempotent-monoid`: Possible Infinity (type e) fails. -/
def Models.full_idempotent_monoid.possible_infinity_e : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).HoldsAx Classicism.P.PossibleInfinityE.schemaIn

/-- `full-idempotent-monoid`: □Relational Choice holds. -/
def Models.full_idempotent_monoid.necessary_relational_choice_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).IsModel ∧ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).HoldsAx Classicism.P.NecRelationalChoice.schemaIn

/-- `full-idempotent-monoid`: Relational Choice holds. -/
def Models.full_idempotent_monoid.relational_choice_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).IsModel ∧ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).HoldsAx Classicism.P.RelationalChoice.schemaIn

/-- `full-idempotent-monoid`: Transversal Choice holds. -/
def Models.full_idempotent_monoid.transversal_choice_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).IsModel ∧ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Idem).HoldsAx Classicism.P.TransversalChoice.schemaIn

/-- `full-involution-group`: Infinity Schema (type t) fails. -/
def Models.full_involution_group.infinity_t : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.infinityT)

/-- `full-involution-group`: No Pure Contingency holds. -/
def Models.full_involution_group.no_pure_contingency_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).IsModel ∧ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.noContingency)

/-- `full-involution-group`: Infinity Schema (type e) fails. -/
def Models.full_involution_group.infinity_e : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.infinityE)

/-- `full-involution-group`: Axiom of Infinity (type e) fails. -/
def Models.full_involution_group.axiom_of_infinity_e : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).HoldsAx Classicism.P.AxiomOfInfinityE.schemaIn

/-- `full-involution-group`: Possible Infinity (type e) fails. -/
def Models.full_involution_group.possible_infinity_e : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).HoldsAx Classicism.P.PossibleInfinityE.schemaIn

/-- `full-involution-group`: □Relational Choice holds. -/
def Models.full_involution_group.necessary_relational_choice_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).IsModel ∧ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).HoldsAx Classicism.P.NecRelationalChoice.schemaIn

/-- `full-involution-group`: Relational Choice holds. -/
def Models.full_involution_group.relational_choice_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).IsModel ∧ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).HoldsAx Classicism.P.RelationalChoice.schemaIn

/-- `full-involution-group`: Transversal Choice holds. -/
def Models.full_involution_group.transversal_choice_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).IsModel ∧ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.Invol).HoldsAx Classicism.P.TransversalChoice.schemaIn

/-- `full-permutation-group-infinite-set`: No Pure Contingency holds. -/
def Models.full_permutation_group_infinite_set.no_pure_contingency_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).IsModel ∧ (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.noContingency)

/-- `full-permutation-group-infinite-set`: Infinity Schema (type e) fails. -/
def Models.full_permutation_group_infinite_set.infinity_e : Prop :=
  (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.infinityE)

/-- `full-permutation-group-infinite-set`: Axiom of Infinity (type e) fails. -/
def Models.full_permutation_group_infinite_set.axiom_of_infinity_e : Prop :=
  (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).HoldsAx Classicism.P.AxiomOfInfinityE.schemaIn

/-- `full-permutation-group-infinite-set`: Possible Infinity (type e) fails. -/
def Models.full_permutation_group_infinite_set.possible_infinity_e : Prop :=
  (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).HoldsAx Classicism.P.PossibleInfinityE.schemaIn

/-- `full-permutation-group-infinite-set`: □Relational Choice holds. -/
def Models.full_permutation_group_infinite_set.necessary_relational_choice_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).IsModel ∧ (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).HoldsAx Classicism.P.NecRelationalChoice.schemaIn

/-- `full-permutation-group-infinite-set`: Relational Choice holds. -/
def Models.full_permutation_group_infinite_set.relational_choice_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).IsModel ∧ (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).HoldsAx Classicism.P.RelationalChoice.schemaIn

/-- `full-permutation-group-infinite-set`: Transversal Choice holds. -/
def Models.full_permutation_group_infinite_set.transversal_choice_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).IsModel ∧ (Classicism.Meta.Intensional.MSet.model (Equiv.Perm ℕ)).HoldsAx Classicism.P.TransversalChoice.schemaIn

/-- `full-surjection-monoid`: No Pure Contingency holds. -/
def Models.full_surjection_monoid.no_pure_contingency_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).IsModel ∧ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.noContingency)

/-- `full-surjection-monoid`: Infinity Schema (type e) fails. -/
def Models.full_surjection_monoid.infinity_e : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.infinityE)

/-- `full-surjection-monoid`: Axiom of Infinity (type e) fails. -/
def Models.full_surjection_monoid.axiom_of_infinity_e : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).HoldsAx Classicism.P.AxiomOfInfinityE.schemaIn

/-- `full-surjection-monoid`: Possible Infinity (type e) fails. -/
def Models.full_surjection_monoid.possible_infinity_e : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).IsModel ∧ ¬ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).HoldsAx Classicism.P.PossibleInfinityE.schemaIn

/-- `full-surjection-monoid`: □Relational Choice holds. -/
def Models.full_surjection_monoid.necessary_relational_choice_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).IsModel ∧ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).HoldsAx Classicism.P.NecRelationalChoice.schemaIn

/-- `full-surjection-monoid`: Relational Choice holds. -/
def Models.full_surjection_monoid.relational_choice_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).IsModel ∧ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).HoldsAx Classicism.P.RelationalChoice.schemaIn

/-- `full-surjection-monoid`: Transversal Choice holds. -/
def Models.full_surjection_monoid.transversal_choice_r : Prop :=
  (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).IsModel ∧ (Classicism.Meta.Intensional.MSet.model Classicism.Meta.Intensional.FullActionModels.surj).HoldsAx Classicism.P.TransversalChoice.schemaIn

/-- `full-two-object-chain`: Distinctness-preserving collapse holds. -/
def Models.full_two_object_chain.distinctness_preserving_collapse : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.chain).IsModel ∧ (Classicism.Meta.Intensional.FullActionModels.chain).HoldsAx Classicism.P.DistinctnessPreservingCollapse.schemaIn

/-- `full-two-object-chain`: Infinity Schema (type t) fails. -/
def Models.full_two_object_chain.infinity_t : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.chain).IsModel ∧ ¬ (Classicism.Meta.Intensional.FullActionModels.chain).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.infinityT)

/-- `full-two-object-chain`: Infinity Schema (type e) fails. -/
def Models.full_two_object_chain.infinity_e : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.chain).IsModel ∧ ¬ (Classicism.Meta.Intensional.FullActionModels.chain).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.infinityE)

/-- `full-two-object-chain`: Axiom of Infinity (type e) fails. -/
def Models.full_two_object_chain.axiom_of_infinity_e : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.chain).IsModel ∧ ¬ (Classicism.Meta.Intensional.FullActionModels.chain).HoldsAx Classicism.P.AxiomOfInfinityE.schemaIn

/-- `full-two-object-chain`: Possible Infinity (type e) fails. -/
def Models.full_two_object_chain.possible_infinity_e : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.chain).IsModel ∧ ¬ (Classicism.Meta.Intensional.FullActionModels.chain).HoldsAx Classicism.P.PossibleInfinityE.schemaIn

/-- `full-two-object-chain`: □Relational Choice holds. -/
def Models.full_two_object_chain.necessary_relational_choice_r : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.chain).IsModel ∧ (Classicism.Meta.Intensional.FullActionModels.chain).HoldsAx Classicism.P.NecRelationalChoice.schemaIn

/-- `full-two-object-chain`: Relational Choice holds. -/
def Models.full_two_object_chain.relational_choice_r : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.chain).IsModel ∧ (Classicism.Meta.Intensional.FullActionModels.chain).HoldsAx Classicism.P.RelationalChoice.schemaIn

/-- `full-two-object-chain`: Transversal Choice holds. -/
def Models.full_two_object_chain.transversal_choice_r : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.chain).IsModel ∧ (Classicism.Meta.Intensional.FullActionModels.chain).HoldsAx Classicism.P.TransversalChoice.schemaIn

/-- `full-two-object-retract`: Infinity Schema (type e) fails. -/
def Models.full_two_object_retract.infinity_e : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.retract).IsModel ∧ ¬ (Classicism.Meta.Intensional.FullActionModels.retract).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.infinityE)

/-- `full-two-object-retract`: Axiom of Infinity (type e) fails. -/
def Models.full_two_object_retract.axiom_of_infinity_e : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.retract).IsModel ∧ ¬ (Classicism.Meta.Intensional.FullActionModels.retract).HoldsAx Classicism.P.AxiomOfInfinityE.schemaIn

/-- `full-two-object-retract`: Possible Infinity (type e) fails. -/
def Models.full_two_object_retract.possible_infinity_e : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.retract).IsModel ∧ ¬ (Classicism.Meta.Intensional.FullActionModels.retract).HoldsAx Classicism.P.PossibleInfinityE.schemaIn

/-- `full-two-object-retract`: □Relational Choice holds. -/
def Models.full_two_object_retract.necessary_relational_choice_r : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.retract).IsModel ∧ (Classicism.Meta.Intensional.FullActionModels.retract).HoldsAx Classicism.P.NecRelationalChoice.schemaIn

/-- `full-two-object-retract`: Relational Choice holds. -/
def Models.full_two_object_retract.relational_choice_r : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.retract).IsModel ∧ (Classicism.Meta.Intensional.FullActionModels.retract).HoldsAx Classicism.P.RelationalChoice.schemaIn

/-- `full-two-object-retract`: Transversal Choice holds. -/
def Models.full_two_object_retract.transversal_choice_r : Prop :=
  (Classicism.Meta.Intensional.FullActionModels.retract).IsModel ∧ (Classicism.Meta.Intensional.FullActionModels.retract).HoldsAx Classicism.P.TransversalChoice.schemaIn

/-- argument `barcan-d6`: BF holds in every model meeting its conditions. -/
def Arguments.barcan_d6.barcan_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} {C : Type} [CategoryTheory.SmallCategory C] (A : Classicism.Meta.Intensional.Premodel Sig C), A.IsModel → Classicism.Meta.Intensional.Premodel.D6Surjective A → (A).HoldsAx Classicism.P.Barcan.schemaIn

/-- argument `dpc-isolated-actual-world`: Distinctness-preserving collapse holds in every model meeting its conditions. -/
def Arguments.dpc_isolated_actual_world.distinctness_preserving_collapse : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} {C : Type} [CategoryTheory.SmallCategory C] (A : Classicism.Meta.Intensional.Premodel Sig C), A.IsModel → Classicism.Meta.Intensional.Premodel.ActualWorldIsolated A → (A).HoldsAx Classicism.P.DistinctnessPreservingCollapse.schemaIn

/-- argument `finitely-many-propositions`: Infinity Schema (type t) fails in every model meeting its conditions. -/
def Arguments.finitely_many_propositions.infinity_t : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} {C : Type} [CategoryTheory.SmallCategory C] (A : Classicism.Meta.Intensional.Premodel Sig C), A.IsModel → Classicism.Meta.Intensional.Premodel.Full A → Classicism.Meta.Intensional.Premodel.FinitelyManyPropositions A → ¬ (A).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.infinityT)

/-- argument `no-pure-contingency-one-object`: No Pure Contingency holds in every model meeting its conditions. -/
def Arguments.no_pure_contingency_one_object.no_pure_contingency_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} {C : Type} [CategoryTheory.SmallCategory C] (A : Classicism.Meta.Intensional.Premodel Sig C), A.IsModel → Classicism.Meta.Intensional.Premodel.OneObject A → (A).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.noContingency)

/-- argument `one-individual`: Infinity Schema (type e) fails in every model meeting its conditions. -/
def Arguments.one_individual.infinity_e : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} {C : Type} [CategoryTheory.SmallCategory C] (A : Classicism.Meta.Intensional.Premodel Sig C), A.IsModel → Classicism.Meta.Intensional.Premodel.OneIndividual A → ¬ (A).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.infinityE)

/-- argument `one-individual`: Axiom of Infinity (type e) fails in every model meeting its conditions. -/
def Arguments.one_individual.axiom_of_infinity_e : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} {C : Type} [CategoryTheory.SmallCategory C] (A : Classicism.Meta.Intensional.Premodel Sig C), A.IsModel → Classicism.Meta.Intensional.Premodel.OneIndividual A → ¬ (A).HoldsAx Classicism.P.AxiomOfInfinityE.schemaIn

/-- argument `one-individual`: Possible Infinity (type e) fails in every model meeting its conditions. -/
def Arguments.one_individual.possible_infinity_e : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} {C : Type} [CategoryTheory.SmallCategory C] (A : Classicism.Meta.Intensional.Premodel Sig C), A.IsModel → Classicism.Meta.Intensional.Premodel.OneIndividual A → ¬ (A).HoldsAx Classicism.P.PossibleInfinityE.schemaIn

/-- argument `relational-choice-full-boxed`: □Relational Choice holds in every model meeting its conditions. -/
def Arguments.relational_choice_full_boxed.necessary_relational_choice_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} {C : Type} [CategoryTheory.SmallCategory C] (A : Classicism.Meta.Intensional.Premodel Sig C), A.IsModel → Classicism.Meta.Intensional.Premodel.Full A → Classicism.Meta.Intensional.Premodel.MetatheoryChoice A → (A).HoldsAx Classicism.P.NecRelationalChoice.schemaIn

/-- argument `relational-choice-full`: Relational Choice holds in every model meeting its conditions. -/
def Arguments.relational_choice_full.relational_choice_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} {C : Type} [CategoryTheory.SmallCategory C] (A : Classicism.Meta.Intensional.Premodel Sig C), A.IsModel → Classicism.Meta.Intensional.Premodel.Full A → Classicism.Meta.Intensional.Premodel.MetatheoryChoice A → (A).HoldsAx Classicism.P.RelationalChoice.schemaIn

/-- argument `transversal-choice-extensionally-full`: Transversal Choice holds in every model meeting its conditions. -/
def Arguments.transversal_choice_extensionally_full.transversal_choice_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} {C : Type} [CategoryTheory.SmallCategory C] (A : Classicism.Meta.Intensional.Premodel Sig C), A.IsModel → Classicism.Meta.Intensional.Premodel.ExtFull A → Classicism.Meta.Intensional.Premodel.MetatheoryChoice A → (A).HoldsAx Classicism.P.TransversalChoice.schemaIn

/-- `finite-support-one-object`, argument `actual-world`: Actuality holds in every model meeting its conditions. -/
def Arguments.finite_support_one_object.actual_world.actuality : Prop :=
  ∀ (M : Type) [Monoid M] [MulAction M ℕ] [FaithfulSMul M ℕ], Classicism.Meta.Intensional.MonoidModel.ActualWorldPinned M → ((Classicism.Meta.Intensional.MonoidModel.model M)).HoldsAx Classicism.P.Actuality.schemaIn

/-- `finite-support-one-object`, argument `collapsing-atomless`: Atomicity fails in every model meeting its conditions. -/
def Arguments.finite_support_one_object.collapsing_atomless.atomicity_r : Prop :=
  ∀ (M : Type) [Monoid M] [MulAction M ℕ] [FaithfulSMul M ℕ], Classicism.Meta.Intensional.MonoidModel.CollapseUnpinned M → ¬ ((Classicism.Meta.Intensional.MonoidModel.model M)).HoldsAx Classicism.P.Atomicity.schemaIn

/-- `finite-support-one-object`, argument `collapsing-atomless`: Atomicity (type t) fails in every model meeting its conditions. -/
def Arguments.finite_support_one_object.collapsing_atomless.atomicity_t : Prop :=
  ∀ (M : Type) [Monoid M] [MulAction M ℕ] [FaithfulSMul M ℕ], Classicism.Meta.Intensional.MonoidModel.CollapseUnpinned M → ¬ ((Classicism.Meta.Intensional.MonoidModel.model M)).HoldsAx Classicism.P.AtomicityT.schemaIn

/-- `finite-support-one-object`, argument `barcan-positive`: BF fails in every model meeting its conditions. -/
def Arguments.finite_support_one_object.barcan_positive.barcan_r : Prop :=
  ∀ (M : Type) [Monoid M] [MulAction M ℕ] [FaithfulSMul M ℕ], Classicism.Meta.Intensional.MonoidModel.PositivePreserving M → ¬ ((Classicism.Meta.Intensional.MonoidModel.model M)).HoldsAx Classicism.P.Barcan.schemaIn

end Classicism.Statements
