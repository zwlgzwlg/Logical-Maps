import Classicism.Certified.Signatures
import Classicism.Semantics.IntensionalTheory
import Classicism.Models.Permutations
import Classicism.Models.Monoids
import Classicism.Models.ContingentBarcan

/-!
# Generated statements: models' verdicts

Written by `pmap lean classicism` from the YAML records. **Do not edit.**

One declaration per verdict a model record proves in Lean (its `lean.verdicts`): that
the principle holds, or fails, in the record's Lean model.
-/

namespace Classicism.Statements
open Classicism

/-- `finite-support-dyadic-roundings`: Actuality holds. -/
def Models.finite_support_dyadic_roundings.actuality : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.pow2).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.pow2).HoldsAx Classicism.P.Actuality.schemaIn

/-- `finite-support-dyadic-roundings`: Atomicity (type t) holds. -/
def Models.finite_support_dyadic_roundings.atomicity_t : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.pow2).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.pow2).HoldsAx Classicism.P.AtomicityT.schemaIn

/-- `finite-support-dyadic-roundings`: No Pure Contingency holds. -/
def Models.finite_support_dyadic_roundings.no_pure_contingency_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.pow2).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.pow2).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.noContingency)

/-- `finite-support-dyadic-roundings`: ND fails. -/
def Models.finite_support_dyadic_roundings.distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.pow2).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.pow2).HoldsAx Classicism.P.NecessityOfDistinctness.schemaIn

/-- `finite-support-dyadic-roundings`: □ND fails. -/
def Models.finite_support_dyadic_roundings.necessary_distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.pow2).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.pow2).HoldsAx Classicism.P.NecNecessityOfDistinctness.schemaIn

/-- `finite-support-dyadic-roundings`: BF fails. -/
def Models.finite_support_dyadic_roundings.barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.pow2).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.pow2).HoldsAx Classicism.P.Barcan.schemaIn

/-- `finite-support-dyadic-roundings`: □BF fails. -/
def Models.finite_support_dyadic_roundings.necessary_barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.pow2).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.pow2).HoldsAx Classicism.P.NecBarcan.schemaIn

/-- `finite-support-dyadic-roundings`: Boolean Completeness fails. -/
def Models.finite_support_dyadic_roundings.boolean_completeness_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.pow2).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.pow2).HoldsAx Classicism.P.BooleanCompleteness.schemaIn

/-- `finite-support-identity-or-collapse-surjections`: BF holds. -/
def Models.finite_support_identity_or_collapse_surjections.barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj01).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj01).HoldsAx Classicism.P.Barcan.schemaIn

/-- `finite-support-identity-or-collapse-surjections`: □BF holds. -/
def Models.finite_support_identity_or_collapse_surjections.necessary_barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj01).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj01).HoldsAx Classicism.P.NecBarcan.schemaIn

/-- `finite-support-identity-or-collapse-surjections`: Actuality holds. -/
def Models.finite_support_identity_or_collapse_surjections.actuality : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj01).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj01).HoldsAx Classicism.P.Actuality.schemaIn

/-- `finite-support-identity-or-collapse-surjections`: No Pure Contingency holds. -/
def Models.finite_support_identity_or_collapse_surjections.no_pure_contingency_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj01).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj01).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.noContingency)

/-- `finite-support-identity-or-collapse-surjections`: ND fails. -/
def Models.finite_support_identity_or_collapse_surjections.distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj01).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj01).HoldsAx Classicism.P.NecessityOfDistinctness.schemaIn

/-- `finite-support-identity-or-collapse-surjections`: □ND fails. -/
def Models.finite_support_identity_or_collapse_surjections.necessary_distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj01).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj01).HoldsAx Classicism.P.NecNecessityOfDistinctness.schemaIn

/-- `finite-support-identity-or-collapse-surjections`: Atomicity (type t) fails. -/
def Models.finite_support_identity_or_collapse_surjections.atomicity_t : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj01).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj01).HoldsAx Classicism.P.AtomicityT.schemaIn

/-- `finite-support-identity-or-collapse-surjections`: Boolean Completeness fails. -/
def Models.finite_support_identity_or_collapse_surjections.boolean_completeness_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj01).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj01).HoldsAx Classicism.P.BooleanCompleteness.schemaIn

/-- `finite-support-identity-or-collapse`: Actuality holds. -/
def Models.finite_support_identity_or_collapse.actuality : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono01).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono01).HoldsAx Classicism.P.Actuality.schemaIn

/-- `finite-support-identity-or-collapse`: No Pure Contingency holds. -/
def Models.finite_support_identity_or_collapse.no_pure_contingency_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono01).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono01).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.noContingency)

/-- `finite-support-identity-or-collapse`: ND fails. -/
def Models.finite_support_identity_or_collapse.distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono01).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono01).HoldsAx Classicism.P.NecessityOfDistinctness.schemaIn

/-- `finite-support-identity-or-collapse`: □ND fails. -/
def Models.finite_support_identity_or_collapse.necessary_distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono01).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono01).HoldsAx Classicism.P.NecNecessityOfDistinctness.schemaIn

/-- `finite-support-identity-or-collapse`: BF fails. -/
def Models.finite_support_identity_or_collapse.barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono01).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono01).HoldsAx Classicism.P.Barcan.schemaIn

/-- `finite-support-identity-or-collapse`: □BF fails. -/
def Models.finite_support_identity_or_collapse.necessary_barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono01).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono01).HoldsAx Classicism.P.NecBarcan.schemaIn

/-- `finite-support-identity-or-collapse`: Atomicity (type t) fails. -/
def Models.finite_support_identity_or_collapse.atomicity_t : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono01).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono01).HoldsAx Classicism.P.AtomicityT.schemaIn

/-- `finite-support-identity-or-collapse`: Boolean Completeness fails. -/
def Models.finite_support_identity_or_collapse.boolean_completeness_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono01).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono01).HoldsAx Classicism.P.BooleanCompleteness.schemaIn

/-- `finite-support-monotone-maps`: Atomlessness holds. -/
def Models.finite_support_monotone_maps.atomlessness : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono).HoldsAx Classicism.P.Atomlessness.schemaIn

/-- `finite-support-monotone-maps`: No Pure Contingency holds. -/
def Models.finite_support_monotone_maps.no_pure_contingency_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.noContingency)

/-- `finite-support-monotone-maps`: ND fails. -/
def Models.finite_support_monotone_maps.distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono).HoldsAx Classicism.P.NecessityOfDistinctness.schemaIn

/-- `finite-support-monotone-maps`: □ND fails. -/
def Models.finite_support_monotone_maps.necessary_distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono).HoldsAx Classicism.P.NecNecessityOfDistinctness.schemaIn

/-- `finite-support-monotone-maps`: BF fails. -/
def Models.finite_support_monotone_maps.barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono).HoldsAx Classicism.P.Barcan.schemaIn

/-- `finite-support-monotone-maps`: □BF fails. -/
def Models.finite_support_monotone_maps.necessary_barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono).HoldsAx Classicism.P.NecBarcan.schemaIn

/-- `finite-support-monotone-maps`: Actuality fails. -/
def Models.finite_support_monotone_maps.actuality : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono).HoldsAx Classicism.P.Actuality.schemaIn

/-- `finite-support-monotone-maps`: Atomicity (type t) fails. -/
def Models.finite_support_monotone_maps.atomicity_t : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono).HoldsAx Classicism.P.AtomicityT.schemaIn

/-- `finite-support-monotone-maps`: Boolean Completeness fails. -/
def Models.finite_support_monotone_maps.boolean_completeness_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.mono).HoldsAx Classicism.P.BooleanCompleteness.schemaIn

/-- `finite-support-monotone-surjections`: BF holds. -/
def Models.finite_support_monotone_surjections.barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj).HoldsAx Classicism.P.Barcan.schemaIn

/-- `finite-support-monotone-surjections`: □BF holds. -/
def Models.finite_support_monotone_surjections.necessary_barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj).HoldsAx Classicism.P.NecBarcan.schemaIn

/-- `finite-support-monotone-surjections`: Atomlessness holds. -/
def Models.finite_support_monotone_surjections.atomlessness : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj).HoldsAx Classicism.P.Atomlessness.schemaIn

/-- `finite-support-monotone-surjections`: No Pure Contingency holds. -/
def Models.finite_support_monotone_surjections.no_pure_contingency_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.noContingency)

/-- `finite-support-monotone-surjections`: ND fails. -/
def Models.finite_support_monotone_surjections.distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj).HoldsAx Classicism.P.NecessityOfDistinctness.schemaIn

/-- `finite-support-monotone-surjections`: □ND fails. -/
def Models.finite_support_monotone_surjections.necessary_distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj).HoldsAx Classicism.P.NecNecessityOfDistinctness.schemaIn

/-- `finite-support-monotone-surjections`: Actuality fails. -/
def Models.finite_support_monotone_surjections.actuality : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj).HoldsAx Classicism.P.Actuality.schemaIn

/-- `finite-support-monotone-surjections`: Atomicity (type t) fails. -/
def Models.finite_support_monotone_surjections.atomicity_t : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj).HoldsAx Classicism.P.AtomicityT.schemaIn

/-- `finite-support-monotone-surjections`: Boolean Completeness fails. -/
def Models.finite_support_monotone_surjections.boolean_completeness_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.monoSurj).HoldsAx Classicism.P.BooleanCompleteness.schemaIn

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

/-- `finite-support-permutations`: No Pure Contingency holds. -/
def Models.finite_support_permutations.no_pure_contingency_r : Prop :=
  (Classicism.Meta.Intensional.Perms.model).IsModel ∧ (Classicism.Meta.Intensional.Perms.model).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.noContingency)

/-- `finite-support-permutations`: Actuality fails. -/
def Models.finite_support_permutations.actuality : Prop :=
  (Classicism.Meta.Intensional.Perms.model).IsModel ∧ ¬ (Classicism.Meta.Intensional.Perms.model).HoldsAx Classicism.P.Actuality.schemaIn

/-- `finite-support-permutations`: Atomicity (type t) fails. -/
def Models.finite_support_permutations.atomicity_t : Prop :=
  (Classicism.Meta.Intensional.Perms.model).IsModel ∧ ¬ (Classicism.Meta.Intensional.Perms.model).HoldsAx Classicism.P.AtomicityT.schemaIn

/-- `finite-support-permutations`: Boolean Completeness fails. -/
def Models.finite_support_permutations.boolean_completeness_r : Prop :=
  (Classicism.Meta.Intensional.Perms.model).IsModel ∧ ¬ (Classicism.Meta.Intensional.Perms.model).HoldsAx Classicism.P.BooleanCompleteness.schemaIn

/-- `finite-support-truncated-shifts`: BF holds. -/
def Models.finite_support_truncated_shifts.barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.shifts).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.shifts).HoldsAx Classicism.P.Barcan.schemaIn

/-- `finite-support-truncated-shifts`: □BF holds. -/
def Models.finite_support_truncated_shifts.necessary_barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.shifts).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.shifts).HoldsAx Classicism.P.NecBarcan.schemaIn

/-- `finite-support-truncated-shifts`: Actuality holds. -/
def Models.finite_support_truncated_shifts.actuality : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.shifts).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.shifts).HoldsAx Classicism.P.Actuality.schemaIn

/-- `finite-support-truncated-shifts`: Atomicity (type t) holds. -/
def Models.finite_support_truncated_shifts.atomicity_t : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.shifts).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.shifts).HoldsAx Classicism.P.AtomicityT.schemaIn

/-- `finite-support-truncated-shifts`: No Pure Contingency holds. -/
def Models.finite_support_truncated_shifts.no_pure_contingency_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.shifts).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.shifts).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.noContingency)

/-- `finite-support-truncated-shifts`: ND fails. -/
def Models.finite_support_truncated_shifts.distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.shifts).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.shifts).HoldsAx Classicism.P.NecessityOfDistinctness.schemaIn

/-- `finite-support-truncated-shifts`: □ND fails. -/
def Models.finite_support_truncated_shifts.necessary_distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.shifts).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.shifts).HoldsAx Classicism.P.NecNecessityOfDistinctness.schemaIn

/-- `finite-support-truncated-shifts`: Boolean Completeness fails. -/
def Models.finite_support_truncated_shifts.boolean_completeness_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.shifts).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.shifts).HoldsAx Classicism.P.BooleanCompleteness.schemaIn

/-- `finite-support-truncations`: Atomicity (type t) holds. -/
def Models.finite_support_truncations.atomicity_t : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.truncs).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.truncs).HoldsAx Classicism.P.AtomicityT.schemaIn

/-- `finite-support-truncations`: No Pure Contingency holds. -/
def Models.finite_support_truncations.no_pure_contingency_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.truncs).IsModel ∧ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.truncs).HoldsAx (Classicism.Meta.AxiomSet.pureVersion Classicism.Meta.AxiomSet.noContingency)

/-- `finite-support-truncations`: ND fails. -/
def Models.finite_support_truncations.distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.truncs).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.truncs).HoldsAx Classicism.P.NecessityOfDistinctness.schemaIn

/-- `finite-support-truncations`: □ND fails. -/
def Models.finite_support_truncations.necessary_distinctness_necessary_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.truncs).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.truncs).HoldsAx Classicism.P.NecNecessityOfDistinctness.schemaIn

/-- `finite-support-truncations`: BF fails. -/
def Models.finite_support_truncations.barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.truncs).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.truncs).HoldsAx Classicism.P.Barcan.schemaIn

/-- `finite-support-truncations`: □BF fails. -/
def Models.finite_support_truncations.necessary_barcan_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.truncs).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.truncs).HoldsAx Classicism.P.NecBarcan.schemaIn

/-- `finite-support-truncations`: Actuality fails. -/
def Models.finite_support_truncations.actuality : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.truncs).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.truncs).HoldsAx Classicism.P.Actuality.schemaIn

/-- `finite-support-truncations`: Boolean Completeness fails. -/
def Models.finite_support_truncations.boolean_completeness_r : Prop :=
  (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.truncs).IsModel ∧ ¬ (Classicism.Meta.Intensional.MonoidModel.model Classicism.Meta.Intensional.Monoids.truncs).HoldsAx Classicism.P.BooleanCompleteness.schemaIn

/-- `finite-support-two-object-all-maps`: BF holds. -/
def Models.finite_support_two_object_all_maps.barcan_r : Prop :=
  (Classicism.Meta.Intensional.ContingentBarcan.model).IsModel ∧ (Classicism.Meta.Intensional.ContingentBarcan.model).HoldsAx Classicism.P.Barcan.schemaIn

/-- `finite-support-two-object-all-maps`: □BF fails. -/
def Models.finite_support_two_object_all_maps.necessary_barcan_r : Prop :=
  (Classicism.Meta.Intensional.ContingentBarcan.model).IsModel ∧ ¬ (Classicism.Meta.Intensional.ContingentBarcan.model).HoldsAx Classicism.P.NecBarcan.schemaIn

end Classicism.Statements
