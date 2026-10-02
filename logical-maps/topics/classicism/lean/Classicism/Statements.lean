import Classicism.Certified.Schemas
import Classicism.Syntax.SentenceSchemas
import Classicism.Syntax.Pure

/-!
# Generated statements

Written by `pmap lean classicism` from the YAML records. **Do not edit.**

Each declaration below is the statement of one database record, assembled from its
premises and conclusion. A proof is supplied by inhabiting the corresponding `Prop`,
so a Lean proof cannot drift from the claim the map displays. Regenerate after any
change to a record or to a principle's `lean_def`.
-/

namespace Classicism.Statements
open Classicism

/-- Principle definition check: `actual-profile-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.ActualProfile.listSchema)

/-- Principle definition check: `actuality`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema)

/-- Principle definition check: `atomicity-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.Atomicity.schema)

/-- Principle definition check: `atomicity-t`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.AtomicityT.schema)

/-- Principle definition check: `atomlessness`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.Atomlessness.schema)

/-- Principle definition check: `barcan-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.Barcan.schema)

/-- Principle definition check: `barcan-t`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.BarcanT.schema)

/-- Principle definition check: `boolean-completeness-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.BooleanCompleteness.schema)

/-- Principle definition check: `boolean-completeness-t`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.BooleanCompletenessT.schema)

/-- Principle definition check: `broad-necessitism-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.BroadNecessitism.schema)

/-- Principle definition check: `converse-barcan-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.ConverseBarcan.schema)

/-- Principle definition check: `distinctness-necessary-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecessityOfDistinctness.schema)

/-- Principle definition check: `distinctness-necessary-t`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecessityOfDistinctnessT.schema)

/-- Principle definition check: `distinctness-preserving-collapse`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.DistinctnessPreservingCollapse.schema)

/-- Principle definition check: `distinctness-schema-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.distinctness (Classicism.Meta.AxiomSet.empty : Classicism.Meta.AxiomSet Classicism.Meta.Signature.pure)))

/-- Principle definition check: `distinctness-signature-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.distinctness Classicism.Meta.AxiomSet.empty)

/-- Principle definition check: `existence-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.Existence.schema)

/-- Principle definition check: `extensionality-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.Extensionality.schema)

/-- Principle definition check: `fregean-axiom`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.FregeanAxiom.schema)

/-- Principle definition check: `functional-choice-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.FunctionalChoice.schema)

/-- Principle definition check: `functionality-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.Functionality.schema)

/-- Principle definition check: `gallin-extensional-comprehension-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.GallinExtensionalComprehension.schema)

/-- Principle definition check: `identity-necessary-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecessityOfIdentity.schema)

/-- Principle definition check: `inextensible-comprehension-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.InextensibleComprehension.schema)

/-- Principle definition check: `intensionality-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.Intensionality.schema)

/-- Principle definition check: `modal-b`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.ModalB.schema)

/-- Principle definition check: `modal-five`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.ModalFive.schema)

/-- Principle definition check: `modal-four`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.ModalFour.schema)

/-- Principle definition check: `modal-k`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.ModalK.schema)

/-- Principle definition check: `modal-t`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.ModalT.schema)

/-- Principle definition check: `modalized-fregean`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.ModalizedFregean.schema)

/-- Principle definition check: `modalized-functionality-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.ModalizedFunctionality.schema)

/-- Principle definition check: `modalized-plenitude-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.ModalizedPlenitude.schema)

/-- Principle definition check: `necessary-actuality`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecActuality.schema)

/-- Principle definition check: `necessary-atomicity-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecAtomicity.schema)

/-- Principle definition check: `necessary-barcan-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBarcan.schema)

/-- Principle definition check: `necessary-barcan-t`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBarcanT.schema)

/-- Principle definition check: `necessary-boolean-completeness-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBooleanCompleteness.schema)

/-- Principle definition check: `necessary-distinctness-necessary-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema)

/-- Principle definition check: `necessary-distinctness-necessary-t`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctnessT.schema)

/-- Principle definition check: `necessary-extensionality-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecExtensionality.schema)

/-- Principle definition check: `necessary-fregean-axiom`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecFregeanAxiom.schema)

/-- Principle definition check: `necessary-functional-choice-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecFunctionalChoice.schema)

/-- Principle definition check: `necessary-functionality-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecFunctionality.schema)

/-- Principle definition check: `necessary-gallin-extensional-comprehension-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecGallinExtensionalComprehension.schema)

/-- Principle definition check: `necessary-modal-b`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecModalB.schema)

/-- Principle definition check: `necessary-modal-five`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecModalFive.schema)

/-- Principle definition check: `necessary-plenitude-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecPlenitude.schema)

/-- Principle definition check: `necessary-relational-choice-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecRelationalChoice.schema)

/-- Principle definition check: `necessary-rigid-comprehension-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecRigidComprehension.schema)

/-- Principle definition check: `necessary-strong-leibniz-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecStrongLeibniz.schema)

/-- Principle definition check: `necessary-strong-leibniz-t`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecStrongLeibnizT.schema)

/-- Principle definition check: `necessary-tractarianism-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecTractarianism.schema)

/-- Principle definition check: `necessary-transversal-choice-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecTransversalChoice.schema)

/-- Principle definition check: `necessary-transversal-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecTransversal.schema)

/-- Principle definition check: `necessary-vicinity`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecVicinity.schema)

/-- Principle definition check: `necessary-weakly-inextensible-comprehension-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecWeaklyInextensibleComprehension.schema)

/-- Principle definition check: `no-contingency-signature-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.noContingency _)

/-- Principle definition check: `no-pure-contingency-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure))

/-- Principle definition check: `persistent-comprehension-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.PersistentComprehension.schema)

/-- Principle definition check: `plenitude-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.Plenitude.schema)

/-- Principle definition check: `possibility-schema-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.possibility (Classicism.Meta.AxiomSet.empty : Classicism.Meta.AxiomSet Classicism.Meta.Signature.pure)))

/-- Principle definition check: `possibility-signature-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.possibility Classicism.Meta.AxiomSet.empty)

/-- Principle definition check: `pure-b-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.pureB Classicism.Meta.Signature.pure))

/-- Principle definition check: `relational-choice-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.RelationalChoice.schema)

/-- Principle definition check: `rigid-comprehension-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.RigidComprehension.schema)

/-- Principle definition check: `signature-b-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.signatureB _)

/-- Principle definition check: `strong-leibniz-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.StrongLeibniz.schema)

/-- Principle definition check: `strong-leibniz-t`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.StrongLeibnizT.schema)

/-- Principle definition check: `tractarianism-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.Tractarianism.schema)

/-- Principle definition check: `transversal-choice-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.TransversalChoice.schema)

/-- Principle definition check: `transversal-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.Transversal.schema)

/-- Principle definition check: `very-weak-rigid-comprehension-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.VeryWeakRigidComprehension.schema)

/-- Principle definition check: `vicinity`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.Vicinity.schema)

/-- Principle definition check: `weak-rigid-comprehension-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.WeakRigidComprehension.schema)

/-- Principle definition check: `weakly-inextensible-comprehension-r`. -/
example {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
  (Classicism.Meta.AxiomSet.ofPure Classicism.P.WeaklyInextensibleComprehension.schema)

/-- `actual-profile-r-implies-actuality`

Actual Profile ⇒ Actuality -/
def actual_profile_r_implies_actuality : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.ActualProfile.listSchema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema)

/-- `actuality-and-bf-imply-inextensible-comprehension`

Actuality ∧ BF ⇒ Inextensible Comprehension -/
def actuality_and_bf_imply_inextensible_comprehension : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Barcan.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.InextensibleComprehension.schema)

/-- `actuality-and-distinctness-preserving-collapse-imply-inextensible-comprehension`

Actuality ∧ Distinctness-preserving collapse ⇒ Inextensible Comprehension -/
def actuality_and_distinctness_preserving_collapse_imply_inextensible_comprehension : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.DistinctnessPreservingCollapse.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.InextensibleComprehension.schema)

/-- `actuality-implies-actual-profile-r`

Actuality ⇒ Actual Profile -/
def actuality_implies_actual_profile_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.ActualProfile.listSchema)

/-- `actuality-implies-persistent-comprehension-r`

Actuality ⇒ Persistent Comprehension -/
def actuality_implies_persistent_comprehension_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.PersistentComprehension.schema)

/-- `actuality-implies-transversal`

Actuality ⇒ Transversal -/
def actuality_implies_transversal : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Transversal.schema)

/-- `actuality-implies-vicinity`

Actuality ⇒ Vicinity -/
def actuality_implies_vicinity : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Vicinity.schema)

/-- `actuality-implies-weakly-inextensible-comprehension-r`

Actuality ⇒ Weakly Inextensible Comprehension -/
def actuality_implies_weakly_inextensible_comprehension_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.WeaklyInextensibleComprehension.schema)

/-- `actuality-incompatible-with-atomlessness`

Actuality ∧ Atomlessness ⇒ ⊥ -/
def actuality_incompatible_with_atomlessness : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Atomlessness.schema) →
    False

/-- `atomicity-and-bf-imply-necessary-actuality`

Atomicity ∧ BF ⇒ □Actuality -/
def atomicity_and_bf_imply_necessary_actuality : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Atomicity.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Barcan.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecActuality.schema)

/-- `atomicity-and-bf-imply-strong-leibniz`

Atomicity ∧ BF ⇒ Strong Leibniz Biconditionals -/
def atomicity_and_bf_imply_strong_leibniz : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Atomicity.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Barcan.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.StrongLeibniz.schema)

/-- `atomicity-r-implies-atomicity-t`

Atomicity ⇒ Atomicity (type t) -/
def atomicity_r_implies_atomicity_t : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Atomicity.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.AtomicityT.schema)

/-- `atomicity-t-and-bf-imply-atomicity`

Atomicity (type t) ∧ BF ⇒ Atomicity -/
def atomicity_t_and_bf_imply_atomicity : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.AtomicityT.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Barcan.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Atomicity.schema)

/-- `atomicity-t-and-bf-imply-necessary-actuality`

Atomicity (type t) ∧ BF ⇒ □Actuality -/
def atomicity_t_and_bf_imply_necessary_actuality : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.AtomicityT.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Barcan.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecActuality.schema)

/-- `atomicity-t-and-bf-t-imply-strong-leibniz-t`

Atomicity (type t) ∧ BF (type t) ⇒ Strong Leibniz Biconditionals (type t) -/
def atomicity_t_and_bf_t_imply_strong_leibniz_t : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.AtomicityT.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.BarcanT.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.StrongLeibnizT.schema)

/-- `atomicity-t-incompatible-with-atomlessness`

Atomicity (type t) ∧ Atomlessness ⇒ ⊥ -/
def atomicity_t_incompatible_with_atomlessness : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.AtomicityT.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Atomlessness.schema) →
    False

/-- `barcan-r-implies-barcan-t`

BF ⇒ BF (type t) -/
def barcan_r_implies_barcan_t : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Barcan.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.BarcanT.schema)

/-- `barcan-r-implies-functionality-r`

BF ⇒ Functionality -/
def barcan_r_implies_functionality_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Barcan.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Functionality.schema)

/-- `boolean-completeness-r-implies-boolean-completeness-t`

Boolean Completeness ⇒ Boolean Completeness (type t) -/
def boolean_completeness_r_implies_boolean_completeness_t : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.BooleanCompleteness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.BooleanCompletenessT.schema)

/-- `boolean-completeness-r-implies-weakly-inextensible-comprehension-r`

Boolean Completeness ⇒ Weakly Inextensible Comprehension -/
def boolean_completeness_r_implies_weakly_inextensible_comprehension_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.BooleanCompleteness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.WeaklyInextensibleComprehension.schema)

/-- `c5-and-actuality-imply-completeness`

□ND ∧ Actuality ⇒ Boolean Completeness -/
def c5_and_actuality_imply_completeness : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.BooleanCompleteness.schema)

/-- `c5-and-actuality-imply-rigid-comprehension`

□ND ∧ Actuality ⇒ Rigid Comprehension -/
def c5_and_actuality_imply_rigid_comprehension : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RigidComprehension.schema)

/-- `c5-and-atomicity-imply-necessary-atomicity`

□ND ∧ Atomicity ⇒ □Atomicity -/
def c5_and_atomicity_imply_necessary_atomicity : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Atomicity.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecAtomicity.schema)

/-- `c5-and-atomicity-imply-necessary-completeness`

□ND ∧ Atomicity ⇒ □Boolean Completeness -/
def c5_and_atomicity_imply_necessary_completeness : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Atomicity.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBooleanCompleteness.schema)

/-- `c5-and-atomicity-imply-necessary-plenitude`

□ND ∧ Atomicity ⇒ □Plenitude -/
def c5_and_atomicity_imply_necessary_plenitude : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Atomicity.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecPlenitude.schema)

/-- `c5-and-atomicity-imply-necessary-rigid-comprehension`

□ND ∧ Atomicity ⇒ □Rigid Comprehension -/
def c5_and_atomicity_imply_necessary_rigid_comprehension : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Atomicity.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecRigidComprehension.schema)

/-- `c5-and-atomicity-imply-no-pure-contingency`

□ND ∧ Atomicity ⇒ No Pure Contingency -/
def c5_and_atomicity_imply_no_pure_contingency : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Atomicity.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure))

/-- `c5-and-atomicity-t-imply-no-pure-contingency`

□ND ∧ Atomicity (type t) ⇒ No Pure Contingency -/
def c5_and_atomicity_t_imply_no_pure_contingency : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.AtomicityT.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure))

/-- `c5-and-completeness-imply-actuality`

□ND ∧ Boolean Completeness ⇒ Actuality -/
def c5_and_completeness_imply_actuality : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.BooleanCompleteness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema)

/-- `c5-and-completeness-imply-plenitude`

□ND ∧ Boolean Completeness ⇒ Plenitude -/
def c5_and_completeness_imply_plenitude : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.BooleanCompleteness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Plenitude.schema)

/-- `c5-and-necessary-actuality-imply-atomicity`

□ND ∧ □Actuality ⇒ Atomicity -/
def c5_and_necessary_actuality_imply_atomicity : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecActuality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Atomicity.schema)

/-- `c5-and-necessary-completeness-imply-atomicity`

□ND ∧ □Boolean Completeness ⇒ Atomicity -/
def c5_and_necessary_completeness_imply_atomicity : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBooleanCompleteness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Atomicity.schema)

/-- `c5-and-necessary-rigid-comprehension-imply-necessary-gallin-comprehension`

□ND ∧ □Rigid Comprehension ⇒ □Gallin Extensional Comprehension -/
def c5_and_necessary_rigid_comprehension_imply_necessary_gallin_comprehension : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecRigidComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecGallinExtensionalComprehension.schema)

/-- `c5-and-persistent-comprehension-imply-gallin`

□ND ∧ Persistent Comprehension ⇒ Gallin Extensional Comprehension -/
def c5_and_persistent_comprehension_imply_gallin : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.PersistentComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.GallinExtensionalComprehension.schema)

/-- `classicism-implies-broad-necessitism-r`

⊤ ⇒ Broad Necessitism -/
def classicism_implies_broad_necessitism_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.BroadNecessitism.schema)

/-- `classicism-implies-converse-barcan-r`

⊤ ⇒ CBF -/
def classicism_implies_converse_barcan_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.ConverseBarcan.schema)

/-- `classicism-implies-existence-r`

⊤ ⇒ Existence -/
def classicism_implies_existence_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Existence.schema)

/-- `classicism-implies-identity-necessary-r`

⊤ ⇒ NI -/
def classicism_implies_identity_necessary_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecessityOfIdentity.schema)

/-- `classicism-implies-intensionality-r`

⊤ ⇒ Intensionality -/
def classicism_implies_intensionality_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Intensionality.schema)

/-- `classicism-implies-modal-four`

⊤ ⇒ 4 -/
def classicism_implies_modal_four : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.ModalFour.schema)

/-- `classicism-implies-modal-k`

⊤ ⇒ K -/
def classicism_implies_modal_k : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.ModalK.schema)

/-- `classicism-implies-modal-t`

⊤ ⇒ T -/
def classicism_implies_modal_t : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.ModalT.schema)

/-- `classicism-implies-modalized-fregean`

⊤ ⇒ Modalized Fregean Axiom -/
def classicism_implies_modalized_fregean : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.ModalizedFregean.schema)

/-- `classicism-implies-modalized-functionality-r`

⊤ ⇒ Modalized Functionality -/
def classicism_implies_modalized_functionality_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.ModalizedFunctionality.schema)

/-- `classicism-implies-modalized-plenitude-r`

⊤ ⇒ Modalized Plenitude -/
def classicism_implies_modalized_plenitude_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.ModalizedPlenitude.schema)

/-- `completeness-and-actuality-imply-weak-rigid-comprehension`

Boolean Completeness ∧ Actuality ⇒ Weak Rigid Comprehension -/
def completeness_and_actuality_imply_weak_rigid_comprehension : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.BooleanCompleteness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.WeakRigidComprehension.schema)

/-- `distinctness-necessary-r-implies-distinctness-necessary-t`

ND ⇒ ND (type t) -/
def distinctness_necessary_r_implies_distinctness_necessary_t : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecessityOfDistinctness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecessityOfDistinctnessT.schema)

/-- `distinctness-necessary-t-implies-modal-five`

ND (type t) ⇒ 5 -/
def distinctness_necessary_t_implies_modal_five : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecessityOfDistinctnessT.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.ModalFive.schema)

/-- `distinctness-necessary-t-implies-vicinity`

ND (type t) ⇒ Vicinity -/
def distinctness_necessary_t_implies_vicinity : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecessityOfDistinctnessT.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Vicinity.schema)

/-- `distinctness-preserving-collapse-and-nd-imply-fregean-axiom`

Distinctness-preserving collapse ∧ ND ⇒ Fregean Axiom -/
def distinctness_preserving_collapse_and_nd_imply_fregean_axiom : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.DistinctnessPreservingCollapse.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecessityOfDistinctness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.FregeanAxiom.schema)

/-- `distinctness-schema-r-implies-possibility-schema-r`

Distinctness Maximalism (pure) ⇒ Possibility Maximalism (pure) -/
def distinctness_schema_r_implies_possibility_schema_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.distinctness (Classicism.Meta.AxiomSet.empty : Classicism.Meta.AxiomSet Classicism.Meta.Signature.pure))) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.possibility (Classicism.Meta.AxiomSet.empty : Classicism.Meta.AxiomSet Classicism.Meta.Signature.pure)))

/-- `distinctness-signature-r-implies-distinctness-schema-r`

Distinctness Maximalism (signature Σ) ⇒ Distinctness Maximalism (pure) -/
def distinctness_signature_r_implies_distinctness_schema_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.distinctness Classicism.Meta.AxiomSet.empty) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.distinctness (Classicism.Meta.AxiomSet.empty : Classicism.Meta.AxiomSet Classicism.Meta.Signature.pure)))

/-- `distinctness-signature-r-implies-possibility-signature-r`

Distinctness Maximalism (signature Σ) ⇒ Possibility Maximalism (signature Σ) -/
def distinctness_signature_r_implies_possibility_signature_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.distinctness Classicism.Meta.AxiomSet.empty) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.possibility Classicism.Meta.AxiomSet.empty)

/-- `extensionality-r-implies-actuality`

Extensionality ⇒ Actuality -/
def extensionality_r_implies_actuality : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Extensionality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema)

/-- `extensionality-r-implies-atomicity-r`

Extensionality ⇒ Atomicity -/
def extensionality_r_implies_atomicity_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Extensionality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Atomicity.schema)

/-- `extensionality-r-implies-boolean-completeness-r`

Extensionality ⇒ Boolean Completeness -/
def extensionality_r_implies_boolean_completeness_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Extensionality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.BooleanCompleteness.schema)

/-- `extensionality-r-implies-fregean-axiom`

Extensionality ⇒ Fregean Axiom -/
def extensionality_r_implies_fregean_axiom : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Extensionality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.FregeanAxiom.schema)

/-- `extensionality-r-implies-functionality-r`

Extensionality ⇒ Functionality -/
def extensionality_r_implies_functionality_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Extensionality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Functionality.schema)

/-- `extensionality-r-implies-necessary-extensionality-r`

Extensionality ⇒ □Extensionality -/
def extensionality_r_implies_necessary_extensionality_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Extensionality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecExtensionality.schema)

/-- `extensionality-r-implies-plenitude-r`

Extensionality ⇒ Plenitude -/
def extensionality_r_implies_plenitude_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Extensionality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Plenitude.schema)

/-- `extensionality-r-implies-rigid-comprehension-r`

Extensionality ⇒ Rigid Comprehension -/
def extensionality_r_implies_rigid_comprehension_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Extensionality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RigidComprehension.schema)

/-- `fregean-axiom-implies-distinctness-preserving-collapse`

Fregean Axiom ⇒ Distinctness-preserving collapse -/
def fregean_axiom_implies_distinctness_preserving_collapse : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.FregeanAxiom.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.DistinctnessPreservingCollapse.schema)

/-- `fregean-axiom-implies-extensionality-r`

Fregean Axiom ⇒ Extensionality -/
def fregean_axiom_implies_extensionality_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.FregeanAxiom.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Extensionality.schema)

/-- `fregean-axiom-implies-necessary-distinctness-necessary-r`

Fregean Axiom ⇒ □ND -/
def fregean_axiom_implies_necessary_distinctness_necessary_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.FregeanAxiom.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema)

/-- `fregean-axiom-implies-necessary-fregean-axiom`

Fregean Axiom ⇒ □Fregean Axiom -/
def fregean_axiom_implies_necessary_fregean_axiom : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.FregeanAxiom.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecFregeanAxiom.schema)

/-- `fregean-axiom-implies-no-contingency-signature-r`

Fregean Axiom ⇒ No Contingency (signature Σ) -/
def fregean_axiom_implies_no_contingency_signature_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.FregeanAxiom.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.noContingency _)

/-- `fregean-axiom-implies-no-pure-contingency-r`

Fregean Axiom ⇒ No Pure Contingency -/
def fregean_axiom_implies_no_pure_contingency_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.FregeanAxiom.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure))

/-- `functional-choice-r-implies-plenitude-r`

Functional Choice ⇒ Plenitude -/
def functional_choice_r_implies_plenitude_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.FunctionalChoice.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Plenitude.schema)

/-- `functional-choice-r-implies-relational-choice-r`

Functional Choice ⇒ Relational Choice -/
def functional_choice_r_implies_relational_choice_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.FunctionalChoice.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RelationalChoice.schema)

/-- `functionality-r-implies-tractarianism-r`

Functionality ⇒ Tractarianism -/
def functionality_r_implies_tractarianism_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Functionality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Tractarianism.schema)

/-- `gallin-comprehension-and-bf-imply-rigid-comprehension`

Gallin Extensional Comprehension ∧ BF ⇒ Rigid Comprehension -/
def gallin_comprehension_and_bf_imply_rigid_comprehension : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.GallinExtensionalComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Barcan.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RigidComprehension.schema)

/-- `gallin-comprehension-and-bf-imply-weak-rigid-comprehension`

Gallin Extensional Comprehension ∧ BF ⇒ Weak Rigid Comprehension -/
def gallin_comprehension_and_bf_imply_weak_rigid_comprehension : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.GallinExtensionalComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Barcan.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.WeakRigidComprehension.schema)

/-- `gallin-comprehension-implies-nd`

Gallin Extensional Comprehension ⇒ ND -/
def gallin_comprehension_implies_nd : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.GallinExtensionalComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecessityOfDistinctness.schema)

/-- `inextensible-comprehension-r-implies-weakly-inextensible-comprehension-r`

Inextensible Comprehension ⇒ Weakly Inextensible Comprehension -/
def inextensible_comprehension_r_implies_weakly_inextensible_comprehension_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.InextensibleComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.WeaklyInextensibleComprehension.schema)

/-- `maximalist-distinctness-incompatible-with-nd`

Distinctness Maximalism (pure) ∧ ND ⇒ ⊥ -/
def maximalist_distinctness_incompatible_with_nd : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.distinctness (Classicism.Meta.AxiomSet.empty : Classicism.Meta.AxiomSet Classicism.Meta.Signature.pure))) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecessityOfDistinctness.schema) →
    False

/-- `maximalist-distinctness-incompatible-with-necessary-actuality`

Distinctness Maximalism (pure) ∧ □Actuality ⇒ ⊥ -/
def maximalist_distinctness_incompatible_with_necessary_actuality : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.distinctness (Classicism.Meta.AxiomSet.empty : Classicism.Meta.AxiomSet Classicism.Meta.Signature.pure))) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecActuality.schema) →
    False

/-- `maximalist-distinctness-incompatible-with-necessary-atomicity-r`

Distinctness Maximalism (pure) ∧ □Atomicity ⇒ ⊥ -/
def maximalist_distinctness_incompatible_with_necessary_atomicity_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.distinctness (Classicism.Meta.AxiomSet.empty : Classicism.Meta.AxiomSet Classicism.Meta.Signature.pure))) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecAtomicity.schema) →
    False

/-- `maximalist-distinctness-incompatible-with-necessary-barcan-r`

Distinctness Maximalism (pure) ∧ □BF ⇒ ⊥ -/
def maximalist_distinctness_incompatible_with_necessary_barcan_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.distinctness (Classicism.Meta.AxiomSet.empty : Classicism.Meta.AxiomSet Classicism.Meta.Signature.pure))) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBarcan.schema) →
    False

/-- `maximalist-distinctness-incompatible-with-necessary-boolean-completeness-r`

Distinctness Maximalism (pure) ∧ □Boolean Completeness ⇒ ⊥ -/
def maximalist_distinctness_incompatible_with_necessary_boolean_completeness_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.distinctness (Classicism.Meta.AxiomSet.empty : Classicism.Meta.AxiomSet Classicism.Meta.Signature.pure))) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBooleanCompleteness.schema) →
    False

/-- `maximalist-distinctness-incompatible-with-necessary-functionality-r`

Distinctness Maximalism (pure) ∧ □Functionality ⇒ ⊥ -/
def maximalist_distinctness_incompatible_with_necessary_functionality_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.distinctness (Classicism.Meta.AxiomSet.empty : Classicism.Meta.AxiomSet Classicism.Meta.Signature.pure))) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecFunctionality.schema) →
    False

/-- `maximalist-distinctness-incompatible-with-necessary-rigid-comprehension-r`

Distinctness Maximalism (pure) ∧ □Rigid Comprehension ⇒ ⊥ -/
def maximalist_distinctness_incompatible_with_necessary_rigid_comprehension_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.distinctness (Classicism.Meta.AxiomSet.empty : Classicism.Meta.AxiomSet Classicism.Meta.Signature.pure))) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecRigidComprehension.schema) →
    False

/-- `maximalist-distinctness-incompatible-with-necessary-tractarianism-r`

Distinctness Maximalism (pure) ∧ □Tractarianism ⇒ ⊥ -/
def maximalist_distinctness_incompatible_with_necessary_tractarianism_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.distinctness (Classicism.Meta.AxiomSet.empty : Classicism.Meta.AxiomSet Classicism.Meta.Signature.pure))) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecTractarianism.schema) →
    False

/-- `maximalist-distinctness-incompatible-with-rigid-comprehension`

Distinctness Maximalism (pure) ∧ Rigid Comprehension ⇒ ⊥ -/
def maximalist_distinctness_incompatible_with_rigid_comprehension : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.distinctness (Classicism.Meta.AxiomSet.empty : Classicism.Meta.AxiomSet Classicism.Meta.Signature.pure))) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RigidComprehension.schema) →
    False

/-- `modal-b-implies-distinctness-necessary-r`

B ⇒ ND -/
def modal_b_implies_distinctness_necessary_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.ModalB.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecessityOfDistinctness.schema)

/-- `modal-b-implies-pure-b-r`

B ⇒ B for pure sentences -/
def modal_b_implies_pure_b_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.ModalB.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.pureB Classicism.Meta.Signature.pure))

/-- `modal-b-implies-signature-b-r`

B ⇒ B for sentences of Σ -/
def modal_b_implies_signature_b_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.ModalB.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.signatureB _)

/-- `modal-five-implies-modal-b`

5 ⇒ B -/
def modal_five_implies_modal_b : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.ModalFive.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.ModalB.schema)

/-- `nd-and-bf-imply-necessary-nd`

ND ∧ BF ⇒ □ND -/
def nd_and_bf_imply_necessary_nd : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecessityOfDistinctness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Barcan.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema)

/-- `necessary-actuality-implies-actuality`

□Actuality ⇒ Actuality -/
def necessary_actuality_implies_actuality : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecActuality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema)

/-- `necessary-actuality-implies-necessary-transversal`

□Actuality ⇒ □Transversal -/
def necessary_actuality_implies_necessary_transversal : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecActuality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecTransversal.schema)

/-- `necessary-actuality-implies-necessary-vicinity`

□Actuality ⇒ □Vicinity -/
def necessary_actuality_implies_necessary_vicinity : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecActuality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecVicinity.schema)

/-- `necessary-actuality-implies-necessary-weakly-inextensible-comprehension-r`

□Actuality ⇒ □Weakly Inextensible Comprehension -/
def necessary_actuality_implies_necessary_weakly_inextensible_comprehension_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecActuality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecWeaklyInextensibleComprehension.schema)

/-- `necessary-atomicity-and-necessary-bf-imply-necessary-strong-leibniz`

□Atomicity ∧ □BF ⇒ □Strong Leibniz Biconditionals -/
def necessary_atomicity_and_necessary_bf_imply_necessary_strong_leibniz : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecAtomicity.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBarcan.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecStrongLeibniz.schema)

/-- `necessary-atomicity-and-necessary-bf-t-imply-necessary-strong-leibniz-t`

□Atomicity ∧ □BF (type t) ⇒ □Strong Leibniz Biconditionals (type t) -/
def necessary_atomicity_and_necessary_bf_t_imply_necessary_strong_leibniz_t : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecAtomicity.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBarcanT.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecStrongLeibnizT.schema)

/-- `necessary-atomicity-completeness-bf-imply-rigid-comprehension`  (conjectured)

□Atomicity ∧ Boolean Completeness ∧ BF ⇒ Rigid Comprehension -/
def necessary_atomicity_completeness_bf_imply_rigid_comprehension : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecAtomicity.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.BooleanCompleteness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Barcan.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RigidComprehension.schema)

/-- `necessary-atomicity-r-implies-atomicity-r`

□Atomicity ⇒ Atomicity -/
def necessary_atomicity_r_implies_atomicity_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecAtomicity.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Atomicity.schema)

/-- `necessary-barcan-r-implies-barcan-r`

□BF ⇒ BF -/
def necessary_barcan_r_implies_barcan_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBarcan.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Barcan.schema)

/-- `necessary-barcan-r-implies-necessary-barcan-t`

□BF ⇒ □BF (type t) -/
def necessary_barcan_r_implies_necessary_barcan_t : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBarcan.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBarcanT.schema)

/-- `necessary-barcan-r-implies-necessary-functionality-r`

□BF ⇒ □Functionality -/
def necessary_barcan_r_implies_necessary_functionality_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBarcan.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecFunctionality.schema)

/-- `necessary-barcan-t-implies-barcan-t`

□BF (type t) ⇒ BF (type t) -/
def necessary_barcan_t_implies_barcan_t : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBarcanT.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.BarcanT.schema)

/-- `necessary-bf-and-actuality-imply-inextensible-comprehension`

□BF ∧ Actuality ⇒ Inextensible Comprehension -/
def necessary_bf_and_actuality_imply_inextensible_comprehension : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBarcan.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.InextensibleComprehension.schema)

/-- `necessary-boolean-completeness-r-implies-boolean-completeness-r`

□Boolean Completeness ⇒ Boolean Completeness -/
def necessary_boolean_completeness_r_implies_boolean_completeness_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBooleanCompleteness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.BooleanCompleteness.schema)

/-- `necessary-distinctness-necessary-r-implies-distinctness-necessary-r`

□ND ⇒ ND -/
def necessary_distinctness_necessary_r_implies_distinctness_necessary_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecessityOfDistinctness.schema)

/-- `necessary-distinctness-necessary-r-implies-necessary-barcan-r`

□ND ⇒ □BF -/
def necessary_distinctness_necessary_r_implies_necessary_barcan_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBarcan.schema)

/-- `necessary-distinctness-necessary-r-implies-necessary-distinctness-necessary-t`

□ND ⇒ □ND (type t) -/
def necessary_distinctness_necessary_r_implies_necessary_distinctness_necessary_t : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctnessT.schema)

/-- `necessary-distinctness-necessary-r-implies-necessary-modal-five`

□ND ⇒ □5 -/
def necessary_distinctness_necessary_r_implies_necessary_modal_five : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecModalFive.schema)

/-- `necessary-distinctness-necessary-t-implies-distinctness-necessary-t`

□ND (type t) ⇒ ND (type t) -/
def necessary_distinctness_necessary_t_implies_distinctness_necessary_t : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctnessT.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecessityOfDistinctnessT.schema)

/-- `necessary-distinctness-necessary-t-implies-necessary-distinctness-necessary-r`

□ND (type t) ⇒ □ND -/
def necessary_distinctness_necessary_t_implies_necessary_distinctness_necessary_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctnessT.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema)

/-- `necessary-distinctness-necessary-t-implies-necessary-vicinity`

□ND (type t) ⇒ □Vicinity -/
def necessary_distinctness_necessary_t_implies_necessary_vicinity : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctnessT.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecVicinity.schema)

/-- `necessary-extensionality-r-implies-extensionality-r`

□Extensionality ⇒ Extensionality -/
def necessary_extensionality_r_implies_extensionality_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecExtensionality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Extensionality.schema)

/-- `necessary-fregean-axiom-implies-fregean-axiom`

□Fregean Axiom ⇒ Fregean Axiom -/
def necessary_fregean_axiom_implies_fregean_axiom : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecFregeanAxiom.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.FregeanAxiom.schema)

/-- `necessary-functional-choice-r-implies-functional-choice-r`

□Functional Choice ⇒ Functional Choice -/
def necessary_functional_choice_r_implies_functional_choice_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecFunctionalChoice.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.FunctionalChoice.schema)

/-- `necessary-functional-choice-r-implies-necessary-plenitude-r`

□Functional Choice ⇒ □Plenitude -/
def necessary_functional_choice_r_implies_necessary_plenitude_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecFunctionalChoice.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecPlenitude.schema)

/-- `necessary-functional-choice-r-implies-necessary-relational-choice-r`

□Functional Choice ⇒ □Relational Choice -/
def necessary_functional_choice_r_implies_necessary_relational_choice_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecFunctionalChoice.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecRelationalChoice.schema)

/-- `necessary-functionality-r-implies-functionality-r`

□Functionality ⇒ Functionality -/
def necessary_functionality_r_implies_functionality_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecFunctionality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Functionality.schema)

/-- `necessary-functionality-r-implies-necessary-tractarianism-r`

□Functionality ⇒ □Tractarianism -/
def necessary_functionality_r_implies_necessary_tractarianism_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecFunctionality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecTractarianism.schema)

/-- `necessary-gallin-comprehension-implies-gallin-comprehension`

□Gallin Extensional Comprehension ⇒ Gallin Extensional Comprehension -/
def necessary_gallin_comprehension_implies_gallin_comprehension : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecGallinExtensionalComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.GallinExtensionalComprehension.schema)

/-- `necessary-gallin-comprehension-implies-necessary-nd`

□Gallin Extensional Comprehension ⇒ □ND -/
def necessary_gallin_comprehension_implies_necessary_nd : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecGallinExtensionalComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema)

/-- `necessary-gallin-comprehension-implies-necessary-rigid-comprehension`

□Gallin Extensional Comprehension ⇒ □Rigid Comprehension -/
def necessary_gallin_comprehension_implies_necessary_rigid_comprehension : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecGallinExtensionalComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecRigidComprehension.schema)

/-- `necessary-modal-b-implies-modal-b`

□B ⇒ B -/
def necessary_modal_b_implies_modal_b : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecModalB.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.ModalB.schema)

/-- `necessary-modal-b-implies-necessary-distinctness-necessary-r`

□B ⇒ □ND -/
def necessary_modal_b_implies_necessary_distinctness_necessary_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecModalB.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema)

/-- `necessary-modal-five-implies-modal-five`

□5 ⇒ 5 -/
def necessary_modal_five_implies_modal_five : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecModalFive.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.ModalFive.schema)

/-- `necessary-modal-five-implies-necessary-modal-b`

□5 ⇒ □B -/
def necessary_modal_five_implies_necessary_modal_b : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecModalFive.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecModalB.schema)

/-- `necessary-nd-implies-bf`

□ND ⇒ BF -/
def necessary_nd_implies_bf : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Barcan.schema)

/-- `necessary-plenitude-r-implies-atomicity-r`

□Plenitude ⇒ Atomicity -/
def necessary_plenitude_r_implies_atomicity_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecPlenitude.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Atomicity.schema)

/-- `necessary-plenitude-r-implies-necessary-actuality`

□Plenitude ⇒ □Actuality -/
def necessary_plenitude_r_implies_necessary_actuality : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecPlenitude.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecActuality.schema)

/-- `necessary-plenitude-r-implies-necessary-atomicity-r`

□Plenitude ⇒ □Atomicity -/
def necessary_plenitude_r_implies_necessary_atomicity_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecPlenitude.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecAtomicity.schema)

/-- `necessary-plenitude-r-implies-necessary-distinctness-necessary-r`

□Plenitude ⇒ □ND -/
def necessary_plenitude_r_implies_necessary_distinctness_necessary_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecPlenitude.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema)

/-- `necessary-plenitude-r-implies-plenitude-r`

□Plenitude ⇒ Plenitude -/
def necessary_plenitude_r_implies_plenitude_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecPlenitude.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Plenitude.schema)

/-- `necessary-relational-choice-and-necessary-plenitude-imply-necessary-functional-choice`

□Relational Choice ∧ □Plenitude ⇒ □Functional Choice -/
def necessary_relational_choice_and_necessary_plenitude_imply_necessary_functional_choice : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecRelationalChoice.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecPlenitude.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecFunctionalChoice.schema)

/-- `necessary-relational-choice-r-implies-relational-choice-r`

□Relational Choice ⇒ Relational Choice -/
def necessary_relational_choice_r_implies_relational_choice_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecRelationalChoice.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RelationalChoice.schema)

/-- `necessary-rigid-comprehension-r-implies-necessary-actuality`

□Rigid Comprehension ⇒ □Actuality -/
def necessary_rigid_comprehension_r_implies_necessary_actuality : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecRigidComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecActuality.schema)

/-- `necessary-rigid-comprehension-r-implies-necessary-boolean-completeness-r`

□Rigid Comprehension ⇒ □Boolean Completeness -/
def necessary_rigid_comprehension_r_implies_necessary_boolean_completeness_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecRigidComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBooleanCompleteness.schema)

/-- `necessary-rigid-comprehension-r-implies-rigid-comprehension-r`

□Rigid Comprehension ⇒ Rigid Comprehension -/
def necessary_rigid_comprehension_r_implies_rigid_comprehension_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecRigidComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RigidComprehension.schema)

/-- `necessary-strong-leibniz-and-rigid-comprehension-imply-necessary-bf-t`

□Strong Leibniz Biconditionals ∧ Rigid Comprehension ⇒ □BF (type t) -/
def necessary_strong_leibniz_and_rigid_comprehension_imply_necessary_bf_t : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecStrongLeibniz.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RigidComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBarcanT.schema)

/-- `necessary-strong-leibniz-implies-necessary-atomicity`

□Strong Leibniz Biconditionals ⇒ □Atomicity -/
def necessary_strong_leibniz_implies_necessary_atomicity : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecStrongLeibniz.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecAtomicity.schema)

/-- `necessary-strong-leibniz-r-implies-necessary-strong-leibniz-t`

□Strong Leibniz Biconditionals ⇒ □Strong Leibniz Biconditionals (type t) -/
def necessary_strong_leibniz_r_implies_necessary_strong_leibniz_t : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecStrongLeibniz.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecStrongLeibnizT.schema)

/-- `necessary-strong-leibniz-r-implies-strong-leibniz-r`

□Strong Leibniz Biconditionals ⇒ Strong Leibniz Biconditionals -/
def necessary_strong_leibniz_r_implies_strong_leibniz_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecStrongLeibniz.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.StrongLeibniz.schema)

/-- `necessary-strong-leibniz-t-and-necessary-bf-imply-necessary-strong-leibniz`

□Strong Leibniz Biconditionals (type t) ∧ □BF ⇒ □Strong Leibniz Biconditionals -/
def necessary_strong_leibniz_t_and_necessary_bf_imply_necessary_strong_leibniz : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecStrongLeibnizT.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBarcan.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecStrongLeibniz.schema)

/-- `necessary-strong-leibniz-t-implies-strong-leibniz-t`

□Strong Leibniz Biconditionals (type t) ⇒ Strong Leibniz Biconditionals (type t) -/
def necessary_strong_leibniz_t_implies_strong_leibniz_t : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecStrongLeibnizT.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.StrongLeibnizT.schema)

/-- `necessary-tractarianism-r-implies-necessary-barcan-r`

□Tractarianism ⇒ □BF -/
def necessary_tractarianism_r_implies_necessary_barcan_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecTractarianism.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBarcan.schema)

/-- `necessary-tractarianism-r-implies-tractarianism-r`

□Tractarianism ⇒ Tractarianism -/
def necessary_tractarianism_r_implies_tractarianism_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecTractarianism.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Tractarianism.schema)

/-- `necessary-transversal-and-necessary-relational-choice-imply-necessary-transversal-choice`

□Transversal ∧ □Relational Choice ⇒ □Transversal Choice -/
def necessary_transversal_and_necessary_relational_choice_imply_necessary_transversal_choice : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecTransversal.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecRelationalChoice.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecTransversalChoice.schema)

/-- `necessary-transversal-choice-r-implies-necessary-relational-choice-r`

□Transversal Choice ⇒ □Relational Choice -/
def necessary_transversal_choice_r_implies_necessary_relational_choice_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecTransversalChoice.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecRelationalChoice.schema)

/-- `necessary-transversal-choice-r-implies-necessary-transversal-r`

□Transversal Choice ⇒ □Transversal -/
def necessary_transversal_choice_r_implies_necessary_transversal_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecTransversalChoice.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecTransversal.schema)

/-- `necessary-transversal-choice-r-implies-transversal-choice-r`

□Transversal Choice ⇒ Transversal Choice -/
def necessary_transversal_choice_r_implies_transversal_choice_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecTransversalChoice.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.TransversalChoice.schema)

/-- `necessary-transversal-r-implies-transversal-r`

□Transversal ⇒ Transversal -/
def necessary_transversal_r_implies_transversal_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecTransversal.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Transversal.schema)

/-- `necessary-vicinity-and-necessary-weakly-inextensible-comprehension-imply-necessary-actuality`

□Vicinity ∧ □Weakly Inextensible Comprehension ⇒ □Actuality -/
def necessary_vicinity_and_necessary_weakly_inextensible_comprehension_imply_necessary_actuality : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecVicinity.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecWeaklyInextensibleComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecActuality.schema)

/-- `necessary-vicinity-implies-vicinity`

□Vicinity ⇒ Vicinity -/
def necessary_vicinity_implies_vicinity : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecVicinity.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Vicinity.schema)

/-- `necessary-weakly-inextensible-comprehension-r-implies-weakly-inextensible-comprehension-r`

□Weakly Inextensible Comprehension ⇒ Weakly Inextensible Comprehension -/
def necessary_weakly_inextensible_comprehension_r_implies_weakly_inextensible_comprehension_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecWeaklyInextensibleComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.WeaklyInextensibleComprehension.schema)

/-- `no-contingency-signature-r-implies-no-pure-contingency-r`

No Contingency (signature Σ) ⇒ No Pure Contingency -/
def no_contingency_signature_r_implies_no_pure_contingency_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.noContingency _) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure))

/-- `no-contingency-signature-r-implies-signature-b-r`

No Contingency (signature Σ) ⇒ B for sentences of Σ -/
def no_contingency_signature_r_implies_signature_b_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.noContingency _) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.signatureB _)

/-- `no-pure-contingency-and-actuality-imply-necessary-actuality`

No Pure Contingency ∧ Actuality ⇒ □Actuality -/
def no_pure_contingency_and_actuality_imply_necessary_actuality : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecActuality.schema)

/-- `no-pure-contingency-and-atomicity-imply-necessary-atomicity`

No Pure Contingency ∧ Atomicity ⇒ □Atomicity -/
def no_pure_contingency_and_atomicity_imply_necessary_atomicity : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Atomicity.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecAtomicity.schema)

/-- `no-pure-contingency-and-b-imply-necessary-b`

No Pure Contingency ∧ B ⇒ □B -/
def no_pure_contingency_and_b_imply_necessary_b : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.ModalB.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecModalB.schema)

/-- `no-pure-contingency-and-bf-imply-necessary-bf`

No Pure Contingency ∧ BF ⇒ □BF -/
def no_pure_contingency_and_bf_imply_necessary_bf : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Barcan.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBarcan.schema)

/-- `no-pure-contingency-and-bf-t-imply-necessary-bf-t`

No Pure Contingency ∧ BF (type t) ⇒ □BF (type t) -/
def no_pure_contingency_and_bf_t_imply_necessary_bf_t : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.BarcanT.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBarcanT.schema)

/-- `no-pure-contingency-and-completeness-imply-necessary-completeness`

No Pure Contingency ∧ Boolean Completeness ⇒ □Boolean Completeness -/
def no_pure_contingency_and_completeness_imply_necessary_completeness : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.BooleanCompleteness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBooleanCompleteness.schema)

/-- `no-pure-contingency-and-extensionality-imply-necessary-extensionality`

No Pure Contingency ∧ Extensionality ⇒ □Extensionality -/
def no_pure_contingency_and_extensionality_imply_necessary_extensionality : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Extensionality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecExtensionality.schema)

/-- `no-pure-contingency-and-five-imply-necessary-five`

No Pure Contingency ∧ 5 ⇒ □5 -/
def no_pure_contingency_and_five_imply_necessary_five : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.ModalFive.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecModalFive.schema)

/-- `no-pure-contingency-and-fregean-imply-necessary-fregean`

No Pure Contingency ∧ Fregean Axiom ⇒ □Fregean Axiom -/
def no_pure_contingency_and_fregean_imply_necessary_fregean : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.FregeanAxiom.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecFregeanAxiom.schema)

/-- `no-pure-contingency-and-functional-choice-imply-necessary-functional-choice`

No Pure Contingency ∧ Functional Choice ⇒ □Functional Choice -/
def no_pure_contingency_and_functional_choice_imply_necessary_functional_choice : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.FunctionalChoice.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecFunctionalChoice.schema)

/-- `no-pure-contingency-and-functionality-imply-necessary-functionality`

No Pure Contingency ∧ Functionality ⇒ □Functionality -/
def no_pure_contingency_and_functionality_imply_necessary_functionality : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Functionality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecFunctionality.schema)

/-- `no-pure-contingency-and-gallin-comprehension-imply-necessary-gallin-comprehension`

No Pure Contingency ∧ Gallin Extensional Comprehension ⇒ □Gallin Extensional Comprehension -/
def no_pure_contingency_and_gallin_comprehension_imply_necessary_gallin_comprehension : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.GallinExtensionalComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecGallinExtensionalComprehension.schema)

/-- `no-pure-contingency-and-nd-imply-necessary-nd`

No Pure Contingency ∧ ND ⇒ □ND -/
def no_pure_contingency_and_nd_imply_necessary_nd : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecessityOfDistinctness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema)

/-- `no-pure-contingency-and-nd-t-imply-necessary-nd-t`

No Pure Contingency ∧ ND (type t) ⇒ □ND (type t) -/
def no_pure_contingency_and_nd_t_imply_necessary_nd_t : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecessityOfDistinctnessT.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctnessT.schema)

/-- `no-pure-contingency-and-plenitude-imply-necessary-plenitude`

No Pure Contingency ∧ Plenitude ⇒ □Plenitude -/
def no_pure_contingency_and_plenitude_imply_necessary_plenitude : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Plenitude.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecPlenitude.schema)

/-- `no-pure-contingency-and-relational-choice-imply-necessaryelational-choice`

No Pure Contingency ∧ Relational Choice ⇒ □Relational Choice -/
def no_pure_contingency_and_relational_choice_imply_necessaryelational_choice : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RelationalChoice.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecRelationalChoice.schema)

/-- `no-pure-contingency-and-rigid-comprehension-imply-necessary-rigid-comprehension`

No Pure Contingency ∧ Rigid Comprehension ⇒ □Rigid Comprehension -/
def no_pure_contingency_and_rigid_comprehension_imply_necessary_rigid_comprehension : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RigidComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecRigidComprehension.schema)

/-- `no-pure-contingency-and-strong-leibniz-imply-necessary-strong-leibniz`

No Pure Contingency ∧ Strong Leibniz Biconditionals ⇒ □Strong Leibniz Biconditionals -/
def no_pure_contingency_and_strong_leibniz_imply_necessary_strong_leibniz : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.StrongLeibniz.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecStrongLeibniz.schema)

/-- `no-pure-contingency-and-strong-leibniz-t-imply-necessary-strong-leibniz-t`

No Pure Contingency ∧ Strong Leibniz Biconditionals (type t) ⇒ □Strong Leibniz Biconditionals (type t) -/
def no_pure_contingency_and_strong_leibniz_t_imply_necessary_strong_leibniz_t : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.StrongLeibnizT.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecStrongLeibnizT.schema)

/-- `no-pure-contingency-and-tractarianism-imply-necessary-tractarianism`

No Pure Contingency ∧ Tractarianism ⇒ □Tractarianism -/
def no_pure_contingency_and_tractarianism_imply_necessary_tractarianism : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Tractarianism.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecTractarianism.schema)

/-- `no-pure-contingency-and-transversal-choice-imply-necessary-transversal-choice`

No Pure Contingency ∧ Transversal Choice ⇒ □Transversal Choice -/
def no_pure_contingency_and_transversal_choice_imply_necessary_transversal_choice : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.TransversalChoice.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecTransversalChoice.schema)

/-- `no-pure-contingency-and-transversal-imply-necessary-transversal`

No Pure Contingency ∧ Transversal ⇒ □Transversal -/
def no_pure_contingency_and_transversal_imply_necessary_transversal : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Transversal.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecTransversal.schema)

/-- `no-pure-contingency-and-vicinity-imply-necessary-vicinity`

No Pure Contingency ∧ Vicinity ⇒ □Vicinity -/
def no_pure_contingency_and_vicinity_imply_necessary_vicinity : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Vicinity.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecVicinity.schema)

/-- `no-pure-contingency-and-weakly-inextensible-comprehension-imply-necessary-weakly-inextensible-comprehension`

No Pure Contingency ∧ Weakly Inextensible Comprehension ⇒ □Weakly Inextensible Comprehension -/
def no_pure_contingency_and_weakly_inextensible_comprehension_imply_necessary_weakly_inextensible_comprehension : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.WeaklyInextensibleComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecWeaklyInextensibleComprehension.schema)

/-- `no-pure-contingency-r-implies-pure-b-r`

No Pure Contingency ⇒ B for pure sentences -/
def no_pure_contingency_r_implies_pure_b_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.pureB Classicism.Meta.Signature.pure))

/-- `persistent-comprehension-r-implies-actuality`

Persistent Comprehension ⇒ Actuality -/
def persistent_comprehension_r_implies_actuality : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.PersistentComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema)

/-- `plenitude-r-implies-actuality`

Plenitude ⇒ Actuality -/
def plenitude_r_implies_actuality : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Plenitude.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema)

/-- `plenitude-r-implies-distinctness-necessary-r`

Plenitude ⇒ ND -/
def plenitude_r_implies_distinctness_necessary_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Plenitude.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecessityOfDistinctness.schema)

/-- `possibility-and-necessary-barcan-t-incompatible`

Possibility Maximalism (pure) ∧ □BF (type t) ⇒ ⊥ -/
def possibility_and_necessary_barcan_t_incompatible : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.possibility (Classicism.Meta.AxiomSet.empty : Classicism.Meta.AxiomSet Classicism.Meta.Signature.pure))) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBarcanT.schema) →
    False

/-- `possibility-and-necessary-relational-choice-incompatible`

Possibility Maximalism (pure) ∧ □Relational Choice ⇒ ⊥ -/
def possibility_and_necessary_relational_choice_incompatible : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.possibility (Classicism.Meta.AxiomSet.empty : Classicism.Meta.AxiomSet Classicism.Meta.Signature.pure))) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecRelationalChoice.schema) →
    False

/-- `possibility-and-necessary-strong-leibniz-t-incompatible`

Possibility Maximalism (pure) ∧ □Strong Leibniz Biconditionals (type t) ⇒ ⊥ -/
def possibility_and_necessary_strong_leibniz_t_incompatible : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.possibility (Classicism.Meta.AxiomSet.empty : Classicism.Meta.AxiomSet Classicism.Meta.Signature.pure))) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecStrongLeibnizT.schema) →
    False

/-- `possibility-and-no-pure-contingency-incompatible`

Possibility Maximalism (pure) ∧ No Pure Contingency ⇒ ⊥ -/
def possibility_and_no_pure_contingency_incompatible : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.possibility (Classicism.Meta.AxiomSet.empty : Classicism.Meta.AxiomSet Classicism.Meta.Signature.pure))) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) →
    False

/-- `possibility-schema-r-implies-distinctness-schema-r`

Possibility Maximalism (pure) ⇒ Distinctness Maximalism (pure) -/
def possibility_schema_r_implies_distinctness_schema_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.possibility (Classicism.Meta.AxiomSet.empty : Classicism.Meta.AxiomSet Classicism.Meta.Signature.pure))) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.distinctness (Classicism.Meta.AxiomSet.empty : Classicism.Meta.AxiomSet Classicism.Meta.Signature.pure)))

/-- `possibility-signature-r-implies-distinctness-signature-r`

Possibility Maximalism (signature Σ) ⇒ Distinctness Maximalism (signature Σ) -/
def possibility_signature_r_implies_distinctness_signature_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.possibility Classicism.Meta.AxiomSet.empty) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.distinctness Classicism.Meta.AxiomSet.empty)

/-- `possibility-signature-r-implies-possibility-schema-r`

Possibility Maximalism (signature Σ) ⇒ Possibility Maximalism (pure) -/
def possibility_signature_r_implies_possibility_schema_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.possibility Classicism.Meta.AxiomSet.empty) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.possibility (Classicism.Meta.AxiomSet.empty : Classicism.Meta.AxiomSet Classicism.Meta.Signature.pure)))

/-- `pure-b-and-pure-possibility-incompatible`

B for pure sentences ∧ Possibility Maximalism (pure) ⇒ ⊥ -/
def pure_b_and_pure_possibility_incompatible : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.pureB Classicism.Meta.Signature.pure)) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.possibility (Classicism.Meta.AxiomSet.empty : Classicism.Meta.AxiomSet Classicism.Meta.Signature.pure))) →
    False

/-- `relational-choice-and-boolean-completeness-imply-transversal-choice`  (conjectured)

Relational Choice ∧ Boolean Completeness ⇒ Transversal Choice -/
def relational_choice_and_boolean_completeness_imply_transversal_choice : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RelationalChoice.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.BooleanCompleteness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.TransversalChoice.schema)

/-- `relational-choice-and-extensionality-imply-transversal-choice`

Relational Choice ∧ Extensionality ⇒ Transversal Choice -/
def relational_choice_and_extensionality_imply_transversal_choice : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RelationalChoice.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Extensionality.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.TransversalChoice.schema)

/-- `relational-choice-and-plenitude-imply-functional-choice-r`

Relational Choice ∧ Plenitude ⇒ Functional Choice -/
def relational_choice_and_plenitude_imply_functional_choice_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RelationalChoice.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Plenitude.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.FunctionalChoice.schema)

/-- `relational-choice-and-very-weak-rigid-comprehension-imply-transversal-choice`

Relational Choice ∧ Very Weak Rigid Comprehension ⇒ Transversal Choice -/
def relational_choice_and_very_weak_rigid_comprehension_imply_transversal_choice : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RelationalChoice.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.VeryWeakRigidComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.TransversalChoice.schema)

/-- `relational-choice-r-implies-transversal-choice-r`  (conjectured)

Relational Choice ⇒ Transversal Choice -/
def relational_choice_r_implies_transversal_choice_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RelationalChoice.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.TransversalChoice.schema)

/-- `rigid-comprehension-and-bf-imply-necessary-bf`

Rigid Comprehension ∧ BF ⇒ □BF -/
def rigid_comprehension_and_bf_imply_necessary_bf : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RigidComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Barcan.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBarcan.schema)

/-- `rigid-comprehension-and-nd-imply-plenitude`

Rigid Comprehension ∧ ND ⇒ Plenitude -/
def rigid_comprehension_and_nd_imply_plenitude : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RigidComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecessityOfDistinctness.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Plenitude.schema)

/-- `rigid-comprehension-r-implies-actuality`

Rigid Comprehension ⇒ Actuality -/
def rigid_comprehension_r_implies_actuality : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RigidComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema)

/-- `rigid-comprehension-r-implies-boolean-completeness-r`

Rigid Comprehension ⇒ Boolean Completeness -/
def rigid_comprehension_r_implies_boolean_completeness_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RigidComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.BooleanCompleteness.schema)

/-- `rigid-comprehension-r-implies-inextensible-comprehension-r`

Rigid Comprehension ⇒ Inextensible Comprehension -/
def rigid_comprehension_r_implies_inextensible_comprehension_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RigidComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.InextensibleComprehension.schema)

/-- `rigid-comprehension-r-implies-persistent-comprehension-r`

Rigid Comprehension ⇒ Persistent Comprehension -/
def rigid_comprehension_r_implies_persistent_comprehension_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RigidComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.PersistentComprehension.schema)

/-- `rigid-comprehension-r-implies-weak-rigid-comprehension-r`

Rigid Comprehension ⇒ Weak Rigid Comprehension -/
def rigid_comprehension_r_implies_weak_rigid_comprehension_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RigidComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.WeakRigidComprehension.schema)

/-- `signature-b-r-implies-pure-b-r`

B for sentences of Σ ⇒ B for pure sentences -/
def signature_b_r_implies_pure_b_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.signatureB _) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.pureB Classicism.Meta.Signature.pure))

/-- `strong-leibniz-r-implies-atomicity-r`

Strong Leibniz Biconditionals ⇒ Atomicity -/
def strong_leibniz_r_implies_atomicity_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.StrongLeibniz.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Atomicity.schema)

/-- `strong-leibniz-r-implies-strong-leibniz-t`

Strong Leibniz Biconditionals ⇒ Strong Leibniz Biconditionals (type t) -/
def strong_leibniz_r_implies_strong_leibniz_t : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.StrongLeibniz.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.StrongLeibnizT.schema)

/-- `strong-leibniz-t-implies-atomicity-t`

Strong Leibniz Biconditionals (type t) ⇒ Atomicity (type t) -/
def strong_leibniz_t_implies_atomicity_t : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.StrongLeibnizT.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.AtomicityT.schema)

/-- `strong-leibniz-t-implies-necessary-actuality`

Strong Leibniz Biconditionals (type t) ⇒ □Actuality -/
def strong_leibniz_t_implies_necessary_actuality : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.StrongLeibnizT.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecActuality.schema)

/-- `tractarianism-r-implies-barcan-r`

Tractarianism ⇒ BF -/
def tractarianism_r_implies_barcan_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Tractarianism.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Barcan.schema)

/-- `transversal-and-relational-choice-imply-transversal-choice`

Transversal ∧ Relational Choice ⇒ Transversal Choice -/
def transversal_and_relational_choice_imply_transversal_choice : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Transversal.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RelationalChoice.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.TransversalChoice.schema)

/-- `transversal-choice-r-implies-relational-choice-r`

Transversal Choice ⇒ Relational Choice -/
def transversal_choice_r_implies_relational_choice_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.TransversalChoice.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RelationalChoice.schema)

/-- `transversal-choice-r-implies-transversal-r`

Transversal Choice ⇒ Transversal -/
def transversal_choice_r_implies_transversal_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.TransversalChoice.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Transversal.schema)

/-- `very-weak-rigid-comprehension-r-implies-weak-rigid-comprehension-r`

Very Weak Rigid Comprehension ⇒ Weak Rigid Comprehension -/
def very_weak_rigid_comprehension_r_implies_weak_rigid_comprehension_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.VeryWeakRigidComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.WeakRigidComprehension.schema)

/-- `vicinity-and-distinctness-preserving-collapse-imply-actuality`

Vicinity ∧ Distinctness-preserving collapse ⇒ Actuality -/
def vicinity_and_distinctness_preserving_collapse_imply_actuality : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Vicinity.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.DistinctnessPreservingCollapse.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema)

/-- `vicinity-and-weakly-inextensible-comprehension-imply-actuality`

Vicinity ∧ Weakly Inextensible Comprehension ⇒ Actuality -/
def vicinity_and_weakly_inextensible_comprehension_imply_actuality : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Vicinity.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.WeaklyInextensibleComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema)

/-- `weak-rigid-comprehension-r-implies-boolean-completeness-r`

Weak Rigid Comprehension ⇒ Boolean Completeness -/
def weak_rigid_comprehension_r_implies_boolean_completeness_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.WeakRigidComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.BooleanCompleteness.schema)

/-- `weak-rigid-comprehension-r-implies-persistent-comprehension-r`

Weak Rigid Comprehension ⇒ Persistent Comprehension -/
def weak_rigid_comprehension_r_implies_persistent_comprehension_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.WeakRigidComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.PersistentComprehension.schema)

/-- `weak-rigid-comprehension-r-implies-very-weak-rigid-comprehension-r`

Weak Rigid Comprehension ⇒ Very Weak Rigid Comprehension -/
def weak_rigid_comprehension_r_implies_very_weak_rigid_comprehension_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.WeakRigidComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.VeryWeakRigidComprehension.schema)

/-- `weak-rigid-comprehension-r-implies-weakly-inextensible-comprehension-r`

Weak Rigid Comprehension ⇒ Weakly Inextensible Comprehension -/
def weak_rigid_comprehension_r_implies_weakly_inextensible_comprehension_r : Prop :=
  ∀ {Sig : Classicism.Meta.Signature} (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.WeakRigidComprehension.schema) →
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.WeaklyInextensibleComprehension.schema)

/-- `finite-support-sections-and-projection`

Finite-support action model: N and N×2, sections and projection: a witness satisfying 2 principles
and violating 2. -/
def finite_support_sections_and_projection : Prop :=
  ∃ (Sig : Classicism.Meta.Signature) (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax ∧
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema) ∧
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecActuality.schema) ∧
    ¬ Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.InextensibleComprehension.schema) ∧
    ¬ Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Barcan.schema)

/-- `full-boolean-valued-atom-and-atomless`

Full Boolean-valued model: one atom and an atomless component: a witness satisfying 7 principles
and violating 6. -/
def full_boolean_valued_atom_and_atomless : Prop :=
  ∃ (Sig : Classicism.Meta.Signature) (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax ∧
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecNecessityOfDistinctness.schema) ∧
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBarcan.schema) ∧
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Barcan.schema) ∧
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RelationalChoice.schema) ∧
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.FunctionalChoice.schema) ∧
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Plenitude.schema) ∧
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema) ∧
    ¬ Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.AtomicityT.schema) ∧
    ¬ Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Atomicity.schema) ∧
    ¬ Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Atomlessness.schema) ∧
    ¬ Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecFunctionalChoice.schema) ∧
    ¬ Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecPlenitude.schema) ∧
    ¬ Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecActuality.schema)

/-- `symmetric-infinite-classes`

Symmetric ideally-full model: automorphisms of infinitely many infinite classes: a witness satisfying 7 principles
and violating 5. -/
def symmetric_infinite_classes : Prop :=
  ∃ (Sig : Classicism.Meta.Signature) (Ax : Classicism.Meta.AxiomSet Sig), Classicism.Meta.AxiomSet.Consistent Ax ∧
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.BooleanCompleteness.schema) ∧
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBooleanCompleteness.schema) ∧
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Barcan.schema) ∧
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecBarcan.schema) ∧
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure (Classicism.Meta.AxiomSet.npc Classicism.Meta.Signature.pure)) ∧
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Atomlessness.schema) ∧
    Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.InextensibleComprehension.schema) ∧
    ¬ Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Transversal.schema) ∧
    ¬ Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.Actuality.schema) ∧
    ¬ Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.RelationalChoice.schema) ∧
    ¬ Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.AtomicityT.schema) ∧
    ¬ Classicism.Meta.AxiomSet.Entails Ax (Classicism.Meta.AxiomSet.ofPure Classicism.P.NecessityOfDistinctness.schema)

end Classicism.Statements
