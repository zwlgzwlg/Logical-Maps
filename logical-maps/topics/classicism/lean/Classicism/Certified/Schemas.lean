import Classicism.Tools.Schema
import Classicism.Certified.Quoted

/-!
# The map's principles as schemas

Every principle of the shallow layer (from its strict twin where it has one), read into the object language
as a schema: `P.quoted`, the sentence as a function of the principle's object-type
parameters; `P.reflect`, that reading it back gives the strict twin, by `rfl`; and
`P.schema`, the axiom set of its instances at closed types. This is the one home of those declarations.
-/

#classicism_schema
  Classicism.P.ModalK Classicism.P.ModalT Classicism.P.ModalFour Classicism.P.ModalFive
  Classicism.P.ModalB Classicism.P.ModalizedFregean Classicism.P.FregeanAxiom
  Classicism.P.Intensionality Classicism.P.Extensionality Classicism.P.Functionality
  Classicism.P.ModalizedFunctionality Classicism.P.NecessityOfIdentity
  Classicism.P.NecessityOfDistinctness Classicism.P.NecessityOfDistinctnessT
  Classicism.P.NecNecessityOfDistinctnessT Classicism.P.NecNecessityOfDistinctness
  Classicism.P.Barcan Classicism.P.BarcanT Classicism.P.NecBarcan
  Classicism.P.NecBarcanT Classicism.P.ConverseBarcan Classicism.P.Tractarianism
  Classicism.P.RigidComprehension Classicism.P.WeakRigidComprehension
  Classicism.P.VeryWeakRigidComprehension Classicism.P.PersistentComprehension
  Classicism.P.InextensibleComprehension Classicism.P.GallinExtensionalComprehension
  Classicism.P.FunctionalChoice Classicism.P.RelationalChoice Classicism.P.Existence
  Classicism.P.Atomicity Classicism.P.AtomicityT Classicism.P.NecAtomicity
  Classicism.P.Atomlessness Classicism.P.BooleanCompleteness Classicism.P.BooleanCompletenessT
  Classicism.P.NecBooleanCompleteness Classicism.P.Actuality Classicism.P.NecActuality
  Classicism.P.ActualProfile Classicism.P.NecRigidComprehension Classicism.P.Plenitude
  Classicism.P.NecGallinExtensionalComprehension Classicism.P.NecPlenitude
  Classicism.P.NecModalB Classicism.P.NecModalFive Classicism.P.NecFregeanAxiom
  Classicism.P.NecExtensionality Classicism.P.NecFunctionality Classicism.P.NecTractarianism
  Classicism.P.NecFunctionalChoice Classicism.P.NecRelationalChoice
  Classicism.P.StrongLeibniz Classicism.P.StrongLeibnizT Classicism.P.NecStrongLeibniz
  Classicism.P.NecStrongLeibnizT Classicism.P.DistinctnessPreservingCollapse
  Classicism.P.BroadNecessitism
