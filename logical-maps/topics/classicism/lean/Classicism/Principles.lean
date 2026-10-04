import Classicism.Principles.Base
import Classicism.Principles.Coarse
import Classicism.Principles.Extensionality
import Classicism.Principles.Lattice
import Classicism.Principles.Instances
import Classicism.Principles.Comprehension
import Classicism.Principles.Choice
import Classicism.Principles.Infinity
import Classicism.Principles.Schematic

/-!
# Principle statements

One definition per principle of the map with a shallow statement, named as the map's
`lean_def` convention expects (`Classicism.P.<Name>`), in a file per category of the map
(the `category` field of the principle's record):

| file | the map's category |
| --- | --- |
| `Principles/Base.lean` | `base`: theorems of `C`, `K`, `T`, `4`, CBF, NI, Existence |
| `Principles/Coarse.lean` | `coarse`: `B`, `5`, ND, BF, Tractarianism |
| `Principles/Extensionality.lean` | `extensionality`: the Fregean Axiom, Extensionality, Functionality |
| `Principles/Lattice.lean` | `lattice`: Atomicity, Boolean Completeness, Actuality, Strong Leibniz |
| `Principles/Instances.lean` | `instances`: the principles at `t` kept beside their general forms |
| `Principles/Comprehension.lean` | `comprehension`: the comprehension principles |
| `Principles/Choice.lean` | `choice`: Choice, Plenitude, Transversals |
| `Principles/Infinity.lean` | `infinity`: the Axioms of Infinity and Possible Infinity |
| `Principles/Schematic.lean` | `schematic`: the Distinctness-Preserving Collapse |

The sentence schemas, the map's other `schematic` principles and its `signature` ones, are
not shallow statements: they are defined in the object language, in `Syntax/`.

## Principles are families of formulas, indexed by types

The map's metalinguistic quantifier `∀ᵀʸ σ` ranges over *types*, and a principle is a
family of formulas, its **instances**, one for each choice of types. No formula of the
paper's language quantifies over types, so a principle is not itself a formula, and it is
not rendered here as one Lean proposition quantifying over types. Each principle takes its
types as explicit **type parameters** and is a formula once they are fixed:
`Functionality σ τ` is `(∀z. Xz = Yz) → X = Y` for `X Y : σ → τ`, and `Barcan Prop` is BF
at type `t`. The guards `[Ty σ]` (a **Ty-parameter**) and `[Rel τ]` (a **Rel-parameter**)
are the map's side conditions on the types. The set of a principle's instances, as
sentences of the object language, is its **schema**, `P.X.schema`
(`Certified/Schemas.lean`); the README sets out these names.

This is what the type-system check enforces: a binder over a type may be a parameter of a
declaration, never a quantifier inside a formula. A record about principles is then an
implication between *instances*, with the types the argument needs as parameters, which
the paper reads as a metatheorem and which keeps every certified statement within the
strict layer's reach.

`□P` for a principle `P` is likewise the family of `□`-prefixed instances, so a boxed
principle boxes the formula after its type parameters, as the Background says.

Definitions are from `topics/classicism/background.md`; each statement is the record's
`formal` field with its type quantifier made a parameter.

## The paper's symbols

The files open the scope `Classicism.Paper` where its symbols are used, so that the
statements read as the map writes them: `x ≤ ¬ x`, `W ≠ ⊥`, `Persistent (¬ Y)`. The scope
changes no terms (`Paper.lean`). The exception is `Principles/Coarse.lean`, which does not
open it: Tractarianism's `≤` at `Prop` is `entails`, and inside the scope it would be
`Rel.le`.
-/
