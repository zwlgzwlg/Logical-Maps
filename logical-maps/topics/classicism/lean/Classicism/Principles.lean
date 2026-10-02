import Classicism.Comprehension
import Classicism.Lattice
import Classicism.Cardinality

/-!
# Principle statements

One definition per principle of the map that this first step covers, named as the map's
`lean_def` convention expects (`Classicism.P.<Name>`).

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
-/

namespace Classicism.P

/-! ### Modal principles, at type `t` -/

/-- `modal-k`: `∀pq. □(p→q) → (□p → □q)`. -/
def ModalK : Prop := ∀ p q : Prop, □ (p → q) → □ p → □ q
/-- `modal-t`: `∀p. □p → p`. -/
def ModalT : Prop := ∀ p : Prop, □ p → p
/-- `modal-four`: `∀p. □p → □□p`. -/
def ModalFour : Prop := ∀ p : Prop, □ p → □ □ p
/-- `modal-five`: `∀p. ◇p → □◇p`. -/
def ModalFive : Prop := ∀ p : Prop, ◇ p → □ ◇ p
/-- `modal-b`: `∀p. p → □◇p`. -/
def ModalB : Prop := ∀ p : Prop, p → □ ◇ p
/-- `modalized-fregean`: `∀pq. □(p↔q) → p = q`. -/
def ModalizedFregean : Prop := ∀ p q : Prop, □ (p ↔ q) → p = q
/-- `fregean-axiom`: `∀pq. (p↔q) → p = q`. -/
def FregeanAxiom : Prop := ∀ p q : Prop, (p ↔ q) → p = q

/-! ### Coarse-grainedness principles, at a type -/

/-- `intensionality-r` at the relational type `τ`: `□(∀z̄. X[z̄] ↔ Y[z̄]) → X = Y`. -/
def Intensionality (τ : Type) [Rel τ] : Prop := ∀ X Y : τ, □ (coext X Y) → X = Y
/-- `extensionality-r` at `τ`: `(∀z̄. X[z̄] ↔ Y[z̄]) → X = Y`. -/
def Extensionality (τ : Type) [Rel τ] : Prop := ∀ X Y : τ, coext X Y → X = Y
/-- `functionality-r` at `σ → τ`: `(∀z. Xz = Yz) → X = Y`, `τ` relational. -/
def Functionality (σ τ : Type) [Ty σ] [Rel τ] : Prop :=
  ∀ X Y : σ → τ, (∀ z, X z = Y z) → X = Y
/-- `modalized-functionality-r` at `σ → τ`: `□(∀z. Xz = Yz) → X = Y`. -/
def ModalizedFunctionality (σ τ : Type) [Ty σ] [Rel τ] : Prop :=
  ∀ X Y : σ → τ, □ (∀ z, X z = Y z) → X = Y
/-- `identity-necessary-r` (NI) at `σ`: `∀xy. x = y → □(x = y)`. -/
def NecessityOfIdentity (σ : Type) [Ty σ] : Prop := ∀ x y : σ, x = y → □ (x = y)
/-- `distinctness-necessary-r` (ND) at `σ`: `∀xy. x ≠ y → □(x ≠ y)`. -/
def NecessityOfDistinctness (σ : Type) [Ty σ] : Prop := ∀ x y : σ, x ≠ y → □ (x ≠ y)
/-- `distinctness-necessary-t`: ND at type `t`. -/
def NecessityOfDistinctnessT : Prop := NecessityOfDistinctness Prop
/-- `necessary-distinctness-necessary-t`: □ND at type `t`. -/
def NecNecessityOfDistinctnessT : Prop := □ NecessityOfDistinctnessT
/-- `barcan-r` (BF) at `σ`: `∀X. (∀x. □Xx) → □(∀x. Xx)`. -/
def Barcan (σ : Type) [Ty σ] : Prop := ∀ X : σ → Prop, (∀ x, □ (X x)) → □ (∀ x, X x)
/-- `barcan-t`: BF at type `t`. -/
def BarcanT : Prop := Barcan Prop
/-- `necessary-barcan-t`: □BF at type `t`. -/
def NecBarcanT : Prop := □ BarcanT
/-- `necessary-distinctness-necessary-r`: □ND at `σ`. -/
def NecNecessityOfDistinctness (σ : Type) [Ty σ] : Prop := □ (NecessityOfDistinctness σ)
/-- `necessary-barcan-r`: □BF at `σ`. -/
def NecBarcan (σ : Type) [Ty σ] : Prop := □ (Barcan σ)
/-- `converse-barcan-r` (CBF) at `σ`: `∀X. □(∀x. Xx) → ∀x. □Xx`. -/
def ConverseBarcan (σ : Type) [Ty σ] : Prop := ∀ X : σ → Prop, □ (∀ x, X x) → ∀ x, □ (X x)
/-- `existence-r` at `σ`: `∃x^σ. x = x`. The type system has two shapes of type, `e` and
the relational types; `Existence e` is the axiom `e_exists`, and `Existence τ` for
relational `τ` is a theorem of `C⁻`. The two instances are the two records' proofs. -/
def Existence (σ : Type) [Ty σ] : Prop := ∃ x : σ, x = x
/-- `tractarianism-r` at `σ`: `∀pX. (∀x. p ≤ Xx) → p ≤ ∀x. Xx`. -/
def Tractarianism (σ : Type) [Ty σ] : Prop :=
  ∀ (p : Prop) (X : σ → Prop), (∀ x, p ≤ X x) → p ≤ (∀ x, X x)

/-! ### Lattice principles, at a relational type -/

/-- `atomicity-r` at `τ`: `∀x. x ≤ ¬x ∨ ∃y. Atom(y) ∧ y ≤ x`, every non-bottom entity has
an atom below it. -/
def Atomicity (τ : Type) [Rel τ] : Prop :=
  ∀ x : τ, Rel.le x (Rel.neg x) ∨ ∃ y : τ, Atom y ∧ Rel.le y x
/-- `atomicity-t`: Atomicity at type `t`. -/
def AtomicityT : Prop := Atomicity Prop
/-- `necessary-atomicity-r` at `τ`: the instance boxed. -/
def NecAtomicity (τ : Type) [Rel τ] : Prop := □ (Atomicity τ)

/-- `atomlessness`: `∀p. ◇p → ∃q. ◇q ∧ q ≤ p ∧ q ≠ p`, every possible proposition has a
possible proposition strictly below it. -/
def Atomlessness : Prop := ∀ p : Prop, ◇ p → ∃ q : Prop, ◇ q ∧ Rel.le q p ∧ q ≠ p

/-- `boolean-completeness-r` at `τ`: `∀X. ∃y. GLB_τ(y, X)`, every property of entities
of the type has a greatest lower bound. -/
def BooleanCompleteness (τ : Type) [Rel τ] : Prop := ∀ X : τ → Prop, ∃ y : τ, GLB y X
/-- Boolean Completeness, its LUB form: `∀X. ∃y. LUB_τ(y, X)`, every property of entities
of the type has a least upper bound. Equivalent to the official form, at each type
(`Results/Forms.lean`). -/
def BooleanCompletenessLUB (τ : Type) [Rel τ] : Prop := ∀ X : τ → Prop, ∃ y : τ, LUB y X
/-- `boolean-completeness-t`: Boolean Completeness at type `t`. -/
def BooleanCompletenessT : Prop := BooleanCompleteness Prop
/-- `necessary-boolean-completeness-r` at `τ`: the instance boxed. -/
def NecBooleanCompleteness (τ : Type) [Rel τ] : Prop := □ (BooleanCompleteness τ)

/-- `actuality`: `∃p. p ∧ ∀q. q → p ≤ q`, there is a true proposition that entails every
truth — a true atom, an actual world. -/
def Actuality : Prop := ∃ p : Prop, p ∧ ∀ q : Prop, q → Rel.le p q
/-- `necessary-actuality`: Actuality boxed. -/
def NecActuality : Prop := □ Actuality

/-- `actual-profile-r` at `σ`, for one argument: `∀x. ∃Y. Yx ∧ ∀Z. Zx → Y ≤ Z`, every
individual of the type has a true property entailing every property it has. The map's
principle is over finite argument tuples; this is the unary instance, and its nullary
instance is Actuality itself. -/
def ActualProfile (σ : Type) [Ty σ] : Prop :=
  ∀ x : σ, ∃ Y : σ → Prop, Y x ∧ ∀ Z : σ → Prop, Z x → Rel.le Y Z

/-! ### Comprehension, at a relational type

Each says that every relation of the type, including a proposition, is coextensive with
one of the stated kind. The map's `∀ᵀʸ σ̄` over argument tuples is the parameter `τ`,
since a relational type *is* a tuple type ending in `t`. -/

/-- `rigid-comprehension-r` at `τ`. -/
def RigidComprehension (τ : Type) [Rel τ] : Prop :=
  ∀ X : τ, ∃ Y : τ, Rigid Y ∧ coext X Y
/-- `weak-rigid-comprehension-r` at `τ`. -/
def WeakRigidComprehension (τ : Type) [Rel τ] : Prop :=
  ∀ X : τ, ∃ Y : τ, WeaklyRigid Y ∧ coext X Y
/-- `very-weak-rigid-comprehension-r` at `τ`. -/
def VeryWeakRigidComprehension (τ : Type) [Rel τ] : Prop :=
  ∀ X : τ, ∃ Y : τ, VeryWeaklyRigid Y ∧ coext X Y
/-- `persistent-comprehension-r` at `τ`. -/
def PersistentComprehension (τ : Type) [Rel τ] : Prop :=
  ∀ X : τ, ∃ Y : τ, Persistent Y ∧ coext X Y
/-- `inextensible-comprehension-r` at `τ`. -/
def InextensibleComprehension (τ : Type) [Rel τ] : Prop :=
  ∀ X : τ, ∃ Y : τ, Inextensible Y ∧ coext X Y
/-- `necessary-rigid-comprehension-r` at `τ`: the instance boxed. -/
def NecRigidComprehension (τ : Type) [Rel τ] : Prop := □ (RigidComprehension τ)
/-- `gallin-extensional-comprehension-r` at `τ`: every relation is coextensive with one
that is persistent and has a persistent pointwise negation. Gallin's rigidity convention. -/
def GallinExtensionalComprehension (τ : Type) [Rel τ] : Prop :=
  ∀ X : τ, ∃ Y : τ, Persistent Y ∧ Persistent (Rel.neg Y) ∧ coext X Y
/-- `necessary-gallin-extensional-comprehension-r` at `τ`: the instance boxed. -/
def NecGallinExtensionalComprehension (τ : Type) [Rel τ] : Prop :=
  □ (GallinExtensionalComprehension τ)

/-! ### Choice

`Serial` and `Functional` are the Background's, for a curried `U^{στt}`. `Functional`
includes totality. Relational Choice covers relations with individual outputs, since
such a relation still ends in `t`; Functional Choice cannot, because an operation's
output type must differ from `e`. -/

/-- `Serial(U) := ∀x. ∃y. (Ux)y`. -/
def Serial {σ τ : Type} [Ty σ] [Ty τ] (U : σ → τ → Prop) : Prop := ∀ x, ∃ y, U x y
/-- `Functional(U) := ∀x. ∃y. (Ux)y ∧ ∀z. (Ux)z → y = z`. -/
def Functional {σ τ : Type} [Ty σ] [Ty τ] (U : σ → τ → Prop) : Prop :=
  ∀ x, ∃ y, U x y ∧ ∀ z, U x z → y = z

/-- `functional-choice-r` at `σ`, `τ`: every serial relation `U : σ → τ → Prop` admits a
selecting operation, whose output type `τ` is relational. -/
def FunctionalChoice (σ τ : Type) [Ty σ] [Rel τ] : Prop :=
  ∀ U : σ → τ → Prop, Serial U → ∃ X : σ → τ, ∀ x, U x (X x)

/-- `relational-choice-r` at `σ`, `τ`: every serial relation has a functional
subrelation. The output type is unrestricted. -/
def RelationalChoice (σ τ : Type) [Ty σ] [Ty τ] : Prop :=
  ∀ U : σ → τ → Prop, Serial U → ∃ S : σ → τ → Prop, Functional S ∧ ∀ x y, S x y → U x y

/-- `plenitude-r` at `σ`, `τ`: every functional relation `U : σ → τ → Prop` is represented
by an operation, whose output type `τ` is relational (Classicism, §2.4). -/
def Plenitude (σ τ : Type) [Ty σ] [Rel τ] : Prop :=
  ∀ U : σ → τ → Prop, Functional U → ∃ X : σ → τ, ∀ y, U y (X y)
/-- `necessary-plenitude-r` at `σ`, `τ`: the instance boxed. -/
def NecPlenitude (σ τ : Type) [Ty σ] [Rel τ] : Prop := □ (Plenitude σ τ)

/-! ### Further principles of the map (28 September)

Boxed forms of principles above, the Strong Leibniz Biconditionals with Bacon's strong
worlds, the distinctness-preserving modality of §2.6, and Broad Necessitism. -/

/-- `necessary-modal-b`: `B` boxed. -/
def NecModalB : Prop := □ ModalB
/-- `necessary-modal-five`: `5` boxed. -/
def NecModalFive : Prop := □ ModalFive
/-- `necessary-fregean-axiom`. -/
def NecFregeanAxiom : Prop := □ FregeanAxiom
/-- `necessary-extensionality-r` at `τ`. -/
def NecExtensionality (τ : Type) [Rel τ] : Prop := □ (Extensionality τ)
/-- `necessary-functionality-r` at `σ`, `τ`. -/
def NecFunctionality (σ τ : Type) [Ty σ] [Rel τ] : Prop := □ (Functionality σ τ)
/-- `necessary-tractarianism-r` at `σ`. -/
def NecTractarianism (σ : Type) [Ty σ] : Prop := □ (Tractarianism σ)
/-- `necessary-functional-choice-r` at `σ`, `τ`. -/
def NecFunctionalChoice (σ τ : Type) [Ty σ] [Rel τ] : Prop := □ (FunctionalChoice σ τ)
/-- `necessary-relational-choice-r` at `σ`, `τ`. -/
def NecRelationalChoice (σ τ : Type) [Ty σ] [Ty τ] : Prop := □ (RelationalChoice σ τ)

/-- `SWorld_τ(W) := ◇_τ W ∧ □∀Y. W ≤ Y ∨ W ≤ ¬Y`, with `◇_τ W := W ≠ ⊥_τ` (Bacon §8.2). -/
def SWorld {τ : Type} [Rel τ] (W : τ) : Prop :=
  W ≠ Rel.bot τ ∧ □ (∀ Y : τ, Rel.le W Y ∨ Rel.le W (Rel.neg Y))
/-- `strong-leibniz-r` at `τ`: every possible entity is entailed by a strong world. -/
def StrongLeibniz (τ : Type) [Rel τ] : Prop :=
  ∀ X : τ, X ≠ Rel.bot τ → ∃ W : τ, SWorld W ∧ Rel.le W X
/-- `strong-leibniz-t`. -/
def StrongLeibnizT : Prop := StrongLeibniz Prop
/-- `necessary-strong-leibniz-r` at `τ`. -/
def NecStrongLeibniz (τ : Type) [Rel τ] : Prop := □ (StrongLeibniz τ)
/-- `necessary-strong-leibniz-t`. -/
def NecStrongLeibnizT : Prop := □ StrongLeibnizT

/-- `□_≠p := ∃q. q ∧ □(◇q → p)`, the distinctness-preserving necessity (Classicism, §2.6). -/
def BoxNe (p : Prop) : Prop := ∃ q : Prop, q ∧ □ (◇ q → p)
/-- `distinctness-preserving-collapse`: `∀p. p → □_≠p`. -/
def DistinctnessPreservingCollapse : Prop := ∀ p : Prop, p → BoxNe p

/-- `broad-necessitism-r` at `σ`: `∀x. □∃y. y = x`. -/
def BroadNecessitism (σ : Type) [Ty σ] : Prop := ∀ x : σ, □ (∃ y : σ, y = x)

/-! ### Transversals, Vicinity, Weak Inextensibility, Modalized Plenitude (25–28 September) -/

/-- `Equiv(R)`: `R` is reflexive, symmetric and transitive, at the evaluation point. -/
def EquivRel {σ : Type} [Ty σ] (R : σ → σ → Prop) : Prop :=
  (∀ x, R x x) ∧ (∀ x y, R x y → R y x) ∧ (∀ x y z, R x y → R y z → R x z)

/-- `transversal-r` at `σ`: a property of properties picks out exactly one property from
each coextension class. -/
def Transversal (σ : Type) [Ty σ] : Prop :=
  ∃ F : (σ → Prop) → Prop, ∀ X : σ → Prop, ∃ Y : σ → Prop,
    F Y ∧ (∀ z, X z ↔ Y z) ∧ ∀ Y' : σ → Prop, (F Y' ∧ ∀ z, X z ↔ Y' z) → Y' = Y
/-- `necessary-transversal-r` at `σ`: the instance boxed. -/
def NecTransversal (σ : Type) [Ty σ] : Prop := □ (Transversal σ)

/-- `transversal-choice-r` at `σ`: every equivalence relation has a transversal, a
property with exactly one instance in each cell. -/
def TransversalChoice (σ : Type) [Ty σ] : Prop :=
  ∀ R : σ → σ → Prop, EquivRel R →
    ∃ F : σ → Prop, ∀ x, ∃ y, R x y ∧ F y ∧ ∀ z, (R x z ∧ F z) → y = z
/-- `necessary-transversal-choice-r` at `σ`: the instance boxed. -/
def NecTransversalChoice (σ : Type) [Ty σ] : Prop := □ (TransversalChoice σ)

/-- `weakly-inextensible-comprehension-r` at `τ`: every relation, including a proposition,
is coextensive with a weakly inextensible one. -/
def WeaklyInextensibleComprehension (τ : Type) [Rel τ] : Prop :=
  ∀ X : τ, ∃ Y : τ, WeaklyInextensible Y ∧ coext X Y
/-- `necessary-weakly-inextensible-comprehension-r` at `τ`: the instance boxed. -/
def NecWeaklyInextensibleComprehension (τ : Type) [Rel τ] : Prop :=
  □ (WeaklyInextensibleComprehension τ)

/-- `vicinity`: `∃p. p ∧ ∀q. q → p ≤ ◇q`, a true proposition entails the possibility of
each truth. -/
def Vicinity : Prop := ∃ p : Prop, p ∧ ∀ q : Prop, q → Rel.le p (◇ q)
/-- `necessary-vicinity`: Vicinity boxed. -/
def NecVicinity : Prop := □ Vicinity

/-- `modalized-plenitude-r` at `σ`, `τ`: if necessarily each argument has a value that is
necessarily the relation's unique value for it, some operation necessarily represents the
relation; the output type `τ` is relational. -/
def ModalizedPlenitude (σ τ : Type) [Ty σ] [Rel τ] : Prop :=
  ∀ U : σ → τ → Prop, □ (∀ x, ∃ y, □ (U x y ∧ ∀ z, U x z → y = z)) →
    ∃ X : σ → τ, □ (∀ x y, U x y ↔ y = X x)

/-! ### Infinity, and Countable Boolean Completeness (2 October)

With the finite cardinalities and countability of the Background (`Cardinality.lean`). -/

/-- The Axiom of Infinity at `σ`: `¬∃Z. FiniteCardinality_σ(Z) ∧ Z(λu. ⊤)`, no finite
cardinality holds of the universal property. -/
def AxiomOfInfinity (σ : Type) [Ty σ] : Prop :=
  ¬ ∃ Z : (σ → Prop) → Prop, FiniteCardinality Z ∧ Z (λ _ ↦ True)
/-- `axiom-of-infinity-e`: there are not finitely many individuals. -/
def AxiomOfInfinityE : Prop := AxiomOfInfinity e
/-- `axiom-of-infinity-t`: there are not finitely many propositions. -/
def AxiomOfInfinityT : Prop := AxiomOfInfinity Prop
/-- `possible-infinity-e`: the Axiom of Infinity at `e`, under a diamond. -/
def PossibleInfinityE : Prop := ◇ AxiomOfInfinityE
/-- `possible-infinity-t`: the Axiom of Infinity at `t`, under a diamond. -/
def PossibleInfinityT : Prop := ◇ AxiomOfInfinityT

/-- `countable-boolean-completeness-r` at `τ`: every countable property of entities of the
type has a least upper bound. -/
def CountableBooleanCompleteness (τ : Type) [Rel τ] : Prop :=
  ∀ X : τ → Prop, Ctbl X → ∃ y : τ, LUB y X

end Classicism.P
