import Classicism.Comprehension
import Classicism.Lattice

/-!
# Principle statements

One definition per principle of the map that this first step covers, named as the map's
`lean_def` convention expects (`Classicism.P.<Name>`).

## Principles are families of formulas, indexed by types

The map's metalinguistic quantifier `∀ᵀʸ σ` ranges over *types*, and a principle is a
**schema**: a family of formulas, one for each choice of types. No formula of the paper's
language quantifies over types, so a schema is not itself a formula, and it is not
rendered here as one Lean proposition quantifying over types. Each principle takes its
types as **explicit parameters** and is a formula once they are fixed: `Functionality σ τ`
is `(∀z. Xz = Yz) → X = Y` for `X Y : σ → τ`, and `Barcan Prop` is BF at type `t`. The
guards `[Ty σ]`, `[Rel τ]` are the map's side conditions on the types.

This is what the type-system check enforces: a binder over a type may be a parameter of a
declaration, never a quantifier inside a formula. A record about principles is then an
implication between *instances*, with the types the argument needs as parameters, which
the paper reads as a metatheorem and which keeps every certified statement within the
strict layer's reach.

`□S` for a schema `S` is likewise the family of `□`-prefixed instances, so a boxed
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
/-- `gallin-extensional-comprehension-r` at `τ`: every relation is coextensive with one
that is persistent and has a persistent pointwise negation. Gallin's rigidity convention. -/
def GallinExtensionalComprehension (τ : Type) [Rel τ] : Prop :=
  ∀ X : τ, ∃ Y : τ, Persistent Y ∧ Persistent (Rel.neg Y) ∧ coext X Y

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

end Classicism.P
