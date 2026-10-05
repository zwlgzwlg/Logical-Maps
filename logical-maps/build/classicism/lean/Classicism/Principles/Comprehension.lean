import Classicism.Paper
import Classicism.Comprehension
import Classicism.Lattice

/-!
# Principles of the map's category `comprehension`

Each says that every relation of the type, including a proposition, is coextensive with
one of the stated kind. The map's `∀ᵀʸ σ̄` over argument tuples is the parameter `τ`,
since a relational type *is* a tuple type ending in `t`. See `Classicism/Principles.lean`
for how a principle is stated and where its forms go.
-/

namespace Classicism.P
open Classicism.Paper

/-- `rigid-comprehension-r` at `τ`. -/
def RigidComprehension (τ : Type) [Rel τ] : Prop :=
  ∀ X : τ, ∃ Y : τ, Rigid Y ∧ coext X Y
/-- `necessary-rigid-comprehension-r` at `τ`: the instance boxed. -/
def NecRigidComprehension (τ : Type) [Rel τ] : Prop := □ (RigidComprehension τ)
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
/-- `weakly-inextensible-comprehension-r` at `τ`: every relation, including a proposition,
is coextensive with a weakly inextensible one. -/
def WeaklyInextensibleComprehension (τ : Type) [Rel τ] : Prop :=
  ∀ X : τ, ∃ Y : τ, WeaklyInextensible Y ∧ coext X Y
/-- `necessary-weakly-inextensible-comprehension-r` at `τ`: the instance boxed. -/
def NecWeaklyInextensibleComprehension (τ : Type) [Rel τ] : Prop :=
  □ (WeaklyInextensibleComprehension τ)

/-- `gallin-extensional-comprehension-r` at `τ`: every relation is coextensive with one
that is persistent and has a persistent pointwise negation. Gallin's rigidity convention. -/
def GallinExtensionalComprehension (τ : Type) [Rel τ] : Prop :=
  ∀ X : τ, ∃ Y : τ, Persistent Y ∧ Persistent (¬ Y) ∧ coext X Y
/-- `necessary-gallin-extensional-comprehension-r` at `τ`: the instance boxed. -/
def NecGallinExtensionalComprehension (τ : Type) [Rel τ] : Prop :=
  □ (GallinExtensionalComprehension τ)

end Classicism.P
