import Classicism.Paper

/-!
# Finite cardinalities and countability

The Background of `topics/classicism` defines, at a type `σ`,

    𝟎_σ                  := λX. ∀u. ¬Xu
    Suc_σ(Z)             := λX. ∃y. Xy ∧ Z(λu. Xu ∧ u ≠ y)
    FiniteCardinality_σ(Z) := ∀W. (W𝟎_σ ∧ ∀Y. WY → W(Suc_σ Y)) → WZ

so `𝟎_σ` is the cardinality of the empty property, `Suc_σ` adds one, and the finite
cardinalities are those reached from `𝟎_σ` by finitely many successors, in the
impredicative sense: they have every property of cardinalities that `𝟎_σ` has and that
passes from a cardinality to its successor. Every type here ends in `t`, so no type `σσ` is
needed. The Axioms of Infinity (`Principles.lean`) say that no finite cardinality holds of
the universal property.

Following Goodsell's *Arithmetic is Necessary*, the numbers are the finite cardinalities
of individuals, of type `ν := (e → t) → t`, and a property `X` is countable when it
injects into them:

    Ctbl_τ(X) := ∃R^{τνt}. ∀y z. Xy ∧ Xz → ((∃n ∈ ℕ. Ryn ∧ Rzn) ↔ y = z)

with `n ∈ ℕ` for `FiniteCardinality_e(n)`. Countable Boolean Completeness uses it.
-/

namespace Classicism

/-- `𝟎_σ := λX. ∀u. ¬Xu`, the cardinality of the empty property. -/
def ZeroCard (σ : Type) [Ty σ] : (σ → Prop) → Prop := λ X ↦ ∀ u, ¬ X u

/-- `Suc_σ Z := λX. ∃y. Xy ∧ Z(λu. Xu ∧ u ≠ y)`, one more than the cardinality `Z`. -/
def SucCard {σ : Type} [Ty σ] (Z : (σ → Prop) → Prop) : (σ → Prop) → Prop :=
  λ X ↦ ∃ y, X y ∧ Z (λ u ↦ X u ∧ u ≠ y)

/-- `FiniteCardinality_σ(Z)`: `Z` has every property of cardinalities that `𝟎_σ` has and
that passes from a cardinality to its successor. -/
def FiniteCardinality {σ : Type} [Ty σ] (Z : (σ → Prop) → Prop) : Prop :=
  ∀ W : ((σ → Prop) → Prop) → Prop, (W (ZeroCard σ) ∧ ∀ Y, W Y → W (SucCard Y)) → W Z

/-- `Ctbl_τ(X)`: `X` injects into the natural numbers, the finite cardinalities of
individuals. -/
def Ctbl {τ : Type} [Ty τ] (X : τ → Prop) : Prop :=
  ∃ R : τ → ((e → Prop) → Prop) → Prop, ∀ y z : τ, X y ∧ X z →
    ((∃ n, FiniteCardinality n ∧ R y n ∧ R z n) ↔ y = z)

end Classicism
