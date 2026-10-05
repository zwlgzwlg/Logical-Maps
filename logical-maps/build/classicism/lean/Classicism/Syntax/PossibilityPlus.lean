import Classicism.Syntax.ClosedTypes
import Classicism.Syntax.Conservativity
import Classicism.Syntax.Blocks
import Classicism.Syntax.Constants

/-!
# Possibility+

The strengthening of Possibility Maximalism to open formulas whose free variables are
individual variables (Classicism, §2.5, p. 41):

- **Possibility+ (pure)**: `∀x₁ … xₙ. (⋀_{i<j} xᵢ ≠ xⱼ) → ◇P`, for `P` pure, its free
  variables among the individual variables `x₁ … xₙ`, and consistent with `C`; `n ≥ 0`.
- **Possibility+ (signature `Σ`)**: the same for `P` in `Σ`'s language, consistent with
  `C(Σ)`, with `xᵢ ≠ c` added to the antecedent for each individual constant `c` in `P`.

An open formula is consistent with the theory when it is so with its variables read as new
constants, that is, when its existential closure `∃x̄. P` is consistent.

The individual constants in the antecedent of Possibility+ for `Σ` are given as a list
`ds` that includes those in `P` (`AxiomSet.possibilityPlusSig`): an instance with more is
weaker than the one with exactly those, which is among the instances, so the schema is
equivalent to the one with exactly those. With `ds` empty the antecedent is the pure one,
so that the pure schema read in `Σ` is part of the schema for `Σ`
(`ofPure_possibilityPlus_subset`).
-/

namespace Classicism.Meta

variable {Sig : Signature}

/-- An individual constant, as a term of type `e`. -/
abbrev IndConst (Sig : Signature) : Type := {c : Sig.Const // Sig.typeOf c = Ty.e}

namespace Term

/-- An individual constant, as a term of type `e`. -/
def indConst {Γ : Ctx} (c : IndConst Sig) : Term Sig Γ Ty.e := c.2 ▸ Term.const c.1

/-- `a ≠ x₁ ∧ … ∧ a ≠ xₙ`, `⊤` for `n = 0`. -/
def neAll {Γ : Ctx} {σ : Ty} (a : Term Sig Γ σ) : (n : Nat) → Terms Sig Γ (List.replicate n σ) →
    Formula Sig Γ
  | 0, _ => top
  | n + 1, xs => conj (neg (eq' a xs.head)) (neAll a n xs.tail)

/-- `x₁ ≠ b ∧ … ∧ xₙ ≠ b`, `⊤` for `n = 0`. -/
def allNe {Γ : Ctx} : (n : Nat) → Terms Sig Γ (List.replicate n Ty.e) → Term Sig Γ Ty.e →
    Formula Sig Γ
  | 0, _, _ => top
  | n + 1, xs, b => conj (neg (eq' xs.head b)) (allNe n xs.tail b)

/-- `⋀_{i<j} xᵢ ≠ xⱼ`: the entities of a tuple pairwise distinct. -/
def distinct {Γ : Ctx} {σ : Ty} : (n : Nat) → Terms Sig Γ (List.replicate n σ) → Formula Sig Γ
  | 0, _ => top
  | n + 1, xs => conj (neAll xs.head n xs.tail) (distinct n xs.tail)

/-- `D` with `⋀ᵢ xᵢ ≠ c` conjoined for each constant `c` of the list. -/
def neConsts {Γ : Ctx} (n : Nat) (xs : Terms Sig Γ (List.replicate n Ty.e)) :
    List (IndConst Sig) → Formula Sig Γ → Formula Sig Γ
  | [], D => D
  | c :: ds, D => conj (allNe n xs (indConst c)) (neConsts n xs ds D)

/-- An individual constant is in the paper's language: its type is `e`. -/
theorem closedTypes_indConst {Γ : Ctx} (c : IndConst Sig) :
    (indConst c : Term Sig Γ Ty.e).closedTypes = true := by
  obtain ⟨c, h⟩ := c
  have : ∀ {τ : Ty} (h : Sig.typeOf c = τ), (h ▸ Term.const c : Term Sig Γ τ).closedTypes =
      decide τ.Closed := by
    intro τ h; subst h; rfl
  exact (this h).trans (by simp)

/-- With no variables, the conjunction for the constants is `⊤ ∧ … ∧ ⊤`, in the paper's
language. -/
theorem closedTypes_neConsts_zero {Γ : Ctx} :
    ∀ ds : List (IndConst Sig), (neConsts 0 (.nil : Terms Sig Γ []) ds top).closedTypes = true
  | [] => rfl
  | _ :: ds => by
    simp only [neConsts, allNe, closedTypes_conj, closedTypes_neConsts_zero ds, Bool.and_true]
    rfl

end Term

/-- A tuple of terms of the pure language, read in a signature. -/
def Terms.ofPure {Γ : Ctx} : {σs : List Ty} → Terms Signature.pure Γ σs → Terms Sig Γ σs
  | [], .nil => .nil
  | _ :: _, .cons a as => .cons (Term.ofPure a) (Terms.ofPure as)

theorem Terms.ofPure_vars : ∀ (σs : List Ty) (Γ : Ctx),
    Terms.ofPure (Sig := Sig) (Terms.vars σs Γ) = Terms.vars σs Γ
  | [], _ => rfl
  | σ :: σs, Γ => by
    show Terms.cons (Term.ofPure ((Term.var .zero : Term Signature.pure (σ :: Γ) σ).rename (Ren.wkBlock σs)))
        (Terms.ofPure (Terms.vars σs (σ :: Γ))) = _
    rw [Term.ofPure_rename, Terms.ofPure_vars σs (σ :: Γ)]; rfl

namespace Term

theorem ofPure_neAll {Γ : Ctx} {σ : Ty} (a : Term Signature.pure Γ σ) : ∀ (n : Nat)
    (xs : Terms Signature.pure Γ (List.replicate n σ)),
    Term.ofPure (Sig := Sig) (neAll a n xs) = neAll (Term.ofPure a) n (Terms.ofPure xs)
  | 0, _ => rfl
  | n + 1, .cons x xs => by
    show conj (neg (eq' (Term.ofPure a) (Term.ofPure x))) (Term.ofPure (neAll a n xs)) = _
    rw [ofPure_neAll a n xs]; rfl

theorem ofPure_distinct {Γ : Ctx} {σ : Ty} : ∀ (n : Nat) (xs : Terms Signature.pure Γ (List.replicate n σ)),
    Term.ofPure (Sig := Sig) (distinct n xs) = distinct n (Terms.ofPure xs)
  | 0, _ => rfl
  | n + 1, .cons x xs => by
    show conj (Term.ofPure (neAll x n xs)) (Term.ofPure (distinct n xs)) = _
    rw [ofPure_neAll, ofPure_distinct n xs]; rfl

end Term

namespace AxiomSet

variable (Sig)

/-- **Possibility+**, for the pure formulas of a signature's language:
`∀x₁ … xₙ. (⋀_{i<j} xᵢ ≠ xⱼ) → ◇P`, for `P` pure with its free variables among the
individual variables `x̄`, and `∃x̄. P` consistent; at the pure signature, the map's
Possibility+ (pure). -/
def possibilityPlus : AxiomSet Sig := fun a => a.closedTypes = true ∧
  ∃ (n : Nat) (P : Formula Sig (Ctx.block (List.replicate n Ty.e) [])),
    P.pure = true ∧ Consistent (single (Term.existsBlock _ P)) ∧
      a = Term.forallBlock _ (Term.imp (Term.distinct n (Terms.vars _ [])) (Term.dia P))

/-- **Possibility+ for the signature**: `∀x₁ … xₙ. (⋀_{i<j} xᵢ ≠ xⱼ ∧ ⋀_{i,c} xᵢ ≠ c) → ◇P`,
for `P` in the signature's language with its free variables among the individual
variables `x̄`, `∃x̄. P` consistent, and `c` over a list of individual constants that
includes those in `P`. -/
def possibilityPlusSig : AxiomSet Sig := fun a => a.closedTypes = true ∧
  ∃ (n : Nat) (P : Formula Sig (Ctx.block (List.replicate n Ty.e) [])) (ds : List (IndConst Sig)),
    (∀ c ∈ P.consts, ∀ h : Sig.typeOf c = Ty.e, ⟨c, h⟩ ∈ ds) ∧
    Consistent (single (Term.existsBlock _ P)) ∧
      a = Term.forallBlock _ (Term.imp
        (Term.neConsts n (Terms.vars _ []) ds (Term.distinct n (Terms.vars _ []))) (Term.dia P))

end AxiomSet

end Classicism.Meta
