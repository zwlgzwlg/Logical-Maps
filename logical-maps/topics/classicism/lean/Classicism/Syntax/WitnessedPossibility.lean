import Classicism.Syntax.SentenceSchemas
import Classicism.Syntax.Blocks
import Classicism.Syntax.Pure
import Classicism.Syntax.Constants

/-!
# Sentence schemas with constants put for variables

Witnessed Possibility and its kin, Logical Necessity and Modal Freedom: the schemas of a
signature `Σ` over a pure formula `P` whose free variables are among a block `x̄`, with
distinct constants `c̄` of `Σ` of the matching types put for `x̄`, written `P[c̄/x̄]`
(`Term.atConsts`). A list `cs` of constants with no repetition is the tuple `c̄`, and the
block's types are theirs, `cs.map Sig.typeOf`; `P` is a formula of the pure language in
that block, read in `Σ`.

- **Witnessed Possibility**: `(∃x̄. P) → ◇P[c̄/x̄]`.
- **Converse Witnessed Possibility**: `◇P[c̄/x̄] → ∃x̄. P`.
- **Possibly Witnessed Possibility**: `◇(∃x̄. P) → ◇P[c̄/x̄]`.
- **Logical Necessity**: `□P[c̄/x̄] ↔ ∀x̄. P`.
- **Modal Freedom**: `◇P[c̄/x̄] ∧ ◇Q[d̄/ȳ] → ◇(P[c̄/x̄] ∧ Q[d̄/ȳ])`, the constants `c̄d̄`
  all distinct.

The empty tuple is included, so each schema has an instance at every closed pure sentence.
What follows from them is in `Results/SentenceSchemas/WitnessedPossibility.lean`.

Also here, **Separated Structure** (Classicism, §2.5, pp. 38–39): `Fc = Gc → F = G`, for a
constant `c` of `Σ` and closed terms `F`, `G` of `Σ`'s language not containing `c`; and
**Independence**: `c ≠ A d₁ … dₙ`, for a closed pure term `A` and distinct constants
`c, d₁, …, dₙ`, `n ≥ 0`. The constant `c` has the relational type `ρ` of `A d₁ … dₙ`, and
`c` is read at that type through the equation of the types.
-/

namespace Classicism.Meta

variable {Sig : Signature}

/-- The constants of a list, as a tuple of closed terms of their types. -/
def Terms.consts : (cs : List Sig.Const) → Terms Sig [] (cs.map Sig.typeOf)
  | [] => .nil
  | c :: cs => .cons (.const c) (Terms.consts cs)

namespace Term

/-- `P[c̄/x̄]`: a pure formula with its free variables among a block, read in the signature,
with the constants `c̄` put for the block's variables. -/
def atConsts (cs : List Sig.Const) (P : Formula Signature.pure (Ctx.block (cs.map Sig.typeOf) [])) :
    Sentence Sig :=
  (Term.ofPure P).subst (Sub.consBlock (Terms.consts cs) Sub.id)

/-- With no constants, `P[c̄/x̄]` is `P`, read in the signature. -/
theorem atConsts_nil (P : Formula Signature.pure []) : atConsts (Sig := Sig) [] P = Term.ofPure P :=
  Term.subst_id _

/-- Reading into a signature commutes with the block quantifiers. -/
theorem ofPure_existsBlock : ∀ (σs : List Ty) {Γ : Ctx} (P : Formula Signature.pure (Ctx.block σs Γ)),
    Term.ofPure (Sig := Sig) (existsBlock σs P) = existsBlock σs (Term.ofPure P)
  | [], _, _ => rfl
  | _ :: σs, _, P => by
    show Term.ofPure (exists' (existsBlock σs P)) = exists' (existsBlock σs (Term.ofPure P))
    rw [← ofPure_existsBlock σs P]; rfl

theorem ofPure_forallBlock : ∀ (σs : List Ty) {Γ : Ctx} (P : Formula Signature.pure (Ctx.block σs Γ)),
    Term.ofPure (Sig := Sig) (forallBlock σs P) = forallBlock σs (Term.ofPure P)
  | [], _, _ => rfl
  | _ :: σs, _, P => by
    show Term.ofPure (forall' (forallBlock σs P)) = forall' (forallBlock σs (Term.ofPure P))
    rw [← ofPure_forallBlock σs P]; rfl

end Term

namespace AxiomSet

variable (Sig)

/-- **Witnessed Possibility** for the signature: `(∃x̄. P) → ◇P[c̄/x̄]`, for `P` pure with
its free variables among `x̄` and `c̄` distinct constants of the matching types. -/
def witnessedPossibility : AxiomSet Sig := fun a =>
  ∃ (cs : List Sig.Const) (P : Formula Signature.pure (Ctx.block (cs.map Sig.typeOf) [])),
    cs.Nodup ∧ a = Term.imp (Term.ofPure (Term.existsBlock _ P)) (Term.dia (Term.atConsts cs P))

/-- **Converse Witnessed Possibility**: `◇P[c̄/x̄] → ∃x̄. P`. -/
def converseWitnessedPossibility : AxiomSet Sig := fun a =>
  ∃ (cs : List Sig.Const) (P : Formula Signature.pure (Ctx.block (cs.map Sig.typeOf) [])),
    cs.Nodup ∧ a = Term.imp (Term.dia (Term.atConsts cs P)) (Term.ofPure (Term.existsBlock _ P))

/-- **Possibly Witnessed Possibility**: `◇(∃x̄. P) → ◇P[c̄/x̄]`. -/
def possiblyWitnessedPossibility : AxiomSet Sig := fun a =>
  ∃ (cs : List Sig.Const) (P : Formula Signature.pure (Ctx.block (cs.map Sig.typeOf) [])),
    cs.Nodup ∧
      a = Term.imp (Term.dia (Term.ofPure (Term.existsBlock _ P))) (Term.dia (Term.atConsts cs P))

/-- **Logical Necessity**: `□P[c̄/x̄] ↔ ∀x̄. P`. -/
def logicalNecessity : AxiomSet Sig := fun a =>
  ∃ (cs : List Sig.Const) (P : Formula Signature.pure (Ctx.block (cs.map Sig.typeOf) [])),
    cs.Nodup ∧ a = Term.iff (Term.box (Term.atConsts cs P)) (Term.ofPure (Term.forallBlock _ P))

/-- **Modal Freedom**: `◇P[c̄/x̄] ∧ ◇Q[d̄/ȳ] → ◇(P[c̄/x̄] ∧ Q[d̄/ȳ])`, for `P` and `Q` pure,
with their free variables among disjoint blocks, and the constants `c̄d̄` distinct. -/
def modalFreedom : AxiomSet Sig := fun a =>
  ∃ (cs ds : List Sig.Const) (P : Formula Signature.pure (Ctx.block (cs.map Sig.typeOf) []))
    (Q : Formula Signature.pure (Ctx.block (ds.map Sig.typeOf) [])),
    (cs ++ ds).Nodup ∧
      a = Term.imp (Term.conj (Term.dia (Term.atConsts cs P)) (Term.dia (Term.atConsts ds Q)))
        (Term.dia (Term.conj (Term.atConsts cs P) (Term.atConsts ds Q)))

/-- **Separated Structure**: `Fc = Gc → F = G`, for a constant `c` and closed terms `F`, `G`
not containing it. -/
def separatedStructure : AxiomSet Sig := fun a =>
  ∃ (c : Sig.Const) (ρ : RTy) (F G : Term Sig [] (Sig.typeOf c ⇒ ρ)),
    c ∉ F.consts ∧ c ∉ G.consts ∧
      a = Term.imp (Term.eq' (Term.app F (Term.const c)) (Term.app G (Term.const c))) (Term.eq' F G)

/-- **Independence**: `c ≠ A d₁ … dₙ`, for a closed pure term `A` and distinct constants
`c, d₁, …, dₙ`. -/
def independence : AxiomSet Sig := fun a =>
  ∃ (c : Sig.Const) (ds : List Sig.Const) (ρ : RTy) (h : Sig.typeOf c = Ty.rel ρ)
    (A : Term Signature.pure [] (ds.map Sig.typeOf ⇒* ρ)),
    (c :: ds).Nodup ∧
      a = Term.neg (Term.eq' (h ▸ Term.const c) (Term.appBlock (Term.ofPure A) (Terms.consts ds)))

end AxiomSet

end Classicism.Meta
