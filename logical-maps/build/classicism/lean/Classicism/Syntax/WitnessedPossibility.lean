import Classicism.Syntax.ClosedTypes
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

/-- Putting constants for a block of variables changes no type in a formula: each constant
has the type of its variable. So `P[c̄/x̄]` is in the paper's language just when `P` is. -/
theorem closedTypes_atConsts (cs : List Sig.Const)
    (P : Formula Signature.pure (Ctx.block (cs.map Sig.typeOf) [])) :
    (atConsts cs P).closedTypes = P.closedTypes := by
  have keeps : ∀ (cs : List Sig.Const) {Γ : Ctx} (s : Sub Sig Γ []), s.KeepsTypes →
      (Sub.consBlock (Terms.consts cs) s).KeepsTypes := by
    intro cs
    induction cs with
    | nil => intro _ s h; exact h
    | cons c cs ih => intro _ s h; exact ih _ (Sub.KeepsTypes.cons rfl h)
  unfold atConsts
  rw [closedTypes_subst _ (keeps cs _ Sub.KeepsTypes.id), closedTypes_ofPure]

/-- Putting constants for a block of variables commutes with negation and conjunction. -/
theorem atConsts_neg (cs : List Sig.Const)
    (P : Formula Signature.pure (Ctx.block (cs.map Sig.typeOf) [])) :
    atConsts cs (neg P) = neg (atConsts cs P) := rfl

theorem atConsts_conj (cs : List Sig.Const)
    (P Q : Formula Signature.pure (Ctx.block (cs.map Sig.typeOf) [])) :
    atConsts cs (conj P Q) = conj (atConsts cs P) (atConsts cs Q) := rfl

/-- The block quantifiers keep a formula in the paper's language when the block's types are
closed. -/
theorem closedTypes_existsBlock : ∀ (σs : List Ty) {Γ : Ctx} (P : Formula Sig (Ctx.block σs Γ)),
    (existsBlock σs P).closedTypes = (σs.all (fun σ => decide σ.Closed) && P.closedTypes)
  | [], _, _ => by simp [existsBlock]
  | σ :: σs, _, P => by
    simp only [existsBlock, closedTypes_exists', closedTypes_existsBlock σs P, List.all_cons,
      Bool.and_assoc]

theorem closedTypes_forallBlock : ∀ (σs : List Ty) {Γ : Ctx} (P : Formula Sig (Ctx.block σs Γ)),
    (forallBlock σs P).closedTypes = (σs.all (fun σ => decide σ.Closed) && P.closedTypes)
  | [], _, _ => by simp [forallBlock]
  | σ :: σs, _, P => by
    simp only [forallBlock, closedTypes_forall', closedTypes_forallBlock σs P, List.all_cons,
      Bool.and_assoc]

theorem closedTypes_forallBlock_eq_existsBlock (σs : List Ty) {Γ : Ctx}
    (P : Formula Sig (Ctx.block σs Γ)) :
    (forallBlock σs P).closedTypes = (existsBlock σs P).closedTypes := by
  rw [closedTypes_forallBlock, closedTypes_existsBlock]

end Term

namespace AxiomSet

variable (Sig)

/-- **Witnessed Possibility** for the signature: `(∃x̄. P) → ◇P[c̄/x̄]`, for `P` pure with
its free variables among `x̄` and `c̄` distinct constants of the matching types. -/
def witnessedPossibility : AxiomSet Sig := fun a => a.closedTypes = true ∧
  ∃ (cs : List Sig.Const) (P : Formula Signature.pure (Ctx.block (cs.map Sig.typeOf) [])),
    cs.Nodup ∧ a = Term.imp (Term.ofPure (Term.existsBlock _ P)) (Term.dia (Term.atConsts cs P))

/-- **Converse Witnessed Possibility**: `◇P[c̄/x̄] → ∃x̄. P`. -/
def converseWitnessedPossibility : AxiomSet Sig := fun a => a.closedTypes = true ∧
  ∃ (cs : List Sig.Const) (P : Formula Signature.pure (Ctx.block (cs.map Sig.typeOf) [])),
    cs.Nodup ∧ a = Term.imp (Term.dia (Term.atConsts cs P)) (Term.ofPure (Term.existsBlock _ P))

/-- **Possibly Witnessed Possibility**: `◇(∃x̄. P) → ◇P[c̄/x̄]`. -/
def possiblyWitnessedPossibility : AxiomSet Sig := fun a => a.closedTypes = true ∧
  ∃ (cs : List Sig.Const) (P : Formula Signature.pure (Ctx.block (cs.map Sig.typeOf) [])),
    cs.Nodup ∧
      a = Term.imp (Term.dia (Term.ofPure (Term.existsBlock _ P))) (Term.dia (Term.atConsts cs P))

/-- **Logical Necessity**: `□P[c̄/x̄] ↔ ∀x̄. P`. -/
def logicalNecessity : AxiomSet Sig := fun a => a.closedTypes = true ∧
  ∃ (cs : List Sig.Const) (P : Formula Signature.pure (Ctx.block (cs.map Sig.typeOf) [])),
    cs.Nodup ∧ a = Term.iff (Term.box (Term.atConsts cs P)) (Term.ofPure (Term.forallBlock _ P))

/-- **Modal Freedom**: `◇P[c̄/x̄] ∧ ◇Q[d̄/ȳ] → ◇(P[c̄/x̄] ∧ Q[d̄/ȳ])`, for `P` and `Q` pure,
with their free variables among disjoint blocks, and the constants `c̄d̄` distinct. -/
def modalFreedom : AxiomSet Sig := fun a => a.closedTypes = true ∧
  ∃ (cs ds : List Sig.Const) (P : Formula Signature.pure (Ctx.block (cs.map Sig.typeOf) []))
    (Q : Formula Signature.pure (Ctx.block (ds.map Sig.typeOf) [])),
    (cs ++ ds).Nodup ∧
      a = Term.imp (Term.conj (Term.dia (Term.atConsts cs P)) (Term.dia (Term.atConsts ds Q)))
        (Term.dia (Term.conj (Term.atConsts cs P) (Term.atConsts ds Q)))

/-! ### Membership

An instance of each schema from its formula and constants: it is in the paper's language
when `∃x̄. P` is, the block's types and `P`'s being closed (`P[c̄/x̄]` has the types of `P`,
`Term.closedTypes_atConsts`). -/

variable {Sig}

theorem closedTypes_of_existsBlock {σs : List Ty} {P : Formula Signature.pure (Ctx.block σs [])}
    (h : (Term.existsBlock σs P).closedTypes = true) : P.closedTypes = true := by
  rw [Term.closedTypes_existsBlock, Bool.and_eq_true] at h; exact h.2

theorem closedTypes_existsBlock_neg {σs : List Ty} (P : Formula Signature.pure (Ctx.block σs [])) :
    (Term.existsBlock σs (Term.neg P)).closedTypes = (Term.existsBlock σs P).closedTypes := by
  rw [Term.closedTypes_existsBlock, Term.closedTypes_existsBlock, Term.closedTypes_neg]

theorem witnessedPossibility_mem {cs : List Sig.Const}
    {P : Formula Signature.pure (Ctx.block (cs.map Sig.typeOf) [])} (hcs : cs.Nodup)
    (h : (Term.existsBlock _ P).closedTypes = true) :
    witnessedPossibility Sig
      (Term.imp (Term.ofPure (Term.existsBlock _ P)) (Term.dia (Term.atConsts cs P))) :=
  ⟨by simp [Term.closedTypes_atConsts, h, closedTypes_of_existsBlock h], cs, P, hcs, rfl⟩

theorem converseWitnessedPossibility_mem {cs : List Sig.Const}
    {P : Formula Signature.pure (Ctx.block (cs.map Sig.typeOf) [])} (hcs : cs.Nodup)
    (h : (Term.existsBlock _ P).closedTypes = true) :
    converseWitnessedPossibility Sig
      (Term.imp (Term.dia (Term.atConsts cs P)) (Term.ofPure (Term.existsBlock _ P))) :=
  ⟨by simp [Term.closedTypes_atConsts, h, closedTypes_of_existsBlock h], cs, P, hcs, rfl⟩

theorem possiblyWitnessedPossibility_mem {cs : List Sig.Const}
    {P : Formula Signature.pure (Ctx.block (cs.map Sig.typeOf) [])} (hcs : cs.Nodup)
    (h : (Term.existsBlock _ P).closedTypes = true) :
    possiblyWitnessedPossibility Sig
      (Term.imp (Term.dia (Term.ofPure (Term.existsBlock _ P))) (Term.dia (Term.atConsts cs P))) :=
  ⟨by simp [Term.closedTypes_atConsts, h, closedTypes_of_existsBlock h], cs, P, hcs, rfl⟩

theorem logicalNecessity_mem {cs : List Sig.Const}
    {P : Formula Signature.pure (Ctx.block (cs.map Sig.typeOf) [])} (hcs : cs.Nodup)
    (h : (Term.existsBlock _ P).closedTypes = true) :
    logicalNecessity Sig
      (Term.iff (Term.box (Term.atConsts cs P)) (Term.ofPure (Term.forallBlock _ P))) :=
  ⟨by simp [Term.closedTypes_atConsts, Term.closedTypes_forallBlock_eq_existsBlock, h,
    closedTypes_of_existsBlock h], cs, P, hcs, rfl⟩

theorem modalFreedom_mem {cs ds : List Sig.Const}
    {P : Formula Signature.pure (Ctx.block (cs.map Sig.typeOf) [])}
    {Q : Formula Signature.pure (Ctx.block (ds.map Sig.typeOf) [])} (hcs : (cs ++ ds).Nodup)
    (hP : P.closedTypes = true) (hQ : Q.closedTypes = true) :
    modalFreedom Sig
      (Term.imp (Term.conj (Term.dia (Term.atConsts cs P)) (Term.dia (Term.atConsts ds Q)))
        (Term.dia (Term.conj (Term.atConsts cs P) (Term.atConsts ds Q)))) :=
  ⟨by simp [Term.closedTypes_atConsts, hP, hQ], cs, ds, P, Q, hcs, rfl⟩

variable (Sig)

/-- **Separated Structure**: `Fc = Gc → F = G`, for a constant `c` and closed terms `F`, `G`
not containing it. -/
def separatedStructure : AxiomSet Sig := fun a => a.closedTypes = true ∧
  ∃ (c : Sig.Const) (ρ : RTy) (F G : Term Sig [] (Sig.typeOf c ⇒ ρ)),
    c ∉ F.consts ∧ c ∉ G.consts ∧
      a = Term.imp (Term.eq' (Term.app F (Term.const c)) (Term.app G (Term.const c))) (Term.eq' F G)

/-- **Independence**: `c ≠ A d₁ … dₙ`, for a closed pure term `A` and distinct constants
`c, d₁, …, dₙ`. -/
def independence : AxiomSet Sig := fun a => a.closedTypes = true ∧
  ∃ (c : Sig.Const) (ds : List Sig.Const) (ρ : RTy) (h : Sig.typeOf c = Ty.rel ρ)
    (A : Term Signature.pure [] (ds.map Sig.typeOf ⇒* ρ)),
    (c :: ds).Nodup ∧
      a = Term.neg (Term.eq' (h ▸ Term.const c) (Term.appBlock (Term.ofPure A) (Terms.consts ds)))

/-- **General Separated Structure**: `P[c̄/x̄] = Q[c̄/x̄] → λx̄. P = λx̄. Q`, for terms `P`, `Q` of
`Σ`'s language with their free variables among the block `x̄` and none of the distinct
constants `c̄` in them.

The map states it as `F a₁ ⋯ aₙ = G b₁ ⋯ bₘ → λx̄. F(πa₁) ⋯ (πaₙ) = λx̄. G(πb₁) ⋯ (πbₘ)`, for
closed `F`, `G` without the constants, `a`'s and `b`'s constants possibly repeated, and `π` a
bijection from `x̄` to the distinct ones. Each such instance is one of these, with
`P := F(πa₁) ⋯ (πaₙ)`, whose `P[c̄/x̄]` is `F a₁ ⋯ aₙ`; and each of these is equivalent in `C`,
by β, to one of the map's, with `F := λx̄. P` applied to the constants `c̄` in order. -/
def generalSeparatedStructure : AxiomSet Sig := fun a => a.closedTypes = true ∧
  ∃ (cs : List Sig.Const) (ρ : RTy) (P Q : Term Sig (Ctx.block (cs.map Sig.typeOf) []) ρ),
    cs.Nodup ∧ (∀ c ∈ cs, c ∉ P.consts ∧ c ∉ Q.consts) ∧
      a = Term.imp
        (Term.eq' (P.subst (Sub.consBlock (Terms.consts cs) Sub.id))
          (Q.subst (Sub.consBlock (Terms.consts cs) Sub.id)))
        (Term.eq' (Term.lamBlock _ P) (Term.lamBlock _ Q))

end AxiomSet

end Classicism.Meta
