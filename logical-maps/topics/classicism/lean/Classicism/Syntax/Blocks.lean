import Classicism.Syntax.Derivation

/-!
# Blocks of variables

The vocabulary for a *list* of types where the paper's language has one type: a block of
variables `x₁ … xₙ` in place of one variable, a function of `n` arguments in place of a
function of one, `∀x₁ … ∀xₙ` in place of `∀x`, and the conjunction `x₁ = y₁ ∧ … ∧ xₙ = yₙ`
in place of `x = y`. These are what the vectorization of `Syntax/Vectorize.lean` produces,
and the vocabulary in which the list forms of the map's principles are stated.

A block is added to a context by `List.reverseAux`: the block `σ₁ … σₙ` over `Γ` is
`σₙ :: … :: σ₁ :: Γ`, its last variable innermost, and adding `σ :: σs` over `Γ` *is*
adding `σs` over `σ :: Γ`, by definition. So every operation here is defined by recursion
on the list, the first type outermost, with no cast.

A one-element block is the unblocked form on the nose: `∀` over `[σ]` is `∀x:σ`, the
identity over `[σ]` is `x = y` (not `x = y ∧ ⊤`), and the block constants at `[σ]` are
the constants at `σ`. So vectorizing a type into a one-element list is type substitution,
with no conversion.
-/

namespace Classicism.Meta

variable {Sig : Signature}

/-! ### Block contexts, renamings and substitutions -/

/-- The context `Γ` extended by a block of variables of the types `σs`, the first
outermost: `List.reverseAux σs Γ`, written out so that it unfolds at reducible
transparency, as `rw` and `simp` need. -/
@[reducible] def Ctx.block : List Ty → Ctx → Ctx
  | [], Γ => Γ
  | σ :: σs, Γ => Ctx.block σs (σ :: Γ)

theorem Ctx.block_eq_reverseAux (σs : List Ty) (Γ : Ctx) : Ctx.block σs Γ = List.reverseAux σs Γ := by
  induction σs generalizing Γ with
  | nil => rfl
  | cons σ σs ih => exact ih (σ :: Γ)

@[simp] theorem Ctx.block_nil (Γ : Ctx) : Ctx.block [] Γ = Γ := rfl
@[simp] theorem Ctx.block_cons (σ : Ty) (σs : List Ty) (Γ : Ctx) :
    Ctx.block (σ :: σs) Γ = Ctx.block σs (σ :: Γ) := rfl

/-- Weakening past a block. -/
def Ren.wkBlock : ∀ (σs : List Ty) {Γ : Ctx}, Ren Γ (Ctx.block σs Γ)
  | [], _ => Ren.id
  | σ :: σs, _ => Ren.comp (Ren.wkBlock σs) (Ren.shift (σ := σ))

/-- A renaming pushed under a block. -/
def Ren.liftBlock : ∀ (σs : List Ty) {Γ Δ : Ctx}, Ren Γ Δ → Ren (Ctx.block σs Γ) (Ctx.block σs Δ)
  | [], _, _, r => r
  | σ :: σs, _, _, r => Ren.liftBlock σs (Ren.lift r (σ := σ))

/-- A substitution pushed under a block. -/
def Sub.liftBlock : ∀ (σs : List Ty) {Γ Δ : Ctx}, Sub Sig Γ Δ → Sub Sig (Ctx.block σs Γ) (Ctx.block σs Δ)
  | [], _, _, s => s
  | σ :: σs, _, _, s => Sub.liftBlock σs (Sub.lift s (σ := σ))

/-! ### Tuples of terms -/

/-- A tuple of terms, one of each of the types `σs`, in context `Γ`. -/
inductive Terms (Sig : Signature) (Γ : Ctx) : List Ty → Type
  | nil : Terms Sig Γ []
  | cons {σ : Ty} {σs : List Ty} : Term Sig Γ σ → Terms Sig Γ σs → Terms Sig Γ (σ :: σs)

namespace Terms

/-! The operations on tuples recurse on the list of types and take the tuple apart by its
projections, never by matching it: so a tuple whose length is known computes componentwise
even when the tuple itself is not written out, and a one-element tuple is, for every
operation, just its term. -/

/-- The first term of a tuple. -/
def head {Γ : Ctx} {σ : Ty} {σs : List Ty} : Terms Sig Γ (σ :: σs) → Term Sig Γ σ
  | .cons a _ => a

/-- The rest of a tuple. -/
def tail {Γ : Ctx} {σ : Ty} {σs : List Ty} : Terms Sig Γ (σ :: σs) → Terms Sig Γ σs
  | .cons _ as => as

@[simp] theorem head_cons {Γ : Ctx} {σ : Ty} {σs : List Ty} (a : Term Sig Γ σ) (as : Terms Sig Γ σs) :
    (Terms.cons a as).head = a := rfl
@[simp] theorem tail_cons {Γ : Ctx} {σ : Ty} {σs : List Ty} (a : Term Sig Γ σ) (as : Terms Sig Γ σs) :
    (Terms.cons a as).tail = as := rfl

theorem cons_head_tail {Γ : Ctx} {σ : Ty} {σs : List Ty} :
    ∀ as : Terms Sig Γ (σ :: σs), Terms.cons as.head as.tail = as
  | .cons _ _ => rfl

theorem eq_nil {Γ : Ctx} : ∀ as : Terms Sig Γ [], as = .nil
  | .nil => rfl

/-- A tuple of one term. -/
abbrev single {Γ : Ctx} {σ : Ty} (a : Term Sig Γ σ) : Terms Sig Γ [σ] := .cons a .nil

/-- The term of a one-element tuple. -/
abbrev head1 {Γ : Ctx} {σ : Ty} (as : Terms Sig Γ [σ]) : Term Sig Γ σ := as.head

theorem head1_single {Γ : Ctx} {σ : Ty} (a : Term Sig Γ σ) : (single a).head1 = a := rfl
@[simp] theorem single_head1 {Γ : Ctx} {σ : Ty} : ∀ as : Terms Sig Γ [σ], single as.head1 = as
  | .cons _ .nil => rfl

/-- Rename each term of a tuple. -/
def rename {Γ Δ : Ctx} (r : Ren Γ Δ) : ∀ {σs : List Ty}, Terms Sig Γ σs → Terms Sig Δ σs
  | [], _ => .nil
  | _ :: _, as => .cons (as.head.rename r) (rename r as.tail)

/-- Substitute into each term of a tuple. -/
def subst {Γ Δ : Ctx} (s : Sub Sig Γ Δ) : ∀ {σs : List Ty}, Terms Sig Γ σs → Terms Sig Δ σs
  | [], _ => .nil
  | _ :: _, as => .cons (as.head.subst s) (subst s as.tail)

@[simp] theorem rename_nil {Γ Δ : Ctx} (r : Ren Γ Δ) : rename r (.nil : Terms Sig Γ []) = .nil := rfl
@[simp] theorem rename_cons {Γ Δ : Ctx} (r : Ren Γ Δ) {σ : Ty} {σs : List Ty} (a : Term Sig Γ σ)
    (as : Terms Sig Γ σs) : rename r (.cons a as) = .cons (a.rename r) (rename r as) := rfl
@[simp] theorem subst_nil {Γ Δ : Ctx} (s : Sub Sig Γ Δ) : subst s (.nil : Terms Sig Γ []) = .nil := rfl
@[simp] theorem subst_cons {Γ Δ : Ctx} (s : Sub Sig Γ Δ) {σ : Ty} {σs : List Ty} (a : Term Sig Γ σ)
    (as : Terms Sig Γ σs) : subst s (.cons a as) = .cons (a.subst s) (subst s as) := rfl

theorem head1_rename {Γ Δ : Ctx} (r : Ren Γ Δ) {σ : Ty} (as : Terms Sig Γ [σ]) :
    (as.rename r).head1 = as.head1.rename r := rfl
theorem head1_subst {Γ Δ : Ctx} (s : Sub Sig Γ Δ) {σ : Ty} (as : Terms Sig Γ [σ]) :
    (as.subst s).head1 = as.head1.subst s := rfl

theorem rename_rename {Γ Δ Θ : Ctx} (r : Ren Δ Θ) (r' : Ren Γ Δ) :
    ∀ {σs : List Ty} (as : Terms Sig Γ σs), (as.rename r').rename r = as.rename (Ren.comp r r')
  | [], .nil => rfl
  | _ :: _, .cons a as => by simp [Term.rename_rename, rename_rename r r' as]

theorem subst_subst {Γ Δ Θ : Ctx} (s : Sub Sig Δ Θ) (s' : Sub Sig Γ Δ) :
    ∀ {σs : List Ty} (as : Terms Sig Γ σs), (as.subst s').subst s = as.subst (Sub.comp s s')
  | [], .nil => rfl
  | _ :: _, .cons a as => by simp [Term.subst_subst, subst_subst s s' as]

theorem subst_rename {Γ Δ Θ : Ctx} (s : Sub Sig Δ Θ) (r : Ren Γ Δ) :
    ∀ {σs : List Ty} (as : Terms Sig Γ σs), (as.rename r).subst s = as.subst (Sub.compRen s r)
  | [], .nil => rfl
  | _ :: _, .cons a as => by simp [Term.subst_rename, subst_rename s r as]

theorem rename_subst {Γ Δ Θ : Ctx} (r : Ren Δ Θ) (s : Sub Sig Γ Δ) :
    ∀ {σs : List Ty} (as : Terms Sig Γ σs), (as.subst s).rename r = as.subst (Ren.compSub r s)
  | [], .nil => rfl
  | _ :: _, .cons a as => by simp [Term.rename_subst, rename_subst r s as]

theorem rename_eq_subst {Γ Δ : Ctx} (r : Ren Γ Δ) :
    ∀ {σs : List Ty} (as : Terms Sig Γ σs), as.rename r = as.subst (Sub.ofRen r)
  | [], .nil => rfl
  | _ :: _, .cons a as => by simp [Term.rename_eq_subst r a, rename_eq_subst r as]

theorem subst_id : ∀ {Γ : Ctx} {σs : List Ty} (as : Terms Sig Γ σs), as.subst Sub.id = as
  | _, [], .nil => rfl
  | _, _ :: _, .cons a as => by simp [Term.subst_id, subst_id as]

/-- The variables of a block, in order, in the context the block extends. -/
def vars : ∀ (σs : List Ty) (Γ : Ctx), Terms Sig (Ctx.block σs Γ) σs
  | [], _ => .nil
  | σ :: σs, Γ =>
    .cons ((Term.var .zero : Term Sig (σ :: Γ) σ).rename (Ren.wkBlock σs)) (vars σs (σ :: Γ))

end Terms

/-- A tuple of terms for a block, then a substitution for the rest: the substitution
that sends the block's variables to the tuple. -/
def Sub.consBlock : ∀ {σs : List Ty} {Γ Δ : Ctx}, Terms Sig Δ σs → Sub Sig Γ Δ →
    Sub Sig (Ctx.block σs Γ) Δ
  | [], _, _, _, s => s
  | _ :: σs, Γ, Δ, as, s =>
    Sub.consBlock (σs := σs) (Γ := _ :: Γ) (Δ := Δ) as.tail (Sub.cons as.head s)

/-! ### Application and abstraction over a block -/

namespace Term

/-- `F a₁ … aₙ`: a function of the block's types applied to a tuple. -/
def appBlock : ∀ {Γ : Ctx} {σs : List Ty} {ρ : RTy}, Term Sig Γ (σs ⇒* ρ) → Terms Sig Γ σs →
    Term Sig Γ ρ
  | _, [], _, f, _ => f
  | _, _ :: _, _, f, as => appBlock (.app f as.head) as.tail

/-- `λx₁ … xₙ. B`. -/
def lamBlock : ∀ (σs : List Ty) {Γ : Ctx} {ρ : RTy}, Term Sig (Ctx.block σs Γ) ρ →
    Term Sig Γ (σs ⇒* ρ)
  | [], _, _, b => b
  | _ :: σs, _, _, b => .lam (lamBlock σs b)

/-- `∀x₁ … ∀xₙ. P`. -/
def forallBlock : ∀ (σs : List Ty) {Γ : Ctx}, Formula Sig (Ctx.block σs Γ) → Formula Sig Γ
  | [], _, p => p
  | _ :: σs, _, p => forall' (forallBlock σs p)

/-- `∃x₁ … ∃xₙ. P`. -/
def existsBlock : ∀ (σs : List Ty) {Γ : Ctx}, Formula Sig (Ctx.block σs Γ) → Formula Sig Γ
  | [], _, p => p
  | _ :: σs, _, p => exists' (existsBlock σs p)

/-- `a₁ = b₁ ∧ … ∧ aₙ = bₙ`: `⊤` for the empty block, and the identity itself for a
one-element block. -/
def eqBlock : ∀ {Γ : Ctx} {σs : List Ty}, Terms Sig Γ σs → Terms Sig Γ σs → Formula Sig Γ
  | _, [], _, _ => top
  | _, [_], as, bs => eq' as.head bs.head
  | _, _ :: _ :: _, as, bs => conj (eq' as.head bs.head) (eqBlock as.tail bs.tail)

/-- `λX. ∀x₁ … ∀xₙ. X x₁ … xₙ`, the block quantifier as a constant; at a one-element
block, the quantifier itself. -/
def allC : ∀ (σs : List Ty) {Γ : Ctx}, Term Sig Γ ((σs ⇒* .t) ⇒ .t)
  | [σ], _ => .all σ
  | σs, Γ => .lam (forallBlock σs (appBlock
      ((Term.var .zero : Term Sig (Ty.rel (σs ⇒* .t) :: Γ) (σs ⇒* .t)).rename (Ren.wkBlock σs))
      (Terms.vars σs _)))

/-- `λX. ∃x₁ … ∃xₙ. X x₁ … xₙ`; at a one-element block, the quantifier itself. -/
def exC : ∀ (σs : List Ty) {Γ : Ctx}, Term Sig Γ ((σs ⇒* .t) ⇒ .t)
  | [σ], _ => .ex σ
  | σs, Γ => .lam (existsBlock σs (appBlock
      ((Term.var .zero : Term Sig (Ty.rel (σs ⇒* .t) :: Γ) (σs ⇒* .t)).rename (Ren.wkBlock σs))
      (Terms.vars σs _)))

/-- `λx₁ … xₙ y₁ … yₙ. x₁ = y₁ ∧ … ∧ xₙ = yₙ`; at a one-element block, identity itself. -/
def eqC : ∀ (σs : List Ty) {Γ : Ctx}, Term Sig Γ (σs ⇒* (σs ⇒* .t))
  | [σ], _ => .eq σ
  | σs, Γ => lamBlock σs (lamBlock σs
      (eqBlock ((Terms.vars σs Γ).rename (Ren.wkBlock σs)) (Terms.vars σs (Ctx.block σs Γ))))

/-! ### Renaming and substitution through the block forms -/

theorem rename_appBlock {Γ Δ : Ctx} (r : Ren Γ Δ) :
    ∀ {σs : List Ty} {ρ : RTy} (f : Term Sig Γ (σs ⇒* ρ)) (as : Terms Sig Γ σs),
      (appBlock f as).rename r = appBlock (f.rename r) (as.rename r)
  | [], _, _, .nil => rfl
  | _ :: _, _, f, .cons a as => rename_appBlock r (.app f a) as

theorem subst_appBlock {Γ Δ : Ctx} (s : Sub Sig Γ Δ) :
    ∀ {σs : List Ty} {ρ : RTy} (f : Term Sig Γ (σs ⇒* ρ)) (as : Terms Sig Γ σs),
      (appBlock f as).subst s = appBlock (f.subst s) (as.subst s)
  | [], _, _, .nil => rfl
  | _ :: _, _, f, .cons a as => subst_appBlock s (.app f a) as

theorem rename_lamBlock : ∀ (σs : List Ty) {Γ Δ : Ctx} (r : Ren Γ Δ) {ρ : RTy}
    (b : Term Sig (Ctx.block σs Γ) ρ),
    (lamBlock σs b).rename r = lamBlock σs (b.rename (Ren.liftBlock σs r))
  | [], _, _, _, _, _ => rfl
  | σ :: σs, Γ, _, r, _, b => congrArg Term.lam (rename_lamBlock σs (Γ := σ :: Γ) (Ren.lift r) b)

theorem subst_lamBlock : ∀ (σs : List Ty) {Γ Δ : Ctx} (s : Sub Sig Γ Δ) {ρ : RTy}
    (b : Term Sig (Ctx.block σs Γ) ρ),
    (lamBlock σs b).subst s = lamBlock σs (b.subst (Sub.liftBlock σs s))
  | [], _, _, _, _, _ => rfl
  | σ :: σs, Γ, _, s, _, b => congrArg Term.lam (subst_lamBlock σs (Γ := σ :: Γ) (Sub.lift s) b)

theorem rename_forallBlock : ∀ (σs : List Ty) {Γ Δ : Ctx} (r : Ren Γ Δ)
    (p : Formula Sig (Ctx.block σs Γ)),
    (forallBlock σs p).rename r = forallBlock σs (p.rename (Ren.liftBlock σs r))
  | [], _, _, _, _ => rfl
  | _ :: σs, _, _, r, p => by
    simp only [forallBlock, forall', rename_app, rename_lam, rename_all]
    rw [rename_forallBlock σs (Ren.lift r) p]; rfl

theorem subst_forallBlock : ∀ (σs : List Ty) {Γ Δ : Ctx} (s : Sub Sig Γ Δ)
    (p : Formula Sig (Ctx.block σs Γ)),
    (forallBlock σs p).subst s = forallBlock σs (p.subst (Sub.liftBlock σs s))
  | [], _, _, _, _ => rfl
  | _ :: σs, _, _, s, p => by
    simp only [forallBlock, forall', subst_app, subst_lam, subst_all]
    rw [subst_forallBlock σs (Sub.lift s) p]; rfl

theorem rename_existsBlock : ∀ (σs : List Ty) {Γ Δ : Ctx} (r : Ren Γ Δ)
    (p : Formula Sig (Ctx.block σs Γ)),
    (existsBlock σs p).rename r = existsBlock σs (p.rename (Ren.liftBlock σs r))
  | [], _, _, _, _ => rfl
  | _ :: σs, _, _, r, p => by
    simp only [existsBlock, exists', rename_app, rename_lam, rename_ex]
    rw [rename_existsBlock σs (Ren.lift r) p]; rfl

theorem subst_existsBlock : ∀ (σs : List Ty) {Γ Δ : Ctx} (s : Sub Sig Γ Δ)
    (p : Formula Sig (Ctx.block σs Γ)),
    (existsBlock σs p).subst s = existsBlock σs (p.subst (Sub.liftBlock σs s))
  | [], _, _, _, _ => rfl
  | _ :: σs, _, _, s, p => by
    simp only [existsBlock, exists', subst_app, subst_lam, subst_ex]
    rw [subst_existsBlock σs (Sub.lift s) p]; rfl

theorem rename_eqBlock {Γ Δ : Ctx} (r : Ren Γ Δ) :
    ∀ {σs : List Ty} (as bs : Terms Sig Γ σs),
      (eqBlock as bs).rename r = eqBlock (as.rename r) (bs.rename r)
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | _ :: _ :: _, as, bs => by
    show Term.conj ((eq' as.head bs.head).rename r) ((eqBlock as.tail bs.tail).rename r) = _
    rw [rename_eqBlock r as.tail bs.tail]; rfl

theorem subst_eqBlock {Γ Δ : Ctx} (s : Sub Sig Γ Δ) :
    ∀ {σs : List Ty} (as bs : Terms Sig Γ σs),
      (eqBlock as bs).subst s = eqBlock (as.subst s) (bs.subst s)
  | [], _, _ => rfl
  | [_], _, _ => rfl
  | _ :: _ :: _, as, bs => by
    show Term.conj ((eq' as.head bs.head).subst s) ((eqBlock as.tail bs.tail).subst s) = _
    rw [subst_eqBlock s as.tail bs.tail]; rfl

end Term

/-! ### The algebra of block substitutions -/

namespace Sub

/-- Substituting after weakening past a block forgets the block. -/
theorem compRen_consBlock_wkBlock : ∀ {σs : List Ty} {Γ Δ : Ctx} (as : Terms Sig Δ σs)
    (s : Sub Sig Γ Δ), Sub.compRen (Sub.consBlock as s) (Ren.wkBlock σs) = s
  | [], _, _, .nil, s => rfl
  | _ :: σs, Γ, _, .cons a as, s => by
    have := compRen_consBlock_wkBlock (σs := σs) (Γ := _ :: Γ) as (Sub.cons a s)
    funext τ v
    show Sub.consBlock as (Sub.cons a s) τ (Ren.wkBlock σs τ (Ren.shift τ v)) = s τ v
    rw [show Sub.consBlock as (Sub.cons a s) τ (Ren.wkBlock σs τ (Ren.shift τ v))
        = Sub.compRen (Sub.consBlock as (Sub.cons a s)) (Ren.wkBlock σs) τ (Ren.shift τ v) from rfl,
      this]
    rfl

/-- `(as, t) ∘ ⇑σs s = (as, t ∘ s)`: the block substitution after a substitution lifted
over the block. -/
theorem comp_consBlock_liftBlock : ∀ {σs : List Ty} {Γ Θ Δ : Ctx} (as : Terms Sig Δ σs)
    (t : Sub Sig Θ Δ) (s : Sub Sig Γ Θ),
    Sub.comp (Sub.consBlock as t) (Sub.liftBlock σs s) = Sub.consBlock as (Sub.comp t s)
  | [], _, _, _, .nil, _, _ => rfl
  | _ :: σs, Γ, Θ, _, .cons a as, t, s => by
    have := comp_consBlock_liftBlock (σs := σs) (Γ := _ :: Γ) (Θ := _ :: Θ) as (Sub.cons a t)
      (Sub.lift s)
    show Sub.comp (Sub.consBlock as (Sub.cons a t)) (Sub.liftBlock σs (Sub.lift s))
      = Sub.consBlock as (Sub.cons a (Sub.comp t s))
    rw [this]
    congr 1
    funext τ v
    cases v with
    | zero => rfl
    | succ v =>
      show ((s τ v).weaken).subst (Sub.cons a t) = (s τ v).subst t
      rw [Term.weaken, Term.subst_rename, Sub.compRen_cons_shift]

/-- A substitution after a block substitution: `t ∘ (as, s) = (t as, t ∘ s)`. -/
theorem comp_consBlock : ∀ {σs : List Ty} {Γ Θ Δ : Ctx} (t : Sub Sig Θ Δ) (as : Terms Sig Θ σs)
    (s : Sub Sig Γ Θ), Sub.comp t (Sub.consBlock as s) = Sub.consBlock (as.subst t) (Sub.comp t s)
  | [], _, _, _, _, .nil, _ => rfl
  | _ :: σs, Γ, _, _, t, .cons a as, s => by
    have := comp_consBlock (σs := σs) (Γ := _ :: Γ) t as (Sub.cons a s)
    show Sub.comp t (Sub.consBlock as (Sub.cons a s)) = Sub.consBlock (as.subst t) (Sub.cons (a.subst t) (Sub.comp t s))
    rw [this]
    congr 1
    funext τ v
    cases v <;> rfl

theorem comp_id_left {Γ Δ : Ctx} (s : Sub Sig Γ Δ) : Sub.comp Sub.id s = s := by
  funext τ v; exact Term.subst_id _

end Sub

/-- The block's variables, substituted by a block substitution, are its tuple. -/
theorem Terms.vars_subst_consBlock : ∀ {σs : List Ty} {Γ Δ : Ctx} (as : Terms Sig Δ σs)
    (s : Sub Sig Γ Δ), (Terms.vars σs Γ).subst (Sub.consBlock as s) = as
  | [], _, _, .nil, _ => rfl
  | _ :: σs, Γ, _, .cons a as, s => by
    show Terms.cons (((Term.var .zero).rename (Ren.wkBlock σs)).subst (Sub.consBlock as (Sub.cons a s)))
        ((Terms.vars σs (_ :: Γ)).subst (Sub.consBlock as (Sub.cons a s))) = .cons a as
    rw [Term.subst_rename, Sub.compRen_consBlock_wkBlock, vars_subst_consBlock as (Sub.cons a s)]
    rfl

/-! ### Conversion through the block forms -/

/-- Two tuples, pointwise convertible. -/
inductive Terms.Conv {Γ : Ctx} : ∀ {σs : List Ty}, Terms Sig Γ σs → Terms Sig Γ σs → Prop
  | nil : Terms.Conv .nil .nil
  | cons {σ : Ty} {σs : List Ty} {a b : Term Sig Γ σ} {as bs : Terms Sig Γ σs} :
      a ≡ b → Terms.Conv as bs → Terms.Conv (.cons a as) (.cons b bs)

theorem Terms.Conv.refl {Γ : Ctx} : ∀ {σs : List Ty} (as : Terms Sig Γ σs), Terms.Conv as as
  | [], .nil => .nil
  | _ :: _, .cons a as => .cons (Classicism.Meta.Conv.refl a) (Terms.Conv.refl as)

theorem Terms.Conv.symm {Γ : Ctx} : ∀ {σs : List Ty} {as bs : Terms Sig Γ σs},
    Terms.Conv as bs → Terms.Conv bs as
  | _, _, _, .nil => .nil
  | _, _, _, .cons h hs => .cons (Classicism.Meta.Conv.symm h) (Terms.Conv.symm hs)

theorem Terms.Conv.trans {Γ : Ctx} : ∀ {σs : List Ty} {as bs cs : Terms Sig Γ σs},
    Terms.Conv as bs → Terms.Conv bs cs → Terms.Conv as cs
  | _, _, _, _, .nil, .nil => .nil
  | _, _, _, _, .cons h hs, .cons h' hs' =>
    .cons (Classicism.Meta.Conv.trans h h') (Terms.Conv.trans hs hs')

theorem Terms.Conv.head1 {Γ : Ctx} {σ : Ty} : ∀ {as bs : Terms Sig Γ [σ]},
    Terms.Conv as bs → as.head1 ≡ bs.head1
  | .cons _ .nil, .cons _ .nil, .cons h .nil => h

theorem Terms.Conv.of_head1 {Γ : Ctx} {σ : Ty} : ∀ {as bs : Terms Sig Γ [σ]},
    as.head1 ≡ bs.head1 → Terms.Conv as bs
  | .cons _ .nil, .cons _ .nil, h => .cons h .nil

/-- Equal terms are convertible. -/
theorem Conv.of_eq {Γ : Ctx} {σ : Ty} {a b : Term Sig Γ σ} (h : a = b) : a ≡ b := h ▸ Conv.refl a

namespace Conv

theorem appBlock_congr {Γ : Ctx} :
    ∀ {σs : List Ty} {ρ : RTy} {f f' : Term Sig Γ (σs ⇒* ρ)} {as bs : Terms Sig Γ σs},
      f ≡ f' → Terms.Conv as bs → Term.appBlock f as ≡ Term.appBlock f' bs
  | [], _, _, _, .nil, .nil, hf, _ => hf
  | _ :: _, _, _, _, .cons _ _, .cons _ _, hf, .cons ha has =>
    appBlock_congr (f := Term.app _ _) (f' := Term.app _ _) (Conv.app_congr hf ha) has

theorem lamBlock_congr : ∀ (σs : List Ty) {Γ : Ctx} {ρ : RTy} {b b' : Term Sig (Ctx.block σs Γ) ρ},
    b ≡ b' → Term.lamBlock σs b ≡ Term.lamBlock σs b'
  | [], _, _, _, _, h => h
  | _ :: σs, _, _, _, _, h => Conv.lam_congr (lamBlock_congr σs h)

theorem forallBlock_congr : ∀ (σs : List Ty) {Γ : Ctx} {p q : Formula Sig (Ctx.block σs Γ)},
    p ≡ q → Term.forallBlock σs p ≡ Term.forallBlock σs q
  | [], _, _, _, h => h
  | _ :: σs, _, _, _, h => Conv.app_congr (Conv.refl _) (Conv.lam_congr (forallBlock_congr σs h))

theorem existsBlock_congr : ∀ (σs : List Ty) {Γ : Ctx} {p q : Formula Sig (Ctx.block σs Γ)},
    p ≡ q → Term.existsBlock σs p ≡ Term.existsBlock σs q
  | [], _, _, _, h => h
  | _ :: σs, _, _, _, h => Conv.app_congr (Conv.refl _) (Conv.lam_congr (existsBlock_congr σs h))

theorem eqBlock_congr {Γ : Ctx} : ∀ {σs : List Ty} {as as' bs bs' : Terms Sig Γ σs},
    Terms.Conv as as' → Terms.Conv bs bs' → Term.eqBlock as bs ≡ Term.eqBlock as' bs'
  | [], .nil, .nil, .nil, .nil, _, _ => Conv.refl _
  | [_], .cons _ .nil, .cons _ .nil, .cons _ .nil, .cons _ .nil, .cons ha .nil, .cons hb .nil =>
    Conv.app_congr (Conv.app_congr (Conv.refl _) ha) hb
  | _ :: _ :: _, .cons _ _, .cons _ _, .cons _ _, .cons _ _, .cons ha has, .cons hb hbs =>
    Conv.app_congr (Conv.app_congr (Conv.refl _) (Conv.app_congr (Conv.app_congr (Conv.refl _) ha) hb))
      (eqBlock_congr has hbs)

/-- **Block β**: `(λx̄. B) ā ≡ B[ā/x̄]`. -/
theorem appBlock_lamBlock : ∀ (σs : List Ty) {Γ : Ctx} {ρ : RTy} (b : Term Sig (Ctx.block σs Γ) ρ)
    (as : Terms Sig Γ σs), Term.appBlock (Term.lamBlock σs b) as ≡ b.subst (Sub.consBlock as Sub.id)
  | [], _, _, b, .nil => by
    show b ≡ b.subst Sub.id
    rw [Term.subst_id]; exact Conv.refl b
  | _ :: σs, Γ, _, b, .cons a as => by
    show Term.appBlock (Term.app (Term.lam (Term.lamBlock σs b)) a) as ≡ _
    refine Conv.trans (appBlock_congr (Conv.beta _ a) (Terms.Conv.refl as)) ?_
    have e1 : (Term.lamBlock σs b).instantiate a
        = Term.lamBlock σs (b.subst (Sub.liftBlock σs (Sub.cons a Sub.id))) :=
      Term.subst_lamBlock σs (Γ := _ :: Γ) (Sub.cons a Sub.id) b
    rw [e1]
    refine Conv.trans (appBlock_lamBlock σs _ as) (Conv.of_eq ?_)
    have e2 := Term.subst_subst (Sub.consBlock as Sub.id) (Sub.liftBlock σs (Sub.cons a Sub.id)) b
    rw [e2, Sub.comp_consBlock_liftBlock, Sub.comp_id_left]
    rfl

/-- **Block η**: `λx̄. F x̄ ≡ F`, for `F` not mentioning the block. -/
theorem lamBlock_appBlock : ∀ (σs : List Ty) {Γ : Ctx} {ρ : RTy} (f : Term Sig Γ (σs ⇒* ρ)),
    Term.lamBlock σs (Term.appBlock (f.rename (Ren.wkBlock σs)) (Terms.vars σs Γ)) ≡ f
  | [], _, _, f => by
    show f.rename Ren.id ≡ f
    rw [Term.rename_id]; exact Conv.refl f
  | σ :: σs, Γ, _, f => by
    have e2 : (Term.app f.weaken (Term.var .zero : Term Sig (σ :: Γ) σ)).rename (Ren.wkBlock σs)
        = Term.app (f.rename (Ren.comp (Ren.wkBlock σs) Ren.shift))
            ((Term.var .zero : Term Sig (σ :: Γ) σ).rename (Ren.wkBlock σs)) := by
      rw [Term.rename_app, Term.weaken, Term.rename_rename]
    have e : Term.appBlock (f.rename (Ren.wkBlock (σ :: σs))) (Terms.vars (σ :: σs) Γ)
        = Term.appBlock ((Term.app f.weaken (Term.var .zero)).rename (Ren.wkBlock σs))
            (Terms.vars σs (σ :: Γ)) := by
      rw [e2]; rfl
    show Term.lam (Term.lamBlock σs _) ≡ f
    rw [e]
    exact Conv.trans (Conv.lam_congr (lamBlock_appBlock σs _)) (Conv.eta f)

end Conv

/-! ### More algebra: lifting over a block -/

namespace Sub

/-- A substitution lifted over a block, after weakening past it, is the substitution
weakened past it. -/
theorem compRen_liftBlock_wkBlock : ∀ (σs : List Ty) {Γ Δ : Ctx} (s : Sub Sig Γ Δ),
    Sub.compRen (Sub.liftBlock σs s) (Ren.wkBlock σs) = Ren.compSub (Ren.wkBlock σs) s
  | [], _, _, s => by
    funext τ v; exact (Term.rename_id _).symm
  | σ :: σs, Γ, Δ, s => by
    have ih := compRen_liftBlock_wkBlock σs (Γ := σ :: Γ) (Δ := σ :: Δ) (Sub.lift s)
    funext τ v
    show Sub.compRen (Sub.liftBlock σs (Sub.lift s)) (Ren.wkBlock σs) τ (Ren.shift τ v) = _
    rw [ih]
    show ((s τ v).weaken).rename (Ren.wkBlock σs) = (s τ v).rename (Ren.comp (Ren.wkBlock σs) Ren.shift)
    rw [Term.weaken, Term.rename_rename]

/-- `(as, t) ∘ ⇑σs r = (as, t ∘ r)`, for a renaming lifted over the block. -/
theorem compRen_consBlock_liftBlock : ∀ {σs : List Ty} {Γ Θ Δ : Ctx} (as : Terms Sig Δ σs)
    (t : Sub Sig Θ Δ) (r : Ren Γ Θ),
    Sub.compRen (Sub.consBlock as t) (Ren.liftBlock σs r) = Sub.consBlock as (Sub.compRen t r)
  | [], _, _, _, .nil, _, _ => rfl
  | _ :: σs, Γ, Θ, _, .cons a as, t, r => by
    have := compRen_consBlock_liftBlock (σs := σs) (Γ := _ :: Γ) (Θ := _ :: Θ) as (Sub.cons a t)
      (Ren.lift r)
    show Sub.compRen (Sub.consBlock as (Sub.cons a t)) (Ren.liftBlock σs (Ren.lift r))
      = Sub.consBlock as (Sub.cons a (Sub.compRen t r))
    rw [this]
    congr 1
    funext τ v
    cases v <;> rfl

/-- A renaming after a block substitution: `r ∘ (as, t) = (r as, r ∘ t)`. -/
theorem _root_.Classicism.Meta.Ren.compSub_consBlock : ∀ {σs : List Ty} {Γ Θ Δ : Ctx}
    (r : Ren Θ Δ) (as : Terms Sig Θ σs) (t : Sub Sig Γ Θ),
    Ren.compSub r (Sub.consBlock as t) = Sub.consBlock (as.rename r) (Ren.compSub r t)
  | [], _, _, _, _, .nil, _ => rfl
  | _ :: σs, Γ, _, _, r, .cons a as, t => by
    have := Ren.compSub_consBlock (σs := σs) (Γ := _ :: Γ) r as (Sub.cons a t)
    show Ren.compSub r (Sub.consBlock as (Sub.cons a t))
      = Sub.consBlock (as.rename r) (Sub.cons (a.rename r) (Ren.compSub r t))
    rw [this]
    congr 1
    funext τ v
    cases v <;> rfl

/-- Lifting over a block is the block's variables, then the substitution weakened past
the block. -/
theorem consBlock_vars_compSub : ∀ (σs : List Ty) {Γ Δ : Ctx} (t : Sub Sig Γ Δ),
    Sub.consBlock (Terms.vars σs Δ) (Ren.compSub (Ren.wkBlock σs) t) = Sub.liftBlock σs t
  | [], _, _, t => by funext τ v; exact Term.rename_id _
  | σ :: σs, Γ, Δ, t => by
    have ih := consBlock_vars_compSub σs (Γ := σ :: Γ) (Δ := σ :: Δ) (Sub.lift t)
    show Sub.consBlock (Terms.vars σs (σ :: Δ)) (Sub.cons ((Term.var .zero).rename (Ren.wkBlock σs))
      (Ren.compSub (Ren.comp (Ren.wkBlock σs) Ren.shift) t)) = Sub.liftBlock σs (Sub.lift t)
    rw [← ih]
    congr 1
    funext τ v
    cases v with
    | zero => rfl
    | succ v =>
      show (t τ v).rename (Ren.comp (Ren.wkBlock σs) Ren.shift) = ((t τ v).weaken).rename (Ren.wkBlock σs)
      rw [Term.weaken, Term.rename_rename]

/-- The block's variables, then the weakening past the block: the identity. -/
theorem consBlock_vars_wkBlock : ∀ (σs : List Ty) (Γ : Ctx),
    Sub.consBlock (Terms.vars σs Γ) (Sub.ofRen (Ren.wkBlock σs)) = (Sub.id : Sub Sig (Ctx.block σs Γ) _)
  | [], _ => by funext τ v; rfl
  | σ :: σs, Γ => by
    have ih := consBlock_vars_wkBlock σs (σ :: Γ)
    show Sub.consBlock (Terms.vars σs (σ :: Γ))
        (Sub.cons ((Term.var .zero).rename (Ren.wkBlock σs)) (Sub.ofRen (Ren.comp (Ren.wkBlock σs) Ren.shift)))
      = Sub.id
    have e : (Sub.cons ((Term.var .zero : Term Sig (σ :: Γ) σ).rename (Ren.wkBlock σs))
        (Sub.ofRen (Ren.comp (Ren.wkBlock σs) Ren.shift)) : Sub Sig (σ :: Γ) (Ctx.block σs (σ :: Γ)))
        = Sub.ofRen (Ren.wkBlock σs) := by
      funext τ v; cases v <;> rfl
    rw [e, ih]

end Sub

/-- A substitution lifted over a block leaves the block's variables alone. -/
theorem Terms.vars_subst_liftBlock : ∀ (σs : List Ty) {Γ Δ : Ctx} (s : Sub Sig Γ Δ),
    (Terms.vars σs Γ).subst (Sub.liftBlock σs s) = Terms.vars σs Δ
  | [], _, _, _ => rfl
  | σ :: σs, Γ, Δ, s => by
    have ih := vars_subst_liftBlock σs (Γ := σ :: Γ) (Δ := σ :: Δ) (Sub.lift s)
    show Terms.cons (((Term.var .zero).rename (Ren.wkBlock σs)).subst (Sub.liftBlock σs (Sub.lift s)))
        ((Terms.vars σs (σ :: Γ)).subst (Sub.liftBlock σs (Sub.lift s))) = _
    rw [Term.subst_rename, Sub.compRen_liftBlock_wkBlock, ih]
    rfl

/-- A function weakened past a block and applied to the block's variables, with the
block then instantiated at a tuple: the function applied to the tuple. -/
theorem Term.appBlock_vars_subst_consBlock {Γ : Ctx} {σs : List Ty} {ρ : RTy}
    (f : Term Sig Γ (σs ⇒* ρ)) (as : Terms Sig Γ σs) :
    (Term.appBlock (f.rename (Ren.wkBlock σs)) (Terms.vars σs Γ)).subst (Sub.consBlock as Sub.id)
      = Term.appBlock f as := by
  rw [Term.subst_appBlock, Term.subst_rename, Sub.compRen_consBlock_wkBlock, Term.subst_id,
    Terms.vars_subst_consBlock]

/-- A function weakened past a block `σ :: σs` and applied to the block's variables is the
function weakened past `σ` and applied to its variable, then weakened past `σs` and applied
to theirs. -/
theorem Term.appBlock_vars_cons (σ : Ty) (σs : List Ty) {Γ : Ctx} {ρ : RTy}
    (f : Term Sig Γ ((σ :: σs) ⇒* ρ)) :
    Term.appBlock (f.rename (Ren.wkBlock (σ :: σs))) (Terms.vars (σ :: σs) Γ)
      = Term.appBlock ((Term.app f.weaken (Term.var .zero)).rename (Ren.wkBlock σs))
          (Terms.vars σs (σ :: Γ)) := by
  rw [Term.rename_app, Term.weaken, Term.rename_rename]; rfl

/-! ### The block constants are closed -/

namespace Term

private theorem subst_allC_body (σs : List Ty) {Γ Δ : Ctx} (s : Sub Sig Γ Δ) :
    (forallBlock σs (appBlock
      ((Term.var .zero : Term Sig (Ty.rel (σs ⇒* .t) :: Γ) (σs ⇒* .t)).rename (Ren.wkBlock σs))
      (Terms.vars σs _))).subst (Sub.lift s)
    = forallBlock σs (appBlock
      ((Term.var .zero : Term Sig (Ty.rel (σs ⇒* .t) :: Δ) (σs ⇒* .t)).rename (Ren.wkBlock σs))
      (Terms.vars σs _)) := by
  rw [subst_forallBlock, subst_appBlock, subst_rename, Sub.compRen_liftBlock_wkBlock,
    Terms.vars_subst_liftBlock]
  rfl

private theorem subst_exC_body (σs : List Ty) {Γ Δ : Ctx} (s : Sub Sig Γ Δ) :
    (existsBlock σs (appBlock
      ((Term.var .zero : Term Sig (Ty.rel (σs ⇒* .t) :: Γ) (σs ⇒* .t)).rename (Ren.wkBlock σs))
      (Terms.vars σs _))).subst (Sub.lift s)
    = existsBlock σs (appBlock
      ((Term.var .zero : Term Sig (Ty.rel (σs ⇒* .t) :: Δ) (σs ⇒* .t)).rename (Ren.wkBlock σs))
      (Terms.vars σs _)) := by
  rw [subst_existsBlock, subst_appBlock, subst_rename, Sub.compRen_liftBlock_wkBlock,
    Terms.vars_subst_liftBlock]
  rfl

private theorem subst_eqC_body (σs : List Ty) {Γ Δ : Ctx} (s : Sub Sig Γ Δ) :
    (lamBlock σs (lamBlock σs (eqBlock ((Terms.vars σs Γ).rename (Ren.wkBlock σs))
      (Terms.vars σs (Ctx.block σs Γ))))).subst s
    = lamBlock σs (lamBlock σs (eqBlock ((Terms.vars σs Δ).rename (Ren.wkBlock σs))
      (Terms.vars σs (Ctx.block σs Δ)))) := by
  rw [subst_lamBlock, subst_lamBlock, subst_eqBlock, Terms.subst_rename,
    Sub.compRen_liftBlock_wkBlock, ← Terms.rename_subst, Terms.vars_subst_liftBlock,
    Terms.vars_subst_liftBlock]

@[simp] theorem subst_allC (σs : List Ty) {Γ Δ : Ctx} (s : Sub Sig Γ Δ) :
    (allC σs).subst s = allC σs := by
  match σs with
  | [_] => rfl
  | [] => exact congrArg Term.lam (subst_allC_body [] s)
  | σ :: σ' :: σs => exact congrArg Term.lam (subst_allC_body (σ :: σ' :: σs) s)

@[simp] theorem subst_exC (σs : List Ty) {Γ Δ : Ctx} (s : Sub Sig Γ Δ) :
    (exC σs).subst s = exC σs := by
  match σs with
  | [_] => rfl
  | [] => exact congrArg Term.lam (subst_exC_body [] s)
  | σ :: σ' :: σs => exact congrArg Term.lam (subst_exC_body (σ :: σ' :: σs) s)

@[simp] theorem subst_eqC (σs : List Ty) {Γ Δ : Ctx} (s : Sub Sig Γ Δ) :
    (eqC σs).subst s = eqC σs := by
  match σs with
  | [_] => rfl
  | [] => exact subst_eqC_body [] s
  | σ :: σ' :: σs => exact subst_eqC_body (σ :: σ' :: σs) s

end Term

/-- The body of a block abstraction, weakened past the block and applied to its
variables, converts back to the body. -/
theorem Conv.appBlock_lamBlock_vars (σs : List Ty) {Γ : Ctx} {ρ : RTy}
    (b : Term Sig (Ctx.block σs Γ) ρ) :
    Term.appBlock ((Term.lamBlock σs b).rename (Ren.wkBlock σs)) (Terms.vars σs Γ) ≡ b := by
  rw [Term.rename_lamBlock]
  refine Conv.trans (Conv.appBlock_lamBlock σs _ _) (Conv.of_eq ?_)
  rw [Term.rename_eq_subst, Term.subst_subst]
  show b.subst (Sub.comp (Sub.consBlock (Terms.vars σs Γ) Sub.id) (Sub.ofRen (Ren.liftBlock σs (Ren.wkBlock σs)))) = b
  have e : Sub.comp (Sub.consBlock (Terms.vars (Sig := Sig) σs Γ) Sub.id)
        (Sub.ofRen (Ren.liftBlock σs (Ren.wkBlock σs)))
      = Sub.compRen (Sub.consBlock (Terms.vars (Sig := Sig) σs Γ) Sub.id)
        (Ren.liftBlock σs (Ren.wkBlock σs)) := by
    funext τ v; rfl
  rw [e, Sub.compRen_consBlock_liftBlock]
  show b.subst (Sub.consBlock (Terms.vars σs Γ) (Sub.ofRen (Ren.wkBlock σs))) = b
  rw [Sub.consBlock_vars_wkBlock, Term.subst_id]

namespace Conv

/-- The block quantifier, as a constant applied to a block abstraction, is the block of
quantifiers. -/
theorem allC_lamBlock (σs : List Ty) {Γ : Ctx} (p : Formula Sig (Ctx.block σs Γ)) :
    Term.app (Term.allC σs) (Term.lamBlock σs p) ≡ Term.forallBlock σs p := by
  match σs, p with
  | [σ], p => exact Conv.refl _
  | [], p =>
    show Term.app (Term.lam (Term.appBlock ((Term.var .zero).rename Ren.id) .nil)) p ≡ p
    exact Conv.trans (Conv.beta _ p) (Conv.of_eq rfl)
  | σ :: σ' :: σs, p =>
    refine Conv.trans (Conv.beta _ _) ?_
    rw [Term.instantiate, Term.subst_forallBlock, Term.subst_appBlock, Term.subst_rename,
      Sub.compRen_liftBlock_wkBlock, Terms.vars_subst_liftBlock]
    exact Conv.forallBlock_congr _ (Conv.appBlock_lamBlock_vars _ p)

/-- The same for `∃`. -/
theorem exC_lamBlock (σs : List Ty) {Γ : Ctx} (p : Formula Sig (Ctx.block σs Γ)) :
    Term.app (Term.exC σs) (Term.lamBlock σs p) ≡ Term.existsBlock σs p := by
  match σs, p with
  | [σ], p => exact Conv.refl _
  | [], p =>
    show Term.app (Term.lam (Term.appBlock ((Term.var .zero).rename Ren.id) .nil)) p ≡ p
    exact Conv.trans (Conv.beta _ p) (Conv.of_eq rfl)
  | σ :: σ' :: σs, p =>
    refine Conv.trans (Conv.beta _ _) ?_
    rw [Term.instantiate, Term.subst_existsBlock, Term.subst_appBlock, Term.subst_rename,
      Sub.compRen_liftBlock_wkBlock, Terms.vars_subst_liftBlock]
    exact Conv.existsBlock_congr _ (Conv.appBlock_lamBlock_vars _ p)

/-- The block quantifier as a constant, applied to any predicate: the block of
quantifiers over the predicate applied to the block's variables. -/
theorem allC_eta (σs : List Ty) {Γ : Ctx} (F : Term Sig Γ (σs ⇒* .t)) :
    Term.app (Term.allC σs) F
      ≡ Term.forallBlock σs (Term.appBlock (F.rename (Ren.wkBlock σs)) (Terms.vars σs Γ)) :=
  Conv.trans (Conv.app_congr (Conv.refl _) (Conv.symm (Conv.lamBlock_appBlock σs F)))
    (Conv.allC_lamBlock σs _)

/-- The same for `∃`. -/
theorem exC_eta (σs : List Ty) {Γ : Ctx} (F : Term Sig Γ (σs ⇒* .t)) :
    Term.app (Term.exC σs) F
      ≡ Term.existsBlock σs (Term.appBlock (F.rename (Ren.wkBlock σs)) (Terms.vars σs Γ)) :=
  Conv.trans (Conv.app_congr (Conv.refl _) (Conv.symm (Conv.lamBlock_appBlock σs F)))
    (Conv.exC_lamBlock σs _)

/-- The block identity, as a constant applied to two tuples, is the conjunction of
identities. -/
theorem eqC_appBlock (σs : List Ty) {Γ : Ctx} (as bs : Terms Sig Γ σs) :
    Term.appBlock (Term.appBlock (Term.eqC σs) as) bs ≡ Term.eqBlock as bs := by
  match σs, as, bs with
  | [σ], .cons a .nil, .cons b .nil => exact Conv.refl _
  | [], .nil, .nil => exact Conv.refl _
  | σ :: σ' :: σs, as, bs =>
    show Term.appBlock (Term.appBlock (Term.lamBlock (σ :: σ' :: σs) (Term.lamBlock (σ :: σ' :: σs)
      (Term.eqBlock ((Terms.vars (σ :: σ' :: σs) Γ).rename (Ren.wkBlock (σ :: σ' :: σs)))
        (Terms.vars (σ :: σ' :: σs) (Ctx.block (σ :: σ' :: σs) Γ))))) as) bs ≡ _
    refine Conv.trans (appBlock_congr (Conv.appBlock_lamBlock _ _ as) (Terms.Conv.refl bs)) ?_
    rw [Term.subst_lamBlock]
    refine Conv.trans (Conv.appBlock_lamBlock _ _ bs) (Conv.of_eq ?_)
    rw [Term.subst_subst, Sub.comp_consBlock_liftBlock, Sub.comp_id_left, Term.subst_eqBlock,
      Terms.subst_rename, Sub.compRen_consBlock_wkBlock, Terms.vars_subst_consBlock,
      Terms.vars_subst_consBlock]

end Conv

/-! ### The pointwise operations at a block

At `σs ⇒* ρ` each type-subscripted operation is the operation at `ρ` applied pointwise over
the whole block: the paper's recursive definition, `n` of its steps at once. Each is proved
applied, by induction on the list (a δ-step, then β), and then bare, by η. -/

/-- Two weakenings, then an instantiation lifted under one binder, are one weakening. -/
theorem Term.weaken_weaken_subst_lift {Γ : Ctx} {σ τ υ : Ty} (X : Term Sig Γ σ) (Y : Term Sig Γ τ) :
    ((X.weaken (τ := τ)).weaken (τ := υ)).subst (Sub.lift (Sub.cons Y Sub.id)) = X.weaken := by
  rw [Term.weaken, Term.weaken, Term.subst_rename, Term.subst_rename, Term.weaken,
    Term.rename_eq_subst]
  rfl

namespace Conv

/-- `const_{σs ⇒* ρ} p` is `λx̄. const_ρ p`. -/
theorem app_constR_block : ∀ (σs : List Ty) {Γ : Ctx} (ρ : RTy) (p : Formula Sig Γ),
    Term.app (Term.constR (σs ⇒* ρ)) p
      ≡ Term.lamBlock σs (Term.app (Term.constR ρ) (p.rename (Ren.wkBlock σs)))
  | [], _, ρ, p => by
    show _ ≡ Term.app (Term.constR ρ) (p.rename Ren.id)
    rw [Term.rename_id]; exact Conv.refl _
  | σ :: σs, Γ, ρ, p => by
    refine Conv.trans (Conv.app_congr (Conv.delta rfl) (Conv.refl p)) ?_
    refine Conv.trans (Conv.beta _ p) ?_
    show Term.lam (Term.app (Term.constR (σs ⇒* ρ)) p.weaken) ≡ _
    refine Conv.trans (Conv.lam_congr (app_constR_block σs ρ p.weaken)) (Conv.of_eq ?_)
    show Term.lam _ = Term.lam _
    rw [Term.weaken, Term.rename_rename]; rfl

/-- `¬_{σs ⇒* ρ} X` is `λx̄. ¬_ρ (X x̄)`. -/
theorem app_negR_block : ∀ (σs : List Ty) {Γ : Ctx} (ρ : RTy) (X : Term Sig Γ (σs ⇒* ρ)),
    Term.app (Term.negR (σs ⇒* ρ)) X
      ≡ Term.lamBlock σs (Term.app (Term.negR ρ)
          (Term.appBlock (X.rename (Ren.wkBlock σs)) (Terms.vars σs Γ)))
  | [], _, ρ, X => by
    show _ ≡ Term.app (Term.negR ρ) (X.rename Ren.id)
    rw [Term.rename_id]; exact Conv.refl _
  | σ :: σs, Γ, ρ, X => by
    refine Conv.trans (Conv.app_congr (Conv.delta rfl) (Conv.refl X)) ?_
    refine Conv.trans (Conv.beta _ X) ?_
    show Term.lam (Term.app (Term.negR (σs ⇒* ρ)) (Term.app X.weaken (Term.var .zero))) ≡ _
    refine Conv.trans (Conv.lam_congr (app_negR_block σs ρ _)) (Conv.of_eq ?_)
    show Term.lam _ = Term.lam _
    rw [Term.appBlock_vars_cons]

/-- `□_{σs ⇒* ρ} X` is `λx̄. □_ρ (X x̄)`. -/
theorem app_boxR_block : ∀ (σs : List Ty) {Γ : Ctx} (ρ : RTy) (X : Term Sig Γ (σs ⇒* ρ)),
    Term.app (Term.boxR (σs ⇒* ρ)) X
      ≡ Term.lamBlock σs (Term.app (Term.boxR ρ)
          (Term.appBlock (X.rename (Ren.wkBlock σs)) (Terms.vars σs Γ)))
  | [], _, ρ, X => by
    show _ ≡ Term.app (Term.boxR ρ) (X.rename Ren.id)
    rw [Term.rename_id]; exact Conv.refl _
  | σ :: σs, Γ, ρ, X => by
    refine Conv.trans (Conv.app_congr (Conv.delta rfl) (Conv.refl X)) ?_
    refine Conv.trans (Conv.beta _ X) ?_
    show Term.lam (Term.app (Term.boxR (σs ⇒* ρ)) (Term.app X.weaken (Term.var .zero))) ≡ _
    refine Conv.trans (Conv.lam_congr (app_boxR_block σs ρ _)) (Conv.of_eq ?_)
    show Term.lam _ = Term.lam _
    rw [Term.appBlock_vars_cons]

/-- `X ∧_{σs ⇒* ρ} Y` is `λx̄. X x̄ ∧_ρ Y x̄`. -/
theorem app_andR_block : ∀ (σs : List Ty) {Γ : Ctx} (ρ : RTy) (X Y : Term Sig Γ (σs ⇒* ρ)),
    Term.app (Term.app (Term.andR (σs ⇒* ρ)) X) Y
      ≡ Term.lamBlock σs (Term.app (Term.app (Term.andR ρ)
          (Term.appBlock (X.rename (Ren.wkBlock σs)) (Terms.vars σs Γ)))
          (Term.appBlock (Y.rename (Ren.wkBlock σs)) (Terms.vars σs Γ)))
  | [], _, ρ, X, Y => by
    show _ ≡ Term.app (Term.app (Term.andR ρ) (X.rename Ren.id)) (Y.rename Ren.id)
    rw [Term.rename_id, Term.rename_id]; exact Conv.refl _
  | σ :: σs, Γ, ρ, X, Y => by
    refine Conv.trans (Conv.app_congr (Conv.app_congr (Conv.delta rfl) (Conv.refl X)) (Conv.refl Y)) ?_
    refine Conv.trans (Conv.app_congr (Conv.beta _ X) (Conv.refl Y)) ?_
    refine Conv.trans (Conv.beta _ Y) ?_
    show Term.lam (Term.app (Term.app (Term.andR (σs ⇒* ρ))
      (Term.app (((X.weaken).weaken).subst (Sub.lift (Sub.cons Y Sub.id))) (Term.var .zero)))
      (Term.app Y.weaken (Term.var .zero))) ≡ _
    rw [Term.weaken_weaken_subst_lift]
    refine Conv.trans (Conv.lam_congr (app_andR_block σs ρ _ _)) (Conv.of_eq ?_)
    show Term.lam _ = Term.lam _
    rw [Term.appBlock_vars_cons, Term.appBlock_vars_cons]

/-- `X ∨_{σs ⇒* ρ} Y` is `λx̄. X x̄ ∨_ρ Y x̄`. -/
theorem app_orR_block : ∀ (σs : List Ty) {Γ : Ctx} (ρ : RTy) (X Y : Term Sig Γ (σs ⇒* ρ)),
    Term.app (Term.app (Term.orR (σs ⇒* ρ)) X) Y
      ≡ Term.lamBlock σs (Term.app (Term.app (Term.orR ρ)
          (Term.appBlock (X.rename (Ren.wkBlock σs)) (Terms.vars σs Γ)))
          (Term.appBlock (Y.rename (Ren.wkBlock σs)) (Terms.vars σs Γ)))
  | [], _, ρ, X, Y => by
    show _ ≡ Term.app (Term.app (Term.orR ρ) (X.rename Ren.id)) (Y.rename Ren.id)
    rw [Term.rename_id, Term.rename_id]; exact Conv.refl _
  | σ :: σs, Γ, ρ, X, Y => by
    refine Conv.trans (Conv.app_congr (Conv.app_congr (Conv.delta rfl) (Conv.refl X)) (Conv.refl Y)) ?_
    refine Conv.trans (Conv.app_congr (Conv.beta _ X) (Conv.refl Y)) ?_
    refine Conv.trans (Conv.beta _ Y) ?_
    show Term.lam (Term.app (Term.app (Term.orR (σs ⇒* ρ))
      (Term.app (((X.weaken).weaken).subst (Sub.lift (Sub.cons Y Sub.id))) (Term.var .zero)))
      (Term.app Y.weaken (Term.var .zero))) ≡ _
    rw [Term.weaken_weaken_subst_lift]
    refine Conv.trans (Conv.lam_congr (app_orR_block σs ρ _ _)) (Conv.of_eq ?_)
    show Term.lam _ = Term.lam _
    rw [Term.appBlock_vars_cons, Term.appBlock_vars_cons]

/-- Coextensiveness at `σs ⇒* ρ` is `∀x̄. X x̄ ≡_ρ Y x̄`. -/
theorem app_coextR_block : ∀ (σs : List Ty) {Γ : Ctx} (ρ : RTy) (X Y : Term Sig Γ (σs ⇒* ρ)),
    Term.app (Term.app (Term.coextR (σs ⇒* ρ)) X) Y
      ≡ Term.forallBlock σs (Term.app (Term.app (Term.coextR ρ)
          (Term.appBlock (X.rename (Ren.wkBlock σs)) (Terms.vars σs Γ)))
          (Term.appBlock (Y.rename (Ren.wkBlock σs)) (Terms.vars σs Γ)))
  | [], _, ρ, X, Y => by
    show _ ≡ Term.app (Term.app (Term.coextR ρ) (X.rename Ren.id)) (Y.rename Ren.id)
    rw [Term.rename_id, Term.rename_id]; exact Conv.refl _
  | σ :: σs, Γ, ρ, X, Y => by
    refine Conv.trans (Conv.app_congr (Conv.app_congr (Conv.delta rfl) (Conv.refl X)) (Conv.refl Y)) ?_
    refine Conv.trans (Conv.app_congr (Conv.beta _ X) (Conv.refl Y)) ?_
    refine Conv.trans (Conv.beta _ Y) ?_
    show Term.forall' (Term.app (Term.app (Term.coextR (σs ⇒* ρ))
      (Term.app (((X.weaken).weaken).subst (Sub.lift (Sub.cons Y Sub.id))) (Term.var .zero)))
      (Term.app Y.weaken (Term.var .zero))) ≡ _
    rw [Term.weaken_weaken_subst_lift]
    refine Conv.trans (Conv.app_congr (Conv.refl _) (Conv.lam_congr (app_coextR_block σs ρ _ _)))
      (Conv.of_eq ?_)
    show Term.forall' _ = Term.forall' _
    rw [Term.appBlock_vars_cons, Term.appBlock_vars_cons]

/-- Pointwise implication at `σs ⇒* ρ` is `∀x̄. X x̄ ⊑_ρ Y x̄`. -/
theorem app_boxImpR_block : ∀ (σs : List Ty) {Γ : Ctx} (ρ : RTy) (X Y : Term Sig Γ (σs ⇒* ρ)),
    Term.app (Term.app (Term.boxImpR (σs ⇒* ρ)) X) Y
      ≡ Term.forallBlock σs (Term.app (Term.app (Term.boxImpR ρ)
          (Term.appBlock (X.rename (Ren.wkBlock σs)) (Terms.vars σs Γ)))
          (Term.appBlock (Y.rename (Ren.wkBlock σs)) (Terms.vars σs Γ)))
  | [], _, ρ, X, Y => by
    show _ ≡ Term.app (Term.app (Term.boxImpR ρ) (X.rename Ren.id)) (Y.rename Ren.id)
    rw [Term.rename_id, Term.rename_id]; exact Conv.refl _
  | σ :: σs, Γ, ρ, X, Y => by
    refine Conv.trans (Conv.app_congr (Conv.app_congr (Conv.delta rfl) (Conv.refl X)) (Conv.refl Y)) ?_
    refine Conv.trans (Conv.app_congr (Conv.beta _ X) (Conv.refl Y)) ?_
    refine Conv.trans (Conv.beta _ Y) ?_
    show Term.forall' (Term.app (Term.app (Term.boxImpR (σs ⇒* ρ))
      (Term.app (((X.weaken).weaken).subst (Sub.lift (Sub.cons Y Sub.id))) (Term.var .zero)))
      (Term.app Y.weaken (Term.var .zero))) ≡ _
    rw [Term.weaken_weaken_subst_lift]
    refine Conv.trans (Conv.app_congr (Conv.refl _) (Conv.lam_congr (app_boxImpR_block σs ρ _ _)))
      (Conv.of_eq ?_)
    show Term.forall' _ = Term.forall' _
    rw [Term.appBlock_vars_cons, Term.appBlock_vars_cons]

/-! The bare constants, at a block. -/

theorem constR_block (σs : List Ty) {Γ : Ctx} (ρ : RTy) :
    (Term.constR (σs ⇒* ρ) : Term Sig Γ _)
      ≡ Term.lam (Term.lamBlock σs (Term.app (Term.constR ρ)
          ((Term.var .zero : Term Sig (Ty.t :: Γ) Ty.t).rename (Ren.wkBlock σs)))) :=
  Conv.trans (Conv.symm (Conv.eta _)) (Conv.lam_congr (app_constR_block σs ρ (Term.var .zero)))

theorem negR_block (σs : List Ty) {Γ : Ctx} (ρ : RTy) :
    (Term.negR (σs ⇒* ρ) : Term Sig Γ _)
      ≡ Term.lam (Term.lamBlock σs (Term.app (Term.negR ρ)
          (Term.appBlock ((Term.var .zero : Term Sig (Ty.rel (σs ⇒* ρ) :: Γ) _).rename
            (Ren.wkBlock σs)) (Terms.vars σs _)))) :=
  Conv.trans (Conv.symm (Conv.eta _)) (Conv.lam_congr (app_negR_block σs ρ (Term.var .zero)))

theorem boxR_block (σs : List Ty) {Γ : Ctx} (ρ : RTy) :
    (Term.boxR (σs ⇒* ρ) : Term Sig Γ _)
      ≡ Term.lam (Term.lamBlock σs (Term.app (Term.boxR ρ)
          (Term.appBlock ((Term.var .zero : Term Sig (Ty.rel (σs ⇒* ρ) :: Γ) _).rename
            (Ren.wkBlock σs)) (Terms.vars σs _)))) :=
  Conv.trans (Conv.symm (Conv.eta _)) (Conv.lam_congr (app_boxR_block σs ρ (Term.var .zero)))

theorem andR_block (σs : List Ty) {Γ : Ctx} (ρ : RTy) :
    (Term.andR (σs ⇒* ρ) : Term Sig Γ _)
      ≡ Term.lam (Term.lam (Term.lamBlock σs (Term.app (Term.app (Term.andR ρ)
          (Term.appBlock ((Term.var (.succ .zero) :
            Term Sig (Ty.rel (σs ⇒* ρ) :: Ty.rel (σs ⇒* ρ) :: Γ) _).rename (Ren.wkBlock σs))
            (Terms.vars σs _)))
          (Term.appBlock ((Term.var .zero :
            Term Sig (Ty.rel (σs ⇒* ρ) :: Ty.rel (σs ⇒* ρ) :: Γ) _).rename (Ren.wkBlock σs))
            (Terms.vars σs _))))) :=
  Conv.trans (Conv.symm (Conv.eta _)) (Conv.lam_congr (Conv.trans (Conv.symm (Conv.eta _))
    (Conv.lam_congr (app_andR_block σs ρ (Term.var (.succ .zero)) (Term.var .zero)))))

theorem orR_block (σs : List Ty) {Γ : Ctx} (ρ : RTy) :
    (Term.orR (σs ⇒* ρ) : Term Sig Γ _)
      ≡ Term.lam (Term.lam (Term.lamBlock σs (Term.app (Term.app (Term.orR ρ)
          (Term.appBlock ((Term.var (.succ .zero) :
            Term Sig (Ty.rel (σs ⇒* ρ) :: Ty.rel (σs ⇒* ρ) :: Γ) _).rename (Ren.wkBlock σs))
            (Terms.vars σs _)))
          (Term.appBlock ((Term.var .zero :
            Term Sig (Ty.rel (σs ⇒* ρ) :: Ty.rel (σs ⇒* ρ) :: Γ) _).rename (Ren.wkBlock σs))
            (Terms.vars σs _))))) :=
  Conv.trans (Conv.symm (Conv.eta _)) (Conv.lam_congr (Conv.trans (Conv.symm (Conv.eta _))
    (Conv.lam_congr (app_orR_block σs ρ (Term.var (.succ .zero)) (Term.var .zero)))))

theorem coextR_block (σs : List Ty) {Γ : Ctx} (ρ : RTy) :
    (Term.coextR (σs ⇒* ρ) : Term Sig Γ _)
      ≡ Term.lam (Term.lam (Term.forallBlock σs (Term.app (Term.app (Term.coextR ρ)
          (Term.appBlock ((Term.var (.succ .zero) :
            Term Sig (Ty.rel (σs ⇒* ρ) :: Ty.rel (σs ⇒* ρ) :: Γ) _).rename (Ren.wkBlock σs))
            (Terms.vars σs _)))
          (Term.appBlock ((Term.var .zero :
            Term Sig (Ty.rel (σs ⇒* ρ) :: Ty.rel (σs ⇒* ρ) :: Γ) _).rename (Ren.wkBlock σs))
            (Terms.vars σs _))))) :=
  Conv.trans (Conv.symm (Conv.eta _)) (Conv.lam_congr (Conv.trans (Conv.symm (Conv.eta _))
    (Conv.lam_congr (app_coextR_block σs ρ (Term.var (.succ .zero)) (Term.var .zero)))))

theorem boxImpR_block (σs : List Ty) {Γ : Ctx} (ρ : RTy) :
    (Term.boxImpR (σs ⇒* ρ) : Term Sig Γ _)
      ≡ Term.lam (Term.lam (Term.forallBlock σs (Term.app (Term.app (Term.boxImpR ρ)
          (Term.appBlock ((Term.var (.succ .zero) :
            Term Sig (Ty.rel (σs ⇒* ρ) :: Ty.rel (σs ⇒* ρ) :: Γ) _).rename (Ren.wkBlock σs))
            (Terms.vars σs _)))
          (Term.appBlock ((Term.var .zero :
            Term Sig (Ty.rel (σs ⇒* ρ) :: Ty.rel (σs ⇒* ρ) :: Γ) _).rename (Ren.wkBlock σs))
            (Terms.vars σs _))))) :=
  Conv.trans (Conv.symm (Conv.eta _)) (Conv.lam_congr (Conv.trans (Conv.symm (Conv.eta _))
    (Conv.lam_congr (app_boxImpR_block σs ρ (Term.var (.succ .zero)) (Term.var .zero)))))

end Conv

/-! ### Holes over a block -/

namespace Hole

/-- The hole in the function position of a block application. -/
def appLBlock : ∀ {Γ Γ' : Ctx} {σs : List Ty} {ρ : RTy} {τ : Ty},
    Hole Sig Γ (σs ⇒* ρ) Γ' τ → Terms Sig Γ σs → Hole Sig Γ ρ Γ' τ
  | _, _, [], _, _, C, _ => C
  | _, _, _ :: _, _, _, C, as => appLBlock (.appL C as.head) as.tail

/-- The hole under a block abstraction. -/
def lamBlock : ∀ (σs : List Ty) {Γ Γ' : Ctx} {ρ : RTy} {τ : Ty},
    Hole Sig (Ctx.block σs Γ) ρ Γ' τ → Hole Sig Γ (σs ⇒* ρ) Γ' τ
  | [], _, _, _, _, C => C
  | _ :: σs, _, _, _, _, C => .lam (lamBlock σs C)

theorem plug_appLBlock : ∀ {Γ Γ' : Ctx} {σs : List Ty} {ρ : RTy} {τ : Ty}
    (C : Hole Sig Γ (σs ⇒* ρ) Γ' τ) (as : Terms Sig Γ σs) (a : Term Sig Γ' τ),
    (appLBlock C as).plug a = Term.appBlock (C.plug a) as
  | _, _, [], _, _, _, .nil, _ => rfl
  | _, _, _ :: _, _, _, C, .cons b bs, a => plug_appLBlock (.appL C b) bs a

theorem plug_lamBlock : ∀ (σs : List Ty) {Γ Γ' : Ctx} {ρ : RTy} {τ : Ty}
    (C : Hole Sig (Ctx.block σs Γ) ρ Γ' τ) (a : Term Sig Γ' τ),
    (lamBlock σs C).plug a = Term.lamBlock σs (C.plug a)
  | [], _, _, _, _, _, _ => rfl
  | _ :: σs, _, _, _, _, C, a => congrArg Term.lam (plug_lamBlock σs C a)

end Hole

/-! ### The block rules, derived -/

/-- Hypotheses weakened past a block. -/
abbrev Hyps.wkBlock (σs : List Ty) {Γ : Ctx} (Δ : List (Formula Sig Γ)) :
    List (Formula Sig (Ctx.block σs Γ)) :=
  Δ.map (Term.rename (Ren.wkBlock σs))

theorem Hyps.wkBlock_nil {Γ : Ctx} : ∀ (Δ : List (Formula Sig Γ)), Hyps.wkBlock [] Δ = Δ
  | [] => rfl
  | a :: Δ => by
    show (a.rename Ren.id) :: Hyps.wkBlock [] Δ = a :: Δ
    rw [Term.rename_id, Hyps.wkBlock_nil Δ]

theorem Hyps.wkBlock_cons (σ : Ty) (σs : List Ty) {Γ : Ctx} (Δ : List (Formula Sig Γ)) :
    Hyps.wkBlock (σ :: σs) Δ = Hyps.wkBlock σs (Hyps.weaken (σ := σ) Δ) := by
  simp only [Hyps.wkBlock, Hyps.weaken, List.map_map]
  congr 1
  funext a
  show a.rename (Ren.comp (Ren.wkBlock σs) Ren.shift) = (a.rename Ren.shift).rename (Ren.wkBlock σs)
  rw [Term.rename_rename]

namespace Derivable

variable {Ax : AxiomSet Sig}

/-- `∀`-introduction over a block. -/
theorem allIBlock : ∀ (σs : List Ty) {Γ : Ctx} {Δ : List (Formula Sig Γ)}
    {p : Formula Sig (Ctx.block σs Γ)},
    Derivable Ax (Hyps.wkBlock σs Δ) p → Derivable Ax Δ (Term.forallBlock σs p)
  | [], _, Δ, _, h => by
    rw [Hyps.wkBlock_nil] at h; exact h
  | σ :: σs, _, Δ, _, h => by
    rw [Hyps.wkBlock_cons] at h
    exact allI (allIBlock σs h)

/-- `∀`-elimination over a block: the body at a tuple. -/
theorem allEBlock : ∀ (σs : List Ty) {Γ : Ctx} {Δ : List (Formula Sig Γ)}
    {p : Formula Sig (Ctx.block σs Γ)},
    Derivable Ax Δ (Term.forallBlock σs p) → (as : Terms Sig Γ σs) →
      Derivable Ax Δ (p.subst (Sub.consBlock as Sub.id))
  | [], _, _, p, h, .nil => by
    show Derivable Ax _ (p.subst Sub.id)
    rw [Term.subst_id]; exact h
  | _ :: σs, Γ, _, p, h, .cons a as => by
    have h₁ := allEβ h a
    rw [Term.instantiate, Term.subst_forallBlock] at h₁
    have h₂ := allEBlock σs h₁ as
    rw [Term.subst_subst, Sub.comp_consBlock_liftBlock, Sub.comp_id_left] at h₂
    exact h₂

/-- `∃`-introduction over a block: the body at a tuple. -/
theorem exIBlock : ∀ (σs : List Ty) {Γ : Ctx} {Δ : List (Formula Sig Γ)}
    {p : Formula Sig (Ctx.block σs Γ)} (as : Terms Sig Γ σs),
    Derivable Ax Δ (p.subst (Sub.consBlock as Sub.id)) → Derivable Ax Δ (Term.existsBlock σs p)
  | [], _, _, p, .nil, h => by
    rw [show Sub.consBlock (.nil : Terms Sig _ []) Sub.id = Sub.id from rfl, Term.subst_id] at h
    exact h
  | _ :: σs, Γ, _, p, .cons a as, h => by
    apply exIβ a
    rw [Term.instantiate, Term.subst_existsBlock]
    apply exIBlock σs as
    rw [Term.subst_subst, Sub.comp_consBlock_liftBlock, Sub.comp_id_left]
    exact h

/-- The body of a `λ` over the weakened variable, `(λv. B[⇑]) v`, converts to `B`. -/
theorem _root_.Classicism.Meta.Conv.app_lam_weaken_zero {Γ : Ctx} {σ : Ty} {ρ : RTy}
    (b : Term Sig (σ :: Γ) ρ) :
    Term.app (Term.lam b).weaken (Term.var .zero) ≡ b := by
  refine Conv.trans (Conv.beta _ _) (Conv.of_eq ?_)
  show (b.rename (Ren.lift Ren.shift)).subst (Sub.cons (Term.var .zero) Sub.id) = b
  rw [Term.subst_rename]
  conv => rhs; rw [← Term.subst_id b]
  congr 1
  funext τ v
  cases v <;> rfl

/-- `∃`-elimination over a block. -/
theorem exEBlock : ∀ (σs : List Ty) {Γ : Ctx} {Δ : List (Formula Sig Γ)}
    {p : Formula Sig (Ctx.block σs Γ)} {r : Formula Sig Γ},
    Derivable Ax Δ (Term.existsBlock σs p) →
    Derivable Ax (p :: Hyps.wkBlock σs Δ) (r.rename (Ren.wkBlock σs)) → Derivable Ax Δ r
  | [], _, Δ, p, r, h, h' => by
    have e' : r.rename (Ren.wkBlock []) = r := Term.rename_id r
    rw [Hyps.wkBlock_nil, e'] at h'
    exact impE (impI h') h
  | σ :: σs, Γ, Δ, p, r, h, h' => by
    refine exE h ?_
    have hyp' : Derivable Ax (Term.app (Term.lam (Term.existsBlock σs p)).weaken (Term.var .zero) ::
        Hyps.weaken Δ) (Term.existsBlock σs p) :=
      conv hyp₀ (Conv.app_lam_weaken_zero _)
    have e : r.weaken.rename (Ren.wkBlock σs) = r.rename (Ren.wkBlock (σ :: σs)) := by
      show (r.rename Ren.shift).rename (Ren.wkBlock σs) = r.rename (Ren.comp (Ren.wkBlock σs) Ren.shift)
      rw [Term.rename_rename]
    have h'' : Derivable Ax (p :: Hyps.wkBlock σs
        (Term.app (Term.lam (Term.existsBlock σs p)).weaken (Term.var .zero) :: Hyps.weaken Δ))
        (r.weaken.rename (Ren.wkBlock σs)) := by
      rw [e]
      refine weaken h' ?_
      intro x hx
      simp only [List.mem_cons] at hx ⊢
      rcases hx with rfl | hx
      · exact Or.inl rfl
      · right
        simp only [Hyps.wkBlock, List.map_cons, List.mem_cons]
        right
        rw [Hyps.wkBlock_cons] at hx; exact hx
    exact exEBlock σs hyp' h''

/-- Reflexivity over a block. -/
theorem reflBlock : ∀ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σs : List Ty} (as : Terms Sig Γ σs),
    Derivable Ax Δ (Term.eqBlock as as)
  | _, _, [], .nil => top
  | _, _, [_], .cons a .nil => refl a
  | _, _, _ :: _ :: _, .cons a as => andI (refl a) (reflBlock as)

/-- Leibniz's Law over a block. -/
theorem llBlock : ∀ (σs : List Ty) {Γ : Ctx} {Δ : List (Formula Sig Γ)}
    (P : Formula Sig (Ctx.block σs Γ)) {as bs : Terms Sig Γ σs},
    Derivable Ax Δ (Term.eqBlock as bs) → Derivable Ax Δ (P.subst (Sub.consBlock as Sub.id)) →
      Derivable Ax Δ (P.subst (Sub.consBlock bs Sub.id))
  | [], _, _, _, .nil, .nil, _, h => h
  | [_], _, _, P, .cons a .nil, .cons b .nil, he, h => llβ P he h
  | σ :: σ' :: σs, Γ, Δ, P, .cons a as, .cons b bs, he, h => by
    -- first the tail, with `a` in place
    have h₁ : Derivable Ax Δ ((P.subst (Sub.liftBlock (σ' :: σs) (Sub.cons a Sub.id))).subst
        (Sub.consBlock as Sub.id)) := by
      rw [Term.subst_subst, Sub.comp_consBlock_liftBlock, Sub.comp_id_left]; exact h
    have h₂ := llBlock (σ' :: σs) _ (andE₂ he) h₁
    rw [Term.subst_subst, Sub.comp_consBlock_liftBlock, Sub.comp_id_left] at h₂
    -- then the head
    let Q : Formula Sig (σ :: Γ) := P.subst (Sub.consBlock (bs.rename Ren.shift) Sub.id)
    have hQ : ∀ c : Term Sig Γ σ, Q.instantiate c = P.subst (Sub.consBlock bs (Sub.cons c Sub.id)) := by
      intro c
      show (P.subst _).subst _ = _
      rw [Term.subst_subst, Sub.comp_consBlock, Terms.subst_rename, Sub.compRen_cons_shift,
        Terms.subst_id]
      rfl
    have h₃ : Derivable Ax Δ (Q.instantiate a) := by rw [hQ]; exact h₂
    have h₄ := llβ Q (andE₁ he) h₃
    rw [hQ] at h₄
    exact h₄

/-! ### The rules for the block constants

The quantifier and identity rules once more, for `allC`, `exC` and `eqC` applied to an
arbitrary predicate or tuple: the form in which the generic vectorization of a rule's
premises and conclusion comes out. -/

/-- `UI` for the block quantifier as a constant. -/
theorem allEC (σs : List Ty) {Γ : Ctx} {Δ : List (Formula Sig Γ)} {F : Term Sig Γ (σs ⇒* .t)}
    (h : Derivable Ax Δ (Term.app (Term.allC σs) F)) (as : Terms Sig Γ σs) :
    Derivable Ax Δ (Term.appBlock F as) := by
  have := allEBlock σs (conv h (Conv.allC_eta σs F)) as
  rw [Term.appBlock_vars_subst_consBlock] at this
  exact this

/-- `Gen` for the block quantifier as a constant. -/
theorem allIC (σs : List Ty) {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig (Ctx.block σs Γ)}
    (h : Derivable Ax (Hyps.wkBlock σs Δ) p) :
    Derivable Ax Δ (Term.app (Term.allC σs) (Term.lamBlock σs p)) :=
  conv (allIBlock σs h) (Conv.symm (Conv.allC_lamBlock σs p))

/-- `EG` for the block quantifier as a constant. -/
theorem exIC (σs : List Ty) {Γ : Ctx} {Δ : List (Formula Sig Γ)} {F : Term Sig Γ (σs ⇒* .t)}
    (as : Terms Sig Γ σs) (h : Derivable Ax Δ (Term.appBlock F as)) :
    Derivable Ax Δ (Term.app (Term.exC σs) F) := by
  refine conv (exIBlock σs as ?_) (Conv.symm (Conv.exC_eta σs F))
  rw [Term.appBlock_vars_subst_consBlock]; exact h

/-- `Inst` for the block quantifier as a constant. -/
theorem exEC (σs : List Ty) {Γ : Ctx} {Δ : List (Formula Sig Γ)} {F : Term Sig Γ (σs ⇒* .t)}
    {r : Formula Sig Γ} (h : Derivable Ax Δ (Term.app (Term.exC σs) F))
    (h' : Derivable Ax (Term.appBlock (F.rename (Ren.wkBlock σs)) (Terms.vars σs Γ) ::
      Hyps.wkBlock σs Δ) (r.rename (Ren.wkBlock σs))) :
    Derivable Ax Δ r :=
  exEBlock σs (conv h (Conv.exC_eta σs F)) h'

/-- `Ref` for the block identity as a constant. -/
theorem reflC {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σs : List Ty} (as : Terms Sig Γ σs) :
    Derivable Ax Δ (Term.appBlock (Term.appBlock (Term.eqC σs) as) as) :=
  conv (reflBlock as) (Conv.symm (Conv.eqC_appBlock σs as as))

/-- `LL` for the block identity as a constant. -/
theorem llC (σs : List Ty) {Γ : Ctx} {Δ : List (Formula Sig Γ)} (F : Term Sig Γ (σs ⇒* .t))
    {as bs : Terms Sig Γ σs}
    (he : Derivable Ax Δ (Term.appBlock (Term.appBlock (Term.eqC σs) as) bs))
    (h : Derivable Ax Δ (Term.appBlock F as)) : Derivable Ax Δ (Term.appBlock F bs) := by
  have := llBlock σs (Term.appBlock (F.rename (Ren.wkBlock σs)) (Terms.vars σs Γ))
    (conv he (Conv.eqC_appBlock σs as bs)) (by rw [Term.appBlock_vars_subst_consBlock]; exact h)
  rw [Term.appBlock_vars_subst_consBlock] at this
  exact this

end Derivable

/-! ### Checks: one-element blocks are the unblocked forms, on the nose -/

section Checks
variable {Γ : Ctx}

example (σ : Ty) (ρ : RTy) : [σ] ⇒* ρ = σ ⇒ ρ := rfl
example (σ : Ty) (p : Formula Sig (σ :: Γ)) : Term.forallBlock [σ] p = Term.forall' p := rfl
example (σ : Ty) (p : Formula Sig (σ :: Γ)) : Term.existsBlock [σ] p = Term.exists' p := rfl
example (σ : Ty) {ρ : RTy} (b : Term Sig (σ :: Γ) ρ) : Term.lamBlock [σ] b = Term.lam b := rfl
example (σ : Ty) {ρ : RTy} (f : Term Sig Γ (σ ⇒ ρ)) (a : Term Sig Γ σ) :
    Term.appBlock f (.single a) = Term.app f a := rfl
example (σ : Ty) (a b : Term Sig Γ σ) : Term.eqBlock (.single a) (.single b) = Term.eq' a b := rfl
-- for any one-element tuple, not only a literal one
example (σ : Ty) {ρ : RTy} (f : Term Sig Γ (σ ⇒ ρ)) (as : Terms Sig Γ [σ]) :
    Term.appBlock f as = Term.app f as.head1 := rfl
example (σ : Ty) (as bs : Terms Sig Γ [σ]) : Term.eqBlock as bs = Term.eq' as.head1 bs.head1 := rfl
example (σ : Ty) {Δ : Ctx} (r : Ren Γ Δ) (as : Terms Sig Γ [σ]) :
    (as.rename r).head1 = as.head1.rename r := rfl
example (σ : Ty) : (Term.allC [σ] : Term Sig Γ _) = Term.all σ := rfl
example (σ : Ty) : (Term.eqC [σ] : Term Sig Γ _) = Term.eq σ := rfl
-- the empty block: no quantifier, and `⊤` for identity
example (p : Formula Sig Γ) : Term.forallBlock [] p = p := rfl
example : Term.eqBlock (.nil : Terms Sig Γ []) .nil = Term.top := rfl
-- two elements: two quantifiers, outermost first, and a conjunction
example (σ τ : Ty) (p : Formula Sig (τ :: σ :: Γ)) :
    Term.forallBlock [σ, τ] p = Term.forall' (Term.forall' p) := rfl
example (σ τ : Ty) (a b : Term Sig Γ σ) (c d : Term Sig Γ τ) :
    Term.eqBlock (.cons a (.single c)) (.cons b (.single d))
      = Term.conj (Term.eq' a b) (Term.eq' c d) := rfl

end Checks

end Classicism.Meta
