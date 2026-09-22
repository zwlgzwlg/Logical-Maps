import Classicism.Meta.Types

/-!
# Terms of the object language

The terms of Classicism's language `L(Sig)` over a signature `Sig` of nonlogical constants
(Classicism, §1.1), as an **intrinsically typed** syntax: `Term Sig Γ σ` is the type of terms
of type `σ` whose free variables are those of the context `Γ`, so that an ill-typed term
cannot be written down. Variables are de Bruijn indices into `Γ`, which makes
α-equivalence syntactic identity and leaves β and η as the only conversions.

The logical constants are the paper's: `∧`, `∨`, `¬`, and at each type `σ` the
quantifiers `∀σ`, `∃σ` and identity `=σ`. They are constants, so application and
abstraction are the only ways to build a term; the paper's abbreviations `→`, `↔`, `⊤`,
`⊥`, `□` follow in `Term.imp` and friends.

The two operations every later module rests on are renaming and substitution, each a map
on variables lifted through binders, with the four composition laws relating them. These
are the standard de Bruijn algebra; nothing in them is specific to Classicism.
-/

namespace Classicism.Meta

/-- A signature: a type of nonlogical constants, each with a type of `R`. -/
structure Signature where
  /-- The constants. -/
  Const : Type
  /-- The type of each constant. -/
  typeOf : Const → Ty

/-- The pure language, with no nonlogical constants. -/
def Signature.pure : Signature := ⟨Empty, Empty.elim⟩

/-- A context: the types of the variables in scope, innermost first. -/
abbrev Ctx := List Ty

/-- A variable: a de Bruijn index into the context, carrying its type. -/
inductive Var : Ctx → Ty → Type
  /-- The innermost variable. -/
  | zero {Γ : Ctx} {σ : Ty} : Var (σ :: Γ) σ
  /-- A variable from further out. -/
  | succ {Γ : Ctx} {σ τ : Ty} : Var Γ σ → Var (τ :: Γ) σ
  deriving DecidableEq

/-- Terms of `L(Sig)` in context `Γ`, at type `σ`. -/
inductive Term (Sig : Signature) : Ctx → Ty → Type
  /-- A variable. -/
  | var {Γ σ} : Var Γ σ → Term Sig Γ σ
  /-- A nonlogical constant of `Sig`. -/
  | const {Γ} (c : Sig.Const) : Term Sig Γ (Sig.typeOf c)
  /-- Application. -/
  | app {Γ : Ctx} {σ : Ty} {ρ : RTy} : Term Sig Γ (σ ⇒ ρ) → Term Sig Γ σ → Term Sig Γ ρ
  /-- Abstraction over the innermost variable. -/
  | lam {Γ : Ctx} {σ : Ty} {ρ : RTy} : Term Sig (σ :: Γ) ρ → Term Sig Γ (σ ⇒ ρ)
  /-- Conjunction, of type `t → t → t`. -/
  | and {Γ} : Term Sig Γ (RTy.t ⇒ RTy.t ⇒ RTy.t)
  /-- Disjunction. -/
  | or {Γ} : Term Sig Γ (RTy.t ⇒ RTy.t ⇒ RTy.t)
  /-- Negation. -/
  | not {Γ} : Term Sig Γ (RTy.t ⇒ RTy.t)
  /-- The universal quantifier at `σ`, of type `(σ → t) → t`. -/
  | all {Γ} (σ : Ty) : Term Sig Γ ((σ ⇒ RTy.t) ⇒ RTy.t)
  /-- The existential quantifier at `σ`. -/
  | ex {Γ} (σ : Ty) : Term Sig Γ ((σ ⇒ RTy.t) ⇒ RTy.t)
  /-- Identity at `σ`, of type `σ → σ → t`. -/
  | eq {Γ} (σ : Ty) : Term Sig Γ (σ ⇒ σ ⇒ RTy.t)

/-- A formula: a term of type `t`. -/
abbrev Formula (Sig : Signature) (Γ : Ctx) : Type := Term Sig Γ RTy.t

/-- A sentence: a closed formula. -/
abbrev Sentence (Sig : Signature) : Type := Formula Sig []

namespace Term

variable {Sig : Signature} {Γ : Ctx}

/-! ### The paper's abbreviations, Figure 1 -/

/-- `P ∧ Q`. -/
abbrev conj (p q : Formula Sig Γ) : Formula Sig Γ := .app (.app .and p) q
/-- `P ∨ Q`. -/
abbrev disj (p q : Formula Sig Γ) : Formula Sig Γ := .app (.app .or p) q
/-- `¬P`. -/
abbrev neg (p : Formula Sig Γ) : Formula Sig Γ := .app .not p
/-- `P → Q := ¬P ∨ Q`. -/
abbrev imp (p q : Formula Sig Γ) : Formula Sig Γ := disj (neg p) q
/-- `P ↔ Q := (P → Q) ∧ (Q → P)`. -/
abbrev iff (p q : Formula Sig Γ) : Formula Sig Γ := conj (imp p q) (imp q p)
/-- `∀v. P`, for `P` a formula with one more variable in scope: `∀σ (λv. P)`. -/
abbrev forall' {σ : Ty} (p : Formula Sig (σ :: Γ)) : Formula Sig Γ := .app (.all σ) (.lam p)
/-- `∃v. P`. -/
abbrev exists' {σ : Ty} (p : Formula Sig (σ :: Γ)) : Formula Sig Γ := .app (.ex σ) (.lam p)
/-- `A = B` at type `σ`. -/
abbrev eq' {σ : Ty} (a b : Term Sig Γ σ) : Formula Sig Γ := .app (.app (.eq σ) a) b
/-- `⊤ := ∀p.p ∨ ¬∀p.p`. -/
abbrev top : Formula Sig Γ :=
  disj (forall' (.var .zero)) (neg (forall' (.var .zero)))
/-- `⊥ := ∀p.p ∧ ¬∀p.p`. -/
abbrev bot : Formula Sig Γ :=
  conj (forall' (.var .zero)) (neg (forall' (.var .zero)))
/-- `□P := (P = ⊤)`. -/
abbrev box (p : Formula Sig Γ) : Formula Sig Γ := eq' p top
/-- `◇P := ¬□¬P`. -/
abbrev dia (p : Formula Sig Γ) : Formula Sig Γ := neg (box (neg p))

/-! ### Purity

A term is pure when it contains no nonlogical constant. Over the pure signature every
term is; over another, this is the side condition of No Pure Contingency and of the
Maximalist principles. -/

/-- Does the term contain no nonlogical constant? -/
def pure : ∀ {Γ : Ctx} {σ : Ty}, Term Sig Γ σ → Bool
  | _, _, .var _ => true
  | _, _, .const _ => false
  | _, _, .app f a => f.pure && a.pure
  | _, _, .lam b => b.pure
  | _, _, .and | _, _, .or | _, _, .not | _, _, .all _ | _, _, .ex _ | _, _, .eq _ => true

/-! ### Renaming -/

end Term

/-- A renaming: a type-preserving map of variables from one context to another. -/
def Ren (Γ Δ : Ctx) : Type := ∀ σ : Ty, Var Γ σ → Var Δ σ

namespace Ren

variable {Γ Δ Θ : Ctx}

/-- The identity renaming. -/
def id : Ren Γ Γ := fun _ v => v

/-- Composition. -/
def comp (r : Ren Δ Θ) (r' : Ren Γ Δ) : Ren Γ Θ := fun _ v => r _ (r' _ v)

/-- Push a renaming under a binder. -/
def lift (r : Ren Γ Δ) {σ : Ty} : Ren (σ :: Γ) (σ :: Δ)
  | _, .zero => .zero
  | _, .succ v => .succ (r _ v)

/-- The renaming that moves everything out past a new innermost variable. -/
def shift {σ : Ty} : Ren Γ (σ :: Γ) := fun _ v => .succ v

@[simp] theorem lift_zero (r : Ren Γ Δ) {σ : Ty} : Ren.lift r (σ := σ) _ .zero = .zero := rfl
@[simp] theorem lift_succ (r : Ren Γ Δ) {σ τ : Ty} (v : Var Γ σ) :
    Ren.lift r (σ := τ) _ (.succ v) = .succ (r _ v) := rfl

theorem lift_id {σ : Ty} : Ren.lift (Ren.id : Ren Γ Γ) (σ := σ) = Ren.id := by
  funext τ v; cases v <;> rfl

theorem lift_comp (r : Ren Δ Θ) (r' : Ren Γ Δ) {σ : Ty} :
    Ren.lift (Ren.comp r r') (σ := σ) = Ren.comp (Ren.lift r) (Ren.lift r') := by
  funext τ v; cases v <;> rfl

end Ren

namespace Term

variable {Sig : Signature}

/-- Apply a renaming to a term. -/
def rename : ∀ {Γ Δ : Ctx}, Ren Γ Δ → ∀ {σ : Ty}, Term Sig Γ σ → Term Sig Δ σ
  | _, _, r, _, .var v => .var (r _ v)
  | _, _, _, _, .const c => .const c
  | _, _, r, _, .app f a => .app (f.rename r) (a.rename r)
  | _, _, r, _, .lam b => .lam (b.rename (Ren.lift r))
  | _, _, _, _, .and => .and
  | _, _, _, _, .or => .or
  | _, _, _, _, .not => .not
  | _, _, _, _, .all σ => .all σ
  | _, _, _, _, .ex σ => .ex σ
  | _, _, _, _, .eq σ => .eq σ

/-- Weakening: the same term, with a new innermost variable it does not mention. -/
abbrev weaken {Γ : Ctx} {τ σ : Ty} (a : Term Sig Γ σ) : Term Sig (τ :: Γ) σ := a.rename Ren.shift

theorem rename_id : ∀ {Γ : Ctx} {σ : Ty} (a : Term Sig Γ σ), a.rename Ren.id = a
  | _, _, .var _ | _, _, .const _ | _, _, .and | _, _, .or | _, _, .not
  | _, _, .all _ | _, _, .ex _ | _, _, .eq _ => rfl
  | _, _, .app f a => by simp [rename, rename_id f, rename_id a]
  | _, _, .lam b => by simp [rename, Ren.lift_id, rename_id b]

theorem rename_rename : ∀ {Γ Δ Θ : Ctx} (r : Ren Δ Θ) (r' : Ren Γ Δ) {σ : Ty} (a : Term Sig Γ σ),
    (a.rename r').rename r = a.rename (Ren.comp r r')
  | _, _, _, _, _, _, .var _ | _, _, _, _, _, _, .const _ | _, _, _, _, _, _, .and
  | _, _, _, _, _, _, .or | _, _, _, _, _, _, .not | _, _, _, _, _, _, .all _
  | _, _, _, _, _, _, .ex _ | _, _, _, _, _, _, .eq _ => rfl
  | _, _, _, r, r', _, .app f a => by simp [rename, rename_rename r r' f, rename_rename r r' a]
  | _, _, _, r, r', _, .lam b => by
    simp [rename, rename_rename (Ren.lift r) (Ren.lift r') b, Ren.lift_comp]

end Term

/-! ### Substitution -/

/-- A substitution: a type-preserving map from the variables of one context to terms over
another. -/
def Sub (Sig : Signature) (Γ Δ : Ctx) : Type := ∀ σ : Ty, Var Γ σ → Term Sig Δ σ

namespace Sub

variable {Sig : Signature} {Γ Δ Θ : Ctx}

/-- The identity substitution. -/
def id : Sub Sig Γ Γ := fun _ v => .var v

/-- Push a substitution under a binder: the new variable is kept, the rest are weakened. -/
def lift (s : Sub Sig Γ Δ) {σ : Ty} : Sub Sig (σ :: Γ) (σ :: Δ)
  | _, .zero => .var .zero
  | _, .succ v => (s _ v).weaken

/-- Extend a substitution with a term for a new innermost variable. -/
def cons {σ : Ty} (a : Term Sig Δ σ) (s : Sub Sig Γ Δ) : Sub Sig (σ :: Γ) Δ
  | _, .zero => a
  | _, .succ v => s _ v

/-- A renaming, as a substitution. -/
def ofRen (r : Ren Γ Δ) : Sub Sig Γ Δ := fun _ v => .var (r _ v)

@[simp] theorem lift_zero (s : Sub Sig Γ Δ) {σ : Ty} : Sub.lift s (σ := σ) _ .zero = .var .zero := rfl
@[simp] theorem lift_succ (s : Sub Sig Γ Δ) {σ τ : Ty} (v : Var Γ σ) :
    Sub.lift s (σ := τ) _ (.succ v) = (s _ v).weaken := rfl
@[simp] theorem cons_zero {σ : Ty} (a : Term Sig Δ σ) (s : Sub Sig Γ Δ) : cons a s _ .zero = a := rfl
@[simp] theorem cons_succ {σ τ : Ty} (a : Term Sig Δ σ) (s : Sub Sig Γ Δ) (v : Var Γ τ) :
    cons a s _ (.succ v) = s _ v := rfl

theorem lift_id {σ : Ty} : Sub.lift (Sub.id : Sub Sig Γ Γ) (σ := σ) = Sub.id := by
  funext τ v; cases v <;> rfl

theorem lift_ofRen (r : Ren Γ Δ) {σ : Ty} :
    Sub.lift (ofRen r : Sub Sig Γ Δ) (σ := σ) = ofRen (Ren.lift r) := by
  funext τ v; cases v <;> rfl

end Sub

namespace Term

variable {Sig : Signature}

/-- Apply a substitution to a term. -/
def subst : ∀ {Γ Δ : Ctx}, Sub Sig Γ Δ → ∀ {σ : Ty}, Term Sig Γ σ → Term Sig Δ σ
  | _, _, s, _, .var v => s _ v
  | _, _, _, _, .const c => .const c
  | _, _, s, _, .app f a => .app (f.subst s) (a.subst s)
  | _, _, s, _, .lam b => .lam (b.subst (Sub.lift s))
  | _, _, _, _, .and => .and
  | _, _, _, _, .or => .or
  | _, _, _, _, .not => .not
  | _, _, _, _, .all σ => .all σ
  | _, _, _, _, .ex σ => .ex σ
  | _, _, _, _, .eq σ => .eq σ

/-- `b[a]`: substitute `a` for the innermost variable of `b`. This is what a β-step
does, and what instantiating a quantifier does. -/
abbrev instantiate {Γ : Ctx} {σ τ : Ty} (b : Term Sig (σ :: Γ) τ) (a : Term Sig Γ σ) :
    Term Sig Γ τ :=
  b.subst (Sub.cons a Sub.id)

theorem subst_id : ∀ {Γ : Ctx} {σ : Ty} (a : Term Sig Γ σ), a.subst Sub.id = a
  | _, _, .var _ | _, _, .const _ | _, _, .and | _, _, .or | _, _, .not
  | _, _, .all _ | _, _, .ex _ | _, _, .eq _ => rfl
  | _, _, .app f a => by simp [subst, subst_id f, subst_id a]
  | _, _, .lam b => by simp [subst, Sub.lift_id, subst_id b]

/-- A renaming is the substitution that sends each variable to a variable. -/
theorem rename_eq_subst : ∀ {Γ Δ : Ctx} (r : Ren Γ Δ) {σ : Ty} (a : Term Sig Γ σ),
    a.rename r = a.subst (Sub.ofRen r)
  | _, _, _, _, .var _ | _, _, _, _, .const _ | _, _, _, _, .and | _, _, _, _, .or
  | _, _, _, _, .not | _, _, _, _, .all _ | _, _, _, _, .ex _ | _, _, _, _, .eq _ => rfl
  | _, _, r, _, .app f a => by simp [rename, subst, rename_eq_subst r f, rename_eq_subst r a]
  | _, _, r, _, .lam b => by
    simp [rename, subst, rename_eq_subst (Ren.lift r) b, Sub.lift_ofRen]

/-! The four composition laws. `subst_rename` and `rename_subst` are the two mixed cases,
which the lifting lemmas need, and `subst_subst` is the one that matters downstream. -/

/-- The composite substitution `s ∘ r`, on variables. -/
def _root_.Classicism.Meta.Sub.compRen {Γ Δ Θ : Ctx} (s : Sub Sig Δ Θ) (r : Ren Γ Δ) : Sub Sig Γ Θ :=
  fun _ v => s _ (r _ v)
/-- The composite `r ∘ s`, applying a renaming to the terms of a substitution. -/
def _root_.Classicism.Meta.Ren.compSub {Γ Δ Θ : Ctx} (r : Ren Δ Θ) (s : Sub Sig Γ Δ) : Sub Sig Γ Θ :=
  fun _ v => (s _ v).rename r
/-- The composite of two substitutions. -/
def _root_.Classicism.Meta.Sub.comp {Γ Δ Θ : Ctx} (s : Sub Sig Δ Θ) (s' : Sub Sig Γ Δ) : Sub Sig Γ Θ :=
  fun _ v => (s' _ v).subst s

theorem _root_.Classicism.Meta.Sub.lift_compRen {Γ Δ Θ : Ctx} (s : Sub Sig Δ Θ) (r : Ren Γ Δ) {σ : Ty} :
    Sub.lift (Sub.compRen s r) (σ := σ) = Sub.compRen (Sub.lift s) (Ren.lift r) := by
  funext τ v; cases v <;> rfl

theorem subst_rename : ∀ {Γ Δ Θ : Ctx} (s : Sub Sig Δ Θ) (r : Ren Γ Δ) {σ : Ty} (a : Term Sig Γ σ),
    (a.rename r).subst s = a.subst (Sub.compRen s r)
  | _, _, _, _, _, _, .var _ | _, _, _, _, _, _, .const _ | _, _, _, _, _, _, .and
  | _, _, _, _, _, _, .or | _, _, _, _, _, _, .not | _, _, _, _, _, _, .all _
  | _, _, _, _, _, _, .ex _ | _, _, _, _, _, _, .eq _ => rfl
  | _, _, _, s, r, _, .app f a => by simp [rename, subst, subst_rename s r f, subst_rename s r a]
  | _, _, _, s, r, _, .lam b => by
    simp [rename, subst, subst_rename (Sub.lift s) (Ren.lift r) b, Sub.lift_compRen]

theorem _root_.Classicism.Meta.Ren.lift_compSub {Γ Δ Θ : Ctx} (r : Ren Δ Θ) (s : Sub Sig Γ Δ) {σ : Ty} :
    Sub.lift (Ren.compSub r s) (σ := σ) = Ren.compSub (Ren.lift r) (Sub.lift s) := by
  funext τ v
  cases v with
  | zero => rfl
  | succ v =>
    show ((s _ v).rename r).weaken = ((s _ v).weaken).rename (Ren.lift r)
    simp only [weaken, rename_rename]
    rfl

theorem rename_subst : ∀ {Γ Δ Θ : Ctx} (r : Ren Δ Θ) (s : Sub Sig Γ Δ) {σ : Ty} (a : Term Sig Γ σ),
    (a.subst s).rename r = a.subst (Ren.compSub r s)
  | _, _, _, _, _, _, .var _ | _, _, _, _, _, _, .const _ | _, _, _, _, _, _, .and
  | _, _, _, _, _, _, .or | _, _, _, _, _, _, .not | _, _, _, _, _, _, .all _
  | _, _, _, _, _, _, .ex _ | _, _, _, _, _, _, .eq _ => rfl
  | _, _, _, r, s, _, .app f a => by simp [rename, subst, rename_subst r s f, rename_subst r s a]
  | _, _, _, r, s, _, .lam b => by
    simp [rename, subst, rename_subst (Ren.lift r) (Sub.lift s) b, Ren.lift_compSub]

theorem _root_.Classicism.Meta.Sub.lift_comp {Γ Δ Θ : Ctx} (s : Sub Sig Δ Θ) (s' : Sub Sig Γ Δ) {σ : Ty} :
    Sub.lift (Sub.comp s s') (σ := σ) = Sub.comp (Sub.lift s) (Sub.lift s') := by
  funext τ v
  cases v with
  | zero => rfl
  | succ v =>
    show ((s' _ v).subst s).weaken = ((s' _ v).weaken).subst (Sub.lift s)
    simp only [weaken, rename_subst, subst_rename]
    rfl

theorem subst_subst : ∀ {Γ Δ Θ : Ctx} (s : Sub Sig Δ Θ) (s' : Sub Sig Γ Δ) {σ : Ty} (a : Term Sig Γ σ),
    (a.subst s').subst s = a.subst (Sub.comp s s')
  | _, _, _, _, _, _, .var _ | _, _, _, _, _, _, .const _ | _, _, _, _, _, _, .and
  | _, _, _, _, _, _, .or | _, _, _, _, _, _, .not | _, _, _, _, _, _, .all _
  | _, _, _, _, _, _, .ex _ | _, _, _, _, _, _, .eq _ => rfl
  | _, _, _, s, s', _, .app f a => by simp [subst, subst_subst s s' f, subst_subst s s' a]
  | _, _, _, s, s', _, .lam b => by
    simp [subst, subst_subst (Sub.lift s) (Sub.lift s') b, Sub.lift_comp]

/-- Substituting under a `cons` into a weakened term drops the `cons`. -/
@[simp] theorem _root_.Classicism.Meta.Sub.compRen_cons_shift {Γ Δ : Ctx} {σ : Ty}
    (a : Term Sig Δ σ) (s : Sub Sig Γ Δ) :
    Sub.compRen (Sub.cons a s) (Ren.shift (σ := σ)) = s := by
  funext τ v; rfl

/-- Substituting into a weakened term, for the innermost variable, does nothing. -/
theorem instantiate_weaken {Γ : Ctx} {σ τ : Ty} (a : Term Sig Γ τ) (b : Term Sig Γ σ) :
    (a.weaken (τ := σ)).instantiate b = a := by
  rw [instantiate, weaken, subst_rename, Sub.compRen_cons_shift]
  exact subst_id a

end Term

end Classicism.Meta
