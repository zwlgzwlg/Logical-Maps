import Classicism.Meta.Quote
import Classicism.Meta.Normalize

/-!
# Translation of strict proofs into derivations

The second half of the translator. `#classicism_derive foo` reads the strict proof of
`foo` and declares

    foo.derivable : ∀ σ' …, Theorem C.axioms(Minus) (foo.quoted σ' …)

a derivation, in the metalogical layer's system, of the sentence the quoter made of
`foo`'s statement, with the theorem's type parameters as object-type variables. The
kernel checks it. So, for each theorem it reaches, the chain is complete: a shallow proof
in Lean, the transformer's strict proof from the eleven axioms, and a derivation in `H`
plus the eleven identities as an object of Lean, each link kernel-checked and each
translator untrusted.

## What a strict proof is made of

Almost entirely Leibniz's Law. A survey of the strict layer's proof terms found `Eq`,
`congrArg`, `Eq.trans`, `Eq.symm`, `Eq.mpr`, `congrFun` and `Eq.rec` in the thousands,
the eleven axioms entering mostly through the fields of the Boolean-algebra instances,
and the natural-deduction constructors, `Or.elim`, `And.intro`, `Exists.elim` and the
rest, a handful of times. So the translation is chiefly equational: each Lean identity
lemma is `LL` at a predicate, and `Classicism/Meta/Derivation.lean` has the derived rule
for each, `eqCongr`, `eqTrans`, `eqMpr` and so on.

## The three things the translation has to supply

* **Conversion.** Lean's kernel applies β silently; `congrArg f h` has the type
  `f a = f b` with `f a` a redex, and what uses it expects the reduct. The object language
  has a `conv` rule, so wherever the formula a derivation proves and the formula its use
  expects differ, `coerce` bridges them. The proof is one reflective lemma, `Conv.of_nf`,
  whose hypothesis the kernel discharges by evaluating the verified normalizer of
  `Classicism/Meta/Normalize.lean` on both sides. η is reduced at the source by both
  quoters, so it does not arise.
* **Citations.** A library theorem used in the proof is translated at the types it is
  used at, once per distinct instantiation, and declared as `c.derivable_n`; its citation
  is that declaration, weakened into the current context by `Derivable.ofTheorem`. This
  sidesteps the class-parametric statement of, say, `BA.rule_imp_intro`, which in the
  object language is a different sentence at each type.
* **Unfolding.** Fields of the class instances, `BA.comm_and instBAProp`, are unfolded to
  what they are, an axiom or a congruence; `BA.and` and the like in statements are quoted
  through their instances.

## How it is built

Everything is constructed directly as expressions with every implicit argument supplied,
never through unification, since the formulas involved are large and the derivations
contain thousands of nodes. The option `Classicism.Meta.Translate.check` type-checks every
node as it is built, for debugging; the kernel checks the whole in any case.
-/

open Lean Meta Elab Term Command Classicism.Meta.Quote

namespace Classicism.Meta.Translate

register_option Classicism.Meta.Translate.check : Bool := {
  defValue := false
  descr := "type-check every node the translator builds (slow; for debugging)"
}

register_option Classicism.Meta.Translate.convAxiom : Bool := {
  defValue := false
  descr := "for measurement only: replace every conversion proof by `sorryAx`, to see what the conversions cost the kernel"
}

register_option Classicism.Meta.Translate.profile : Bool := {
  defValue := false
  descr := "print the time the translator spent in each phase"
}

register_option Classicism.Meta.Translate.progress : String := {
  defValue := ""
  descr := "a file to which `#classicism_derive_audit` appends a line per theorem as it \
    goes; Lean captures what elaboration prints, so a long run cannot be watched otherwise"
}

/-- An untyped object term. A logical constant is read by name with its type index, a
relational operation by name with its type and its arguments, so that the context, which
every constructor of the typed syntax carries, plays no part in the comparison. -/
inductive Tm where
  | var (i : Nat)
  | app (f a : Tm)
  | lam (b : Tm)
  | const (n : Name) (ty : Expr)
  | rel (n : Name) (ρ : Expr) (args : List Tm)
  | opaque (e : Expr)
  deriving BEq, Inhabited, Repr

namespace Tm

/-- Shift the free variables at or above `c` by `d`. -/
partial def shift (d : Nat) (c : Nat) : Tm → Tm
  | var i => if i ≥ c then var (i + d) else var i
  | app f a => app (shift d c f) (shift d c a)
  | lam b => lam (shift d (c + 1) b)
  | rel n ρ args => rel n ρ (args.map (shift d c))
  | t => t

/-- Substitute `s` for the variable `j`, lowering those above it. -/
partial def subst (j : Nat) (s : Tm) : Tm → Tm
  | var i => if i == j then s else if i > j then var (i - 1) else var i
  | app f a => app (subst j s f) (subst j s a)
  | lam b => lam (subst (j + 1) (shift 1 0 s) b)
  | rel n ρ args => rel n ρ (args.map (subst j s))
  | t => t

/-- Does the variable `j` occur free? -/
partial def occurs (j : Nat) : Tm → Bool
  | var i => i == j
  | app f a => occurs j f || occurs j a
  | lam b => occurs (j + 1) b
  | rel _ _ args => args.any (occurs j)
  | _ => false

/-- Lower the free variables above `j` by one, `j` itself not occurring. -/
partial def lower (j : Nat) : Tm → Tm
  | var i => if i > j then var (i - 1) else var i
  | app f a => app (lower j f) (lower j a)
  | lam b => lam (lower (j + 1) b)
  | rel n ρ args => rel n ρ (args.map (lower j))
  | t => t

/-- η-reduce at the root, as `Term.etaRed` does. -/
def etaRed : Tm → Tm
  | lam (app g (var 0)) => if occurs 0 g then lam (app g (var 0)) else lower 0 g
  | t => t

/-- One pass, exactly as `Term.step` computes it: parallel β, with η at each abstraction.
Relational operations at a type variable are stuck for the kernel, so they are stuck here. -/
partial def step : Tm → Tm
  | app f a =>
    match step f with
    | lam b => subst 0 (step a) b
    | f' => app f' (step a)
  | lam b => etaRed (lam (step b))
  | t => t

/-- The normal form, and the number of passes of `step` that reach it: the fuel to give
`Term.nf` so that the kernel does no more work than needed. -/
partial def normalize (t : Tm) (fuel : Nat := 0) : Option (Tm × Nat) :=
  -- typed terms normalize, but a shadow is untyped; a runaway is cut off rather than
  -- allowed to eat the machine
  if fuel > 500 then none else
  let t' := step t
  if t' == t then some (t, fuel) else normalize t' (fuel + 1)

end Tm

/-- One hypothesis in scope: its Lean variable, its object formula as quoted when it was
introduced, and how many object variables were then in scope. -/
structure Hyp where
  fvar : FVarId
  formula : Expr
  depth : Nat
  deriving Inhabited

structure TCtx where
  q : QCtx := {}
  hyps : List Hyp := []
  /-- The axiom set, `C.axioms` or `C.axiomsMinus`. -/
  ax : Expr
  axIsC : Bool
  /-- The object context as a `List Ty`, cached; rebuilt at each binder. -/
  ctxCache : Expr := mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Classicism.Meta.Ty)
  /-- The hypotheses as a `List (Formula Sig Γ)`, cached; rebuilt at each binder. -/
  hypsCache : Expr := mkApp (mkConst ``List.nil [Level.zero])
    (mkApp2 (mkConst ``Classicism.Meta.Formula) (mkConst ``Classicism.Meta.Signature.pure)
      (mkApp (mkConst ``List.nil [Level.zero]) (mkConst ``Classicism.Meta.Ty)))

structure TState where
  /-- Specializations in progress, to catch a theorem citing itself. -/
  specs : Std.HashSet String := {}
  /-- Milliseconds spent, by phase, for the profile the command prints. -/
  timing : Std.HashMap String Nat := {}
  /-- Quotations already made, by object context and Lean expression. -/
  quotes : Std.HashMap (Expr × Expr) (Expr × Expr) := {}
  /-- Normalized shadows already computed, with the passes they took. -/
  nfs : Std.HashMap Expr (Tm × Nat) := {}
  /-- Shadows already read, by expression. -/
  shadows : Std.HashMap Expr Tm := {}
  /-- Phases being timed, so that a recursive phase is not counted once per level. -/
  activePhases : Std.HashSet String := {}

abbrev TrM := ReaderT TCtx (StateRefT TState TermElabM)

/-- Time an action, under a phase name; an action already inside its phase is not timed
again. -/
def timed {α} (phase : String) (k : TrM α) : TrM α := do
  if (← get).activePhases.contains phase then k else
  modify fun s => { s with activePhases := s.activePhases.insert phase }
  let t₀ ← IO.monoMsNow
  try k finally
    let t₁ ← IO.monoMsNow
    modify fun s => { s with
      timing := s.timing.insert phase (s.timing.getD phase 0 + (t₁ - t₀))
      activePhases := s.activePhases.erase phase }

/-! ### Expressions of the object syntax -/

def sigE : Expr := mkConst ``Classicism.Meta.Signature.pure
def tyE : Expr := mkConst ``Classicism.Meta.Ty
def rtE : Expr := mkConst ``Classicism.Meta.RTy.t
def tRel (ρ : Expr) : Expr := mkApp (mkConst ``Classicism.Meta.Ty.rel) ρ
def tyT : Expr := tRel rtE
def tArr (σ ρ : Expr) : Expr := mkApp2 (mkConst ``Classicism.Meta.RTy.arr) σ ρ

/-- Split an object type `Ty.rel (σ ⇒ ρ)`. -/
partial def splitArrow (T : Expr) : TrM (Expr × Expr) := do
  let T ← instantiateMVars T
  if let some ρ := T.app1? ``Classicism.Meta.Ty.rel then
    if let some (σ, ρ') := ρ.app2? ``Classicism.Meta.RTy.arr then return (σ, ρ')
  let T' ← whnf T
  if T' != T then splitArrow T' else
  throwError "derive: {T} is not an arrow type"

/-- The relational type of an object type `Ty.rel ρ`. -/
partial def relOf (T : Expr) : TrM Expr := do
  let T ← instantiateMVars T
  if let some ρ := T.app1? ``Classicism.Meta.Ty.rel then return ρ
  let T' ← whnf T
  if T' != T then relOf T' else throwError "derive: {T} is not a relational type"

def mkTApp (Γ σ ρ f a : Expr) : Expr := mkAppN (mkConst ``Classicism.Meta.Term.app) #[sigE, Γ, σ, ρ, f, a]
def mkTLam (Γ σ ρ b : Expr) : Expr := mkAppN (mkConst ``Classicism.Meta.Term.lam) #[sigE, Γ, σ, ρ, b]
def mkTVar (Γ σ v : Expr) : Expr := mkAppN (mkConst ``Classicism.Meta.Term.var) #[sigE, Γ, σ, v]
/-- An abbreviation of `Classicism/Meta/Term.lean`, `conj p q` and the like, in context. -/
def mkAbbr (n : Name) (Γ : Expr) (args : Array Expr) : Expr := mkAppN (mkConst n) (#[sigE, Γ] ++ args)
/-- A relational operation of `Classicism/Meta/Relational.lean`, `andR ρ X Y`. -/
def mkRel (n : Name) (ρ Γ : Expr) (args : Array Expr) : Expr := mkAppN (mkConst n) (#[sigE, ρ, Γ] ++ args)

/-- The object context from the `i`-th innermost variable outward, as a `List Ty`. -/
def ctxFrom (i : Nat) : TrM Expr := do
  let vars := (← read).q.objVars.drop i
  let mut acc := mkApp (mkConst ``List.nil [Level.zero]) tyE
  for (_, σ) in vars.reverse do
    acc := mkAppN (mkConst ``List.cons [Level.zero]) #[tyE, σ, acc]
  return acc

/-- The object context, innermost first, as a `List Ty`. -/
def ctxE : TrM Expr := return (← read).ctxCache

def depth : TrM Nat := return (← read).q.objVars.length

/-- The variable at de Bruijn index `i`, of type `σ`. -/
def varE (i : Nat) (σ : Expr) : TrM Expr := do
  let vars := (← read).q.objVars.toArray
  let mut v := mkAppN (mkConst ``Classicism.Meta.Var.zero) #[← ctxFrom (i + 1), σ]
  for j in [0:i] do
    let j := i - 1 - j
    v := mkAppN (mkConst ``Classicism.Meta.Var.succ) #[← ctxFrom (j + 1), σ, vars[j]!.2, v]
  return v

/-- `a.weaken` at the new variable's type `τ`, in the context `Γ` of `a`. -/
def weakenE (Γ τ σ a : Expr) : Expr :=
  mkAppN (mkConst ``Classicism.Meta.Term.weaken) #[sigE, Γ, τ, σ, a]

/-- The body of a quoted abstraction `Term.lam Sig Γ σ ρ b`, if it is one. -/
def lamBody? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``Classicism.Meta.Term.lam 5 then some e.appArg! else none

/-- `b.instantiate a`. -/
def instE (Γ σ τ b a : Expr) : Expr :=
  mkAppN (mkConst ``Classicism.Meta.Term.instantiate) #[sigE, Γ, σ, τ, b, a]

/-- `a.close` into the context `Γ`. -/
def closeE (Γ σ a : Expr) : Expr :=
  mkAppN (mkConst ``Classicism.Meta.Term.close) #[sigE, Γ, σ, a]

/-- A hypothesis' formula in the current context: weakened once per object variable
introduced since it. -/
def hypFormula (h : Hyp) : TrM Expr := do
  let mut f := h.formula
  let vars := (← read).q.objVars.reverse
  for k in [h.depth:vars.length] do
    let Γ ← ctxFrom (vars.length - k)
    f := weakenE Γ vars[k]!.2 tyT f
  return f

/-- The hypotheses as a `List (Formula Sig Γ)`, computed afresh. -/
def hypsList : TrM Expr := do
  let Γ ← ctxFrom 0
  let fty := mkApp2 (mkConst ``Classicism.Meta.Formula) sigE Γ
  let mut acc := mkApp (mkConst ``List.nil [Level.zero]) fty
  for h in (← read).hyps.reverse do
    acc := mkAppN (mkConst ``List.cons [Level.zero]) #[fty, ← hypFormula h, acc]
  return acc

/-- The hypotheses as a `List (Formula Sig Γ)`. -/
def hypsE : TrM Expr := return (← read).hypsCache

/-- Run with the caches rebuilt for the current variables and hypotheses. -/
def withCaches {α} (k : TrM α) : TrM α := do
  let Γ ← ctxFrom 0
  let Δ ← withReader (fun c => { c with ctxCache := Γ }) hypsList
  withReader (fun c => { c with ctxCache := Γ, hypsCache := Δ }) k

/-- Enter an object variable. -/
def withObj {α} (nm : Name) (ty : Expr) (k : Expr → TrM α) : TrM α := do
  let σ ← (quoteTy ty).run (← read).q
  withLocalDeclD nm ty fun x =>
    withReader (fun c => { c with q := { c.q with objVars := (x.fvarId!, σ) :: c.q.objVars } })
      (withCaches (k x))

/-- Enter a hypothesis. -/
def withHyp {α} (nm : Name) (ty : Expr) (formula : Expr) (k : Expr → TrM α) : TrM α := do
  let d ← depth
  withLocalDeclD nm ty fun h =>
    withReader (fun c => { c with hyps := ⟨h.fvarId!, formula, d⟩ :: c.hyps }) (withCaches (k h))

/-! ### The direct quoter

The same reading as `Classicism/Meta/Quote.lean`, built as an expression with every
implicit argument supplied instead of as syntax to elaborate, which is what makes it fast
enough to run on every subterm of a proof. Returns the term and its object type. -/

partial def quoteE (e : Expr) : TrM (Expr × Expr) := timed "quote" do
  let e ← instantiateMVars e
  let Γ ← ctxE
  let key := (Γ, e)
  if let some r := (← get).quotes[key]? then return r
  checkSystem "derive"
  let r ← go Γ e
  modify fun s => { s with quotes := s.quotes.insert key r }
  return r
where
  q (e : Expr) : TrM (Expr × Expr) := quoteE e
  ty (e : Expr) : TrM Expr := timed "quote.ty" do (quoteTy e).run (← read).q
  rty (e : Expr) : TrM Expr := timed "quote.ty" do (quoteRTy e).run (← read).q
  formula (Γ : Expr) (n : Name) (args : Array Expr) : TrM (Expr × Expr) :=
    return (mkAbbr n Γ args, tyT)
  go (Γ : Expr) (e : Expr) : TrM (Expr × Expr) := do
    match e with
    | .mdata _ b => q b
    | .letE _ _ v b _ => q (b.instantiate1 v)
    | .fvar id =>
      let some i := (← read).q.objVars.findIdx? (·.1 == id)
        | throwError "derive: the variable {e} is not an object variable in scope"
      let σ := (← read).q.objVars[i]!.2
      return (mkTVar Γ σ (← varE i σ), σ)
    | .lam nm d b _ =>
      -- quoted faithfully, with no η-reduction and no β-reduction of redexes: the
      -- derivation's formulas then agree with the quotations of Lean's types
      -- syntactically wherever Lean's kernel did not convert, and a conversion proof is
      -- needed only where it did
      let σ ← ty d
      withObj nm d fun x => do
        let (b', bT) ← q (b.instantiate1 x)
        let ρ ← relOf bT
        return (mkTLam Γ σ ρ b', tRel (tArr σ ρ))
    | .forallE nm d b _ =>
      if ← timed "quote.isProp" (isProp d) then
        if b.hasLooseBVars then throwError "derive: a formula depends on a proof: {e}"
        let (d', _) ← q d
        if b.isConstOf ``False then formula Γ ``Classicism.Meta.Term.neg #[d']
        else formula Γ ``Classicism.Meta.Term.imp #[d', (← q b).1]
      else
        let σ ← ty d
        withObj nm d fun x => do
          let (b', _) ← q (b.instantiate1 x)
          return (mkAppN (mkConst ``Classicism.Meta.Term.forall') #[sigE, Γ, σ, b'], tyT)
    | _ =>
      match e.getAppFnArgs with
      | (``And, #[a, b]) => formula Γ ``Classicism.Meta.Term.conj #[(← q a).1, (← q b).1]
      | (``Or, #[a, b]) => formula Γ ``Classicism.Meta.Term.disj #[(← q a).1, (← q b).1]
      | (``Not, #[a]) => formula Γ ``Classicism.Meta.Term.neg #[(← q a).1]
      | (``Classicism.imp, #[a, b]) => formula Γ ``Classicism.Meta.Term.imp #[(← q a).1, (← q b).1]
      | (``Classicism.iff, #[a, b]) => formula Γ ``Classicism.Meta.Term.iff #[(← q a).1, (← q b).1]
      | (``Classicism.Strict.Top, #[]) | (``True, #[]) => formula Γ ``Classicism.Meta.Term.top #[]
      | (``Classicism.Strict.Bot, #[]) | (``False, #[]) => formula Γ ``Classicism.Meta.Term.bot #[]
      | (``Classicism.Strict.everything, #[]) =>
        let v0 := mkTVar (mkAppN (mkConst ``List.cons [Level.zero]) #[tyE, tyT, Γ]) tyT
          (mkAppN (mkConst ``Classicism.Meta.Var.zero) #[Γ, tyT])
        return (mkAppN (mkConst ``Classicism.Meta.Term.forall') #[sigE, Γ, tyT, v0], tyT)
      | (``Classicism.Strict.Box, #[a]) => formula Γ ``Classicism.Meta.Term.box #[(← q a).1]
      | (``Classicism.Strict.Dia, #[a]) => formula Γ ``Classicism.Meta.Term.dia #[(← q a).1]
      | (``Eq, #[α, a, b]) =>
        let σ ← ty α
        return (mkAppN (mkConst ``Classicism.Meta.Term.eq') #[sigE, Γ, σ, (← q a).1, (← q b).1], tyT)
      | (``Exists, #[α, F]) =>
        let σ ← ty α
        match F with
        | .lam nm d b _ =>
          withObj nm d fun x => do
            let (b', _) ← q (b.instantiate1 x)
            return (mkAppN (mkConst ``Classicism.Meta.Term.exists') #[sigE, Γ, σ, b'], tyT)
        | _ =>
          let ex := mkAppN (mkConst ``Classicism.Meta.Term.ex) #[sigE, Γ, σ]
          return (mkTApp Γ (tRel (tArr σ rtE)) rtE ex (← q F).1, tyT)
      | (``Classicism.Strict.SRel.constP, #[τ, _, p]) =>
        let ρ ← rty τ; return (mkRel ``Classicism.Meta.Term.constR ρ Γ #[(← q p).1], tRel ρ)
      | (``Classicism.Strict.SRel.neg, #[τ, _, X]) =>
        let ρ ← rty τ; return (mkRel ``Classicism.Meta.Term.negR ρ Γ #[(← q X).1], tRel ρ)
      | (``Classicism.Strict.SRel.and, #[τ, _, X, Y]) =>
        let ρ ← rty τ; return (mkRel ``Classicism.Meta.Term.andR ρ Γ #[(← q X).1, (← q Y).1], tRel ρ)
      | (``Classicism.Strict.SRel.or, #[τ, _, X, Y]) =>
        let ρ ← rty τ; return (mkRel ``Classicism.Meta.Term.orR ρ Γ #[(← q X).1, (← q Y).1], tRel ρ)
      | (``Classicism.Strict.SRel.coext, #[τ, _, X, Y]) =>
        let ρ ← rty τ; return (mkRel ``Classicism.Meta.Term.coextR ρ Γ #[(← q X).1, (← q Y).1], tyT)
      | (``Classicism.Strict.SRel.boxAt, #[τ, _, X]) =>
        let ρ ← rty τ; return (mkRel ``Classicism.Meta.Term.boxR ρ Γ #[(← q X).1], tRel ρ)
      | (``Classicism.Strict.SRel.boxImp, #[τ, _, X, Y]) =>
        let ρ ← rty τ; return (mkRel ``Classicism.Meta.Term.boxImpR ρ Γ #[(← q X).1, (← q Y).1], tyT)
      | (``Eq, args) =>
        -- `Eq α`, `Eq α a`: identity unapplied or partially applied, as η-reduction of
        -- `fun z => a = z` leaves it
        let σ ← ty args[0]!
        let mut acc := mkAppN (mkConst ``Classicism.Meta.Term.eq) #[sigE, Γ, σ]
        let mut T := tRel (tArr σ (tArr σ rtE))
        for a in args.extract 1 args.size do
          let (σ', ρ) ← splitArrow T
          acc := mkTApp Γ σ' ρ acc (← q a).1
          T := tRel ρ
        return (acc, T)
      | (``Exists, #[α]) =>
        let σ ← ty α
        return (mkAppN (mkConst ``Classicism.Meta.Term.ex) #[sigE, Γ, σ], tRel (tArr (tRel (tArr σ rtE)) rtE))
      | (``And, args) | (``Or, args) | (``Not, args) =>
        -- a connective unapplied or partially applied, as the instance fields at `Prop`
        -- leave it: the constant, then the applications
        let c := e.getAppFn.constName!
        let base := if c == ``And then ``Classicism.Meta.Term.and
          else if c == ``Or then ``Classicism.Meta.Term.or else ``Classicism.Meta.Term.not
        let mut acc := mkAppN (mkConst base) #[sigE, Γ]
        let mut T := if c == ``Not then tRel (tArr tyT rtE) else tRel (tArr tyT (tArr tyT rtE))
        for a in args do
          let (σ, ρ) ← splitArrow T
          acc := mkTApp Γ σ ρ acc (← q a).1
          T := tRel ρ
        return (acc, T)
      | _ =>
        let f := e.getAppFn
        let args := e.getAppArgs
        if f.isFVar then
          let mut (acc, T) ← q f
          for a in args do
            let (σ, ρ) ← splitArrow T
            let (a', _) ← q a
            acc := mkTApp Γ σ ρ acc a'
            T := tRel ρ
          return (acc, T)
        if f.isLambda then
          -- a redex is quoted as a redex
          let mut (acc, T) ← q f
          for a in args do
            let (σ, ρ) ← splitArrow T
            let (a', _) ← q a
            acc := mkTApp Γ σ ρ acc a'
            T := tRel ρ
          return (acc, T)
        match ← timed "quote.unfold" (unfoldDefinition? e) with
        | some e' => q e'
        | none =>
          let e' ← timed "quote.unfold" (whnfCore e)
          if e' != e then q e'
          else
            let e'' ← timed "quote.unfold" (whnfR e)
            if e'' != e then q e''
            else throwError "derive: cannot read {e} as an object term"

/-- Quote a Lean proposition as a formula in the current context. -/
def quoteF (e : Expr) : TrM Expr := return (← quoteE e).1

/-- Quote a Lean object as a term in the current context. -/
def quoteT (e : Expr) : TrM Expr := return (← quoteE e).1

/-! ### Rules, built directly -/

/-- A rule of `Derivable`, with every argument given: the parameters `Sig` and `Ax`, then
the constructor's own in order. -/
def rule (n : Name) (args : Array Expr) : TrM Expr := timed "rule" do
  let r := mkAppN (mkConst n) (#[sigE, (← read).ax] ++ args)
  if Classicism.Meta.Translate.check.get (← getOptions) then
    try Meta.check r catch ex =>
      throwError "derive: internal error building {n}:\n{ex.toMessageData}"
  return r

/-! ### Conversion

For the check that two formulas convert, before the kernel is asked to, the translator
keeps an **untyped shadow** of the object syntax, `Tm`, into which object-term expressions
are read with `whnf` at each node, and in which β- and η-normalization is a few lines.
Two formulas whose shadows normalize alike are then joined by `Conv.of_nf`, and the
kernel's evaluation of the verified normalizer is the real check. -/


/-- Normalize a type expression for comparison: unfold abbreviations such as `Ty.t` at
every level. -/
partial def normTy (e : Expr) : MetaM Expr := do
  let e ← whnf (← instantiateMVars e)
  match e.getAppFnArgs with
  | (``Classicism.Meta.Ty.rel, #[ρ]) => return mkApp (mkConst ``Classicism.Meta.Ty.rel) (← normTy ρ)
  | (``Classicism.Meta.RTy.arr, #[σ, ρ]) =>
    return mkApp2 (mkConst ``Classicism.Meta.RTy.arr) (← normTy σ) (← normTy ρ)
  | _ => return e

/-- Read an object-term expression as a shadow term. Anything that is not a constructor
of the syntax after `whnf`, such as a relational operation at a type variable, is opaque. -/
partial def shadow (t : Expr) : TrM Tm := do
  let t ← instantiateMVars t
  if let some r := (← get).shadows[t]? then return r
  let r ← go t
  modify fun s => { s with shadows := s.shadows.insert t r }
  return r
where
  go (t : Expr) : TrM Tm := do
    -- a substitution is done on the shadow, not by evaluating the syntax's
    match t.getAppFn.constName?, t.getAppArgs with
    | some ``Classicism.Meta.Term.instantiate, #[_, _, _, _, b, a] =>
      return Tm.subst 0 (← shadow a) (← shadow b)
    | some ``Classicism.Meta.Term.weaken, #[_, _, _, _, a] => return Tm.shift 1 0 (← shadow a)
    | some ``Classicism.Meta.Term.close, #[_, _, _, a] => shadow a
    | _, _ =>
    let t ← whnf t
    match t.getAppFn.constName?, t.getAppArgs with
    | some ``Classicism.Meta.Term.app, #[_, _, _, _, f, a] => return .app (← shadow f) (← shadow a)
    | some ``Classicism.Meta.Term.lam, #[_, _, _, _, b] => return .lam (← shadow b)
    | some ``Classicism.Meta.Term.var, #[_, _, _, v] => return .var (← varIndex v)
    | some ``Classicism.Meta.Term.and, _ => return .const ``Classicism.Meta.Term.and tyT
    | some ``Classicism.Meta.Term.or, _ => return .const ``Classicism.Meta.Term.or tyT
    | some ``Classicism.Meta.Term.not, _ => return .const ``Classicism.Meta.Term.not tyT
    | some ``Classicism.Meta.Term.all, #[_, _, σ] => return .const ``Classicism.Meta.Term.all (← normTy σ)
    | some ``Classicism.Meta.Term.ex, #[_, _, σ] => return .const ``Classicism.Meta.Term.ex (← normTy σ)
    | some ``Classicism.Meta.Term.eq, #[_, _, σ] => return .const ``Classicism.Meta.Term.eq (← normTy σ)
    | some ``Classicism.Meta.Term.const, #[_, _, c] => return .const ``Classicism.Meta.Term.const (← instantiateMVars c)
    | some n, args =>
      if n == ``Classicism.Meta.Term.constR || n == ``Classicism.Meta.Term.negR
          || n == ``Classicism.Meta.Term.andR || n == ``Classicism.Meta.Term.orR
          || n == ``Classicism.Meta.Term.coextR || n == ``Classicism.Meta.Term.boxR
          || n == ``Classicism.Meta.Term.boxImpR then
        -- `op ρ Γ X …`: the type, then the operands
        let ρ ← normTy args[1]!
        let ops ← (args.extract 3 args.size).mapM shadow
        return .rel n ρ ops.toList
      return .opaque (← instantiateMVars t)
    | _, _ => return .opaque (← instantiateMVars t)
  varIndex (v : Expr) : TrM Nat := do
    let v ← whnf v
    match v.getAppFn.constName?, v.getAppArgs with
    | some ``Classicism.Meta.Var.zero, _ => pure 0
    | some ``Classicism.Meta.Var.succ, args => return (← varIndex args.back!) + 1
    | _, _ => throwError "derive: not a variable: {v}"

/-- The normalized shadow of an object term and the passes it took, memoized. -/
def shadowNf (t : Expr) : TrM (Tm × Nat) := timed "nf" do
  let t ← instantiateMVars t
  if let some r := (← get).nfs[t]? then return r
  let sh ← timed "nf.shadow" (shadow t)
  -- the bind keeps the normalization inside the timer (Lean evaluates eagerly)
  let some r ← timed "nf.normalize" (do let _ ← pure (); return sh.normalize)
    | throwError "derive: the shadow of{indentExpr t}\ndid not normalize in 500 passes"
  modify fun s => { s with nfs := s.nfs.insert t r }
  return r

/-- Use a derivation of `got` as one of `exp`: directly if they are the same, else through
`conv` with `Conv.of_nf`, after checking that their shadows normalize alike. -/
def coerce (d got exp : Expr) : TrM Expr := do
  let got ← instantiateMVars got
  let exp ← instantiateMVars exp
  if got == exp then return d
  let (g', kg) ← shadowNf got
  let (e', ke) ← shadowNf exp
  unless g' == e' do
    throwError "derive: the derivation proves{indentExpr got}\nbut{indentExpr exp}\nwas expected, and the two do not convert; normal forms {repr g'} and {repr e'}"
  if kg == 0 && ke == 0 then
    -- equal after unfolding abbreviations and evaluating substitutions: definitionally
    -- equal, so the derivation is used as it is and the kernel evaluates
    modify fun s => { s with timing := s.timing.insert "defeq" (s.timing.getD "defeq" 0 + 1) }
    return d
  let Γ ← ctxE
  let termTy := mkApp3 (mkConst ``Classicism.Meta.Term) sigE Γ tyT
  let nfOf (n : Nat) (t : Expr) : Expr :=
    mkAppN (mkConst ``Classicism.Meta.Term.nf) #[sigE, Γ, tyT, mkRawNatLit n, t]
  let refl (t : Expr) : Expr := mkAppN (mkConst ``Eq.refl [Level.one]) #[termTy, t]
  -- evaluate on one side where the other is already normal
  let c ← if Classicism.Meta.Translate.convAxiom.get (← getOptions) then
      pure (mkApp2 (mkConst ``sorryAx [Level.zero]) (mkAppN (mkConst ``Classicism.Meta.Conv) #[sigE, Γ, tyT, got, exp]) (mkConst ``Bool.false))
    else if ke == 0 then
      pure (mkAppN (mkConst ``Classicism.Meta.Conv.of_nf_left) #[sigE, Γ, tyT, mkRawNatLit kg, got, exp, refl exp])
    else if kg == 0 then
      pure (mkAppN (mkConst ``Classicism.Meta.Conv.of_nf_right) #[sigE, Γ, tyT, mkRawNatLit ke, got, exp, refl got])
    else
      let n := max kg ke
      pure (mkAppN (mkConst ``Classicism.Meta.Conv.of_nf) #[sigE, Γ, tyT, mkRawNatLit n, got, exp, refl (nfOf n got)])
  let kind := s!"conv[{max kg ke} passes; got={got.getAppFn.constName?.getD `_}; exp={exp.getAppFn.constName?.getD `_}]"
  modify fun s => { s with timing := s.timing.insert kind (s.timing.getD kind 0 + 1) }
  rule ``Classicism.Meta.Derivable.conv #[Γ, ← hypsE, got, exp, d, c]

/-! ### The interpretation -/

/-- The membership proof for the hypothesis at index `i`: `tail` past the hypotheses in
front of it, then `head`. -/
def memProof (i : Nat) : TrM Expr := do
  let Γ ← ctxE
  let fty := mkApp2 (mkConst ``Classicism.Meta.Formula) sigE Γ
  let formulas ← (← read).hyps.mapM hypFormula
  let target := formulas[i]!
  let listE (fs : List Expr) : Expr := Id.run do
    let mut acc := mkApp (mkConst ``List.nil [Level.zero]) fty
    for g in fs.reverse do acc := mkAppN (mkConst ``List.cons [Level.zero]) #[fty, g, acc]
    return acc
  let rec go (j : Nat) (fs : List Expr) : TrM Expr := do
    match fs with
    | [] => throwError "derive: internal error in memProof"
    | f :: rest =>
      if j == i then return mkAppN (mkConst ``List.Mem.head [Level.zero]) #[fty, target, listE rest]
      else return mkAppN (mkConst ``List.Mem.tail [Level.zero]) #[fty, target, f, listE rest, ← go (j + 1) rest]
  go 0 formulas

/-- Is the argument a type or an instance? -/
def isParam (a : Expr) : MetaM Bool := do
  let t ← whnf (← inferType a)
  if let .sort l := t then return !l.isZero
  return (← isClass? t).isSome

/-- A proof of `Ax a` for an axiom of `C⁻`, in the current axiom set. -/
def axiomProof (ctor : Name) (tyArgs : Array Expr) : TrM Expr := do
  let h := mkAppN (mkConst (`Classicism.Meta.C.axiomsMinus ++ ctor)) (#[sigE] ++ tyArgs)
  if (← read).axIsC then
    let a := mkAppN (mkConst (`Classicism.Meta.C ++ ctor)) (#[sigE] ++ tyArgs)
    return mkAppN (mkConst ``Classicism.Meta.C.axioms.minus) #[sigE, a, h]
  else return h

/-- `Term.imp A B` and friends, as expressions in context. -/
def impE (Γ A B : Expr) : Expr := mkAbbr ``Classicism.Meta.Term.imp Γ #[A, B]
def negE (Γ A : Expr) : Expr := mkAbbr ``Classicism.Meta.Term.neg Γ #[A]
def conjE (Γ A B : Expr) : Expr := mkAbbr ``Classicism.Meta.Term.conj Γ #[A, B]
def disjE (Γ A B : Expr) : Expr := mkAbbr ``Classicism.Meta.Term.disj Γ #[A, B]
def iffE (Γ A B : Expr) : Expr := mkAbbr ``Classicism.Meta.Term.iff Γ #[A, B]
def botE (Γ : Expr) : Expr := mkAbbr ``Classicism.Meta.Term.bot Γ #[]
def eqE (Γ σ a b : Expr) : Expr := mkAppN (mkConst ``Classicism.Meta.Term.eq') #[sigE, Γ, σ, a, b]

mutual

/-- The derivation of a strict proof term `t : A`: the formula it proves, and the proof of
`Derivable Ax Δ` of it. -/
partial def interp (t : Expr) : TrM (Expr × Expr) := do
  let t := (← instantiateMVars t).consumeMData
  checkSystem "derive"
  match t with
  | .letE _ _ v b _ => interp (b.instantiate1 v)
  | .mdata _ b => interp b
  | .fvar id =>
    let hs := (← read).hyps
    let some i := hs.findIdx? (·.fvar == id)
      | throwError "derive: {t} is not a hypothesis in scope"
    let f ← hypFormula hs[i]!
    let d ← rule ``Classicism.Meta.Derivable.hyp #[← ctxE, ← hypsE, f, ← memProof i]
    return (f, d)
  | .lam nm d b _ =>
    if ← isProp d then
      let H ← quoteF d
      let Γ ← ctxE
      let Δ ← hypsE
      withHyp nm d H fun h => do
        let body := b.instantiate1 h
        let (B, db) ← interp body
        let bodyTy ← whnfR (← inferType body)
        if bodyTy.isConstOf ``False then
          let db ← coerce db B (botE Γ)
          let everything := mkAbbr ``Classicism.Meta.Term.forall' Γ #[tyT,
            mkTVar (mkAppN (mkConst ``List.cons [Level.zero]) #[tyE, tyT, Γ]) tyT
              (mkAppN (mkConst ``Classicism.Meta.Var.zero) #[Γ, tyT])]
          let Δ' := mkAppN (mkConst ``List.cons [Level.zero]) #[mkApp2 (mkConst ``Classicism.Meta.Formula) sigE Γ, H, Δ]
          let h₁ ← rule ``Classicism.Meta.Derivable.andE₁ #[Γ, Δ', everything, negE Γ everything, db]
          let h₂ ← rule ``Classicism.Meta.Derivable.andE₂ #[Γ, Δ', everything, negE Γ everything, db]
          let d ← rule ``Classicism.Meta.Derivable.notI #[Γ, Δ, H, everything, h₁, h₂]
          return (negE Γ H, d)
        let d ← rule ``Classicism.Meta.Derivable.impI #[Γ, Δ, H, B, db]
        return (impE Γ H B, d)
    else
      if ← isParam' d then
        throwError "derive: a proof abstracts over a type or an instance inside a formula"
      let Γ ← ctxE
      let Δ ← hypsE
      let σ ← (quoteTy d).run (← read).q
      withObj nm d fun x => do
        let (B, db) ← interp (b.instantiate1 x)
        let F := mkAbbr ``Classicism.Meta.Term.forall' Γ #[σ, B]
        let d ← rule ``Classicism.Meta.Derivable.allI #[Γ, Δ, σ, B, db]
        return (F, d)
  | .proj S i e =>
    let ty ← whnf (← inferType e)
    match S, i, ty.getAppFnArgs with
    | ``And, 0, (_, #[a, b]) => interp (mkApp3 (mkConst ``And.left) a b e)
    | ``And, 1, (_, #[a, b]) => interp (mkApp3 (mkConst ``And.right) a b e)
    | ``Iff, 0, (_, #[a, b]) => interp (mkApp3 (mkConst ``Iff.mp) a b e)
    | ``Iff, 1, (_, #[a, b]) => interp (mkApp3 (mkConst ``Iff.mpr) a b e)
    | _, _, _ =>
      -- a field of a class instance: reduce the projection of the constructor
      let t' ← whnfCore t
      if t' != t then interp t'
      else
        let t'' ← whnfR t
        if t'' != t then interp t''
        else throwError "derive: projection {t} is not handled"
  | .app .. | .const .. => interpApp t.getAppFn t.getAppArgs
  | _ => throwError "derive: proof term of an unexpected form: {t}"

partial def isParam' (d : Expr) : TrM Bool := do
  let d ← whnf d
  if let .sort l := d then return !l.isZero
  return (← isClass? d).isSome

/-- A derivation of a branch `f : A → C` of a case analysis, as `(A :: Δ) ⊢ C`. -/
partial def branch (f : Expr) (A : Expr) (AF CF : Expr) : TrM Expr := do
  match f with
  | .lam nm _ b _ =>
    withHyp nm A AF fun h => do
      let (got, d) ← interp (b.instantiate1 h)
      coerce d got CF
  | _ =>
    let (got, d) ← interp f
    let Γ ← ctxE
    let Δ ← hypsE
    let imp := impE Γ AF CF
    let d ← coerce d got imp
    let d' ← rule ``Classicism.Meta.Derivable.weaken₁ #[Γ, Δ, imp, AF, d]
    let h0 ← rule ``Classicism.Meta.Derivable.hyp₀ #[Γ, Δ, AF]
    let Δ' := mkAppN (mkConst ``List.cons [Level.zero]) #[mkApp2 (mkConst ``Classicism.Meta.Formula) sigE Γ, AF, Δ]
    rule ``Classicism.Meta.Derivable.impE #[Γ, Δ', AF, CF, d', h0]

partial def interpApp (f : Expr) (args : Array Expr) : TrM (Expr × Expr) := do
  let t := mkAppN f args
  let Γ ← ctxE
  let Δ ← hypsE
  if let .const c ls := f then
    match c, args with
    | ``id, #[_, a] => return ← interp a
    | ``Eq.refl, #[_, a] | ``rfl, #[_, a] =>
      let (a', σ) ← quoteE a
      return (eqE Γ σ a' a', ← rule ``Classicism.Meta.Derivable.refl #[Γ, Δ, σ, a'])
    | ``Eq.symm, #[_, a, b, h] =>
      let (got, d) ← interp h
      let (a', σ) ← quoteE a; let (b', _) ← quoteE b
      let d ← coerce d got (eqE Γ σ a' b')
      return (eqE Γ σ b' a', ← rule ``Classicism.Meta.Derivable.eqSymm #[Γ, Δ, σ, a', b', d])
    | ``Eq.trans, #[_, a, b, c', h₁, h₂] =>
      let (g₁, d₁) ← interp h₁
      let (g₂, d₂) ← interp h₂
      let (a', σ) ← quoteE a; let (b', _) ← quoteE b; let (c'', _) ← quoteE c'
      let d₁ ← coerce d₁ g₁ (eqE Γ σ a' b')
      let d₂ ← coerce d₂ g₂ (eqE Γ σ b' c'')
      return (eqE Γ σ a' c'', ← rule ``Classicism.Meta.Derivable.eqTrans #[Γ, Δ, σ, a', b', c'', d₁, d₂])
    | ``Trans.trans, _ =>
      if args.size ≥ 12 && args[6]!.isAppOf ``instTransEq then
        return ← interpApp (mkConst ``Eq.trans ls.tail!) (#[args[0]!] ++ args.extract 7 args.size)
      throwError "derive: `Trans.trans` not at an equation"
    | ``congrArg, #[_, _, a₁, a₂, fn, h] =>
      let (got, d) ← interp h
      let (a₁', σ) ← quoteE a₁; let (a₂', _) ← quoteE a₂
      let d ← coerce d got (eqE Γ σ a₁' a₂')
      let (fn', fT) ← quoteE fn
      let (_, ρ) ← splitArrow fT
      if let some B := lamBody? fn' then
        -- a lambda: conclude with the substitution, as Lean's type has it
        let l := instE Γ σ (tRel ρ) B a₁'
        let r := instE Γ σ (tRel ρ) B a₂'
        return (eqE Γ (tRel ρ) l r, ← rule ``Classicism.Meta.Derivable.eqCongrβ #[Γ, Δ, σ, ρ, B, a₁', a₂', d])
      let l := mkTApp Γ σ ρ fn' a₁'
      let r := mkTApp Γ σ ρ fn' a₂'
      return (eqE Γ (tRel ρ) l r, ← rule ``Classicism.Meta.Derivable.eqCongr #[Γ, Δ, σ, ρ, fn', a₁', a₂', d])
    | ``congrFun, #[_, _, f₁, f₂, h, a] =>
      let (got, d) ← interp h
      let (f₁', fT) ← quoteE f₁; let (f₂', _) ← quoteE f₂
      let (σ, ρ) ← splitArrow fT
      let d ← coerce d got (eqE Γ fT f₁' f₂')
      let (a', _) ← quoteE a
      match lamBody? f₁', lamBody? f₂' with
      | some b₁, some b₂ =>
        let l := instE Γ σ (tRel ρ) b₁ a'
        let r := instE Γ σ (tRel ρ) b₂ a'
        return (eqE Γ (tRel ρ) l r, ← rule ``Classicism.Meta.Derivable.eqCongrFunβ #[Γ, Δ, σ, ρ, b₁, b₂, d, a'])
      | _, _ =>
        let l := mkTApp Γ σ ρ f₁' a'
        let r := mkTApp Γ σ ρ f₂' a'
        return (eqE Γ (tRel ρ) l r, ← rule ``Classicism.Meta.Derivable.eqCongrFun #[Γ, Δ, σ, ρ, f₁', f₂', d, a'])
    | ``Eq.mpr, #[α, β, h, p] =>
      let (gh, dh) ← interp h
      let (gp, dp) ← interp p
      let α' ← quoteF α; let β' ← quoteF β
      let dh ← coerce dh gh (eqE Γ tyT α' β')
      let dp ← coerce dp gp β'
      return (α', ← rule ``Classicism.Meta.Derivable.eqMpr #[Γ, Δ, α', β', dh, dp])
    | ``Eq.mp, #[α, β, h, p] =>
      let (gh, dh) ← interp h
      let (gp, dp) ← interp p
      let α' ← quoteF α; let β' ← quoteF β
      let dh ← coerce dh gh (eqE Γ tyT α' β')
      let dp ← coerce dp gp α'
      return (β', ← rule ``Classicism.Meta.Derivable.eqMp #[Γ, Δ, α', β', dh, dp])
    | ``Eq.rec, _ | ``Eq.ndrec, _ =>
      if args.size < 6 then throwError "derive: a partially applied recursor"
      let a := args[1]!; let motive := args[2]!
      let m := args[3]!; let b := args[4]!; let h := args[5]!
      let arity : Nat := if c == ``Eq.rec then 2 else 1
      let P ← forallBoundedTelescope (← inferType motive) (some arity) fun xs _ => do
        let body := (motive.beta xs).headBeta
        if arity == 2 then
          if body.containsFVar xs[1]!.fvarId! then
            throwError "derive: a motive depends on the identity proof"
        mkLambdaFVars #[xs[0]!] body
      let (gh, dh) ← interp h
      let (gm, dm) ← interp m
      let (a', σ) ← quoteE a; let (b', _) ← quoteE b
      let (P', _) ← quoteE P
      let dh ← coerce dh gh (eqE Γ σ a' b')
      let some Pb := lamBody? P'
        | throwError "derive: a motive that is not an abstraction"
      let dm ← coerce dm gm (instE Γ σ tyT Pb a')
      let F := instE Γ σ tyT Pb b'
      let d ← rule ``Classicism.Meta.Derivable.substβ #[Γ, Δ, σ, a', b', Pb, dh, dm]
      return ← feed (mkAppN f (args.extract 0 6)) F d (args.extract 6 args.size)
    | ``And.intro, #[a, b, ha, hb] =>
      let (ga, da) ← interp ha; let (gb, db) ← interp hb
      let a' ← quoteF a; let b' ← quoteF b
      let da ← coerce da ga a'; let db ← coerce db gb b'
      return (conjE Γ a' b', ← rule ``Classicism.Meta.Derivable.andI #[Γ, Δ, a', b', da, db])
    | ``And.left, #[a, b, h] =>
      let (g, d) ← interp h
      let a' ← quoteF a; let b' ← quoteF b
      let d ← coerce d g (conjE Γ a' b')
      return (a', ← rule ``Classicism.Meta.Derivable.andE₁ #[Γ, Δ, a', b', d])
    | ``And.right, #[a, b, h] =>
      let (g, d) ← interp h
      let a' ← quoteF a; let b' ← quoteF b
      let d ← coerce d g (conjE Γ a' b')
      return (b', ← rule ``Classicism.Meta.Derivable.andE₂ #[Γ, Δ, a', b', d])
    | ``Or.inl, #[a, b, h] =>
      let (g, d) ← interp h
      let a' ← quoteF a; let b' ← quoteF b
      let d ← coerce d g a'
      return (disjE Γ a' b', ← rule ``Classicism.Meta.Derivable.orI₁ #[Γ, Δ, a', b', d])
    | ``Or.inr, #[a, b, h] =>
      let (g, d) ← interp h
      let a' ← quoteF a; let b' ← quoteF b
      let d ← coerce d g b'
      return (disjE Γ a' b', ← rule ``Classicism.Meta.Derivable.orI₂ #[Γ, Δ, a', b', d])
    | ``Or.elim, #[a, b, c', h, fn, g] =>
      let (gh, dh) ← interp h
      let a' ← quoteF a; let b' ← quoteF b; let c'' ← quoteF c'
      let dh ← coerce dh gh (disjE Γ a' b')
      let df ← branch fn a a' c''
      let dg ← branch g b b' c''
      return (c'', ← rule ``Classicism.Meta.Derivable.orE #[Γ, Δ, a', b', c'', dh, df, dg])
    | ``absurd, #[a, b, h, nh] =>
      let (gh, dh) ← interp h; let (gn, dn) ← interp nh
      let a' ← quoteF a; let b' ← quoteF b
      let dh ← coerce dh gh a'
      let dn ← coerce dn gn (negE Γ a')
      return (b', ← rule ``Classicism.Meta.Derivable.notE #[Γ, Δ, a', b', dh, dn])
    | ``False.elim, #[C, h] =>
      let (g, d) ← interp h
      let C' ← quoteF C
      let d ← coerce d g (botE Γ)
      return (C', ← rule ``Classicism.Meta.Derivable.botE #[Γ, Δ, C', d])
    | ``Iff.intro, #[a, b, fn, g] =>
      let a' ← quoteF a; let b' ← quoteF b
      let df ← branch fn a a' b'
      let dg ← branch g b b' a'
      return (iffE Γ a' b', ← rule ``Classicism.Meta.Derivable.iffI #[Γ, Δ, a', b', df, dg])
    | ``Iff.mp, #[a, b, h] =>
      let (g, d) ← interp h
      let a' ← quoteF a; let b' ← quoteF b
      let d ← coerce d g (iffE Γ a' b')
      return (impE Γ a' b', ← rule ``Classicism.Meta.Derivable.andE₁ #[Γ, Δ, impE Γ a' b', impE Γ b' a', d])
    | ``Iff.mpr, #[a, b, h] =>
      let (g, d) ← interp h
      let a' ← quoteF a; let b' ← quoteF b
      let d ← coerce d g (iffE Γ a' b')
      return (impE Γ b' a', ← rule ``Classicism.Meta.Derivable.andE₂ #[Γ, Δ, impE Γ a' b', impE Γ b' a', d])
    | ``Exists.intro, #[α, p, w, h] =>
      let (g, d) ← interp h
      let (p', _) ← quoteE p; let (w', σ) ← quoteE w
      let _ := α
      let ex := mkAppN (mkConst ``Classicism.Meta.Term.ex) #[sigE, Γ, σ]
      let F := mkTApp Γ (tRel (tArr σ rtE)) rtE ex p'
      if let some pb := lamBody? p' then
        let d ← coerce d g (instE Γ σ tyT pb w')
        return (F, ← rule ``Classicism.Meta.Derivable.exIβ #[Γ, Δ, σ, pb, w', d])
      let d ← coerce d g (mkTApp Γ σ rtE p' w')
      return (F, ← rule ``Classicism.Meta.Derivable.exI #[Γ, Δ, σ, p', w', d])
    | ``Exists.elim, #[α, p, b, h, fn] =>
      let (gh, dh) ← interp h
      let (p', _) ← quoteE p
      let σ ← (quoteTy α).run (← read).q
      let ex := mkAppN (mkConst ``Classicism.Meta.Term.ex) #[sigE, Γ, σ]
      let exF := mkTApp Γ (tRel (tArr σ rtE)) rtE ex p'
      let dh ← coerce dh gh exF
      let b' ← quoteF b
      let .lam wn wt wb _ := fn | throwError "derive: `Exists.elim` with a branch that is not a lambda"
      let d' ← withObj wn wt fun w => do
        let inner := wb.instantiate1 w
        let .lam hn ht hb _ := inner | throwError "derive: `Exists.elim` with a branch that is not a lambda"
        let Γ' ← ctxE
        -- the hypothesis is `p w`, as the rule states it: `F.weaken` applied to the variable
        let pw := weakenE Γ σ (tRel (tArr σ rtE)) p'
        let v0 := mkTVar Γ' σ (mkAppN (mkConst ``Classicism.Meta.Var.zero) #[Γ, σ])
        let hf := mkTApp Γ' σ rtE pw v0
        withHyp hn ht hf fun hh => do
          let (g, d) ← interp (hb.instantiate1 hh)
          coerce d g (weakenE Γ σ tyT b')
      return (b', ← rule ``Classicism.Meta.Derivable.exE #[Γ, Δ, σ, p', b', dh, d'])
    | ``Classicism.e_exists, #[] =>
      unless (← read).axIsC do throwError "derive: `e_exists` used, but the theorem was to be derived in C⁻"
      let a := mkApp (mkConst ``Classicism.Meta.C.existence_e) sigE
      let pf := mkApp (mkConst ``Classicism.Meta.C.axioms.existence_e) sigE
      let d ← rule ``Classicism.Meta.Derivable.ax #[Γ, Δ, a, pf]
      let F ← quoteF (← inferType t)
      return (F, ← coerce d (closeE Γ tyT a) F)
    | _, _ =>
      if (`Classicism.Axiomatic).isPrefixOf c then
        let short := c.components.getLast!
        let tyArgs ← (args.filterM fun a => do return (← whnf (← inferType a)).isSort)
        let qc := (← read).q
        let tyArgs' ← tyArgs.mapM fun a => (quoteTy a).run qc
        let a := mkAppN (mkConst (`Classicism.Meta.C ++ short)) (#[sigE] ++ tyArgs')
        let pf ← axiomProof short tyArgs'
        let d ← rule ``Classicism.Meta.Derivable.ax #[Γ, Δ, a, pf]
        let F ← quoteF (← inferType t)
        return (F, ← coerce d (closeE Γ tyT a) F)
      if (`Classicism).isPrefixOf c then
        if let some (.thmInfo _) := (← getEnv).find? c then
          let mut k := 0
          for a in args do
            if ← isParam a then k := k + 1 else break
          let params := args.extract 0 k
          let name ← ensureSpecialized c ls params
          let stmt ← inferType (mkAppN f params)
          let S ← quoteF stmt
          let S₀ ← closedQuote stmt
          let tvs := (← read).q.tyVars.reverse.toArray.map (·.2.2)
          let thm := mkAppN (mkConst name) tvs
          let d ← rule ``Classicism.Meta.Derivable.ofTheorem #[Γ, Δ, S₀, thm]
          let d ← coerce d (closeE Γ tyT S₀) S
          return ← feed (mkAppN f params) S d (args.extract k args.size)
      if ← isMatcher c then
        let info ← getConstInfo c
        return ← interp (((info.value! (allowOpaque := true)).instantiateLevelParams info.levelParams ls).beta args).headBeta
      if let some t' ← unfoldDefinition? t then return ← interp t'
      let t' ← whnfCore t
      if t' != t then return ← interp t'
      let t'' ← whnfR t
      if t'' != t then return ← interp t''
      throwError "derive: no rule for the constant {c}"
  let (F, d) ← interp f
  feed f F d args

/-- The sentence for a closed statement, in the empty context. -/
partial def closedQuote (stmt : Expr) : TrM Expr := do
  withReader (fun c => { c with q := { c.q with objVars := [] }, hyps := [] }) (withCaches (quoteF stmt))

/-- Apply a derived function to its remaining arguments: modus ponens for a proof, `UI`
for a term. -/
partial def feed (cur : Expr) (F d : Expr) (args : Array Expr) : TrM (Expr × Expr) := do
  let mut cur := cur
  let mut F := F
  let mut d := d
  for a in args do
    let Γ ← ctxE
    let Δ ← hypsE
    let .forallE nm dom body _ ← whnf (← inferType cur)
      | throwError "derive: {cur} is applied to {a} but is not a function"
    if ← isProp dom then
      if body.hasLooseBVars then throwError "derive: a formula depends on a proof"
      let (ga, da) ← interp a
      let A ← quoteF dom
      let da ← coerce da ga A
      if (← whnfR body).isConstOf ``False then
        d ← coerce d F (negE Γ A)
        d ← rule ``Classicism.Meta.Derivable.notE #[Γ, Δ, A, botE Γ, da, d]
        F := botE Γ
      else
        let B ← quoteF body
        d ← coerce d F (impE Γ A B)
        d ← rule ``Classicism.Meta.Derivable.impE #[Γ, Δ, A, B, d, da]
        F := B
    else
      if ← isParam' dom then throwError "derive: a type argument after the leading parameters"
      let σ ← (quoteTy dom).run (← read).q
      let (bodyF, _) ← quoteE (.lam nm dom body .default)
      let some B := lamBody? bodyF
        | throwError "derive: internal error, a quantifier body that is not an abstraction"
      let allF := mkAbbr ``Classicism.Meta.Term.forall' Γ #[σ, B]
      d ← coerce d F allF
      let (a', _) ← quoteE a
      d ← rule ``Classicism.Meta.Derivable.allEβ #[Γ, Δ, σ, B, d, a']
      F := instE Γ σ tyT B a'
    cur := mkApp cur a
  return (F, d)

/-- The specialization of the library theorem `c` at the parameters `params`, declared
on first use as `c.derivable_n`, abstracted over the object-type variables in scope. -/
partial def ensureSpecialized (c : Name) (ls : List Level) (params : Array Expr) : TrM Name := do
  let tyFvars := (← read).q.tyVars.reverse.toArray.map (fun (id, _, _) => mkFVar id)
  let key ← mkLambdaFVars tyFvars (mkAppN (mkConst c ls) params)
  let keyS := s!"{(← read).axIsC}|{key}"
  -- the name is determined by the instantiation, so a specialization declared earlier,
  -- by this run or an earlier command, is found in the environment and reused
  let name := c ++ Name.mkSimple s!"derivable_{hash keyS}"
  if (← getEnv).contains name then return name
  if (← get).specs.contains keyS then
    throwError "derive: {c} depends on itself at these types"
  let info ← getConstInfo c
  let .thmInfo _ := info | throwError "derive: {c} is not a theorem"
  if Classicism.Meta.Translate.profile.get (← getOptions) then
    IO.eprintln s!"  specializing {c} ({(← get).specs.size} in progress)"
  let body := (((info.value! (allowOpaque := true)).instantiateLevelParams info.levelParams ls).beta params).headBeta
  let stmt ← instantiateForall info.type params
  modify fun s => { s with specs := s.specs.insert keyS }
  let tvs := (← read).q.tyVars.reverse.toArray.map (·.2.2)
  let (ty, val) ← withReader (fun c => { c with q := { c.q with objVars := [] }, hyps := [] }) <| withCaches do
    let S ← quoteF stmt
    let (got, d) ← interp body
    let d ← coerce d got S
    let thmTy := mkAppN (mkConst ``Classicism.Meta.Theorem) #[sigE, (← read).ax, S]
    return (← mkForallFVars tvs thmTy, ← mkLambdaFVars tvs d)
  timed "addDecl" (withOptions (Elab.async.set · false) do
    addDecl (.thmDecl { name := name, levelParams := [], type := ty, value := val }))
  let size := val.approxDepth.toNat
  let st ← get
  let timing := st.timing.insert "specializations" (st.timing.getD "specializations" 0 + 1)
  let timing := timing.insert "maxDepth" (max (timing.getD "maxDepth" 0) size)
  set { st with timing := timing }
  return name

end

/-! ### The command -/

/-- Derive `foo`: declare `foo.derivable`. -/
def derive (foo : Name) : TermElabM Unit := do
  let info ← getConstInfo foo
  let .thmInfo _ := info | throwError "derive: {foo} is not a theorem"
  let axs ← collectAxioms foo
  let axIsC := axs.contains ``Classicism.e_exists
  let ax := mkApp (mkConst (if axIsC then ``Classicism.Meta.C.axioms else ``Classicism.Meta.C.axiomsMinus)) sigE
  forallTelescope info.type fun xs body => do
    let mut k := 0
    let mut kinds : Array (Expr × Kind) := #[]
    for x in xs do
      let t ← whnf (← inferType x)
      if t.isSort && !t.isProp then kinds := kinds.push (x, .ty); k := k + 1
      else if let some cls := (← isClass? t) then
        let σ := t.getAppArgs[0]!
        if cls != ``Classicism.Ty then
          if let some idx := kinds.findIdx? (·.1 == σ) then kinds := kinds.set! idx (σ, .rty)
        k := k + 1
      else break
    let stmt ← mkForallFVars (xs.extract k xs.size) body
    let value := ((info.value! (allowOpaque := true)).beta (xs.extract 0 k)).headBeta
    let rec go (i : Nat) (ctx : QCtx) (tvs : Array Expr) : TermElabM Unit := do
      if h : i < kinds.size then
        let (σ, kind) := kinds[i]
        let tyOfKind := if kind == .ty then tyE else mkConst ``Classicism.Meta.RTy
        withLocalDeclD ((← σ.fvarId!.getUserName).appendAfter "'") tyOfKind fun tv =>
          go (i + 1) { ctx with tyVars := (σ.fvarId!, kind, tv) :: ctx.tyVars } (tvs.push tv)
      else
        let tctx : TCtx := { q := ctx, ax := ax, axIsC := axIsC }
        let ((S, d), st) ← (do
          let S ← quoteF stmt
          let (got, d) ← interp value
          let d ← coerce d got S
          return (S, d)).run tctx |>.run {}
        if Classicism.Meta.Translate.profile.get (← getOptions) then
          logInfo m!"profile (ms): {st.timing.toList}"
        let thmTy := mkAppN (mkConst ``Classicism.Meta.Theorem) #[sigE, ax, S]
        let ty ← mkForallFVars tvs thmTy
        let val ← mkLambdaFVars tvs d
        withOptions (Elab.async.set · false) do
          addDecl (.thmDecl { name := foo ++ `derivable, levelParams := [], type := ty, value := val })
    go 0 {} #[]

syntax (name := classicismDerive) "#classicism_derive " ident+ : command

@[command_elab classicismDerive] def elabDerive : CommandElab := fun stx => do
  for id in stx[1].getArgs do
    let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
    try
      withScope (fun sc => { sc with opts := maxHeartbeats.set sc.opts 0 }) (liftTermElabM (derive n))
      let ty := (← getConstInfo (n ++ `derivable)).type
      let inC := ty.find? (·.isConstOf ``Classicism.Meta.C.axioms) |>.isSome
      logInfo m!"{n} ⟶ {n ++ `derivable} : {ty}\nderived ✓ in {if inC then "C" else "C⁻"}"
    catch ex =>
      logError m!"{n}: not derived — {ex.toMessageData}"

/-- `#classicism_derive_audit Mod …` derives every theorem of the modules whose name ends
in `strict`, and reports. -/
syntax (name := classicismDeriveAudit) "#classicism_derive_audit " ident+ : command

@[command_elab classicismDeriveAudit] def elabDeriveAudit : CommandElab := fun stx => do
  for modId in stx[1].getArgs do
    let env ← getEnv
    let some idx := env.getModuleIdx? modId.getId
      | logError m!"no module {modId.getId}"; continue
    let mut names : Array Name := #[]
    for (n, ci) in env.constants.toList do
      if env.getModuleIdxFor? n == some idx then
        if let .thmInfo _ := ci then
          if n.components.getLast? == some `strict then names := names.push n
    names := names.qsort (fun a b => a.toString < b.toString)
    let mut ok : Nat := 0
    let mut failures : Array MessageData := #[]
    let mut i := 0
    let mut times : Array String := #[]
    -- a line per theorem, with the time it took, appended to the progress file as it
    -- happens; the heartbeat limit is the file's, so that a runaway fails rather than
    -- running on
    let progressFile := Classicism.Meta.Translate.progress.get (← getOptions)
    let report (line : String) : CommandElabM Unit := do
      unless progressFile == "" do
        IO.FS.withFile progressFile .append fun h => h.putStrLn line
    for n in names do
      i := i + 1
      let t₀ ← IO.monoMsNow
      let line ← try
          liftTermElabM (derive n)
          ok := ok + 1
          pure s!"[{i}/{names.size}] {n} ✓ {(← IO.monoMsNow) - t₀} ms"
        catch ex =>
          failures := failures.push m!"{n}: {ex.toMessageData}"
          pure s!"[{i}/{names.size}] {n} ✗ {(← IO.monoMsNow) - t₀} ms"
      times := times.push line
      report line
    logInfo m!"{modId.getId}: {ok} of {names.size} strict theorems derived\n\
{MessageData.joinSep failures.toList "\n"}\n{"\n".intercalate times.toList}"

end Classicism.Meta.Translate
