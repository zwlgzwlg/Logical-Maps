import Lean
import Classicism.Meta.Denotation
import Classicism.Strict

/-!
# Quotation of statements

The first half of the translator from the strict layer into the metalogical one: `⌜·⌝`,
reading a strict **statement**, a Lean proposition, as a sentence of the object language.
`#classicism_quote foo` declares two things for a theorem `foo : p`:

* `foo.quoted : Ty → … → Sentence Signature.pure`, the sentence, with each of `foo`'s type
  parameters made an object-type variable; and
* `foo.reflect : ∀ σ …, Sentence.holds (Interp.ofDomain e) (foo.quoted σ …) = p[σ := ⟦σ⟧]`,
  proved by `rfl`, in the interpretation whose domain is the Lean type `e` itself, since
  the statement may mention it.

The second is the check. The quoter is a meta-program and not trusted; if it produced the
wrong sentence, or an ill-typed one, the reflection equation would fail to elaborate or
the kernel would reject `rfl`. So a quoted sentence that passes reads back as exactly the
strict statement, with the type variables read as any object types.

## What is quoted

The vocabulary of strict statements: `Prop`, `e`, arrows, local variables, `∧`, `∨`, `¬`,
`∀`, `∃`, `=`, the paper's `imp`, `iff`, `Top`, `Bot`, `Box`, `Dia`, `everything`, and
λ-abstraction and application. Any other constant of this library is unfolded and the
result quoted; so a definition such as `P.Functionality.strict` quotes through its body.
A class operation at a *concrete* type unfolds through its instance; at a type variable it
does not, and that is the one thing reported as unquotable for now, the class mirrors'
object-language counterparts being the next piece of work.

Type parameters guarded by `Ty` or `RelTy` become variables of type `Ty` or `RTy`; those
guarded by `SRel` or `SOrder` wait on that same piece.
-/

open Lean Meta Elab Term Command

namespace Classicism.Meta.Quote

/-- How a Lean type parameter is read: as an object type, or as a relational one. -/
inductive Kind
  | ty
  | rty
  deriving BEq, Inhabited

/-- The reading of the local context: Lean type parameters to object-type variables, and
Lean object variables, innermost first, to their object types. -/
structure QCtx where
  tyVars : List (FVarId × Kind × Expr) := []
  objVars : List (FVarId × Expr) := []

abbrev QM := ReaderT QCtx TermElabM

private def tyE : Expr := mkConst ``Classicism.Meta.Ty
private def rtyE : Expr := mkConst ``Classicism.Meta.RTy
private def relE (ρ : Expr) : Expr := mkApp (mkConst ``Classicism.Meta.Ty.rel) ρ
private def tE : Expr := relE (mkConst ``Classicism.Meta.RTy.t)

mutual

/-- Read a Lean type as an object type. -/
partial def quoteTy (e : Expr) : QM Expr := do
  let e ← instantiateMVars e
  match e with
  | .sort .zero => return tE
  | .const ``Classicism.e _ => return mkConst ``Classicism.Meta.Ty.e
  | .fvar id =>
    match (← read).tyVars.find? (·.1 == id) with
    | some (_, .ty, x) => return x
    | some (_, .rty, x) => return relE x
    | none => throwError "quote: the type variable {e} is not a parameter of the statement"
  | .forallE _ d b _ =>
    if b.hasLooseBVars then throwError "quote: a dependent type {e} is not a type of R"
    return relE (mkApp2 (mkConst ``Classicism.Meta.RTy.arr) (← quoteTy d) (← quoteRTy b))
  | .mdata _ b => quoteTy b
  | _ =>
    let e' ← whnfR e
    if e' != e then quoteTy e' else throwError "quote: {e} is not a type of R"

/-- Read a Lean type as a relational type. -/
partial def quoteRTy (e : Expr) : QM Expr := do
  let e ← instantiateMVars e
  match e with
  | .sort .zero => return mkConst ``Classicism.Meta.RTy.t
  | .fvar id =>
    match (← read).tyVars.find? (·.1 == id) with
    | some (_, .rty, x) => return x
    | _ => throwError "quote: {e} is not known to be a relational type"
  | .forallE _ d b _ =>
    if b.hasLooseBVars then throwError "quote: a dependent type {e} is not a type of R"
    return mkApp2 (mkConst ``Classicism.Meta.RTy.arr) (← quoteTy d) (← quoteRTy b)
  | .mdata _ b => quoteRTy b
  | _ =>
    let e' ← whnfR e
    if e' != e then quoteRTy e' else throwError "quote: {e} is not a relational type"

end

/-- The syntax of a de Bruijn index. -/
private def varStx : Nat → TermElabM (TSyntax `term)
  | 0 => `(Classicism.Meta.Var.zero)
  | n + 1 => do `(Classicism.Meta.Var.succ $(← varStx n))

/-- Enter a binder over an object variable. -/
private def withObj {α} (nm : Name) (ty : Expr) (k : Expr → QM α) : QM α := do
  let σ ← quoteTy ty
  withLocalDeclD nm ty fun x =>
    withReader (fun c => { c with objVars := (x.fvarId!, σ) :: c.objVars }) (k x)

/-- Read a strict statement, or a subterm of one, as the syntax of an object term. -/
partial def quoteTerm (e : Expr) : QM (TSyntax `term) := do
  let e ← instantiateMVars e
  match e with
  | .mdata _ b => quoteTerm b
  | .letE _ _ v b _ => quoteTerm (b.instantiate1 v)
  | .fvar id =>
    let some i := (← read).objVars.findIdx? (·.1 == id)
      | throwError "quote: the variable {e} is not an object variable in scope"
    `(Classicism.Meta.Term.var $(← varStx i))
  | .lam nm d b _ =>
    withObj nm d fun x => do
      let b' ← quoteTerm (b.instantiate1 x)
      `(Classicism.Meta.Term.lam $b')
  | .forallE nm d b _ =>
    if ← isProp d then
      if b.hasLooseBVars then throwError "quote: a formula depends on a proof: {e}"
      let d' ← quoteTerm d
      if b.isConstOf ``False then `(Classicism.Meta.Term.neg $d')
      else `(Classicism.Meta.Term.imp $d' $(← quoteTerm b))
    else
      let σ ← quoteTy d
      let σs ← exprToSyntax σ
      withObj nm d fun x => do
        let b' ← quoteTerm (b.instantiate1 x)
        `(Classicism.Meta.Term.forall' (σ := $σs) $b')
  | _ =>
    match e.getAppFnArgs with
    | (``And, #[a, b]) => do `(Classicism.Meta.Term.conj $(← quoteTerm a) $(← quoteTerm b))
    | (``Or, #[a, b]) => do `(Classicism.Meta.Term.disj $(← quoteTerm a) $(← quoteTerm b))
    | (``Not, #[a]) => do `(Classicism.Meta.Term.neg $(← quoteTerm a))
    | (``Classicism.imp, #[a, b]) => do `(Classicism.Meta.Term.imp $(← quoteTerm a) $(← quoteTerm b))
    | (``Classicism.iff, #[a, b]) => do `(Classicism.Meta.Term.iff $(← quoteTerm a) $(← quoteTerm b))
    | (``Classicism.Strict.Top, #[]) => `(Classicism.Meta.Term.top)
    | (``Classicism.Strict.Bot, #[]) => `(Classicism.Meta.Term.bot)
    | (``True, #[]) => `(Classicism.Meta.Term.top)
    | (``False, #[]) => `(Classicism.Meta.Term.bot)
    | (``Classicism.Strict.everything, #[]) =>
      `(Classicism.Meta.Term.forall' (σ := Classicism.Meta.Ty.t) Classicism.Meta.Term.v0)
    | (``Classicism.Strict.Box, #[a]) => do `(Classicism.Meta.Term.box $(← quoteTerm a))
    | (``Classicism.Strict.Dia, #[a]) => do `(Classicism.Meta.Term.dia $(← quoteTerm a))
    | (``Eq, #[α, a, b]) => do
      let σs ← exprToSyntax (← quoteTy α)
      `(Classicism.Meta.Term.eq' (σ := $σs) $(← quoteTerm a) $(← quoteTerm b))
    | (``Exists, #[α, .lam nm d b _]) => do
      let _ := α
      let σs ← exprToSyntax (← quoteTy d)
      withObj nm d fun x => do
        let b' ← quoteTerm (b.instantiate1 x)
        `(Classicism.Meta.Term.exists' (σ := $σs) $b')
    | (``Exists, #[α, F]) => do
      -- `∃ F` with `F` not a lambda: `∃σ F`
      let σs ← exprToSyntax (← quoteTy α)
      `(Classicism.Meta.Term.app (Classicism.Meta.Term.ex $σs) $(← quoteTerm F))
    | _ =>
      let f := e.getAppFn
      let args := e.getAppArgs
      if f.isFVar then
        -- an object variable applied to arguments
        let mut acc ← quoteTerm f
        for a in args do
          acc ← `(Classicism.Meta.Term.app $acc $(← quoteTerm a))
        return acc
      if f.isLambda then
        return ← quoteTerm (e.headBeta)
      -- anything else: unfold one step and try again, so that this library's definitions
      -- and its instances at concrete types quote through their bodies
      match ← unfoldDefinition? e with
      | some e' => quoteTerm e'
      | none =>
        let e' ← whnfCore e
        if e' != e then quoteTerm e'
        else
          -- a projection of an instance at a concrete type reduces under `whnfR`
          let e'' ← whnfR e
          if e'' != e then quoteTerm e''
          else throwError "quote: cannot read {e} as an object term; a class operation \
at a type variable has no object-language counterpart yet"

/-! ### The command -/

/-- The `Ty` marker instance at a type. -/
private def tyMk (σ : Expr) : Expr :=
  mkApp2 (mkConst ``Classicism.Ty.mk) σ (mkConst ``Unit.unit)
private def relTyMk (σ : Expr) : Expr :=
  mkApp2 (mkConst ``Classicism.RelTy.mk) σ (mkConst ``Unit.unit)

/-- Quote the statement `ty`. Returns the quoted sentence as a function of the type
parameters, and the reflection statement and its proof. -/
def quoteStatement (ty : Expr) : TermElabM (Expr × Expr × Expr) := do
  forallTelescope ty fun xs body => do
    -- classify the leading parameters
    let mut k := 0
    let mut kinds : Array (Expr × Kind) := #[]
    let mut insts : Array Expr := #[]
    for x in xs do
      let t ← whnf (← inferType x)
      if t.isSort && !t.isProp then
        kinds := kinds.push (x, .ty); k := k + 1
      else if let some cls := (← isClass? t) then
        let σ := t.getAppArgs[0]!
        if cls == ``Classicism.Ty then pure ()
        else if cls == ``Classicism.RelTy then
          -- a `RelTy` guard on a parameter makes it a relational-type variable
          if let some idx := kinds.findIdx? (·.1 == σ) then kinds := kinds.set! idx (σ, .rty)
        else throwError "quote: a parameter of class {cls} has no object-language reading yet"
        insts := insts.push x; k := k + 1
      else break
    let stmt ← mkForallFVars (xs.extract k xs.size) body
    -- object-type variables, one per type parameter
    let rec go (i : Nat) (ctx : QCtx) (tvs : Array Expr) : TermElabM (Expr × Expr × Expr) := do
      if h : i < kinds.size then
        let (σ, kind) := kinds[i]
        let tyOfKind := if kind == .ty then tyE else rtyE
        withLocalDeclD ((← σ.fvarId!.getUserName).appendAfter "'") tyOfKind fun tv =>
          go (i + 1) { ctx with tyVars := (σ.fvarId!, kind, tv) :: ctx.tyVars } (tvs.push tv)
      else
        let stx ← (quoteTerm stmt).run ctx
        let sentenceTy := mkApp (mkConst ``Classicism.Meta.Sentence) (mkConst ``Classicism.Meta.Signature.pure)
        let sentence ← elabTermEnsuringType stx (some sentenceTy)
        synthesizeSyntheticMVarsNoPostponing
        let sentence ← instantiateMVars sentence
        if sentence.hasMVar then throwError "quote: the sentence has unresolved holes:{indentExpr sentence}"
        let quoted ← mkLambdaFVars tvs sentence
        -- the reflection statement: `e` reads as the Lean type `e`, since the statement
        -- mentions it, and the type variables read as `⟦σ'⟧` over that domain
        let D : Expr := Expr.const ``Classicism.e []
        do
          let I := mkApp (mkConst ``Classicism.Meta.Interp.ofDomain) D
          let lhs := mkApp3 (mkConst ``Classicism.Meta.Sentence.holds)
            (mkConst ``Classicism.Meta.Signature.pure) I (mkAppN quoted tvs)
          -- instantiate the original statement's parameters, one binder at a time: a type
          -- parameter by the reading of its object-type variable, an instance by the marker
          let mut rhs := ty
          let mut ti := 0
          for _ in [0:k] do
            let .forallE _ d b _ := rhs | throwError "quote: internal error in the telescope"
            let d ← whnf d
            let arg ← if d.isSort then
                let (_, kind) := kinds[ti]!
                let tv := tvs[ti]!
                ti := ti + 1
                pure (if kind == .ty then mkApp2 (mkConst ``Classicism.Meta.Ty.denote) D tv
                  else mkApp2 (mkConst ``Classicism.Meta.RTy.denote) D tv)
              else
                let cls := d.getAppFn.constName!
                let subject := d.getAppArgs[0]!
                pure (if cls == ``Classicism.Ty then tyMk subject else relTyMk subject)
            rhs := b.instantiate1 arg
          let eq ← mkEq lhs rhs
          let reflectTy ← mkForallFVars tvs eq
          let reflectVal ← mkLambdaFVars tvs (← mkEqRefl lhs)
          return (quoted, reflectTy, reflectVal)
    go 0 {} #[]

/-- Declare `n.quoted` and `n.reflect` from the results of `quoteStatement`. -/
def declareQuoted (n : Name) (quoted reflectTy reflectVal : Expr) : TermElabM Unit := do
  let quotedTy ← inferType quoted
  let dv : DefinitionVal := { name := n ++ `quoted, levelParams := [], type := quotedTy, value := quoted, hints := .abbrev, safety := .safe }
  let tv : TheoremVal := { name := n ++ `reflect, levelParams := [], type := reflectTy, value := reflectVal }
  withOptions (Elab.async.set · false) do
    addDecl (.defnDecl dv)
    addDecl (.thmDecl tv)

/-- `#classicism_quote foo …` quotes the statement of each theorem, declaring `foo.quoted`
and the reflection theorem `foo.reflect`, checked by `rfl`. -/
syntax (name := classicismQuote) "#classicism_quote " ident+ : command

@[command_elab classicismQuote] def elabQuote : CommandElab := fun stx => do
  for id in stx[1].getArgs do
    let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
    let info ← getConstInfo n
    try
      let (quoted, reflectTy, reflectVal) ← liftTermElabM (quoteStatement info.type)
      liftTermElabM (declareQuoted n quoted reflectTy reflectVal)
      logInfo m!"{n} ⟶ {n ++ `quoted}:{indentExpr (← getConstInfo (n ++ `quoted)).value!}\nreflects ✓"
    catch ex =>
      logError m!"{n}: not quoted — {ex.toMessageData}"

/-- `#classicism_quote_audit Mod …` quotes every theorem of the modules whose name ends in
`strict`, and reports. -/
syntax (name := classicismQuoteAudit) "#classicism_quote_audit " ident+ : command

@[command_elab classicismQuoteAudit] def elabQuoteAudit : CommandElab := fun stx => do
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
    for n in names do
      let info ← getConstInfo n
      try
        let (quoted, reflectTy, reflectVal) ← liftTermElabM (quoteStatement info.type)
        liftTermElabM (declareQuoted n quoted reflectTy reflectVal)
        ok := ok + 1
      catch ex =>
        failures := failures.push m!"{n}: {ex.toMessageData}"
    logInfo m!"{modId.getId}: {ok} of {names.size} strict statements quoted and reflected\n\
{MessageData.joinSep failures.toList "\n"}"

end Classicism.Meta.Quote
