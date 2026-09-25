import Classicism.Tools.Translate
import Classicism.Syntax.Entailment

/-!
# Principles as schemas, and the map's arrows as entailments

The map's principles are the shallow layer's `Prop`-valued definitions with type
parameters, `Classicism.P.Barcan σ` and the rest. This module reads each into the object
language as a **schema**, an axiom set of instances over its object-type parameters, and
reads each record theorem `P … → Q …` together with its kernel-checked derivation into an
**entailment** between schemas, `P.schema ⟹ Q.schema`, the form of the map's arrows.

- `#classicism_schema P …` quotes the principle `P` (its statement being `∀ params, P params`,
  by the quoter of `Quote.lean`), declaring `P.quoted`, the reflection theorem `P.reflect`,
  and `P.schema : AxiomSet Signature.pure`, the sentences `P.quoted σ' …` for all
  object types `σ' …`.
- `#classicism_entails_audit Mod …` does that for every record theorem of a module, deriving
  first where no derivation exists, and reports.
- `#classicism_entails foo …` reads the statement of `foo`, of the form
  `P₁ … → … → Pₙ … → Q …`, and its derivation `foo.derivable` (from
  `#classicism_derive`), and declares `foo.entails : P₁.schema ∪ … ∪ Pₙ.schema ⟹ Q.schema`.
  For each instance of `Q` it specializes the derivation to the object types that make
  its consequent that instance (any type for a parameter the consequent does not mention),
  and cites the premises as axioms of their schemas — the instances read off the
  statement, converted by the translator where an operation at a constructor type has
  been unfolded. When the statement fixes the conclusion's types (`Existence e`) the
  conclusion is the singleton; when they are expressions in its parameters
  (`Existence (σ → t)`), the family of those instances.

Both are checked by the kernel like everything else: the schema is a definition, the
entailment a theorem whose proof cites the derivation.
-/

namespace Classicism.Meta

open Lean Elab Command Term Meta Classicism.Meta.Quote

/-! ### Schemas -/

/-- The statement of a principle: `∀ params, P params`, with `P` its strict twin
`P.strict` when the transformer has made one (the twin is in the paper's vocabulary, which
the quoter reads and reflection checks by `rfl`). -/
def principleStatement (n : Name) : MetaM Expr := do
  let info ← getConstInfo n
  forallTelescope info.type fun xs body => do
    unless body.isProp do throwError "{n} is not a principle: its type is not `Prop`"
    mkForallFVars xs (mkAppN (Lean.mkConst n (info.levelParams.map mkLevelParam)) xs)

/-- `∃ rest, a = q rest`, for `q` a quoted schema applied to some of its parameters. -/
partial def schemaBody (q a : Expr) : MetaM Expr := do
  let qty ← whnf (← inferType q)
  if qty.isForall then
    withLocalDeclD qty.bindingName! qty.bindingDomain! fun x => do
      let inner ← schemaBody (mkApp q x) a
      mkAppM ``Exists #[← mkLambdaFVars #[x] inner]
  else
    mkEq a q

/-- From `quoted : ∀ (x₁ : Ty) …, Sentence`, the axiom set `fun a => ∃ x₁ …, a = quoted x₁ …`. -/
def schemaOfQuoted (quoted : Expr) : MetaM Expr := do
  let sentenceTy := mkApp (Lean.mkConst ``Classicism.Meta.Sentence) (Lean.mkConst ``Classicism.Meta.Signature.pure)
  withLocalDeclD `a sentenceTy fun a => do
    mkLambdaFVars #[a] (← schemaBody quoted a)

/-- Declare `n.quoted`, `n.reflect` and `n.schema` for the principle `n`. -/
def declareSchema (n : Name) : TermElabM Unit := do
  let ty ← principleStatement n
  let (quoted, reflectTy, reflectVal) ← quoteStatement ty
  declareQuoted n quoted reflectTy reflectVal
  setReducibilityStatus (n ++ `quoted) .reducible
  let schema ← schemaOfQuoted (Lean.mkConst (n ++ `quoted))
  let schemaTy ← inferType schema
  let dv : DefinitionVal := { name := n ++ `schema, levelParams := [], type := schemaTy, value := schema, hints := .abbrev, safety := .safe }
  withOptions (Elab.async.set · false) do addDecl (.defnDecl dv)
  setReducibilityStatus (n ++ `schema) .reducible

/-- `#classicism_schema P …`: each principle `P` becomes a schema, `P.schema`. -/
syntax (name := classicismSchema) "#classicism_schema " ident+ : command

@[command_elab classicismSchema] def elabSchema : CommandElab := fun stx => do
  for id in stx[1].getArgs do
    let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
    try
      liftTermElabM (declareSchema n)
      logInfo m!"{n} ⟶ {n ++ `schema}:{indentExpr (← getConstInfo (n ++ `quoted)).value!}"
    catch ex =>
      logError m!"{n}: no schema — {ex.toMessageData}"

/-! ### Entailments -/

/-- The principle a strict twin `P.strict` is a twin of. -/
def principleOf (n : Name) : Name :=
  match n with
  | .str p "strict" => p
  | _ => n

/-- The premises and conclusion of a strict statement `imp (P₁ …) (imp … (Q …))`, as
principle names. -/
partial def recordShapeGo (e : Expr) (acc : List Name) : MetaM (List Name × Name) := do
  let e ← instantiateMVars e
  if e.isAppOfArity ``Classicism.imp 2 then
    let d := e.getAppArgs[0]!
    let some dn := d.getAppFn.constName?
      | throwError "entails: a premise is not a principle:{indentExpr d}"
    recordShapeGo e.getAppArgs[1]! (acc ++ [principleOf dn])
  else if e.isArrow then
    let d := e.bindingDomain!
    let some dn := d.getAppFn.constName?
      | throwError "entails: a premise is not a principle:{indentExpr d}"
    recordShapeGo e.bindingBody! (acc ++ [principleOf dn])
  else
    let some hn := e.getAppFn.constName?
      | throwError "entails: the conclusion is not a principle:{indentExpr e}"
    pure (acc, principleOf hn)

/-- Telescope the *parameters* of a statement — its leading type and instance binders —
and hand the rest to `k`. Unlike `forallTelescope`, this stops at the first hypothesis,
so that a record's premises `P … → … → Q …`, arrows in the shallow layer, are left in the
body. -/
partial def paramTelescope {α} (ty : Expr) (k : Array Expr → Expr → TermElabM α) : TermElabM α :=
  go ty #[]
where
  go (e : Expr) (xs : Array Expr) : TermElabM α := do
    match e with
    | .forallE nm d b bi =>
      let d' ← whnf d
      if (d'.isSort && !d'.isProp) || (← isClass? d').isSome then
        withLocalDecl nm bi d fun x => go (b.instantiate1 x) (xs.push x)
      else k xs e
    | _ => k xs e

/-- Read a statement `P₁ … → … → Q …` (under its parameters) into the list of its
premises' principle names and its conclusion's. -/
def recordShape (ty : Expr) : TermElabM (List Name × Name) := do
  paramTelescope ty fun _ body => recordShapeGo body []

/-- The union `P₁.schema ∪ … ∪ Pₙ.schema`, or `AxiomSet.empty`. -/
def premisesSet (ps : List Name) : MetaM Expr := do
  let pureSig := Lean.mkConst ``Classicism.Meta.Signature.pure
  match ps with
  | [] => pure (mkApp (Lean.mkConst ``Classicism.Meta.AxiomSet.empty) pureSig)
  | p :: rest =>
    let mut acc := Lean.mkConst (p ++ `schema)
    for q in rest do
      acc ← mkAppM ``Union.union #[acc, Lean.mkConst (q ++ `schema)]
    return acc

/-- The left-nested union of the schemas `ss` (nonempty). -/
def unionOf (ss : List Expr) : MetaM Expr := do
  match ss with
  | [] => throwError "entails: empty union"
  | S :: rest =>
    let mut acc := S
    for T in rest do
      acc ← mkAppM ``Union.union #[acc, T]
    return acc

/-- A proof that `x` is in the left-nested union of `ss`, at position `i`, given a proof `h`
that it is in `ss[i]`. -/
partial def unionMem (ss : List Expr) (i : Nat) (x h : Expr) : MetaM Expr := do
  if ss.length ≤ 1 then return h
  let prefix_ := ss.dropLast
  let last := ss.getLast!
  let left := mkApp (← unionOf prefix_) x
  let right := mkApp last x
  if i == ss.length - 1 then mkAppOptM ``Or.inr #[left, right, h]
  else mkAppOptM ``Or.inl #[left, right, ← unionMem prefix_ i x h]

/-- `⟨args[i], ⟨args[i+1], … rfl⟩⟩ : ∃ rest, x = q rest`, the equation by `rfl`. -/
partial def schemaMemBuild (x : Expr) (args : Array Expr) (i : Nat) (q : Expr) : MetaM Expr := do
  if h : i < args.size then
    let inner ← schemaMemBuild x args (i + 1) (mkApp q args[i])
    let qty ← whnf (← inferType q)
    let motive ← withLocalDeclD `y qty.bindingDomain! fun y => do
      mkLambdaFVars #[y] (← schemaBody (mkApp q y) x)
    mkAppOptM ``Exists.intro #[none, motive, args[i], inner]
  else
    mkEqRefl x

/-- A proof that `x` is in `P.schema`: `⟨args, rfl⟩`, the arguments found by unification. -/
def schemaMem (P : Name) (x : Expr) : MetaM Expr := do
  let quoted := Lean.mkConst (P ++ `quoted)
  let qty ← inferType quoted
  -- metavariables for the schema's parameters
  let (mvars, _, _) ← forallMetaTelescope qty
  let inst := mkAppN quoted mvars
  unless ← isDefEq inst x do
    throwError "entails: the premise{indentExpr x}\nis not an instance of {P}"
  let args ← mvars.mapM instantiateMVars
  schemaMemBuild x args 0 quoted

/-- The antecedent of `imp X Y`, i.e. of `app (app or (neg X)) Y`, reducing each layer. -/
def impPremise? (s : Expr) : MetaM (Option Expr) := do
  let s ← whnfR s
  match s.getAppFnArgs with
  | (``Classicism.Meta.Term.app, #[_, _, _, _, f, _]) =>
    let f ← whnfR f
    match f.getAppFnArgs with
    | (``Classicism.Meta.Term.app, #[_, _, _, _, _, nx]) =>
      let nx ← whnfR nx
      match nx.getAppFnArgs with
      | (``Classicism.Meta.Term.app, #[_, _, _, _, _, x]) => pure (some x)
      | _ => pure none
    | _ => pure none
  | _ => pure none


/-- The object types of the instances in the strict statement `imp (P₁.strict T…) (… (Q.strict U…))`:
for each premise and for the conclusion, the quotation of each type argument, with the
theorem's type parameters read as the object-type variables `tvs` (the derivation's, in
order). -/
def instanceArgsOf (strictTy : Expr) (tvs : Array Expr) :
    TermElabM (Array (Array Expr) × Array Expr) := do
  paramTelescope strictTy fun xs body => do
    let mut tyVars : List (FVarId × Quote.Kind × Expr) := []
    let mut j := 0
    for x in xs do
      if (← whnf (← inferType x)).isSort then
        let some tv := tvs[j]? | throwError "entails: more type parameters than object-type variables"
        let kind := if (← whnf (← inferType tv)).isConstOf ``Classicism.Meta.Ty
          then Quote.Kind.ty else Quote.Kind.rty
        tyVars := (x.fvarId!, kind, tv) :: tyVars
        j := j + 1
    let ctx : Quote.QCtx := { tyVars := tyVars }
    -- each type argument as the object type of the schema's corresponding parameter: a
    -- `Ty` or an `RTy`, as `P.quoted` takes it
    let argsOf (d : Expr) : TermElabM (Array Expr) := do
      let some pn := d.getAppFn.constName? | throwError "entails: not a principle:{indentExpr d}"
      let quotedTy ← inferType (Lean.mkConst (principleOf pn ++ `quoted))
      let kinds ← forallTelescope quotedTy fun ys _ => ys.mapM fun y => do
        pure ((← whnf (← inferType y)).isConstOf ``Classicism.Meta.RTy)
      let mut args : Array Expr := #[]
      let mut k := 0
      for a in d.getAppArgs do
        if (← whnf (← inferType a)).isSort then
          let isR := kinds[k]?.getD false
          args := args.push (← (if isR then Quote.quoteRTy a else Quote.quoteTy a).run ctx)
          k := k + 1
      return args
    let mut e := body
    let mut out : Array (Array Expr) := #[]
    repeat
      if e.isAppOfArity ``Classicism.imp 2 then
        out := out.push (← argsOf e.getAppArgs[0]!)
        e := e.getAppArgs[1]!
      else if e.isArrow then
        out := out.push (← argsOf e.bindingDomain!)
        e := e.bindingBody!
      else break
    return (out, ← argsOf e)

/-- Convert `d : Theorem target got` into a derivation of `exp`, when the two are the same
sentence up to the unfolding of the operations at constructor types and βη: δ in the empty
context on both (`unfoldConv`), the conversion certificate of `coerce` between the results,
and back. What `citeTheorem` does for a cited theorem. -/
def convertDeriv (target d got exp : Expr) : TermElabM Expr := do
  let nil := mkApp (Lean.mkConst ``List.nil [Level.zero]) Translate.tyE
  let tctx : Translate.TCtx := { ax := target, axIsC := true }
  let act : Translate.TrM Expr := do
    -- to the constructor at the head: `P.quoted τ…` unfolds (`quoted` is declared with the
    -- hints of an abbreviation, which `whnfR` does not see)
    let got ← whnf got
    let exp ← whnf exp
    if got == exp then return d
    let Δ ← Translate.hypsE
    let (got', p₁) ← Translate.unfoldConv nil got
    let d₁ ← match p₁ with
      | none => pure d
      | some p => Translate.rule ``Classicism.Meta.Derivable.conv #[nil, Δ, got, got', d, p]
    let (exp', p₂) ← Translate.unfoldConv nil exp
    let d₂ ← Translate.coerce d₁ got' exp'
    match p₂ with
    | none => pure d₂
    | some p =>
      Translate.rule ``Classicism.Meta.Derivable.conv
        #[nil, Δ, exp', exp, d₂, Translate.convSymm nil Translate.tyT exp exp' p]
  (act.run tctx).run' {}

/-- The axiom set and the conclusion of a `Derivable Sig Ax Γ Δ p` (or `Theorem Ax p`). -/
def derivableParts? (e : Expr) : Option (Expr × Expr) :=
  match e.getAppFnArgs with
  | (``Classicism.Meta.Derivable, #[_, Ax, _, _, p]) => some (Ax, p)
  | _ => none

/-- Given `d : Theorem Ax S` with `S = imp X₁ (… (imp Xₙ Y))`, the derivation of `Y` from
`C.axioms ∪ Ps`, citing each `Xᵢ` as an axiom in `Pᵢ.schema`. -/
def dischargePremises (ps : List Name) (Ps : Expr) (pargs : Array (Array Expr)) (d : Expr) :
    TermElabM Expr := do
  let axioms := Lean.mkConst ``Classicism.Meta.C.axioms
  let pureSig := Lean.mkConst ``Classicism.Meta.Signature.pure
  let _target ← mkAppM ``Union.union #[mkApp axioms pureSig, Ps]
  -- lift d to the target axiom set
  let dty ← whnf (← inferType d)
  let some (Ax, _) := derivableParts? dty
    | throwError "entails: the derivation does not have a `Theorem` type:{indentExpr dty}"
  let lift ←
    if Ax.isConstOf ``Classicism.Meta.C.axioms || (Ax.isAppOf ``Classicism.Meta.C.axioms) then
      withLocalDeclD `a (mkApp (Lean.mkConst ``Classicism.Meta.Sentence) pureSig) fun a =>
      withLocalDeclD `h (mkApp Ax a) fun h => do
        mkLambdaFVars #[a, h] (← mkAppOptM ``Or.inl #[mkApp (mkApp axioms pureSig) a, mkApp Ps a, h])
    else
      withLocalDeclD `a (mkApp (Lean.mkConst ``Classicism.Meta.Sentence) pureSig) fun a =>
      withLocalDeclD `h (mkApp Ax a) fun h => do
        mkLambdaFVars #[a, h] (← mkAppOptM ``False.elim #[← mkAppM ``Union.union #[mkApp axioms pureSig, Ps] <&> (mkApp · a), h])
  let mut cur ← mkAppM ``Classicism.Meta.Derivable.mono #[lift, d]
  let schemas := ps.map fun p => Lean.mkConst (p ++ `schema)
  for (p, i) in ps.zipIdx do
    -- cur : Theorem target (imp X rest)
    let cty ← whnf (← inferType cur)
    let some (_, s) := derivableParts? cty | throwError "entails: internal (premise)"
    let some X ← impPremise? s | throwError "entails: the derivation's statement is not an implication:{indentExpr s}"
    let target ← mkAppM ``Union.union #[mkApp axioms pureSig, Ps]
    let quoted := Lean.mkConst (p ++ `quoted)
    -- the instance of the premise's schema, from the strict statement; it is the premise as
    -- the derivation states it, or converts to it (the operations at constructor types
    -- unfolded there)
    let some args := pargs[i]? | throwError "entails: no premise {i} in the strict statement"
    let inst := mkAppN quoted args
    let mem ← schemaMemBuild inst args 0 quoted
    let memU ← unionMem schemas i inst mem
    let axInst ← mkAppOptM ``Classicism.Meta.Derivable.axiom
      #[pureSig, target, inst, ← mkAppOptM ``Or.inr #[mkApp (mkApp axioms pureSig) inst, mkApp Ps inst, memU]]
    let ax ← convertDeriv target axInst inst X
    cur ← mkAppM ``Classicism.Meta.Derivable.impE #[cur, ax]
  return cur

/-- The consequent of `imp X Y`, i.e. of `app (app or (app not X)) Y`. -/
def impRest? (s : Expr) : Option Expr :=
  match s.getAppFnArgs with
  | (``Classicism.Meta.Term.app, #[_, _, _, _, f, y]) =>
    match f.getAppFnArgs with
    | (``Classicism.Meta.Term.app, #[_, _, _, _, o, _]) =>
      if o.isAppOf ``Classicism.Meta.Term.or then some y else none
    | _ => none
  | _ => none

/-- `C.axioms ∪ Ps`. -/
def withC (Ps : Expr) : MetaM Expr :=
  mkAppM ``Union.union #[mkApp (Lean.mkConst ``Classicism.Meta.C.axioms) (Lean.mkConst ``Classicism.Meta.Signature.pure), Ps]

/-- Eliminate `hyp : ∃ x₁ …, a = quoted x₁ …` down to the equation, then specialize the
derivation `dname` so that its consequent is that instance, discharge its premises, and
rewrite along the equation. -/
partial def entailsElim (ps : List Name) (Ps : Expr) (dname : Name) (strictTy : Expr)
    (a hyp qcur : Expr) : TermElabM Expr := do
  let hty ← whnf (← inferType hyp)
  if hty.isAppOfArity ``Exists 2 then
    let dom := hty.getAppArgs[0]!
    let pred := hty.getAppArgs[1]!
    let goal ← mkAppM ``Classicism.Meta.Theorem #[← withC Ps, a]
    let k ← withLocalDeclD `x dom fun x => do
      withLocalDeclD `hx (← instantiateMVars (← whnf (mkApp pred x))) fun hx => do
        mkLambdaFVars #[x, hx] (← entailsElim ps Ps dname strictTy a hx (mkApp qcur x))
    mkAppOptM ``Exists.elim #[dom, pred, goal, hyp, k]
  else
    -- hyp : a = qcur (for a singleton conclusion, qcur is the equation's right side)
    let qcur ← match hty.eq? with
      | some (_, _, rhs) => pure rhs
      | none => pure qcur
    -- specialize the derivation so that its consequent is qcur: the
    -- conclusion's instance in the strict statement, its object types over the derivation's
    -- parameters, unified with qcur's
    let dty ← inferType (Lean.mkConst dname)
    let (tvs, _, _) ← forallMetaTelescope dty
    let (pargs, cargs) ← instanceArgsOf strictTy tvs
    let qquoted := qcur.getAppFn
    let cinst := mkAppN qquoted cargs
    unless ← isDefEq cinst qcur do
      throwError "entails: the conclusion's instance{indentExpr cinst}\nis not the schema's{indentExpr qcur}: the record gives only some instances"
    for tv in tvs do
      unless ← tv.mvarId!.isAssigned do
        let tvTy ← whnf (← inferType tv)
        if tvTy.isConstOf ``Classicism.Meta.Ty then
          tv.mvarId!.assign (Lean.mkConst ``Classicism.Meta.Ty.e)
        else
          tv.mvarId!.assign (Lean.mkConst ``Classicism.Meta.RTy.t)
    let d ← instantiateMVars (mkAppN (Lean.mkConst dname) tvs)
    let pargs ← pargs.mapM (·.mapM instantiateMVars)
    let dty' ← whnf (← inferType d)
    let some (_, s) := derivableParts? dty' | throwError "entails: internal (consequent)"
    let mut y := s
    for _ in ps do
      let y' ← whnfR y
      let some rest := impRest? y' | throwError "entails: not an implication:{indentExpr y'}"
      y := rest
    let D₀ ← dischargePremises ps Ps pargs d
    let target ← withC Ps
    let D ← convertDeriv target D₀ y qcur
    let sentenceTy := mkApp (Lean.mkConst ``Classicism.Meta.Sentence) (Lean.mkConst ``Classicism.Meta.Signature.pure)
    let motive ← withLocalDeclD `s sentenceTy fun s => do
      mkLambdaFVars #[s] (← mkAppM ``Classicism.Meta.Theorem #[← withC Ps, s])
    -- `Eq.mpr (congrArg motive hyp) D : motive a`, from `hyp : a = qcur` and `D : motive qcur`
    let hyp' ← instantiateMVars hyp
    let e ← mkAppM ``congrArg #[motive, hyp']
    mkAppM ``Eq.mpr #[e, D]

/-- Declare `foo.entails`. -/
def declareEntails (foo : Name) : TermElabM Unit := do
  let info ← getConstInfo foo
  let (ps, q) ← recordShape info.type
  let dname := foo ++ `derivable
  let some _dinfo := (← getEnv).find? dname
    | throwError "entails: no derivation {dname}; run `#classicism_derive {foo}` first"
  for p in q :: ps do
    unless (← getEnv).contains (p ++ `schema) do
      throwError "entails: no schema {p ++ `schema}; run `#classicism_schema {p}` first"
  let Ps ← premisesSet ps
  let pureSig := Lean.mkConst ``Classicism.Meta.Signature.pure
  let sentenceTy := mkApp (Lean.mkConst ``Classicism.Meta.Sentence) pureSig
  -- the conclusion: the schema `Q.schema` when the strict statement leaves its types
  -- variable; the singleton `{Q.quoted τ…}` when it fixes them, as `Existence e` does
  let dty ← inferType (Lean.mkConst dname)
  let Qs ← forallTelescope dty fun tvs _ => do
    let (_, cargs) ← instanceArgsOf info.type tvs
    let inst := mkAppN (Lean.mkConst (q ++ `quoted)) cargs
    if cargs.all fun c => !c.hasAnyFVar (fun id => tvs.any (·.fvarId! == id)) then
      -- the conclusion's types are fixed: the one instance, as `Existence e`
      mkAppM ``Classicism.Meta.AxiomSet.single #[inst]
    else if cargs.all (fun c => tvs.contains c) && cargs.toList.eraseDups.length == cargs.size then
      -- the conclusion's types are parameters: the whole schema
      pure (Lean.mkConst (q ++ `schema))
    else
      -- expressions in the parameters, as `Existence (σ → t)`: the instances over them,
      -- `fun a => ∃ σ' …, a = Q.quoted (…)`
      withLocalDeclD `a sentenceTy fun a => do
        let mut body ← mkEq a inst
        for tv in tvs.reverse do
          body ← mkAppM ``Exists #[← mkLambdaFVars #[tv] body]
        mkLambdaFVars #[a] body
  let stmt ← mkAppM ``Classicism.Meta.AxiomSet.Entails #[Ps, Qs]
  -- the proof: fun a ha => elim ha, rewriting a to the instance, then the derivation
  let proof ← withLocalDeclD `a sentenceTy fun a => do
    let haTy := mkApp Qs a
    withLocalDeclD `ha haTy fun ha => do
      let body ← entailsElim ps Ps dname info.type a ha (Lean.mkConst (q ++ `quoted))
      mkLambdaFVars #[a, ha] body
  let proof ← instantiateMVars proof
  let tv : TheoremVal := { name := foo ++ `entails, levelParams := [], type := stmt, value := proof }
  withOptions (Elab.async.set · false) do addDecl (.thmDecl tv)

/-! ### Rules

An entailment between schemas forgets which instance of the premise yields which instance
of the conclusion. A metalogical proof that descends into the object language needs to
keep that: a step "from Atomicity at `ρ` and BF at `σ`, Atomicity at `σ → ρ`" is applied
at particular types, inside an induction on the type. `foo.rule` is the derivation of the
record theorem read that way, as a theorem of `C` for every choice of object types,

    foo.rule : ∀ σ' ρ' …, C.Theorem (imp (P₁.quoted …) (… (imp (Pₙ.quoted …) (Q.quoted …))))

each instance written through its schema's `quoted`, so that the rule composes with
`Theorem.mp` and the schemas' membership. -/

/-- Declare `foo.rule`. -/
def declareRule (foo : Name) : TermElabM Unit := do
  let info ← getConstInfo foo
  let (ps, q) ← recordShape info.type
  let dname := foo ++ `derivable
  unless (← getEnv).contains dname do
    throwError "rule: no derivation {dname}; run `#classicism_derive {foo}` first"
  for p in q :: ps do
    unless (← getEnv).contains (p ++ `schema) do
      throwError "rule: no schema {p ++ `schema}; run `#classicism_schema {p}` first"
  let dty ← inferType (Lean.mkConst dname)
  let pureSig := Lean.mkConst ``Classicism.Meta.Signature.pure
  let axiomsC := mkApp (Lean.mkConst ``Classicism.Meta.C.axioms) pureSig
  let (stmt, proof) ← forallTelescope dty fun tvs body => do
    let (pargs, cargs) ← instanceArgsOf info.type tvs
    let nil := mkApp (Lean.mkConst ``List.nil [Level.zero]) Translate.tyE
    let mut exp := mkAppN (Lean.mkConst (q ++ `quoted)) cargs
    for (p, args) in (ps.zip pargs.toList).reverse do
      exp := Translate.impE nil (mkAppN (Lean.mkConst (p ++ `quoted)) args) exp
    let d := mkAppN (Lean.mkConst dname) tvs
    let some (Ax, got) := derivableParts? (← whnf body)
      | throwError "rule: {dname} does not have a `Theorem` type"
    -- a derivation in `C⁻` is one in `C`
    let d ← if Ax.isAppOf ``Classicism.Meta.C.axioms then pure d else do
      let lift ← withLocalDeclD `a (mkApp (Lean.mkConst ``Classicism.Meta.Sentence) pureSig) fun a =>
        withLocalDeclD `h (mkApp Ax a) fun h => do
          mkLambdaFVars #[a, h] (← mkAppOptM ``False.elim #[mkApp axiomsC a, h])
      mkAppM ``Classicism.Meta.Derivable.mono #[lift, d]
    let D ← convertDeriv axiomsC d got exp
    let thm ← mkAppM ``Classicism.Meta.Theorem #[axiomsC, exp]
    return (← mkForallFVars tvs thm, ← mkLambdaFVars tvs D)
  let proof ← instantiateMVars proof
  let tv : TheoremVal := { name := foo ++ `rule, levelParams := [], type := stmt, value := proof }
  withOptions (Elab.async.set · false) do addDecl (.thmDecl tv)

/-- `#classicism_rule foo …`: each record theorem `foo` with a derivation becomes the rule
`foo.rule`. -/
syntax (name := classicismRule) "#classicism_rule " ident+ : command

@[command_elab classicismRule] def elabRule : CommandElab := fun stx => do
  for id in stx[1].getArgs do
    let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
    try
      liftTermElabM (declareRule n)
      logInfo m!"{n} ⟶ {n ++ `rule} : {(← getConstInfo (n ++ `rule)).type}"
    catch ex =>
      logError m!"{n}: no rule — {ex.toMessageData}"

/-- `#classicism_certify foo …`: the whole chain for a theorem `foo : P₁ … → … → Q …` of
the shallow layer, at the point where it is stated. It makes schemas of the principles it
mentions that have none yet, derives `foo` in the object language (`foo.derivable`), and
declares the rule `foo.rule`; each step is skipped when its declaration already exists. The
report gives the rule and the axioms it rests on. -/
syntax (name := classicismCertify) "#classicism_certify " ident+ : command

@[command_elab classicismCertify] def elabCertify : CommandElab := fun stx => do
  for id in stx[1].getArgs do
    let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
    try
      let (ps, q) ← liftTermElabM do recordShape (← getConstInfo n).type
      for p in q :: ps do
        unless (← getEnv).contains (p ++ `schema) do liftTermElabM (declareSchema p)
      unless (← getEnv).contains (n ++ `derivable) do
        withScope (fun sc => { sc with opts := maxHeartbeats.set sc.opts 0 })
          (liftTermElabM (Translate.derive n))
      liftTermElabM (declareRule n)
      let ax ← liftTermElabM (collectAxioms (n ++ `rule))
      logInfo m!"{n} ⟶ {n ++ `rule} : {(← getConstInfo (n ++ `rule)).type}\ncertified ✓ (axioms: {ax.toList})"
    catch ex =>
      logError m!"{n}: not certified — {ex.toMessageData}"

/-- `#classicism_entails foo …`: each record theorem `foo : P₁ … → … → Q …` with a derivation
`foo.strict.derivable` becomes `foo.entails : P₁.schema ∪ … ⟹ Q.schema`. -/
syntax (name := classicismEntails) "#classicism_entails " ident+ : command

@[command_elab classicismEntails] def elabEntails : CommandElab := fun stx => do
  for id in stx[1].getArgs do
    let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
    try
      liftTermElabM (declareEntails n)
      logInfo m!"{n} ⟶ {n ++ `entails} : {(← getConstInfo (n ++ `entails)).type}"
    catch ex =>
      logError m!"{n}: no entailment — {ex.toMessageData}"

/-- `#classicism_entails_audit Mod …`: for every theorem `foo` of the module with a strict twin
`foo.strict`, derive it if `foo.strict.derivable` does not exist, then declare
`foo.entails`; report what was certified and what was not, and why. -/
syntax (name := classicismEntailsAudit) "#classicism_entails_audit " ident+ : command

@[command_elab classicismEntailsAudit] def elabEntailsAudit : CommandElab := fun stx => do
  for modId in stx[1].getArgs do
    let env ← getEnv
    let some idx := env.getModuleIdx? modId.getId
      | logError m!"no module {modId.getId}"; continue
    let mut names : Array Name := #[]
    let mut skipped : Array Name := #[]
    for (n, ci) in env.constants.toList do
      if env.getModuleIdxFor? n == some idx then
        if let .thmInfo _ := ci then
          if !n.isInternal then
            -- a record theorem is built from the map's principles; a helper lemma is not
            let isRecord ← liftTermElabM do
              try
                let (ps, q) ← recordShape (← getConstInfo n).type
                pure ((q :: ps).all fun p => (`Classicism.P).isPrefixOf p)
              catch _ => pure false
            if isRecord then names := names.push n else skipped := skipped.push n
    names := names.qsort (fun a b => a.toString < b.toString)
    let mut ok : Nat := 0
    let mut lines : Array String := #[]
    let mut failures : Array MessageData := #[]
    for n in names do
      let t₀ ← IO.monoMsNow
      try
        unless (← getEnv).contains (n ++ `derivable) do
          withScope (fun sc => { sc with opts := maxHeartbeats.set sc.opts 0 })
            (liftTermElabM (Classicism.Meta.Translate.derive n))
        liftTermElabM (declareEntails n)
        ok := ok + 1
        lines := lines.push s!"{n} ✓ {(← IO.monoMsNow) - t₀} ms : {← liftTermElabM do
          pure (toString (← Meta.ppExpr (← getConstInfo (n ++ `entails)).type))}"
      catch ex =>
        failures := failures.push m!"{n}: {ex.toMessageData}"
        lines := lines.push s!"{n} ✗ {(← IO.monoMsNow) - t₀} ms"
    logInfo m!"{modId.getId}: {ok} of {names.size} record theorems certified as entailments; \
{skipped.size} helper lemmas skipped\n{MessageData.joinSep failures.toList "\n"}\n\
{"\n".intercalate lines.toList}"

end Classicism.Meta
