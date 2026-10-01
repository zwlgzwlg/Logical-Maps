import Classicism.Tools.Translate
import Classicism.Syntax.Entailment
import Classicism.Syntax.VectorizeDerivable

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
  *closed* object types `σ' …`, the types of the paper's language (no type variable:
  `Syntax/Types.lean`).
- `#classicism_entails_audit Mod …` does that for every record theorem of a module, deriving
  first where no derivation exists, and reports.
- For a principle with a Ty-parameter, `#classicism_schema` declares its **list form**
  too (`P.listQuoted`, `P.listSchema`, and `P.listSchema ⟹ P.schema`); for a record with
  one, the audit declares `foo.listRule` and `foo.listEntails`, and `#classicism_certify`
  declares `foo.listRule` (the sections *List forms* below).
- `#classicism_entails foo …` reads the statement of `foo`, of the form
  `P₁ … → … → Pₙ … → Q …`, and its derivation `foo.derivable` (from
  `#classicism_derive`), and declares `foo.entails : P₁.schema ∪ … ∪ Pₙ.schema ⟹ Q.schema`.
  For each instance of `Q` it specializes the derivation to the object types that make
  its consequent that instance (any type for a parameter the consequent does not mention),
  and cites the premises as axioms of their schemas — the instances read off the
  statement, converted by the translator where an operation at a constructor type has
  been unfolded, their types closed because the conclusion's are. When the statement fixes the conclusion's types (`Existence e`) the
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

/-- `Ty.Closed x`, `RTy.Closed x` or `Ty.AllClosed x`, as `x` is a type, a relational type
or a list of types. -/
def closedProp (x : Expr) : MetaM Expr := do
  let ty ← whnf (← inferType x)
  if ty.isConstOf ``Classicism.Meta.Ty then
    mkAppM ``Classicism.Meta.Ty.Closed #[x]
  else if ty.isAppOf ``List then
    mkAppM ``Classicism.Meta.Ty.AllClosed #[x]
  else
    mkAppM ``Classicism.Meta.RTy.Closed #[x]

/-- `∃ x₁ … xₙ, x₁ closed ∧ … ∧ xₙ closed ∧ a = q x₁ … xₙ`, for `q` a quoted schema
applied to some of its parameters: the instances at closed types. -/
def schemaBody (q a : Expr) : MetaM Expr := do
  forallTelescope (← inferType q) fun xs _ => do
    let mut body ← mkEq a (mkAppN q xs)
    for x in xs.reverse do
      body ← mkAppM ``And #[← closedProp x, body]
    for x in xs.reverse do
      body ← mkAppM ``Exists #[← mkLambdaFVars #[x] body]
    return body

/-- From `quoted : ∀ (x₁ : Ty) …, Sentence`, the axiom set of its instances at closed
types, `fun a => ∃ x₁ …, x₁ closed ∧ … ∧ a = quoted x₁ …`. -/
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

/-- A proof that the type `e` is closed, from proofs `hyps` that some free variables are:
by its constructors down to those variables, and by evaluation for anything else. -/
partial def closedProof (hyps : Array (Expr × Expr)) (e : Expr) : MetaM Expr := do
  if let some (_, h) := hyps.find? (·.1 == e) then return h
  let e' ← whnfR e
  match e'.getAppFnArgs with
  | (``Classicism.Meta.Ty.e, #[]) => pure (Lean.mkConst ``Classicism.Meta.Ty.closed_e)
  | (``Classicism.Meta.Ty.rel, #[ρ]) =>
    mkAppM ``Iff.mpr #[← mkAppM ``Classicism.Meta.Ty.closed_rel #[ρ], ← closedProof hyps ρ]
  | (``Classicism.Meta.RTy.t, #[]) => pure (Lean.mkConst ``Classicism.Meta.RTy.closed_t)
  | (``Classicism.Meta.RTy.arr, #[σ, ρ]) =>
    mkAppM ``Iff.mpr #[← mkAppM ``Classicism.Meta.RTy.closed_arr #[σ, ρ],
      ← mkAppM ``And.intro #[← closedProof hyps σ, ← closedProof hyps ρ]]
  | (``Classicism.Meta.RTy.arrs, #[σs, ρ]) =>
    mkAppM ``Iff.mpr #[← mkAppM ``Classicism.Meta.RTy.closed_arrs #[σs, ρ],
      ← mkAppM ``And.intro #[← closedProof hyps σs, ← closedProof hyps ρ]]
  | (``List.cons, #[_, σ, tl]) =>
    if tl.isAppOf ``List.nil then
      mkAppM ``Classicism.Meta.Ty.allClosed_singleton #[← closedProof hyps σ]
    else mkDecideProof (← closedProp e)
  | _ => mkDecideProof (← closedProp e)

/-- A proof of `x ∈ q.schema`, that is of the body `∃ rest, rest closed ∧ x = q rest`, at
the arguments `args`: `⟨args, closedness, rfl⟩`, the closedness from `hyps`, and the
equation `eq?` in place of `rfl` when it is given. -/
partial def schemaMemBuild (hyps : Array (Expr × Expr)) (x : Expr) (args : Array Expr) (q : Expr)
    (eq? : Option Expr := none) : MetaM Expr := do
  let body ← instantiateMVars (← schemaBody q x)
  go body args.toList args.toList
where
  go (prop : Expr) (args cargs : List Expr) : MetaM Expr := do
    if prop.isAppOfArity ``Exists 2 then
      let pred := prop.appArg!
      match args with
      | a :: rest =>
        let inner ← go (pred.beta #[a]).headBeta rest cargs
        mkAppOptM ``Exists.intro #[none, pred, a, inner]
      | [] => throwError "schema membership: too few arguments"
    else if prop.isAppOfArity ``And 2 then
      match cargs with
      | c :: rest =>
        mkAppM ``And.intro #[← closedProof hyps c, ← go prop.appArg! [] rest]
      | [] => throwError "schema membership: too few arguments"
    else
      match eq? with
      | some h => pure h
      | none => mkEqRefl x

/-- A proof that `x` is in `P.schema`: `⟨args, closedness, rfl⟩`, the arguments found by
unification and their closedness from `hyps`. -/
def schemaMem (P : Name) (x : Expr) (hyps : Array (Expr × Expr) := #[]) : MetaM Expr := do
  let quoted := Lean.mkConst (P ++ `quoted)
  let qty ← inferType quoted
  -- metavariables for the schema's parameters
  let (mvars, _, _) ← forallMetaTelescope qty
  let inst := mkAppN quoted mvars
  unless ← isDefEq inst x do
    throwError "entails: the premise{indentExpr x}\nis not an instance of {P}"
  let args ← mvars.mapM instantiateMVars
  schemaMemBuild hyps x args quoted

/-! ### List forms

A principle with a Ty-parameter has a **list form** beside its schema: one instance for
each finite list of types, the empty list included (`VECTORIZATION-PLAN.md`). It is
*defined*, never written: `P.listQuoted σs …` is `P.quoted` at the type variable `var 0`,
vectorized along `0 ↦ σs` (`Syntax/Vectorize.lean`), so it cannot be mis-stated. The
first Ty-parameter is the one vectorized, which in every principle of the map is its
input; a second (Relational Choice's output) stays a single type, passed through the type
variable `var 1` assigned the one-element list of it, and a Rel-parameter is passed as
itself. The assignment so mentions only the Ty-parameters, and a record over the same
ones vectorizes along the same assignment, which is what lets its instances come out as
list forms on the nose.
Declared with it:

- `P.listSchema`, its instances over closed types;
- `P.listQuoted_single`, that at a one-element list it is the principle: by computation,
  up to the Rel-parameters, which the translation leaves alone when they are closed;
- `P.schema_subset_listSchema` and `P.listSchema_entails_schema`, the list form entails
  the restricted form. -/

/-- The kinds of a principle's parameters, from `P.quoted`'s type: `true` for a type, `false`
for a relational type. -/
def paramKinds (n : Name) : MetaM (Array Bool) := do
  forallTelescope (← inferType (Lean.mkConst (n ++ `quoted))) fun xs _ => xs.mapM fun x => do
    pure ((← whnf (← inferType x)).isConstOf ``Classicism.Meta.Ty)

/-- The type variable standing for the Ty-parameter at position `j`: `var 0` for the
vectorized one (the first), `var 1`, `var 2`, … for the others, in order. -/
def tyVarIndex (kinds : Array Bool) (j : Nat) : Nat :=
  ((List.range j).filter fun i => kinds[i]!).length

/-- The entries of the assignment of a list form: the list, then the one-element list of
each other Ty-parameter's type, in order. -/
def listEntries (kinds : Array Bool) (i₀ : Nat) (xs : Array Expr) : MetaM (Array Expr) := do
  let tyE := Lean.mkConst ``Classicism.Meta.Ty
  let entries ← (List.range kinds.size).filterMapM fun j => do
    if j == i₀ then pure (some xs[j]!)
    else if kinds[j]! then pure (some (← mkListLit tyE [xs[j]!]))
    else pure none
  return entries.toArray

/-- The assignment of a list form, given its arguments `xs` (the list at position `i₀`):
`Assign.ofList` of the list and of the one-element list of each other Ty-parameter's type,
in order. It mentions no Rel-parameter, so that a principle and a record over the same
Ty-parameters vectorize along the same assignment. -/
def listAssign (kinds : Array Bool) (i₀ : Nat) (xs : Array Expr) : MetaM Expr := do
  let tyE := Lean.mkConst ``Classicism.Meta.Ty
  let entries ← (List.range kinds.size).filterMapM fun j => do
    if j == i₀ then pure (some xs[j]!)
    else if kinds[j]! then pure (some (← mkListLit tyE [xs[j]!]))
    else pure none
  mkAppM ``Classicism.Meta.Assign.ofList #[← mkListLit (← mkAppM ``List #[tyE]) entries]

/-- The binders of a list form: the list at `i₀`, the others with their kinds. -/
def listBinders (kinds : Array Bool) (i₀ : Nat) : MetaM (Array (Name × Expr)) := do
  let tyE := Lean.mkConst ``Classicism.Meta.Ty
  let listTy ← mkAppM ``List #[tyE]
  return kinds.mapIdx fun j k =>
    if j == i₀ then (`σs, listTy)
    else if k then (Name.mkSimple s!"τ{j}", tyE)
    else (Name.mkSimple s!"ρ{j}", Lean.mkConst ``Classicism.Meta.RTy)

/-- Eliminate `hyp`, a membership `∃ x₁ …, x₁ closed ∧ … ∧ a = q x₁ …`, into a proof of
`goal`, handing the continuation the types, their closedness, and the equation. -/
partial def elimSchemaMem (hyp goal : Expr)
    (k : Array Expr → Array (Expr × Expr) → Expr → MetaM Expr)
    (xs : Array Expr := #[]) (hyps : Array (Expr × Expr) := #[]) : MetaM Expr := do
  let hty ← whnf (← inferType hyp)
  if hty.isAppOfArity ``And 2 then
    let c := hty.appFn!.appArg!
    elimSchemaMem (← mkAppM ``And.right #[hyp]) goal k xs (hyps.push (c.appArg!, ← mkAppM ``And.left #[hyp]))
  else if hty.isAppOfArity ``Exists 2 then
    let dom := hty.getAppArgs[0]!
    let pred := hty.getAppArgs[1]!
    let kk ← withLocalDeclD `x dom fun x => do
      withLocalDeclD `hx (← instantiateMVars (mkApp pred x).headBeta) fun hx => do
        mkLambdaFVars #[x, hx] (← elimSchemaMem hx goal k (xs.push x) hyps)
    mkAppOptM ``Exists.elim #[dom, pred, goal, hyp, kk]
  else
    k xs hyps hyp

/-- Declare the list form of the principle `n`, if it has a Ty-parameter. -/
def declareListForm (n : Name) : TermElabM Bool := do
  let kinds ← paramKinds n
  let some i₀ := kinds.findIdx? (fun b => b) | return false
  let quoted := Lean.mkConst (n ++ `quoted)
  let pureSig := Lean.mkConst ``Classicism.Meta.Signature.pure
  let sentenceTy := mkApp (Lean.mkConst ``Classicism.Meta.Sentence) pureSig
  let tyVar (j : Nat) := mkApp (Lean.mkConst ``Classicism.Meta.Ty.var) (mkNatLit j)
  -- `listQuoted`
  let binders ← listBinders kinds i₀
  let (lqTy, lqVal) ← withLocalDeclsDND binders fun xs => do
    let θ ← listAssign kinds i₀ xs
    let args := (List.range kinds.size).toArray.map fun j =>
      if kinds[j]! then tyVar (tyVarIndex kinds j) else xs[j]!
    let hc := mkApp (Lean.mkConst ``Classicism.Meta.Signature.pure_vecFixed) θ
    let body ← mkAppM ``Classicism.Meta.Term.vec1 #[θ, hc, mkAppN quoted args]
    pure (← mkForallFVars xs sentenceTy, ← mkLambdaFVars xs body)
  let lq := n ++ `listQuoted
  let dv : DefinitionVal :=
    { name := lq, levelParams := [], type := lqTy, value := lqVal, hints := .abbrev, safety := .safe }
  withOptions (Elab.async.set · false) do addDecl (.defnDecl dv)
  modifyEnv fun env => addNoncomputable env lq
  setReducibilityStatus lq .reducible
  -- `listSchema`
  let ls := n ++ `listSchema
  let schema ← schemaOfQuoted (Lean.mkConst lq)
  let lsTy ← inferType schema
  let dv : DefinitionVal :=
    { name := ls, levelParams := [], type := lsTy, value := schema, hints := .abbrev, safety := .safe }
  withOptions (Elab.async.set · false) do addDecl (.defnDecl dv)
  modifyEnv fun env => addNoncomputable env ls
  setReducibilityStatus ls .reducible
  -- `listQuoted_single`: at `[σ]`, the principle at `σ`, given the Rel-parameters closed
  let tyE := Lean.mkConst ``Classicism.Meta.Ty
  let sbinders := binders.set! i₀ (`σ, tyE)
  let (lsTy, lsVal) ← withLocalDeclsDND sbinders fun xs => do
    let rels := (List.range kinds.size).filter (fun j => !kinds[j]!)
    let hbinders ← rels.toArray.mapM fun j => do
      pure (Name.mkSimple s!"h{j}", ← mkAppM ``Classicism.Meta.RTy.Closed #[xs[j]!])
    withLocalDeclsDND hbinders fun hs => do
      let single ← mkListLit tyE [xs[i₀]!]
      let lxs := xs.set! i₀ single
      let lhs := mkAppN (Lean.mkConst lq) lxs
      let θ ← listAssign kinds i₀ lxs
      let rem := (List.range kinds.size).toArray.map fun j =>
        if kinds[j]! then xs[j]! else mkApp2 (Lean.mkConst ``Classicism.Meta.RTy.vec) θ xs[j]!
      let remE := mkAppN quoted rem
      unless ← isDefEq lhs remE do
        throwError "list form of {n}: at a one-element list it does not compute to the principle"
      let mut pf ← mkEqRefl quoted
      let mut r := 0
      for j in List.range kinds.size do
        if kinds[j]! then
          pf ← mkCongrFun pf xs[j]!
        else
          pf ← mkCongr pf (← mkAppM ``Classicism.Meta.RTy.vec_closed #[θ, hs[r]!])
          r := r + 1
      let stmt ← mkEq lhs (mkAppN quoted xs)
      pure (← mkForallFVars (xs ++ hs) stmt, ← mkLambdaFVars (xs ++ hs) pf)
  let tv : TheoremVal := { name := n ++ `listQuoted_single, levelParams := [], type := lsTy, value := lsVal }
  withOptions (Elab.async.set · false) do addDecl (.thmDecl tv)
  -- `schema_subset_listSchema`, and the entailment
  let subTy ← mkAppM ``HasSubset.Subset #[Lean.mkConst (n ++ `schema), Lean.mkConst ls]
  let subVal ← withLocalDeclD `a sentenceTy fun a => do
    withLocalDeclD `ha (mkApp (Lean.mkConst (n ++ `schema)) a) fun ha => do
      let goal := mkApp (Lean.mkConst ls) a
      let body ← elimSchemaMem ha goal fun ys hyps heq => do
        let single ← mkListLit tyE [ys[i₀]!]
        let lys := ys.set! i₀ single
        let rels := (List.range kinds.size).filter (fun j => !kinds[j]!)
        let hrel ← rels.toArray.mapM fun j => closedProof hyps ys[j]!
        let eqS ← mkAppM ``Eq.symm #[mkAppN (Lean.mkConst (n ++ `listQuoted_single)) (ys ++ hrel)]
        let eqA ← mkAppM ``Eq.trans #[heq, eqS]
        schemaMemBuild hyps a lys (Lean.mkConst lq) (some eqA)
      mkLambdaFVars #[a, ha] body
  let subVal ← instantiateMVars subVal
  let tv : TheoremVal := { name := n ++ `schema_subset_listSchema, levelParams := [], type := subTy, value := subVal }
  withOptions (Elab.async.set · false) do addDecl (.thmDecl tv)
  let entTy ← mkAppM ``Classicism.Meta.AxiomSet.Entails #[Lean.mkConst ls, Lean.mkConst (n ++ `schema)]
  let entVal ← mkAppM ``Classicism.Meta.AxiomSet.Entails.of_subset #[Lean.mkConst (n ++ `schema_subset_listSchema)]
  let tv : TheoremVal := { name := n ++ `listSchema_entails_schema, levelParams := [], type := entTy, value := entVal }
  withOptions (Elab.async.set · false) do addDecl (.thmDecl tv)
  return true

/-- `#classicism_schema P …`: each principle `P` becomes a schema, `P.schema`. -/
syntax (name := classicismSchema) "#classicism_schema " ident+ : command

@[command_elab classicismSchema] def elabSchema : CommandElab := fun stx => do
  let mut lists : Nat := 0
  let mut withTy : Nat := 0
  for id in stx[1].getArgs do
    let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
    try
      liftTermElabM (declareSchema n)
      logInfo m!"{n} ⟶ {n ++ `schema}:{indentExpr (← getConstInfo (n ++ `quoted)).value!}"
    catch ex =>
      logError m!"{n}: no schema — {ex.toMessageData}"
    if (← liftTermElabM (paramKinds n)).any (fun b => b) then
      withTy := withTy + 1
      try
        if ← liftTermElabM (declareListForm n) then lists := lists + 1
      catch ex =>
        logError m!"{n}: no list form — {ex.toMessageData}"
  if withTy > 0 then
    logInfo m!"#classicism_schema: {lists} of {withTy} principles with a Ty-parameter have list forms"

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
theorem's type parameters read as the metalogical ones `tvs` (the derivation's, in
order). -/
def instanceArgsOf (strictTy : Expr) (tvs : Array Expr) :
    TermElabM (Array (Array Expr) × Array Expr) := do
  paramTelescope strictTy fun xs body => do
    let mut tyVars : List (FVarId × Quote.Kind × Expr) := []
    let mut j := 0
    for x in xs do
      if (← whnf (← inferType x)).isSort then
        let some tv := tvs[j]? | throwError "entails: more type parameters than the derivation has"
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
def dischargePremises (ps : List Name) (Ps : Expr) (pargs : Array (Array Expr)) (d : Expr)
    (hyps : Array (Expr × Expr)) : TermElabM Expr := do
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
    let mem ← schemaMemBuild hyps inst args quoted
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

/-- Eliminate `hyp : ∃ x₁ …, x₁ closed ∧ … ∧ a = quoted x₁ …` down to the equation,
collecting the closedness of the types in `hyps`, then specialize the derivation `dname`
so that its consequent is that instance, discharge its premises, and rewrite along the
equation. -/
partial def entailsElim (ps : List Name) (Ps : Expr) (dname : Name) (strictTy : Expr)
    (a hyp qcur : Expr) (hyps : Array (Expr × Expr) := #[]) : TermElabM Expr := do
  let hty ← whnf (← inferType hyp)
  if hty.isAppOfArity ``And 2 then
    let c := hty.appFn!.appArg!
    let h₁ ← mkAppM ``And.left #[hyp]
    let h₂ ← mkAppM ``And.right #[hyp]
    entailsElim ps Ps dname strictTy a h₂ qcur (hyps.push (c.appArg!, h₁))
  else if hty.isAppOfArity ``Exists 2 then
    let dom := hty.getAppArgs[0]!
    let pred := hty.getAppArgs[1]!
    let goal ← mkAppM ``Classicism.Meta.Theorem #[← withC Ps, a]
    let k ← withLocalDeclD `x dom fun x => do
      withLocalDeclD `hx (← instantiateMVars (← whnf (mkApp pred x))) fun hx => do
        mkLambdaFVars #[x, hx] (← entailsElim ps Ps dname strictTy a hx (mkApp qcur x) hyps)
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
    let D₀ ← dischargePremises ps Ps pargs d hyps
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
      -- expressions in the parameters, as `Existence (σ → t)`: the instances over them at
      -- closed types, `fun a => ∃ σ' …, σ' closed ∧ … ∧ a = Q.quoted (…)`
      withLocalDeclD `a sentenceTy fun a => do
        let mut body ← mkEq a inst
        for tv in tvs.reverse do
          body ← mkAppM ``And #[← closedProp tv, body]
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

/-- The rule of the record `foo` at the object types `tvs`, any expressions of the kinds of
the derivation's parameters: the statement `imp (P₁.quoted …) (… (Q.quoted …))`, its
derivation in `C`, and the instances' arguments, the premises' and the conclusion's. -/
def ruleAt (foo : Name) (tvs : Array Expr) :
    TermElabM (Expr × Expr × Array (Array Expr) × Array Expr) := do
  let info ← getConstInfo foo
  let (ps, q) ← recordShape info.type
  let dname := foo ++ `derivable
  unless (← getEnv).contains dname do
    throwError "rule: no derivation {dname}; run `#classicism_derive {foo}` first"
  for p in q :: ps do
    unless (← getEnv).contains (p ++ `schema) do
      throwError "rule: no schema {p ++ `schema}; run `#classicism_schema {p}` first"
  let pureSig := Lean.mkConst ``Classicism.Meta.Signature.pure
  let axiomsC := mkApp (Lean.mkConst ``Classicism.Meta.C.axioms) pureSig
  let (pargs, cargs) ← instanceArgsOf info.type tvs
  let nil := mkApp (Lean.mkConst ``List.nil [Level.zero]) Translate.tyE
  let mut exp := mkAppN (Lean.mkConst (q ++ `quoted)) cargs
  for (p, args) in (ps.zip pargs.toList).reverse do
    exp := Translate.impE nil (mkAppN (Lean.mkConst (p ++ `quoted)) args) exp
  let d := mkAppN (Lean.mkConst dname) tvs
  let some (Ax, got) := derivableParts? (← whnf (← inferType d))
    | throwError "rule: {dname} does not have a `Theorem` type"
  -- a derivation in `C⁻` is one in `C`
  let d ← if Ax.isAppOf ``Classicism.Meta.C.axioms then pure d else do
    let lift ← withLocalDeclD `a (mkApp (Lean.mkConst ``Classicism.Meta.Sentence) pureSig) fun a =>
      withLocalDeclD `h (mkApp Ax a) fun h => do
        mkLambdaFVars #[a, h] (← mkAppOptM ``False.elim #[mkApp axiomsC a, h])
    mkAppM ``Classicism.Meta.Derivable.mono #[lift, d]
  let D ← convertDeriv axiomsC d got exp
  return (exp, D, pargs, cargs)

/-- Declare `foo.rule`. -/
def declareRule (foo : Name) : TermElabM Unit := do
  let dty ← inferType (Lean.mkConst (foo ++ `derivable))
  let axiomsC := mkApp (Lean.mkConst ``Classicism.Meta.C.axioms) (Lean.mkConst ``Classicism.Meta.Signature.pure)
  let (stmt, proof) ← forallTelescope dty fun tvs _ => do
    let (exp, D, _, _) ← ruleAt foo tvs
    let thm ← mkAppM ``Classicism.Meta.Theorem #[axiomsC, exp]
    return (← mkForallFVars tvs thm, ← mkLambdaFVars tvs D)
  let proof ← instantiateMVars proof
  let tv : TheoremVal := { name := foo ++ `rule, levelParams := [], type := stmt, value := proof }
  withOptions (Elab.async.set · false) do addDecl (.thmDecl tv)

/-! ### List forms of records

A record whose statement has a Ty-parameter has a list form too: its derivation, uniform
in the parameter, holds at the type variable `var 0`, and the vectorization theorem
(`C.Theorem.vec`) carries it to every list. Each instance comes out either as a list form,
`P.listQuoted σs …`, when its first Ty-argument is the record's vectorized parameter, or
as a restricted instance at the translated types (`Atomicity` at `σs ⇒* τ`), the other
parameters' translations rewritten away by their closedness. So

    foo.listRule : ∀ σs τ … ρ …, τ closed → … → ρ closed → … →
      C.Theorem (imp (P₁.listQuoted σs …) (… Q…))
    foo.listEntails : P₁.listSchema ∪ … ⟹ Q.listSchema

with a restricted instance's schema in place of a list schema where the instance is
restricted, and the family of the conclusion's instances in place of `Q.listSchema` where
the conclusion is not `Q`'s list form at the record's own parameters. The forms are
checked against the vectorized derivation by unification, and a record whose instances
do not take one of these forms gets none. -/

mutual
  /-- The translation along `θ` of a type expression, as a list expression: computed
  through the constructors and the assignment's entries `ls` (`θ` is `Assign.ofList ls`),
  and left as `Ty.vec θ x` at anything else, so that a remnant keeps `θ` folded. -/
  partial def vecTyExpr (θ : Expr) (ls : Array Expr) (a : Expr) : MetaM Expr := do
    let tyE := Lean.mkConst ``Classicism.Meta.Ty
    let a' ← whnfR a
    match a'.getAppFnArgs with
    | (``Classicism.Meta.Ty.e, #[]) => mkListLit tyE [a']
    | (``Classicism.Meta.Ty.rel, #[ρ]) =>
      mkListLit tyE [mkApp (Lean.mkConst ``Classicism.Meta.Ty.rel) (← vecRTyExpr θ ls ρ)]
    | (``Classicism.Meta.Ty.var, #[n]) =>
      match n.nat? <|> n.rawNatLit? with
      | some i => pure (ls[i]?.getD (← mkListLit tyE [a']))
      | none => pure (mkApp2 (Lean.mkConst ``Classicism.Meta.Ty.vec) θ a)
    | _ => pure (mkApp2 (Lean.mkConst ``Classicism.Meta.Ty.vec) θ a)
  /-- The translation along `θ` of a relational type expression, likewise. -/
  partial def vecRTyExpr (θ : Expr) (ls : Array Expr) (a : Expr) : MetaM Expr := do
    let a' ← whnfR a
    match a'.getAppFnArgs with
    | (``Classicism.Meta.RTy.t, #[]) => pure a'
    | (``Classicism.Meta.RTy.arr, #[σ, ρ]) =>
      let l ← vecTyExpr θ ls σ
      let r ← vecRTyExpr θ ls ρ
      match l.getAppFnArgs with
      | (``List.cons, #[_, x, tl]) =>
        if tl.isAppOf ``List.nil then return mkApp2 (Lean.mkConst ``Classicism.Meta.RTy.arr) x r
        else return mkApp2 (Lean.mkConst ``Classicism.Meta.RTy.arrs) l r
      | _ => return mkApp2 (Lean.mkConst ``Classicism.Meta.RTy.arrs) l r
    | _ => pure (mkApp2 (Lean.mkConst ``Classicism.Meta.RTy.vec) θ a)
end

/-- The element of the one-element list a type expression translates to, if it is one. -/
def singleOf (θ : Expr) (ls : Array Expr) (a : Expr) : MetaM (Option Expr) := do
  let r ← vecTyExpr θ ls a
  match r.getAppFnArgs with
  | (``List.cons, #[_, x, tl]) => pure (if tl.isAppOf ``List.nil then some x else none)
  | _ => pure none

/-! Where a closed parameter passes through a vectorization, its translation stands
unreduced inside the sentence, `RTy.vec θ ρ` or `Ty.vec θ τ`, with whatever assignment
`θ` the vectorization had. Two vectorizations of the same sentence along assignments
that agree on its type variables differ only there. Reduced with those translations kept
folded, the two sentences are the same function of them, so each translation can be
rewritten away by the parameter's closedness (`RTy.vec_closed`, `Ty.vec_closed`), and the
two shown equal. -/

/-- Reduce a term to normal form, keeping folded a translation stuck at a free variable,
an assignment, and proofs. -/
partial def reduceToRemnants (e : Expr) : MetaM Expr := do
  if ← isProof e then return e
  if e.isAppOf ``Classicism.Meta.Assign.ofList then return e
  let e' ← whnf e
  if e'.isAppOfArity ``Classicism.Meta.RTy.vec 2 || e'.isAppOfArity ``Classicism.Meta.Ty.vec 2 then
    return e'
  match e' with
  | .app f a => return mkApp (← reduceToRemnants f) (← reduceToRemnants a)
  | .lam n t b bi =>
    withLocalDecl n bi (← reduceToRemnants t) fun x => do
      mkLambdaFVars #[x] (← reduceToRemnants (b.instantiate1 x))
  | .forallE n t b bi =>
    withLocalDecl n bi (← reduceToRemnants t) fun x => do
      mkForallFVars #[x] (← reduceToRemnants (b.instantiate1 x))
  | _ => return e'

/-- The translations in `e` of the variables with a closedness proof in `hyps`, each once,
with what each is and the proof that it is: `RTy.vec θ ρ = ρ`, `Ty.vec θ τ = [τ]`. -/
def remnantsIn (hyps : Array (Expr × Expr)) (e : Expr) : MetaM (Array (Expr × Expr × Expr)) := do
  let found ← IO.mkRef (#[] : Array Expr)
  e.forEach fun sub => do
    if sub.isAppOfArity ``Classicism.Meta.RTy.vec 2 || sub.isAppOfArity ``Classicism.Meta.Ty.vec 2 then
      if hyps.any (·.1 == sub.appArg!) then
        unless (← found.get).contains sub do found.modify (·.push sub)
  (← found.get).mapM fun sub => do
    let x := sub.appArg!
    let θ := sub.appFn!.appArg!
    let some (_, h) := hyps.find? (·.1 == x) | throwError "remnants: internal"
    if sub.isAppOf ``Classicism.Meta.RTy.vec then
      return (sub, x, ← mkAppM ``Classicism.Meta.RTy.vec_closed #[θ, h])
    else
      return (sub, ← mkListLit (Lean.mkConst ``Classicism.Meta.Ty) [x],
        ← mkAppM ``Classicism.Meta.Ty.vec_closed #[θ, h])

/-- `e` with each closed parameter's translation replaced by what it is, and the proof
that the result is `e`. -/
def removeRemnants (hyps : Array (Expr × Expr)) (e : Expr) : MetaM (Expr × Expr) := do
  let r ← reduceToRemnants e
  let rems ← remnantsIn hyps r
  if rems.isEmpty then
    return (r, ← mkExpectedTypeHint (← mkEqRefl e) (← mkEq e r))
  let tys ← rems.mapM fun (rem, _, _) => inferType rem
  withLocalDeclsDND (tys.map fun t => (`y, t)) fun ys => do
    let mut body := r
    for ((rem, _, _), y) in rems.zip ys do
      body := (← kabstract body rem).instantiate1 y
    let H ← mkLambdaFVars ys body
    let mut pf ← mkEqRefl H
    for (_, _, h) in rems do
      pf ← mkCongr pf h
    let e' := (mkAppN H (rems.map (·.2.1))).headBeta
    return (e', ← mkExpectedTypeHint pf (← mkEq e e'))

/-- A proof that `A = B`, two vectorized sentences the same up to the translations of
closed parameters (`hyps`, their closedness). Both are compared in normal form: the
unifier, comparing them as they stand, can lose itself unfolding the vectorization. -/
def remnantEq (hyps : Array (Expr × Expr)) (A B : Expr) : MetaM Expr := do
  let (A', pA) ← removeRemnants hyps A
  let (B', pB) ← removeRemnants hyps B
  unless ← isDefEq A' B' do
    throwError "the sentences{indentExpr A}\nand{indentExpr B}\nare not the same up to closed types"
  mkEqTrans pA (← mkEqSymm pB)

/-- `classicism_vec_eq` closes a goal `A = B` between two vectorized sentences the same
up to the translations of closed parameters, using the closedness hypotheses in the
context. -/
syntax (name := classicismVecEq) "classicism_vec_eq" : tactic

open Lean.Elab.Tactic in
@[tactic classicismVecEq] def evalVecEq : Tactic := fun _ => withMainContext do
  let goal ← getMainGoal
  let some (_, A, B) := (← instantiateMVars (← goal.getType)).eq?
    | throwError "classicism_vec_eq: the goal is not an equation"
  let mut hyps : Array (Expr × Expr) := #[]
  for d in ← getLCtx do
    unless d.isImplementationDetail do
      let t ← whnfR (← instantiateMVars d.type)
      if t.isAppOfArity ``Classicism.Meta.RTy.Closed 1 || t.isAppOfArity ``Classicism.Meta.Ty.Closed 1 then
        hyps := hyps.push (t.appArg!, d.toExpr)
  goal.assign (← remnantEq hyps A B)
  replaceMainGoal []

/-- Is `a` the type variable `var 0`? -/
def isTyVar0 (a : Expr) : Bool :=
  a.isAppOfArity ``Classicism.Meta.Ty.var 1 &&
    (a.appArg!.nat? == some 0 || a.appArg!.rawNatLit? == some 0)

/-- Does `a` mention the type variable `var 0`? -/
def hasTyVar0 (a : Expr) : Bool := (a.find? isTyVar0).isSome

/-- A type expression with each translation of a variable, `RTy.vec θ ρ`, replaced by the
variable: what it is when the variable is closed. -/
def cleanRemnants (e : Expr) : Expr :=
  e.replace fun sub =>
    if sub.isAppOfArity ``Classicism.Meta.RTy.vec 2 && sub.appArg!.isFVar then some sub.appArg!
    else none

/-- The form the instance `P.quoted as` takes under vectorization along `θ`, and whether
it is a list form. -/
def instanceForm (θ : Expr) (ls : Array Expr) (P : Name) (as : Array Expr) : MetaM (Expr × Bool) := do
  let σs := ls[0]!
  let kinds ← paramKinds P
  let i₀? := kinds.findIdx? (fun b => b)
  let hasList := (← getEnv).contains (P ++ `listQuoted)
  let isList := match i₀? with
    | some i₀ => isTyVar0 as[i₀]! && hasList
    | none => false
  let mut args : Array Expr := #[]
  for j in List.range kinds.size do
    let a := as[j]!
    if isList && some j == i₀? then
      args := args.push σs
    else if kinds[j]! then
      let some a' ← singleOf θ ls a
        | throwError "list rule: the argument{indentExpr a}\nof {P} does not translate to one type"
      args := args.push (cleanRemnants a')
    else if isList then
      -- the list form's other arguments are not vectorized: the list's own variable has
      -- no place in them
      if hasTyVar0 a then
        throwError "list rule: the relational argument{indentExpr a}\nof {P}'s list form mentions the list's type variable"
      args := args.push (cleanRemnants (← vecRTyExpr θ ls a))
    else
      args := args.push (cleanRemnants (← vecRTyExpr θ ls a))
  let f := Lean.mkConst (P ++ if isList then `listQuoted else `quoted)
  return (mkAppN f args, isList)

/-- What the list rule of a record records for its list entailment. -/
structure ListRuleInfo where
  kinds : Array Bool
  i₀ : Nat
  /-- The premises' principles and whether each is a list form. -/
  premises : Array (Name × Bool)
  conclusion : Name
  conclusionIsList : Bool

/-- Declare `foo.listRule`, if the record has a Ty-parameter. -/
def declareListRule (foo : Name) : TermElabM (Option ListRuleInfo) := do
  let info ← getConstInfo foo
  let (ps, q) ← recordShape info.type
  let dty ← inferType (Lean.mkConst (foo ++ `derivable))
  let kinds ← forallTelescope dty fun tvs _ => tvs.mapM fun tv => do
    pure ((← whnf (← inferType tv)).isConstOf ``Classicism.Meta.Ty)
  let some i₀ := kinds.findIdx? (fun b => b) | return none
  let binders ← listBinders kinds i₀
  let others := (List.range kinds.size).filter (· != i₀)
  let axiomsC := mkApp (Lean.mkConst ``Classicism.Meta.C.axioms) (Lean.mkConst ``Classicism.Meta.Signature.pure)
  let nil := mkApp (Lean.mkConst ``List.nil [Level.zero]) Translate.tyE
  let (stmt, proof, forms, qform) ← withLocalDeclsDND binders fun xs => do
    let hbinders ← others.toArray.mapM fun j => do
      pure (Name.mkSimple s!"h{j}",
        ← mkAppM (if kinds[j]! then ``Classicism.Meta.Ty.Closed else ``Classicism.Meta.RTy.Closed) #[xs[j]!])
    withLocalDeclsDND hbinders fun hs => do
      let θ ← listAssign kinds i₀ xs
      let hc := mkApp (Lean.mkConst ``Classicism.Meta.Signature.pure_vecFixed) θ
      let tvs := (List.range kinds.size).toArray.map fun j =>
        if kinds[j]! then mkApp (Lean.mkConst ``Classicism.Meta.Ty.var) (mkNatLit (tyVarIndex kinds j))
        else xs[j]!
      let (_, D, pargs, cargs) ← ruleAt foo tvs
      let d' ← mkAppM ``Classicism.Meta.C.Theorem.vec #[θ, hc, D]
      let ls ← listEntries kinds i₀ xs
      let mut forms : Array (Expr × Bool) := #[]
      for (p, as) in ps.zip pargs.toList do
        forms := forms.push (← instanceForm θ ls p as)
      let qform ← instanceForm θ ls q cargs
      -- each instance of the vectorized derivation's statement is its form, up to the
      -- closed parameters' translations
      let hyps := (others.toArray.zip hs).map fun (j, h) => (xs[j]!, h)
      let insts := (ps.zip pargs.toList).map (fun (p, as) => mkAppN (Lean.mkConst (p ++ `quoted)) as)
        ++ [mkAppN (Lean.mkConst (q ++ `quoted)) cargs]
      let targets := forms.toList.map (·.1) ++ [qform.1]
      let mut eqs : Array Expr := #[]
      for (inst, tgt) in insts.zip targets do
        let V ← mkAppM ``Classicism.Meta.Term.vec1 #[θ, hc, inst]
        try
          eqs := eqs.push (← remnantEq hyps V tgt)
        catch _ =>
          throwError "list rule: the vectorized instance{indentExpr inst}\nis not{indentExpr tgt}"
      -- the statement, by congruence through the implications
      let sentenceTy := mkApp (Lean.mkConst ``Classicism.Meta.Sentence) (Lean.mkConst ``Classicism.Meta.Signature.pure)
      let impF ← withLocalDeclD `p sentenceTy fun p =>
        withLocalDeclD `q sentenceTy fun q' => do mkLambdaFVars #[p, q'] (Translate.impE nil p q')
      let mut S := targets.getLast!
      let mut eqS := eqs.back!
      for (tgt, e) in (targets.dropLast.zip eqs.toList.dropLast).reverse do
        eqS ← mkCongr (← mkCongrArg impF e) eqS
        S := Translate.impE nil tgt S
      let final := S
      let thmOf (x : Expr) : MetaM Expr := mkAppM ``Classicism.Meta.Theorem #[axiomsC, x]
      let pf ← mkEqMP (← mkCongrArg (← mkAppM ``Classicism.Meta.Theorem #[axiomsC]) eqS) d'
      let stmt ← mkForallFVars (xs ++ hs) (← thmOf final)
      pure (stmt, ← mkLambdaFVars (xs ++ hs) pf, forms, qform)
  let proof ← instantiateMVars proof
  let tv : TheoremVal := { name := foo ++ `listRule, levelParams := [], type := stmt, value := proof }
  withOptions (Elab.async.set · false) do addDecl (.thmDecl tv)
  return some { kinds, i₀, premises := (ps.zip forms.toList).toArray.map fun (p, f) => (p, f.2),
                conclusion := q, conclusionIsList := qform.2 }

/-- What `foo.listRule` records for its list entailment, read off its statement, for a
list rule declared earlier. -/
def listRuleInfo (foo : Name) : TermElabM ListRuleInfo := do
  let (ps, q) ← recordShape (← getConstInfo foo).type
  let dty ← inferType (Lean.mkConst (foo ++ `derivable))
  let kinds ← forallTelescope dty fun tvs _ => tvs.mapM fun tv => do
    pure ((← whnf (← inferType tv)).isConstOf ``Classicism.Meta.Ty)
  let some i₀ := kinds.findIdx? (fun b => b) | throwError "list rule: {foo} has no Ty-parameter"
  forallTelescope (← inferType (Lean.mkConst (foo ++ `listRule))) fun _ body => do
    let some (_, S) := derivableParts? (← whnf body) | throwError "list rule: internal"
    let mut Y := S
    let mut premises : Array (Name × Bool) := #[]
    for p in ps do
      let some X ← impPremise? Y | throwError "list rule: not an implication"
      premises := premises.push (p, (← instantiateMVars X).isAppOf (p ++ `listQuoted))
      let some rest := impRest? (← whnfR Y) | throwError "list rule: not an implication"
      Y := rest
    return { kinds, i₀, premises, conclusion := q,
             conclusionIsList := (← instantiateMVars Y).isAppOf (q ++ `listQuoted) }

/-- Declare `foo.listEntails`, from `foo.listRule`: the premises' list schemas (a restricted
instance's schema where the instance is restricted) entail the conclusion's list schema,
or the family of the conclusion's instances where it is not `Q`'s list form at the
record's own parameters. -/
def declareListEntails (foo : Name) (info : ListRuleInfo) : TermElabM Unit := do
  let pureSig := Lean.mkConst ``Classicism.Meta.Signature.pure
  let sentenceTy := mkApp (Lean.mkConst ``Classicism.Meta.Sentence) pureSig
  let axiomsC := mkApp (Lean.mkConst ``Classicism.Meta.C.axioms) pureSig
  let sets := info.premises.toList.map fun (p, isList) =>
    Lean.mkConst (p ++ if isList then `listSchema else `schema)
  let Ps ← if sets.isEmpty then pure (mkApp (Lean.mkConst ``Classicism.Meta.AxiomSet.empty) pureSig)
    else unionOf sets
  let ruleName := foo ++ `listRule
  let ruleTy ← inferType (Lean.mkConst ruleName)
  let nParams := info.kinds.size
  -- the conclusion set
  let Qs ← forallTelescope ruleTy fun ys body => do
    let xs := ys[:nParams].toArray
    let some (_, S) := derivableParts? (← whnf body) | throwError "list entails: internal"
    let mut Y := S
    for _ in info.premises do
      let some rest := impRest? (← whnfR Y) | throwError "list entails: not an implication"
      Y := rest
    let qls := info.conclusion ++ `listQuoted
    if info.conclusionIsList && Y.isAppOf qls && Y.getAppArgs == xs then
      pure (Lean.mkConst (info.conclusion ++ `listSchema))
    else
      withLocalDeclD `a sentenceTy fun a => do
        let mut body ← mkEq a Y
        for x in xs.reverse do
          body ← mkAppM ``And #[← closedProp x, body]
        for x in xs.reverse do
          body ← mkAppM ``Exists #[← mkLambdaFVars #[x] body]
        mkLambdaFVars #[a] body
  let stmt ← mkAppM ``Classicism.Meta.AxiomSet.Entails #[Ps, Qs]
  let target ← withC Ps
  let proof ← withLocalDeclD `a sentenceTy fun a => do
    withLocalDeclD `ha (← whnfR (mkApp Qs a)) fun ha => do
      let goal ← mkAppM ``Classicism.Meta.Theorem #[target, a]
      let body ← elimSchemaMem ha goal fun ys hyps heq => do
        let others := (List.range nParams).filter (· != info.i₀)
        let hrel ← others.toArray.mapM fun j => closedProof hyps ys[j]!
        let rule := mkAppN (Lean.mkConst ruleName) (ys ++ hrel)
        let lift ← withLocalDeclD `b sentenceTy fun b =>
          withLocalDeclD `h (mkApp axiomsC b) fun h => do
            mkLambdaFVars #[b, h] (← mkAppOptM ``Or.inl #[mkApp axiomsC b, mkApp Ps b, h])
        let mut cur ← mkAppM ``Classicism.Meta.Derivable.mono #[lift, rule]
        for (i, (p, isList)) in info.premises.toList.zipIdx.map (fun (x, i) => (i, x)) do
          let cty ← whnf (← inferType cur)
          let some (_, st) := derivableParts? cty | throwError "list entails: internal (premise)"
          let some X ← impPremise? st | throwError "list entails: not an implication"
          let X ← instantiateMVars X
          let q := Lean.mkConst (p ++ if isList then `listQuoted else `quoted)
          let mem ← schemaMemBuild hyps X X.getAppArgs q
          let memU ← unionMem sets i X mem
          let ax ← mkAppOptM ``Classicism.Meta.Derivable.axiom
            #[pureSig, target, X, ← mkAppOptM ``Or.inr #[mkApp axiomsC X, mkApp Ps X, memU]]
          cur ← mkAppM ``Classicism.Meta.Derivable.impE #[cur, ax]
        let motive ← withLocalDeclD `s sentenceTy fun s => do
          mkLambdaFVars #[s] (← mkAppM ``Classicism.Meta.Theorem #[target, s])
        mkAppM ``Eq.mpr #[← mkAppM ``congrArg #[motive, heq], cur]
      mkLambdaFVars #[a, ha] body
  let proof ← instantiateMVars proof
  let tv : TheoremVal := { name := foo ++ `listEntails, levelParams := [], type := stmt, value := proof }
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

/-- Declare `foo.listRule` when `foo` has a Ty-parameter, and report it, or why not. -/
def certifyListRule (n : Name) : CommandElabM Unit := do
  try
    if (← liftTermElabM (declareListRule n)).isSome then
      logInfo m!"{n} ⟶ {n ++ `listRule} : {(← getConstInfo (n ++ `listRule)).type}"
  catch ex =>
    logInfo m!"{n}: no list rule — {ex.toMessageData}"

/-- `#classicism_certify foo …`: the whole chain for a theorem `foo : P₁ … → … → Q …` of
the shallow layer, at the point where it is stated. It makes schemas of the principles it
mentions that have none yet, derives `foo` in the object language (`foo.derivable`), and
declares the rule `foo.rule`, and, when `foo` has a Ty-parameter, its list form
`foo.listRule`; each step is skipped when its declaration already exists. The report gives
the rule and the axioms it rests on. -/
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
      certifyListRule n
    catch ex =>
      logError m!"{n}: not certified — {ex.toMessageData}"

/-- `#classicism_entails foo …`: each record theorem `foo : P₁ … → … → Q …` with a derivation
becomes `foo.entails : P₁.schema ∪ … ⟹ Q.schema`, and, when `foo` has a Ty-parameter,
`foo.listEntails`, from its list rule (declared here if `#classicism_certify` has not). -/
syntax (name := classicismEntails) "#classicism_entails " ident+ : command

@[command_elab classicismEntails] def elabEntails : CommandElab := fun stx => do
  for id in stx[1].getArgs do
    let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
    try
      liftTermElabM (declareEntails n)
      logInfo m!"{n} ⟶ {n ++ `entails} : {(← getConstInfo (n ++ `entails)).type}"
    catch ex =>
      logError m!"{n}: no entailment — {ex.toMessageData}"
    try
      let info? ← liftTermElabM do
        if (← getEnv).contains (n ++ `listRule) then pure (some (← listRuleInfo n))
        else declareListRule n
      if let some info := info? then
        liftTermElabM (declareListEntails n info)
        logInfo m!"{n} ⟶ {n ++ `listEntails} : {(← getConstInfo (n ++ `listEntails)).type}"
    catch ex =>
      logInfo m!"{n}: no list entailment — {ex.toMessageData}"

/-- `#classicism_entails_audit Mod …`: for every theorem `foo` of the module with a strict twin
`foo.strict`, derive it if `foo.strict.derivable` does not exist, then declare
`foo.entails`, and, for a record with a Ty-parameter, `foo.listRule` and `foo.listEntails`;
report what was certified and what was not, and why. -/
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
    let mut withTy : Nat := 0
    let mut listOk : Nat := 0
    let mut listFailures : Array MessageData := #[]
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
      -- the list form, for a record with a Ty-parameter
      if (← getEnv).contains (n ++ `derivable) then
        try
          if let some info ← liftTermElabM (declareListRule n) then
            withTy := withTy + 1
            liftTermElabM (declareListEntails n info)
            listOk := listOk + 1
            lines := lines.push s!"{n} ✓ list form : {← liftTermElabM do
              pure (toString (← Meta.ppExpr (← getConstInfo (n ++ `listEntails)).type))}"
        catch ex =>
          withTy := withTy + 1
          listFailures := listFailures.push m!"{n}: no list form — {ex.toMessageData}"
    logInfo m!"{modId.getId}: {ok} of {names.size} record theorems certified as entailments; \
{skipped.size} helper lemmas skipped\n{MessageData.joinSep failures.toList "\n"}\n\
{"\n".intercalate lines.toList}"
    if withTy > 0 then
      logInfo m!"{modId.getId}: {listOk} of {withTy} record theorems with a Ty-parameter \
certified in list form\n{MessageData.joinSep listFailures.toList "\n"}"

end Classicism.Meta
