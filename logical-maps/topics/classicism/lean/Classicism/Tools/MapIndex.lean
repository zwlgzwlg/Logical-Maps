import Lean

/-!
# The index of the map's certificates

`#classicism_map_index "file.json"`, run after `import Classicism.Map`, writes for each
certificate in the namespace `Classicism.Map` (one theorem per map result, named by its id)
where it is and what it rests on, and where the result's proofs are, so that the map can
link each result to the Lean a reader wants to see:

* `certificate`: the theorem, its file and lines, and the axioms it depends on (the map
  admits `propext`, `Classical.choice` and `Quot.sound`);
* `proofs`: the declarations that prove the result, each with its file and lines, found by
  the naming convention: `Classicism.Proofs.<id>` (the shallow proof in
  `Results/Records.lean`, at one argument type for a result at every arity),
  `Classicism.<id>` (a shallow core certified where it is composed, in
  `Results/Arity.lean`), `Classicism.Meta.<id>` (the metalogical proof), and then the theorems of `Classicism/Results/` that the
  certificate cites, `foo` for a cited `foo.entails`, `foo.derivable` and the like.

Files are relative to the Lean project's root. It is what `scripts/MapIndex.lean` runs,
outside the library build.
-/

namespace Classicism.Tools.MapIndex

open Lean Elab Command

/-- The module a declaration lives in. -/
def moduleOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => env.mainModule

/-- A module's source file, relative to the project root. -/
def fileOf (mod : Name) : String :=
  String.intercalate "/" (mod.components.map Name.toString) ++ ".lean"

/-- A declaration's file and lines, as JSON. -/
def location (n : Name) : CommandElabM (Option Json) := do
  let env ← getEnv
  unless env.contains n do return none
  let some r ← findDeclarationRanges? n | return none
  return some <| Json.mkObj [
    ("name", toJson n.toString),
    ("file", toJson (fileOf (moduleOf env n))),
    ("lines", toJson [r.range.pos.line, r.range.endPos.line])]

/-- The suffixes of the declarations the certification commands generate. -/
def generated : List String := ["entails", "listEntails", "derivable", "rule", "listRule"]

/-- The declaration a cited name stands for: `foo` for `foo.entails` and the like. -/
def base (env : Environment) (n : Name) : Name :=
  match n with
  | .str p s => if generated.contains s && env.contains p then p else n
  | _ => n

/-- The value of a definition or theorem. -/
def valueOf (env : Environment) (n : Name) : Option Expr :=
  match env.find? n with
  | some (.thmInfo t) => some t.value
  | some info => info.value?
  | none => none

/-- The proofs of the result (or the equivalence) a certificate proves, in the order a
reader wants them; `byName` for a result, whose id names its proofs too. -/
def proofsOf (cert : Name) (byName : Bool) : CommandElabM (Array Name) := do
  let env ← getEnv
  let id := cert.getString!
  let named := if byName then [`Classicism.Proofs ++ id.toName, `Classicism ++ id.toName,
    `Classicism.Meta ++ id.toName].filter env.contains else []
  let cited := ((valueOf env cert).map (·.getUsedConstants) |>.getD #[]).toList.map (base env)
  -- the proofs cited: in `Principles/` (a form's two directions, beside its definition) and
  -- in `Results/`
  let inResults := cited.filter fun c =>
    ((`Classicism.Principles).isPrefixOf (moduleOf env c) ||
      (`Classicism.Results).isPrefixOf (moduleOf env c)) && env.contains c
  let mut out : Array Name := #[]
  for c in named ++ inResults do
    unless out.contains c do out := out.push c
  return out

/-- The definitions of the forms a generated statement relates: `P.X` for each
`P.X.schemaIn` it mentions, and for each `P.X.listSchemaIn` the list form's definition by
vectorization, `P.X.listQuoted`. -/
def definitionsOf (stmt : Name) : CommandElabM (Array Name) := do
  let env ← getEnv
  let used := ((valueOf env stmt).map (·.getUsedConstants) |>.getD #[]).toList
  let mut out : Array Name := #[]
  for c in used do
    if let .str p s := c then
      let d := if s == "listSchemaIn" then p ++ `listQuoted else p
      if (s == "schemaIn" || s == "listSchemaIn") && env.contains d && !out.contains d then
        out := out.push d
  return out

/-- A certificate's entry: where it is and what it rests on, and where its proofs are. -/
def entryOf (c : Name) (byName : Bool) : CommandElabM (Option (Json × Bool)) := do
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let axioms ← collectAxioms c
  let some loc ← location c | return none
  let loc := loc.setObjVal! "axioms" (toJson (axioms.map Name.toString))
  let mut proofs : Array Json := #[]
  for p in ← proofsOf c byName do
    if let some l ← location p then proofs := proofs.push l
  return some (Json.mkObj [("certificate", loc), ("proofs", Json.arr proofs)],
    axioms.all allowed.contains)

/-- `#classicism_map_index "file.json"`: write the index of the certificates in
`Classicism.Map`: the results' (`Classicism.Map.<id>`) and the forms'
(`Classicism.Map.<principle id>.<form id>`), a form's entry also giving the definitions of
the two forms it relates. -/
elab "#classicism_map_index " path:str : command => do
  let env ← getEnv
  let thms := env.constants.fold (init := #[]) fun acc n info =>
    match info with
    | .thmInfo _ => if (`Classicism.Map).isPrefixOf n then acc.push n else acc
    | _ => acc
  let thms := thms.qsort (·.toString < ·.toString)
  let unhyphen (n : Name) := n.getString!.replace "_" "-"
  let mut results : Array (String × Json) := #[]
  let mut forms : Std.HashMap String (Array (String × Json)) := {}
  let mut outside : Nat := 0
  for c in thms do
    if c.getPrefix == `Classicism.Map then
      let some (e, ok) ← entryOf c true | continue
      unless ok do outside := outside + 1
      results := results.push (unhyphen c, e)
    else if c.getPrefix.getPrefix == `Classicism.Map then
      let some (e, ok) ← entryOf c false | continue
      unless ok do outside := outside + 1
      let stmt := `Classicism.Statements ++ c.getPrefix.getString!.toName ++ c.getString!.toName
      let mut defs : Array Json := #[]
      for d in ← definitionsOf stmt do
        if let some l ← location d then defs := defs.push l
      let principle := unhyphen c.getPrefix
      forms := forms.insert principle
        ((forms.getD principle #[]).push (unhyphen c, e.setObjVal! "definitions" (Json.arr defs)))
  let formsJson := Json.mkObj (forms.toList.map fun (p, fs) => (p, Json.mkObj fs.toList))
  let json := Json.mkObj [("results", Json.mkObj results.toList), ("forms", formsJson)]
  IO.FS.writeFile path.getString (json.pretty ++ "\n")
  logInfo m!"{results.size} result certificates and {forms.fold (fun n _ fs => n + fs.size) 0} \
    form certificates indexed to {path.getString}; {outside} rest on an axiom outside \
    propext, Classical.choice, Quot.sound"

end Classicism.Tools.MapIndex
