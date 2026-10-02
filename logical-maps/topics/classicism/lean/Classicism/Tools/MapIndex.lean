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

/-- The proofs of the result a certificate proves, in the order a reader wants them. -/
def proofsOf (cert : Name) : CommandElabM (Array Name) := do
  let env ← getEnv
  let id := cert.getString!
  let byName := [`Classicism.Proofs ++ id.toName, `Classicism ++ id.toName,
    `Classicism.Meta ++ id.toName].filter env.contains
  let some info := env.find? cert | return byName.toArray
  let value := match info with
    | .thmInfo t => some t.value
    | _ => info.value?
  let cited := (value.map (·.getUsedConstants) |>.getD #[]).toList.map (base env)
  let inResults := cited.filter fun c =>
    (`Classicism.Results).isPrefixOf (moduleOf env c) && env.contains c
  let mut out : Array Name := #[]
  for c in byName ++ inResults do
    unless out.contains c do out := out.push c
  return out

/-- `#classicism_map_index "file.json"`: write the index of the certificates in
`Classicism.Map`. -/
elab "#classicism_map_index " path:str : command => do
  let env ← getEnv
  let certs := env.constants.fold (init := #[]) fun acc n info =>
    match info with
    | .thmInfo _ => if (`Classicism.Map).isPrefixOf n && n.getPrefix == `Classicism.Map
        then acc.push n else acc
    | _ => acc
  let certs := certs.qsort (·.toString < ·.toString)
  let allowed := [`propext, `Classical.choice, `Quot.sound]
  let mut entries : Array (String × Json) := #[]
  let mut outside : Nat := 0
  for c in certs do
    let id := c.getString!.replace "_" "-"
    let axioms ← collectAxioms c
    unless axioms.all allowed.contains do outside := outside + 1
    let some loc ← location c | continue
    let loc := loc.setObjVal! "axioms" (toJson (axioms.map Name.toString))
    let mut proofs : Array Json := #[]
    for p in ← proofsOf c do
      if let some l ← location p then proofs := proofs.push l
    entries := entries.push (id, Json.mkObj [("certificate", loc), ("proofs", Json.arr proofs)])
  let json := Json.mkObj [("results", Json.mkObj entries.toList)]
  IO.FS.writeFile path.getString (json.pretty ++ "\n")
  logInfo m!"{certs.size} certificates indexed to {path.getString}; \
    {outside} rest on an axiom outside propext, Classical.choice, Quot.sound"

end Classicism.Tools.MapIndex
