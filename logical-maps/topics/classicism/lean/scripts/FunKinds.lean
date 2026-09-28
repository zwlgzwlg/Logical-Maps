import Lean
open Lean Elab Meta

/-! For each `fun` written in a source file, whether the elaborated term is a proof (its type
is a proposition) or a term of a type in `Type`. Prints one line per `fun`:
`<kind> <byte offset of fun> <byte offset of =>/↦>` with kind `proof`, `term` or `mixed`.

It is the check behind the shallow layer's convention (`HANDOFF.md`, §3): `λ x ↦ …` for a
term of a type in `Type`, `fun h => …` for a proof. Run from `Cian/`:

    lake env lean --run scripts/FunKinds.lean Classicism/Results/Records.lean Classicism.Results.Records

Not part of the library build. -/

unsafe def main (args : List String) : IO UInt32 := do
  let file := args[0]!
  let modName := args[1]!.toName
  initSearchPath (← findSysroot)
  enableInitializersExecution
  let input ← IO.FS.readFile file
  let inputCtx := Parser.mkInputContext input file
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, messages) ← processHeader header {} messages inputCtx (mainModule := modName)
  for m in messages.toList do IO.eprintln s!"header: {← m.toString}"
  let cmdState := { Command.mkState env messages {} with infoState := { enabled := true } }
  let s ← IO.processCommands inputCtx parserState cmdState
  for m in s.commandState.messages.toList do
    if m.severity == .error then
      IO.eprintln s!"error: {← m.toString}"
  let mut found : Std.HashMap Nat (Nat × Array Bool) := {}
  for t in s.commandState.infoState.trees do
    let r ← t.foldInfoM (init := ([] : List (Nat × Nat × Bool))) fun ctx info acc => do
      match info with
      | .ofTermInfo ti =>
        let stx := ti.stx
        if stx.getKind == ``Lean.Parser.Term.fun && stx[1].getKind == ``Lean.Parser.Term.basicFun then
          match stx.getPos? (canonicalOnly := true), stx[1][2].getPos? (canonicalOnly := true) with
          | some p, some q =>
            let isP ← ctx.runMetaM ti.lctx do
              let e ← instantiateMVars ti.expr
              let ty ← instantiateMVars (← inferType e)
              isProp ty
            return (p.byteIdx, q.byteIdx, isP) :: acc
          | _, _ => return acc
        else return acc
      | _ => return acc
    for (p, q, b) in r do
      let (q0, bs) := found.getD p (q, #[])
      found := found.insert p (q0, bs.push b)
  for (p, (q, bs)) in found.toList do
    let kind := if bs.all id then "proof" else if bs.all (! ·) then "term" else "mixed"
    IO.println s!"{kind} {p} {q}"
  return 0
