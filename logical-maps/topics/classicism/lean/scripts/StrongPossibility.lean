import Classicism.Map
import Lean.Util.FoldConsts

/-! Check that both public certificates reach the same two pure licences and
the unary twin reading. Run `lake env lean scripts/StrongPossibility.lean`. -/

open Lean

private def libraryDecl (env : Environment) (n : Name) : Bool :=
  match env.getModuleIdxFor? n with
  | some i => (`Classicism).isPrefixOf env.header.moduleNames[i.toNat]!
  | none => false

/-- Follow proof bodies throughout the library, including private helpers. -/
private partial def dependencies (env : Environment) : List Name → NameSet → NameSet
  | [], seen => seen
  | n :: rest, seen =>
    if seen.contains n then dependencies env rest seen
    else
      let body := (env.find? n).bind fun c => c.value? (allowOpaque := true)
      let next := body.map (fun e => e.getUsedConstants.toList.filter (libraryDecl env))
      dependencies env (next.getD [] ++ rest) (seen.insert n)

run_cmd
  let shared := [``Classicism.Meta.UnarySP.inconsistent_in_closed_signature,
    ``Classicism.Meta.UnarySP.inconsistent_of_permanent_licences,
    ``Classicism.Meta.UnarySP.pure_licence_of_finite,
    ``Classicism.Meta.UnarySP.permanent_licence,
    ``Classicism.Meta.UnarySP.guarded_permanent_licence,
    ``Classicism.Meta.UnarySP.guard_of_descriptors,
    ``Classicism.Proofs.UnarySP.reflect_permanent.derivableC,
    ``Classicism.Proofs.UnarySP.reflect_guarded.derivableC,
    ``Classicism.Proofs.UnarySP.russell_witness.derivableC,
    ``Classicism.Meta.StrongPossibility.UnaryCanonical.canonical_separation,
    ``Classicism.Meta.StrongPossibility.UnarySeparation.reads_term,
    ``Classicism.Meta.StrongPossibility.UnaryLayerReading.canFind_iff,
    ``Classicism.Meta.StrongPossibility.UnaryLayerReading.isCode_iff,
    ``Classicism.Meta.StrongPossibility.DoubleCover.twin_iff]
  for root in [``Classicism.Map.strong_possibility_r_inconsistent,
      ``Classicism.Map.strong_possibility_signature_r_inconsistent] do
    let seen := dependencies (← getEnv) [root] {}
    for required in shared do
      unless seen.contains required do
        throwError m!"{root} did not reach {required}"
    for retired in [`Classicism.Meta.ProxyDiagonal.Q,
        `Classicism.Meta.ProxyDiagonal.canonical_proxy_separation,
        `Classicism.Meta.ProxyDiagonal.predecessors,
        `Classicism.Meta.ProxyDiagonal.pure_from_predecessors,
        `Classicism.Meta.ProxyDiagonal.inconsistent_in_admitted_signature,
        `Classicism.Meta.StrongPossibilityLicences.pure_inconsistent,
        `Classicism.Meta.StrongPossibility.UnaryLayerReading.allUpper_fixed,
        `Classicism.Meta.UnarySP.pure_inconsistent_of_separation,
        `Classicism.Meta.UnarySP.inconsistent_of_guards] do
      if seen.contains retired then throwError m!"{root} reached {retired}"
    logInfo m!"{root} uses the unary twin reading and both pure permanence licences"

#print axioms Classicism.Map.strong_possibility_r_inconsistent
#print axioms Classicism.Map.strong_possibility_signature_r_inconsistent
