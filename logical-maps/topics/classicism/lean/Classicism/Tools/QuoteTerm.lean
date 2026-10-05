import Classicism.Tools.Quote
import Classicism.Semantics.Denotation

/-!
# Quotation of closed terms

`#classicism_quote_term foo`: the companion of `#classicism_quote` for a closed definition at a
type of the object language rather than a statement. It declares `foo.term`, the quoted term,
and `foo.reflect`, that the term denotes `foo` over the domain `e`, by `rfl`.
-/

open Lean Meta Elab Term Command

namespace Classicism.Meta.Quote

/-- `#classicism_quote_term foo`: quote the value of a closed definition `foo : T` at a type of
the object language, declaring `foo.term : Term Signature.pure [] ⌜T⌝` and `foo.reflect`, that
its denotation over the domain `e` is `foo`, by `rfl`. -/
elab "#classicism_quote_term " ids:ident+ : command => do
  for id in ids do
    let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
    liftTermElabM do
      let val := Lean.mkConst n
      let ty ← inferType val
      let σ ← (quoteTy ty).run {}
      let stx ← (quoteTerm ((← unfoldDefinition? val).getD val)).run {}
      let pureSig := Lean.mkConst ``Classicism.Meta.Signature.pure
      let ctx := mkApp (Lean.mkConst ``List.nil [Level.zero]) (Lean.mkConst ``Classicism.Meta.Ty)
      let termTy := mkApp3 (Lean.mkConst ``Classicism.Meta.Term) pureSig ctx σ
      let t ← elabTermEnsuringType stx (some termTy)
      synthesizeSyntheticMVarsNoPostponing
      let t ← instantiateMVars t
      if t.hasMVar then throwError "quote: the term has unresolved holes:{indentExpr t}"
      let I := mkApp (Lean.mkConst ``Classicism.Meta.Interp.ofDomain) (Lean.mkConst ``Classicism.e)
      let lhs ← mkAppM ``Classicism.Meta.Term.denote #[I, t,
        mkApp (Lean.mkConst ``Classicism.Meta.Env.nil) (Lean.mkConst ``Classicism.e)]
      let eq ← mkEq lhs val
      let pf ← if ← isDefEq lhs val then mkEqRefl lhs else
        -- `→` is quoted as `¬p ∨ q`: rewrite back, as `#classicism_quote` does
        let defs ← reflectDefs val
        let lemmas ← (reflectSimpSet ++ defs).mapM fun n =>
          `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
        let stx ← `(by simp only [$lemmas,*]; try rfl)
        let v ← Term.withoutErrToSorry do
          let v ← elabTermEnsuringType stx (some eq)
          synthesizeSyntheticMVarsNoPostponing
          instantiateMVars v
        if v.hasSorry then throwError "quote: {n} does not reflect"
        pure v
      let tName := n ++ Name.mkSimple "term"
      let rName := n ++ Name.mkSimple "reflect"
      let dv : DefinitionVal := { name := tName, levelParams := [], type := termTy, value := t, hints := .abbrev, safety := .safe }
      let tv : TheoremVal := { name := rName, levelParams := [], type := eq, value := pf }
      withOptions (Elab.async.set · false) do
        addDecl (.defnDecl dv)
        addDecl (.thmDecl tv)
      logInfo m!"{n} ⟶ {tName}, reflects ✓"

end Classicism.Meta.Quote
