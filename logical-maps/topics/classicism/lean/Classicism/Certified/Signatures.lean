import Classicism.Certified.Schemas
import Classicism.Syntax.SentenceSchemas
import Classicism.Syntax.Pure
import Classicism.Syntax.Conservativity
import Classicism.Syntax.WitnessedPossibility
import Classicism.Syntax.PossibilityPlus
import Classicism.Syntax.Infinity
import Classicism.Syntax.StrongPossibility
import Classicism.Syntax.OrdinaryComprehension

/-!
# Every principle at every signature

The convention (Cian, 2 October): each of the map's principles is a schema at every
signature `Σ`, that is, a function from signatures to schemas.

* A principle indexed by types: `P.X.schemaIn`, its instances read in `Σ`'s language,
  `AxiomSet.ofPure P.X.schema`; `P.X.listSchemaIn` likewise for a list form. Declared here
  for every principle by `#classicism_schema_in`.
* A sentence schema relative to a signature: `noContingency Σ`, `signatureB Σ`, and
  Distinctness and Possibility relative to `C`, `distinctnessC Σ` and `possibilityC Σ`.
* Its pure version: `pureVersion S`, the schema `S` at the pure signature read in `Σ`'s
  language. No Pure Contingency is `pureVersion noContingency`, Pure B is
  `pureVersion signatureB`, and Distinctness and Possibility (pure) are
  `pureVersion distinctnessC` and `pureVersion possibilityC`.

A pure principle throws `Σ` away, but its sentences are still read in `Σ`'s language: a
sentence's type records its signature, and `ofPure` is the inclusion of the pure language
in every other. A result about such functions holds at every `Σ`; that is the `∀ Sig` with
which the map's statements open (`Statements.lean`).

The principles' own declarations stay at the pure signature (`P.X.quoted`, `P.X.schema`),
and so do the proofs about them: a pure derivation is one in every signature
(`Derivable.ofPure`), so a pure entailment holds at every `Σ` (`Map.lean`). The converse
direction, that what is consistent in the pure language stays so with constants added, is
the conservativity of `C(Σ)` over `C` (`Syntax/Conservativity.lean`), for a signature of the
paper's language, whose constants have closed types (`Signature.Closed`); the map's
statements range over those. It gives the inclusions below between a schema relative to a
signature and its pure version.
-/

open Lean Elab Command in
/-- `#classicism_schema_in`: declare `P.X.schemaIn` (and `P.X.listSchemaIn`) for every
principle `P.X` with a schema (a list form). -/
elab "#classicism_schema_in" : command => do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun acc n _ =>
    match n with
    | .str p s =>
      if (`Classicism.P).isPrefixOf p && (s == "schema" || s == "listSchema") then acc.push n
      else acc
    | _ => acc
  for n in names.qsort (·.toString < ·.toString) do
    let .str p s := n | continue
    let id := mkIdent (Name.str p (s ++ "In"))
    let src := mkIdent n
    elabCommand (← `(command|
      /-- The schema at every signature: its sentences, read in the signature's language. -/
      @[reducible] def $id {Sig : Classicism.Meta.Signature} : Classicism.Meta.AxiomSet Sig :=
        Classicism.Meta.AxiomSet.ofPure $src))
  logInfo m!"{names.size} schemas declared at every signature"

#classicism_schema_in

namespace Classicism.Meta.AxiomSet

/-- The pure version of a schema given at every signature: the schema at the pure
signature, read in the signature's language. -/
@[reducible] def pureVersion {Sig : Signature} (S : (Sig' : Signature) → AxiomSet Sig') :
    AxiomSet Sig :=
  AxiomSet.ofPure (S Signature.pure)

/-- Distinctness relative to `C`, at a signature: the map's Distinctness. -/
@[reducible] def distinctnessC (Sig : Signature) : AxiomSet Sig := distinctness empty

/-- Possibility relative to `C`, at a signature: the map's Possibility. -/
@[reducible] def possibilityC (Sig : Signature) : AxiomSet Sig := possibility empty

/-- At the pure signature every sentence is pure, so No Pure Contingency is No Contingency
there. -/
theorem npc_pure_eq : npc Signature.pure = noContingency Signature.pure :=
  funext fun _ => propext ⟨fun ⟨p, _, h⟩ => ⟨p, h⟩, fun ⟨p, h⟩ => ⟨p, Term.pure_of_pureSig p, h⟩⟩

/-- Likewise B for pure sentences and B for the signature. -/
theorem pureB_pure_eq : pureB Signature.pure = signatureB Signature.pure :=
  funext fun _ => propext ⟨fun ⟨p, _, h⟩ => ⟨p, h⟩, fun ⟨p, h⟩ => ⟨p, Term.pure_of_pureSig p, h⟩⟩

/-- No Pure Contingency, as the pure version of No Contingency, is `npc` of the pure
signature read in the signature: the form in which `Results/SentenceSchemas/` proves it. -/
theorem pureVersion_noContingency {Sig : Signature} :
    pureVersion (Sig := Sig) noContingency = AxiomSet.ofPure (npc Signature.pure) := by
  rw [npc_pure_eq]

/-- Pure B, as the pure version of Signature B, likewise. -/
theorem pureVersion_signatureB {Sig : Signature} :
    pureVersion (Sig := Sig) signatureB = AxiomSet.ofPure (pureB Signature.pure) := by
  rw [pureB_pure_eq]

/-- No Pure Contingency, either way: `npc Σ` (`P → □P` for each pure sentence of `Σ`'s
language) is the pure version of No Contingency. -/
theorem npc_eq_pureVersion {Sig : Signature} : npc Sig = pureVersion noContingency := by
  rw [pureVersion_noContingency, npc_eq_ofPure]

/-- Pure B, either way. -/
theorem pureB_eq_pureVersion {Sig : Signature} : pureB Sig = pureVersion signatureB := by
  rw [pureVersion_signatureB, pureB_eq_ofPure]

/-- Possibility (pure) is part of Possibility for a closed signature: what is consistent
with `C` is consistent with `C(Σ)`. -/
theorem pureVersion_possibilityC_subset {Sig : Signature} (hS : Sig.Closed) :
    pureVersion (Sig := Sig) possibilityC ⊆ possibilityC Sig :=
  ofPure_possibility_subset hS

/-- Distinctness (pure) is part of Distinctness for a closed signature: what `C` does not
prove, `C(Σ)` does not prove. -/
theorem pureVersion_distinctnessC_subset {Sig : Signature} (hS : Sig.Closed) :
    pureVersion (Sig := Sig) distinctnessC ⊆ distinctnessC Sig :=
  ofPure_distinctness_subset hS

end Classicism.Meta.AxiomSet
