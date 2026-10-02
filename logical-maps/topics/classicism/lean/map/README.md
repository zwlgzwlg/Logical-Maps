# The Lean side of the map

A draft of how this project plugs into the Logical Map (`zwlgzwlg/Logical-Maps`,
`topics/classicism`), in the map's own terms. Nothing here changes the map; it is what
the map's YAML and build would carry once the project moves there, and the change to the
map's build script that it needs (`pmap.patch`).

## How the map certifies a result

The map already has a Lean mechanism (`scripts/pmap.py`, used by the Unbounded Utility
topic):

- each principle names a Lean term in `lean_def`;
- `pmap lean` writes `<lib>/Statements.lean`, one `Prop` per result, assembled from the
  result's premises and conclusion in the shape the topic declares under `lean:`;
- a result's `certificate.lean_ref` names a proof, and `pmap lean-check --update` marks the
  result `verified` only if that proof has the generated type and rests on no axiom beyond
  `propext`, `Classical.choice` and `Quot.sound`.

So the official certificate of a result is the declaration its `lean_ref` names, checked
against a statement the map writes itself.

## What is here

| file | what it is |
| --- | --- |
| `lean.yaml` | The fields the map would carry: `lean_lib` and `lean` (for `topic.yaml`), a `lean_def` for each of the 95 principles formalized here, each principle's `forms`, and a `lean_ref` for each of the 230 results certified. |
| `pmap.patch` | The proposed change to the map's build script and JSON schemas (below). |
| `generate.py` | Runs the map's own generator, with `pmap.patch` applied in memory, on a checkout of the map with these fields added, writing `Classicism/Statements.lean`; `--refs` fills `lean_ref` from `Classicism/Map.lean`, `--patch` rewrites `pmap.patch`. |
| `index.json` | For each certified result and form: its certificate (file, lines, axioms) and the declarations a reader wants, the proofs (file, lines), and for a form the definitions of both forms. Written by `scripts/MapIndex.lean`. |

and, in the library:

| file | what it is |
| --- | --- |
| `Classicism/Certified/Signatures.lean` | Each principle as a schema at every signature: `P.X.schemaIn`, `pureVersion`, `distinctnessC`, `possibilityC`. |
| `Classicism/Statements.lean` | The generated statements: 265 of the 270 results (those whose principles all have a `lean_def`), 35 models, 22 forms. Not edited by hand. |
| `Classicism/Map.lean` | One certificate per result proved, named by its id, and per form, named `<principle>.<form>`, each of the generated type: the `lean_ref`s. Each is one line citing the proof. |
| `Classicism/Results/Forms.lean` | The shallow proofs of the equivalences between a principle's forms, a section per principle (the list forms' are in `Results/Lists.lean`). |
| `Classicism/Tools/MapIndex.lean` | `#classicism_map_index`, which writes `index.json`. |

To regenerate, from `Cian/`:

    python3 map/generate.py <logical-maps checkout> --refs   # needs pyyaml, jsonschema
    lake build
    lake env lean scripts/MapIndex.lean

## Principles at every signature

Each of the map's principles is a schema at every signature `Σ`, a function from
signatures to schemas (`Classicism/Certified/Signatures.lean`):

| kind of principle | its schema at `Σ` | example |
| --- | --- | --- |
| indexed by types | its instances, read in `Σ`'s language | `P.Barcan.schemaIn` |
| relative to a signature | the schema at `Σ` | `noContingency _`, `distinctnessC _` |
| the pure version of one | that schema at the pure signature, read in `Σ`'s language | `pureVersion noContingency` (No Pure Contingency) |

A pure principle throws `Σ` away, but its sentences are still read in `Σ`'s language: in
Lean a sentence's type records its signature, and `ofPure` is the inclusion. These are the
`lean_def`s; Actual Profile's is its list form (`P.ActualProfile.listSchemaIn`), since the
map states it for tuples.

## The shape of a statement

A result, `A₁, …, Aₙ ⇒ C`:

    ∀ {Sig} (_ : Sig.Closed) (Ax : AxiomSet Sig),
      Entails Ax A₁ → … → Entails Ax Aₙ → Entails Ax C

every schema over any signature that entails the premises entails the conclusion: the
entailment `A₁ ∪ … ∪ Aₙ ⟹ C`, at every signature. An incompatibility ends instead in
`¬ Consistent Ax`: every schema entailing the premises is inconsistent. A form `F` of a
principle `P`:

    ∀ {Sig} (_ : Sig.Closed) (Ax : AxiomSet Sig), Entails Ax P ↔ Entails Ax F

`Ax` appears because the map's generator builds a statement as a chain with one proposition
per principle, and `Entails Ax A` is that proposition. `Sig` is bound because a statement is
one closed proposition about functions of the signature. It ranges over the signatures of
the paper's language, whose constants have closed types (`Signature.Closed`): a Lean
`Signature` may also give a constant a type variable, and then `∃v. v = v` at that type is
a pure theorem of `C(Σ)` that `C` does not prove, so the results relating a schema for a
signature to its pure version fail there. Only those use the hypothesis.

The certificate is the object-language entailment, not the shallow proof. The claim is
about `C`, and the map's axiom list is harmless elsewhere but not here: `propext` is the
Fregean Axiom, so a shallow proof passing that check would show nothing about `C`. The
entailments use `propext` and `Quot.sound` only as reasoning about syntax.

## The change to the map's build script (`pmap.patch`)

Two additions to `generate_lean_statements`, and the matching entries in the JSON schemas:

- **`lean.result.falsum`**: how a result concluding `False` is written (default `False`).
  Classicism sets it to `¬ Consistent Ax`. (The key cannot be `false`: YAML reads that as
  the boolean.)
- **`forms`** on a principle: equivalent forms, each with an `id`, a `name`, a
  `statement`, a `lean_def` and a `lean_ref`; each gets the statement above, named
  `<principle>.<form>`.

Still to do in the map: `lean-check` to check the forms' `lean_ref`s as it does the
results', and the viewer to show the forms on a principle's page.

## What a map viewer should see

Today the viewer's "lean" link is the root of the topic's Lean directory for every result.
With `index.json` it can link each result to its proof:

- **Proof**, the first entry of `proofs`: the shallow proof in `Results/Records.lean`, at one
  argument type for a result at every arity, or the metalogical proof in
  `Results/SentenceSchemas/`;
- **At every arity**, when there is a second entry: the theorem in `Results/Arity.lean`;
- **Certificate**: the line in `Classicism/Map.lean`, with its axioms.

and, on a principle's page, each form with its **definition** (beside the official one in
`Principles.lean`, or for a list form its definition by vectorization, `P.X.listQuoted`),
its **proofs** (in `Results/Forms.lean` or `Results/Lists.lean`) and its **certificate**.

A link is a file and a line range, made into a URL by the map's build (a GitHub blob at a
pinned commit, `#L2145-L2160`, or a rendered source page with line anchors). This needs a
small change to `pmap` and `viewer/template.html` in the map repository.

## Open points

- **Axioms.** 194 result certificates rest on `propext` and `Quot.sound` only, and six more
  also on `Classical.choice` (the models), all within the map's list. Three rest also on
  `Classicism.e` and `e_exists`, through the consistency facts from the model in `Prop`,
  which needs an individual: `maximalist-distinctness-incompatible-with-nd`,
  `possibility-and-no-pure-contingency-incompatible` and
  `pure-b-and-pure-possibility-incompatible`. `lean-check` would refuse those three until
  the map's list allows the two, or the model is built on a type known to be inhabited.
- **Coverage.** 2 of the map's 97 principles have no `lean_def` yet, General Separated
  Structure and the Necessity of Arithmetic, so 5 results have no statement. Of the 265
  stated, 35 are not yet proved here: Appendix E's incompatibilities, the Gödel results, the
  conjectured ones, most of those about Separated Structure and Independence, Strong
  Possibility, the Infinity schemas, and the incompatibilities of Witnessed Possibility,
  which need a signature with a constant.
- **Forms.** 22: Boolean Completeness's LUB form, and the list forms of the 21 principles
  with a type parameter whose two directions are proved (`P.X.listSchema_entails_schema`, by
  inclusion; `P.X.schema_entails_listSchema`, `Results/Lists.lean`). For Actual Profile,
  whose official form on the map is the list form, the form is the single-argument one.
  Four principles with a list form lack the second direction: Transversal, Transversal
  Choice and their boxed forms.
- **Models.** 35 of the map's models get statements (`∃` a consistent `Ax` entailing what
  the model satisfies and not what it violates); none is certified yet.
- **No Pure Contingency defined twice.** `npc Σ` (P → □P for each pure sentence of `Σ`'s
  language) and `pureVersion noContingency` are the same set (`npc_eq_pureVersion`), and so
  are the two Pure B's.
- **Conservativity.** `C(Σ)` is conservative over `C` for a closed signature
  (`Syntax/Conservativity.lean`), so the consistency facts proved in the pure language hold
  at every such signature (`consistent_ofPure_iff`).
- **Mathlib.** `lean-check` runs `lake build` on the topic's Lean directory; this project
  needs Mathlib (for the model theory only).
