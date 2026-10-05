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
| `lean.yaml` | The fields the map would carry: `lean_lib` and `lean` (for `topic.yaml`), a `lean_def` for each of the 95 principles formalized here, the reserved `lean` field (`ref`, `equivalence_ref`) of 60 of the map's 77 variants, and a `lean_ref` for each of the 234 results certified. |
| `pmap.patch` | The proposed change to the map's build script and JSON schemas (below). |
| `generate.py` | Runs the map's own generator, with `pmap.patch` applied in memory, on a checkout of the map with these fields added, writing `Classicism/Statements.lean`; `--refs` fills `lean_ref` from `Classicism/Map.lean`, `--patch` rewrites `pmap.patch`. |
| `index.json` | For each certified result and variant: its certificate (file, lines, axioms) and the declarations a reader wants, the proofs (file, lines), and for a variant the definitions of both forms. Written by `scripts/MapIndex.lean`. |

and, in the library:

| file | what it is |
| --- | --- |
| `Classicism/Certified/Signatures.lean` | Each principle as a schema at every signature: `P.X.schemaIn`, `pureVersion`, `distinctnessC`, `possibilityC`. |
| `Classicism/Statements.lean` | The generated statements, from the map at `2abe6c1` (4 October): 266 of the 316 results (those whose principles all have a `lean_def`), 14 models, 60 variants. Not edited by hand. |
| `Classicism/Map.lean` | One certificate per result proved, named by its id, and per form, named `<principle>.<form>`, each of the generated type: the `lean_ref`s. Each is one line citing the proof. |
| `Classicism/Principles/*.lean` | The principles, a file per category of the map, each form defined beside its principle with the shallow proofs of the two directions, `P.X.to_<form>` and `P.X.of_<form>` (the list forms' are in `Results/Lists.lean`). |
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

    ∀ {Sig} (_ : Sig.Admitted) (Ax : AxiomSet Sig),
      Entails Ax A₁ → … → Entails Ax Aₙ → Entails Ax C

every schema over any signature that entails the premises entails the conclusion: the
entailment `A₁ ∪ … ∪ Aₙ ⟹ C`, at every signature. An incompatibility ends instead in
`¬ Consistent Ax`: every schema entailing the premises is inconsistent. A form `F` of a
principle `P`:

    ∀ {Sig} (_ : Sig.Admitted) (Ax : AxiomSet Sig), Entails Ax P ↔ Entails Ax F

`Ax` appears because the map's generator builds a statement as a chain with one proposition
per principle, and `Entails Ax A` is that proposition. `Sig` is bound because a statement is
one closed proposition about functions of the signature. It ranges over the signatures the
map's Background admits (`Signature.Admitted`): their constants have closed types, the
paper's (a Lean `Signature` may also give a constant a type variable, and then `∃v. v = v`
at that type is a pure theorem of `C(Σ)` that `C` does not prove, so the results relating
a schema for a signature to its pure version fail there); and, the Background's standing
assumption, at least one constant has a type other than `e` (the proofs of the
incompatibilities of Witnessed Possibility, Separated Structure and No Contingency need a
constant of relational type).

A model, satisfying `S₁, …, Sₘ` and violating `V₁, …, Vₖ`:

    ∃ (Sig) (_ : Sig.Admitted) (Ax : AxiomSet Sig), Consistent Ax ∧ Complete Ax ∧
      Entails Ax S₁ ∧ … ∧ ¬ Entails Ax V₁ ∧ …

a consistent **complete** theory (`Syntax/ClosedTypes.lean`: it decides every sentence of the
paper's language), the syntactic form of a single model. Without completeness the violations
need not hold together: the empty theory entails neither the Fregean Axiom nor its negation,
so a merely consistent theory would "violate" both (Astra's audit, 4 October). The statement
cannot name the model's construction; the certificate's proof is where that construction
appears.

**The sentence schemas range over the paper's language.** The object language here also has
type variables, a device of the metalogic; every sentence schema (No Contingency, No Pure
Contingency, B, Distinctness, Possibility, Witnessed Possibility and its kin, Separated
Structure, Independence, Possibility+, Strong Possibility, Ordinary Comprehension) requires
each instance to have only closed types (`Term.closedTypes`), and every principle's schema is
shown to have only such instances (`P.X.schema_closedTypes`). Before 4 October they did not,
so that "type variable `0` is empty" was an instance of No Contingency and of Possibility
(Astra's audit).

The certificate is the object-language entailment, not the shallow proof. The claim is
about `C`, and the map's axiom list is harmless elsewhere but not here: `propext` is the
Fregean Axiom, so a shallow proof passing that check would show nothing about `C`. The
entailments use `propext` and `Quot.sound` only as reasoning about syntax.

## The change to the map's build script (`pmap.patch`)

Two additions to `generate_lean_statements`, and the matching entry in the topic schema:

- **`lean.result.falsum`**: how a result concluding `False` is written (default `False`).
  Classicism sets it to `¬ Consistent Ax`. (The key cannot be `false`: YAML reads that as
  the boolean.)
- **variants**: a principle's variant whose reserved `lean` field gives `ref`, the
  variant's schema, gets the statement above, named `<principle>.<variant>`. Its certificate
  is `lean.equivalence_ref`. The field is the map's own (`principle.schema.json`), so the
  principle schema needs no change.

Still to do in the map: `lean-check` to check the variants' `equivalence_ref`s as it does
the results' `lean_ref`s, and the viewer to show them on a principle's page.

## What a map viewer should see

Today the viewer's "lean" link is the root of the topic's Lean directory for every result.
With `index.json` it can link each result to its proof:

- **Proof**, the first entry of `proofs`: the shallow proof in `Results/Records/`, at one
  argument type for a result at every arity, or the metalogical proof in
  `Results/SentenceSchemas/`;
- **At every arity**, when there is a second entry: the theorem in `Results/Arity.lean`;
- **Certificate**: the line in `Classicism/Map.lean`, with its axioms.

and, on a principle's page, each form with its **definition** (beside the official one in
`Principles/`, or for a list form its definition by vectorization, `P.X.listQuoted`),
its **proofs** (beside the definition in `Principles/`, or in `Results/Lists.lean`) and its
**certificate**.

A link is a file and a line range, made into a URL by the map's build (a GitHub blob at a
pinned commit, `#L2145-L2160`, or a rendered source page with line anchors). This needs a
small change to `pmap` and `viewer/template.html` in the map repository.

## Open points

- **Axioms.** Every certificate rests on `propext`, `Quot.sound` and `Classical.choice` at
  most, the map's list. (Until 4 October three rested also on `Classicism.e` and `e_exists`,
  through the model in `Prop` built on the shallow layer's `e`; it is now built on `Unit`.)
- **Coverage.** 14 of the map's 109 principles have no `lean_def` yet: General Separated
  Structure and the Necessity of Arithmetic, and those added to the map since 2 October
  (Rigid Power, Tame Rigidity, Intensional Choice and others), so 50 results have no
  statement. Of the 266 stated, 32 are not yet proved here: the newest,
  `atomicity-t-and-weakly-inextensible-comprehension-imply-actuality`, and Appendix E's incompatibilities, the Gödel results, the
  six conjectured ones, most of those about Separated Structure and Independence, Strong
  Possibility, the Infinity schemas, Bacon's Theorem 8.2, and C5 and Atomicity ⇒ No Pure
  Contingency (now that No Pure Contingency ranges over the paper's language only, this one
  is open to the automorphism proof; see HANDOFF, §8).
- **Variants.** 60 of the map's 77 have a Lean statement, and 56 of those a certificate:
  the 20 polyadic variants whose two directions are proved (`P.X.listSchema_entails_schema`,
  by inclusion; `P.X.schema_entails_listSchema`, `Results/Lists.lean`); the 26 duals of
  principles with a shallow statement and the 3 LUB forms (`P.X.to_<variant>`,
  `P.X.of_<variant>`, beside the principle in `Principles/`); and the 7 dual polyadic
  variants, composed from both. Stated but not proved: the polyadic variants of Transversal,
  Transversal Choice and their boxed forms. Not stated: the duals of the sentence schemas,
  the GLB forms of Countable Boolean Completeness, and the variants of principles without a
  `lean_def`.
- **Models.** 14 of the map's 89 models get statements (`∃` a consistent complete `Ax`
  entailing what the model satisfies and not what it violates, above); the others' verdicts
  mention a principle without a `lean_def`. None is certified yet.
- **No Pure Contingency defined twice.** `npc Σ` (P → □P for each pure sentence of `Σ`'s
  language) and `pureVersion noContingency` are the same set (`npc_eq_pureVersion`), and so
  are the two Pure B's.
- **Conservativity.** `C(Σ)` is conservative over `C` for a closed signature
  (`Syntax/Conservativity.lean`), so the consistency facts proved in the pure language hold
  at every such signature (`consistent_ofPure_iff`).
- **Mathlib.** `lean-check` runs `lake build` on the topic's Lean directory; this project
  needs Mathlib (for the model theory only).
