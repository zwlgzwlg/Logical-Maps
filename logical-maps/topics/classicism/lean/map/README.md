# The Lean side of the map

How the Classicism topic's records and this Lean project fit together. The map's general
mechanism is in `scripts/pmap.py` (`lean`, `lean-check`, `build`); what follows is what this
topic puts into it.

## Where each piece lives

| piece | where |
| --- | --- |
| the topic's Lean setup: library, imports, the shape of a statement, the index, the link template | `topic.yaml`, `lean_lib` and `lean` |
| a principle's Lean schema | its record's `lean_def`, e.g. `Classicism.P.Barcan.schemaIn` |
| a variant's schema and certificate | the variant's `lean`: `ref`, `equivalence_ref`, and `status`, which `lean-check --update` writes |
| a result's certificate | its record's `certificate.lean_ref`, e.g. `Classicism.Map.barcan_r_implies_functionality_r`; `certificate.lean`, which `lean-check --update` writes |
| the statements the certificates prove | `Classicism/Statements.lean`, written by `pmap lean classicism` from the records. Never edited by hand. |
| the certificates | `Classicism/Map.lean`: one theorem per result proved, named by its id, and per variant, `<principle>.<variant>`, each one line citing the proof |
| a model's verdicts proved one by one | the model record's `lean`: `model`, a Lean term for it, and `verdicts`, each `holds` or `fails` a principle with its `ref` and `status`, which `lean-check --update` writes |
| the statements of those verdicts | `Classicism/ModelStatements.lean`, written by `pmap lean classicism`. Never edited by hand. |
| their certificates | `Classicism/MapModels.lean`: one theorem per verdict, `Models.<model id>.<principle id>`, citing the verdict proved in `Models/` |
| where every certificate, proof and principle definition is | `map/index.json`, written by `scripts/MapIndex.lean` (`Classicism/Tools/MapIndex.lean`) |

`lean-check` audits each certificate against its generated statement and the map's list of
axioms (`propext`, `Classical.choice`, `Quot.sound`), results and variants alike, and
writes the index. The build turns the index into links from each result, principle and
variant to its proofs, definitions and certificate: GitHub links pinned to the commit
the map is built from (`lean.source_url`).

## After a change to the Lean

From `logical-maps/`:

    python3 scripts/pmap.py lean-check classicism --update   # build, audit, statuses, index
    python3 scripts/pmap.py validate
    git commit …                                              # the Lean, the records, map/index.json

Contributors do not commit build output; the maintainer rebuilds `build/` and commits it,
since the website imports it, and a contributor's local `pmap build` is for looking. The
links are pinned to the commit a build runs at,
so the published map's links point at the published Lean; a local build warns when
`lean/` has uncommitted changes, whose lines the links would miss. A first build on a new
machine needs Mathlib's cache (`lake exe cache get`, from this directory), then about
twenty minutes; the model theory is the only part that imports Mathlib.

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

**A model's verdicts, one by one.** A model whose whole package is not yet formalized can
still have its verdicts certified singly. For the record's Lean model `A`, a verdict that `P`
holds reads

    A.IsModel ∧ A.HoldsAx P.schemaIn

and one that it fails `A.IsModel ∧ ¬ A.HoldsAx P.schemaIn`; for a principle relative to a
signature (category `signature`), the statement also asks `A.Admitted`, that the model's
signature is one the map's statements range over, so a model of the pure language cannot
certify those. The models of `Models/` are of the pure language, where `P.X.schemaIn` holds
iff `P.X.schema` does (`Premodel.holdsAx_schemaIn_iff`, `Semantics/IntensionalTheory.lean`).
On 5 October 91 verdicts of eleven models were certified this way: Parts 1 to 8 of Appendix D
and the two-object model after Part 8 (`finite-support-*` on the map), and the two M-set models
of §3, on the idempotent monoid and the two-element group (`full-idempotent-monoid`,
`full-involution-group`, from `Semantics/IntensionalExamples.lean`).

The verdicts compose into the whole model's statement once the model is of an admitted
signature: `Premodel.theory`, the sentences holding in a model, is consistent
(`theory_consistent`) and complete (`theory_complete`), and entails a schema iff the schema
holds in the model (`theory_entails_iff`). With every verdict of a record certified, the
model statement is `⟨Sig, hAdm, A.theory, theory_consistent M, theory_complete M, …⟩`, each
conjunct `entails_of_holdsAx M h` or `not_entails_of_not_holdsAx M h`. What is missing is a
model of an admitted signature: the Appendix D models with `Σ` interpreted as the records
say, and the verdicts on the principles relative to a signature there.

**General arguments, and the verdicts they give.** A general argument on the map says that
every model meeting some conditions has a verdict. In Lean it is a theorem over models
(`MapArguments.lean`), and its statement is generated (`ModelStatements.lean`):

- **Topic argument:** `Arguments.<argument>.<principle>` reads: for every intensional action
  model meeting the argument's conditions, the verdict. Each condition is the Lean predicate
  named in `conditions.yaml` (`Models/Conditions.lean`).
- **Group argument:** `Arguments.<group>.<argument>.<principle>` reads: for every value of
  what the group's construction is built from, meeting the group's conditions, the verdict
  in the model built from it. For the finite-support group this is a monoid acting faithfully
  on `ℕ`.

A model meets a condition by a proof named in its record's `lean.meets`, or in its group's
`lean.meets` for every member; member-specific proofs are in `MapModels.lean` under
`Map.Meets`. The map then generates `MapDerived.lean`. For each argument the map applies to a
model, it certifies the model's verdict by applying the argument's certificate to the model's
proofs. So the Lean follows the map's route: a verdict that rests on an argument is proved
by that argument, and only the meeting of conditions is particular to the model.

On 5 October six verdicts of five arguments were proved this way:

| Argument | Condition | Verdict |
| --- | --- | --- |
| `no-pure-contingency-one-object` | one object | No Pure Contingency holds |
| `barcan-d6` | Proposition D.6's surjectivity | BF holds |
| the finite-support group's `actual-world` | actual-world-pinned | Actuality holds |
| `collapsing-atomless` | collapse-unpinned | Atomicity and Atomicity (`t`) fail |
| `barcan-positive` | positive-preserving | BF fails |

They give 23 model verdicts. These replace 21 that had been certified model by model, and
add Atomicity's failure in the two identity-or-collapse models.

Several arguments are not proved yet, because the condition the Lean proves differs from
the map's prose:

- **`boolean-completeness`:** the Lean lemma `not_bc_of` assumes `BCWitness`, which is not
  the condition `unbounded-haecceities` as the map states it.
- **`atomicity`:** the Lean lemma `atomicityT_of_singletons` gives Atomicity at `t` only,
  where the argument claims it at every relational type.

The certificate is the object-language entailment, not the shallow proof. The claim is
about `C`, and the map's axiom list is harmless elsewhere but not here: `propext` is the
Fregean Axiom, so a shallow proof passing that check would show nothing about `C`. The
entailments use `propext` and `Quot.sound` only as reasoning about syntax.

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
- **Models.** 14 of the map's 97 models get statements (`∃` a consistent complete `Ax`
  entailing what the model satisfies and not what it violates, above); the others' verdicts
  mention a principle without a `lean_def`. None is certified as a whole yet; 93 single
  verdicts of eleven models are (above).
- **No Pure Contingency defined twice.** `npc Σ` (P → □P for each pure sentence of `Σ`'s
  language) and `pureVersion noContingency` are the same set (`npc_eq_pureVersion`), and so
  are the two Pure B's.
- **Conservativity.** `C(Σ)` is conservative over `C` for a closed signature
  (`Syntax/Conservativity.lean`), so the consistency facts proved in the pure language hold
  at every such signature (`consistent_ofPure_iff`).
- **Mathlib.** `lean-check` runs `lake build` on the topic's Lean directory; this project
  needs Mathlib (for the model theory only).
