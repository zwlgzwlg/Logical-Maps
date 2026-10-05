# Open work and open questions

What the Lean side of the map has not done, and what is waiting on a decision. For
coverage, `python3 scripts/pmap.py lean-check classicism` (from `logical-maps/`) is the
authority; the lists below were taken from it on 4 October 2026. How to do the work:
`AGENTS.md`.

## Results stated but not proved

32 results have a generated statement and no certificate.

- **Separated Structure, Independence and Witnessed Possibility**:
  `distinctness-signature-r-implies-separated-structure-r`,
  `logical-necessity-r-implies-separated-structure-r`,
  `logical-necessity-r-implies-modal-freedom-signature-r`,
  `possibility-signature-r-implies-witnessed-possibility-r`,
  `possibly-witnessed-possibility-r-implies-separated-structure-r`,
  `separated-structure-r-implies-possibly-witnessed-possibility-r`,
  `separated-structure-r-implies-independence-signature-r`,
  `pure-distinctness-and-separated-structure-imply-signature-distinctness`.
- **Strong Possibility**: `strong-possibility-r-implies-possibility-schema-r`, its
  signature forms, and the two incompatibilities with the Distinctness-Preserving
  Collapse.
- **The Infinity principles and schemas**: `atomlessness-implies-infinity-t`,
  `axiom-of-infinity-{e,t}-implies-infinity-{e,t}`,
  `possible-infinity-{e,t}-implies-axiom-of-infinity-{e,t}`,
  `possibility-schema-r-implies-possible-infinity-t`, `pure-distinctness-implies-infinity-t`,
  `pure-possibility-implies-axiom-of-infinity-t`. (Possible Infinity and BF do give the
  Axiom of Infinity: `Results/Records/Infinity.lean`.)
- **Possibility incompatibilities that need models not yet built** (Appendix E's coalesced
  sums, a Henkin model without choice): `possibility-and-countable-boolean-completeness-incompatible`,
  `possibility-and-necessary-relational-choice-incompatible`,
  `possibility-and-necessary-strong-leibniz-t-incompatible`.
- **Choice and Transversals**: `relational-choice-r-implies-transversal-choice-r`,
  `relational-choice-and-boolean-completeness-imply-transversal-choice`.
- **`c5-and-atomicity(-t)-imply-no-pure-contingency`**: now that No Pure Contingency ranges
  over the paper's language only, open to the automorphism proof of the map's write-up: the
  atom-exchanging automorphism extended to every type by recursion on the type, and an
  induction on pure terms. A substantial formalization.
- **`necessary-strong-leibniz-and-rigid-comprehension-imply-necessary-bf-t`** (Bacon's
  Theorem 8.2): see the questions below.
- **`maximalist-distinctness-incompatible-with-rigid-comprehension`**: Gödel's theorem;
  the boxed version is proved.
- **`atomicity-t-and-weakly-inextensible-comprehension-imply-actuality`**: new on the map,
  4 October.
- **`necessary-atomicity-completeness-bf-imply-rigid-comprehension`** (Proposition 2.11):
  refuted by Cian's countermodel (1 October), so not to be proved. What Lean has is the
  version with a restriction principle in place of the step that fails
  (`rigid_comprehension_r_of_restriction`, `Results/Records/C5.lean`; `VERIFICATION.md`,
  "Proposition 2.11").

## Principles without a Lean definition

General Separated Structure and the Necessity of Arithmetic, whose definitions need care (a
bijection of constants to variables; the class of arithmetical sentences); and those added
to the map since 2 October: Rigid Power, Tame Rigidity, Intensional Choice, and boxed forms
(`necessary-atomicity-t`, `necessary-boolean-completeness-t`,
`necessary-countable-boolean-completeness-r`, `necessary-inextensible-comprehension-r`,
`necessary-persistent-comprehension-r`, `necessary-weak-rigid-comprehension-r`, and the
boxed Rigid Power, Tame Rigidity and Intensional Choice). Most are routine to state; each
needs checking against the map's wording.

## Variants

- Stated but not proved: the polyadic forms of Transversal, Transversal Choice and their
  boxed forms (`P.X.listSchemaIn`); the direction from the list form needs an induction
  on the list, as in `Results/Lists.lean`.
- Not stated: the duals of the sentence schemas (No Contingency, No Pure Contingency,
  Signature and Pure B, Witnessed Possibility and its kin, Logical Necessity, Modal
  Freedom, Possibility+ in both forms), to be defined beside their schemas in `Syntax/`;
  the GLB form of Countable Boolean Completeness and its boxed form, which needs the
  countability of `λz. X(¬z)` from that of `X`; and the variants of the principles above
  without a definition.

## Models

No model statement is certified. A certificate needs a consistent complete theory with the
model's verdicts: a model's verdicts as `Consistent` and `¬ Theorem` facts, extended to a
complete theory by a Lindenbaum construction. Open alongside: the symmetric ideally full
model and the other two-object variants of Appendix D (`Classicism/Models/README.md`), the
coalesced sums of Appendix E, and what a model file should export (verdicts as
`Consistent` / `¬ Theorem` facts, or the model with its `HoldsAx` facts).

## Questions

- **Bacon's Theorem 8.2.** The map's sketch applies Rigid Comprehension inside the box (a
  rigid collection of world properties accessible to `W`, with `W` chosen at the inner
  world), but the premise is unboxed, and an axiom cannot be necessitated. Either the
  argument uses only the actual instance and rigidity carries it, or the premise should be
  `□`Rigid Comprehension; the book would settle it.
- **The very-weak-rigid-comprehension route to Boolean Completeness at `t`**: Lean has it
  (`very_weak_rigid_comprehension_implies_boolean_completeness_t`); the map does not record
  it.
- **Type variables are conservative.** That derivability and consistency are unchanged by
  the type variables, for sentences and theories of the paper's language, should follow by
  instantiating every type variable at `e`, a vectorization at singleton lists
  (`C.Theorem.vec`). Not formalized, like the agreement of this natural deduction system with
  the paper's Hilbert-style axiomatization; Cian, 4 October: fine to leave for now.

## Housekeeping

- `Classicism/Strict/`: its fate is Cian's call. Its mirror `SPointwise` lacks the
  `Pointwise` fields added after the first eleven, so the strict transformer does not reach
  the ten form equivalences that use them; `Tools/Schema.lean` still has code paths for the
  `.strict` twins.
- Small cleanups, worth doing only when the whole project is being rebuilt anyway: none at
  present.
