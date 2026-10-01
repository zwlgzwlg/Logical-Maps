# Plan: lists of types, and the vectorization theorem

*Written 1 October 2026, from the design agreed with Cian on 30 September – 1 October,
and a survey of the code that day. To be carried out phase by phase (§6); each phase ends
with a green build and its audit counts recorded in `HANDOFF.md`. Decisions still open
are collected in §9.*

## 1. What we are building

A principle of the map with a type parameter σ declared `[Ty σ]` has two forms:

- the **restricted form**, with one instance for each type σ; and
- the **list form**, with one instance for each finite list `σs = σ₁ … σₙ` of types, the
  empty list included. A variable of type σ becomes a block of variables `x₁ … xₙ`, a
  function from σ becomes a function of n arguments, a quantifier over σ becomes a block
  of n quantifiers, and identity at σ becomes the conjunction `x₁ = y₁ ∧ … ∧ xₙ = yₙ`
  (`⊤` when n = 0).

Functionality, for instance: the restricted instance at `(σ; τ)` is
`∀X Y : σ → τ. (∀z. X z = Y z) → X = Y`, and the list instance at `(σs; τ)` is
`∀X Y : σ₁ → … → σₙ → τ. (∀z₁ … zₙ. X z₁ … zₙ = Y z₁ … zₙ) → X = Y`.

The metalogic gets one general fact, the **vectorization theorem**: if a sentence that
mentions a type variable α is derivable, so is its translation with α replaced by any list
of types. The translator's derivations are generic in their type parameters, so every
certified result with a Ty-parameter yields its list form with no further proof. (The
translator itself changes in one line: Phase 1.)

When the plan is done:

- every principle with a Ty-parameter has its list form beside its restricted form
  (`P.X.listSchema` beside `P.X.schema`), with the entailments between them;
- every certified result with a Ty-parameter has its list form beside its restricted
  form (`foo.listEntails` beside `foo.entails`);
- the results "at every arity" are unary shallow proofs, vectorized, with no induction
  per result; the stopgaps of 28 September (`P.BarcanArgs`, `P.NecBarcanArgs`, the
  inductions in `Results/Arity.lean` and `Results/Atomicity.lean`, the `_unary` records)
  are gone or replaced, as if the project had been designed this way from the start;
- the README has a section setting out the names (§8).

## 2. Vocabulary

These are the words the code, the docs and the conversation will use. Today's code uses
"type variable" for what is called a *type parameter* below (71 times, in 17 files) and
sometimes "schema" for a *principle*; Phase 1 brings it into line.

| term | meaning |
| --- | --- |
| **principle** | the shallow definition, e.g. `P.Functionality : (σ τ : Type) → [Ty σ] → [Rel τ] → Prop` |
| **instance** | one sentence of the object language, `P.Functionality.quoted σ τ` (in the shallow layer, the Lean proposition `P.Functionality σ τ`) |
| **schema** | the axiom set of all instances, `P.Functionality.schema` |
| **restricted form, list form** | of a principle with a Ty-parameter: the two schemas of §1, `P.X.schema` and `P.X.listSchema` |
| **type parameter** | a variable bound by Lean that stands for a type: in the shallow layer `σ : Type` with a marker (`[Ty σ]` a **Ty-parameter**, `[Rel τ]` a **Rel-parameter**); in the metalogic `σ : Meta.Ty` or `τ : Meta.RTy` |
| **type variable** | `Ty.var i`, a type *of the object language* about which nothing is known; part of the syntax, bound by nothing |
| **closed type** | a type with no type variable: the types of the paper's language |
| **assignment** | a map from type variables to lists of types |
| **vectorization** | the translation of terms, formulas and derivations along an assignment |
| **block** | the list of variables standing in for one variable whose type is vectorized |

## 3. Design decisions

**D1. Type variables in the object language.** `Meta.Ty` gets a third constructor,
`var : Nat → Ty`. A type variable is never relational, so it can be the type of a variable
or the argument type of an arrow but never a codomain: the object-language image of a
Ty-parameter. Application and λ always produce relational types, so the only terms of a
variable type are variables, which is what lets a variable be split into a block.

**D2. Schemas range over closed types.** `Ty.closed`/`RTy.closed` say a type has no
variable, and `#classicism_schema` generates `P.X.schema = {P.X.quoted σ … | σ … closed}`.
The map's schemas are about the paper's types, and closedness is what keeps a list form's
other parameters out of the translation's way (D5): the list form is the translation at
`var 0`, which must not touch a closed τ. Rules and derivations (`foo.derivable`,
`foo.rule`) keep quantifying over all types: they are uniform, so they hold at type
variables too, and that is what Phase 4 uses. Cost: the generator's membership proofs
(`schemaMemBuild`, now `⟨args, rfl⟩`) supply closedness, and the 55 hand-written proofs
that unpack membership take the extra hypothesis, mostly to ignore it. The alternative,
schemas over all types, is harmless (by the vectorization theorem an instance at a type
variable proves nothing an instance at a closed type does not, and every model reads a
variable as it reads `e`) and saves those edits, but every list form then needs a
variable chosen fresh for its other parameters. See §9.

**D3. What a type variable denotes.** Only closed sentences matter to the models, but
Lean's denotation functions are total, so a type variable needs a reading, and every
proof by cases on a type gains a case. In the reading in `Prop`, a variable denotes what
`e` denotes. In the action models nothing has to be chosen: the outer domain at a type is
built from the premodel's `inner : Ty → C ⥤ Type`, which already assigns an inner
domain to every type, so `RawT` at a variable is `(inner (.var i)).obj W`, exactly as at
`e`; a variable is valued by `inner`. The full and ideally full models build `inner` by
`Ty.rec`, and there a variable's case is `De`, the domain of `e`. In every proof by cases
the variable's case is the `e` case.

**D4. Vectorization acts along an assignment.** Every type goes to a list of types (a
one-element list except at an assigned variable), every term to a tuple of terms (a single
term except at an assigned variable, where it is the block). So several Ty-parameters can
be vectorized at once (Relational Choice's inputs and outputs), the one-element case is
type substitution, and vectorizations compose. Recommended refinement: define the block
operations so that a one-element block *is* the unvectorized operation (`∀` over `[σ]` is
`all σ`, not `λX. ∀x. X x`), so that type substitution and the restricted instances come
out on the nose rather than up to η.

**D5. A list form is defined, not written.** `P.X.listQuoted σs … := (P.X.quoted (var 0) …)`
vectorized along `0 ↦ σs`, one variable per Ty-parameter; it cannot be mis-stated. A
readable form in the block vocabulary is proved equal to it and printed by the audit, and
`P.X.quoted σ … = P.X.listQuoted [σ] …` holds by computation (the *uniformity* of the
quoted principle).

**D6. Generated, not hand-written.** `#classicism_schema` declares the list form of every
principle with a Ty-parameter, with `P.X.listSchema ⟹ P.X.schema`. `#classicism_certify`
declares `foo.listRule` and `foo.listEntails` for every record with a Ty-parameter. The
audits count them.

**D7. Results at every arity are unary proofs, vectorized.** A result about relations of
every arity is proved in the shallow layer at `σ → Prop` (or at `σ → τ`), in the paper's
own words, and vectorized. No shallow statement mentions a list, and no auxiliary
principle stands in for a list form. A result whose proof is pointwise at a relational
type and needs no list-form premise stays a kernel at a Rel-parameter τ, as now: it is
already at every arity.

**D8. From the restricted form to the list form.** Per principle:
- a theorem of `C` with a proof generic in the type (Modalized Functionality, Converse
  Barcan, Necessity of Identity, Broad Necessitism): vectorize its proof;
- otherwise an induction on the list: the empty list directly, and the step from `σs` to
  `σ₁ :: σs` is the vectorization (in `σ₂`) of a shallow proof of the two-element case
  from restricted instances,
  `X σ₂ τ → X σ₁ (σ₂ → τ) → [X over σ₁, σ₂; τ]`;
- Plenitude: open (the two-element step needs Functionality); recorded, not attempted.

**D9. The map.** Whether the map gets separate list-form nodes or annotations on the
principle records, the Lean side is the same.

## 4. Where things will live

| module | after the plan |
| --- | --- |
| `Syntax/Types.lean` | `Ty.var`; `Ty.closed`, `RTy.closed`; `RTy.arrs σs ρ`, written `σs ⇒* ρ` (`RTy.ofArgs σs` is `σs ⇒* t`); the module doc on type variables |
| `Syntax/Blocks.lean` (new) | tuples of terms `Terms Sig Γ σs`; `appBlock`, `lamBlock`, `allBlock`, `exBlock`, `eqBlock`, `forallBlock`; their β, η and δ conversions |
| `Syntax/Vectorize.lean` (new) | assignments; the translation of types, contexts, variables, terms and holes; its laws with renaming and substitution; conversion preserved; one-element case and composition |
| `Syntax/Derivation.lean` | the block rules, derived: `allIBlock`, `allEBlock`, `exIBlock`, `exEBlock`, `reflBlock`, `llBlock` |
| `Syntax/Vectorization.lean` (new) | the theorem `Derivable.vec`, `Theorem.vec`; lifting a rule; the induction principle for list schemas (D8) |
| `Semantics/*` | a case for type variables (D3) |
| `Principles.lean` | docstring in the vocabulary of §2; `BarcanArgs`, `NecBarcanArgs` and the "Auxiliary schemas" section gone; `ActualProfile`'s docstring says the map's principle is its list form |
| `Pointwise.lean` | modal laws used only by the old kernels removed (§7) |
| `Results/Records.lean` | the shallow records, unary as now; `_unary` suffixes gone (their list forms are the map's records); `_at_t` records replaced where a unary proof is supplied |
| `Results/Lists.lean` (new) | restricted ⇔ list for every principle: the two-element steps, certified; the theorems of `C`; the inductions |
| `Results/Arity.lean` | the results at every arity: kernels needing a list-form premise restated at `σ → Prop` and vectorized; kernels at τ without one kept; the metalogic reduced to compositions |
| `Results/Atomicity.lean` | the step `Atomicity τ → BF σ → Atomicity (σ → τ)` kept, vectorized in σ; the induction on the type gone |
| `Tools/Schema.lean` | closed schemas; list forms in `#classicism_schema`; `listRule`, `listEntails` in `#classicism_certify`; audits report them |
| `Certified/*.lean` | regenerated |
| `Tools/Tests.lean`, `Syntax/Examples.lean` | the translation at concrete lists, checked by `rfl` |
| `README.md`, `Classicism/README.md`, `HANDOFF.md`, `VERIFICATION.md`, `MAP-SURVEY.md` | §8 |

## 5. The translation, in brief

For an assignment θ (default: each variable to itself):

| | becomes |
| --- | --- |
| type `e`, `t`, unassigned variable | itself (a one-element list) |
| assigned variable `var i` | the list `θ i` |
| `σ ⇒ ρ` | `(σ's list) ⇒* ρ'` |
| context Γ | each entry replaced by its list, innermost last within a block |
| variable of an assigned type | its block of variables |
| `app F a` | `appBlock F' a'` (F applied to the whole tuple) |
| `lam b` | `lamBlock b'` |
| `all σ`, `ex σ` | `allBlock`, `exBlock` over σ's list |
| `eq σ` | `eqBlock` over σ's list: the conjunction of identities, `⊤` if empty |
| a pointwise constant at ρ | the same constant at ρ' |
| a signature constant | itself (its type is closed) |

What has to be proved, in order: the translation commutes with renaming and with
substitution (the de Bruijn bookkeeping for blocks of variable length, done once here and
nowhere else); it preserves conversion (a β-, η- or δ-step at an assigned type becomes as
many steps as the block is long); and each rule of `Derivable` goes to its block version.
Subst goes to Subst, its side derivations being in the logical part, whose one axiom
(Existence at `e`) mentions no variable. The theorem:

    Derivable.vec : (∀ a, Ax a → Ax' (a.vec θ)) → (∀ a, Ax.logical a → Ax'.logical (a.vec θ)) →
      Derivable Ax Δ p → Derivable Ax' (Δ.vec θ) (p.vec θ)
    C.Theorem.vec : C.Theorem p → C.Theorem (p.vec θ)

and a record's list form is its rule at type variables, vectorized:

    foo.listRule : ∀ σs … (closed), C.Theorem (imp (P₁.listQuoted …) (… (Q.listQuoted σs …)))
    foo.listEntails : P₁.listSchema ∪ … ⟹ Q.listSchema

A premise whose Ty-parameter is not the vectorized one comes out as a restricted
instance, which is a one-element list instance (D4, D5).

## 6. Phases

Each phase is one or more commits, ends with `lake build` green, and records in
`HANDOFF.md` the audit counts (today: 199 of 199 record theorems derived, 111 of 111
certified, 147 of 230 map results proved).

**Phase 0. Setup.** Lean toolchain and the Mathlib part the project uses (`HANDOFF.md`
§2); a full build to fix the baseline counts.

**Phase 1. Type variables and closed types (D1–D3), and the vocabulary.**
- `Ty.var`; `beq` and decidable equality; `Ty.closed`, `RTy.closed` with simp lemmas;
  `Ty.cases` (used nowhere) becomes three-way.
- Every explicit application of the mutual recursor gains an argument for the new
  constructor: `RTy.induction` in `Syntax/Types.lean`; the translator's generated
  induction for class laws (`ensureFieldInduction`, `Tools/Translate.lean`, where
  `RTy.rec` is applied to one argument per constructor), a trivial case since its motive
  on `Ty` is `True`; and `RawR`, `ActionFull`, `IntensionalFull`, `IdeallyFull` below.
  This is the translator's only change.
- Semantics, the variable case (D3), about 25 sites in 8 files:
  `Semantics/Denotation.lean` (`Ty.denote`, `Ty.denote_nonempty`);
  `Semantics/Action.lean` and `Semantics/Intensional.lean` (`RawR`, `RawT` and its `map`,
  the functoriality lemmas, the default element); `Semantics/ActionFull.lean`,
  `Semantics/IntensionalFull.lean`, `Semantics/IdeallyFull.lean` (`inner` by `Ty.rec`,
  pinning); `Semantics/ActionFacts.lean`, `Semantics/IntensionalFacts.lean` (`cases σ`).
  `Models/` and `Strict/` have none.
- Schemas over closed types: `schemaOfQuoted` and the entailment generator in
  `Tools/Schema.lean`; the hand-written proofs that unpack schema membership (55 sites,
  mostly `Results/Schemas/Consistency.lean`, `Results/Arity.lean`) take the closedness
  hypothesis along.
- The terminology sweep of §2, in comments and docs; the README section of §8 for the
  objects that exist today.
- *Done when* the build is green and every audit count is unchanged.

**Phase 2. Blocks.** `RTy.arrs`; `Terms`; the block operations with D4's one-element
convention; their conversions; the derived block rules. Tests: each block rule at a
concrete list of length 0, 1 and 2.

**Phase 3. The translation.** Assignments; translation of types, contexts, variables,
terms, holes; renaming and substitution laws; conversion preserved; one-element case is
type substitution; composition. Definitions the kernel will evaluate are written through
`Term.rec`, as `rename` and `subst` are. Tests: Functionality, BF, Relational Choice at
`[]`, `[e]`, `[e, t]`, checked by `rfl`.

**Phase 4. The theorem.** `Derivable.vec`, `Theorem.vec`, lifting a rule; `#print axioms`
shows nothing beyond Lean's three. A first use by hand: the list form of
`barcan_r_implies_functionality_r`.

**Phase 5. The pipeline.** `#classicism_schema` declares `listQuoted`, `listSchema`, the
uniformity equation, the readable form and `listSchema ⟹ schema`; `#classicism_certify`
declares `listRule`, `listEntails`; `Certified/` regenerated; the audits count list forms.
The README table (§8) gets its list rows.

**Phase 6. Restricted ⇔ list.** `Results/Lists.lean`, per D8: the theorems of `C`; for the
others the empty case and the two-element step (BF, ND, Tractarianism, Functionality,
both Choices, their boxed forms, and Existence, whose restricted instances are theorems of
`C` proved by cases on the type, so that its list form needs the step too); the generic
induction. Plenitude and Actual Profile recorded as open in the restricted-to-list
direction.

**Phase 7. Folding in** (§7): `BarcanArgs` and its inductions removed; the kernels that
used it restated at `σ → Prop` and vectorized; Atomicity by vectorizing its step; the
`_unary` and `_at_t` records; `Pointwise` trimmed; the counts in `MAP-SURVEY.md`.

**Phase 8. Documentation complete** (§8).

**Phase 9. What the lists unlock.** The haecceity results (`actuality-implies-actual-profile-r`
first: its unary proof exists and Actuality has no type parameter, so its list form is the
map's record outright; then Extensionality ⇒ Atomicity by haecceities, the haecceity LUB
in Weak Rigid Comprehension, Proposition 2.11) and the Boolean Completeness family, whose
pointwise meet is an ordinary λ-term at `σ → t`.

**Phase 10. The map** (in `Logical-Maps`, outside this repository): list-form principles
(or annotations, D9), with the empty list; the records between the two forms; `lean:`
fields citing `foo.listEntails` and `P.X.listSchema ⟹ P.X.schema`; `pmap.py lean` taught
the new shapes.

## 7. What gets folded in

From the survey of 1 October. The rule throughout: a result about relations of every
arity whose proof needs a *list-form premise* (BF over a tuple) or a *tuple as an object*
(a haecceity) is a unary proof, vectorized; a result whose proof is pointwise reasoning at
a relational type and needs neither stays a kernel at a Rel-parameter τ, since it is
already at every arity. A unary proof often needs no list-form premise at all: in `C5`,
BF at σ comes from `□ND` at `t` inside the proof
(`necessary_distinctness_necessary_r_implies_necessary_barcan_r : □ND_t → □BF σ`), and
`□ND_t` has no type parameter, so vectorizing gives every arity from `□ND_t` directly.

**`Principles.lean`.** `P.BarcanArgs` and `P.NecBarcanArgs` and their section go; their
role is played by the list forms of BF and `□`BF. `Certified/Schemas.lean` stops quoting
them.

**`Results/Arity.lean`, shallow part.**
- Removed, their content being the two-element steps of BF and `□`BF in
  `Results/Lists.lean`: `barcanArgs_t`, `barcanArgs_step`, `necBarcanArgs_t`,
  `necBarcanArgs_step`.
- Restated at `σ → Prop` and vectorized, because they use BF over the tuple:
  `weaklyInextensible_of_b_barcanArgs`, `inextensible_of_persistent_c5`,
  `weaklyInextensible_of_neg`, `c5_actuality_rigid_comprehension`,
  `c5_necessary_actuality_necessary_rigid_comprehension`,
  `gallin_barcanArgs_weak_rigid_comprehension`, `gallin_necBarcanArgs_rigid_comprehension`,
  `nec_gallin_necBarcanArgs_nec_rigid_comprehension`. Where `Results/Records.lean` already
  has the unary statement (`c5_and_actuality_imply_rigid_comprehension_unary`,
  `c5_and_atomicity_imply_necessary_rigid_comprehension_unary`, and the unary lemmas
  `inextensible_of_persistent_c5`, `weaklyInextensible_of_persistent_b_bf` there), that is
  the theorem vectorized and the kernel goes.
- Kept as kernels at τ (no tuple premise): `actual_iff`, `persistent_coext_of_actual`,
  `actuality_implies_persistent_comprehension_r`,
  `very_weak_rigid_comprehension_r_implies_weak_rigid_comprehension_r`,
  `weaklyInextensible_of_all`, `extensionality_r_implies_rigid_comprehension_r`,
  `persistent_neg_of_c5`, `c5_and_persistent_comprehension_imply_gallin`, `c5_rigid_gallin`,
  `c5_and_necessary_rigid_comprehension_imply_necessary_gallin_comprehension`,
  `c5_necessary_atomicity_t`, `fregean_actuality_necessary_actuality`.
- `necAtomicity_step` (`□`Atomicity at τ, `□`BF at σ, so `□`Atomicity at `σ → τ`): kept,
  vectorized in σ.

**`Results/Arity.lean`, metalogic part.**
- Replaced by the general machinery: `barcanArgs_of_barcan` and `necBarcanArgs_of_necBarcan`
  (by `P.Barcan.schema ⟹ P.Barcan.listSchema` and its boxed form, `Results/Lists.lean`);
  `necBarcanArgs_of_c5` (by the vectorized `□ND_t → □BF σ`); `atomicity_of_atomicity_at_t_barcan`
  and `necAtomicity_of_at_t_necBarcan`, inductions on the type (by the vectorized steps).
- Kept, re-cited: the compositions that are the map's arrows,
  `actuality_implies_persistent_comprehension_r`, `c5_and_actuality_imply_rigid_comprehension`,
  `gallin_comprehension_and_bf_imply_weak_rigid_comprehension`,
  `gallin_comprehension_and_bf_imply_rigid_comprehension`,
  `c5_and_atomicity_imply_necessary_rigid_comprehension`,
  `c5_and_necessary_actuality_imply_atomicity`, `c5_and_necessary_completeness_imply_atomicity`,
  `c5_and_atomicity_imply_necessary_atomicity`, `extensionality_r_implies_atomicity_r`,
  `necessary_gallin_comprehension_implies_necessary_rigid_comprehension`,
  `necessary_plenitude_r_implies_atomicity_r`, `necessary_plenitude_r_implies_necessary_atomicity_r`.
  A conclusion indexed by a relational type is reached from the vectorized one at
  `σs ⇒* t` by `RTy.ofArgs_args`: every relational type is `(its arguments) ⇒* t`.

**`Results/Atomicity.lean`.** `atomicity_step` (Atomicity at τ, BF at σ, so Atomicity at
`σ → τ`) stays and is vectorized in σ; at τ = `t` that is the map's arrow, and the
induction `atomicity_of_atomicityT_barcan` goes (it duplicates
`atomicity_of_atomicity_at_t_barcan` above). The file stays the worked example, now of
vectorizing a step: the step at one argument, vectorized, *is* the induction.

**`Pointwise.lean`.** Of the nine modal laws added on 28 September, all used only in
`Results/Arity.lean`, three serve only the kernels being restated (`boxImp_of_top_or`,
`top_boxAt_of_b`, `top_boxAt_of_neg`) and go if nothing else needs them; the other six
serve kernels that stay.

**`Results/Records.lean`.**
- `_unary` records: `c5_and_actuality_imply_rigid_comprehension_unary` and
  `c5_and_atomicity_imply_necessary_rigid_comprehension_unary` lose the suffix, their
  list forms being the map's records; `actuality_implies_actual_profile_r_unary` likewise
  (Phase 9's pilot: Actuality has no type parameter, so its list form is the map's record
  outright); `actuality_implies_persistent_comprehension_r_unary` goes, the kernel at τ
  being the record at every arity already.
- `_at_t` records, proved only at `t` where the map's record is at every arity: the
  Boolean Completeness family (`weak_rigid_comprehension_r_implies_boolean_completeness_r_at_t`,
  `rigid_comprehension_r_implies_boolean_completeness_r_at_t`,
  `extensionality_r_implies_boolean_completeness_r_at_t`,
  `necessary_rigid_comprehension_r_implies_necessary_boolean_completeness_r_at_t`,
  `c5_and_actuality_imply_completeness_at_t`, `c5_and_atomicity_imply_necessary_completeness_at_t`),
  the Plenitude pair (`c5_and_completeness_imply_plenitude_at_t`,
  `rigid_comprehension_and_nd_imply_plenitude_at_t`), and the Atomicity pair
  (`c5_and_necessary_actuality_imply_atomicity_at_t`,
  `c5_and_necessary_completeness_imply_atomicity_at_t`). Each either gets a unary proof
  at `σ → t`, whose vectorization at the empty list is the `t` case so that the `_at_t`
  theorem goes (Phase 9; the Boolean Completeness family needs the pointwise meet at
  `σ → t`), or stays as the `t`-instance a composition starts from (the Atomicity pair,
  whose compositions carry them to every arity through the vectorized step).
- `classicism_implies_existence_r_at_e` and `_relational` stay: the restricted form of
  Existence is proved by cases on the type; its list form comes from the two-element step
  (Phase 6).

**Docs.** `VERIFICATION.md` (line 886 cites `barcanArgs_of_barcan`), `HANDOFF.md` §4a
(closed), `MAP-SURVEY.md` (counts).

## 8. Documentation

- `README.md`: a new section, **Names: principles, instances and schemas**, after "The
  relational type system", with two tables: the objects behind a principle's name
  (below), and type parameters against type variables. "The relational type system" is
  reworded in the vocabulary of §2 (it now calls a principle "a schema").
- `Classicism/README.md`: the module table; a section **Type variables and vectorization**
  (the translation, the theorem, why the theorem needs a type variable rather than a type
  parameter); "Schemas, entailments and rules" with list forms; "A metalogical proof with
  object-level steps" presents vectorization as the route to a result at every arity and
  induction on the type as the route when the argument is not uniform.
- `HANDOFF.md`: §4a closed with a pointer here; §5 agenda; the conventions of §3.
- `VERIFICATION.md`: what a list-form certificate rests on (the theorem, kernel-checked;
  the generators untrusted, their output checked).
- `MAP-SURVEY.md`: the counts after Phases 7 and 9.

The README table, in its final form:

| name | layer | type | what it is |
| --- | --- | --- | --- |
| `P.Functionality` | shallow | `(σ τ : Type) → [Ty σ] → [Rel τ] → Prop` | the principle: for Lean types standing for object types, the instance as Lean states it |
| `P.Functionality.quoted` | metalogic | `Ty → RTy → Sentence Signature.pure` | for object types, the instance as a sentence |
| `P.Functionality.reflect` | both | the quoted sentence, read in the model on `e`, is `P.Functionality` at the types it denotes | the check on the quoter |
| `P.Functionality.schema` | metalogic | `AxiomSet Signature.pure` | the restricted form: all instances at closed types |
| `P.Functionality.listQuoted` | metalogic | `List Ty → RTy → Sentence Signature.pure` | the list instance, defined as the vectorized `quoted` |
| `P.Functionality.listSchema` | metalogic | `AxiomSet Signature.pure` | the list form: all list instances, the empty list included |
| `foo` (e.g. `Proofs.barcan_r_implies_functionality_r`) | shallow | `∀ {σ τ} [Ty σ] [Rel τ], P.Barcan σ → P.Functionality σ τ` | the record's proof, under the gate |
| `foo.quoted`, `foo.derivable` | metalogic | `Ty → RTy → Sentence …`; `∀ σ τ, Theorem C.axioms (foo.quoted σ τ)` | its statement as a sentence, and the translated derivation |
| `foo.rule` | metalogic | `∀ σ τ, C.Theorem (imp (P.Barcan.quoted σ) (P.Functionality.quoted σ τ))` | the derivation, keeping which instance yields which |
| `foo.entails` | metalogic | `P.Barcan.schema ⟹ P.Functionality.schema` | the arrow between restricted forms |
| `foo.listRule`, `foo.listEntails` | metalogic | the same with `listQuoted`, `listSchema` | the arrow between list forms |

## 9. Decisions for Cian

1. **D2**, schemas over closed types (recommended), or over all types (fewer edits, a
   fresh-variable condition wherever a list form is defined).
2. **D3** as described: in `Prop` a variable reads as `e`; in the action models it is
   valued by the premodel's `inner`, which already covers every type.
3. **Names**: `listQuoted`, `listSchema`, `listRule`, `listEntails`, "list form",
   "restricted form"; `Ty.var`; `Syntax/Vectorize.lean` and `Syntax/Vectorization.lean`.
4. **Record names**: the shallow record theorem keeps the map id and states the unary
   case; its `.listEntails` is the map's arrow. (Today such a theorem carries `_unary`.)
5. **Relational Choice**: vectorize inputs and outputs (two lists), or inputs only.
