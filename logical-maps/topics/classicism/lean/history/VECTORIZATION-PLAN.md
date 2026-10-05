# Plan: lists of types, and the vectorization theorem

*Written 1 October 2026, from the design agreed with Cian on 30 September – 1 October,
and a survey of the code that day. To be carried out phase by phase (§6); each phase ends
with a green build and its audit counts recorded in `HANDOFF.md`. An adversarial review
of the same day is folded in (D1–D5, D8, §4–§6); the decisions taken are in §9.*

## Status

- **Phases 0–4 done** (1 October). Type variables (Phase 1, commit `12e5100`); blocks
  (`Syntax/Blocks.lean`, Phase 2); the translation (`Syntax/Vectorize.lean`, Phase 3); the
  theorem (`Syntax/VectorizeDerivable.lean`, Phase 4), with its checks in
  `Certified/Vectorized.lean`: Barcan, Functionality and Relational Choice at `[]`, `[σ]`
  and `[e, t]` by `rfl`, and `barcan_r_implies_functionality_r` at every list. Audit counts
  unchanged throughout.
- **Phase 1b done** (1 October): "type parameter" for a Lean-bound type throughout the
  comments, docs and the checkers' messages, "type variable" kept for `Ty.var`;
  "principle", "instance", "schema" as in §2; "shallow core" for "kernel"; the README's
  section *Names: principles, instances and schemas*; `Classicism/README.md`'s module
  table, its `RawR` note and a section *Type variables and vectorization*.
- **Phase 5, first half done** (1 October): schemas over closed types (D2). The generator
  builds `∃ σ' …, σ' closed ∧ … ∧ a = P.quoted σ' …`, proves closedness of compound types
  from the parameters' (`closedProof`), and threads the conclusion's closedness through
  `foo.entails`. The hand-written proofs that unpack membership were fewer than estimated:
  ten sites in five files. Counts unchanged.
- **Phase 5 done** (1 October). `#classicism_schema` declares the list form of every
  principle with a Ty-parameter, 20 of 20: `listQuoted`, `listSchema`, `listQuoted_single`
  (the uniformity equation), `listSchema ⟹ schema`. The entailment audit declares
  `foo.listRule` and `foo.listEntails` for the 43 records with a Ty-parameter, and
  `#classicism_certify` declares `foo.listRule` (the Atomicity and BF-over-tuples steps
  have theirs). The audits report the counts. What the implementation settled:
  - The vectorized Ty-parameter is a principle's *first*; a second (Relational Choice's
    output, the only case) is passed through the type variable `var 1` assigned the
    one-element list of its type, so that the assignment mentions Ty-parameters only and
    a principle and a record over the same Ty-parameters vectorize along the same
    assignment. Rel-parameters are passed as themselves. This replaces D5's "a principle
    can name the ones to vectorize": no principle of the map needs more.
  - Where a closed parameter passes through a vectorization, its translation stands
    unreduced (`RTy.vec θ ρ`, `Ty.vec θ τ`), with the assignment of that vectorization.
    A list rule takes every parameter but the list closed, and each instance of the
    vectorized derivation is shown equal to its form by reducing both to normal form with
    those translations kept folded and rewriting them away by closedness
    (`RTy.vec_closed`, `Ty.vec_closed`); the tactic `classicism_vec_eq` does the same in a
    proof.
  - A record's instance becomes a list form when its first Ty-argument is the record's
    vectorized parameter, else a restricted instance at the translated types (the
    conclusion of `extensionality_r_implies_functionality_r` is Functionality's list form,
    its premise Extensionality at `σs ⇒* τ`). A list form's other arguments are
    translated too, so Functional Choice into `τ → t` implies Relational Choice into `τ`
    in list form, with Functional Choice's list form into `τ ⇒ t`.
  - Not done: a "readable form" of each list instance printed by the audit. The list
    instances are readable by construction (the readable translation), and
    `Certified/Vectorized.lean` checks three of them by `rfl` against the sentences
    written out.
- **Phase 6 done** (1 October). `Results/Lists.lean` proves `P.schema ⟹ P.listSchema`
  for all twenty principles with a list form, so with `P.listSchema ⟹ P.schema` each
  principle's restricted and list forms are equivalent. Thirteen by induction on the
  list, from fifteen two-element forms (`P.BarcanCons`, …) and their shallow steps,
  certified; Plenitude, its boxed form and Actual Profile by coding a tuple as an object
  (D8's sketches went through as written, Actual Profile by the lattice order, not the
  box); the four theorems of `C` from their list entailments. Counts unchanged but for
  the two new list forms of records and the new file's own line.
- **Phase 7 done** (1 October), as §7 has it, with these particulars:
  - `P.BarcanArgs`, `P.NecBarcanArgs`, their steps and inductions gone, and the three
    `Pointwise` laws only they used.
  - The cores that used BF over the tuple are unary, at `σ → t`. In `C5` they take `□ND`
    at `t` and get `□`BF at `σ` inside the proof (`gallin_c5_rigid_comprehension`, its
    boxed form, and the records `c5_and_actuality_imply_rigid_comprehension`,
    `c5_and_atomicity_imply_necessary_rigid_comprehension`, which lost `_unary`), so their
    vectorizations have no list premise; outside `C5`, BF at `σ`
    (`gallin_bf_weak_rigid_comprehension`), and BF over the list from BF.
  - A vectorized unary result reaches every relational type as `σs ⇒* t`
    (`schema_subset_args`, `Results/Lists.lean`).
  - Atomicity and its boxed form by the vectorized step, at `t`
    (`Results/Atomicity.lean`, `necAtomicity_of_at_t_necBarcan`).
  - `actuality_implies_actual_profile_r` lost `_unary`, its list form being the map's record
    (Phase 9's pilot, done here); `actuality_implies_persistent_comprehension_r_unary` gone,
    the shallow core at `τ` being the record at every arity.
  - `#classicism_entails` declares the list entailment of a record with a Ty-parameter,
    as the audit does.
  - The `_at_t` records stay for Phase 9.
  - Counts: 110 of 110 records certified (one fewer, its helper now counted as one), 42
    of 42 with a Ty-parameter in list form; the `Pointwise` audit twelve theorems fewer
    (the three laws as fields, at `Prop` and at arrows, and three helpers).
- **Phase 8 done** (1 October), as §8 has it:
  - `README.md`: the Names table has the converse row, `P.schema_entails_listSchema`.
  - `Classicism/README.md`: list forms, the equivalence and the results at every arity,
    and the Atomicity section's two routes to "for every `n`".
  - `HANDOFF.md` §3: the conventions for results at every arity and for list forms.
  - `VERIFICATION.md`: a section on what a list-form certificate rests on.
  - `MAP-SURVEY.md`: the counts after Phase 7.

  Next: Phase 9. Its pilot, Actual Profile, is done.
- **Phase 9 done** (1 October), but for Proposition 2.11, which Cian reports refuted by a
  countermodel. Twelve map results, each now a theorem at every arity in
  `Results/Arity.lean`:
  - **Boolean Completeness.** The records with Boolean Completeness as conclusion are
    proved at `σ → t` (in `Results/Records.lean`), where the greatest lower bound is the
    pointwise meet `λz. ∀Y. X*Y → Yz`, and vectorized:
    - Weak Rigid, Rigid and `□`Rigid Comprehension, and Extensionality, imply Boolean
      Completeness;
    - through them, `C5` with Actuality, or with Atomicity, does.
  - **Plenitude.** Propositions 2.14 and 2.16 are proved for output `σ' → t`, vectorized
    in `σ'`, every output type being `σs ⇒* t` (`schema_subset_args₂`). Through them,
    Extensionality and `C5` with Atomicity give Plenitude and `□`Plenitude.
  - **The haecceities.** Boolean Completeness and Actuality imply Weak Rigid
    Comprehension, by the least upper bound of the haecceities of the `X`s at `σ → t`.
    Actual Profile over the empty list is Actuality, by `rfl`.
  - **Records at `t`.** The `_at_t` records that the new ones supersede and nothing
    cites are gone; those cited by proofs at `t` stay.

  `MAP-SURVEY.md`: 160 of 230 map results proved in Lean, none in part.
- **Afterwards (2 October).** `Results/Atomicity.lean`, the step at a Rel-parameter
  certified in its own file, is folded into the pattern of the other results: the record
  `atomicity-t-and-bf-imply-atomicity` at `σ → t` in `Results/Records.lean`, at every
  arity in `Results/Arity.lean`.
- **What the implementation changed in the design**, all within the plan's intent:
  - Tuples are taken apart by their projections (`Terms.head`, `Terms.tail`) and every
    block operation recurses on the list of types, not on the tuple; so an operation on a
    tuple of known length computes even when the tuple is not written out, and a
    one-element tuple *is* its term for every operation. Without this the translation of
    `p ∧ q` was not `p' ∧ q'` on the nose.
  - The readable translation of D4 is not a pattern match on nested applications (Lean
    cannot compute such a match when the types are Lean variables, and cannot generate
    its equations): it is one `Term.rec` that returns, beside each subterm's translation,
    a *view* of it (the body of an abstraction; how to translate it applied, for `∀σ`,
    `∃σ`, `=σ`, `=σ a`). It inspects no type, and so computes on the quoter's output with
    type parameters in it. That it converts to the generic translation is a logical
    relation on views (`Ty.VecSound`).
  - The δ-rule at a block: each pointwise operation at `σs ⇒* ρ` converts to the operation
    at `ρ` applied pointwise over the block (`Conv.negR_block` and its six kin, in
    `Blocks.lean`), proved by induction on the list.
  - Holes are translated only when relational, which every hole for a formula is.
  - `Derivable.vecG` asks that the axioms vectorize to axioms and the logical part to the
    logical part; `C.Theorem.vec` and `C.TheoremMinus.vec` are the cases used.
  - A variable's translation is its block weakened past the blocks of the variables after
    it by *one* renaming, the weakenings composed before they act (`Var.vecRen`). Renamed
    twice, a block of unknown length does not compute to the block renamed once by the
    composite, and the list form of ND at `σ :: τ :: τs` and its two-element form at
    `τ :: τs`, which reach a variable across different binders, did not compute to the
    same sentence.
  - Not done, and not needed so far: the general statements that a one-element assignment
    is type substitution and that vectorizations compose. The first holds by `rfl` on every
    principle checked; the second has no use yet.

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
| **schema** | an axiom set, `AxiomSet`: the two words are synonyms (Cian, 2 October), as in the paper. The schema of a principle is the axiom set of all its instances, `P.Functionality.schema`; a **sentence schema**, such as No Pure Contingency, is schematic in a sentence rather than a type, defined by a condition on sentences with no principle behind it (`Syntax/SentenceSchemas.lean`) |
| **at a signature** | each of the map's principles is a schema at every signature `Σ` (Cian, 2 October): `P.X.schemaIn`, its instances read in `Σ`'s language; a signature-relative sentence schema at `Σ`; the pure version of one, `pureVersion S`, its schema at the pure signature read in `Σ`'s language (`Certified/Signatures.lean`) |
| **form** | a principle's official form or one equivalent to it on the map's principle page (the LUB form of Boolean Completeness, a list form), with a certificate of the equivalence (`Results/Forms.lean`, `Map.lean`) |
| **restricted form, list form** | of a principle with a Ty-parameter: the two schemas of §1, `P.X.schema` and `P.X.listSchema` |
| **type parameter** | a variable bound by Lean that stands for a type: in the shallow layer `σ : Type` with a marker (`[Ty σ]` a **Ty-parameter**, `[Rel τ]` a **Rel-parameter**); in the metalogic `σ : Meta.Ty` or `τ : Meta.RTy` |
| **type variable** | `Ty.var i`, a type *of the object language* about which nothing is known; part of the syntax, bound by nothing |
| **closed type** | a type with no type variable: the types of the paper's language |
| **assignment** | a map from type variables to lists of types |
| **vectorization** | the translation of terms, formulas and derivations along an assignment |
| **block** | the list of variables standing in for one variable whose type is vectorized |
| **shallow core** | the gated shallow theorem that carries a result's argument, certified by the translator as a rule; the metalogic turns it into the map's arrow, by composing with other entailments or by vectorizing. ("Kernel" is kept for Lean's kernel, the type checker.) |

## 3. Design decisions

**D1. Type variables in the object language.** `Meta.Ty` gets a third constructor,
`var : Nat → Ty`. A type variable is never relational, so it can be the type of a variable
or the argument type of an arrow but never a codomain: the object-language image of a
Ty-parameter. Application and λ always produce relational types, so the only terms of a
variable type are variables and signature constants. Signature constants are required to
have closed types (the theorem is stated for signatures that meet the condition, as the
pure signature trivially does), so every term of a variable type is a variable, which is
what lets a variable be split into a block.

**D2. Schemas range over closed types.** `Ty.Closed`/`RTy.Closed` (in `Prop`, with
`Closed (σ ⇒ ρ)` reducing to `Closed σ ∧ Closed ρ`, and lemmas for `⇒*` and for the
arguments of a relational type) say a type has no variable, and `#classicism_schema`
generates `P.X.schema = {P.X.quoted σ … | σ … closed}`. The map's schemas are about the
paper's types, and closedness keeps a list form's other parameters out of the
translation's way (D5). Rules and derivations (`foo.derivable`, `foo.rule`) keep
quantifying over all types: they are uniform, so they hold at type variables too, and that
is what Phase 4 uses. Cost: about 70 hand-written proofs unpack schema membership and take
the extra hypothesis, mostly to ignore it; and the generator's membership proofs
(`schemaMemBuild`, now `⟨args, rfl⟩`) must prove closedness of compound types built from
the parameters (`σ ⇒ ρ`, `σs ⇒* τ`, the arguments of a relational type). Nothing needs
closed schemas before the list forms, so this is its own phase, after the theorem
(Phase 5). The alternative, schemas over all types, is rejected: in a general premodel the
domain at a variable is a free field (`inner (var i)`), so consistency proofs from models
would gain genuine cases, and every list form would need a variable chosen fresh for its
other parameters.

**D3. What a type variable denotes.** Only closed sentences matter to the models, but
Lean's denotation functions are total, so a type variable needs a reading, and every
proof by cases on a type gains a case. In the reading in `Prop`, a variable denotes what
`e` denotes. In the action models nothing has to be chosen: the outer domain at a type is
built from the premodel's `inner : Ty → C ⥤ Type`, which already assigns an inner
domain to every type, so `RawT` at a variable is `(inner (.var i)).obj W`, exactly as at
`e`; a variable is valued by `inner`. The full and ideally full models build `inner` by
`Ty.rec`, and there a variable's case is `De`, the domain of `e`. In every proof by cases
the variable's case is the `e` case, with one exception: `Premodel.dflt`
(`Semantics/Action.lean`), the default element used where the paper's interpretation is
undefined, is built at `e` from the nonemptiness of `e`'s domain, and at a variable there
is nothing to build it from; it is only ever used at relational types, so it is restricted
to `RTy`. About 29 sites in all.

**D4. Vectorization acts along an assignment.** Every type goes to a list of types (a
one-element list except at an assigned variable), every term to a tuple of terms (a single
term except at an assigned variable, where it is the block). So several Ty-parameters can
be vectorized at once (no principle of the map needs it today, Relational Choice being
vectorized in its input only, but it costs nothing), the one-element case is type
substitution, and vectorizations compose.

**The block forms come out on the nose** (decided 1 October). The quoter writes `∀x:σ. φ`
as `all σ` applied to `λx. φ`; translated piece by piece, that would be the block
quantifier applied to a block abstraction, a β-redex, so readable list forms, the
uniformity equation and the steps of D8 would hold only up to conversion, needing a proved
conversion lemma per principle (the verified normalizer cannot supply them: it is stuck on
a list of unknown length). Instead the translation treats the binding forms as units:
`∀x:σ. φ`, `∃x:σ. φ` and `a = b` go directly to `∀x₁ … ∀xₙ. φ'`, `∃x₁ … ∃xₙ. φ'` and the
conjunction of identities; a bare `all σ`, `ex σ` or `eq σ` elsewhere goes to the block
constant. And a one-element block *is* the unvectorized form (identity over `[σ]` is
`x = y`, not `x = y ∧ ⊤`), so the one-element assignment is type substitution on the
nose. The cost is in the translation's definition: its application case looks at the raw
function for `all σ`, `ex σ`, `eq σ`.

**D5. A list form is defined, not written.** `P.X.listQuoted σs … := (P.X.quoted (var 0) …)`
vectorized along `0 ↦ σs`; it cannot be mis-stated. Every Ty-parameter is vectorized by
default, and a principle can name the ones to vectorize: Relational Choice names its input
σ only, its output τ staying a single type (Cian, 1 October). A
readable form in the block vocabulary is proved equal to it and printed by the audit, and
`P.X.quoted σ … = P.X.listQuoted [σ] …` (the *uniformity* of the quoted principle) holds
by computation, given that the other parameters are closed (`τ.vec θ = τ` for closed τ).

**D6. Generated, not hand-written.** `#classicism_schema` declares the list form of every
principle with a Ty-parameter, with `P.X.listSchema ⟹ P.X.schema`. `#classicism_certify`
declares `foo.listRule` and `foo.listEntails` for every record with a Ty-parameter. The
audits count them.

**D7. Results at every arity are unary proofs, vectorized.** A result about relations of
every arity is proved in the shallow layer at `σ → Prop` (or at `σ → τ`), in the paper's
own words, and vectorized. No shallow statement mentions a list, and no auxiliary
principle stands in for a list form. A result whose proof is pointwise at a relational
type and needs no list-form premise keeps its shallow core at a Rel-parameter τ, as now: it is
already at every arity.

**D8. From the restricted form to the list form.** Per principle:
- a theorem of `C` with a proof generic in the type (Modalized Functionality, Converse
  Barcan, Necessity of Identity, Broad Necessitism): vectorize its proof;
- otherwise an induction on the list, with two bases, the empty list (directly) and the
  one-element lists (where the list instance is the restricted instance, on the nose), and
  a step from a nonempty `σs` to `σ₁ :: σs`: the vectorization in `σ₂` of a shallow proof
  of the two-element case from restricted instances. Its shape follows the principle's
  parameters. Without a codomain (BF, ND, Existence, Tractarianism):
  `X σ₂ → X σ₁ → [X over σ₁, σ₂]`. With a relational codomain τ (Functionality, Functional
  Choice): `X σ₂ τ → X σ₁ (σ₂ → τ) → [X over σ₁, σ₂; τ]`. Relational Choice, whose output
  τ is any type: `X σ₂ τ → X σ₁ (σ₂ → τ → Prop) → [X over σ₁, σ₂; τ]`, the relation chosen
  for each `x₁` being the output of the second choice. Boxed principles by `K`;
- by coding a tuple as an object (Cian, 1 October): the tuple `x₁ … xₙ` is coded by
  `λR. R x₁ … xₙ`, of type `(σs ⇒* t) ⇒ t`, and the code is injective (apply two codes
  to `λy₁ … yₙ. y₁ = x₁ ∧ … ∧ yₙ = xₙ`). Then a unary shallow theorem relating the
  principle at the code type to the principle at σ, vectorized in σ, has as premise a
  restricted instance (at the closed type `(σs ⇒* t) ⇒ t`) and as conclusion the list
  form, with no induction. For **Plenitude**, where the two-element step would need
  Functionality: `Plenitude ((σ → Prop) → Prop) τ → Plenitude σ τ`. Given `S` functional
  in its first argument, `S' c z` holds when `c` is the code of some `x` with `S x z`,
  or `c` is no code and `z = ⊤_τ` (the default makes `S'` functional at non-codes too;
  τ is relational, so `⊤_τ` exists); Plenitude at the code type gives an operation `F`,
  and `λx. F (λR. R x)` represents `S`. For **Actual Profile**:
  `ActualProfile ((σ → Prop) → Prop) → ActualProfile σ`, transporting `Z` to
  `λc. ∃y. c = (λR. R y) ∧ Z y` and back under the box by the (necessary) injectivity
  of the code. Both arguments are sketches, to be checked in Lean.

**D9. The map.** Whether the map gets separate list-form nodes or annotations on the
principle records, the Lean side is the same.

## 4. Where things will live

| module | after the plan |
| --- | --- |
| `Syntax/Types.lean` | `Ty.var`; `Ty.Closed`, `RTy.Closed`; `RTy.arrs σs ρ`, written `σs ⇒* ρ`, with `RTy.ofArgs σs` defined as `σs ⇒* t` so that `ofArgs_args` plugs into list forms; the module doc on type variables |
| `Syntax/Blocks.lean` (new) | block contexts (a block is prepended by `List.reverseAux`, so that extending a context by a block needs no cast); tuples of terms `Terms Sig Γ σs`; `appBlock`, `lamBlock`, the block quantifiers and the conjunction of identities, with D4's one-element convention; their conversions; the block rules, derived (`allIBlock`, `allEBlock`, `exIBlock`, `exEBlock`, `reflBlock`, `llBlock`), here rather than in `Derivation.lean`, which does not import this file |
| `Syntax/Vectorize.lean` (new) | assignments; the translation of types, contexts, variables, terms and holes, with D4's binding forms; its laws with renaming and substitution; conversion preserved; one-element case and composition |
| `Syntax/VectorizeDerivable.lean` (new) | the theorem `Derivable.vec`, `Theorem.vec`; lifting a rule; the induction principle for list schemas (D8) |
| `Semantics/*` | a case for type variables (D3) |
| `Principles.lean` | docstring in the vocabulary of §2; `BarcanArgs`, `NecBarcanArgs` and the "Auxiliary schemas" section gone; `ActualProfile`'s docstring says the map's principle is its list form |
| `Pointwise.lean` | modal laws used only by the old shallow cores removed (§7) |
| `Results/Records.lean` | the shallow records, unary as now; `_unary` suffixes gone (their list forms are the map's records); `_at_t` records replaced where a unary proof is supplied |
| `Results/Lists.lean` (new) | restricted ⇔ list for every principle: the two-element steps, certified; the theorems of `C`; the inductions |
| `Results/Arity.lean` | the results at every arity: shallow cores needing a list-form premise restated at `σ → Prop` and vectorized; shallow cores at τ without one kept; the metalogic reduced to compositions |
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
| context Γ | each entry replaced by its list, prepended by `List.reverseAux` (innermost last within a block) |
| variable of an assigned type | its block of variables |
| `∀x:σ. φ`, `∃x:σ. φ` | `∀x₁ … ∀xₙ. φ'`, `∃x₁ … ∃xₙ. φ'` (D4) |
| `a = b` at σ | `a₁ = b₁ ∧ … ∧ aₙ = bₙ`, `⊤` if empty, the identity itself if one (D4) |
| `app F a` otherwise | `appBlock F' a'` (F applied to the whole tuple) |
| `lam b` | `lamBlock b'` |
| bare `all σ`, `ex σ`, `eq σ` | the block constants over σ's list |
| a pointwise constant at ρ | the same constant at ρ' |
| a signature constant | itself (its type is closed, D1) |

What has to be proved, in order: the translation commutes with renaming and with
substitution (the de Bruijn bookkeeping for blocks of variable length, done once here and
nowhere else); it preserves conversion (a β-, η- or δ-step at an assigned type becomes a
short chain of steps, as many as the block is long, or an η-step when it is empty); and
each rule of `Derivable` goes to its block version.
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

**Phase 1. The root change, in one commit** (D1, D3; `Closed` and `⇒*` from D2 and D4).
Every change to `Syntax/Types.lean` or `Syntax/Term.lean` makes the whole pipeline
rebuild, all 199 derivations included, so everything that touches them lands together.
- `Ty.var`; `beq` and decidable equality; `Ty.Closed`, `RTy.Closed` with their lemmas;
  `RTy.arrs`, and `RTy.ofArgs` redefined through it; `Ty.cases` (used nowhere) becomes
  three-way.
- Every explicit application of the mutual recursor gains an argument for the new
  constructor: `RTy.induction` in `Syntax/Types.lean`; the translator's generated
  induction for class laws (`ensureFieldInduction`, `Tools/Translate.lean`, where
  `RTy.rec` is applied to one argument per constructor), a trivial case since its motive
  on `Ty` is `True`; and `RawR`, `ActionFull`, `IntensionalFull`, `IdeallyFull` below.
  This is the translator's only change.
- Semantics, the variable case (D3), about 29 sites in 8 files:
  `Semantics/Denotation.lean` (`Ty.denote`, `Ty.denote_nonempty`);
  `Semantics/Action.lean` and `Semantics/Intensional.lean` (`RawR`, `RawT` and its `map`,
  the functoriality lemmas; `dflt` restricted to relational types);
  `Semantics/ActionFull.lean` (including `Ty.sizeOf_pos`), `Semantics/IntensionalFull.lean`,
  `Semantics/IdeallyFull.lean` (`inner` by `Ty.rec`, pinning); `Semantics/ActionFacts.lean`,
  `Semantics/IntensionalFacts.lean` (`cases σ`). `Models/` and `Strict/` have none.
- *Done when* the build is green and every audit count is unchanged.

**Phase 1b. The vocabulary, its own commit.** The terminology sweep of §2, in comments
and docs: "type variable" where a type parameter is meant (including `Syntax/Term.lean`'s
"stuck at a type variable", said of a type parameter); "schema" where a principle is meant;
"kernel" where a shallow core is meant (`Results/Arity.lean`, `README.md`,
`Classicism/README.md`, `MAP-SURVEY.md`, `HANDOFF.md`, `VERIFICATION.md`), "kernel" staying
for Lean's kernel. `Classicism/README.md` on `RawR` mentions the new recursor argument. The
README section of §8 for the objects that exist today.

**Phase 2. Blocks** (`Syntax/Blocks.lean`). Block contexts by `List.reverseAux`; `Terms`;
the block operations with D4's one-element convention; their conversions; the derived
block rules. Tests: each block rule at concrete lists of length 0, 1 and 2.

**Phase 3. The translation** (`Syntax/Vectorize.lean`). Assignments; translation of types,
contexts, variables, terms and holes, with D4's binding forms; renaming and substitution
laws; conversion preserved; one-element case is type substitution; composition. The
recursion has a shape new to this project (a tuple of terms as output, a look at the
function at each application), so its cost to Lean's kernel is measured on the certified
sentences before anything relies on evaluating it. Tests: Functionality, BF, Relational
Choice at `[]`, `[e]`, `[e, t]`, checked by `rfl`.

**Phase 4. The theorem** (`Syntax/VectorizeDerivable.lean`). `Derivable.vec`, `Theorem.vec`,
lifting a rule, for signatures with closed constant types; `#print axioms` shows nothing
beyond Lean's three. Tests: `Theorem.vec` applied to certified derivations at `[]`, `[e]`,
`[e, t]`, and the empty-list instances (BF at `[]` is `∀X:t. □X → □X`). A first use by
hand: the list form of `barcan_r_implies_functionality_r`.

**Phase 5. Closed schemas, then the pipeline.** First D2: `Closed` in the generated
schemas and the generator's membership proofs (closedness of compound types from the
parameters'); the hand-written proofs that unpack membership (about 70: `Contingency` 12,
`Incompatibilities` 9, `Arity` 8, `Consistency` 7, `Monoids` 7, `PossibilityDistinctness`
4, `Records` 4, `Pointed` 3, `Atomicity` 2). Then the list forms: `#classicism_schema`
declares `listQuoted`, `listSchema`, the uniformity equation, the readable form and
`listSchema ⟹ schema`; `#classicism_certify` declares `listRule`, `listEntails`;
`Certified/` regenerated; the audits count list forms. The README table (§8) gets its list
rows.

**Phase 6. Restricted ⇔ list.** `Results/Lists.lean`, per D8: the theorems of `C`; the
two-element steps, shaped by each principle's parameters, with the bases at `[]` and at
one-element lists (BF, ND, Tractarianism, Functionality, both Choices, their boxed forms,
and Existence, whose restricted instances are theorems of `C` proved by cases on the type,
so that its list form needs the step too); the generic induction. Plenitude and Actual
Profile by coding a tuple as an object (D8).

**Phase 7. Folding in** (§7): `BarcanArgs` and its inductions removed; the shallow cores that
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
a relational type and needs neither keeps its shallow core at a Rel-parameter τ, since it is
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
  the theorem vectorized and the old shallow core goes.
- Kept as shallow cores at τ (no tuple premise): `actual_iff`, `persistent_coext_of_actual`,
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
`Results/Arity.lean`, three serve only the shallow cores being restated (`incl_of_top_or`,
`top_boxAt_of_b`, `top_boxAt_of_neg`) and go if nothing else needs them; the other six
serve shallow cores that stay.

**`Results/Records.lean`.**
- `_unary` records: `c5_and_actuality_imply_rigid_comprehension_unary` and
  `c5_and_atomicity_imply_necessary_rigid_comprehension_unary` lose the suffix, their
  list forms being the map's records; `actuality_implies_actual_profile_r_unary` likewise
  (Phase 9's pilot: Actuality has no type parameter, so its list form is the map's record
  outright); `actuality_implies_persistent_comprehension_r_unary` goes, the shallow core at τ
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

## 9. Decisions

Taken on 1 October:

1. **D2**: schemas over closed types.
2. **D3** as described: in `Prop` a variable reads as `e`; in the action models it is
   valued by the premodel's `inner`; `dflt` restricted to relational types.
3. **D4**: the block forms on the nose, the translation treating `∀`, `∃` and `=` as units.
4. **Relational Choice**: its input only.

Still open, with the current choice:

5. **Names**: `listQuoted`, `listSchema`, `listRule`, `listEntails`, "list form",
   "restricted form"; `Ty.var`; `Syntax/Blocks.lean`, `Syntax/Vectorize.lean`,
   `Syntax/VectorizeDerivable.lean`.
6. **Record names**: the shallow record theorem keeps the map id and states the unary
   case; its `.listEntails` is the map's arrow. (Today such a theorem carries `_unary`.)
