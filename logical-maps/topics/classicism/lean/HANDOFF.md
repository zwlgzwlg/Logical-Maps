# Handoff: the Lean formalization of *Classicism*, as of 25 September 2026

Written for the next Claude instance working with Cian Dorr on this project, in a fresh
environment with none of the previous conversation. Read this first, then the two READMEs
it points to. Cian is the author of the paper being formalized (Bacon and Dorr,
*Classicism*) and of the Logical Map it serves; treat the mathematics as his and check
claims against the paper, not against memory.

## 1. What this is

Three things in one Lean 4 project, the Lean side of the map's Classicism topic,
`logical-maps/topics/classicism/lean/` in the Logical Maps repository (since 4 October;
before that `Cian/` in `zwlgzwlg/Lean-Classicism`, now retired, whose history the dated
entries below describe). How the map uses it, and the workflow after a Lean change:
`map/README.md`.

1. **The shallow layer** (`Classicism/*.lean`): the theory Classicism in ordinary Lean,
   under a *gate* that admits `propext` and `funext` only with closed arguments, which is
   exactly the rule of Equivalence and ξ. Its vocabulary (`Core`, `Equivalence`), a
   library (`Booleanism`, `Identities`, `Modal`, `Order`, `Comprehension`, `Pointwise`,
   `Lattice`), the map's principles (`Principles`), and one theorem per record of the map
   (`Results/Records.lean`).
2. **The metalogical layer** (`Syntax/`, `Semantics/`, `Results/`): the object language
   as an object of Lean — intrinsically typed de Bruijn terms over a signature, βηδ
   conversion, `Derivable Ax Δ p` (natural deduction closed under *Elimination*'s Subst
   rule, the axiom set an index), `C` as the logical axioms, entailment `Ax₁ ⟹ Ax₂`
   between schemas, the sentence schemas (No Pure Contingency, Distinctness,
   Possibility, Max), and the models: the reading in `Prop` (full Henkin models) and
   **action models** (the paper's §3) in two forms, the applicative form of the paper
   (`Semantics/Action*.lean`) and the **intensional** form of Cian's draft *Boolean
   Completeness without Rigid Comprehension* (`Semantics/Intensional*.lean`, the one the
   results cite and the one new models are built in), with soundness for all three.
3. **The tools** (`Tools/`, outputs in `Certified/`): the gate checker, the type-system
   check, the quoter (shallow statement → sentence, reflection by `rfl`), the
   **translator** (gated shallow proof → kernel-checked derivation), and the pipeline
   that reads each record theorem into an entailment between schemas
   (`#classicism_entails_audit`) or a rule between instances (`#classicism_certify`).

The main `README.md` describes the shape and the shallow theory; `Classicism/README.md`
is the metalogical layer's guide (design decisions, module table, how to write a
metalogical proof with object-level steps, the record of the 24 September experiment and
re-architecture). `Classicism/Strict/` is an earlier route (Appendix A on Lean proof
terms), kept as a sideline; nothing on the main route uses it. `VERIFICATION.md` is the
audit record.

## 2. Getting up to speed

- Toolchain `leanprover/lean4:v4.33.1`; Mathlib pinned to `v4.33.1` (only the action
  models use it). First build in a fresh environment: `lake exe cache get` (Mathlib's
  cache, else Mathlib compiles for hours), then `lake build` from `Cian/`. In the cloud
  session of 26 September the network policy blocked both the Lean release host and the
  Mathlib cache host; Lean came from the GitHub release tarball (`elan toolchain link`),
  and the part of Mathlib the project imports built from source in about ten minutes on
  four cores, 645 modules, so the whole of Mathlib is never needed. A warm full
  build is about 2–3 minutes for 806 jobs; the expensive parts are the certifying files
  in `Certified/` (the record derivations and entailments, seconds each now) and
  `Results/Arity.lean`.
- Run **one** heavy Lean process at a time; the translator can take gigabytes on a bad
  proof shape (see §7). Do not open a certifying file in an editor with the Lean server
  on: it redoes the work.
- The Logical Map is the enclosing repository, `zwlgzwlg/Logical-Maps` (Cian's fork
  `ciandorr/Logical-Maps`), topic `logical-maps/topics/classicism/`: `principles/*.yaml`, `results/*.yaml`,
  `models/*.yaml`, `background.md` (the definitions the map uses). Its own instructions
  are in `AGENTS.md` and `logical-maps/CLAUDE.md` there; `python3 scripts/pmap.py
  validate` before any commit to it; never hand-edit generated files; never set a
  record's `lean:` field by hand. Private notes and transcripts go in that repo's root
  `.private/` directory (ignored), never published.
- The paper's source (`Classicism (updated).tex`) is in Cian's Overleaf folder on his
  machine and is **read only**; in the cloud, ask Cian for the PDF or the relevant
  section. Propositions cited below are numbered as in the map's records.
- On Cian's machine the previous instance kept a verbatim transcript at
  `~/Dropbox/Logical-Maps/.private/ClaudeConversation-2026-09-20.md` and its memory at
  `~/.claude/projects/-Users-cd50-Dropbox-Logical-Maps/memory/`; the git log of `Cian/`
  (commit messages are descriptive) is the public history.

## 3. Conventions that matter

- **General lemmas live in the library** (Cian, 2 October). A lemma stating a broadly
  applicable property goes in the library module for its subject, not beside the result
  that first needs it: laws of `□` and `◇` in `Modal.lean`; the order, bounds and atoms, at
  `t`, at `σ → t` and at a relational type, in `Lattice.lean`; propositional identities in
  `Booleanism.lean`; pointwise laws at a Rel-parameter in `Pointwise.lean`. Look there before
  proving one. What stays with a result is what is particular to its proof: a closed
  one-step lemma shaped so that `nec%` can carry it under the box, or a construction such as
  a haecceity or a pinned property. `Results/` holds results, the top of `Classicism/` the
  library.
- **Words** (`README.md`, "Names"; `VECTORIZATION-PLAN.md` §2). A *principle* is a
  shallow definition indexed by types; an *instance* is one sentence; a *schema* is an
  axiom set, `AxiomSet` (the two words are synonyms, Cian, 2 October). A principle's
  schema is `P.X.schema`; a *sentence schema* (No Pure Contingency, Distinctness,
  Possibility) is schematic in a sentence and has no principle behind it. Each map
  principle is a schema at every signature (`Certified/Signatures.lean`): `P.X.schemaIn`;
  a signature-relative one at `Σ`; the pure version of one, `pureVersion S`, its schema at
  the pure signature read in `Σ`'s language. A principle's *forms* are the official one and
  those equivalent to it, the map's *variants*. A form is defined beside its principle in
  `Principles/<Category>.lean`, named `P.<Name><Form>` (`P.BarcanDual`,
  `P.BooleanCompletenessLUB`), and followed by the two directions, `P.<Name>.to_<form>` and
  `P.<Name>.of_<form>`, which the audits certify like records; the certificate
  `Map.<principle-id>.<form>` cites their `.entails`. The polyadic (list) forms are the
  exception: defined by vectorization, with their equivalences in `Results/Lists.lean`.
- **No formula quantifies over types.** A principle is a Lean `Prop` with its object
  types as parameters; a record is an implication between *instances*, with the types as
  parameters. The type-system check (`#classicism_types_audit`) enforces it; the quoter
  depends on it.
- **A law that holds by recursion on the structure of a type is a class field**
  (`Rel`, `Order`, `Pointwise`): proved at `Prop` and at `σ → τ`, and the translator
  derives it for every object type by induction. The shallow layer has no induction on
  types; the metalogical layer does (`RTy.induction`).
- **The paper's symbols change no terms** (`Classicism/Paper.lean`): `⊆` for `incl` is
  always on (`Core.lean`); `≤` for `Rel.le` at every type, `∧ ∨ ¬ ⊤ ⊥` at relational
  types and `≡` for coextension need `import Classicism.Paper` and `open Paper` inside
  `namespace Classicism`. The connectives are type-directed elaborators, `And`/`Or`/`Not`
  at `Prop` (including in type positions, whose expected type is `Sort ?u`) and `Rel.and`
  etc. elsewhere; so a connective *at `Prop`* that must stay `Rel.and` (the `Prop`
  instance lemmas of `Pointwise`) is written with the prefix name. Inside the scope `≤` is
  always `Rel.le`, also at `Prop`; outside it `≤` at `Prop` is `entails`, the same relation
  by definition, which `Tractarianism` is stated with, so the lemmas about it write
  `entails` by name. Since 28 September the shallow library (`Lattice`, `Order`, `Modal`,
  `Comprehension`, `Pointwise`), `Results/Records/` and, since 4 October, `Principles/`
  open the scope and use the symbols, except `Principles/Coarse.lean`, where
  `Tractarianism` would change (the principles' terms were checked unchanged). Named predicates from the paper are used where the
  unfolded form was written: `GLB`, `UB`, `Atom`, `Persistent`, and `ActualWorld w`
  (`w ∧ ∀q. q → w ≤ q`, in `Lattice.lean`). Do not open the scope in a file that opens the
  strict algebra or imports Mathlib.
- **`λ … ↦` for terms, `fun … =>` for proofs** (Cian's trial convention, 28 September): in
  the shallow layer an abstraction whose value is a term of a type in `Type` (a property,
  a relation, a proposition-valued function) is written `λ x ↦ …`; one that is a proof
  keeps `fun h => …`. Both are the same syntax to Lean. `scripts/FunKinds.lean` decides
  each `fun` in a file from the elaborated types:
  `lake env lean --run scripts/FunKinds.lean <file> <module>` prints `term`/`proof` and
  the byte offsets of `fun` and `=>`.
  `Results/Records.lean` shows the style. `simp only` with the library's closed `_eq`
  identities is admissible since 25 September (`Tools/Check.lean`, `gatedRules`).
- **Record theorems** in `Results/Records/` (a file per topic, `Results/Records.lean`
  imports them all) are named after the record id with
  hyphens as underscores, one per record, docstring naming the record and the argument's
  source. Helper lemmas must not look like records (a statement whose head is a
  `Classicism.P` principle is read as one): state them unfolded.
- **Object-level steps in a metalogical proof** are shallow lemmas proved with ordinary
  tactics, certified in the same file (`#classicism_derive` for a lemma, `#classicism_certify`
  for a record-shaped one, giving `foo.derivable` / `foo.rule`, and `foo.listRule` when it
  has a Ty-parameter), and applied with
  `Theorem.ofCMinus`, `Theorem.mp`, `Derivable.allEβ` (one binder at a sentence),
  `Derivable.allE₂β` (two binders at once), and `C.TheoremMinus.ofPure` to carry a
  lemma certified at `Signature.pure` into a signature. `Results/Arity.lean` and
  `Results/SentenceSchemas/*.lean` are the models to imitate.
- **A result at every arity is a unary proof, vectorized** (`VECTORIZATION-PLAN.md`, D7).
  Prove it in the shallow layer at `σ` or `σ → t`, from restricted instances, and
  certify it. `#classicism_certify` gives `foo.listRule`, `#classicism_entails` or the
  audit `foo.listEntails`. Then compose:
  - with `P.schema_entails_listSchema` (`Results/Lists.lean`) for a list premise;
  - with `schema_subset_args` for a conclusion over relational types.

  In `C5`, take `□ND` at `t` and get `□`BF at `σ` inside the proof, so that no list
  premise arises. A result whose proof is pointwise reasoning at a relational type keeps
  its shallow core at a Rel-parameter. No shallow statement mentions a list, and no
  auxiliary principle stands in for a list form.
- **List forms are never written by hand**: `P.listQuoted` is the vectorization of
  `P.quoted`. Where two vectorized sentences differ only in the translations of closed
  parameters (`RTy.vec θ ρ`, `Ty.vec θ τ`), `classicism_vec_eq` proves them equal, and
  `Theorem.cast` moves a theorem across the equation.
- Every metalogical result about the map's principles is at `Signature.pure`, where
  `P.schema` lives; sentence schemas are stated for any `Sig`. The map's boxed
  principles are `AxiomSet.box P.schema`; the shallow layer also has `NecBarcanT`,
  `NecNecessityOfDistinctnessT`, `NecActuality`, `NecBooleanCompleteness τ`,
  `NecRigidComprehension τ`, `NecAtomicity τ` where records need them.
- Commit messages start `Cian:` and end with the `Co-Authored-By` line the environment
  supplies. Preserve Cian's text, claims and citations unless the change concerns them.

## 4. Where things stand

- Shallow layer: 67 record theorems, all pass the gate and the type check, all 67
  certified as entailments between schemas at build time (`Certified/Entailed.lean`);
  46 principles quoted into schemas (`Certified/Schemas.lean`); `Results/Records.lean`
  (137 theorems) derives in the object language in seconds at build time.
- **§§2.1–2.3, the `C5` results** (28 September), in `Results/Records.lean`, section
  "`C5`", with `□ND_t` (`NecNecessityOfDistinctnessT`) as the `C5` premise: Proposition
  2.3 (`□ND_t ⇒ BF_σ`, Lemmon's proof), 2.4 (`ND ∧ BF ⇒ □ND`, at `σ` and at `t`), `□ND_t`
  gives `ND_σ`, `□ND_σ`, `□BF_σ`; n. 41 (in `C5` persistent is inextensible); 2.10
  (Actuality ⇒ RC at `σ → t`); 2.5 both ways (Actuality ⇒ BC at `t`; BC at `t → t` ⇒
  Actuality, through 2.14 and 2.15); 2.14 (BC at `σ → t` ⇒ Plenitude `σ t`); 2.6 all
  ways (Atomicity ⇒ `□`Actuality, `□`BC, `□`RC; `□`Actuality, `□`BC, `□`RC ⇒
  Atomicity); 2.12 (RC ∧ BF ⇒ `□BF`); 2.16 (RC ∧ ND ⇒ Plenitude). Two principles added,
  `NecNecessityOfDistinctness σ` and `NecBarcan σ`. Record names were checked against the map
  on 28 September (`MAP-SURVEY.md`): theorems proving a map record in full carry its id,
  and so do those proved at `σ` or `σ → t` whose list form is the map's record; those
  proving only the instances at `t` carry the id with `_at_t`, and their certificates
  claim no more; eight record-shaped theorems the map lacks keep descriptive names. **Proposition 2.11**
  (`□`Atomicity + BC + BF ⇒ RC) **is refuted**: Cian reports a countermodel (1 October),
  so it is not to be proved. Its n. 42, part
  (iv), has two gaps. (a) It boxes a claim pointwise in `z` with `BF` where `□BF` would be
  needed; Cian agreed (28 September) and asked for the `□BF` version. (b) Its "without loss
  of generality" step needs `w″` (the GLB of the `p` with `w ≤ (p = w′)`) to be identical
  to `w′` wherever `w` holds, so that it is still possible and below `X*z ∧ ¬Yz` there; the
  premises do not give this, `□BF` does not help, and a propositional structure where it
  fails is sketched in `VERIFICATION.md`, §"Proposition 2.11". What is proved
  (`rigid_comprehension_r_of_restriction`, a helper in `Records.lean`): Actuality + BC at
  `σ → t` + BF at the property type + a *restriction principle* ⇒ RC at `σ → t`, with the
  paper's `X*`. The restriction principle says: for any `p`, `q` there is an `r` identical
  to `q` wherever `p` holds and entailing everything `p` makes `q` entail (`q` restricted
  to what is accessible from the `p`-worlds). It holds in `C5` (`restriction_of_box_b`,
  `r := q ∧ ◇p`). Restructured this way, gap (a) disappears (BF at @ suffices); gap (b) is
  exactly whether `□`Atomicity + BC + (`□`)BF give the restriction principle. Open; with
  Cian and his coauthor.
- Metalogical results (`Results/`): Atomicity (t) + BF ⇒ Atomicity (induction on the
  type, the step certified); `Results/SentenceSchemas/`: Distinctness ⇔ Possibility relative to
  any theory over any signature; `NPC ∪ Ax ⟹ Ax.box` for every pure schema (the map's
  twenty NPC records as one theorem); the arrows among No Contingency, NPC, signature B,
  pure B, from B and from the Fregean Axiom; the incompatibilities of Possibility,
  Distinctness and Max with the necessitation of anything refutable in a model, with
  instances from the two M-set models (`□BF_t`, `□`Tractarianism, `□ND_t`), Maximalist
  Classicism against ND, Possibility against NPC and against pure B; the consistency
  facts behind them (`Results/SentenceSchemas/README.md` lists the records covered and not).
- Semantics: `Prop` is a model (`Denotation.lean`); action premodels and models with
  soundness (`Action.lean`, `ActionSoundness.lean`); full action models are models
  (`ActionFull.lean`); truncation, the clauses for `□`/`◇`, ND iff injective, BF if
  surjective, the Fregean Axiom criterion (`ActionFacts.lean`); properties of models and
  NPC in every one-object model (`ActionProperties.lean`); the two M-set models on the
  two-element monoids with their verdicts (`ActionExamples.lean`). All of that again in
  the **intensional form** (26 September; `Intensional.lean`, `IntensionalSoundness.lean`,
  `IntensionalFacts.lean`, `IntensionalFull.lean`, `IntensionalProperties.lean`,
  `IntensionalExamples.lean`; `Classicism/README.md`, §"Intensional action models"): a
  relation is a set of tuples with the arrow last, transport and η hold in every
  premodel, the Boolean operations are set operations at every type, a full premodel is
  a model in two lines. `Results/Consistency/Consistency.lean` cites the intensional models;
  the applicative modules stay as formalized mathematics, nothing on the route to a
  certificate using them. Consistency and non-theoremhood from a model:
  `Consistent.of_model` (intensional; `Consistent.of_action_model` for the applicative
  form), `not_theorem_of_model`, `Consistent.of_interp`.
- **Appendix D** (26 September, later): `Semantics/IdeallyFull.lean` has the technique
  (pinning, the finitely pinned subaction, the ideally full domains, `Premodel.ideal`) and
  Proposition D.4 as an induction on terms (`sem_pinned`, `isModel_of_pinned`,
  `ideal_isModel`); `Models/Permutations.lean` is Part 1, the permutation model, with
  `□ND`, `□BF`, `¬`Actuality, Atomlessness, `¬`Atomicity (`t`) as theorems about the
  quoted principles, feeding `Consistency.lean` and two new maximalist incompatibilities
  (`□`Actuality, `□`Atomicity). See `Classicism/README.md`, §"Appendix D".
- **Appendix D, D.6 and Parts 2 to 8** (26 September, later still): Proposition D.6
  (`ideal_bf_of_surjective`); `Models/MonoidModel.lean`, the model over any monoid acting
  on `ℕ` with the verdicts parametrized by the deciding fact about the monoid;
  `Models/Monoids.lean`, the seven monoids of Parts 2 to 8 as submonoids of
  `Function.End ℕ` and every verdict of the paper's table except Boolean Completeness;
  `Consistency.lean` has a section per part (what holds, what fails, the package
  consistent, the failing principles not theorems of the holding ones), with the
  necessitations left to No Pure Contingency (`holdsAx_npc`, every one-object model) and
  `npc_union_entails_box`. `Models/README.md` has the table and Cian's requested survey
  of the two-object variants (not formalized). Not done: the Boolean Completeness
  failures, the two-object models at the end of the appendix, the symmetric model.
- Latest batch (25 Sep): Actuality, `□`Actuality, Actual Profile (unary), Boolean
  Completeness (`τ`, `t`, boxed), Atomlessness, Plenitude defined; bounds `LB/GLB/UB/LUB`
  and the order at `t` as identities in `Lattice.lean`; seventeen records among them,
  Atomicity, comprehension and Plenitude, including Proposition 2.7 (Atomicity (t) + BF
  ⇒ `□`Actuality). Constructions are at `t` or `σ → t`; the uniform statement over
  arities is metalogical work not yet done.
- A finding Cian is acting on: the map's `actuality-implies-inextensible-comprehension-r`
  only yields *weak* inextensibility (the box over the condition is not derivable from
  Actuality alone); Lean has `actuality_implies_weakly_inextensible_comprehension`, the
  record is not stated. Cian said he will fix the map.

## 4a. Tuple layer: running log

(Written as the work goes; newest last.)

- 28 Sep, night: started. Reading `Tools/Translate.lean`, `Tools/Quote.lean`,
  `Tools/TypeSystem.lean` to see where tuple types would enter.
- **Design finding (for the morning).** Literal tuple types, as proposed, would need a
  tuple variable of unknown arity to become a *block* of object variables: `Term`,
  renaming, substitution and the verified normalizer would all need contexts
  `args ρ ++ Γ` whose de Bruijn indices depend on an unknown arity. The existing design
  deliberately avoids that: the relational operations at a type parameter are *constants*
  of the syntax (`negR ρ`, `inclR ρ`, …) with a δ-rule each, and their laws are derived
  by induction on the type. So I have not built tuple types. Instead, the route that
  fits the architecture, tried tonight:
  (1) most arity proofs use a tuple only as `∀x̄ (… X x̄ …)` with one tuple at a time,
  which the existing pointwise operations already express; what they lacked was BF over
  a whole tuple, now the auxiliary schema `P.BarcanArgs` (and its box), derived from BF by
  one certified induction (`Results/Arity.lean`); (2) a few pointwise *modal* laws, added
  to `Pointwise` (a field with a `Prop` proof and an arrow proof; the translator derives
  each for every type automatically); (3) shallow cores at a type parameter `τ`, certified, and
  composed in the metalogic with certified entailments already there. **Result: 7 map
  results proved at every arity in one evening, with no per-result induction.**
  What this route cannot do: results that need a *second* tuple or a tuple as an object
  (the haecceity `λȳ. ȳ = x̄`: Actual Profile, Extensionality ⇒ Atomicity by haecceities,
  the LUB of haecceities in Weak RC and Prop. 2.11), and the Boolean Completeness family,
  which needs a pointwise *meet* `λz̄. ∀Y. F Y → Y[z̄]` at a type parameter, i.e. one new
  syntax constant (a pointwise universal quantifier `allR σ ρ : (σ ⇒ ρ) ⇒ ρ`), touching
  ~20 files (every `match` on `Term`, both semantics' soundness). Questions for Cian: is
  the constant worth adding (it would unlock ~8 BC/Plenitude results), and do the
  haecceity results justify real tuple types later?
- **Done by the end of the night** (all certified; full build green; 157 of 157 record
  theorems derived, 73 of 73 certified). In `Results/Arity.lean`, the map's records at
  every arity, each an entailment between the map's schemas:
  `actuality-implies-persistent-comprehension-r`, `c5-and-actuality-imply-rigid-comprehension`,
  `gallin-comprehension-and-bf-imply-weak-rigid-comprehension`,
  `gallin-comprehension-and-bf-imply-rigid-comprehension`,
  `c5-and-atomicity-imply-necessary-rigid-comprehension`,
  `c5-and-necessary-actuality-imply-atomicity`, `c5-and-necessary-completeness-imply-atomicity`,
  `c5-and-atomicity-imply-necessary-atomicity`, `extensionality-r-implies-atomicity-r`,
  `necessary-gallin-comprehension-implies-necessary-rigid-comprehension`,
  `necessary-plenitude-r-implies-atomicity-r`, `necessary-plenitude-r-implies-necessary-atomicity-r`;
  and the auxiliary inductions `barcanArgs_of_barcan`, `necBarcanArgs_of_necBarcan`,
  `necAtomicity_of_at_t_necBarcan`. In `Results/Records.lean`, six routine records they
  needed: `fregean-axiom-implies-necessary-distinctness-necessary-r`,
  `necessary-gallin-comprehension-implies-{gallin-comprehension, necessary-nd}`,
  `necessary-plenitude-r-implies-{plenitude-r, necessary-distinctness-necessary-r,
  necessary-actuality}`. Two principles added, `NecGallinExtensionalComprehension` and
  `NecPlenitude`; two auxiliary schemas, `BarcanArgs` and `NecBarcanArgs`; six modal laws
  in `Pointwise`. Coverage (`MAP-SURVEY.md`): 104 of 230 map results proved in Lean, 9 in
  part; sweet spot 15 of 40.
- **The bulk track, later the same night.** 38 routine records added to
  `Results/Records.lean` (specializations to `t`, `T`, necessitations with `K`, the choice
  and Fregean records, the Strong Leibniz records at `t`, Broad Necessitism, the
  distinctness-preserving collapse), and four more at every arity in `Results/Arity.lean`
  (`very-weak-rigid-comprehension-r-implies-weak-rigid-comprehension-r`,
  `extensionality-r-implies-rigid-comprehension-r`, `c5-and-persistent-comprehension-imply-gallin`,
  `c5-and-necessary-rigid-comprehension-imply-necessary-gallin-comprehension`), with three
  more `Pointwise` laws and sixteen principles (the boxed forms, `SWorld` and the Strong
  Leibniz principles, `BoxNe` and the collapse, Broad Necessitism). The record audits:
  199 of 199 derived, 111 of 111 certified; full build green. **Coverage: 147 of 230 map
  results proved in Lean, 9 in part** (routine per-type 96 of 112, sentence schemas 27 of
  48, sweet spot 15 of 40, metalogic 9 of 26). The 15 routine results left need the
  finite-cardinality vocabulary (the Infinity principles, Countable Boolean Completeness),
  lattice laws at a type parameter (Strong Leibniz and Atomicity at every arity), tuples
  (Actual Profile), or a decision (Actuality ⇒ Inextensible Comprehension, where the map's
  claim is in doubt).
- **A correction to the coverage counts of earlier in the day.** A record theorem named
  exactly by a map id was counted as proving the record in full; six of them prove only
  the instances at `t` or for relations `σ → t` (their certificates, correctly, say so).
  They are renamed with `_at_t` / `_unary`, and the counts above are recomputed.
- Lessons: a law proved as a bare `Or.inr` or `id` (unapplied) is not read by the
  translator ("no rule for the constant Or.inr"); write `fun h => Or.inr h`. A `/-! -/`
  comment inside a `class` body is a parse error. The paper-notation elaborator cannot
  type `¬ constP w ∨ X` when nothing fixes the type of `constP w`; write `Rel.or (Rel.neg
  (constP w)) X` or ascribe.
- **Closed, 1 October.** Superseded by the vectorization plan, `VECTORIZATION-PLAN.md`,
  agreed with Cian on 30 September – 1 October. Both questions above are answered there:
  the pointwise meet at `σ → t` is an ordinary λ-term and vectorizes to every arity, and
  tuples as objects (the haecceities) come from vectorizing the unary proofs, so neither a
  new syntax constant nor tuple types are needed. `BarcanArgs` and the inductions of
  `Results/Arity.lean` are folded into the general mechanism (plan, §7).

## 5. Agenda, in the order Cian set

**First: the vectorization plan**, `VECTORIZATION-PLAN.md` (agreed 1 October): type
variables in the object language, the vectorization theorem, the list form of every
principle with a `Ty`-parameter, and the results at every arity as vectorized unary
proofs. It supersedes item 0's tuple-types proposal below, which is kept as history.
**Status:** Phases 0–4 done (the plan's "Status" section): type variables, blocks, the
translation and the vectorization theorem (`C.Theorem.vec`), checked on three principles
and one certified arrow (`Certified/Vectorized.lean`). Audit counts unchanged: 199 of 199
record theorems derived, 111 of 111 certified. Phase 1b (the vocabulary sweep) done too.
Phase 5 done: schemas over closed types; list forms of the 20 principles with a
Ty-parameter and of every record with one (`foo.listEntails`). Phase 6 done: each of the
20 principles' restricted form entails its list form (`Results/Lists.lean`), so the two
are equivalent. Phase 7 done: `BarcanArgs` gone; the results at every arity are unary
proofs vectorized, Atomicity by its vectorized step; `actuality-implies-actual-profile-r`
proved in full as a list form (148 of 230 map results). Phase 8 done: the documentation
(`VERIFICATION.md` says what a list-form certificate rests on). Phase 9 done: the Boolean
Completeness and Plenitude records at every arity, BC + Actuality ⇒ WRC by haecceities,
Actual Profile ⇒ Actuality (160 of 230 map results, none in part). Proposition 2.11 is
refuted (Cian, 1 October). Then the map's additions of 25–28 September
(`zwlgzwlg/Logical-Maps` at 8edffb3): nine principles (Transversal, Transversal Choice,
Weakly Inextensible Comprehension, Vicinity, their boxed forms, Modalized Plenitude) and
34 of their results, in `Results/Records.lean`, `Results/Arity.lean` and
`Results/SentenceSchemas/Contingency.lean`; `MAP-SURVEY.md` refreshed against the 270-result map:
195 proved. Then the Strong Leibniz records: seven of the eight proved, unary at `σ → t`
with their every-arity forms in `Results/Arity.lean` (202 of 270). Open: the eighth,
`necessary-strong-leibniz-and-rigid-comprehension-imply-necessary-bf-t` (Bacon's Theorem
8.2, not routine), and the two `c5-and-atomicity(-t)-imply-no-pure-contingency` records.
Then (2 October) `Results/Atomicity.lean` folded into Records and Arity; "schema" made a
synonym of axiom set, `Results/Schemas/` split into `Results/SentenceSchemas/` and
`Results/Consistency/`; and a draft of the map's Lean side (`map/README.md`): the map's
statements generated by its own generator (`Classicism/Statements.lean`), a certificate for
each of the 202 results (`Classicism/Map.lean`, the `lean_ref`s), and an index of where each
certificate and its proofs are (`map/index.json`), for the viewer's links. Then: the
statements without the consistency hypothesis (an incompatibility ends in `¬ Consistent
Ax`), principles at every signature (`Certified/Signatures.lean`), and the forms, piloted
with Boolean Completeness's LUB form (`Results/Forms.lean`), with the change to the map's
build script they need in `map/pmap.patch`. Then general lemmas moved to the library
(§3, the policy), and the list forms of 20 principles made forms; then Modalized
Plenitude's list form, a theorem of `C` by induction on the list (with `C.Theorem.nec`,
Necessitation, now in `Syntax/Entailment.lean`), and `modal-b-implies-pure-b-r` certified
(203 of 270). Next on that front, in the map repository: apply the patch; `lean-check` for
the forms; the viewer to use the index; the map's axiom list and the three certificates
resting on `e_exists`. Transversal and Transversal Choice's list forms wait (Cian, 2
October: what the list form means there is not yet settled).

**Night of 2 October** (Cian's items 2–4 and the map's principles; `VERIFICATION.md` has a
section per step). `boxImp` renamed `incl`. **Conservativity** of `C(Σ)` over `C`
(`Syntax/Conservativity.lean`), syntactic, for closed signatures; with it the two
cross-signature results and `npc Σ = pureVersion noContingency`. The statements now range
over `Signature.Admitted` signatures: closed, and with a constant of a type other than `e`,
the Background's standing assumption. **Principles:** 95 of the map's 97 have a
`lean_def`; new are the Axioms of Infinity and Possible Infinity at `e` and `t`, Countable
Boolean Completeness (`Cardinality.lean`, `Principles.lean`), Witnessed Possibility and its
kin, Logical Necessity, Modal Freedom, Separated Structure, Independence, Possibility+
(pure and for a signature), Ordinary Comprehension, the Infinity schemas and Strong
Possibility (`Syntax/`). General Separated Structure and the Necessity of Arithmetic remain
(their definitions are not obvious: a bijection of constants to variables, and the class
of arithmetical sentences). **Results:** 234 of 270 certified: from item 4,
`maximalist-distinctness-incompatible-with-necessary-functionality-r` and
`-necessary-rigid-comprehension-r`; and 29 results about the new principles, the
incompatibilities that need a constant among them. **Not done from item 4:** Bacon's
Theorem 8.2 and C5 + Atomicity ⇒ No Pure Contingency (§8); the maximalist incompatibility
with Rigid Comprehension unboxed is Gödel.

**4 October** (with Cian, before moving the project into the map). The branch merged into
`main`. `Principles.lean` and `Results/Records.lean` split by the map's categories
(`Principles/<Category>.lean`, `Results/Records/<Topic>.lean`, each old path now an
umbrella); the principles in the paper's notation, their terms checked unchanged. The
**forms convention** (§3, "Words", and `Principles.lean`, §"Forms"): a form is defined
beside its principle and followed by `P.X.to_<form>` / `P.X.of_<form>`. Written: the dual
forms of the 26 principles with a shallow statement and a dual on the map, and the LUB
forms of Boolean Completeness at `t` and boxed; 58 theorems, all certified. For them,
`Pointwise` gained two classical fields (`incl_neg_intro`, `incl_neg_neg`) and
`Lattice.lean` the order laws at a type parameter (`le_antisymm_rel`, `atom_le_or_le_neg_rel`,
…). Not yet: the duals of the sentence schemas (in `Syntax/`), the GLB form of Countable
Boolean Completeness (countability of `X¬`), the map side (the map now calls forms
`variants`, and its polyadic forms are Lean's `list` forms), and the certificates in
`Map.lean` for the new forms, which wait on regenerating `Statements.lean`.

0. **Night of 28 September: the arity results, and a design question for the morning.**
   Cian approved the plan below (tuple types in the shallow layer) and asked that, if it
   turned out to be a mess, we discuss it in the morning. It did not become a mess, but
   it did not go as planned: literal tuple types were not built, for the reason in §4a,
   and a route that fits the existing architecture proved 12 of the arity results at
   every arity instead (`Results/Arity.lean`); the bulk track then added 42 routine
   results, for 147 of 230 map results proved in Lean. **Read §4a first**; it ends with the two
   questions for Cian.
   **Next (plan of 28 September, `MAP-SURVEY.md` for the counts).** Of the map's 230
   Classicism results, 92 are proved in Lean and 8 in part. The sweet spot, a shallow core
   with an induction on the arity of a relational type, has 23 results, 8 of them
   proved only at `t` or `σ → t`. Doing each by the Atomicity pattern (a step lemma from
   `τ` to `σ → τ`, `#classicism_certify`, an induction on `RTy`) works but is unergonomic:
   each proof must be recast as a step, often with a strengthened invariant. Cian's
   proposal: **tuple types in the shallow layer.** A class `Tup A` with instances `Unit`
   and `σ × A`; a relation with argument tuple `A` is `A → Prop`, and the paper's `X[x̄]`,
   `∀x̄`, `λx̄`, `x̄ = ȳ` are Lean's own application, quantifier, abstraction and equality at
   `A`. Since `RTy` is literally a list of argument types, a tuple type is an `RTy` and
   `A → Prop` is that relational type: the quoter maps a tuple parameter to an `RTy`
   parameter, so the schemas are the map's. The translator uncurries: `∀ p : σ × A` to
   `∀x ∀ā`, application to a pair to iterated application, equality of tuples to the
   conjunction of component identities. At a tuple *variable* it emits object-level
   combinators (`∀` over an argument list, application to a list of variables, identity of
   lists) whose rules (intro and elimination, β, Leibniz, and BF at every component giving
   BF over the tuple) are metalogical lemmas proved once by induction on the list, as the
   laws of `Rel`, `Order` and `Pointwise` are derived now. Then the 23 results become
   per-type proofs in the paper's own words, and each is certified by the existing
   pipeline with no per-result induction. Steps: (i) the `Tup` class and the combinator
   lemmas; (ii) the quoter and translator cases, with `#classicism_types` admitting tuple
   parameters; (iii) a pilot: `actuality-implies-actual-profile-r` (also done once by the
   Atomicity pattern, for comparison), `gallin-comprehension-and-bf-imply-weak-rigid-comprehension`
   (BF over a tuple), `c5-and-actuality-imply-rigid-comprehension` (upgrading a `_unary`
   theorem); (iv) the rest of the 23, then the boxed `C5` family by necessitation. In
   parallel and cheap: the 64 per-type routine results not yet in Lean, mostly one-line
   (T, specialization, necessitation with K and 4); splitting `Results/Records.lean` into
   topic modules first would let several agents do them at once. Later: the 21 remaining
   sentence-schema results need schemas with substitution of constants (the Witnessed
   Possibility family), and the 17 remaining metalogic results need models, mostly the
   coalesced sums of Appendix E.

1. **Appendix D models** (Cian's stated next target; "geared towards showing things
   about Actuality, Boolean Completeness and Atomicity", and "arguably easier than the
   coalesced sums"). Build the *ideally full* action models: a category of sets and
   functions, `-^e` the identity action, `W^‡` the finite subsets of `W`, domains the
   elements pinned down by some finite set; the proposition that an ideally full premodel
   is a model, Proposition D.4. In the intensional form (Cian's decision of 26
   September; the paper's combinator route is not needed, he says) this is an induction
   on terms whose cases are the draft's closure lemma, pinning preserved by the action of
   arrows and by application; a full premodel needed no such induction, an ideally full
   one does. Cian's draft `readings/BCsansRC.tex` has the setup, the closure lemma, and
   the further *symmetric* ideally-full models, which he is not asking for yet but whose
   shape the definitions should leave room for. **Done on 26 September: the technique,
   D.4, D.6, and Parts 1 to 8** (see §4). **Done on 28 September: the Boolean
   Completeness failures of all eight parts, `BF` without `□BF`, and the eight parts
   with a point adjoined** (see §4). Remaining: the symmetric model, which waits until
   all such models are done, per Cian, and the survey's other two-object variants if
   Cian wants them. The original plan: Part 1: the permutation group
   of ℕ (ND, BF, Atomlessness hold, so Actuality, Atomicity, BC fail); Part 2: monotone
   surjections (¬ND, BF, ¬BC); Parts 3–8: monotone maps, the `h0 = h1 ∨ h = id`
   restriction (Actuality), truncations `gₙ` (Atomicity without Actuality), powers of two
   `fₙ` (both without BF), shifts `kₙ` (all three, BC fails). These give the maximalist
   incompatibilities with `□`Actuality and `□`BC (`max_box_inconsistent` in
   `Results/SentenceSchemas/Incompatibilities.lean` is waiting for `Consistent (single (neg Y))`),
   the map's `finite-support-*` model records, and Atomlessness verdicts. A `Models/`
   directory is the agreed home once there is more than one file (model verdicts now sit
   in `Semantics/ActionExamples.lean`).
2. **The C5 results** about Actuality/BC/Atomicity: **done**, at every arity since
   1 October (vectorization plan, Phase 9), BC + Actuality ⇒ WRC (haecceity LUB)
   included, except Proposition 2.11, which is refuted (§4), and
   `c5-and-atomicity-t-imply-no-pure-contingency` (the atom-exchanging automorphism
   extended by conjugation over all types: a metalogical proof by induction on terms,
   the next experiment of the Atomicity kind).
3. **Uniform arity** for the constructions now written at `t` / `σ → t` (GLB from a
   rigid coextension, Actuality's comprehension witnesses): either a metalogical
   statement by induction on the arity with object-level rules per step, or a shallow
   class carrying the construction as a field. Decide with Cian.
4. **Conservativity** of `C(Σ)` over `C` for pure sentences (the converse of
   `Syntax/Pure.lean`), which the cross-signature arrows
   `possibility-signature-r-implies-possibility-schema-r` need; syntactically, replace
   constants by fresh variables and discharge by Existence.
5. **Missing principles**: Witnessed Possibility and its kin (substitution of constants
   for variables), Possibility+, Strong Possibility (`◇_≠`), Separated Structure,
   Independence, Modal Freedom, Logical Necessity, the Infinity principles (need finite
   cardinalities), the Necessity of Arithmetic, Countable BC.
6. **Coalesced sums** (Appendix E) and the Henkin model without choice, for the
   remaining Possibility incompatibilities; the map's `coalesced-*` records.
7. **Feeding the map**: teach `scripts/pmap.py lean` the `foo.entails` shape so that
   certified records can carry a `lean:` verification status (never set by hand).
8. Housekeeping (small rebuild-time cleanups are listed in `TODO.md`): `Tools/Schema.lean`
   still has code paths for `.strict` twins; the
   metalogical README's experiment record is history, keep it; `Classicism/Strict/`'s
   fate is Cian's call (currently a sideline).

## 6. How to write the next result

First look in the library for the general facts the proof needs (§3), and put any new
general fact there.

For a map arrow between type-indexed principles whose proof is "for every arity": the
record at `σ → t` in `Results/Records.lean` (certified by the audit, which gives its
`listEntails`), then the theorem at every arity in `Results/Arity.lean`, the list form
composed with `schema_subset_args` and, for BF, `P.Barcan.schema_entails_listSchema` —
copy `atomicity_t_and_bf_imply_atomicity` there. For a result about the
sentence schemas: state it for any `Sig` and `Ax` where possible, prove the
object-level step as a shallow lemma at `Prop` variables, `#classicism_derive` it, and
apply it with `Theorem.ofCMinus (C.TheoremMinus.ofPure foo.derivable)` and `allEβ` —
copy `Results/SentenceSchemas/PossibilityDistinctness.lean`. For a model verdict: build the
premodel, prove `IsModel` (or use `full_isModel`), then use the criteria in
`ActionFacts.lean` and turn verdicts into `Consistent` / `¬ Theorem` facts as
`Results/Consistency/Consistency.lean` does. Keep each object-level lemma small and closed:
the translator's cost is in the shape of the proof term, not its length.

## 7. Lean gotchas learned the hard way

- A single long tactic proof made the translator take 27 GB; nine closed lemmas took
  seconds. Decompose.
- Measure Lean memory with `top`'s footprint, not RSS (compression hides it).
- `forallTelescope` consumes non-dependent arrows: the pipeline uses `paramTelescope`.
- `induction` does not support the mutual `RTy`; use `RTy.induction`.
- A non-`partial` def inside a `mutual` block with a `partial` one is refused.
- Field notation does not resolve through the abbreviations: write `Theorem.mp h`, not
  `h.mp`, when `h`'s head is `Derivable`; `Sentence.holds I p`, not `p.holds`;
  `AxiomSet.box S`, not `S.box` (`P.X.schema.box` even parses as a constant name).
- `Theorem.ax rfl` needs the schema and sentence named, `(Ax := …) (a := …)`, when the
  sentence must be inferred through a substitution.
- Instantiating `∀x∀y` one binder at a time leaves a renamed opaque term that does not
  compute; `allE₂β` substitutes simultaneously.
- `rw` with a hypothesis of the form `Rel.le p q` inserts `Rel.or`; coerce to
  `q = (p ∨ q)` first.
- `𝟙` needs `open CategoryTheory`; `rintro` alternatives must mirror the nesting of `∪`.
- In the pure signature every sentence is pure (`Term.pure_of_pureSig`), so
  `noContingency Signature.pure` and `npc Signature.pure` coincide.
- Certified derivations come out in `C⁻` (`C.axiomsMinus`); lift with `Theorem.ofCMinus`.
- Never write `nec% h` for a hypothesis `h`; only closed lemmas (object parameters are
  fine) may be necessitated.
- Intensional models: an arrow of a one-object category written `(k : star ⟶ star)` for
  `k : M` does not fix the objects of a functor's `map`, which then wants them named
  (`(X := …) (Y := …)`); the reverse, an arrow used as a function, needs a named coercion
  (`Perms.perm`), since `(g : G)` leaves the term with its arrow type; a particular model
  should be a `noncomputable abbrev`, so that `model.W₀`, `model.incl` reduce for `rw`;
  `Set.empty_ne_univ` wants a `Nonempty` instance; a membership `p ∈ F.obj W` needs `F.obj W` to reduce to a `Set`
  at reducible transparency, so the actions of intensions, products and the point are
  `abbrev`s and elements of a full domain are typed as sets where `∈` is used; the
  projections of a concrete premodel (`(MSet.model M).incl`, `.inner`) are the plain
  values only definitionally, so state a fact about a particular model in the plain form
  (`FullT (unitAction M)`, `fullIncl`) and pass it where the model's form is expected.
- A type-directed notation must treat an expected type `Sort ?u` as `Prop`: a `have h : A ∧ B`
  or a theorem statement has that expected type, and reading it as "not `Prop`" made
  `Rel.and` at `Prop`, the same by definition, which every build and audit accepted and
  only the strict route's bridge (`Strict/Tests.lean`) caught. Fixed in `Paper.lean`.
- Monoid models: under `variable (M)`, an `abbrev arrow {X Y : SingleObj M} (g : X ⟶ Y)`
  takes `M` explicitly and every use misparses; declare it under `variable {M} in`. A
  theorem named like the general lemma it is proved from (`not_bf_e` inside `Truncs`)
  shadows it; qualify (`MonoidModel.not_bf_e`). `{0, 1}` at a domain type needs
  `({0, 1} : Set ℕ)`; `show … at h` is `change … at h`; `omega` takes `2 ^ j` as an atom
  but does not beta-reduce `(fun n => n / 2) (2 * y)`, so `show 2 * y / 2 = y` first.
  `Mathlib.Data.Nat.Defs` does not exist in this Mathlib; the `Nat` division and power
  lemmas are in core (`Nat.div_eq_of_lt`, `Nat.mul_div_mul_left`, `Nat.pow_lt_pow_right`,
  `Nat.div_eq_zero_iff` with a `b = 0 ∨` disjunct); `ring` needs `Mathlib.Tactic.Ring`,
  and `Even` on `ℕ` decides only with `Mathlib.Algebra.Group.Nat.Even`. A general lemma
  may already exist under the name you are about to use — `Premodel.holdsAx_npc` was
  there before its monoid-model copy was written; grep first.

## 8. Questions to settle with Cian when they come up

- **Sentences with type variables** (2 October; fixed 4 October after Astra's audit). Every
  sentence schema now requires its instances to have only closed types (`Term.closedTypes`,
  `Syntax/ClosedTypes.lean`), and every principle's schema is shown to have only such
  instances (`P.X.schema_closedTypes`, generated in `Certified/Schemas.lean`). Building an
  instance goes through the membership lemmas (`npc_mem`, `possibility_mem`,
  `witnessedPossibility_mem`, …), which state the sentence explicitly; `simp` then works on
  the side condition, which it cannot when unification has unfolded the sentence.
  `c5-and-atomicity(-t)-imply-no-pure-contingency` is now open to the automorphism proof (the
  map's write-up): `F` extended to every type by recursion on the type, and an induction on
  pure terms. Still open: that derivability and consistency are unchanged by the type
  variables, for sentences and theories of the paper's language (a derivation may pass
  through formulas with type variables). It should follow by instantiating every type
  variable at `e`, a vectorization at singleton lists (`C.Theorem.vec`).
- **Bacon's Theorem 8.2** (`necessary-strong-leibniz-and-rigid-comprehension-imply-necessary-bf-t`).
  The map's sketch applies Rigid Comprehension inside the box (a rigid collection of world
  properties accessible to `W`, with `W` chosen at the inner world), but the premise is
  unboxed, and an axiom cannot be necessitated. Either the argument uses only the actual
  instance and rigidity carries it, or the premise should be `□`Rigid Comprehension; the
  book would settle it.
- **The three certificates resting on `e_exists`** (item 1 of 2 October, deferred).

- The shape of the `Models/` directory and what a model file should export (verdicts as
  `Consistent` / `¬ Theorem` facts, or the model with its `HoldsAx` facts).
- Whether the uniform-arity constructions (agenda item 3) go metalogical or via a class.
- Whether the map should record the very-weak-rigid-comprehension route to Boolean
  Completeness at `t` (Lean has it; the map does not).
- Anything about the map's data itself: Cian edits the map; Lean results are reported to
  him, and the map's `lean:` fields are never set by hand.
