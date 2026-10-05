# Working on the Lean

For anyone about to change the Lean formalization of *Classicism*, agents included. Lean
work is done only when asked for (`logical-maps/CLAUDE.md`, "Mathematical brainstorming is
the default"). Cian Dorr is an author of the paper being formalized and of the map it
serves: treat the mathematics as his, and check claims against the paper, not memory.

## Read first

- `README.md`: the shape of the project, the shallow theory, the gate, names, files,
  building.
- `Classicism/README.md`: the metalogical layer, its design decisions and modules, and how
  to write a metalogical proof with object-level steps.
- `map/README.md`: how the map uses the project, and what to run after a change.
- `TODO.md`: open work and open questions. `CHANGELOG.md`: what changed, by day.
  `VERIFICATION.md`: the audit record, dated: what was checked, and why.
- `Classicism/Strict/` is an earlier route (Appendix A on Lean proof terms), kept as a
  sideline; nothing the map relies on uses it.

## Practicalities

- Toolchain `leanprover/lean4:v4.33.1`, Mathlib at the matching tag (the model theory only).
  In a fresh environment run `lake exe cache get` before the first `lake build`, or Mathlib
  compiles for hours; where the cache host is blocked, the part of Mathlib the project
  imports builds from source in about ten minutes on four cores. A warm full build takes a
  few minutes; a change to a module near the bottom (`Core`, `Pointwise`, `Syntax/Term`)
  rebuilds everything, about twenty-five.
- Run one heavy Lean process at a time: the translator can take gigabytes on a bad proof
  shape. Do not open a certifying file (`Certified/`) in an editor with the Lean server
  on: it redoes the work.
- The map: the enclosing repository, topic `logical-maps/topics/classicism/`. Its rules
  apply here: `python3 scripts/pmap.py validate` before every commit; never edit
  generated files (`Classicism/Statements.lean`, `build/`); never set a record's `lean:`
  status, or a variant's, by hand: `pmap lean-check classicism --update` sets them.
  Private notes go in the outer checkout's `.private/`, never in this directory.
- Commit messages follow the map's style (`classicism: …`) and end with the
  `Co-Authored-By` line the environment supplies. Preserve Cian's text, claims and
  citations unless the change concerns them.

## Conventions

- **General lemmas live in the library.** A lemma stating a broadly applicable property
  goes in the library module for its subject, not beside the result that first needs it:
  laws of `□` and `◇` in `Modal.lean`; the order, bounds and atoms, at `t`, at `σ → t` and
  at a relational type, in `Lattice.lean`; propositional identities in `Booleanism.lean`;
  pointwise laws at a Rel-parameter in `Pointwise.lean`. Look there before proving one.
  What stays with a result is particular to its proof: a closed one-step lemma shaped so
  that `nec%` can carry it under the box, or a construction such as a haecceity.
- **Words** (`README.md`, "Names"). A *principle* is a shallow definition indexed by types;
  an *instance* is one sentence; a *schema* is an axiom set, `AxiomSet`. A principle's
  schema is `P.X.schema`, and at every signature `P.X.schemaIn`
  (`Certified/Signatures.lean`); a *sentence schema* (No Pure Contingency, Possibility, …)
  is schematic in a sentence and defined in `Syntax/`.
- **Forms** (the map's *variants*; `Principles.lean`, "Forms"). A form is defined beside
  its principle in `Principles/<Category>.lean` as `P.<Name><Form>`, followed by the two
  directions `P.<Name>.to_<form>` and `P.<Name>.of_<form>`, which the audits certify; the
  certificate `Map.<principle-id>.<variant-id>` cites their `.entails`. Polyadic forms are
  defined by vectorization, with their equivalences in `Results/Lists.lean`.
- **No formula quantifies over types.** A principle is a Lean `Prop` with its object types
  as parameters; a record is an implication between instances. The type-system check
  enforces it, and the quoter depends on it.
- **A law that holds by recursion on the structure of a type is a class field** (`Rel`,
  `Order`, `Pointwise`), proved at `Prop` and at `σ → τ`; the translator derives it at every
  object type. The strict mirror `SPointwise` has only the first eleven fields, so a proof
  using a later one is not reached by the strict transformer (`Strict/Transformed.lean`).
- **The paper's symbols change no terms** (`Paper.lean`). `⊆` for `incl` is always on;
  `≤`, and `∧ ∨ ¬ ⊤ ⊥` at relational types, and `≡`, need `open Classicism.Paper`. The
  connectives are type-directed: `And`/`Or`/`Not` at `Prop`, `Rel.and` etc. elsewhere, so a
  connective at `Prop` that must stay `Rel.and` is written by name. Inside the scope `≤` is
  always `Rel.le`; outside it `≤` at `Prop` is `entails`, which Tractarianism is stated
  with, so `Principles/Coarse.lean` does not open the scope. Do not open it in a file that
  opens the strict algebra or imports Mathlib. Use the paper's named predicates (`GLB`,
  `UB`, `Atom`, `Persistent`, `ActualWorld`) where the unfolded form would otherwise be
  written.
- **`λ x ↦ …` for terms, `fun h => …` for proofs** in the shallow layer.
  `lake env lean --run scripts/FunKinds.lean <file> <module>` says which each `fun` is.
- **Record theorems** in `Results/Records/` are named after the record id with hyphens as
  underscores, one per record, with a docstring naming the record and the argument's source.
  A theorem proving only the instances at `t` or for relations `σ → t` carries the id with
  `_at_t` or `_unary`, and its certificate claims no more. Helper lemmas must not look like
  records (a statement whose head is a `Classicism.P` principle is read as one): state them
  unfolded.
- **A result at every arity is a unary proof, vectorized** (`history/VECTORIZATION-PLAN.md`). Prove
  it at `σ` or `σ → t` in the shallow layer and let the audit certify it, which gives
  `foo.listEntails`; then compose with `P.X.schema_entails_listSchema` for a list premise and
  with `schema_subset_args` for a conclusion over relational types. In `C5`, take `□ND` at
  `t` and get `□BF` at `σ` inside the proof, so that no list premise arises. List forms are
  never written by hand: `P.X.listQuoted` is the vectorization of `P.X.quoted`.
- **Sentence schemas range over the paper's language**: an instance must have only closed
  types (`Term.closedTypes`, `Syntax/ClosedTypes.lean`); each principle's schema satisfies
  this (`P.X.schema_closedTypes`). Build an instance with the membership lemmas (`npc_mem`,
  `possibility_mem`, `witnessedPossibility_mem`, …), which state the sentence explicitly.
- Every metalogical result about the map's principles is at `Signature.pure`, where
  `P.X.schema` lives; sentence schemas are stated for any `Sig`, and the map's statements
  range over `Signature.Admitted` signatures.

## Writing the next result

Look in the library first for the general facts the proof needs, and put a new general
fact there.

- **A map arrow between type-indexed principles.** The record in `Results/Records/<Topic>.lean`,
  at one argument type if the result is for every arity; the audit certifies it. For every
  arity, add the theorem in `Results/Arity.lean`: copy
  `atomicity_t_and_bf_imply_atomicity`.
- **A result about the sentence schemas.** State it for any `Sig` and `Ax` where possible,
  prove the object-level step as a shallow lemma at `Prop` variables, `#classicism_derive`
  it, and apply it with `Theorem.ofCMinus (C.TheoremMinus.ofPure foo.derivable)` and
  `Derivable.allEβ` (`allE₂β` for two binders at once): copy
  `Results/SentenceSchemas/PossibilityDistinctness.lean`.
- **A model verdict.** Build the intensional premodel, prove `IsModel` (or use
  `full_isModel`), use the criteria in `Semantics/IntensionalFacts.lean`, and turn verdicts
  into `Consistent` and `¬ Theorem` facts as `Results/Consistency/Consistency.lean` does.
- **A form of a principle.** Define it and its two directions beside the principle, add it
  to the list in `Certified/Schemas.lean`, give the variant its `lean` field in the
  principle's record, and add its certificate to `Map.lean`.
- Then the map: give the record its `lean_ref` (the certificate in `Map.lean`), and run
  what `map/README.md` says.

Keep each object-level lemma small and closed: the translator's cost is in the shape of the
proof term, not its length.

## Gotchas

- A single long tactic proof made the translator take 27 GB; nine closed lemmas took
  seconds. Decompose. Measure Lean memory with `top`'s footprint, not RSS.
- A law proved as a bare `Or.inr` or `id`, unapplied, is not read by the translator: write
  `fun h => Or.inr h`.
- Never write `nec% h` for a hypothesis `h`; only closed lemmas (object parameters are fine)
  may be necessitated.
- Certified derivations come out in `C⁻`; lift with `Theorem.ofCMinus`.
- Field notation does not resolve through the abbreviations: `Theorem.mp h`, not `h.mp`;
  `Sentence.holds I p`, not `p.holds`; `AxiomSet.box S`, not `S.box`.
- `Theorem.ax rfl` needs the schema and sentence named, `(Ax := …) (a := …)`, when the
  sentence must be inferred through a substitution. Instantiating `∀x∀y` one binder at a
  time leaves a renamed term that does not compute; `allE₂β` substitutes simultaneously.
- When unification has unfolded a sentence (from a derivation's instantiation, say), `simp`
  cannot see its connectives: state the sentence explicitly, which the membership lemmas
  do. `simp` also unfolds `Term.top` and `Term.bot` before using a lemma about them;
  rewrite step by step there.
- `induction` does not support the mutual `RTy`; use `RTy.induction`. `forallTelescope`
  consumes non-dependent arrows: the pipeline uses `paramTelescope`. A non-`partial` def
  inside a `mutual` block with a `partial` one is refused.
- `rw` with a hypothesis `Rel.le p q` inserts `Rel.or`; coerce to `q = (p ∨ q)` first.
- A `/-! -/` comment inside a `class` body is a parse error. The paper-notation elaborator
  cannot type `¬ constP w ∨ X` when nothing fixes the type of `constP w`: ascribe it.
- A theorem proved over `Classicism.e` (the reflection lemmas' domain) depends on the
  axioms `e` and `e_exists`, outside the map's list; build models for consistency facts on
  `Unit` instead.
- `casesm` and other Mathlib tactics are not available outside the model theory. In
  generated commands, macro hygiene renames hypotheses introduced in a `repeat` loop; build
  the command's text with explicit names instead.
- Intensional models: an arrow of a one-object category written `(k : star ⟶ star)` does
  not fix the objects of a functor's `map`, which then wants them named; an arrow used as a
  function needs a named coercion (`Perms.perm`); a particular model should be a
  `noncomputable abbrev`, so that its projections reduce for `rw`; a membership
  `p ∈ F.obj W` needs `F.obj W` to reduce to a `Set` at reducible transparency; state a fact
  about a particular model in the plain form (`FullT (unitAction M)`) and pass it where the
  model's form is expected.
- Monoid models: under `variable (M)`, an `abbrev arrow {X Y : SingleObj M}` takes `M`
  explicitly and every use misparses; declare it under `variable {M} in`. A theorem named
  like the general lemma it uses shadows it; qualify. `{0, 1}` at a domain type needs
  `({0, 1} : Set ℕ)`; `omega` does not beta-reduce; the `Nat` division and power lemmas are
  in core; `ring` needs `Mathlib.Tactic.Ring`. Grep before writing a general lemma: it may
  exist under the name you are about to use.
