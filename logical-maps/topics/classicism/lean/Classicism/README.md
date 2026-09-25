# The metalogical layer

This README covers the metalogic of the formalisation: `Syntax/`, `Semantics/` and
`Results/`, which are mathematics, and `Tools/` and `Certified/`, which are the
metaprogramming that connects them to the shallow formalisation in `Classicism/` and its
outputs. The main `README.md` describes the shallow layer and the whole; `Strict/README.md`
the strict layer, a sideline.

The shallow layer proves theorems *in* Classicism, in Lean, under a gate. This layer
proves theorems *about* it: the terms of the object language, their derivations and their
models are objects of Lean, so that one can say that a sentence is a theorem of
Classicism, that a schema entails a schema, that a closed pure sentence is necessary if
true, that a sentence holds in a model — and so that a proof in the shallow layer can be
turned, by a program the kernel checks the output of, into a derivation of the object
language. Earlier notes called this the "deep" layer; **metalogical** is the name now.

## What it is for

1. **Metalogical statements.** "Schema A entails schema B" as a theorem about instances;
   No Pure Contingency, a schema over closed *pure* sentences; the Maximalist principles,
   which quantify over syntax; an induction on the structure of a relational type, which
   the shallow layer's classes cannot perform.
2. **Certificates.** A record of the map — an arrow between principles — is a shallow
   theorem `P … → Q …`; the translator makes of it a derivation in the object language
   and the pipeline reads that as `P.schema ⟹ Q.schema`, the form of the arrow, or as a
   rule between instances for use inside a metalogical proof (`Results/`).
3. **Model evidence.** The paper's action models, with soundness, are the models the map's
   non-implication records need; a model of `Ax₁` refuting a sentence of `Ax₂` shows that
   `Ax₁` does not entail `Ax₂`.
4. **The theory itself.** Classicism is defined here as the paper defines it, `H` closed
   under Subst; that the eleven identities axiomatize it (Appendix A) is a theorem to be
   proved about this definition, and the strict layer's transformer is its constructive
   evidence one theorem at a time.

## Design decisions

The first five were settled with Cian on 22 September 2026, the rest on the days named.

- **The syntax is its own datatype, not a subtype of Lean's `Expr`.** This layer proves
  theorems about substitution and conversion, and `Expr`'s are implemented behind
  `extern` with no equations; a typing relation for `Expr` is the Lean4Lean project; and
  the metalogical statements need a small closed grammar with decidable notions of
  "closed" and "pure". The bridge to the shallow layer is the reflection pattern: a
  denotation `⟦·⟧` from terms to propositions, and a quotation `⌜·⌝` the other way, with
  `⟦⌜p⌝⟧ = p` checked per theorem.
- **Terms are intrinsically typed.** `Term Sig Γ σ` is the type of terms of type `σ` with
  free variables from `Γ`; an ill-typed term cannot be written.
- **Variables are de Bruijn indices**, so α-equivalence is identity and only β and η
  remain. No higher-order abstract syntax.
- **The type system is fixed**: `e` and `t` are the only base types. Nonlogical
  vocabulary enters through a `Signature` of constants; the pure language is the empty
  signature.
- **Derivations are not a separate datatype.** `Derivable Ax Δ p` is an inductive
  predicate, by definition the smallest relation closed under its rules; a proof of it
  *is* a derivation tree. A `Type`-valued twin would allow computing with derivations at
  the price of proof relevance in every lemma, and nothing planned needs it.
- **The type-subscripted operations are constants of the syntax with an unfolding rule**
  (23 September). `∧_τ`, `¬_τ`, coextension and the rest were first functions on terms
  by recursion on the type. A function stuck at a type *variable* is not a node of the
  syntax: renaming and substitution could not pass through it, and no derivation could
  mention `∧_τ` for `τ` a variable, which a derivation by induction on the type must. So
  `Term.andR ρ` is a constructor, and the recursion is the δ-rule of conversion,
  `∧_t ≡ ∧` and `∧_{σ→ρ} ≡ λX Y z. X z ∧_ρ Y z`, alongside β and η.
- **Mathlib, for the model theory only** (23 September). The action models import
  Mathlib (categories, functors to `Type`, sets), pinned to the tag matching the
  toolchain and checked out into one directory shared by every Lean project on the
  machine (`.lake/packages` a symlink to it; the configuration has no machine-specific
  path). The shallow layer never imports it, so its axiom audit is unaffected.
- **Classicism is `H` closed under Subst** (24 September, replacing the eleven identities
  as the definition). The rule is *Elimination*'s: from `P ⊢ Q` and `Q ⊢ P`, each on its
  own, and `Δ ⊢ R[P]`, infer `Δ ⊢ R[Q]`, for `R` a formula with one hole, under binders
  or not (`Hole`, a term with a hole, in `Syntax/Derivation.lean`). It gives no logical
  constant a special role: Equivalence is its instance at the hole `P = ⬚`, ξ its
  instance under an abstraction, and both are derived. "On its own" is the substance: the
  premises are derivations from the one hypothesis in the *logical part* of the axiom
  set (Existence at `e` and nothing proper to the theory), so the axiom set is an index
  of the inductive; were the theory's own axioms admitted there, `C + BF` would derive
  `□BF`, and the map's distinction between BF and □BF would collapse. The eleven
  identities are theorems of the system, each a Subst at `λ… P = λ… ⬚` (one is derived
  in `Syntax/Examples.lean`). A map record "`C` plus BF proves this instance" is
  derivability with the union of the axiom sets.
- **The translator reads shallow proofs directly** (24 September, replacing the route
  through the strict layer). A gated shallow proof is natural-deduction shaped: its
  constants are the rules, and the two gated primitives are exactly Subst (`propext` on
  a closed biconditional) and its consequence at every type (`funext` on a closed
  identity, `substEq`). The strict route, an Appendix-A instance per theorem re-expressed
  as natural deduction, cost ten to a hundred times more; the experiment that showed it
  is recounted at the end of this README.

## The modules, in order

| module | contents |
| --- | --- |
| `Syntax/Types.lean` | `Ty` and `RTy`, the mutual inductive of Dorr's *Elimination*, Appendix A: `e`, `t`, and `σ ⇒ ρ` for a type `σ` and a relational `ρ`. Decidable equality; every type is `e` or `σ₁ → … → σₙ → t`. |
| `Syntax/Term.lean` | `Signature`; contexts; `Var`; `Term Sig Γ σ` with the paper's six logical constants `∧`, `∨`, `¬`, `∀σ`, `∃σ`, `=σ` and the seven type-subscripted operations `∧_ρ`, `¬_ρ`, … as constructors, Figure 1's abbreviations `→`, `↔`, `⊤`, `⊥`, `□`, `◇` as definitions, and `Term.unfoldR`, the one-step unfolding of an operation at a constructor type; purity; renaming and substitution, through `Term.rec` for the kernel's sake, with the identity laws and the four composition laws. |
| `Syntax/Conversion.lean` | β, η and δ in three grades: the immediate conversion of a redex, the one-step closure `Step`, and the equivalence closure. `Conv`, written `≡`, is βηδ-conversion, proved a congruence and stable under renaming. |
| `Syntax/Derivation.lean` | `Derivable Ax Δ p`: hypotheses, axioms, the rules for `∧`, `∨`, `¬` with excluded middle, `UI`, `Gen`, `EG`, `Inst`, `Ref`, `LL`, conversion. Weakening and monotonicity admissible; `→` and `↔` rules derived. |
| `Syntax/Axioms.lean` | The eleven identities as sentences; `C.axiomsMinus` and `C.axioms`, the latter adding Existence at `e`; `C.Derivable`, `C.Theorem`. |
| `Syntax/Entailment.lean` | **Entailment between axiom sets**, `Ax₁ ⟹ Ax₂`: every sentence of `Ax₂` a theorem of `C ∪ Ax₁` — the form of the map's arrows. Unions and inclusions of axiom sets; cut (`Derivable.replaceAx`, axioms replaced by their derivations); `refl`, `trans`, monotonicity, unions; `of_imp_family`; `Consistent`. |
| `Syntax/SentenceSchemas.lean` | The map's schemas over *sentences*, which no shallow definition can express: No Pure Contingency, No Contingency and B for a signature, Distinctness and Possibility relative to a theory, and `max`, the maximalization, with Maximalist Classicism `max empty`. |
| `Semantics/Denotation.lean` | `Ty.denote`, `Env`, `Interp`, `Term.denote`: the standard reading of the syntax in Lean, with `t` as `Prop` and `e` as a chosen domain. Renaming and substitution commute with it; conversion preserves it; **soundness** of `Derivable`; the eleven identities hold in `Prop`, so `Prop` is a model of `C` and **`C` is consistent**. |
| `Syntax/Examples.lean` | A β-step by `rfl`, an η-step, purity decided, small derivations (commutativity of `∧` by Subst among them), and the reflection checks: sentences read back are the propositions they abbreviate, by `rfl`. |
| `Semantics/Relational.lean` | The bridge for the type-subscripted operations `∧_τ`, `¬_τ`, `∨_τ`, coextension, the pointwise box and implication (constants of `Syntax/Term.lean`, read in `Semantics/Denotation.lean` by recursion on the type): the standard reading's `SRel` and `SOrder` instances by the same recursion, and one lemma per operation, by induction on the type, that its reading is the strict layer's. Purpose four of this layer, at work. |
| `Tools/Quote.lean` | **The quoter**, first half of the translator: `#classicism_quote foo` reads the statement of `foo` as a sentence, `foo.quoted`, with type parameters as object-type variables, and declares `foo.reflect`, that reading it back gives the statement, by `rfl` or by rewriting. `#classicism_quote_audit` runs it over a module. |
| `Certified/Quoted.lean` | The quoter run over the record theorems at build time; home of every `foo.quoted` and `foo.reflect`. |
| `Syntax/Normalize.lean` | A **verified βη-normalizer** on the syntax, `Term.nf`, with `Conv.of_nf`: two terms with the same normal form convert, the hypothesis decided by evaluation. |
| `Tools/Translate.lean` | **The translator**, second half: `#classicism_derive foo` reads the gated shallow proof of `foo` and declares `foo.derivable`, a kernel-checked derivation of its statement. `#classicism_derive_audit` runs it over a module. |
| `Certified/Derived.lean` | Two quick derivations run at build time, as a check that the whole chain works. |
| `Tools/Schema.lean` | **Principles as schemas and records as entailments.** `#classicism_schema P` quotes the principle `P` (its strict twin) into `P.quoted`, `P.reflect` and `P.schema`, the axiom set of its instances over its object types. `#classicism_entails foo` reads the statement `P₁ … → … → Q …` of a record theorem and its derivation `foo.derivable` into `foo.entails : P₁.schema ∪ … ⟹ Q.schema`, specializing the derivation to each instance of `Q` and citing the premises as axioms; `#classicism_entails_audit Mod` does it for a module, deriving first. |
| `Tools/Schema.lean` (rules) | `#classicism_rule foo` reads the same derivation as a **rule between the schemas' instances**, `foo.rule : ∀ σ' …, C.Theorem (imp (P₁.quoted …) (… (Q.quoted …)))`, keeping the object types, for use inside a metalogical proof; `#classicism_certify foo` is the whole chain at the point where `foo` is stated: transform, schemas, derive, rule. |
| `Certified/Schemas.lean` | The 29 principles as schemas: the home of every `P.quoted`, `P.reflect`, `P.schema`. |
| `Certified/Derivations.lean` | Every record theorem of `Results/Records.lean` derived in the object language: the home of every `foo.strict.derivable`, kept apart because it is the expensive part of the build. |
| `Certified/Entailed.lean` | The record theorems of `Results/Records.lean` certified as entailments: the home of every `foo.entails`. All 28 certify. |
| `Semantics/Action.lean` | **Action premodels and action models**, the paper's models of Classicism, directly: a rooted category, an inner action per type, the outer actions by recursion on the type, the subaction conditions, the total interpretation function `sem`, `Holds`, and `IsModel`. |
| `Semantics/ActionSoundness.lean` | **Soundness of action models**: transport, renaming, substitution, β, η, δ, conversion; every rule of `Derivable`; the eleven identities and Existence hold at every arrow of every action model; `theorem_holds`, `theoremWith_holds`. |
| `Semantics/ActionFull.lean` | **Full action models**: the powerset and exponential actions as functors; the full inner domains by recursion on the type; `Premodel.full` on any rooted category from an action for `e` and an interpretation; **`full_isModel`**, that a full premodel is a model, by the combined induction (inner-ness and transport together, the type-subscripted constants by a second induction on the size of the type); `full_bf_surjective`, the paper's (iii). |
| `Semantics/ActionFacts.lean` | `ND_σ`, `BF_σ` and the Fregean Axiom as sentences; the clauses for `□` and `◇`; **truncation** (`Premodel.truncate`, `sem_truncate`, `isModel_truncate`, `dia_iff_truncate`, `box_iff_truncate`); the paper's generalizations: `ND_σ` holds iff every `h^σ` out of the object is injective, `BF_σ` holds if every `h^σ` is surjective, the Fregean Axiom holds iff propositions agreeing at the identity are equal. |
| `Semantics/ActionProperties.lean` | Properties of action models — propositionally full, quasi-functionally full, full — and what holds in all models with a property: the value of a pure term does not see the arrow (`sem_pure`), so **No Pure Contingency holds in every one-object model** (`holdsAx_npc`); the Fregean Axiom fails in every propositionally full model with a second arrow out of the base. |
| `Results/Atomicity.lean` | **A metalogical proof with object-level steps**, the map's arrow "Atomicity (`t`) and BF imply Atomicity": the step `Atomicity τ → BF σ → Atomicity (σ → τ)` as shallow lemmas proved with ordinary tactics, certified in place by `#classicism_certify` into the rule `atomicity_step.rule`, and the theorem by induction on the relational type, `P.AtomicityT.schema ∪ P.Barcan.schema ⟹ P.Atomicity.schema`. Elaborates in full; not in the build, since its `.olean` does not serialize in reasonable time (see below). |
| `Semantics/ActionExamples.lean` | Full M-set models (`MSet.model`): the idempotent monoid `{1, k}` (`ND_t`, `BF_t` and the Fregean Axiom fail — the map's `full-idempotent-monoid`) and the two-element group (the Fregean Axiom fails, `□ND_σ` and `□BF_σ` hold at every type — `full-involution-group`); at an object whose out-arrows are isomorphisms, `ND_σ` and `BF_σ`; in a groupoid, their necessitations. |

## Conventions worth knowing

- The signature variable is written `Sig`, because `Σ` is reserved syntax in Lean.
- `σ ⇒ ρ` is `RTy.arr σ ρ`, right-associative, and a relational type coerces to a type
  where one is expected, so `RTy.t ⇒ RTy.t ⇒ RTy.t` is the type of `∧`.
- `Term.v0`, `v1`, `v2` name the three innermost variables; in an axiom written
  `λpq. …`, `p` is `v1` and `q` is `v0`.
- Renamings and substitutions are functions taking their type argument explicitly,
  `r _ v`; recursive definitions over terms quantify the context inside, since `lam`
  changes it.
- This layer is ordinary Lean. `funext`, `propext` and choice may be used, and none of the
  audits of the other layers runs here: it is a theory of Classicism's proofs, not a proof
  in Classicism. Its trusted base is the definition of `Derivable`.

## The `C`/`C⁻` line

A derivation in context `Γ` may use the variables of `Γ`, and a closed derivation has
none. So from the eleven identities alone there is no term of type `e` at which to
instantiate `EG`, and `∃x:e. x = x` is not derivable: the contextual system is
existentially neutral at `e` by itself, the paper's `H⁻`. At every relational type the
closed term `λx. ⊤` exists and Existence is derivable. That is the line the shallow layer
drew with the axiom `e_exists`, here for a structural reason.

## The denotation

`Term.denote I` reads a term as a Lean value, given an interpretation `I` of `e` and of the
constants; `t` is `Prop`, so a sentence denotes a proposition. With `Prop` as `t` this is
the paper's full Henkin model. Soundness says a theorem of an axiom set that holds in `I`
holds in `I`, Subst included, by the congruence of filling a hole; Existence at `e` holds
when the domain is inhabited, so Lean's `Prop` is a model of Classicism and `C` proves no
falsehood of it, in particular not `⊥`. The eleven identities hold in `Prop` too, each by
`propext` and `funext`, a corollary of soundness kept as a direct check. The reflection
examples check that reading back a sentence gives the proposition it abbreviates, by
`rfl`: `⊤` reads back as `(∀p. p) ∨ ¬(∀p. p)`, `→` as `imp`, and an identity as the
statement of the shallow theorem. That equation, `⟦⌜p⌝⟧ = p`, is what the quoter is held
to. The readings of types are reducible, so that `⟦t⟧` *is* `Prop` to instance search and
to `simp`.

## The quoter

`Tools/Quote.lean` is a meta-program reading a shallow statement as object syntax: `Prop`,
`e`, arrows and guarded type variables as types; `∧`, `∨`, `¬`, `→`, `↔`, `∀`, `∃`, `=`,
`True`, `False`, `□`, `◇`, the operations of `Rel` at a type variable as the constants
`andR τ'` and the rest, and any other definition of the library through its body, so that
a principle quotes through its definition and an operation at a concrete type through its
instance. `#classicism_quote foo` declares `foo.quoted`, the sentence with the theorem's
type parameters as object-type variables (`Ty` for a `Ty`-guarded parameter, `RTy` for one
guarded by `Rel`, `Order` or `Pointwise`), and `foo.reflect`, the kernel-checked theorem
that reading the sentence back in the standard interpretation with domain `e` gives the
statement with each type variable read as `⟦σ'⟧` and each instance as the class's
instance on that reading (`Semantics/Relational.lean`). Reflection is by `rfl` where the
reading is definitional, and otherwise by rewriting: the shallow `p → q` is read as
`¬p ∨ q`, `↔`, `□` and the operations at `t` likewise, and the definitions the statement
uses are unfolded (`reflectSimpSet`, `reflectDefs`). A failure of the rewriting is fatal,
not turned into `sorry`. `Certified/Quoted.lean` runs it over the record theorems at build
time.

## The translator

`Tools/Translate.lean` is the second half: `#classicism_derive foo` reads the **gated
shallow proof** of `foo` and declares `foo.derivable : ∀ σ' …, Theorem C.axioms(Minus)
(S σ' …)`, a derivation of the quoted statement that the kernel checks. The chain is then
two links for each theorem: the shallow proof in Lean under the gate, and a derivation in
`H` closed under Subst as an object of Lean, both kernel-checked, the translator
untrusted.

**What is translated to what.** A gated proof term is made of the logical inductives'
constructors, eliminators and recursors (`And.intro`, `Or.elim`, `Exists.casesOn`, …),
the identity plumbing that `rw`, `calc` and `▸` emit (`Eq.mpr`, `congrArg`, `Eq.ndrec`,
…), lambdas over hypotheses and over objects, applications, the axioms `em` and
`e_exists`, theorems of this library, and the two gated primitives. Each of the first
kinds is one rule of `Derivable` or a derived rule of `Syntax/Derivation.lean`
(`congrArg` is `LL` at a predicate, `Eq.ndrec` the same with the motive as the predicate,
the `β`-variants `allEβ`, `llβ` matching Lean's typing of an application, which
substitutes). A library theorem cited in a proof is translated **once, at object-type
variables** for its type parameters, as `c.derivable : ∀ σ' … ρ' …, Theorem Ax (S σ' … ρ' …)`,
and cited through `Derivable.ofTheorem` at the object types its type arguments quote to.
And the two primitives are where the gate pays off: `propext h`, whose `h` mentions no
hypothesis, becomes **Subst** at the hole `a = ⬚` with the two directions of `h` as its
premises, and `funext (fun x => h)` becomes `substEq` at the hole `f = λv. ⬚`, closed by
η at both ends. The premises of a Subst are derived at the logical part of the axiom set
(`withLogical`, one nesting per Subst inside a premise), and a theorem cited there is
lifted into it by `mono`.

**A law of a class at a type variable is derived by induction on the type.** The shallow
classes `Rel`, `Order` and `Pointwise` hold their laws as fields, each proved once at
`Prop` and once at `σ → τ` from the law at `τ`. A proof that cites such a law at a type
*variable* cites no axiom and no theorem, and there is no one derivation of the law:
there is one for every object type, by induction on it. `ensureFieldInduction` builds it
through `RTy.rec`: the base case is the translation of the `Prop` instance's proof (a
`propext`, so a Subst), the step the translation of the arrow instance's proof (a
`funext`, so a `substEq`) with the law at the smaller type, cited through the instance
variable, as the induction hypothesis. The law at a constructor type has its operations
unfolded first, `unfoldConv`, by `Conv.delta` under congruences. This is the use of the
metalogical layer the shallow layer cannot provide: induction on the structure of a
relational type.

**Conversion.** Where Lean's kernel silently β-reduced, the object language has the rule
`conv`, and the certificate is one reflective lemma: `Syntax/Normalize.lean` has a
verified βη-normalizer `Term.nf`, and `Conv.of_nf n a b rfl` is a conversion proof the
kernel discharges by evaluation. An untyped shadow of the syntax, `Tm`, decides where a
conversion is needed and with how much fuel; the two trees are descended together by
congruence while their roots are stable, and `of_nf` joins the subterms at the first
difference (`diffConv`); where no conversion is needed the derivation is used as it is.
Everything is built directly as an expression with every implicit argument supplied,
never through unification; `Classicism.Meta.Translate.check` type-checks each node for
debugging, `.profile` prints the time by phase, and `.progress` a file to watch.

**What it costs.** `#classicism_derive_audit` over every theorem of the shallow library —
`Modal`, `Order`, `Comprehension`, `Pointwise`, `Lattice`, `Results/Records` — derives
95 of 95 in nine seconds for the whole run. The kernel's cost is evaluating
substitutions where a rule concludes `b[a]`, which is why `rename`, `subst`, `prename`
and `step` are written through `Term.rec` directly, with `rfl` equations as their simp
set and the structural version for the compiler (`implemented_by`). The translator
restores its memo tables after each nested declaration, since what they hold for a cited
lemma's proof is of no use to the enclosing one.

## Action models

`Semantics/Action.lean` and `Semantics/ActionSoundness.lean` (23 September) are the paper's §"Action models"
and the soundness half of its appendix "Soundness and completeness of action models for
Classicism", formalized directly, for the purpose of model evidence on the map: a
non-implication record is an action model of `C` and the antecedent refuting the
consequent, and soundness makes that a proof of non-derivability.

**The definitions.** An action of a category is a functor `C ⥤ Type`. An action
premodel (`Premodel Sig C`) on a rooted category supplies an *inner* action `-^σ` for
every type, nonempty at `e`, and a value at the root for each constant. Following Cian's
reformulation, every type also has an *outer* action `-^[σ]`, *defined* from the inner
ones by recursion on the type (`RawR`, `RawT`): `-^[e] = -^e`; `-^[t]` the powerset
action, sets of arrows out of `W` with `h` acting by division; `-^[σ→ρ]` the functions on
pairs `⟨h : W → V, x ∈ V^σ⟩` — an inner argument — into `V^[ρ]`, an outer value, with no
well-behavedness asked. The premodel then supplies the subaction, an injective natural
map `incl` from each inner relational domain into the outer one, and the paper's two
conditions on inner elements of arrow type: they are well-behaved
(`i^ρ (α⟨h, x⟩) = α⟨h ≫ i, i^σ x⟩`) and take inner values.

`RawR` is written through `RTy.rec` as a reducible definition, so that `RawR inner .t W`
*is* a `Set` to instance search and the `∈`, `∩`, `ᶜ` and `ext` of sets apply to it.

**The interpretation** `sem h t g` is total: the value of a term relative to an arrow
`h : W₀ → W` and an assignment `g` of inner elements at `W` is an outer element at `W`,
by the paper's nine clauses. The paper's interpretation is partial at exactly one place,
an application whose argument's value is not inner; there `apply` takes a default. An
**action model** (`IsModel`) is a premodel in which no value is ever outside the inner
domain — the paper's definition — and in a model the two interpretations agree
everywhere. `Holds h p g` is `id_W ∈ ⟦p⟧^g_h`.

The seven type-subscripted constants are read by recursion on the type, each clause
written as the reading of its unfolding, so the δ-rule preserves the value by `rfl`.

**Soundness.** `sem_push` is the transport lemma `⟦A⟧^{i∘g}_{i∘h} = i^σ ⟦A⟧^g_h`; its
application case is where the model condition is used, through well-behavedness.
`sem_rename` and `sem_subst` pull an assignment back (the substituted terms' inner
elements, provided by the model condition); `sem_beta`, `sem_eta`, `sem_delta`, and
`sem_conv`. The "more helpful form" of the clauses — `holds_conj`, `holds_forall`,
`holds_eq` and the rest — then carries each rule of `Derivable`: `sound` says a
derivation from hypotheses holding at an arrow and assignment, in a theory whose axioms
hold at that arrow, has a conclusion holding there. The eleven identities and Existence
hold at every arrow of every action model (`axioms_holds`), each identity reduced by
`holds_eq_lam2`/`holds_eq_lam3` to its two bodies holding together at every arrow and
assignment. So: `theorem_holds`, a theorem of `C` holds in every action model, and
`theoremWith_holds`, a theorem of `C` plus an axiom set holds in every action model of
that set.

**Full models** (`Semantics/ActionFull.lean`, later on 23 September). The powerset action and the
exponential action of two actions are functors `C ⥤ Type`; the full inner domain at a
type is defined from them by recursion (through the recursor, as a reducible definition,
so that the domain at `t` *is* a `Set` to instance search); `Premodel.full` is the full
premodel on any rooted category given an action for `e` with nonempty domains and an
interpretation of the constants. **`full_isModel`**: it is an action model. The paper
states this as evident; the proof is a combined induction on terms — inner-ness and the
transport lemma together, since the application case of each needs the other — with the
six logical constants checked one by one to be well-behaved at both levels, and the
type-subscripted constants by an outer induction on the size of their type, each reading
as its unfolding does (`Term.rsize`, `fullP_all`).

**Facts and examples** (`Semantics/ActionFacts.lean`, `Semantics/ActionExamples.lean`). `ND_σ`, `BF_σ` and
the Fregean Axiom as sentences; `holds_box`; the paper's Proposition: `ND_σ` at an object
iff every `h^σ` out of it is injective (`holds_nd_iff`), `BF_σ` if every `h^σ` is
surjective (`holds_bf_of_surjective`); and the Fregean Axiom iff propositions agreeing at
the identity arrow are equal (`holds_fregean_iff`). Then the first two of the map's
models: `MSet.model M`, the full model on the one-object category of a monoid `M` with
one individual. On the idempotent monoid `{1, k}`, `k·k = k`: `k^t` sends both `∅` and
`{1}` to `∅`, so `ND_t` fails (`Idem.not_nd_t`), and `⊤` and `{1}` agree at the identity
but differ, so the Fregean Axiom fails (`Idem.not_fregean`) — the record
`full-idempotent-monoid`'s `distinctness-necessary-t` and `fregean-axiom`. On the
two-element group, every arrow is an isomorphism, so `□ND_σ` and `□BF_σ` hold at every
type (`Invol.box_nd`, `Invol.box_bf`) and the Fregean Axiom fails — `full-involution-group`'s
`necessary-distinctness-necessary-r` and `fregean-axiom`. Each verdict is a theorem about
the same object-language sentence the derivations use, so these are the first
kernel-checked model verdicts on the map.

Two Lean lessons from the day, for whoever continues: the projections of a concrete
premodel (`(full …).W₀`, `.incl`) are definitionally but not syntactically the plain
values, and `rw` and instance search see the syntax, so a proof about a particular model
should first `change` its goal to the plain form; and a Mathlib morphism in `Type` is a
bundled structure, made with `TypeCat.ofHom`, whose application is `rfl`.

The paper's (iii) — in a full model `BF_σ` at the root forces every `h^σ` out of the root
to be surjective — is `full_bf_surjective`, with the "image of the root" predicate
`rootImage` as the inner element; so `BF_t` fails in the idempotent model (`Idem.not_bf_t`,
the record's `barcan-t`), since `k^t` misses `{1}`.

**Truncation** (`Semantics/ActionFacts.lean`, last on 23 September). The paper's truncation of a
premodel by `h : W₀ → V` is `Premodel.truncate`: the same actions with `V` as base and
each constant's value moved along `h`. The paper also discards the objects with no arrow
from `V`; nothing here needs rootedness (the paper's footnote says as much), so the
`rooted` field was dropped from `Premodel` and the truncation lives on the same
category, which makes the transfer lemma `sem_truncate`, `⟦A⟧_{A_h, i} = ⟦A⟧_{A, i∘h}`,
an induction on the same terms. One thing had to be done by hand that the paper does not
mention: the readings of the constants are stuck recursions on the type with the whole
premodel as an argument, so Lean cannot see that they ignore the base and the constants,
and each is transferred by its own lemma (`truncate_constRead` and the rest). Then
`isModel_truncate`, the clause for `◇` (`holds_dia`), and **`dia_iff_truncate`**: `◇P`
holds in `A` iff `P` holds in one of its truncations; `box_iff_truncate` likewise for
`□`.

Not yet: the remaining verdicts of the two records, the intrinsic fullness criterion,
and the infinite models.

## Schemas, entailments and rules

The map's principles are type-indexed families, and its arrows say that one family
entails another. Both have a form in this layer (24 September, at Cian's direction).

**Axiom sets and `⟹`** (`Syntax/Entailment.lean`). `Ax₁ ⟹ Ax₂` says every sentence of
`Ax₂` is a theorem of `C.axioms ∪ Ax₁`. The algebra is what one expects, the one lemma of
substance being cut: a derivation from `C ∪ Ax₂` is one from `C ∪ Ax₁` when each
sentence of `Ax₂` is a theorem of `C ∪ Ax₁`, by replacing each use of an axiom by its
(closed, renamed, weakened) derivation; the logical part of both sets is `C` itself,
which is what carries Subst's premises over. Semantically, entailment transfers holding:
in `Prop` (`AxiomSet.Entails.holds`) and in an action model (`entails_holds`), so a model
of `Ax₁` refuting a sentence of `Ax₂` shows `¬ (Ax₁ ⟹ Ax₂)` (`not_entails_of_model`) —
the map's non-implication records. The three moves a metalogical proof makes when it
descends into the object language — cite an axiom of the set, cite a theorem of
Classicism, apply an implication — are `Theorem.ax`, `Theorem.ofC` and `Theorem.mp`.

**Principles as schemas** (`Tools/Schema.lean`, `Certified/Schemas.lean`). A principle
`P` of the shallow layer with parameters `σ …` is quoted as `∀ σ …, P σ …`:
`P.quoted : Ty → … → Sentence`, `P.reflect`, and `P.schema = {P.quoted σ' … | σ' …}`. A
parameter-free principle gives a singleton. All 29 principles are quoted; the map's
schemas over sentences rather than types — No Pure Contingency, Distinctness,
Possibility, `max` — are written by hand in `Syntax/SentenceSchemas.lean`.

**Records as entailments** (`Certified/Entailed.lean`). A record theorem
`foo : P₁ … → … → Q …` has `foo.derivable : ∀ σ' …, Theorem C (imp X₁ (… Y))` with the
principles' bodies unfolded. `#classicism_entails foo` declares
`foo.entails : P₁.schema ∪ … ⟹ Q.schema`: every instance's object types are read off
the statement (`P σ Prop` reads as `P.quoted σ' t`); for each instance `Q.quoted x⃗` of the
conclusion the derivation is specialized to the parameters making its consequent that
instance, each premise is cited as an axiom of its schema and converted where an
operation at a constructor type has been unfolded in the derivation's statement (by the
translator's `unfoldConv` and `coerce`), and the instance's equation is rewritten along.
The proof is `Exists.elim`, `Derivable.impE`, `Derivable.axiom`, `Derivable.conv` and
`Eq.mpr`, checked by the kernel; it rests on `propext` and `Quot.sound` only. The
conclusion set is `Q.schema` when the statement's conclusion is `Q` at its own
parameters; the singleton `{Q.quoted τ}` when it fixes them (`Existence e`); the family
over the derivation's parameters when it builds them (`Existence (σ → t)`).
`#classicism_entails_audit` certifies every record theorem of a module: **all 28
certify**, in seconds, at build time. These `foo.entails` are what the map's arrows can
cite as certificates, once the map's generator is taught the statement shape.

**Records as rules** (`#classicism_rule`, `#classicism_certify`). An entailment forgets
which instance of the premise yields which instance of the conclusion; a metalogical
proof that descends into the object language needs to keep that. `foo.rule` is the
derivation read as a theorem of `C` for every choice of object types,
`∀ σ' …, C.Theorem (imp (P₁.quoted …) (… (Q.quoted …)))`, each instance written through
its schema's `quoted` so that it composes with `Theorem.mp`. `#classicism_certify foo` is
the whole chain at the point where `foo` is stated: schemas for the principles it mentions
that have none yet, the derivation, the rule.

## A metalogical proof with object-level steps

Cian's question of 24 September: a proof in logic typically alternates between the
metalanguage and abbreviated descriptions of derivations in the object language; how
integral to this layer are the separate directory and the slow build, and what is the
workflow for formalizing one such proof? The experiment is `Results/Atomicity.lean`, the map's
arrow `atomicity-t-and-bf-imply-atomicity`, chosen because its informal proof is a
metatheorem "for every `n`" (apply BF `n` times, at each argument type) with an object-level
argument inside: exactly what the shallow layer cannot state, since `Rel` is a class and
not a code, and this layer can.

**The shape.** One file, in three parts. (1) The step, `Atomicity τ → BF σ → Atomicity
(σ → τ)`, is a theorem of the *shallow* layer at the type variables `σ`, `τ`, proved with
Lean's tactics in the paper's own vocabulary: `em`, `le_iff`, `converse_barcan`,
`intensionality`, and each fact carried under the box a closed lemma necessitated with
`nec%` and pushed through with `K`. (2) `#classicism_certify Classicism.atomicity_step`
runs Appendix A on the proof, quotes the principles it mentions into schemas, derives the
strict proof in the object language, and declares `atomicity_step.rule : ∀ σ' τ',
C.Theorem (imp (Atomicity.quoted τ') (imp (Barcan.quoted σ') (Atomicity.quoted (σ' ⇒ τ'))))`
— the derivation read as a rule between instances, with the object types kept, which
`foo.entails` forgets. (3) The theorem is an induction on the relational type
(`RTy.induction`, `Syntax/Types.lean`): at `t` the premise is an axiom of the set
(`Theorem.ax`), at `σ → τ` the rule applied to the induction hypothesis and the BF
instance (`Theorem.ofC`, `Theorem.mp₂`, `Syntax/Entailment.lean`). The descent into the object
language is the type `Theorem (C.axioms ∪ Ax) p` of the goal; the rule is where the
shallow layer's tactics did the object-level work.

**Tools it needed**, each in its natural place. *`Pointwise τ`* (`Classicism/Pointwise.lean`):
the shallow `Rel τ` supplies the pointwise operations and the pointwise implication
`boxImp` as data and only the three laws Intensionality needs, so at a type variable
nothing can be said about them, while the paper reasons freely about tuples ("by
Leibniz's law", "under the box"). The class states the rules of natural deduction read
pointwise — `⊑` a preorder, `∧_τ` a meet, `X ∧ ¬X` below everything, `const_τ p` above
everything when `p` holds and below everything when not, coextension implication both
ways — proved at `Prop` as tautologies and at `σ → τ` from `τ`; its mirror `SPointwise`
(`Strict/Mirror.lean`) is set up as `SOrder` is, and the translator derives each law for every
object type by induction on the type (`inductionInstances`), in milliseconds. *`Atom`*
and *Atomicity* (`Lattice.lean`, `Principles.lean`). *`RTy.induction`*, and the
three moves `Theorem.ax`, `Theorem.ofC`, `Theorem.mp`. *`#classicism_rule`* and
*`#classicism_certify`* (`Tools/Schema.lean`).

**What it taught.** The step was first one tactic proof of forty lines, and its
derivation ran for an hour, its process growing to 27 GB and swapping (that is what took
the machine down on the afternoon of the 24th). Cut into nine closed lemmas
— a possible instance from BF, `A ≤ X`, `Zz ≤ w`, `Z = A`, `Z = ⊥`, and so on, each
three to eight lines — the same argument derives in five to seven minutes at a peak of
664 MB, each lemma's kernel check four to fifteen seconds, provided two things: the
file imports `Schemas` (hence `Transformed`), else `#classicism_certify` re-transforms
the whole shallow library it depends on, in memory; and the translator restores its memo
tables at the end of each nested declaration (`restoreMemo`, `Tools/Translate.lean`). The lesson
about style stands on its own: write object-level steps as short closed lemmas and cite
them, as the paper does.

What could not be fixed is the *serialization*: the module elaborates completely, every
command succeeding, but writing its `.olean` does not finish in half an hour and grows
past 19 GB, in Lean's export of the axioms of every declaration, which walks each body.
A module with one of the nine lemmas writes in seconds (9 MB); the whole does not, and
neither does the nine-command version, so it is the volume of derivations in one module
and not the way they were made. The file is therefore kept out of the build, with its
status in its header. The other cost, the first-in-file specialization of the
Boolean-algebra lemmas, a minute or two, is paid once per file that derives.

**The decision (24 September, Cian).** The experiment answered the question and changed
the plan. The expense is not in the metalogical proof but in the route to the
derivation: the strict proof of a lemma is a per-lemma instance of the Appendix-A
induction, every propositional step an identity `S = ⊤`, Leibniz's law a 4,407-node DAG,
and the translator re-expresses all of that as natural deduction with conversion
certificates. A gated shallow proof is already natural-deduction shaped, and its
derivation would be the size of the shallow term. So the certification is to move to a
**direct translation from shallow proofs to `Derivable`**, with `Derivable` defined as the
paper defines the theory rather than through the eleven identities: `H` closed under
*Elimination*'s rule Subst (substitution of logical equivalents, `P ⊢ Q` and `Q ⊢ P`
on their own, `Δ ⊢ R[P/x]` gives `Δ ⊢ R[Q/x]`), which gives no logical constant a special
role, in de Bruijn form through a one-hole context so that the hole may sit under
binders (that is ξ). The premises of Subst carry no axioms, which is what keeps
`C ∪ {BF}` from proving `□BF`; so the axiom set becomes an index of the inductive, and
the two kinds of assumption — axioms, cited at any context and never discharged;
hypotheses, in the current context and discharged — stay as they are. The eleven
identities become the theorem they are in the paper (Appendix A), to be proved once
about `Derivable`; the mirror classes disappear (a class law at a type variable is
derived by induction from the two shallow instance proofs directly); the quoter, the
normalizer, `coerce`, the memoized walk, `ensureFieldInduction`, and the commands keep
their interface. `Results/Atomicity.lean` is the first file to be certified that way.

**How integral the separation is**: not at all, on this evidence. The shallow lemma, its
certification and the metalogical theorem sit in one file that reads in the order of the
informal proof; the only thing that moves to the metalogical directories is the file itself, because it
imports the object syntax. The build cost is the derivation, seven minutes here,
incurred by the file that does the deriving and cached in its `.olean`.

## Next

The direct translator (above), then this file's certification through it. After that the
remaining verdicts of the two M-set records; then the map's other models as
instances, the symmetric and coalesced ones included. Appendix A as a theorem, and the
coincidence with the Equivalence-rule system, is deferred: nothing depends on it.
