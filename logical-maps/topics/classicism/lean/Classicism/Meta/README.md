# The metalogical layer

This folder is the third layer of the formalisation. The **shallow** layer states and
proves theorems of Classicism in Lean, under a gate that admits `propext` and `funext`
only with closed arguments. The **strict** layer re-proves them from the eleven closed
identities alone, by a transformer that carries out Appendix A on Lean proof terms. Both
prove theorems *in* Classicism. This layer proves theorems *about* it: the terms of the
object language, their derivations and their models are objects of Lean, so that one can
say that a sentence is a theorem of Classicism, that a schema implies a schema, that a
closed pure sentence is necessary if true, that a sentence holds in a model.

Earlier notes called this the "deep" layer; **metalogical** is the name now.

## What it is for

Four things, none of which the other two layers can do.

1. **Metalogical statements.** "Schema A implies schema B" as a theorem about instances;
   No Pure Contingency, a sentence schema over closed *pure* sentences; the Maximalist
   principles, which quantify over syntax.
2. **Model evidence.** A denotation of the syntax into Lean's own `Prop` is the full
   Henkin model, and other interpretations of the same syntax are the other models on the
   map, so consistency records become checked facts.
3. **Appendix A as a theorem.** The transformer certifies theorems one at a time; that the
   eleven identities axiomatize the theory closed under the rule of Equivalence needs
   derivations as objects.
4. **Induction on the structure of types**, which the shallow layer's classes `Rel` and
   `Order` cannot perform.

## Design decisions

All were settled with Cian on 22 September 2026.

- **The syntax is its own datatype, not a subtype of Lean's `Expr`.** This layer proves
  theorems about substitution and conversion, and `Expr`'s are implemented behind
  `extern` with no equations; a typing relation for `Expr` is the Lean4Lean project; and
  the metalogical statements need a small closed grammar with decidable notions of
  "closed" and "pure". The bridge to the shallow layer is the reflection pattern: a
  denotation `⟦·⟧` from terms to propositions, and a quotation `⌜·⌝` the other way, with
  `⟦⌜p⌝⟧ = p` checked by `rfl` per theorem.
- **Terms are intrinsically typed.** `Term Sig Γ σ` is the type of terms of type `σ` with
  free variables from `Γ`; an ill-typed term cannot be written.
- **Variables are de Bruijn indices**, so α-equivalence is identity and only β and η
  remain. No higher-order abstract syntax.
- **The type system is fixed**: `e` and `t` are the only base types. Nonlogical
  vocabulary enters through a `Signature` of constants; the pure language is the empty
  signature.
- **Derivations are not a separate datatype.** `Derivable Ax Δ p` is an inductive
  predicate, by definition the smallest relation closed under its rules, which is the
  paper's notion of an `H`-theory; a proof of it *is* a derivation tree. A `Type`-valued
  twin would allow computing with derivations at the price of proof relevance in every
  lemma, and nothing planned needs it.
- **No rule is special.** The official system is `H`, in natural-deduction form, plus an
  axiom set, and Classicism is the eleven identities as that set. So a map record "`C`
  plus BF proves this instance" is derivability over a union of axiom sets. The rule of
  Equivalence is Appendix A's *theorem* about this system, to be proved, and the
  Equivalence-rule system will be defined separately and shown to coincide.
- **The translator will read strict proofs**, not shallow ones. Their statements are
  already in the paper's vocabulary, their only special constants are the eleven axioms,
  and the proof walk then exists once, in the transformer.
- **The type-subscripted operations are constants of the syntax with an unfolding rule**
  (23 September, with Cian). `∧_τ`, `¬_τ`, coextension and the rest were first
  functions on terms by recursion on the type. A function stuck at a type *variable* is
  not a node of the syntax: renaming and substitution could not pass through it, and no
  derivation could mention `∧_τ` for `τ` a variable, which a derivation by induction on
  the type must. So `Term.andR ρ` is a constructor, and the recursion is the δ-rule of
  conversion, `∧_t ≡ ∧` and `∧_{σ→ρ} ≡ λX Y z. X z ∧_ρ Y z`, alongside β and η.

## The modules, in order

| module | contents |
| --- | --- |
| `Types.lean` | `Ty` and `RTy`, the mutual inductive of Dorr's *Elimination*, Appendix A: `e`, `t`, and `σ ⇒ ρ` for a type `σ` and a relational `ρ`. Decidable equality; every type is `e` or `σ₁ → … → σₙ → t`. |
| `Term.lean` | `Signature`; contexts; `Var`; `Term Sig Γ σ` with the paper's six logical constants `∧`, `∨`, `¬`, `∀σ`, `∃σ`, `=σ` and the seven type-subscripted operations `∧_ρ`, `¬_ρ`, … as constructors, Figure 1's abbreviations `→`, `↔`, `⊤`, `⊥`, `□`, `◇` as definitions, and `Term.unfoldR`, the one-step unfolding of an operation at a constructor type; purity; renaming and substitution, through `Term.rec` for the kernel's sake, with the identity laws and the four composition laws. |
| `Conversion.lean` | β, η and δ in three grades: the immediate conversion of a redex, the one-step closure `Step`, and the equivalence closure. `Conv`, written `≡`, is βηδ-conversion, proved a congruence and stable under renaming. |
| `Derivation.lean` | `Derivable Ax Δ p`: hypotheses, axioms, the rules for `∧`, `∨`, `¬` with excluded middle, `UI`, `Gen`, `EG`, `Inst`, `Ref`, `LL`, conversion. Weakening and monotonicity admissible; `→` and `↔` rules derived. |
| `Axioms.lean` | The eleven identities as sentences; `C.axiomsMinus` and `C.axioms`, the latter adding Existence at `e`; `C.Derivable`, `C.Theorem`. |
| `Denotation.lean` | `Ty.denote`, `Env`, `Interp`, `Term.denote`: the standard reading of the syntax in Lean, with `t` as `Prop` and `e` as a chosen domain. Renaming and substitution commute with it; conversion preserves it; **soundness** of `Derivable`; the eleven identities hold in `Prop`, so `Prop` is a model of `C` and **`C` is consistent**. |
| `Examples.lean` | A β-step by `rfl`, an η-step, purity decided, small derivations, and the reflection checks: sentences read back are the strict layer's own propositions, by `rfl`. |
| `Relational.lean` | The bridge for the type-subscripted operations `∧_τ`, `¬_τ`, `∨_τ`, coextension, the pointwise box and implication (constants of `Term.lean`, read in `Denotation.lean` by recursion on the type): the standard reading's `SRel` and `SOrder` instances by the same recursion, and one lemma per operation, by induction on the type, that its reading is the strict layer's. Purpose four of this layer, at work. |
| `Quote.lean` | **The quoter**, first half of the translator: `#classicism_quote foo` reads the strict statement of `foo` as a sentence, `foo.quoted`, with type parameters as object-type variables, and declares `foo.reflect`, the `rfl` that reading it back gives the statement. `#classicism_quote_audit` runs it over a module. |
| `Quoted.lean` | The quoter run over the library at build time; home of every `foo.strict.quoted` and `foo.strict.reflect`. |
| `Normalize.lean` | A **verified βη-normalizer** on the syntax, `Term.nf`, with `Conv.of_nf`: two terms with the same normal form convert, the hypothesis decided by evaluation. |
| `Translate.lean` | **The translator**, second half: `#classicism_derive foo` reads the strict proof of `foo` and declares `foo.derivable`, a kernel-checked derivation of `foo.quoted`. `#classicism_derive_audit` runs it over a module. |
| `Derived.lean` | Two quick derivations run at build time, as a check that the whole chain works. |

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
holds in `I`; the eleven identities hold in `Prop`, each by `propext` and `funext`, so
Lean's `Prop` is a model of Classicism and `C` proves no falsehood of it, in particular
not `⊥`. The reflection examples check that reading back a sentence gives exactly the
strict layer's proposition, by `rfl`: `⊤` reads back as `Strict.Top`, `→` as `imp`, and
each axiom as the statement of the corresponding Lean axiom. That equation, `⟦⌜p⌝⟧ = p`,
is what the translator's quotations will be held to.

## The quoter

`Quote.lean` is a meta-program reading a strict statement as object syntax: `Prop`, `e`,
arrows and guarded type parameters as types; the connectives, quantifiers, identity, the
paper's `imp`, `iff`, `Top`, `Bot`, `Box`, `Dia`, λ and application as terms; and any other
constant of the library through its definition, so a principle such as
`P.Functionality.strict` quotes through its body and a class operation at a concrete type
through its instance. The sentence is built as Lean syntax and elaborated against
`Sentence Signature.pure`, so an ill-formed quotation fails to elaborate. The quoter is not
trusted: the reflection theorem `foo.reflect`, that reading the sentence back in the
interpretation with domain `e` gives the strict statement with each type variable read as
its denotation, is checked by the kernel by `rfl`. If the quoter produced the wrong
sentence the check would fail, as it did once during development, when `◇` had been
defined as `¬□¬` where the strict layer has `¬(· = ⊥)`.

A strict statement with a parameter of class `SRel` or `SOrder` quotes through
`Relational.lean`: the parameter becomes a variable of type `RTy`, each class operation at
it becomes the object-language constant `andR τ'` and the like, and the reflection
interpretation reads the variable with the strict layer's instance, `instSRelDenote`. At
a constructor type the operation is not quoted as the constant: the strict instance
unfolds and the operation is read through it, so the constants stand only at type
variables, where the kernel and the normalizer agree that they are stuck.
Reflection is then not `rfl`, since both sides are stuck on the type variable, but
rewriting with the lemma for each operation, `reflect_by_rewriting`, and a failure of that
tactic is fatal, not turned into `sorry`. **Every strict statement of the library quotes
and reflects**, 111 of 111 in `Transformed` and 22 of 22 in `Mirror`.

## The translator

`Translate.lean` is the second half: `#classicism_derive foo` reads the **strict** proof
of `foo` and declares `foo.derivable : ∀ σ' …, Theorem C.axioms(Minus) (foo.quoted σ' …)`,
a derivation of the quoted statement that the kernel checks. With it the chain is
complete for each theorem it reaches: the shallow proof in Lean, the transformer's strict
proof from the eleven axioms, and a derivation in `H` plus the eleven identities as an
object of Lean, every link kernel-checked and every translator untrusted.

Strict proofs are almost entirely equational, so the translation is chiefly Leibniz's
Law: each of Lean's `congrArg`, `Eq.trans`, `Eq.symm`, `Eq.mpr` and `congrFun` is `LL` at a
predicate, and `Derivation.lean` has the derived rule for each. The natural-deduction
constructors that remain, `Or.elim`, `And.intro`, `Exists.elim` and a few more, map to
the rules by name. A library theorem cited in a proof is translated **once, at
object-type variables** for its type parameters, as `c.derivable : ∀ σ' … ρ' …,
Theorem Ax (S σ' … ρ' …)`, and cited through `Derivable.ofTheorem` applied to the object
types the citation's type parameters quote to. A class instance among a lemma's
parameters becomes nothing: the class's operations at the variable are the object
constants `andR ρ'` and the like, and its laws are derived by induction on the type,
below. So `BA.meet_comm`, proved in the strict layer for any Boolean algebra, has one
derivation, with `∧_ρ'` in it, and its use at `σ → Prop` is that derivation at
`σ' ⇒ t` — which is what a type variable in a derivation is for. A first version
specialized each lemma at each type it was used at, and re-derived the Boolean-algebra
laws through the arrow instances' congruence proofs at every type: `ll_lam`, whose
tautology sits three arrows deep, took the kernel hours that way, and takes 17 seconds
now.

Two things make it tractable. Everything is built directly as an expression with every
implicit argument supplied, never through unification; the option
`Classicism.Meta.Translate.check` type-checks each node for debugging. And conversion,
where Lean's kernel silently β-reduced, is one reflective lemma: `Normalize.lean` has a
verified βη-normalizer `Term.nf`, and `Conv.of_nf n a b rfl` is a conversion proof the
kernel discharges by evaluation. An untyped shadow of the syntax, `Tm`, decides where a
conversion is needed and with how much fuel; where none is, the derivation is used as it
is and the kernel evaluates the substitution. Rule variants concluding with
`Term.instantiate`, `allEβ` and friends, match Lean's typing of an application, which
substitutes.

**What it costs.** A library theorem takes seconds to a few minutes, most of it the
kernel evaluating substitutions where a rule concludes `b[a]` and the quoted formula is
its value. That is why `rename`, `subst`, `prename` and `step` are written through
`Term.rec` directly rather than by structural recursion, with `rfl` equations as their
simp set and the structural version kept for the compiler (`implemented_by`): the kernel
evaluates a definition compiled through `brecOn` about ten times slower. A cited lemma is
translated once and reused across a file, and the proof term is walked as the DAG it is
(`ll_lam`'s is 4,407 nodes shared, 1,516,016 as a tree). `Classicism.Meta.Translate.profile`
prints the time by phase, and with `.progress` set, a line per translation with its
kernel time.

**A law of a class at a type variable is derived by induction on the type.** The strict
layer holds the six Boolean identities as the fields of `BA`, and `SRel.coext_refl`,
`and_constP_true`, `and_constP_coext` and `SOrder.le_iff` as fields of the mirrors, each
proved once at `Prop` and once at `σ → τ` from the law at `τ`.
A strict proof that cites such a law at a type *variable* cites no axiom and no theorem,
and there is no one derivation of the law: there is one for every object type, by
induction on it. `ensureFieldInduction` builds it, `SRel.coext_refl.derivable : ∀ τ',
Theorem Ax (S τ')`, through `RTy.rec`: the base case is the translation of the `Prop`
instance's proof, the step is the translation of the arrow instance's proof with the law
at the smaller type, cited through the instance variable, as the induction hypothesis,
and a lemma cited under the hypothesis takes it as a parameter. The law at a constructor
type has its operations unfolded first, `unfoldConv`, by `Conv.delta` under congruences,
as does any theorem cited at a constructor type; the normalizer itself knows no δ,
since an unfolding decided by matching on the type is stuck at a type variable, and a
stuck term is one the kernel can compare with nothing. This is the use of the
metalogical layer that the shallow and strict layers could not provide: induction on
the structure of a relational type.

**What the kernel is given.** Three findings, each measured, shape the conversion
certificate. The kernel evaluates one side against a tree as written quickly, and
compares two forms it must unfold lazily against each other slowly: so each side of a
coercion is first bridged to its canonical tree (the shadow written back, `canon`), and
`Conv.of_nf` is used only in its one-sided forms — given `nf n a = nf n b` the kernel
unfolds both sides in step, comparing the recursor's minor premises at every level,
and a theorem that took 17 seconds took an hour. The normalizer is evaluated only on
what differs: the two trees are descended together by congruence while their roots are
stable under normalization, and `of_nf` joins the subterms at the first difference
(`diffConv`). And explicit β- and η-steps for every pass, tried in between, cost more
than either, since they write out every intermediate formula.

**Running the audit.** `#classicism_derive_audit Classicism.Transformed` takes the
better part of an hour; Lean captures what elaboration prints, so set
`Classicism.Meta.Translate.progress` to a file to watch it, and set `maxHeartbeats`
high but finite, so that a theorem that runs away fails on its own rather than being
found hours later. `Derived.lean` runs two quick ones at build time.

## Next

The audit of the translator over the library with the class laws by induction; then
Appendix A, and the coincidence with the Equivalence-rule system.
