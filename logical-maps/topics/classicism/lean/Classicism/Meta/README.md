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

## The modules, in order

| module | contents |
| --- | --- |
| `Types.lean` | `Ty` and `RTy`, the mutual inductive of Dorr's *Elimination*, Appendix A: `e`, `t`, and `σ ⇒ ρ` for a type `σ` and a relational `ρ`. Decidable equality; every type is `e` or `σ₁ → … → σₙ → t`. |
| `Term.lean` | `Signature`; contexts; `Var`; `Term Sig Γ σ` with the paper's six logical constants `∧`, `∨`, `¬`, `∀σ`, `∃σ`, `=σ` as constructors and Figure 1's abbreviations `→`, `↔`, `⊤`, `⊥`, `□`, `◇` as definitions; purity; renaming and substitution with the identity laws and the four composition laws. |
| `Conversion.lean` | β and η in three grades: the immediate conversion of a redex, the one-step closure `Step`, and the equivalence closure. `Conv`, written `≡`, is βη-conversion, proved a congruence. |
| `Derivation.lean` | `Derivable Ax Δ p`: hypotheses, axioms, the rules for `∧`, `∨`, `¬` with excluded middle, `UI`, `Gen`, `EG`, `Inst`, `Ref`, `LL`, conversion. Weakening and monotonicity admissible; `→` and `↔` rules derived. |
| `Axioms.lean` | The eleven identities as sentences; `C.axiomsMinus` and `C.axioms`, the latter adding Existence at `e`; `C.Derivable`, `C.Theorem`. |
| `Denotation.lean` | `Ty.denote`, `Env`, `Interp`, `Term.denote`: the standard reading of the syntax in Lean, with `t` as `Prop` and `e` as a chosen domain. Renaming and substitution commute with it; conversion preserves it; **soundness** of `Derivable`; the eleven identities hold in `Prop`, so `Prop` is a model of `C` and **`C` is consistent**. |
| `Examples.lean` | A β-step by `rfl`, an η-step, purity decided, small derivations, and the reflection checks: sentences read back are the strict layer's own propositions, by `rfl`. |
| `Relational.lean` | The relational operations `∧_τ`, `¬_τ`, `∨_τ`, coextension, the pointwise box and implication, and `⊤_τ`, `≤_τ`, as **functions on terms by recursion on the type**; the standard reading's `SRel` and `SOrder` instances by the same recursion; and one lemma per operation, by induction on the type, that reading it back gives the strict layer's. Purpose four of this layer, at work. |
| `Quote.lean` | **The quoter**, first half of the translator: `#classicism_quote foo` reads the strict statement of `foo` as a sentence, `foo.quoted`, with type parameters as object-type variables, and declares `foo.reflect`, the `rfl` that reading it back gives the statement. `#classicism_quote_audit` runs it over a module. |
| `Quoted.lean` | The quoter run over the library at build time; home of every `foo.strict.quoted` and `foo.strict.reflect`. |

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
it becomes the object-language operation by recursion on the type, and the reflection
interpretation reads the variable with the strict layer's instance, `instSRelDenote`.
Reflection is then not `rfl`, since both sides are stuck on the type variable, but
rewriting with the lemma for each operation, `reflect_by_rewriting`, and a failure of that
tactic is fatal, not turned into `sorry`. **Every strict statement of the library quotes
and reflects**, 111 of 111 in `Transformed` and 22 of 22 in `Mirror`.

## Next

The translation of strict proofs into derivations; then Appendix A, and the coincidence
with the Equivalence-rule system.
