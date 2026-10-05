# Full action model: surjections of an infinite set

<p class='cert'>Model — Source: Classicism (2024); produced by Andrew Bacon and Cian Dorr; recorded by OpenAI Codex (GPT-6), 17 September 2026.</p>

## Package

- **No Pure Contingency.** Each closed sentence of the pure language, if true, is necessary. This is a sentence schema, not a quantifier over propositions.
- **Rigid Comprehension.** Every relation, including a proposition, is coextensive with a rigid one.
- **Atomicity.** Every non-bottom entity of each relational type has an atom below it.
- **BF.** The Barcan Formula at every type. The predicate formulation closes the formula schema using lambda abstraction.
- **Relational Choice.** Every serial binary relation has a functional subrelation.
- **Axiom of Infinity (type e).** There are not finitely many individuals. No finite cardinality holds of the universal property, so the domain of the type cannot be exhausted by finitely many steps from the empty property.
- **Axiom of Infinity (type t).** There are not finitely many propositions. No finite cardinality holds of the universal property, so the domain of the type cannot be exhausted by finitely many steps from the empty property.
- **No Contingency (signature Σ).** Each closed sentence of the language of the fixed signature Sigma, if true, is necessary. A sentence schema, standing to No Pure Contingency as Possibility Maximalism (signature Σ) stands to Possibility Maximalism (pure).
- **□Rigid Comprehension.** Necessarily, every relation, including a proposition, is coextensive with a rigid one.
- **□Atomicity.** Necessarily, every non-bottom entity of each relational type has an atom below it.
- **□Actuality.** Necessarily, there is a true proposition that entails every true proposition.
- **□BF.** Necessarily, the Barcan Formula holds at every type. The predicate formulation closes the formula schema using lambda abstraction.
- **□Strong Leibniz Biconditionals (type t).** Necessarily, every possible proposition is entailed by a strong world proposition, one that is possible and necessarily entails every proposition or its negation.
- **□Relational Choice.** Necessarily, every serial binary relation has a functional subrelation.
- **B for sentences of Σ.** The B instance for every closed sentence of the language of the fixed signature Sigma.
- **Transversal Choice.** Every equivalence relation, at any type including e, has a transversal, that is, a property with exactly one instance in each of its cells.
- **¬ ND (type t).** ND (type t) in the displayed closed propositional formulation.
- **¬ Independence (signature Σ).** No constant of Sigma is a pure operation applied to other constants: for a closed pure term A and distinct constants c, d_1,…,d_n with n ≥ 0, c differs from A applied to the d’s. With n = 0, no constant denotes a pure entity.
- **¬ Distinctness-preserving collapse.** Every truth is necessary under the distinctness-preserving modality.
- **¬ Witnessed Possibility.** For pure-formulas P with free variables among a finite tuple x, and distinct matching nonlogical constants c, a witness to P entails that P at those constants is possible.
- **¬ Separated Structure.** For each typed nonlogical constant c and closed same-typed terms F,G not containing c, equality after application to c implies equality of F and G.
- **¬ Distinctness Maximalism (signature Σ).** The Distinctness Maximalism schema for the fixed nonlogical signature Sigma.

## Definition

Use the monoid of surjections of an infinite set and a surjective individual action, at its sole object.

Interpretation of Σ, fixed for this record: each relational constant denotes the top element of its type and each individual constant denotes one fixed individual $d$.

## Arguments

### Holds No Pure Contingency, Rigid Comprehension, Atomicity, BF. Fails ND (type t).

The source cites Bacon 2020, Proposition A.3 for the higher-type surjectivity argument.

*Source: Classicism, §3.5, p. 59, third paragraph. By Andrew Bacon and Cian Dorr, 2026-09-17.*

### Holds Relational Choice.

With choice in the metatheory a serial relation has a functional subrelation, and a full model contains every intension, so that subrelation is in the domain; see Classicism, p. 61, on the principles common to full models.

*Source: Classicism, p. 61. By Claude Fable 5.1 (Anthropic), at Cian Dorr's direction, 2026-09-20.*

### Holds Axiom of Infinity (type e), Axiom of Infinity (type t).

The individuals are an infinite set and the arrows an infinite monoid, identity at the identity arrow is literal, and the numeral sets at each type are intensions of a full model, so no finite cardinality holds of the universal property at type e or at type t.

*By Claude Fable 5.1 (Anthropic), at Cian Dorr's direction, 2026-09-20.*

### Fails Independence (signature Σ).

With $c\in\Sigma$ of relational type $\tau$, $c=\top_\tau$ necessarily, so Witnessed Possibility fails for the pure formula $x\ne\top_\tau$, Separated Structure fails since $\lambda x\, .\,x$ and $\lambda x\, .\,\top_\tau$ agree on $c$, Independence (signature Σ) fails since $c$ denotes what a closed pure term denotes, and Distinctness Maximalism (signature Σ) fails since $c=\top_\tau$ is true and unprovable.

*Address: `full-surjection-monoid#sigma-top`. By Claude Fable 5.1 (Anthropic), at Cian Dorr’s request, 2026-09-22.*

### Holds No Contingency (signature Σ).

The relational constants denote pure entities, so a closed Σ-sentence denotes what some $P(d,\ldots,d)$ denotes for a pure formula $P$; the model’s automorphisms carry every individual to every other, so $P(d,\ldots,d)$ is materially equivalent to the pure sentence $\forall x\, .\,P(x,\ldots,x)$ and its negation to $\forall x\, .\,\neg P(x,\ldots,x)$; whichever is true is necessary by No Pure Contingency, and instantiation under the box gives $\Box P(d,\ldots,d)$ or $\Box\neg P(d,\ldots,d)$.

*By Claude Fable 5.1 (Anthropic), at Cian Dorr’s request, 2026-09-23.*

### Fails Distinctness-preserving collapse.

Let $p:=\{\mathrm{id}\}$, true. Any witness $q$ for $\Box_{\ne}p$ is true, so contains the identity, and for a non-identity bijection $i$ the arrow $i^{-1}$ gives $i^{-1}\circ i\in q$, so $\Diamond q$ holds under $i$ while $p$ does not. So no true $q$ has $\Box(\Diamond q\to p)$.

*By Claude Fable 5.1 (Anthropic), 2026-09-23.*

### Holds □Rigid Comprehension, □Atomicity, □Actuality, □BF. In reserve.

*Source: Classicism, §3.5, p. 59, third paragraph; p. 61 and n. 84. By Andrew Bacon and Cian Dorr, 2026-09-17.*

### Fails Witnessed Possibility, Separated Structure, Distinctness Maximalism (signature Σ). In reserve.

Fixed an interpretation of Σ (relational constants as top, individual constants as one fixed individual) and recorded the signature schemata it refutes, at Cian Dorr’s request.

*By Claude Fable 5.1 (Anthropic), 2026-09-22.*

### Holds □Strong Leibniz Biconditionals (type t). In reserve.

Added □Strong Leibniz Biconditionals (type t): every singleton of an arrow is a strong world in a propositionally full one-object model; see the notes.

*By Claude Fable 5.1 (Anthropic), 2026-09-22.*

### Holds □Relational Choice. In reserve.

Boxed the Relational Choice claim; see the notes.

*By Claude Fable 5.1 (Anthropic), 2026-09-22.*

### Holds B for sentences of Σ. In reserve.

Re-fixed the interpretation of Σ so as to settle No Contingency (signature Σ) and B for sentences of Σ, at Cian Dorr’s request; see the notes.

*By Claude Fable 5.1 (Anthropic), 2026-09-23.*

### Holds Transversal Choice. In reserve.

Added Transversal Choice, by the argument recorded for Relational Choice: a full model contains every intension, in particular one whose extension at the evaluation point is a transversal, chosen in the metatheory, of the extension there of an equivalence relation; the equivalence and transversal conditions are unboxed. Recorded on a question of Zachary Goodsell, after an observation of Christopher Sun.

*By Claude Fable 5.1 (Anthropic), 2026-09-25.*


## Notes

The cited construction is a model of the map’s relational-type framework. The description identifies its evaluation point; construction and verification are given at the PDF locations in References.
Under it the signature schemata that give the constants a special role fail: with $c\in\Sigma$ of relational type $\tau$, $c=\top_\tau$ necessarily, so Witnessed Possibility fails for the pure formula $x\ne\top_\tau$, Separated Structure fails since $\lambda x\, .\,x$ and $\lambda x\, .\,\top_\tau$ agree on $c$, Independence (signature Σ) fails since $c$ denotes what a closed pure term denotes, and Distinctness Maximalism (signature Σ) fails since $c=\top_\tau$ is true and unprovable. But No Contingency (signature Σ), and with it B for sentences of Σ, hold. In a one-object model whose propositions are all the sets of arrows, a singleton $\{h\}$ is a strong world exactly when its transport $\{j : j\circ i=h\}$ along every arrow $i$ has at most one member, since the propositions at that world are again all sets of arrows and a two-element set is split by a singleton. Here every arrow is a surjection, so $j\circ i=j^{\prime}\circ i$ forces $j=j^{\prime}$. So every singleton is a strong world, every possible proposition contains an arrow, and the type-t Strong Leibniz Biconditionals hold at every world. □Relational Choice holds: the truncation of a full action model at any arrow is again a full action model, its domains at the reachable objects being unchanged, and Relational Choice holds in every full model given choice in the metatheory (Classicism, p. 61).

## History

The record's revision log before it was written as arguments.

- **2026-09-25** (Claude Fable 5.1 (Anthropic)) — Added Transversal Choice, by the argument recorded for Relational Choice: a full model contains every intension, in particular one whose extension at the evaluation point is a transversal, chosen in the metatheory, of the extension there of an equivalence relation; the equivalence and transversal conditions are unboxed. Recorded on a question of Zachary Goodsell, after an observation of Christopher Sun. Now satisfies: Transversal Choice.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Recorded the Distinctness-preserving collapse; see the notes. Now violates: Distinctness-preserving collapse.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Re-fixed the interpretation of Σ so as to settle No Contingency (signature Σ) and B for sentences of Σ, at Cian Dorr’s request; see the notes. Now satisfies: No Contingency (signature Σ), B for sentences of Σ.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Corrected the justification of □Strong Leibniz Biconditionals (type t): the 22 September argument tacitly used that the monoid is right-cancellative, which holds here; no verdict changes.
- **2026-09-22** (Claude Fable 5.1 (Anthropic)) — Fixed an interpretation of Σ (relational constants as top, individual constants as one fixed individual) and recorded the signature schemata it refutes, at Cian Dorr’s request. Now violates: Witnessed Possibility, Separated Structure, Independence (signature Σ), Distinctness Maximalism (signature Σ).
- **2026-09-22** (Claude Fable 5.1 (Anthropic)) — Added □Strong Leibniz Biconditionals (type t): every singleton of an arrow is a strong world in a propositionally full one-object model; see the notes. Now satisfies: □Strong Leibniz Biconditionals (type t).
- **2026-09-22** (Claude Fable 5.1 (Anthropic)) — Boxed the Relational Choice claim; see the notes. Now satisfies: □Relational Choice.
- **2026-09-20** (Claude Fable 5.1 (Anthropic)) — Added Relational Choice at Cian Dorr's direction. With choice in the metatheory a serial relation has a functional subrelation, and a full model contains every intension, so that subrelation is in the domain; see Classicism, p. 61, on the principles common to full models. Added both Axioms of Infinity: the individuals are an infinite set and the arrows an infinite monoid, identity at the identity arrow is literal, and the numeral sets at each type are intensions of a full model, so no finite cardinality holds of the universal property at type e or at type t. Now satisfies: Relational Choice, Axiom of Infinity (type e), Axiom of Infinity (type t).
- **2026-09-17** (OpenAI Codex (GPT-6)) — Adopted the source’s relational type system at the user’s request. The cited construction now directly supplies the recorded model; the former type-extension obligation is removed. Now satisfies: □Rigid Comprehension, □Atomicity, □Actuality, □BF, No Pure Contingency. Now violates: ND (type t).

## Sources

- **Classicism** — Andrew Bacon and Cian Dorr, Classicism, draft of 16 May 2023, §3.5, p. 59, third paragraph; p. 61 and n. 84.

<p class='cert'>Record: <code>topics/classicism/models/full-surjection-monoid.yaml</code></p>

## Paper references

- **Proof: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — §3.5, p. 59, third paragraph; p. 61 and n. 84
- **Proof: Logical Combinatorialism.** Bacon, Andrew (2020). Logical Combinatorialism. Philosophical Review 129(4), 537–589. As cited in Classicism, §§2.5 and 3.5. Read directly for the import of 22 September 2026; section, footnote and page locators refer to the published pagination. — Proposition A.3, as cited in Classicism p. 59
