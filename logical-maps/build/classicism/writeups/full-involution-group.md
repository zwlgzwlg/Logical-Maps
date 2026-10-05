# Full action model: two-element group

<p class='cert'>Model — Source: Classicism (2024); produced by Andrew Bacon and Cian Dorr; recorded by OpenAI Codex (GPT-6), 17 September 2026.</p>

## Package

- **Atomicity.** Every non-bottom entity of each relational type has an atom below it.
- **□ND.** Necessarily, distinct things of any type are necessarily distinct.
- **Relational Choice.** Every serial binary relation has a functional subrelation.
- **□Rigid Comprehension.** Necessarily, every relation, including a proposition, is coextensive with a rigid one.
- **□Atomicity.** Necessarily, every non-bottom entity of each relational type has an atom below it.
- **□Actuality.** Necessarily, there is a true proposition that entails every true proposition.
- **No Pure Contingency.** Each closed sentence of the pure language, if true, is necessary. This is a sentence schema, not a quantifier over propositions.
- **□Strong Leibniz Biconditionals (type t).** Necessarily, every possible proposition is entailed by a strong world proposition, one that is possible and necessarily entails every proposition or its negation.
- **□Relational Choice.** Necessarily, every serial binary relation has a functional subrelation.
- **Transversal Choice.** Every equivalence relation, at any type including e, has a transversal, that is, a property with exactly one instance in each of its cells.
- **¬ Fregean Axiom.** Materially equivalent propositions are identical.
- **¬ Infinity Schema (type t).** There are arbitrarily many pairwise distinct entities of this fixed type; one sentence for each positive integer n.
- **¬ No Contingency (signature Σ).** Each closed sentence of the language of the fixed signature Sigma, if true, is necessary. A sentence schema, standing to No Pure Contingency as Possibility Maximalism (signature Σ) stands to Possibility Maximalism (pure).
- **¬ Independence (signature Σ).** No constant of Sigma is a pure operation applied to other constants: for a closed pure term A and distinct constants c, d_1,…,d_n with n ≥ 0, c differs from A applied to the d’s. With n = 0, no constant denotes a pure entity.
- **¬ Axiom of Infinity (type t).** There are not finitely many propositions. No finite cardinality holds of the universal property, so the domain of the type cannot be exhausted by finitely many steps from the empty property.
- **¬ Witnessed Possibility.** For pure-formulas P with free variables among a finite tuple x, and distinct matching nonlogical constants c, a witness to P entails that P at those constants is possible.
- **¬ Separated Structure.** For each typed nonlogical constant c and closed same-typed terms F,G not containing c, equality after application to c implies equality of F and G.
- **¬ Distinctness Maximalism (signature Σ).** The Distinctness Maximalism schema for the fixed nonlogical signature Sigma.

## Definition

The full action model on the two-element group $\{1,k\}$ with $k^2=1$: the construction of Classicism p. 59 (record full-idempotent-monoid) with the two-arrow multiplication changed to $k^2=1$. Evaluate at the sole object. The propositions at the evaluation object are the subsets of the two arrows out of it, four in all, and every intension of a full model is present.

Interpretation of Σ, fixed for this record: one designated relational constant $c$ of type $\tau=\bar\sigma t$ denotes $\lambda\bar x\, .\,a$, where $a$ is the unique true atom of the model, the actual-world proposition $\{1\}$; every other relational constant denotes the top element of its type and every individual constant one fixed individual.

## Arguments

### Holds Atomicity, □ND. Fails Fregean Axiom.

The source establishes boxed ND and exhibits four propositions.

*Source: Classicism, §3.5, p. 59, second paragraph; p. 61. By Andrew Bacon and Cian Dorr, 2026-09-17.*

### Holds Relational Choice.

With choice in the metatheory a serial relation has a functional subrelation, and a full model contains every intension, so that subrelation is in the domain; see Classicism, p. 61, on the principles common to full models.

*Source: Classicism, p. 61. By Claude Fable 5.1 (Anthropic), at Cian Dorr's direction, 2026-09-20.*

### Fails Infinity Schema (type t).

The propositions at the evaluation object are the subsets of the two arrows out of it, four in all, and every intension of a full model is present, so the numerals are the finite cardinalities and the fourth holds of the universal property of propositions: the Axiom of Infinity at type t fails, as does the fifth instance of the schema.

*By Claude Fable 5.1 (Anthropic), at Cian Dorr's direction, 2026-09-20.*

### Fails No Contingency (signature Σ), Independence (signature Σ).

No Contingency (signature Σ) fails, since the Σ-sentence $\forall\bar x\, .\,c\bar x$ denotes $a$, true and contingent; Witnessed Possibility fails for the pure formula $x=\top_\tau$, witnessed by $\top_\tau$, since $\Diamond(c=\top_\tau)$ is $\Diamond\Box a$ and $a$ is necessary at no arrow; Separated Structure fails with it, being equivalent to Possibly Witnessed Possibility; Independence (signature Σ) and Distinctness Maximalism (signature Σ) fail through the other relational constants, Σ being assumed to contain at least one: such a constant $c'$ of type $\tau'$ denotes what the closed pure term $\top_{\tau'}$ denotes, and $c'=\top_{\tau'}$ is a true identity that C(Σ) does not prove. The designated constant refutes neither: closed pure terms denote entities fixed by every arrow (Classicism, §3.5, p. 58), whereas $a$ is fixed by no arrow but the identity, so no closed pure term denotes $\lambda\bar x\, .\,a$. Everything that implies these fails with them.

*Address: `full-involution-group#sigma-true-atom`. By Claude Fable 5.1 (Anthropic), at Cian Dorr’s request, 2026-09-22.*

*Revised 2026-09-23 by Claude Fable 5.1 (Anthropic):* Interpretation of Σ re-fixed (designated constant denotes the true atom) so as to settle No Contingency (signature Σ), at Cian Dorr’s request; No Contingency added.

*Revised 2026-09-23 by Claude Fable 5.1 (Anthropic):* Corrected the reason for the Independence and Distinctness failures: they come from the other relational constants, not the designated one. No verdict changed.

### Holds □Rigid Comprehension, □Atomicity, □Actuality, No Pure Contingency. In reserve.

*Source: Classicism, §3.5, p. 59, second paragraph; p. 61. By Andrew Bacon and Cian Dorr, 2026-09-17.*

### Fails Axiom of Infinity (type t). In reserve.

Added Relational Choice at Cian Dorr's direction. With choice in the metatheory a serial relation has a functional subrelation, and a full model contains every intension, so that subrelation is in the domain; see Classicism, p. 61, on the principles common to full models. The propositions at the evaluation object are the subsets of the two arrows out of it, four in all, and every intension of a full model is present, so the numerals are the finite cardinalities and the fourth holds of the universal property of propositions: the Axiom of Infinity at type t fails, as does the fifth instance of the schema.

*By Claude Fable 5.1 (Anthropic), 2026-09-20.*

### Fails Witnessed Possibility, Separated Structure, Distinctness Maximalism (signature Σ). In reserve.

Fixed an interpretation of Σ (relational constants as top, individual constants as one fixed individual) and recorded the signature schemata it refutes, at Cian Dorr’s request.

*By Claude Fable 5.1 (Anthropic), 2026-09-22.*

### Holds □Strong Leibniz Biconditionals (type t). In reserve.

Added □Strong Leibniz Biconditionals (type t): every singleton of an arrow is a strong world in a propositionally full one-object model; see the notes.

*By Claude Fable 5.1 (Anthropic), 2026-09-22.*

### Holds □Relational Choice. In reserve.

Boxed the Relational Choice claim; see the notes.

*By Claude Fable 5.1 (Anthropic), 2026-09-22.*

### Holds Transversal Choice. In reserve.

Added Transversal Choice, by the argument recorded for Relational Choice: a full model contains every intension, in particular one whose extension at the evaluation point is a transversal, chosen in the metatheory, of the extension there of an equivalence relation; the equivalence and transversal conditions are unboxed. Recorded on a question of Zachary Goodsell, after an observation of Christopher Sun.

*By Claude Fable 5.1 (Anthropic), 2026-09-25.*


## Notes

The cited construction is a model of the map’s relational-type framework. The description identifies its evaluation point; construction and verification are given at the PDF locations in References.
Change the two-arrow multiplication to k²=1; evaluate at the sole object.
In a one-object model whose propositions are all the sets of arrows, a singleton $\{h\}$ is a strong world exactly when its transport $\{j : j\circ i=h\}$ along every arrow $i$ has at most one member, since the propositions at that world are again all sets of arrows and a two-element set is split by a singleton. Here the arrows form a group, so $j\circ i=j^{\prime}\circ i$ forces $j=j^{\prime}$. So every singleton is a strong world, every possible proposition contains an arrow, and the type-t Strong Leibniz Biconditionals hold at every world. □Relational Choice holds: the truncation of a full action model at any arrow is again a full action model, its domains at the reachable objects being unchanged, and Relational Choice holds in every full model given choice in the metatheory (Classicism, p. 61).

## History

The record's revision log before it was written as arguments.

- **2026-09-25** (Claude Fable 5.1 (Anthropic)) — Added Transversal Choice, by the argument recorded for Relational Choice: a full model contains every intension, in particular one whose extension at the evaluation point is a transversal, chosen in the metatheory, of the extension there of an equivalence relation; the equivalence and transversal conditions are unboxed. Recorded on a question of Zachary Goodsell, after an observation of Christopher Sun. Now satisfies: Transversal Choice.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Re-fixed the interpretation of Σ so as to settle No Contingency (signature Σ) and B for sentences of Σ, at Cian Dorr’s request; see the notes. Now violates: No Contingency (signature Σ).
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Corrected the reason given for the failures of Independence (signature Σ) and Distinctness (signature Σ): the true atom is denoted by no closed pure term, since such terms denote entities fixed by every arrow; the failures come from the other relational constants, which denote top. No verdict changes.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Corrected the justification of □Strong Leibniz Biconditionals (type t): the 22 September argument tacitly used that the monoid is right-cancellative, which holds here; no verdict changes.
- **2026-09-22** (Claude Fable 5.1 (Anthropic)) — Fixed an interpretation of Σ (relational constants as top, individual constants as one fixed individual) and recorded the signature schemata it refutes, at Cian Dorr’s request. Now violates: Witnessed Possibility, Separated Structure, Independence (signature Σ), Distinctness Maximalism (signature Σ).
- **2026-09-22** (Claude Fable 5.1 (Anthropic)) — Added □Strong Leibniz Biconditionals (type t): every singleton of an arrow is a strong world in a propositionally full one-object model; see the notes. Now satisfies: □Strong Leibniz Biconditionals (type t).
- **2026-09-22** (Claude Fable 5.1 (Anthropic)) — Boxed the Relational Choice claim; see the notes. Now satisfies: □Relational Choice.
- **2026-09-20** (Claude Fable 5.1 (Anthropic)) — Added Relational Choice at Cian Dorr's direction. With choice in the metatheory a serial relation has a functional subrelation, and a full model contains every intension, so that subrelation is in the domain; see Classicism, p. 61, on the principles common to full models. The propositions at the evaluation object are the subsets of the two arrows out of it, four in all, and every intension of a full model is present, so the numerals are the finite cardinalities and the fourth holds of the universal property of propositions: the Axiom of Infinity at type t fails, as does the fifth instance of the schema. Now satisfies: Relational Choice. Now violates: Axiom of Infinity (type t), Infinity Schema (type t).
- **2026-09-17** (OpenAI Codex (GPT-6)) — Adopted the source’s relational type system at the user’s request. The cited construction now directly supplies the recorded model; the former type-extension obligation is removed. Now satisfies: □Rigid Comprehension, □Atomicity, □Actuality, □ND, No Pure Contingency. Now violates: Fregean Axiom.

## Sources

- **Classicism** — Andrew Bacon and Cian Dorr, Classicism, draft of 16 May 2023, §3.5, p. 59, second paragraph; p. 61.

<p class='cert'>Record: <code>topics/classicism/models/full-involution-group.yaml</code></p>

## Paper references

- **Proof: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — §3.5, p. 59, second paragraph; p. 61
