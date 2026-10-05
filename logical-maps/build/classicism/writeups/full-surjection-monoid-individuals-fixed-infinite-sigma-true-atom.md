# Full action model: surjections of an infinite set [infinitely many fixed individuals; Σ true atom]

<p class='cert'>Model — Source: Classicism (2024); produced by Andrew Bacon and Cian Dorr; recorded by OpenAI Codex (GPT-6), 17 September 2026.</p>

## Package

- **No Pure Contingency.** Each closed sentence of the pure language, if true, is necessary. This is a sentence schema, not a quantifier over propositions.
- **Rigid Comprehension.** Every relation, including a proposition, is coextensive with a rigid one.
- **Atomicity.** Every non-bottom entity of each relational type has an atom below it.
- **BF.** The Barcan Formula at every type. The predicate formulation closes the formula schema using lambda abstraction.
- **Axiom of Infinity (type t).** There are not finitely many propositions. No finite cardinality holds of the universal property, so the domain of the type cannot be exhausted by finitely many steps from the empty property.
- **Axiom of Infinity (type e).** There are not finitely many individuals. No finite cardinality holds of the universal property, so the domain of the type cannot be exhausted by finitely many steps from the empty property.
- **□Intensional Choice.** Every closed instance of Intensional Choice is necessary. Box the entire object-variable closure; retain the same type range and other schema side conditions.
- **□Relational Choice.** Necessarily, every serial binary relation has a functional subrelation.
- **Relational Choice.** Every serial binary relation has a functional subrelation.
- **Transversal Choice.** Every equivalence relation, at any type including e, has a transversal, that is, a property with exactly one instance in each of its cells.
- **¬ ND (type t).** ND (type t) in the displayed closed propositional formulation.
- **¬ Distinctness-preserving collapse.** Every truth is necessary under the distinctness-preserving modality.
- **¬ B for sentences of Σ.** The B instance for every closed sentence of the language of the fixed signature Sigma.
- **¬ No Contingency (signature Σ).** Each closed sentence of the language of the fixed signature Sigma, if true, is necessary. A sentence schema, standing to No Pure Contingency as Possibility Maximalism (signature Σ) stands to Possibility Maximalism (pure).
- **¬ Witnessed Possibility.** For pure-formulas P with free variables among a finite tuple x, and distinct matching nonlogical constants c, a witness to P entails that P at those constants is possible.
- **¬ Separated Structure.** For each typed nonlogical constant c and closed same-typed terms F,G not containing c, equality after application to c implies equality of F and G.
- **¬ Independence (signature Σ).** No constant of Sigma is a pure operation applied to other constants: for a closed pure term A and distinct constants c, d_1,…,d_n with n ≥ 0, c differs from A applied to the d’s. With n = 0, no constant denotes a pure entity.
- **¬ Distinctness Maximalism (signature Σ).** The Distinctness Maximalism schema for the fixed nonlogical signature Sigma.

## Definition

Use the monoid of surjections of an infinite set, at its sole object.

Individuals, fixed for this record: at every object the individuals are the natural numbers, and every arrow acts on them as the identity.

Interpretation of Σ, fixed for this record: one designated relational constant $c$ of type $\tau=\bar\sigma t$ denotes $\lambda\bar x\, .\,a$, where $a$ is the unique true atom of the model, the actual-world proposition $\{1\}$; every other constant of Σ, of which there is at least one, is relational and denotes the top element of its type.

*A member of the group Full action models, which supplies this definition with the record's settings, and the arguments marked as shared.*

## Arguments

### Holds No Pure Contingency, Rigid Comprehension, Atomicity, BF. Fails ND (type t).

The source cites Bacon 2020, Proposition A.3 for the higher-type surjectivity argument.

*Source: Classicism, §3.5, p. 59, third paragraph. By Andrew Bacon and Cian Dorr, 2026-09-17.*

### Holds Axiom of Infinity (type t).

The arrows are an infinite monoid, identity at the identity arrow is literal, and the numeral sets at type t are intensions of a full model, so no finite cardinality holds of the universal property at type t.

*By Claude Fable 5.1 (Anthropic), at Cian Dorr's direction, 2026-09-20.*

### Fails Distinctness-preserving collapse.

Let $p:=\{\mathrm{id}\}$, true. Any witness $q$ for $\Box_{\ne}p$ is true, so contains the identity, and for a non-identity bijection $i$ the arrow $i^{-1}$ gives $i^{-1}\circ i\in q$, so $\Diamond q$ holds under $i$ while $p$ does not. So no true $q$ has $\Box(\Diamond q\to p)$.

*By Claude Fable 5.1 (Anthropic), 2026-09-23.*

### Holds Axiom of Infinity (type e).

The individuals at the evaluation object are an infinite set and identity there is literal. The numerals at type $e$ are intensions of a full model, so they are the finite cardinalities, and none of them holds of the universal property: no finite cardinality holds of an infinite set. This is the argument the full surjection-monoid record gave for its own infinite individuals.

*General argument `arguments/fixed-infinite-individuals`. It requires that At every object the individuals are the same infinite set, and every arrow acts on them as the identity. Here: This is the choice of individuals. It requires that The model is full: at each object, the domain of each relational type contains every intension of that type. Here: Every intension of every relational type is present at every object (Classicism, §3.5, p. 59). By Claude Opus 5.5 (Anthropic), at Cian Dorr's direction, 2026-10-03.*

### Holds □Intensional Choice.

For each object $U$ and type $\sigma$ fix a well-ordering $<_U$ of the domain $D^\sigma_U$, and let $W$ be the intension of type $\sigma\to\sigma\to t$ with $W(h):={<_{\operatorname{cod}h}}$. Its value depends only on the arrow's codomain, so by the condition it is in the domain, and at every world its extension well-orders that world's type-$\sigma$ domain. Given $F$ with $\Box\exists x\, .\,Fx$, put $G:=\lambda x\, .\,Fx\land\forall y\, .\,(Fy\to\neg Wyx)$, the $W$-least $F$. It is definable from $F$ and $W$, so in the domain; $G\le F$, and its extension at every arrow is the singleton of the least element of $F$'s. So Intensional Choice holds, and the same at every reachable object gives $\Box$Intensional Choice. Cian Dorr's observation that such models are qualitatively full, made precise.

*General argument `arguments/intensional-choice-well-ordering`. It requires that At every object reachable from the evaluation point, the domain contains every intension whose value at an arrow depends only on the arrow's codomain. Here: The domains are full at every object. It requires that The model is constructed in a metatheory with the axiom of choice. Here: The constructions are carried out in ZFC. By Claude Fable 5.1 (Anthropic), at Cian Dorr's suggestion, 2026-10-03.*

### Holds No Pure Contingency.

Closed pure terms denote entities fixed by every arrow (§3.5, p. 58). With a single object, a proposition fixed by every arrow contains every arrow if it contains the identity and no arrow otherwise, so a true closed pure sentence is necessary: the source's one-object No Pure Contingency observation (p. 79), applied to each closed instance.

*Source: Classicism, §3.5, p. 58; p. 79. General argument `arguments/no-pure-contingency-one-object`. It requires that The model is an action model (Classicism, Appendix D), or an intensional action model in the sense of Dorr's draft (Boolean Completeness does not imply Rigid Comprehension), with a single object. Here: It has one object. By Andrew Bacon and Cian Dorr, 2026-09-17.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic, for every one-object action model; the reason the source's observation holds is spelled out in place of "Boxed positive flags use the source’s explicit one-object No Pure Contingency observation, applied separately to each closed instance."

### Holds □Relational Choice.

The truncation of a full action model at any arrow is again a full action model, its domains at the reachable objects being unchanged, and Relational Choice holds in every full model given choice in the metatheory (Classicism, p. 61).

*General argument `arguments/relational-choice-full-boxed`. It requires that The model is a full action model: an action model (Classicism, Appendix D) that is full at every object. Here: An action model, full at every object (Classicism, §3.5, p. 59; Appendix D). It requires that The model is constructed in a metatheory with the axiom of choice. Here: The constructions are carried out in ZFC. By Claude Fable 5.1 (Anthropic), 2026-09-22.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The two-object full action models' copies stated once for the topic, for every full action model.

### Holds Relational Choice.

With choice in the metatheory a serial relation has a functional subrelation, and a full model contains every intension, so that subrelation is in the domain; see Classicism, p. 61, on the principles common to full models.

*General argument `arguments/relational-choice-full`. It requires that The model is full: at each object, the domain of each relational type contains every intension of that type. Here: Every intension of every relational type is present at every object (Classicism, §3.5, p. 59). It requires that The model is constructed in a metatheory with the axiom of choice. Here: The constructions are carried out in ZFC. By Claude Fable 5.1 (Anthropic), at Cian Dorr's direction, 2026-09-20.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The full action models' copies stated once for the topic.

### Fails B for sentences of Σ.

B for sentences of Σ fails: the Σ-sentence $\forall\bar x\, .\,c\bar x$ denotes $a$, which is true, and under an arrow from which no world in $a$ is accessible $\Diamond a$ is false, so $\Box\Diamond a$ fails.

*General argument `arguments/sigma-true-atom-b`. It requires that Σ has a designated relational constant $c$ of type $\tau=\bar\sigma t$ denoting $\lambda\bar x\, .\,a$, where $a$ is the actual-world proposition, the unique true atom; every other constant, of which there is at least one, is relational and denotes the top element of its type. Here: This is the interpretation. It requires that The actual-world proposition $a$, the strongest truth, is in the domain; it is necessary at no world, and some arrow does not fix it. Here: The singleton $a$ of the identity arrow is in the domain, the model being full. It is necessary at no world: a world other than the identity sees itself, which lies outside $a$, and the identity sees an arrow other than itself. And a non-identity arrow $k$ does not fix it, since $1\in k\cdot a$ would need $1\circ k=1$. It requires that Some world sees no world at which the actual-world proposition is true. Here: A surjection that is not injective: no composite with it is the identity. By Claude Fable 5.1 (Anthropic), at Cian Dorr’s request, 2026-09-22.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The B clause of the records' Σ-as-true-atom argument, stated once for the topic.

### Fails No Contingency (signature Σ), Witnessed Possibility, Separated Structure, Independence (signature Σ), Distinctness Maximalism (signature Σ).

No Contingency (signature Σ) fails, since the Σ-sentence $\forall\bar x\, .\,c\bar x$ denotes $a$, true and contingent; Witnessed Possibility fails for the pure formula $x=\top_\tau$, witnessed by $\top_\tau$, since $\Diamond(c=\top_\tau)$ is $\Diamond\Box a$ and $a$ is necessary at no world; Separated Structure fails with it, being equivalent to Possibly Witnessed Possibility; Independence (signature Σ) and Distinctness Maximalism (signature Σ) fail through the other relational constants: such a constant $c'$ of type $\tau'$ denotes what the closed pure term $\top_{\tau'}$ denotes, and $c'=\top_{\tau'}$ is a true identity that C(Σ) does not prove. The designated constant refutes neither: closed pure terms denote entities fixed by every arrow (Classicism, §3.5, p. 58), whereas some arrow does not fix $a$, so no closed pure term denotes $\lambda\bar x\, .\,a$.

*General argument `arguments/sigma-true-atom`. It requires that Σ has a designated relational constant $c$ of type $\tau=\bar\sigma t$ denoting $\lambda\bar x\, .\,a$, where $a$ is the actual-world proposition, the unique true atom; every other constant, of which there is at least one, is relational and denotes the top element of its type. Here: This is the interpretation. It requires that The actual-world proposition $a$, the strongest truth, is in the domain; it is necessary at no world, and some arrow does not fix it. Here: The singleton $a$ of the identity arrow is in the domain, the model being full. It is necessary at no world: a world other than the identity sees itself, which lies outside $a$, and the identity sees an arrow other than itself. And a non-identity arrow $k$ does not fix it, since $1\in k\cdot a$ would need $1\circ k=1$. By Claude Fable 5.1 (Anthropic), at Cian Dorr’s request, 2026-09-22.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The verbatim copies in ten records (finite-support, symmetric and full action models) stated once for the topic. Its B clause is now sigma-true-atom-b, which needs an arrow from which the actual world is out of reach. "$a$ is fixed by no arrow but the identity" became "some arrow does not fix $a$": in a symmetric model the actual-world proposition is the symmetry group, which its members fix, and the conclusion needs only the weaker claim.

### Holds Transversal Choice.

For an equivalence relation at the evaluation point, a transversal of its extension there, chosen in the metatheory, is by extensional fullness the extension of an element of the domain; the equivalence and transversal conditions are unboxed.

*General argument `arguments/transversal-choice-extensionally-full`. It requires that The model is extensionally full at every object: every set of tuples from the domains at an object is the extension, at the identity arrow, of an element of the domain of the matching relational type there. Here: A full model contains every intension, so in particular one with any given extension at the identity. It requires that The model is constructed in a metatheory with the axiom of choice. Here: The constructions are carried out in ZFC. By Cian Dorr (observation); recorded by Claude Fable 5.1 (Anthropic), on a question of Zachary Goodsell, after an observation of Christopher Sun, 2026-09-25.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The Relational Choice and Transversal Choice arguments merged into one, stated for every extensionally full model.

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic. Its first sentence, deriving extensional fullness from ideal fullness, is now the group's reason for meeting extensionally-full.


## Notes

The cited construction is a model of the map’s relational-type framework. The description identifies its evaluation point; construction and verification are given at the PDF locations in References.

The source takes infinitely many individuals with a surjective action, such as the surjections' action on the set by evaluation. That action gives, on the map's principles, what the variant with infinitely many fixed individuals gives: it is surjective and homogeneous, and the failure of ND at type $e$ that its non-injectivity brings adds nothing, ND failing already at type $t$.

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
