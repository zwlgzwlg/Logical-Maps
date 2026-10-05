# Full action model: two-object chain

<p class='cert'>Model — Source: Classicism (2024); produced by Andrew Bacon and Cian Dorr; recorded by OpenAI Codex (GPT-6), 17 September 2026.</p>

## Package

- **□Rigid Comprehension.** Necessarily, every relation, including a proposition, is coextensive with a rigid one.
- **□Atomicity.** Necessarily, every non-bottom entity of each relational type has an atom below it.
- **□Strong Leibniz Biconditionals.** Necessarily, at each relational type, every possible entity (one distinct from bottom) is entailed by a strong world: a possible entity that necessarily entails every entity of the type or its negation.
- **□BF.** Necessarily, the Barcan Formula holds at every type. The predicate formulation closes the formula schema using lambda abstraction.
- **Distinctness-preserving collapse.** Every truth is necessary under the distinctness-preserving modality.
- **□Intensional Choice.** Every closed instance of Intensional Choice is necessary. Box the entire object-variable closure; retain the same type range and other schema side conditions.
- **□Relational Choice.** Necessarily, every serial binary relation has a functional subrelation.
- **Relational Choice.** Every serial binary relation has a functional subrelation.
- **Countable Boolean Completeness.** Every countable property of entities of a relational type has a least upper bound in that type, where a property is countable when it injects into the natural numbers.
- **Transversal Choice.** Every equivalence relation, at any type including e, has a transversal, that is, a property with exactly one instance in each of its cells.
- **¬ No Pure Contingency.** Each closed sentence of the pure language, if true, is necessary. This is a sentence schema, not a quantifier over propositions.
- **¬ B for pure sentences.** The B instance for every closed sentence in the pure language.
- **¬ Infinity Schema (type t).** There are arbitrarily many pairwise distinct entities of this fixed type; one sentence for each positive integer n.
- **¬ Axiom of Infinity (type e).** There are not finitely many individuals. No finite cardinality holds of the universal property, so the domain of the type cannot be exhausted by finitely many steps from the empty property.
- **¬ Infinity Schema (type e).** There are arbitrarily many pairwise distinct entities of this fixed type; one sentence for each positive integer n.
- **¬ Possible Infinity (type e).** Possibly there are not finitely many individuals: the Axiom of Infinity at this type, under a diamond.
- **¬ Witnessed Possibility.** For pure-formulas P with free variables among a finite tuple x, and distinct matching nonlogical constants c, a witness to P entails that P at those constants is possible.
- **¬ Separated Structure.** For each typed nonlogical constant c and closed same-typed terms F,G not containing c, equality after application to c implies equality of F and G.
- **¬ Independence (signature Σ).** No constant of Sigma is a pure operation applied to other constants: for a closed pure term A and distinct constants c, d_1,…,d_n with n ≥ 0, c differs from A applied to the d’s. With n = 0, no constant denotes a pure entity.
- **¬ Distinctness Maximalism (signature Σ).** The Distinctness Maximalism schema for the fixed nonlogical signature Sigma.

## Definition

Use two objects with one nonidentity arrow from W0 to W1, evaluated at W0.

Individuals, fixed for this record: there is a single individual at every object, and every arrow sends it to the single individual at its target.

Interpretation of Σ, fixed for this record: every constant of Σ is relational, and each denotes the top element of its type.

*A member of the group Full action models, which supplies this definition with the record's settings, and the arguments marked as shared.*

## Arguments

### Holds □Rigid Comprehension, □Atomicity.

*Source: Classicism, §3.5, p. 59, fourth paragraph. By Andrew Bacon and Cian Dorr, 2026-09-17.*

### Fails No Pure Contingency.

The source makes the Fregean Axiom false at W0 and true at W1.

*Source: Classicism, §3.5, p. 59, fourth paragraph. By Andrew Bacon and Cian Dorr, 2026-09-17.*

### Holds □Strong Leibniz Biconditionals.

An atom of type $\bar\sigma t$ at $W_0$ is a single pair $\{\langle\bar a,h\rangle\}$, and its transport along $k$ is $\{\langle\bar a,j\rangle : j\circ k=h\}$ with $j$ ranging over the arrows out of $W_1$, of which there is one; so the transport is empty or a single pair, and decides every relation of $W_1$’s full domain. Every possible relation contains a pair, so every possible relation has a strong world below it, at $W_0$ and trivially at the one-world $W_1$.

*By Claude Fable 5.1 (Anthropic), 2026-09-23.*

### Holds □BF.

The arrows out of $W_0$ are the identity and $k$. A relation at $W_0$ of relational type $\bar\sigma t$ is a set of pairs $\langle i,\bar a\rangle$ with $\bar a$ a tuple at $i$'s target, and $k$ carries it to the relation at $W_1$ whose extension at the identity of $W_1$ is its extension at $k$, the only arrow into $W_1$'s identity being composed with $k$. In a full model that extension at $k$ is any set of tuples at $W_1$, so $k$ acts surjectively at every relational type; at type $e$ it does under either choice of individuals, sending the one individual to the one individual, or each natural number to itself. So BF holds at $W_0$ by Classicism, Proposition 3.24(ii), and it holds at $W_1$, whose only arrow is the identity, so $\Box$BF holds.

*By Claude Opus 5.5 (Anthropic), at Cian Dorr's direction, 2026-10-03.*

### Fails B for pure sentences.

The pure sentence that there are three pairwise distinct propositions is true at $W_0$ and false at $W_1$, from which no arrow returns.

*By Claude Fable 5.1 (Anthropic), 2026-09-25.*

### Holds Distinctness-preserving collapse.

For a true $p$, $a\le p$, since $a$ entails every truth. Take $q:=a$ in the definition of $\Box_{\ne}p$: at a world in $a$, $p$ holds; at a world outside $a$, $\Diamond a$ fails. So every truth is $\Box_{\ne}$-necessary.

*General argument `arguments/dpc-isolated-actual-world`. It requires that The actual-world proposition $a$ is in the domain and entails every truth, and no world outside $a$ sees a world in $a$. Here: The actual-world proposition, the singleton of the identity, is in the domain, the model being full; no arrow leads back from $W_1$ to $W_0$. By Claude Fable 5.1 (Anthropic), 2026-09-23.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The finite-support, symmetric and full action models' copies (eight records) stated once for the topic; what varied, why no world outside the actual world sees back into it, is each record's reason for meeting actual-world-isolated.

### Fails Infinity Schema (type t).

The propositions at the evaluation world are finitely many, and every intension of a full model is present, so the numerals are the finite cardinalities and one of them holds of the universal property of propositions: the Axiom of Infinity at type t fails, as does an instance of the schema.

*General argument `arguments/finitely-many-propositions`. It requires that The model is full: at each object, the domain of each relational type contains every intension of that type. Here: Every intension of every relational type is present at every object (Classicism, §3.5, p. 59). It requires that There are finitely many propositions at the evaluation world. Here: The propositions at the evaluation object are the subsets of the two arrows out of it, four in all. By Claude Fable 5.1 (Anthropic), at Cian Dorr's direction, 2026-09-20.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The copies in three full action models (each with four propositions) stated once for the topic; each record's count is its reason for meeting finitely-many-propositions.

### Holds □Intensional Choice.

For each object $U$ and type $\sigma$ fix a well-ordering $<_U$ of the domain $D^\sigma_U$, and let $W$ be the intension of type $\sigma\to\sigma\to t$ with $W(h):={<_{\operatorname{cod}h}}$. Its value depends only on the arrow's codomain, so by the condition it is in the domain, and at every world its extension well-orders that world's type-$\sigma$ domain. Given $F$ with $\Box\exists x\, .\,Fx$, put $G:=\lambda x\, .\,Fx\land\forall y\, .\,(Fy\to\neg Wyx)$, the $W$-least $F$. It is definable from $F$ and $W$, so in the domain; $G\le F$, and its extension at every arrow is the singleton of the least element of $F$'s. So Intensional Choice holds, and the same at every reachable object gives $\Box$Intensional Choice. Cian Dorr's observation that such models are qualitatively full, made precise.

*General argument `arguments/intensional-choice-well-ordering`. It requires that At every object reachable from the evaluation point, the domain contains every intension whose value at an arrow depends only on the arrow's codomain. Here: The domains are full at every object. It requires that The model is constructed in a metatheory with the axiom of choice. Here: The constructions are carried out in ZFC. By Claude Fable 5.1 (Anthropic), at Cian Dorr's suggestion, 2026-10-03.*

### Fails Axiom of Infinity (type e), Infinity Schema (type e), Possible Infinity (type e).

No two individuals are distinct, and the numeral $\operatorname{Suc}_e\mathbf{0}_e$ holds of the universal property at type $e$ at every world.

*General argument `arguments/one-individual`. It requires that There is exactly one individual, at every world. Here: There is a single individual at every object. By Claude Opus 5.5 (Anthropic), at Cian Dorr's direction, 2026-10-02.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic.

### Holds □Relational Choice.

The truncation of a full action model at any arrow is again a full action model, its domains at the reachable objects being unchanged, and Relational Choice holds in every full model given choice in the metatheory (Classicism, p. 61).

*General argument `arguments/relational-choice-full-boxed`. It requires that The model is a full action model: an action model (Classicism, Appendix D) that is full at every object. Here: An action model, full at every object (Classicism, §3.5, p. 59; Appendix D). It requires that The model is constructed in a metatheory with the axiom of choice. Here: The constructions are carried out in ZFC. By Claude Fable 5.1 (Anthropic), 2026-09-22.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The two-object full action models' copies stated once for the topic, for every full action model.

### Holds Relational Choice.

With choice in the metatheory a serial relation has a functional subrelation, and a full model contains every intension, so that subrelation is in the domain; see Classicism, p. 61, on the principles common to full models.

*General argument `arguments/relational-choice-full`. It requires that The model is full: at each object, the domain of each relational type contains every intension of that type. Here: Every intension of every relational type is present at every object (Classicism, §3.5, p. 59). It requires that The model is constructed in a metatheory with the axiom of choice. Here: The constructions are carried out in ZFC. By Claude Fable 5.1 (Anthropic), at Cian Dorr's direction, 2026-09-20.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The full action models' copies stated once for the topic.

### Fails Witnessed Possibility, Separated Structure, Independence (signature Σ), Distinctness Maximalism (signature Σ).

Let $c\in\Sigma$ have relational type $\tau$, so $c=\top_\tau$ necessarily. Witnessed Possibility fails for the pure formula $x\ne\top_\tau$, witnessed by $\bot_\tau$ but impossible of $c$; Separated Structure fails since $\lambda x\, .\,x$ and $\lambda x\, .\,\top_\tau$ agree on $c$ and differ; Independence (signature Σ) fails since $c$ denotes what the closed pure term $\top_\tau$ denotes; Distinctness Maximalism (signature Σ) fails since $c=\top_\tau$ is a true identity that C(Σ) does not prove.

*General argument `arguments/sigma-top`. It requires that Every constant of Σ is relational, and each denotes the top element of its type. Here: This is the interpretation. By Claude Fable 5.1 (Anthropic), at Cian Dorr’s request, 2026-09-22.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic; it uses nothing about the model.

### Holds Countable Boolean Completeness.

The natural numbers are the finite cardinalities at type $e$ (Background, after Goodsell), and with a single individual there are three: $\mathbf{0}_e$, true of the empty property; $\operatorname{Suc}_e\mathbf{0}_e$, true of the universal one; and the empty cardinality, which is $\operatorname{Suc}_e$ of the second and of itself. By extensional fullness the property of being one of these three is in the domain, so it bounds natural numberhood. A countable property therefore has at most three members in its extension, and their join is its least upper bound.

*General argument `arguments/three-numbers`. It requires that There is exactly one individual, at every world. Here: There is a single individual at every object. It requires that The model is extensionally full at every object: every set of tuples from the domains at an object is the extension, at the identity arrow, of an element of the domain of the matching relational type there. Here: A full model contains every intension, so in particular one with any given extension at the identity. By Claude Opus 5.5 (Anthropic), on Cian Dorr's question whether the failure of Boolean Completeness at type $t$ refutes its countable form here, 2026-10-02.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic.

### Holds Transversal Choice.

For an equivalence relation at the evaluation point, a transversal of its extension there, chosen in the metatheory, is by extensional fullness the extension of an element of the domain; the equivalence and transversal conditions are unboxed.

*General argument `arguments/transversal-choice-extensionally-full`. It requires that The model is extensionally full at every object: every set of tuples from the domains at an object is the extension, at the identity arrow, of an element of the domain of the matching relational type there. Here: A full model contains every intension, so in particular one with any given extension at the identity. It requires that The model is constructed in a metatheory with the axiom of choice. Here: The constructions are carried out in ZFC. By Cian Dorr (observation); recorded by Claude Fable 5.1 (Anthropic), on a question of Zachary Goodsell, after an observation of Christopher Sun, 2026-09-25.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The Relational Choice and Transversal Choice arguments merged into one, stated for every extensionally full model.

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic. Its first sentence, deriving extensional fullness from ideal fullness, is now the group's reason for meeting extensionally-full.


## Notes

The cited construction is a model of the map’s relational-type framework. The description identifies its evaluation point; construction and verification are given at the PDF locations in References. Everything that implies these fails with them.

## History

The record's revision log before it was written as arguments.

- **2026-09-25** (Claude Fable 5.1 (Anthropic)) — Added Transversal Choice, by the argument recorded for Relational Choice: a full model contains every intension, in particular one whose extension at the evaluation point is a transversal, chosen in the metatheory, of the extension there of an equivalence relation; the equivalence and transversal conditions are unboxed. Recorded on a question of Zachary Goodsell, after an observation of Christopher Sun. Now satisfies: Transversal Choice.
- **2026-09-25** (Claude Fable 5.1 (Anthropic)) — Added BF (type t) and □BF (type t), and the failure of Possible Infinity (type t) and of B for pure sentences; see the notes. Now satisfies: BF (type t), □BF (type t). Now violates: Possible Infinity (type t), B for pure sentences.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Recorded the Distinctness-preserving collapse; see the notes. Now satisfies: Distinctness-preserving collapse.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Extended the Strong Leibniz Biconditionals from type t to every relational type, with the necessitation: transports of atoms along the unique arrow out of W1 are atoms or empty. Now satisfies: Strong Leibniz Biconditionals, □Strong Leibniz Biconditionals.
- **2026-09-22** (Claude Fable 5.1 (Anthropic)) — Fixed an interpretation of Σ (relational constants as top, individual constants as one fixed individual) and recorded the signature schemata it refutes, at Cian Dorr’s request. Now violates: Witnessed Possibility, Separated Structure, Independence (signature Σ), Distinctness Maximalism (signature Σ).
- **2026-09-22** (Claude Fable 5.1 (Anthropic)) — Added □Strong Leibniz Biconditionals (type t); see the notes. Now satisfies: □Strong Leibniz Biconditionals (type t).
- **2026-09-22** (Claude Fable 5.1 (Anthropic)) — Boxed the Relational Choice claim; see the notes. Now satisfies: □Relational Choice.
- **2026-09-20** (Claude Fable 5.1 (Anthropic)) — Added Relational Choice at Cian Dorr's direction. With choice in the metatheory a serial relation has a functional subrelation, and a full model contains every intension, so that subrelation is in the domain; see Classicism, p. 61, on the principles common to full models. The propositions at the evaluation object are the subsets of the two arrows out of it, four in all, and every intension of a full model is present, so the numerals are the finite cardinalities and the fourth holds of the universal property of propositions: the Axiom of Infinity at type t fails, as does the fifth instance of the schema. Now satisfies: Relational Choice. Now violates: Axiom of Infinity (type t), Infinity Schema (type t).
- **2026-09-17** (OpenAI Codex (GPT-6)) — Adopted the source’s relational type system at the user’s request. The cited construction now directly supplies the recorded model; the former type-extension obligation is removed. Now satisfies: □Rigid Comprehension, □Atomicity, □Actuality. Now violates: Fregean Axiom, No Pure Contingency.

## Sources

- **Classicism** — Andrew Bacon and Cian Dorr, Classicism, draft of 16 May 2023, §3.5, p. 59, fourth paragraph; p. 61.

<p class='cert'>Record: <code>topics/classicism/models/full-two-object-chain.yaml</code></p>

## Paper references

- **Proof: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — §3.5, p. 59, fourth paragraph; p. 61
