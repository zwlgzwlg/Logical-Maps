# Symmetric ideally-full model: arrows omitting or reserving a fixed individual [one individual]

<p class='cert'>Model — Source: BC does not imply RC (draft); produced by Cian Dorr; recorded by Claude Opus 5 (Anthropic), 19 September 2026.</p>

## Package

- **Boolean Completeness.** Every property of entities of a relational type has a greatest lower bound in that type.
- **Atomlessness.** Atomlessness in the displayed closed propositional formulation.
- **Inextensible Comprehension.** Every relation, including a proposition, is coextensive with a inextensible one.
- **No Pure Contingency.** Each closed sentence of the pure language, if true, is necessary. This is a sentence schema, not a quantifier over propositions.
- **No Contingency (signature Σ).** Each closed sentence of the language of the fixed signature Sigma, if true, is necessary. A sentence schema, standing to No Pure Contingency as Possibility Maximalism (signature Σ) stands to Possibility Maximalism (pure).
- **B for sentences of Σ.** The B instance for every closed sentence of the language of the fixed signature Sigma.
- **¬ BF (type t).** BF (type t) in the displayed closed propositional formulation.
- **¬ Axiom of Infinity (type e).** There are not finitely many individuals. No finite cardinality holds of the universal property, so the domain of the type cannot be exhausted by finitely many steps from the empty property.
- **¬ Infinity Schema (type e).** There are arbitrarily many pairwise distinct entities of this fixed type; one sentence for each positive integer n.
- **¬ Possible Infinity (type e).** Possibly there are not finitely many individuals: the Axiom of Infinity at this type, under a diamond.
- **¬ Witnessed Possibility.** For pure-formulas P with free variables among a finite tuple x, and distinct matching nonlogical constants c, a witness to P entails that P at those constants is possible.
- **¬ Separated Structure.** For each typed nonlogical constant c and closed same-typed terms F,G not containing c, equality after application to c implies equality of F and G.
- **¬ Independence (signature Σ).** No constant of Sigma is a pure operation applied to other constants: for a closed pure term A and distinct constants c, d_1,…,d_n with n ≥ 0, c differs from A applied to the d’s. With n = 0, no constant denotes a pure entity.
- **¬ Distinctness Maximalism (signature Σ).** The Distinctness Maximalism schema for the fixed nonlogical signature Sigma.

## Definition

A symmetric ideally-full intensional action model over one object, the set of natural numbers. Its arrows are of two disjoint kinds: the surjections for which the distinguished individual is its own only preimage, and the functions that omit the distinguished individual from their range. Its symmetry group is the permutations fixing that individual, which is now a proper subset of the first kind. An arrow's value at the distinguished individual still tells the two kinds apart, but no finite set separates any arrow. The evaluation point is the identity arrow.

Individuals, fixed for this record: there is a single individual at every object. The arrows still act on the base as the construction says, and the base still supplies the pinning sets and the symmetry groups.

Interpretation of Σ, fixed for this record: every constant of Σ is relational, and each denotes the top element of its type.

*A member of the group Symmetric ideally-full models, which supplies this definition with the record's settings, and the arguments marked as shared.*

## Arguments

### Holds Boolean Completeness.

By the draft's main theorem with the distinguished individual as the distinguished set. Two arrows agreeing there lie in the same one of the two classes, and a prescription taken from the two of them extends within that class, by nonzero values in the second case and by surjective nonzero values in the first.

*By Cian Dorr, 2026-09-19.*

### Holds Atomlessness.

The first class of arrows contains non-injective ones, which restores the arguments used for the all-surjections model: given a true proposition pinned down by a finite set containing the distinguished individual and one other, the proposition that a fresh individual is not collapsed with that set is a strictly stronger truth; and the same splitting applied to an arbitrary nonzero proposition rather than a true one gives Atomlessness.

*By Cian Dorr, 2026-09-19.*

### Holds Inextensible Comprehension.

At every relational type, by an adaptation of the argument recorded for the all-surjections model (symmetric-all-surjections), whose facts (1)–(3) and transversal lemma are used here. Write $0$ for the distinguished individual, $A$ for the first class of arrows (surjections with $0$ as its own only preimage) and $B$ for the second (arrows omitting $0$ from their range). $B$ is absorbing: if $h\in B$ then $i\circ h$ omits $0$, since $i0=0$ only when $i\in A$ and then $i$ sends nothing else to $0$. So the proposition $\alpha:=\{k : k0=0\}$, the class $A$, is true at $1$, pinned down by $\{0\}$, symmetric, and once false stays false.
Given $X$ pinned down by $S_X$, put $S:=S_X\cup\{0\}$ and $Y:=\lambda\bar z\, .\,\alpha\land\delta_S\land X\bar z$, with $\delta_S$ the proposition that no two members of $S$ are collapsed. $Y$ is symmetric, pinned down by $S$ and coextensive with $X$. At a world in $B$, or one collapsing $S$, $Y$ is empty there and at every world it sees. A world $i\in A$ injective on $S$ can be relabelled by a permutation fixing $0$, hence in the symmetry group, so that it fixes $S$ pointwise. For such $i$ the transversal lemma holds: $i$ is surjective, preimages of points outside $S$ lie outside $S$, the permutation $\tau$ of $\mathbb N\setminus S$ fixes $0$ and so lies in the symmetry group, which keeps the extension of $X$ at $1$ closed under $\tau\cdot$, and $i\circ\tau\in A$ fixes the pinning set of $r$. The rest of the argument, including the leading box, goes through verbatim. BF fails here, so the surjectivity used in the lemma is available only at the worlds in $A$; the conjunct $\alpha$ removes the others.

*By Claude Opus 5.5 (Anthropic), at Cian Dorr's request, 2026-09-27.*

### Fails BF (type t).

In a one-object finitely pinned model, BF (type t) fails as soon as there are a finite $N$, an arrow $i$ and a proposition $q$ in the domain that is the transport $i^{\prime}\cdot p=\{k : k\circ i^{\prime}\in p\}$ of no proposition $p$ along any arrow $i^{\prime}$ agreeing with $i$ on $N$: the intension $X:=\{\langle r,j\rangle : r\ne q\text{ or }j\text{ disagrees with }i\text{ on }N\}$, which the condition puts in the domain, contains $\langle i^{\prime}\cdot p,i^{\prime}\rangle$ for every $p$ and $i^{\prime}$, so $\forall p\, .\,\Box Xp$ holds at the identity, and omits $\langle q,i\rangle$, so $\Box\forall p\, .\,Xp$ fails there. Since membership of $k$ in $i^{\prime}\cdot p$ depends only on $k$ restricted to the range of $i^{\prime}$, it suffices that $q$ separate two arrows agreeing on every such range, as the condition provides.

*General argument `arguments/barcan-t-transport`. It requires that The model is a one-object action model whose entities are finitely pinned, and there are a finite set $N$, an arrow $i$ and a proposition $q$ in the domain such that $q$ separates two arrows that agree on the range of every arrow agreeing with $i$ on $N$, and the intension $\{\langle r,j\rangle : r\ne q\text{ or }j\text{ disagrees with }i\text{ on }N\}$ is in the domain. Here: Take $N=\{0\}$, $i$ any arrow with $i0\ne0$, so that every arrow agreeing with it on $N$ omits $0$ from its range, and $q:=\{k : k0=0\}$, the first class of arrows, pinned down by $\{0\}$ and symmetric: an arrow $k$ of the first class and the arrow $k^{\prime}$ agreeing with it off $0$ but sending $0$ elsewhere, which omits $0$ from its range since $0$ is $k$’s only preimage of $0$, are separated by $q$. The intension the argument uses is pinned down by $N$, and symmetric, since $g\cdot q=q$ for $g$ fixing $0$ and $(g\circ j)0=0$ iff $j0=0$, so it lies in the domain. By Claude Fable 5.1 (Anthropic), answering Cian Dorr’s question whether the failure of BF sharpens to type $t$, 2026-09-23.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The finite-support group's argument and the symmetric range-gap models' copies stated once for the topic; that $X$ is in the domain (pinned down by $N$, and in a symmetric model symmetric) is now part of each record's reason for meeting transport-gap.

### Holds No Pure Contingency.

Closed pure terms denote entities fixed by every arrow (§3.5, p. 58). With a single object, a proposition fixed by every arrow contains every arrow if it contains the identity and no arrow otherwise, so a true closed pure sentence is necessary: the source's one-object No Pure Contingency observation (p. 79), applied to each closed instance.

*Source: Classicism, §3.5, p. 58; p. 79. General argument `arguments/no-pure-contingency-one-object`. It requires that The model is an action model (Classicism, Appendix D), or an intensional action model in the sense of Dorr's draft (Boolean Completeness does not imply Rigid Comprehension), with a single object. Here: It has one object (Dorr, draft, §3.1: closed pure terms denote entities fixed by every arrow). By Andrew Bacon and Cian Dorr, 2026-09-17.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic, for every one-object action model; the reason the source's observation holds is spelled out in place of "Boxed positive flags use the source’s explicit one-object No Pure Contingency observation, applied separately to each closed instance."

### Fails Axiom of Infinity (type e), Infinity Schema (type e), Possible Infinity (type e).

No two individuals are distinct, and the numeral $\operatorname{Suc}_e\mathbf{0}_e$ holds of the universal property at type $e$ at every world.

*General argument `arguments/one-individual`. It requires that There is exactly one individual, at every world. Here: There is a single individual at every object. By Claude Opus 5.5 (Anthropic), at Cian Dorr's direction, 2026-10-02.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic.

### Fails Witnessed Possibility, Separated Structure, Independence (signature Σ), Distinctness Maximalism (signature Σ).

Let $c\in\Sigma$ have relational type $\tau$, so $c=\top_\tau$ necessarily. Witnessed Possibility fails for the pure formula $x\ne\top_\tau$, witnessed by $\bot_\tau$ but impossible of $c$; Separated Structure fails since $\lambda x\, .\,x$ and $\lambda x\, .\,\top_\tau$ agree on $c$ and differ; Independence (signature Σ) fails since $c$ denotes what the closed pure term $\top_\tau$ denotes; Distinctness Maximalism (signature Σ) fails since $c=\top_\tau$ is a true identity that C(Σ) does not prove.

*General argument `arguments/sigma-top`. It requires that Every constant of Σ is relational, and each denotes the top element of its type. Here: This is the interpretation. By Claude Fable 5.1 (Anthropic), at Cian Dorr’s request, 2026-09-22.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic; it uses nothing about the model.

### Holds No Contingency (signature Σ), B for sentences of Σ.

Each constant of Σ denotes what the closed pure term $\top_\tau$ of its type denotes, so a closed sentence of the language of Σ denotes what the pure sentence with $\top_\tau$ in place of each constant denotes; if true it is necessary by No Pure Contingency, which holds here. So No Contingency (signature Σ) holds, and B for sentences of Σ with it: a true Σ-sentence is necessary, hence necessarily possible.

*General argument `arguments/sigma-top-npc`. It requires that Every constant of Σ is relational, and each denotes the top element of its type. Here: This is the interpretation. By Cian Dorr (observation); recorded by Claude Opus 5.5 (Anthropic), 2026-10-02.*

*Revised 2026-10-03 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The argument sigma-single-top, for Σ a single constant of type $t$ denoting $\top$, stated for every interpretation of Σ by top elements, now that such interpretations have no individual constants. It replaces that argument and nc-sigma-homogeneous, which reached the same verdicts through an individual constant when the model's automorphisms carry every individual to every other. With an individual constant and no such automorphisms the verdicts were unknown in 19 models, and nowhere did the individual constants settle a verdict differently.


## Notes

The second of the draft's two variants in which BF fails, arranged so that the range deficiency no longer brings Actuality with it. Since Actuality fails, Weak Rigid Comprehension and Rigid Comprehension fail too, which are recorded as derived verdicts. Atomlessness is the Proposition 45 argument for Atomicity read for an arbitrary nonzero proposition, and the failure of ND at type e follows from the non-injective arrows; neither is displayed separately in the draft. The source is a work in progress. Everything that implies these fails with them.

## History

The record's revision log before it was written as arguments.

- **2026-09-27** (Claude Opus 5.5 (Anthropic), at Cian Dorr's request) — Recorded Inextensible Comprehension at every relational type, adapting the all-surjections argument: the witness also conjoins the proposition that the distinguished individual is fixed, which confines it to the surjective arrows. Replaces the note that left it unknown. Now satisfies: Inextensible Comprehension.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Recorded the failure of Relational Choice, at types (e→t) and e: a functional subrelation of the serial relation pairing each property with its members would be symmetric and finitely pinned, and a symmetry fixing its pinning set would carry its choice for the property of lying outside that set to a second choice. Cian Dorr’s observation that a choice cannot be finitely pinned; argument in the notes. Now violates: Relational Choice.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Noted why Inextensible Comprehension is left unknown: its type-t and type-(e→t) instances hold here, so the failure of Actuality does not sharpen to it at those types.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Recorded the failure of BF at type t, sharpening the failure of BF; argument in the notes. Now violates: BF (type t).
- **2026-09-22** (Claude Fable 5.1 (Anthropic)) — Fixed an interpretation of Σ (relational constants as top, individual constants as one fixed individual) and recorded the signature schemata it refutes, at Cian Dorr’s request. Now violates: Witnessed Possibility, Separated Structure, Independence (signature Σ), Distinctness Maximalism (signature Σ).
- **2026-09-20** (Claude Fable 5.1 (Anthropic)) — Added both Axioms of Infinity at Cian Dorr's direction. The individuals are the natural numbers and identity at the identity arrow is literal, so no numeral counts them. The propositions that a given individual is fixed by the arrow, one for each individual, are pairwise distinct, symmetric and pinned by that individual, so there are infinitely many propositions. The set of numerals at each type is invariant under every arrow, hence symmetric and pinned by the empty set, so finite cardinality is standard and no finite cardinality holds of the universal property at either type. Now satisfies: Axiom of Infinity (type e), Axiom of Infinity (type t).

## Sources

- **BC does not imply RC** — Cian Dorr, Boolean Completeness does not imply Rigid Comprehension, draft of 30 July 2026, §7.2, p. 22; Proposition 45, p. 22; Remark 38, p. 19.

<p class='cert'>Record: <code>topics/classicism/models/symmetric-range-gap-without-actuality.yaml</code></p>

## Paper references

- **Proof: Boolean Completeness does not imply Rigid Comprehension.** Dorr, Cian. Boolean Completeness does not imply Rigid Comprehension. Unpublished draft in progress, 30 July 2026, 27 pages. All page, proposition and lemma locators for this source refer to that draft. Parts of the draft were drafted with AI assistance; its mathematical claims are attributed to the author. — §7.2, p. 22; Proposition 45, p. 22; Remark 38, p. 19
