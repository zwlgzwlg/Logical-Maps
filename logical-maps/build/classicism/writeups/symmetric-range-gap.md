# Symmetric ideally-full model: arrows omitting a fixed individual

<p class='cert'>Model — Source: BC does not imply RC (draft); produced by Cian Dorr; recorded by Claude Opus 5 (Anthropic), 19 September 2026.</p>

## Package

- **Boolean Completeness.** Every property of entities of a relational type has a greatest lower bound in that type.
- **Axiom of Infinity (type e).** There are not finitely many individuals. No finite cardinality holds of the universal property, so the domain of the type cannot be exhausted by finitely many steps from the empty property.
- **Axiom of Infinity (type t).** There are not finitely many propositions. No finite cardinality holds of the universal property, so the domain of the type cannot be exhausted by finitely many steps from the empty property.
- **Actuality.** There is a true proposition that entails every true proposition.
- **Distinctness-preserving collapse.** Every truth is necessary under the distinctness-preserving modality.
- **No Pure Contingency.** Each closed sentence of the pure language, if true, is necessary. This is a sentence schema, not a quantifier over propositions.
- **No Contingency (signature Σ).** Each closed sentence of the language of the fixed signature Sigma, if true, is necessary. A sentence schema, standing to No Pure Contingency as Possibility Maximalism (signature Σ) stands to Possibility Maximalism (pure).
- **B for sentences of Σ.** The B instance for every closed sentence of the language of the fixed signature Sigma.
- **¬ Atomicity (type t).** Atomicity (type t) in the displayed closed propositional formulation.
- **¬ Relational Choice.** Every serial binary relation has a functional subrelation.
- **¬ BF.** The Barcan Formula at every type. The predicate formulation closes the formula schema using lambda abstraction.
- **¬ BF (type t).** BF (type t) in the displayed closed propositional formulation.
- **¬ Intensional Choice.** If a property is necessarily instantiated, then some property entailing it is necessarily uniquely instantiated.
- **¬ Witnessed Possibility.** For pure-formulas P with free variables among a finite tuple x, and distinct matching nonlogical constants c, a witness to P entails that P at those constants is possible.
- **¬ Separated Structure.** For each typed nonlogical constant c and closed same-typed terms F,G not containing c, equality after application to c implies equality of F and G.
- **¬ Independence (signature Σ).** No constant of Sigma is a pure operation applied to other constants: for a closed pure term A and distinct constants c, d_1,…,d_n with n ≥ 0, c differs from A applied to the d’s. With n = 0, no constant denotes a pure entity.
- **¬ Distinctness Maximalism (signature Σ).** The Distinctness Maximalism schema for the fixed nonlogical signature Sigma.

## Definition

A symmetric ideally-full intensional action model over one object, the set of natural numbers. Its symmetry group is the permutations fixing a distinguished individual, and its arrows are those permutations together with all the functions that omit the distinguished individual from their range. The evaluation point is the identity arrow.

Individuals, fixed for this record: the individuals at each object are the base the construction describes, and the arrows act on them as on the base.

Interpretation of Σ, fixed for this record: every constant of Σ is relational, and each denotes the top element of its type.

*A member of the group Symmetric ideally-full models, which supplies this definition with the record's settings, and the arguments marked as shared.*

## Arguments

### Holds Boolean Completeness.

By the draft's main theorem with the distinguished individual as the distinguished set. Moving points off a finite set can be done by a permutation fixing that individual, and two arrows agreeing there are either both permutations or both range-deficient, so a prescription taken from the two of them extends by nonzero values to an arrow of the same kind.

*By Cian Dorr, 2026-09-19.*

### Fails Atomicity (type t).

The symmetry group is an atom, but no atom lies inside the nonempty proposition $T$ of arrows omitting $0$ from their range, which is symmetric and pinned down by $\{0\}$: a nonempty symmetric $p\subseteq T$ pinned down by $N\ni0$ and containing $h$ contains every arrow in $T$ whose restriction to $N$ has the same fibres as $h$’s, and those whose restriction to $N\cup\{m\}$ has the same fibres as $h$’s form a smaller nonempty symmetric proposition pinned down by $N\cup\{m\}$, since $h$’s value at a fresh $m$ can be made to coincide with, or to differ from, a value on $N$.

*By Claude Fable 5.1 (Anthropic), 2026-09-23.*

### Fails Relational Choice.

At the types $(e\to t)$ and $e$. Let $U:=\lambda Xy\, .\,Xy\lor\neg\exists z\, .\,Xz$, a closed term, hence in the domain, and serial. A functional subrelation $S$ of $U$ would lie in the domain at the evaluation object, so it is symmetric and pinned down by a finite set $N$. Two facts about such an $S$ (Dorr, draft, Lemma 19(iv)): every $g\in G$ fixing $N$ pointwise satisfies $g^{[\sigma]}S=S$, and symmetry gives $\langle gA,gy,g\rangle\in S$ whenever $\langle A,y,1\rangle\in S$; together, $\langle gA,gy,1\rangle\in S$. Now let $A$ be the property the condition gives for $N$. Its extension is nonempty, so $S$ relates $A$ at the identity to some $y$ in its extension. The condition gives a member $g$ of the symmetry group that fixes $N$ pointwise, fixes $A$ and moves $y$ to some $gy\ne y$, so $S$ relates $A$ to $gy$ as well, and $S$ is not functional at the identity arrow. The well-ordering of the individuals that Cian Dorr had in mind is refuted by the same two facts, but the direct route needs no derivation of a well-ordering from Relational Choice in C.

*From the group *Symmetric ideally-full models*, shared argument `symmetric-ideally-full#relational-choice`. It requires that For each finite set $N$ of individuals at the evaluation object, some property $A$ in the domain has a nonempty extension there, and each individual $y$ in that extension is moved by a member of the symmetry group that fixes $N$ pointwise and fixes $A$. Here: $M=\{0\}$, the distinguished individual, and for $N$ the property of not belonging to $N\cup\{0\}$: the transposition of $y$ with another individual outside $N\cup\{0\}$ fixes $0$, so lies in the symmetry group. By Claude Fable 5.1 (Anthropic), after Cian Dorr’s observation that a choice over the individuals cannot be finitely pinned down, 2026-09-23.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The members' seven copies, which differed in the property $A$ and the transposition, stated once; each member's $A$ and transposition moved to the condition transposable. The qualitative-contrast model's second argument (OpenAI Codex, 24 September) was dropped.

*Revised 2026-10-06 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The condition transposable no longer mentions the finite set $M$ or the pinning of $A$ by $N\cup M$: the argument uses only that $g$ fixes $N$, the set pinning down $S$, and that $A$ is in the domain. So $g$ is now said to fix $N$ pointwise. Proved in Lean.

### Holds Axiom of Infinity (type e).

There are infinitely many individuals, and identity at the identity arrow is literal, so no numeral counts them. The set of numerals at type $e$ is fixed by every arrow, hence symmetric and pinned down by the empty set, so finite cardinality is standard and no finite cardinality holds of the universal property.

*From the group *Symmetric ideally-full models*, shared argument `symmetric-ideally-full#axiom-of-infinity-e`. It requires that There are infinitely many individuals at the evaluation world. Here: The base is infinite. By Claude Fable 5.1 (Anthropic), at Cian Dorr's direction, 2026-09-20.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The type-$e$ half of the members' argument, stated once; "the individuals are the natural numbers" became "there are infinitely many individuals", which also covers the qualitative links model. The type-$t$ half is axiom-of-infinity-t.

### Holds Axiom of Infinity (type t).

The propositions $C_{n,m}:=\{h : hn=hm\}$, that an arrow collapses $n$ and $m$, are symmetric, since relabelling the individuals of a world by a member of the symmetry group keeps identities among them, and each is pinned down by $\{n,m\}$; by the condition infinitely many of them are pairwise distinct, so there are infinitely many propositions. The set of numerals at type $t$ is fixed by every arrow, hence symmetric and pinned down by the empty set, so finite cardinality is standard and no finite cardinality holds of the universal property.

*From the group *Symmetric ideally-full models*, shared argument `symmetric-ideally-full#axiom-of-infinity-t`. It requires that There are infinitely many pairs of individuals such that, for any two of these pairs, some arrow collapses the one and not the other. Here: The pairs $\{n,m\}$ of positive numbers: a function omitting $0$ from its range that collapses $n$ with $m$ and nothing else is an arrow. By Claude Opus 5.5 (Anthropic), at Cian Dorr's direction, 2026-10-02.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Replaces the members' argument of 20 September (Claude Fable 5.1), which used the propositions $\{h : hn=n\}$ that an arrow fixes a given individual. Those are not symmetric when the symmetry group moves $n$: symmetry asks that $h\in p$ imply $g\circ h\in p$, and $(g\circ h)n=gn$.

### Holds Actuality.

The symmetry group is the smallest symmetric set of arrows containing the identity, and by the condition it is pinned down by a finite set, so it is a proposition in the domain, and an atom entailing every truth.

*Source: Boolean Completeness does not imply Rigid Comprehension, Proposition 24, p. 13; §7.1, p. 21; §8, pp. 23–26. From the group *Symmetric ideally-full models*, shared argument `symmetric-ideally-full#actuality`. It requires that The symmetry group, the smallest symmetric set of arrows containing the identity, is pinned down by a finite set. Here: The two classes of arrows are told apart by an arrow's value at the distinguished individual. By Cian Dorr, 2026-09-19.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The three members' versions stated once; what pins the group down is each member's reason for meeting symmetry-group-pinned.

### Fails BF.

At type e. Take the property of being positive unless things are as they actually are, which is pinned down by the distinguished individual and is symmetric. Every individual necessarily has it, since an arrow either fixes the distinguished individual or omits it from its range and so sends everything to something positive; but it is not necessary that everything has it, since any arrow moving the distinguished individual leaves it out.

*Source: Boolean Completeness does not imply Rigid Comprehension, §7.1, p. 21; §7.2, p. 22. From the group *Symmetric ideally-full models*, shared argument `symmetric-ideally-full#barcan-fixes-or-omits`. It requires that There is a distinguished individual that every arrow either fixes or omits from its range, and some arrow moves it. Here: The arrows are the permutations fixing $0$ and the functions omitting $0$ from their range. By Cian Dorr, 2026-09-19.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The range-gap model's argument, which its variant without Actuality invoked ("by the argument of the previous variant, which goes through verbatim"), stated once.

### Fails BF (type t).

In a one-object finitely pinned model, BF (type t) fails as soon as there are a finite $N$, an arrow $i$ and a proposition $q$ in the domain that is the transport $i^{\prime}\cdot p=\{k : k\circ i^{\prime}\in p\}$ of no proposition $p$ along any arrow $i^{\prime}$ agreeing with $i$ on $N$: the intension $X:=\{\langle r,j\rangle : r\ne q\text{ or }j\text{ disagrees with }i\text{ on }N\}$, which the condition puts in the domain, contains $\langle i^{\prime}\cdot p,i^{\prime}\rangle$ for every $p$ and $i^{\prime}$, so $\forall p\, .\,\Box Xp$ holds at the identity, and omits $\langle q,i\rangle$, so $\Box\forall p\, .\,Xp$ fails there. Since membership of $k$ in $i^{\prime}\cdot p$ depends only on $k$ restricted to the range of $i^{\prime}$, it suffices that $q$ separate two arrows agreeing on every such range, as the condition provides.

*General argument `arguments/barcan-t-transport`. It requires that The model is a one-object action model whose entities are finitely pinned, and there are a finite set $N$, an arrow $i$ and a proposition $q$ in the domain such that $q$ separates two arrows that agree on the range of every arrow agreeing with $i$ on $N$, and the intension $\{\langle r,j\rangle : r\ne q\text{ or }j\text{ disagrees with }i\text{ on }N\}$ is in the domain. Here: Take $N=\{0\}$, $i$ any arrow with $i0\ne0$, so that every arrow agreeing with it on $N$ omits $0$ from its range, and $q:=\{k : k0=0\}$, the symmetry group, pinned down by $\{0\}$ and symmetric: a permutation $k$ fixing $0$ and the arrow $k^{\prime}$ agreeing with it off $0$ but sending $0$ elsewhere, which omits $0$ from its range, are separated by $q$. The intension the argument uses is pinned down by $N$, and symmetric, since $g\cdot q=q$ for $g$ fixing $0$ and $(g\circ j)0=0$ iff $j0=0$, so it lies in the domain. By Claude Fable 5.1 (Anthropic), answering Cian Dorr’s question whether the failure of BF sharpens to type $t$, 2026-09-23.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The finite-support group's argument and the symmetric range-gap models' copies stated once for the topic; that $X$ is in the domain (pinned down by $N$, and in a symmetric model symmetric) is now part of each record's reason for meeting transport-gap.

### Holds Distinctness-preserving collapse.

For a true $p$, $a\le p$, since $a$ entails every truth. Take $q:=a$ in the definition of $\Box_{\ne}p$: at a world in $a$, $p$ holds; at a world outside $a$, $\Diamond a$ fails. So every truth is $\Box_{\ne}$-necessary.

*General argument `arguments/dpc-isolated-actual-world`. It requires that The actual-world proposition $a$ is in the domain and entails every truth, and no world outside $a$ sees a world in $a$. Here: The actual-world proposition is the set of arrows that are permutations, pinned down by $\{0\}$; no composite with an arrow omitting $0$ from its range is a permutation, since the other arrows fix $0$ and so cannot restore it to the range. By Claude Fable 5.1 (Anthropic), 2026-09-23.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The finite-support, symmetric and full action models' copies (eight records) stated once for the topic; what varied, why no world outside the actual world sees back into it, is each record's reason for meeting actual-world-isolated.

### Fails Intensional Choice.

At type $e$. Let $F$ and $a$ be as the condition gives them, and suppose $G\le F$ is necessarily uniquely instantiated. $G$ is in the domain, so it is symmetric and pinned down by a finite set, which we may take to contain $a$; call it $N$. Let $h$ be the arrow the condition gives for $N$. Then $G_h=\{y\}$ for some $y$ in $F_h$. If $\sigma$ in the symmetry group fixes $p$, then $\sigma\circ h$ agrees with $h$ on $N$, so $G_{\sigma\circ h}=G_h$ by pinning, while symmetry gives $G_{\sigma\circ h}=\{\sigma y\}$. So no symmetry fixing $p$ moves $y$, and by the condition $y=p$. Each model's witness takes $F$ with $p$ outside its extension at $h$, a contradiction. $\Box$Intensional Choice fails with it, by T.

*General argument `arguments/intensional-choice-collapse`. It requires that A group $G$ acts on the individuals at the evaluation object, and every element of a relational domain there is symmetric, meaning that $\langle\bar x,h\rangle\in D$ implies $\langle g\cdot\bar x,g\circ h\rangle\in D$ whenever $g\in G$ and $g\circ h$ is an arrow, and is pinned down by a finite set of individuals, its extension at an arrow depending only on the arrow's values there. Here: The relational domains hold exactly the symmetric intensions pinned down by a finite set (Dorr, draft, Definitions 15–18). It requires that The individuals at the evaluation object are those the construction acts on, and the arrows act on them as the construction says. Here: The individuals are the base, acted on as the construction says. It requires that There are an individual $a$ and a necessarily instantiated property $F$ in the domain such that, for every finite set $N$ of individuals at the evaluation object, some arrow $h$ sends $N\cup\{a\}$ to a single individual $p$, and every individual $y\ne p$ in $F$'s extension at $h$ is moved by a member $\sigma$ of the symmetry group that fixes $p$, with $\sigma\circ h$ again an arrow. Here: The distinguished individual $d$ is fixed by every symmetry, so take $F:=\lambda x\, .\,x\ne a\land\neg Ex$, where $E$ is the constant intension $\{d\}$, pinned down by $\varnothing$. Let $h$ be a range-deficient function constant with value $p\ne d$ on $N\cup\{a\}$. Then $F_h$ omits $p$ and $d$, and permutations fixing $p$ and $d$ move every other point. By Claude Opus 5.5 (Anthropic), 2026-10-03.*

*Revised 2026-10-03 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Recorded from the collapse lemma deferred in extraction.md on 3 October until the model records' new format landed (not yet checked by a human). It needs the individuals the construction gives. Not covered: the qualitative-links model, whose arrows preserve a ternary relation and so cannot send everything to one point, and the qualitative-contrast model, whose arrows are bijections and where Intensional Choice holds.

*Revised 2026-10-04 by Claude Fable 5.1 (Anthropic), at Cian Dorr's direction:* Moved from the group symmetric-ideally-full to the topic, so that the symmetry-constrained full models use it too: in those models every intension is pinned down by the finite set of all individuals, and the collapses are the constant maps. The group's `when: individuals: base` is now the condition construction-individuals, met by that parameter value.

### Holds No Pure Contingency.

Closed pure terms denote entities fixed by every arrow (§3.5, p. 58). With a single object, a proposition fixed by every arrow contains every arrow if it contains the identity and no arrow otherwise, so a true closed pure sentence is necessary: the source's one-object No Pure Contingency observation (p. 79), applied to each closed instance.

*Source: Classicism, §3.5, p. 58; p. 79. General argument `arguments/no-pure-contingency-one-object`. It requires that The model is an action model (Classicism, Appendix D), or an intensional action model in the sense of Dorr's draft (Boolean Completeness does not imply Rigid Comprehension), with a single object. Here: It has one object (Dorr, draft, §3.1: closed pure terms denote entities fixed by every arrow). By Andrew Bacon and Cian Dorr, 2026-09-17.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic, for every one-object action model; the reason the source's observation holds is spelled out in place of "Boxed positive flags use the source’s explicit one-object No Pure Contingency observation, applied separately to each closed instance."

### Fails Witnessed Possibility, Separated Structure, Independence (signature Σ), Distinctness Maximalism (signature Σ).

Let $c\in\Sigma$ have relational type $\tau$, so $c=\top_\tau$ necessarily. Witnessed Possibility fails for the pure formula $x\ne\top_\tau$, witnessed by $\bot_\tau$ but impossible of $c$; Separated Structure fails since $\lambda x\, .\,x$ and $\lambda x\, .\,\top_\tau$ agree on $c$ and differ; Independence (signature Σ) fails since $c$ denotes what the closed pure term $\top_\tau$ denotes; Distinctness Maximalism (signature Σ) fails since $c=\top_\tau$ is a true identity that C(Σ) does not prove.

*General argument `arguments/sigma-top`. It requires that Every constant of Σ is relational, and each denotes the top element of its type. Here: This is the interpretation. By Claude Fable 5.1 (Anthropic), at Cian Dorr’s request, 2026-09-22.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic; it uses nothing about the model.

### Holds No Contingency (signature Σ), B for sentences of Σ.

Each constant of Σ denotes what the closed pure term $\top_\tau$ of its type denotes, so a closed sentence of the language of Σ denotes what the pure sentence with $\top_\tau$ in place of each constant denotes; if true it is necessary by No Pure Contingency, which holds here. So No Contingency (signature Σ) holds, and B for sentences of Σ with it: a true Σ-sentence is necessary, hence necessarily possible.

*General argument `arguments/sigma-top-npc`. It requires that Every constant of Σ is relational, and each denotes the top element of its type. Here: This is the interpretation. By Cian Dorr (observation); recorded by Claude Opus 5.5 (Anthropic), 2026-10-02.*

*Revised 2026-10-03 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The argument sigma-single-top, for Σ a single constant of type $t$ denoting $\top$, stated for every interpretation of Σ by top elements, now that such interpretations have no individual constants. It replaces that argument and nc-sigma-homogeneous, which reached the same verdicts through an individual constant when the model's automorphisms carry every individual to every other. With an individual constant and no such automorphisms the verdicts were unknown in 19 models, and nowhere did the individual constants settle a verdict differently.


## Notes

The first of the draft's two variants in which BF is made to fail. Actuality and the range deficiency come from the same finite test here, which is what the next variant prises apart. Atomicity and Rigid Comprehension are not settled in the draft and are left unknown. The source is a work in progress. Everything that implies these fails with them.

## History

The record's revision log before it was written as arguments.

- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Recorded the Distinctness-preserving collapse; see the notes. Now satisfies: Distinctness-preserving collapse.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Re-fixed the interpretation of Σ so as to settle No Contingency (signature Σ) and B for sentences of Σ, at Cian Dorr’s request; see the notes. Now violates: No Contingency (signature Σ), B for sentences of Σ.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Corrected the reason given for the failures of Independence (signature Σ) and Distinctness (signature Σ): the true atom is denoted by no closed pure term, since such terms denote entities fixed by every arrow; the failures come from the other relational constants, which denote top. No verdict changes.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Recorded the failure of Relational Choice, at types (e→t) and e: a functional subrelation of the serial relation pairing each property with its members would be symmetric and finitely pinned, and a symmetry fixing its pinning set would carry its choice for the property of lying outside that set to a second choice. Cian Dorr’s observation that a choice cannot be finitely pinned; argument in the notes. Now violates: Relational Choice.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Recorded the failure of BF at type t, sharpening the failure of BF; argument in the notes. Now violates: BF (type t).
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Recorded the failure of Atomicity (type t), and with it of the Strong Leibniz Biconditionals; see the notes. Now violates: Atomicity (type t).
- **2026-09-22** (Claude Fable 5.1 (Anthropic)) — Fixed an interpretation of Σ (relational constants as top, individual constants as one fixed individual) and recorded the signature schemata it refutes, at Cian Dorr’s request. Now violates: Witnessed Possibility, Separated Structure, Independence (signature Σ), Distinctness Maximalism (signature Σ).
- **2026-09-20** (Claude Fable 5.1 (Anthropic)) — Added both Axioms of Infinity at Cian Dorr's direction. The individuals are the natural numbers and identity at the identity arrow is literal, so no numeral counts them. The propositions that a given individual is fixed by the arrow, one for each individual, are pairwise distinct, symmetric and pinned by that individual, so there are infinitely many propositions. The set of numerals at each type is invariant under every arrow, hence symmetric and pinned by the empty set, so finite cardinality is standard and no finite cardinality holds of the universal property at either type. Now satisfies: Axiom of Infinity (type e), Axiom of Infinity (type t).

## Sources

- **BC does not imply RC** — Cian Dorr, Boolean Completeness does not imply Rigid Comprehension, draft of 30 July 2026, §7.1, p. 21; Proposition 43 and Proposition 44, p. 22; Lemma 21, p. 10; Remark 38, p. 19.

<p class='cert'>Record: <code>topics/classicism/models/symmetric-range-gap.yaml</code></p>

## Paper references

- **Proof: Boolean Completeness does not imply Rigid Comprehension.** Dorr, Cian. Boolean Completeness does not imply Rigid Comprehension. Unpublished draft in progress, 30 July 2026, 27 pages. All page, proposition and lemma locators for this source refer to that draft. Parts of the draft were drafted with AI assistance; its mathematical claims are attributed to the author. — §7.1, p. 21; Proposition 43 and Proposition 44, p. 22; Lemma 21, p. 10; Remark 38, p. 19
