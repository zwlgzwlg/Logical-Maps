# Symmetric ideally-full model: all surjections of N (Base 1)

<p class='cert'>Model — Source: BC does not imply RC (draft); produced by Cian Dorr; recorded by Claude Opus 5 (Anthropic), 19 September 2026.</p>

## Package

- **Boolean Completeness.** Every property of entities of a relational type has a greatest lower bound in that type.
- **Atomlessness.** Atomlessness in the displayed closed propositional formulation.
- **Inextensible Comprehension.** Every relation, including a proposition, is coextensive with a inextensible one.
- **Transversal.** There is a property of properties that picks out exactly one property from each coextension class, that is, exactly one property coextensive with any given property.
- **Axiom of Infinity (type e).** There are not finitely many individuals. No finite cardinality holds of the universal property, so the domain of the type cannot be exhausted by finitely many steps from the empty property.
- **BF.** The Barcan Formula at every type. The predicate formulation closes the formula schema using lambda abstraction.
- **No Pure Contingency.** Each closed sentence of the pure language, if true, is necessary. This is a sentence schema, not a quantifier over propositions.
- **No Contingency (signature Σ).** Each closed sentence of the language of the fixed signature Sigma, if true, is necessary. A sentence schema, standing to No Pure Contingency as Possibility Maximalism (signature Σ) stands to Possibility Maximalism (pure).
- **B for sentences of Σ.** The B instance for every closed sentence of the language of the fixed signature Sigma.
- **¬ Actuality.** There is a true proposition that entails every true proposition.
- **¬ Relational Choice.** Every serial binary relation has a functional subrelation.
- **¬ Intensional Choice.** If a property is necessarily instantiated, then some property entailing it is necessarily uniquely instantiated.
- **¬ Witnessed Possibility.** For pure-formulas P with free variables among a finite tuple x, and distinct matching nonlogical constants c, a witness to P entails that P at those constants is possible.
- **¬ Separated Structure.** For each typed nonlogical constant c and closed same-typed terms F,G not containing c, equality after application to c implies equality of F and G.
- **¬ Independence (signature Σ).** No constant of Sigma is a pure operation applied to other constants: for a closed pure term A and distinct constants c, d_1,…,d_n with n ≥ 0, c differs from A applied to the d’s. With n = 0, no constant denotes a pure entity.
- **¬ Distinctness Maximalism (signature Σ).** The Distinctness Maximalism schema for the fixed nonlogical signature Sigma.

## Definition

A symmetric ideally-full intensional action model over one object, the set of natural numbers. Its arrows are all the surjections of that set, and its symmetry group is all the permutations. A relational domain holds exactly the intensions that are symmetric, meaning indifferent to relabelling the individuals of a world, and pinned down by some finite set. The evaluation point is the identity arrow.

Individuals, fixed for this record: the individuals at each object are the base the construction describes, and the arrows act on them as on the base.

Interpretation of Σ, fixed for this record: every constant of Σ is relational, and each denotes the top element of its type.

*A member of the group Symmetric ideally-full models, which supplies this definition with the record's settings, and the arguments marked as shared.*

## Arguments

### Holds Boolean Completeness.

By the draft's main theorem, whose two hypotheses are verified here with the empty distinguished set: every finite set is amalgamable, since an arrow is prescribed only on a finite set and extends freely, and points can always be moved off a given finite set by a permutation. The least upper bound of a property of type-tau entities is the union of the hulls of its instances.

*By Cian Dorr, 2026-09-19.*

### Fails Actuality.

Given a true proposition pinned down by a finite set, the proposition that a fresh individual is not collapsed with that set is a strictly stronger truth.

*By Cian Dorr, 2026-09-19.*

### Holds Atomlessness.

The same construction, applied to an arbitrary nonzero proposition rather than a true one, splits every possible proposition, which is Atomlessness and hence the failure of Atomicity at type t.

*By Cian Dorr, 2026-09-19.*

### Holds Inextensible Comprehension.

At every relational type. It extends the earlier observations at types $t$ and $e\to t$ and the case $X=\lambda p\, .\,p$ at type $t\to t$, which are instances. Worlds are the arrows $h$, and $h$ sees $i\circ h$. Write $i\cdot r$ for the transport of an entity along $i$; for propositions $i\cdot p=\{k : k\circ i\in p\}$. Three facts about the model are used. (1) Transport: a formula with parameters $\bar r$ holds at $h$ iff it holds at $1$ with parameters $h\cdot\bar r$; in particular whether $Z$ holds of $\bar r$ at $i$ depends only on $i\cdot\bar r$. (2) Pinning: if $r$ is pinned down by $S$ and $g$ fixes $S$ pointwise, then $g\cdot r=r$. (3) Symmetry: the worlds $h$ and $\sigma\circ h$, for a permutation $\sigma$, agree on every root entity; with (2), the extension at $1$ of an $X$ pinned down by $S_X$ is closed under $\tau\cdot$ for every permutation $\tau$ fixing $S_X$ pointwise.
The witness. Given $X$ pinned down by the finite set $S_X$, let $\delta_{S_X}$ be the proposition that no two members of $S_X$ are collapsed, and put $Y:=\lambda\bar z\, .\,\delta_{S_X}\land X\bar z$. It is symmetric and pinned down by $S_X$, and since $\delta_{S_X}$ is true at $1$ it is coextensive with $X$.
Transversal lemma. If $g$ fixes $S_X$ pointwise and $r$ is pinned down by a finite $T$, then $r=g\cdot(\tau\cdot r)$ for a permutation $\tau$ fixing $S_X$ pointwise; so if $r$ is in the extension of $X$ at $1$, then $r=g\cdot r^{\prime}$ for some $r^{\prime}$ also in it. Proof: each $t\in T\setminus S_X$ has a preimage under $g$, as $g$ is surjective, and it lies outside $S_X$, as $g$ fixes $S_X$; choose distinct preimages $t^{\prime}$ and let $\tau$ be a permutation of $\mathbb N\setminus S_X$ with $\tau(t)=t^{\prime}$. Then $g\circ\tau$ fixes $T$ pointwise, so $g\cdot(\tau\cdot r)=(g\circ\tau)\cdot r=r$ by (2), and $\tau\cdot r$ is in the extension of $X$ by (3). The same holds for tuples.
Weak inextensibility at $1$. Let $Z$ hold necessarily of every instance of $Y$, and let $i$ be a world. If $i$ collapses two members of $S_X$, then $\delta_{S_X}$ is false at $i$, so $Y$ is empty there. Otherwise relabel by a permutation, which does not change the world by (3), so that $i$ fixes $S_X$ pointwise. By (1) and (2), $Y$ holds of $\bar r$ at $i$ iff $i\cdot\bar r$ is in the extension of $X$ at $1$; the lemma gives $\bar r^{\prime}$ in that extension with $i\cdot\bar r^{\prime}=i\cdot\bar r$; $Z$ holds of $\bar r^{\prime}$ at $i$, being necessary of it; so by (1) $Z$ holds of $\bar r$ at $i$. Hence $Y\le Z$.
The leading box. At a world $h$ injective on $S_X$, relabel so that $h$ fixes $S_X$; then $h\cdot Y=Y$, and by (1) weak inextensibility at $h$ is weak inextensibility of $Y$ at $1$. At a world collapsing $S_X$, $Y$ is empty there and at every world it sees, since a collapse persists, so it is trivially weakly inextensible. So $Y$ is inextensible. Nothing depends on the argument types. The argument explains the cheapness of inextensibility here: surjectivity and the full permutation group make the necessity of $Z$ cover everything that pinning forces into the extension of $Y$, and the conjunct $\delta_{S_X}$ removes the worlds that collapse the pinning set. The Appendix D models refuting Inextensible Comprehension lack one of these features: an arrow fixing the pinning set may leave points without a preimage outside it, or the relabelling permutations may be missing.

*Address: `symmetric-all-surjections#inextensible-comprehension`. By Claude Opus 5.5 (Anthropic), checked by Cian Dorr, 2026-09-27.*

### Holds Transversal.

At every type. Write $A_h$ for the extension of a property $A$ at the arrow $h$; transport gives $(k\cdot A)_h=A_{h\circ k}$, symmetry gives $A_{g\circ h}=g\cdot A_h$ for permutations $g$, and pinning by $S$ makes $A_h$ depend only on $h{\restriction}S$. If $A$ is pinned by $S$, every permutation fixing $S$ pointwise fixes $E:=A_{\mathbf 1}$; finite supports for the full permutation group are closed under intersection, so $E$ has a least support $S_E$, and $S_{g\cdot E}=g[S_E]$. Let $\hat E$ have extension $g\cdot E$ at $h$ when $h$ is injective on $S_E$, for any permutation $g$ agreeing with $h$ on $S_E$ (well defined, since two such $g$ differ by a permutation fixing $S_E$), and $\varnothing$ when it is not. Then $\hat E$ is pinned by $S_E$, symmetric, and coextensive with $A$ at $\mathbf 1$, and $g\cdot\hat E=\widehat{g\cdot E}$. So the property $F$ whose extension at every arrow is the set of all such $\hat E$ is pinned by $\varnothing$ and symmetric, hence in the domain; at $\mathbf 1$ it holds of exactly one property coextensive with any given property, since $\hat E$ is determined by $E$. Qualitatively, $F$ holds of $X$ iff the least pinning set of $X$ is the least support of its actual extension and, necessarily, if $X$ is instantiated then the members of that set are pairwise distinct; the minimality clause is needed, since a property pinned by $S_E$ together with one further point, and empty wherever that point collides with $S_E$, is coextensive with $\hat E$ but distinct from it. Since a one-object model has No Pure Contingency and $F$ is pinned by $\varnothing$, every instance of Transversal holds at every world.

*Address: `symmetric-all-surjections#transversal`. By Claude Opus 5.5 (Anthropic), checked by Cian Dorr, verifying GPT-6's proposed least-support witness of 30 September, 2026-10-01.*

### Fails Relational Choice.

At the types $(e\to t)$ and $e$. Let $U:=\lambda Xy\, .\,Xy\lor\neg\exists z\, .\,Xz$, a closed term, hence in the domain, and serial. A functional subrelation $S$ of $U$ would lie in the domain at the evaluation object, so it is symmetric and pinned down by a finite set $N$. Two facts about such an $S$ (Dorr, draft, Lemma 21): every $g\in G$ fixing $N$ pointwise satisfies $g^{[\sigma]}S=S$, and symmetry gives $\langle gA,gy,g\rangle\in S$ whenever $\langle A,y,1\rangle\in S$; together, $\langle gA,gy,1\rangle\in S$. Now let $A$ be the property the condition gives for $N$. Its extension is nonempty, so $S$ relates $A$ at the identity to some $y$ in its extension. The condition gives a member $g$ of the symmetry group that fixes $N\cup M$ pointwise, fixes $A$ and moves $y$ to some $gy\ne y$, so $S$ relates $A$ to $gy$ as well, and $S$ is not functional at the identity arrow. The well-ordering of the individuals that Cian Dorr had in mind is refuted by the same two facts, but the direct route needs no derivation of a well-ordering from Relational Choice in C.

*From the group *Symmetric ideally-full models*, shared argument `symmetric-ideally-full#relational-choice`. It requires that There is a finite set $M$ of individuals at the evaluation object such that, for each finite set $N$, some property $A$ in the domain, symmetric and pinned down by $N\cup M$, has a nonempty extension, and each individual $y$ in that extension is moved by a member of the symmetry group that fixes $N\cup M$ pointwise and fixes $A$. Here: $M=\emptyset$, and for $N$ the property of not belonging to $N$: the transposition of $y$ with another individual outside $N$ is a permutation, so lies in the symmetry group. By Claude Fable 5.1 (Anthropic), after Cian Dorr’s observation that a choice over the individuals cannot be finitely pinned down, 2026-09-23.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The members' seven copies, which differed in the property $A$ and the transposition, stated once; each member's $A$ and transposition moved to the condition transposable. The qualitative-contrast model's second argument (OpenAI Codex, 24 September) was dropped.

### Holds Axiom of Infinity (type e).

There are infinitely many individuals, and identity at the identity arrow is literal, so no numeral counts them. The set of numerals at type $e$ is fixed by every arrow, hence symmetric and pinned down by the empty set, so finite cardinality is standard and no finite cardinality holds of the universal property.

*From the group *Symmetric ideally-full models*, shared argument `symmetric-ideally-full#axiom-of-infinity-e`. By Claude Fable 5.1 (Anthropic), at Cian Dorr's direction, 2026-09-20.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The type-$e$ half of the members' argument, stated once; "the individuals are the natural numbers" became "there are infinitely many individuals", which also covers the qualitative links model. The type-$t$ half is axiom-of-infinity-t.

### Holds BF.

At every type. Let $B$ be an entity at the target of an arrow $i$, pinned down by the finite set $M$, and choose a finite set $P$ with a map $s:M\to P$ such that $i\circ s$ is the identity on $M$, possible because $i$ is surjective. Put $A:=\{\langle\bar x,j\rangle : \langle\bar x,k\rangle\in B$ for some arrow $k$ with $k|_M=j\circ s\}$. This is well defined because $B$ is pinned down by $M$. It is pinned down by $P$ and symmetric, since $B$ is. And $i\cdot A=B$: $\langle\bar x,k\rangle\in i\cdot A$ iff $\langle\bar x,k\circ i\rangle\in A$ iff $\langle\bar x,k'\rangle\in B$ for some $k'$ with $k'|_M=k|_M$, iff $\langle\bar x,k\rangle\in B$. So every entity at every world is the transport of an entity at the evaluation point, and a relation that is necessarily true of every entity is necessarily true of all of them.

*Source: Boolean Completeness does not imply Rigid Comprehension, §3.1, p. 9; Proposition 22, p. 11. From the group *Symmetric ideally-full models*, shared argument `symmetric-ideally-full#barcan-surjective`. It requires that Every arrow is surjective. Here: The arrows are all the surjections of $\mathbb N$. By Claude Opus 5.5 (Anthropic), at Cian Dorr's request, 2026-09-27.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The qualitative links model's argument, which proves the draft's claim for the all-surjections model ("at every type because every arrow is surjective and a finitely pinned symmetric intension can be pulled back along an arrow"), stated once for every member whose arrows are surjective.

### Fails Intensional Choice.

At type $e$. Let $F$ and $a$ be as the condition gives them, and suppose $G\le F$ is necessarily uniquely instantiated. $G$ is in the domain, so it is symmetric and pinned down by a finite set, which we may take to contain $a$; call it $N$. Let $h$ be the arrow the condition gives for $N$. Then $G_h=\{y\}$ for some $y$ in $F_h$. If $\sigma$ in the symmetry group fixes $p$, then $\sigma\circ h$ agrees with $h$ on $N$, so $G_{\sigma\circ h}=G_h$ by pinning, while symmetry gives $G_{\sigma\circ h}=\{\sigma y\}$. So no symmetry fixing $p$ moves $y$, and by the condition $y=p$. Each model's witness takes $F$ with $p$ outside its extension at $h$, a contradiction. $\Box$Intensional Choice fails with it, by T.

*General argument `arguments/intensional-choice-collapse`. It requires that A group $G$ acts on the individuals at the evaluation object, and every element of a relational domain there is symmetric, meaning that $\langle\bar x,h\rangle\in D$ implies $\langle g\cdot\bar x,g\circ h\rangle\in D$ whenever $g\in G$ and $g\circ h$ is an arrow, and is pinned down by a finite set of individuals, its extension at an arrow depending only on the arrow's values there. Here: The relational domains hold exactly the symmetric intensions pinned down by a finite set (Dorr, draft, Definitions 15–18). It requires that The individuals at the evaluation object are those the construction acts on, and the arrows act on them as the construction says. Here: The individuals are the base, acted on as the construction says. It requires that There are an individual $a$ and a necessarily instantiated property $F$ in the domain such that, for every finite set $N$ of individuals at the evaluation object, some arrow $h$ sends $N\cup\{a\}$ to a single individual $p$, and every individual $y\ne p$ in $F$'s extension at $h$ is moved by a member $\sigma$ of the symmetry group that fixes $p$, with $\sigma\circ h$ again an arrow. Here: Take $F:=\lambda x\, .\,x\ne a$, so $p\notin F_h$. $h$ is any surjection constant on $N\cup\{a\}$, and a transposition of $y$ with a point outside $N\cup\{a,p\}$ fixes $p$ and moves $y$. By Claude Opus 5.5 (Anthropic), 2026-10-03.*

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

This is the draft's headline separation. Boolean Completeness holds while Rigid Comprehension fails, and since Actuality fails too, Weak Rigid Comprehension fails here as well, which is recorded as a derived verdict. The source is a work in progress.

Open question: is there a closed term of the language, at each type, that denotes this classifier $F$? Pairwise distinctness over a variable number of individuals is expressible with a plural variable $Y^{e\to t}$, as $\forall y\,y'\,((Yy\land Yy'\land y\ne y')\to\Box(\exists z\, .\,Xz\to y\ne y'))$. What is not obvious is how to say in the object language that $X$ is minimally pinned down by the $Y$s.

## History

The record's revision log before it was written as arguments.

- **2026-10-01** (Claude Opus 5.5 (Anthropic), checked by Cian Dorr) — Recorded Transversal and its necessitation at every type, verifying GPT-6's proposed least-support witness of 30 September; see the notes. The separate conjectured record symmetric-all-surjections-transversal is retired. Added the open question whether the classifier is denoted by a closed term. Now satisfies: Transversal, □Transversal.
- **2026-09-30** (GPT-6 (OpenAI Codex), at Zachary Goodsell's request) — Linked the separate bronze-tier conjecture symmetric-all-surjections-transversal and its proposed least-support argument. The established satisfies and violates lists are unchanged.
- **2026-09-27** (Claude Opus 5.5 (Anthropic), checked by Cian Dorr) — Recorded Inextensible Comprehension at every relational type: the witness for X pinned down by S is the conjunction of X with the proposition that S is uncollapsed, and a transversal lemma using surjectivity and the full permutation group shows it inextensible. Replaces the note that left it unknown. Now satisfies: Inextensible Comprehension.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Re-fixed the interpretation of Σ so as to settle No Contingency (signature Σ) and B for sentences of Σ, at Cian Dorr’s request; see the notes. Now satisfies: No Contingency (signature Σ), B for sentences of Σ.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Recorded the failure of Relational Choice, at types (e→t) and e: a functional subrelation of the serial relation pairing each property with its members would be symmetric and finitely pinned, and a symmetry fixing its pinning set would carry its choice for the property of lying outside that set to a second choice. Cian Dorr’s observation that a choice cannot be finitely pinned; argument in the notes. Now violates: Relational Choice.
- **2026-09-23** (Claude Fable 5.1 (Anthropic)) — Noted why Inextensible Comprehension is left unknown: its type-t and type-(e→t) instances hold here, so the failure of Actuality does not sharpen to it at those types.
- **2026-09-22** (Claude Fable 5.1 (Anthropic)) — Fixed an interpretation of Σ (relational constants as top, individual constants as one fixed individual) and recorded the signature schemata it refutes, at Cian Dorr’s request. Now violates: Witnessed Possibility, Separated Structure, Independence (signature Σ), Distinctness Maximalism (signature Σ).
- **2026-09-20** (Claude Fable 5.1 (Anthropic)) — Added both Axioms of Infinity at Cian Dorr's direction. The individuals are the natural numbers and identity at the identity arrow is literal, so no numeral counts them. The propositions that a given individual is fixed by the arrow, one for each individual, are pairwise distinct, symmetric and pinned by that individual, so there are infinitely many propositions. The set of numerals at each type is invariant under every arrow, hence symmetric and pinned by the empty set, so finite cardinality is standard and no finite cardinality holds of the universal property at either type. Now satisfies: Axiom of Infinity (type e), Axiom of Infinity (type t).

## Sources

- **BC does not imply RC** — Cian Dorr, Boolean Completeness does not imply Rigid Comprehension, draft of 30 July 2026, §3.1, p. 9 (base); Proposition 22, p. 11; Proposition 23, p. 12; Theorem 36, p. 18; Corollary 37 and Remark 38, p. 19.
- **GPT-6 proposal 30 Sep; checked 1 Oct** — GPT-6 (OpenAI Codex), proposed least-support witness for Transversal, 30 September 2026, at Zachary Goodsell's request; checked by Claude Opus 5.5 (Anthropic) and Cian Dorr, 1 October 2026.

<p class='cert'>Record: <code>topics/classicism/models/symmetric-all-surjections.yaml</code></p>

## Paper references

- **Proof: Boolean Completeness does not imply Rigid Comprehension.** Dorr, Cian. Boolean Completeness does not imply Rigid Comprehension. Unpublished draft in progress, 30 July 2026, 27 pages. All page, proposition and lemma locators for this source refer to that draft. Parts of the draft were drafted with AI assistance; its mathematical claims are attributed to the author. — §3.1, p. 9; Proposition 22, p. 11; Proposition 23, p. 12; Theorem 36, p. 18; Corollary 37 and Remark 38, p. 19
- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — Appendix D, pp. 73–79. The ideally-full action models of which this is the symmetric variant, and the failures of Boolean Completeness that symmetry blocks.
