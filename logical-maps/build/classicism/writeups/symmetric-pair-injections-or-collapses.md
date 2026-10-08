# Symmetric ideally-full model: pair-preserving injections and pair collapses

<p class='cert'>Model — Source: Misc.; produced by Cian Dorr (the construction, 8 October 2026, as the symmetric analogue of finite-support-pair-injections-or-collapses); Claude Opus 5.5 (Anthropic) (the verdicts, 8 October 2026); recorded by Claude Opus 5.5 (Anthropic), 8 October 2026.</p>

## Package

- **BF.** The Barcan Formula at every type. The predicate formulation closes the formula schema using lambda abstraction.
- **Rigid Comprehension.** Every relation, including a proposition, is coextensive with a rigid one.
- **Axiom of Infinity (type e).** There are not finitely many individuals. No finite cardinality holds of the universal property, so the domain of the type cannot be exhausted by finitely many steps from the empty property.
- **Axiom of Infinity (type t).** There are not finitely many propositions. No finite cardinality holds of the universal property, so the domain of the type cannot be exhausted by finitely many steps from the empty property.
- **Distinctness-preserving collapse.** Every truth is necessary under the distinctness-preserving modality.
- **No Pure Contingency.** Each closed sentence of the pure language, if true, is necessary. This is a sentence schema, not a quantifier over propositions.
- **No Contingency (signature Σ).** Each closed sentence of the language of the fixed signature Sigma, if true, is necessary. A sentence schema, standing to No Pure Contingency as Possibility Maximalism (signature Σ) stands to Possibility Maximalism (pure).
- **B for sentences of Σ.** The B instance for every closed sentence of the language of the fixed signature Sigma.
- **¬ Atomicity (type t).** Atomicity (type t) in the displayed closed propositional formulation.
- **¬ Rigid Power.** If a relation is rigid, so is the property of being a rigid relation that entails it.
- **¬ Relational Choice.** Every serial binary relation has a functional subrelation.
- **¬ Intensional Choice.** If a property is necessarily instantiated, then some property entailing it is necessarily uniquely instantiated.
- **¬ Witnessed Possibility.** For pure-formulas P with free variables among a finite tuple x, and distinct matching nonlogical constants c, a witness to P entails that P at those constants is possible.
- **¬ Separated Structure.** For each typed nonlogical constant c and closed same-typed terms F,G not containing c, equality after application to c implies equality of F and G.
- **¬ Independence (signature Σ).** No constant of Sigma is a pure operation applied to other constants: for a closed pure term A and distinct constants c, d_1,…,d_n with n ≥ 0, c differs from A applied to the d’s. With n = 0, no constant denotes a pure entity.
- **¬ Distinctness Maximalism (signature Σ).** The Distinctness Maximalism schema for the fixed nonlogical signature Sigma.

## Definition

A symmetric ideally-full intensional action model over one object, the set of natural numbers. Its arrows are the functions that identify $0$ with $1$ (the collapses) and the injections that map $\{0,1\}$ onto itself (the pair-preserving injections); its symmetry group is the permutations that preserve $\{0,1\}$ setwise. The evaluation point is the identity arrow.

Individuals, fixed for this record: the individuals at each object are the base the construction describes, and the arrows act on them as on the base.

Interpretation of Σ, fixed for this record: every constant of Σ is relational, and each denotes the top element of its type.

*A member of the group Symmetric ideally-full models, which supplies this definition with the record's settings, and the arguments marked as shared.*

## Arguments

### Holds BF.

At every type, as in finite-support-pair-injections-or-collapses: every arrow agrees on any finite set with a surjective arrow (a permutation preserving $\{0,1\}$, or a surjective collapse), and the pullback of a symmetric entity along it is symmetric, as in the group's argument barcan-surjective; so if $\forall y\,\Box Xy$ holds while $X$, pinned down by $N$, omits $\langle a,k\rangle$, take $j$ surjective agreeing with $k$ on $N$ and $a=j\cdot b$, so that $\langle a,j\rangle\in X$, and by pinning $\langle a,k\rangle\in X$.

*By Claude Opus 5.5 (Anthropic), 2026-10-08.*

### Fails Atomicity (type t).

The collapses form a nonempty proposition, pinned down by $\{0,1\}$ and symmetric, with no atom below it. A nonempty symmetric proposition $p$ of collapses pinned down by a finite $T\supseteq\{0,1\}$ contains a collapse $h$; for $m\notin T$, the collapses agreeing with $h$ on $T$ and sending $m$ into $h[T]$, and those sending $m$ outside $h[T]\cup\{0,1\}$, are both in $p$, and the propositions $\{k : km\in k[T]\}$ and its complement, symmetric and pinned down by $T\cup\{m\}$, split $p$.

*By Claude Opus 5.5 (Anthropic), 2026-10-08.*

### Fails Rigid Power.

The argument of finite-support-pair-injections-or-collapses, whose witnesses are all symmetric. $Y$, with $Y_k=\mathbb N\setminus\{k2\}$ at a pair-preserving injection and $\mathbb N$ at a collapse: a symmetry $g$ keeps $y\ne k2$ as $gy\ne(g\circ k)2$, and $g\circ k$ is in the class of $k$. $\top$ is rigid by $\Box$BF. Along a collapse a weakly rigid property has extension $\mathbb N$ or a finite one: the infinite case uses persistence and pinning only, the finite one the property $k\mapsto k[S]$, which is symmetric. And $\mathbf X$, holding at $k$ of the transports $k'\cdot Z$ of the rigid $Z$ along arrows $k'$ agreeing with $k$ on $\{0,1\}$, is symmetric, since $g\cdot(k'\cdot Z)=(g\circ k')\cdot Z$ and $g\circ k'$ agrees with $g\circ k$ on $\{0,1\}$ (the rigid properties being closed under transport along symmetries). So the property of being a rigid property of individuals is not weakly inextensible, though $\top$ is rigid.

*By Claude Opus 5.5 (Anthropic), 2026-10-08.*

### Holds Rigid Comprehension.

At every relational type. Let $X$ have extension $S$ at the identity and be pinned down by $N\supseteq\{0,1\}$; by symmetry and pinning, $g\cdot s\in S$ for $s\in S$ and $g$ a symmetry fixing $N$ pointwise. Put $L:=\{\langle k'\cdot s,k\rangle : s\in S,\ k'\text{ agreeing with }k\text{ on }N\}$: it is pinned down by $N$, and symmetric, since $g\cdot(k'\cdot s)=(g\circ k')\cdot s$. Its extension is $S$: an arrow $k'$ agreeing with the identity on $N$ is an injection fixing $N$, and agrees on $N\cup M_s$ ($M_s$ pinning $s$) with a symmetry $g$ fixing $N$, so $k'\cdot s=g\cdot s\in S$. It is persistent: $j\cdot(k'\cdot s)=(j\circ k')\cdot s$ with $j\circ k'$ agreeing with $j\circ k$ on $N$. It is inextensible at every world $w$: let $X'$, pinned down by $N'$, contain $\langle j\cdot x,j\rangle$ for every $x\in L_w$ and arrow $j$, and let $k'\cdot s\in L_{j\circ w}$, with $k'$ agreeing with $j\circ w$ on $N$. Choose an arrow $k''$ agreeing with $w$ on $N$ and an arrow $j'$ agreeing with $j$ on $N'\cup\{0,1\}\cup w[N]$ with $j'\circ k''$ agreeing with $k'$ on $M_s$: for $a\in M_s\setminus N$, if $k'a=jd$ for some $d$ put $k''a:=d$ and keep $j'=j$ at $d$; otherwise send $a$ to a fresh point $z$ and put $j'z:=k'a$. When $j$ is an injection, $k'a$ outside the range of $j$ is outside $\{0,1\}$, so $j'$ stays a pair-preserving injection; when $w$ is an injection, so is $k'$, and the $d$ so chosen lie outside $w[N]$ and $\{0,1\}$ and are distinct, so $k''$ stays a pair-preserving injection; collapses take any values. Then $k''\cdot s\in L_w$, so $\langle(j'\circ k'')\cdot s,j'\rangle=\langle k'\cdot s,j'\rangle\in X'$, and by pinning $\langle k'\cdot s,j\rangle\in X'$. So $L$ is rigid and coextensive with $X$.

*By Claude Opus 5.5 (Anthropic), 2026-10-08.*

### Fails Relational Choice.

At the types $(e\to t)$ and $e$. Let $U:=\lambda Xy\, .\,Xy\lor\neg\exists z\, .\,Xz$, a closed term, hence in the domain, and serial. A functional subrelation $S$ of $U$ would lie in the domain at the evaluation object, so it is symmetric and pinned down by a finite set $N$. Two facts about such an $S$ (Dorr, draft, Lemma 19(iv)): every $g\in G$ fixing $N$ pointwise satisfies $g^{[\sigma]}S=S$, and symmetry gives $\langle gA,gy,g\rangle\in S$ whenever $\langle A,y,1\rangle\in S$; together, $\langle gA,gy,1\rangle\in S$. Now let $A$ be the property the condition gives for $N$. Its extension is nonempty, so $S$ relates $A$ at the identity to some $y$ in its extension. The condition gives a member $g$ of the symmetry group that fixes $N$ pointwise, fixes $A$ and moves $y$ to some $gy\ne y$, so $S$ relates $A$ to $gy$ as well, and $S$ is not functional at the identity arrow. The well-ordering of the individuals that Cian Dorr had in mind is refuted by the same two facts, but the direct route needs no derivation of a well-ordering from Relational Choice in C.

*From the group *Symmetric ideally-full models*, shared argument `symmetric-ideally-full#relational-choice`. It requires that For each finite set $N$ of individuals at the evaluation object, some property $A$ in the domain has a nonempty extension there, and each individual $y$ in that extension is moved by a member of the symmetry group that fixes $N$ pointwise and fixes $A$. Here: For $N$ the property of not belonging to $N\cup\{0,1\}$: the transposition of $y$ with another individual outside $N\cup\{0,1\}$ fixes $\{0,1\}$, so lies in the symmetry group. By Claude Fable 5.1 (Anthropic), after Cian Dorr’s observation that a choice over the individuals cannot be finitely pinned down, 2026-09-23.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The members' seven copies, which differed in the property $A$ and the transposition, stated once; each member's $A$ and transposition moved to the condition transposable. The qualitative-contrast model's second argument (OpenAI Codex, 24 September) was dropped.

*Revised 2026-10-06 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The condition transposable no longer mentions the finite set $M$ or the pinning of $A$ by $N\cup M$: the argument uses only that $g$ fixes $N$, the set pinning down $S$, and that $A$ is in the domain. So $g$ is now said to fix $N$ pointwise. Proved in Lean.

### Holds Axiom of Infinity (type e).

There are infinitely many individuals, and identity at the identity arrow is literal, so no numeral counts them. The set of numerals at type $e$ is fixed by every arrow, hence symmetric and pinned down by the empty set, so finite cardinality is standard and no finite cardinality holds of the universal property.

*From the group *Symmetric ideally-full models*, shared argument `symmetric-ideally-full#axiom-of-infinity-e`. It requires that There are infinitely many individuals at the evaluation world. Here: The base is infinite. By Claude Fable 5.1 (Anthropic), at Cian Dorr's direction, 2026-09-20.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The type-$e$ half of the members' argument, stated once; "the individuals are the natural numbers" became "there are infinitely many individuals", which also covers the qualitative links model. The type-$t$ half is axiom-of-infinity-t.

### Holds Axiom of Infinity (type t).

The propositions $C_{n,m}:=\{h : hn=hm\}$, that an arrow collapses $n$ and $m$, are symmetric, since relabelling the individuals of a world by a member of the symmetry group keeps identities among them, and each is pinned down by $\{n,m\}$; by the condition infinitely many of them are pairwise distinct, so there are infinitely many propositions. The set of numerals at type $t$ is fixed by every arrow, hence symmetric and pinned down by the empty set, so finite cardinality is standard and no finite cardinality holds of the universal property.

*From the group *Symmetric ideally-full models*, shared argument `symmetric-ideally-full#axiom-of-infinity-t`. It requires that There are infinitely many pairs of individuals such that, for any two of these pairs, some arrow collapses the one and not the other. Here: The pairs $\{n,m\}$ with $n,m\ge2$: a function that identifies $0$ with $1$ and $n$ with $m$, and nothing else, is an arrow. By Claude Opus 5.5 (Anthropic), at Cian Dorr's direction, 2026-10-02.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Replaces the members' argument of 20 September (Claude Fable 5.1), which used the propositions $\{h : hn=n\}$ that an arrow fixes a given individual. Those are not symmetric when the symmetry group moves $n$: symmetry asks that $h\in p$ imply $g\circ h\in p$, and $(g\circ h)n=gn$.

### Holds Distinctness-preserving collapse.

For a true $p$, $a\le p$, since $a$ entails every truth. Take $q:=a$ in the definition of $\Box_{\ne}p$: at a world in $a$, $p$ holds; at a world outside $a$, $\Diamond a$ fails. So every truth is $\Box_{\ne}$-necessary.

*General argument `arguments/dpc-isolated-actual-world`. It requires that The actual-world proposition $a$ is in the domain and entails every truth, and no world outside $a$ sees a world in $a$. Here: The actual-world proposition is the set of pair-preserving injections: it is symmetric and pinned down by $\{0,1\}$, and a symmetric proposition pinned down by a finite $T\supseteq\{0,1\}$ that contains the identity contains every pair-preserving injection $h$, since $h$ agrees on $T$ with a permutation preserving $\{0,1\}$. Every other arrow is a collapse, and every composite with a collapse is one. By Claude Fable 5.1 (Anthropic), 2026-09-23.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The finite-support, symmetric and full action models' copies (eight records) stated once for the topic; what varied, why no world outside the actual world sees back into it, is each record's reason for meeting actual-world-isolated.

### Fails Intensional Choice.

At type $e$. Let $F$ and $a$ be as the condition gives them, and suppose $G\le F$ is necessarily uniquely instantiated. $G$ is in the domain, so it is symmetric and pinned down by a finite set, which we may take to contain $a$; call it $N$. Let $h$ be the arrow the condition gives for $N$. Then $G_h=\{y\}$ for some $y$ in $F_h$. If $\sigma$ in the symmetry group fixes $p$, then $\sigma\circ h$ agrees with $h$ on $N$, so $G_{\sigma\circ h}=G_h$ by pinning, while symmetry gives $G_{\sigma\circ h}=\{\sigma y\}$. So no symmetry fixing $p$ moves $y$, and by the condition $y=p$. Each model's witness takes $F$ with $p$ outside its extension at $h$, a contradiction. $\Box$Intensional Choice fails with it, by T.

*General argument `arguments/intensional-choice-collapse`. It requires that A group $G$ acts on the individuals at the evaluation object, and every element of a relational domain there is symmetric, meaning that $\langle\bar x,h\rangle\in D$ implies $\langle g\cdot\bar x,g\circ h\rangle\in D$ whenever $g\in G$ and $g\circ h$ is an arrow, and is pinned down by a finite set of individuals, its extension at an arrow depending only on the arrow's values there. Here: The relational domains hold exactly the symmetric intensions pinned down by a finite set (Dorr, draft, Definitions 15–18). It requires that The individuals at the evaluation object are those the construction acts on, and the arrows act on them as the construction says. Here: The individuals are the base, acted on as the construction says. It requires that There are an individual $a$ and a necessarily instantiated property $F$ in the domain such that, for every finite set $N$ of individuals at the evaluation object, some arrow $h$ sends $N\cup\{a\}$ to a single individual $p$, and every individual $y\ne p$ in $F$'s extension at $h$ is moved by a member $\sigma$ of the symmetry group that fixes $p$, with $\sigma\circ h$ again an arrow. Here: Take $F:=\lambda x\, .\,x\ne a$, so $p\notin F_h$. $h$ is a collapse sending $N\cup\{a,0,1\}$ to one $p\notin\{0,1\}$. Swapping $0$ with $1$, or transposing $y$ with a point outside $\{0,1,p,y\}$, fixes $p$, and composes with $h$ to a collapse. By Claude Opus 5.5 (Anthropic), 2026-10-03.*

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

Recorded with only the verdicts the engine needs (Atomicity at type $t$ for the one-individual variant); Actuality and Boolean Completeness follow. For the record, Boolean Completeness also has a direct proof: Dorr's Theorem 36 with the moving symmetry chosen so that injections splice, no arrow being separated here (if $h'a=hq$ for $a$ in the instance's pinning set and $q$ in the upper bound's, move $a$ to $q$).
The symmetric analogue, proposed by Cian Dorr, of finite-support-pair-injections-or-collapses, whose failure of Rigid Power survives the symmetry condition with the same witnesses. Unlike the finite-support model it has Actuality: a symmetric proposition pinned down by a finite set and containing one pair-preserving injection contains them all, so they form a true atom entailing every truth. With Rigid Comprehension, Boolean Completeness and BF holding, the model shows that Rigid Comprehension, even boxed and with Actuality and BF, does not imply Rigid Power. The symmetries are taken to preserve $\{0,1\}$ setwise; with those fixing $0$ and $1$ the arguments are the same.

## Sources

- **Dorr 8 Oct** — Cian Dorr, suggestion of 8 October 2026, in conversation with Claude Opus 5.5 (Anthropic): the model finite-support-pair-injections-or-collapses with the symmetry condition for the permutations fixing $\{0,1\}$, asking whether Rigid Power still fails. Transcript in .private.
- **BC does not imply RC** — Cian Dorr, Boolean Completeness does not imply Rigid Comprehension, draft of 30 July 2026, Definitions 15–18, p. 8 (the symmetric ideally-full construction).

<p class='cert'>Record: <code>topics/classicism/models/symmetric-pair-injections-or-collapses.yaml</code></p>

## Paper references

- **Background: Boolean Completeness does not imply Rigid Comprehension.** Dorr, Cian. Boolean Completeness does not imply Rigid Comprehension. Unpublished draft in progress, 30 July 2026, 27 pages. All page, proposition and lemma locators for this source refer to that draft. Parts of the draft were drafted with AI assistance; its mathematical claims are attributed to the author. — Definitions 15–18, p. 8. The symmetric ideally-full construction, over the monoid of the finite-support model finite-support-pair-injections-or-collapses; Base 2 (symmetric-collapse-pair) with the permutations replaced by all the pair-preserving injections and the surjective collapses by all the collapses.
