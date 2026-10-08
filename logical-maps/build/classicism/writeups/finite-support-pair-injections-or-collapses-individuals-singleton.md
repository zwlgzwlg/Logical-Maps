# Finite-support action model: pair-preserving injections and pair collapses of N [one individual]

<p class='cert'>Model — Source: Misc.; produced by Cian Dorr (the construction, and the expectation that Vicinity holds and Actuality fails, 7 October 2026); Claude Opus 5.5 (Anthropic) (closure under composition, the other verdicts, and the failure of Rigid Power, 7 October 2026); recorded by Claude Opus 5.5 (Anthropic), 8 October 2026.</p>

## Package

- **Vicinity.** There is a true proposition that entails the possibility of each true proposition.
- **BF.** The Barcan Formula at every type. The predicate formulation closes the formula schema using lambda abstraction.
- **Atomlessness.** Atomlessness in the displayed closed propositional formulation.
- **Axiom of Infinity (type t).** There are not finitely many propositions. No finite cardinality holds of the universal property, so the domain of the type cannot be exhausted by finitely many steps from the empty property.
- **Infinity Schema (type t).** There are arbitrarily many pairwise distinct entities of this fixed type; one sentence for each positive integer n.
- **□Intensional Choice.** Every closed instance of Intensional Choice is necessary. Box the entire object-variable closure; retain the same type range and other schema side conditions.
- **No Pure Contingency.** Each closed sentence of the pure language, if true, is necessary. This is a sentence schema, not a quantifier over propositions.
- **Countable Boolean Completeness.** Every countable property of entities of a relational type has a least upper bound in that type, where a property is countable when it injects into the natural numbers.
- **Transversal Choice.** Every equivalence relation, at any type including e, has a transversal, that is, a property with exactly one instance in each of its cells.
- **No Contingency (signature Σ).** Each closed sentence of the language of the fixed signature Sigma, if true, is necessary. A sentence schema, standing to No Pure Contingency as Possibility Maximalism (signature Σ) stands to Possibility Maximalism (pure).
- **B for sentences of Σ.** The B instance for every closed sentence of the language of the fixed signature Sigma.
- **¬ Boolean Completeness (type t).** Boolean Completeness (type t) in the displayed closed propositional formulation.
- **¬ Axiom of Infinity (type e).** There are not finitely many individuals. No finite cardinality holds of the universal property, so the domain of the type cannot be exhausted by finitely many steps from the empty property.
- **¬ Infinity Schema (type e).** There are arbitrarily many pairwise distinct entities of this fixed type; one sentence for each positive integer n.
- **¬ Possible Infinity (type e).** Possibly there are not finitely many individuals: the Axiom of Infinity at this type, under a diamond.
- **¬ Witnessed Possibility.** For pure-formulas P with free variables among a finite tuple x, and distinct matching nonlogical constants c, a witness to P entails that P at those constants is possible.
- **¬ Separated Structure.** For each typed nonlogical constant c and closed same-typed terms F,G not containing c, equality after application to c implies equality of F and G.
- **¬ Independence (signature Σ).** No constant of Sigma is a pure operation applied to other constants: for a closed pure term A and distinct constants c, d_1,…,d_n with n ≥ 0, c differs from A applied to the d’s. With n = 0, no constant denotes a pure entity.
- **¬ Distinctness Maximalism (signature Σ).** The Distinctness Maximalism schema for the fixed nonlogical signature Sigma.

## Definition

The arrows are the functions $f$ on $\mathbb N$ that either identify $0$ with $1$ ($f0=f1$, the collapses) or are injective and map $\{0,1\}$ onto itself (the pair-preserving injections). These compose: two pair-preserving injections compose to one, and a composite with a collapse applied after a pair-preserving injection, or with a collapse applied first, identifies $0$ with $1$. In every part, $W_0^\ddagger$ is the set of finite subsets of $\mathbb N$ and the model is ideally full: a proposition is a set of arrows whose membership depends only on the arrows’ values on some finite set of numbers (it is pinned down by that set), and an entity of a higher type is an applicative behaviour profile pinned down by a finite set in the same sense. There is a single individual, which every arrow fixes; the arrows still act on $\mathbb N$, which supplies the pinning sets. Propositions and properties are thus about finitely many numbers and indifferent to how the arrows treat the rest. Evaluation point: the sole object, at the identity arrow.

Interpretation of Σ, fixed for this record: every constant of Σ is relational, and each denotes the top element of its type.

*A member of the group Finite-support action models on one object, which supplies this definition with the record's settings, and the arguments marked as shared.*

## Arguments

### Holds Vicinity.

The witness is the proposition $p:=\{h : h0\ne h1\}$, the pair-preserving injections, pinned down by $\{0,1\}$ and true. Let $q$ be true, pinned down by a finite $N$, and let $k$ be a pair-preserving injection. The inverse of $k$ on $k[N\cup\{0,1\}]$ maps $\{0,1\}$ onto itself and every other point outside $\{0,1\}$, so it extends to a pair-preserving injection $j$. Then $j\circ k$ agrees with the identity on $N$, so $j\circ k\in q$. Hence every $p$-world can reach a $q$-world: $p\le\Diamond q$.

*By Claude Opus 5.5 (Anthropic), confirming Cian Dorr's expectation, 2026-10-07.*

### Holds BF.

At every type. Every arrow agrees on any finite set with a surjective arrow: a pair-preserving injection with a permutation preserving $\{0,1\}$, a collapse with a surjective collapse. So, as for the monoid of all functions (Appendix D, Part 3), if $\forall y\,\Box Xy$ holds while $X$, pinned down by $N$, omits $\langle a,k\rangle$, take $j$ surjective agreeing with $k$ on $N$, so that $a=j\cdot b$ for some $b$ by pulling back along $j$; then $\langle a,j\rangle\in X$, and so, by pinning, $\langle a,k\rangle\in X$.

*By Claude Opus 5.5 (Anthropic), 2026-10-07.*

### Holds Atomlessness.

Every arrow can be changed at a point outside any finite set without leaving its class (a collapse anywhere outside $\{0,1\}$; a pair-preserving injection by sending a fresh point to a value outside its range), so no singleton is finitely pinned, and every nonempty proposition pinned down by $S$ is split by the value of its arrows at a point outside $S$.

*By Claude Opus 5.5 (Anthropic), 2026-10-07.*

### Holds Axiom of Infinity (type t).

The propositions that a given number is fixed by the arrow, one for each number, are pairwise distinct and each has that number as finite support, so there are infinitely many propositions. The set of numerals at type $t$ is invariant under every arrow, hence has empty support and lies in the domain, so finite cardinality is standard and no finite cardinality holds of the universal property.

*From the group *Finite-support action models on one object*, shared argument `finite-support-one-object#axiom-of-infinity-t`. By Claude Fable 5.1 (Anthropic), at Cian Dorr's direction, 2026-09-20.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The type-$t$ half of the old argument, "individual" becoming "number", so that it covers the one-individual variants.

### Fails Boolean Completeness (type t).

The source (n. 92) conjectures this but does not show it. Any set $F$ of propositions is the extension at the identity of an element of the domain at type $t\to t$, namely the profile $\langle h,p\rangle\mapsto\{i : i\cdot p\in F\}$: it is natural, independent of $h$ and so pinned down by the empty set, and each of its values is pinned down by the pinning set of $p$, since $i\cdot p$ depends only on the values of $i$ there. A least upper bound of $F$ under entailment is a least finitely pinned superset of $\bigcup F$, and it exists only if the least $S$-pinned superset of $\bigcup F$ stops shrinking as the finite set $S$ grows. So the family $F$ of the condition has no least upper bound, and, taking pointwise negations, the family of complements has no greatest lower bound.

*From the group *Finite-support action models on one object*, shared argument `finite-support-one-object#boolean-completeness-t`. It requires that Some family $F$ of propositions has no least finitely pinned superset of its union $\bigcup F$. Here: As for the permutations, with $2$ in place of $0$: let $F$ be the family of propositions $\{h : h2=m,\ hm=2\}$ ($m\ge3$), each pinned down by $\{2,m\}$. A pair-preserving injection $h$ belongs to the least superset of $\bigcup F$ pinned down by $S=\{0,\ldots,N\}$ iff either $h2\in S\setminus\{0,1,2\}$ and $h(h2)=2$, or $h2\notin S$ and $2\notin h(S)$; the $3$-cycle $(2\ N{+}1\ N{+}2)$, which fixes $0$ and $1$, satisfies the second clause for $S$ but neither for $\{0,\ldots,N+1\}$, so these supersets strictly shrink. By Claude Fable 5.1 (Anthropic), 2026-09-25.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The seven members' copies stated once, each member's family moved to the condition no-least-pinned-cover; the truncations' separate argument of 23 September, by Claude Fable 5.1 prompted by Cian Dorr, is now its witness, its own proof that the family is in the domain giving way to the profile above. The trawl's second arguments for the same verdict (25 September, DeepSeek, reviewed by OpenAI Codex) were dropped.

### Holds Axiom of Infinity (type t), Infinity Schema (type t).

As for individuals (the argument infinitely-many-individuals), at type $t$: the Infinity schema holds, and by extensional fullness the property of cardinalities that hold only of properties with finite extensions is in the domain, has every finite cardinality, and excludes those holding of the universal property of propositions, whose extension is infinite.

*General argument `arguments/infinitely-many-propositions`. It requires that The model is extensionally full at every object: every set of tuples from the domains at an object is the extension, at the identity arrow, of an element of the domain of the matching relational type there. Here: The model is ideally full, hence extensionally full at every object (Appendix D, the remark after Definition D.3): for any set $R$ of tuples from the domains at an object $V$, the intension that assigns to every arrow out of $V$ into an object $U$ a fixed set $R_U$ of tuples from $U$’s domains, with $R_V=R$, is pinned down by $\emptyset$, so it is the intension of an element of $V^{\bar\sigma\to t}$ with extension $R$ at $1_V$. It requires that There are infinitely many propositions at the evaluation world. Here: The propositions that a given number is fixed by the arrow, one for each number, are pairwise distinct, each pinned down by that number (the shared argument axiom-of-infinity-t). By Claude Opus 5.5 (Anthropic), at Cian Dorr's direction, 2026-10-06.*

### Holds □Intensional Choice.

For each object $U$ and type $\sigma$ fix a well-ordering $<_U$ of the domain $D^\sigma_U$, and let $W$ be the intension of type $\sigma\to\sigma\to t$ with $W(h):={<_{\operatorname{cod}h}}$. Its value depends only on the arrow's codomain, so by the condition it is in the domain, and at every world its extension well-orders that world's type-$\sigma$ domain. Given $F$ with $\Box\exists x\, .\,Fx$, put $G:=\lambda x\, .\,Fx\land\forall y\, .\,(Fy\to\neg Wyx)$, the $W$-least $F$. It is definable from $F$ and $W$, so in the domain; $G\le F$, and its extension at every arrow is the singleton of the least element of $F$'s. So Intensional Choice holds, and the same at every reachable object gives $\Box$Intensional Choice. Cian Dorr's observation that such models are qualitatively full, made precise.

*General argument `arguments/intensional-choice-well-ordering`. It requires that At every object reachable from the evaluation point, the domain contains every intension whose value at an arrow depends only on the arrow's codomain. Here: With one object such an intension is constant, so it is pinned down by $\emptyset$, and the domain holds every finitely pinned intension. By Claude Fable 5.1 (Anthropic), at Cian Dorr's suggestion, 2026-10-03.*

### Holds No Pure Contingency.

Closed pure terms denote entities fixed by every arrow (§3.5, p. 58). With a single object, a proposition fixed by every arrow contains every arrow if it contains the identity and no arrow otherwise, so a true closed pure sentence is necessary: the source's one-object No Pure Contingency observation (p. 79), applied to each closed instance.

*Source: Classicism, §3.5, p. 58; p. 79. General argument `arguments/no-pure-contingency-one-object`. It requires that The model is an action model (Classicism, Appendix D), or an intensional action model in the sense of Dorr's draft (Boolean Completeness does not imply Rigid Comprehension), with a single object. Here: Each part of Proposition D.5 is a one-object category acting on $\mathbb N$ (Appendix D, Definitions D.1–D.3). By Andrew Bacon and Cian Dorr, 2026-09-17.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic, for every one-object action model; the reason the source's observation holds is spelled out in place of "Boxed positive flags use the source’s explicit one-object No Pure Contingency observation, applied separately to each closed instance."

### Fails Axiom of Infinity (type e), Infinity Schema (type e), Possible Infinity (type e).

No two individuals are distinct, and the numeral $\operatorname{Suc}_e\mathbf{0}_e$ holds of the universal property at type $e$ at every world.

*General argument `arguments/one-individual`. It requires that There is exactly one individual, at every world. Here: The only individual is fixed by every arrow, at the sole object. By Claude Opus 5.5 (Anthropic), at Cian Dorr's direction, 2026-10-02.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic.

### Fails Witnessed Possibility, Separated Structure, Independence (signature Σ), Distinctness Maximalism (signature Σ).

Let $c\in\Sigma$ have relational type $\tau$, so $c=\top_\tau$ necessarily. Witnessed Possibility fails for the pure formula $x\ne\top_\tau$, witnessed by $\bot_\tau$ but impossible of $c$; Separated Structure fails since $\lambda x\, .\,x$ and $\lambda x\, .\,\top_\tau$ agree on $c$ and differ; Independence (signature Σ) fails since $c$ denotes what the closed pure term $\top_\tau$ denotes; Distinctness Maximalism (signature Σ) fails since $c=\top_\tau$ is a true identity that C(Σ) does not prove.

*General argument `arguments/sigma-top`. It requires that Every constant of Σ is relational, and each denotes the top element of its type. Here: This is the interpretation. By Claude Fable 5.1 (Anthropic), at Cian Dorr’s request, 2026-09-22.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic; it uses nothing about the model.

### Holds Countable Boolean Completeness.

The natural numbers are the finite cardinalities at type $e$ (Background, after Goodsell), and with a single individual there are three: $\mathbf{0}_e$, true of the empty property; $\operatorname{Suc}_e\mathbf{0}_e$, true of the universal one; and the empty cardinality, which is $\operatorname{Suc}_e$ of the second and of itself. By extensional fullness the property of being one of these three is in the domain, so it bounds natural numberhood. A countable property therefore has at most three members in its extension, and their join is its least upper bound.

*General argument `arguments/three-numbers`. It requires that There is exactly one individual, at every world. Here: The only individual is fixed by every arrow, at the sole object. It requires that The model is extensionally full at every object: every set of tuples from the domains at an object is the extension, at the identity arrow, of an element of the domain of the matching relational type there. Here: The model is ideally full, hence extensionally full at every object (Appendix D, the remark after Definition D.3): for any set $R$ of tuples from the domains at an object $V$, the intension that assigns to every arrow out of $V$ into an object $U$ a fixed set $R_U$ of tuples from $U$’s domains, with $R_V=R$, is pinned down by $\emptyset$, so it is the intension of an element of $V^{\bar\sigma\to t}$ with extension $R$ at $1_V$. By Claude Opus 5.5 (Anthropic), on Cian Dorr's question whether the failure of Boolean Completeness at type $t$ refutes its countable form here, 2026-10-02.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic.

### Holds Transversal Choice.

For an equivalence relation at the evaluation point, a transversal of its extension there, chosen in the metatheory, is by extensional fullness the extension of an element of the domain; the equivalence and transversal conditions are unboxed.

*General argument `arguments/transversal-choice-extensionally-full`. It requires that The model is extensionally full at every object: every set of tuples from the domains at an object is the extension, at the identity arrow, of an element of the domain of the matching relational type there. Here: The model is ideally full, hence extensionally full at every object (Appendix D, the remark after Definition D.3): for any set $R$ of tuples from the domains at an object $V$, the intension that assigns to every arrow out of $V$ into an object $U$ a fixed set $R_U$ of tuples from $U$’s domains, with $R_V=R$, is pinned down by $\emptyset$, so it is the intension of an element of $V^{\bar\sigma\to t}$ with extension $R$ at $1_V$. By Cian Dorr (observation); recorded by Claude Fable 5.1 (Anthropic), on a question of Zachary Goodsell, after an observation of Christopher Sun, 2026-09-25.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The Relational Choice and Transversal Choice arguments merged into one, stated for every extensionally full model.

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic. Its first sentence, deriving extensional fullness from ideal fullness, is now the group's reason for meeting extensionally-full.

### Holds No Contingency (signature Σ), B for sentences of Σ.

Each constant of Σ denotes what the closed pure term $\top_\tau$ of its type denotes, so a closed sentence of the language of Σ denotes what the pure sentence with $\top_\tau$ in place of each constant denotes; if true it is necessary by No Pure Contingency, which holds here. So No Contingency (signature Σ) holds, and B for sentences of Σ with it: a true Σ-sentence is necessary, hence necessarily possible.

*General argument `arguments/sigma-top-npc`. It requires that Every constant of Σ is relational, and each denotes the top element of its type. Here: This is the interpretation. By Cian Dorr (observation); recorded by Claude Opus 5.5 (Anthropic), 2026-10-02.*

*Revised 2026-10-03 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* The argument sigma-single-top, for Σ a single constant of type $t$ denoting $\top$, stated for every interpretation of Σ by top elements, now that such interpretations have no individual constants. It replaces that argument and nc-sigma-homogeneous, which reached the same verdicts through an individual constant when the model's automorphisms carry every individual to every other. With an individual constant and no such automorphisms the verdicts were unknown in 19 models, and nowhere did the individual constants settle a verdict differently.


## Notes

Cian Dorr proposed the functions that are injective or identify $0$ with $1$; that set is not closed under composition (the injection swapping $0$ with $2$ and $1$ with $3$, followed by the collapse of $0$ with $1$, identifies $2$ with $3$ but not $0$ with $1$), and the monoid recorded is its largest submonoid containing all the collapses, since a collapse applied after an injection $f$ must identify $f0$ with $f1$. It is the first model on the map with Vicinity without Actuality outside C5 (ND fails at type $e$ by a collapse, at type $t$ for the proposition $0\ne1$, which is impossible at a collapse, refuting 5 and B as well), and the first model refuting Rigid Power. Tame Rigidity holds at type $e$: the weakly rigid properties of individuals are the finite disjunctions of haecceities $k\mapsto k[E]$, the properties $Y_F$ ($\mathbb N\setminus k[F]$ at a pair-preserving injection $k$, $\mathbb N$ at a collapse) for finite $F$, and $\top=Y_\emptyset$, all rigid; at higher types it is open.

## Sources

- **Dorr 7 Oct** — Cian Dorr, suggestion of 7 October 2026, in conversation with Claude Opus 5.5 (Anthropic): the monoid of the functions on $\mathbb N$ that are injective or identify $0$ with $1$, for a model with Vicinity but not Actuality outside C5. As stated the set is not closed under composition; the monoid here is its largest submonoid containing every function that identifies $0$ with $1$. Transcript in .private.
- **Classicism** — Andrew Bacon and Cian Dorr, Classicism, draft of 16 May 2023, Appendix D, Definitions D.1–D.3, pp. 73–74 (the ideally full construction).

<p class='cert'>Record: <code>topics/classicism/models/finite-support-pair-injections-or-collapses.yaml</code></p>

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — Appendix D, Definitions D.1–D.3 and Proposition D.5, pp. 73–79. The finite-support construction, here over a new monoid; the analogue in this setting of Dorr's Base 2 (symmetric-collapse-pair) without the symmetry condition.
