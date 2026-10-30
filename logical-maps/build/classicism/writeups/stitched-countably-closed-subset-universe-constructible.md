# Stitched forcing model: countably closed subset forcing [over L]

<p class='cert'>Model — Source: Misc.; produced by GPT-6 Astra, prompted by Daniel Kodsi; recorded by OpenAI Codex, prompted by Daniel Kodsi.</p>

## Package

- **Analytic Necessitism.** If there could be a real number structure, there is a rigid one that is necessarily a real number structure: a rigid property with necessarily distinct instances, with rigid order, addition, multiplication and natural numbers, which necessarily form a complete ordered field. One sentence for each type $\sigma$.
- **□Atoms are self-atoms.** Necessarily, at each relational type, every atom is a self-atom: necessarily, if it is instantiated, it is an atom.
- **□Atoms are strong atoms.** Necessarily, at each relational type, every atom is a strong atom: it necessarily entails every entity of the type or its negation.
- **□Self-atoms are atoms.** Necessarily, at each relational type, every self-atom is an atom.
- **□Self-atoms are strong atoms.** Necessarily, at each relational type, every self-atom is a strong atom: it necessarily entails every entity of the type or its negation.
- **□Rigid Comprehension.** Necessarily, every relation, including a proposition, is coextensive with a rigid one.
- **□Relational Choice.** Necessarily, every serial binary relation has a functional subrelation.
- **Axiom of Infinity (type e).** There are not finitely many individuals. No finite cardinality holds of the universal property, so the domain of the type cannot be exhausted by finitely many steps from the empty property.
- **□Atomicity (type t).** Necessarily, every non-bottom proposition has an atom below it.
- **□BF (type t).** Necessarily, if every proposition necessarily has a property, then necessarily every proposition has it.
- **□Truths are ND-necessary.** Necessarily, every truth is ND-necessary. In C this is the identity $\Box_{\ne}=\lambda p\, .\,p$.
- **¬ Infinity Schema (type t).** There are arbitrarily many pairwise distinct entities of this fixed type; one sentence for each positive integer n.
- **¬ B for pure sentences.** The B instance for every closed sentence in the pure language.
- **¬ Possible Infinity (type t).** Possibly there are not finitely many propositions: the Axiom of Infinity at this type, under a diamond.
- **¬ Witnessed Possibility.** For pure-formulas P with free variables among a finite tuple x, and distinct matching nonlogical constants c, a witness to P entails that P at those constants is possible.
- **¬ Separated Structure.** For each typed nonlogical constant c and closed same-typed terms F,G not containing c, equality after application to c implies equality of F and G.
- **¬ Independence (signature Σ).** No constant of Sigma is a pure operation applied to other constants: for a closed pure term A and distinct constants c, d_1,…,d_n with n ≥ 0, c differs from A applied to the d’s. With n = 0, no constant denotes a pure entity.
- **¬ Maximalism (signature Σ).** The Maximalism schema for the fixed nonlogical signature Σ: every closed identity of its language not provable in C(Σ) is false.

## Definition

The stitching construction of Barton and Goodsell (Continuum Contingency, §8). Work in a generic extension $V[G]$ of a ground model $V$ of ZFC by a weakly homogeneous, hence $V$-decisive, forcing $P$ (§7.1): a set of ordinals definable in $V[G]$ from parameters in $V$ lies in $V$.

Here $P=\operatorname{Fn}((\omega_1)^V,2,{<}(\omega_1)^V)$ is the set in $V$ of countable partial functions from $(\omega_1)^V$ to $2$, ordered by reverse inclusion. It is countably closed and weakly homogeneous. It adds a subset of $(\omega_1)^V$ but no subsets of $\omega$. Use the group's ground-model root, full extensional terminal object, and ground-definable transport; the truth point is the root.

Ground model, fixed for this record: $V$ is Gödel's constructible universe, so that $V[G]=L[G]$; that is, the construction is carried out over $L$, which ZFC proves to be a model of ZFC + $V=L$, so this adds nothing to what the construction presupposes. In particular $V\models\mathrm{CH}$.

Let $C_0$ be the canonical extensional model of $V[G]$ (§7.2.5): one object with its identity arrow, the natural numbers as individuals, two propositions, and at each relational type every function of $V[G]$ between the lower domains, so that its relations of a type are, up to extension, all the subsets in $V[G]$ of the tuples of that type. Call an element of $C_0$ definable when it is definable in $V[G]$ from parameters in $V$. The root $\hat M$ is built in $V$ (§8.3, Definition 1, with the group $W$ trivial): its individuals are the natural numbers; its propositions are the pairs $\langle a,b\rangle$ of a truth value $a$ at the root and a truth value $b$ at $C_0$; and an element of a relational type at the root is a pair of a function in $V$ on the root domains, which gives its extension at the root, and a definable element of $C_0$ of the same type, which gives its extension at $C_0$, the two compatible in that the $C_0$-coordinate of the function's value at an argument is the definable element applied to the argument's $C_0$-component. Every such pair is in the domain, so a root relation may be any set in $V$ of root tuples together with any definable relation of $C_0$. The action model $M$ (§8.4) has the two objects $\hat M$ and $C_0$, their identities, and one arrow $h\colon\hat M\to C_0$, the identity on the individuals, which sends every other element to its $C_0$-component. Truth at the root is the first coordinate, so at the root $\Box p$ holds iff $p$ is true at both objects, and $C_0$ sees only itself. The source works in the full simple type hierarchy; the restriction of its model to the map's relational types is an action model of the same kind. Evaluation point: $\hat M$, at its identity arrow.

Interpretation of Σ, fixed for these records: every constant of Σ is relational, and each denotes the top element of its type.

*A member of the group Stitched forcing models, which supplies this definition with the record's settings, and the arguments marked as shared.*

## Arguments

### Holds Analytic Necessitism.

At every infinite relational type a uniformly ground-definable embedding of the ground real field into the terminal domain has a ground-coded family of root lifts. Their carrier and field relations are paired with their exact transported images, so they are rigid and the carrier has necessarily distinct instances. No new subsets of omega means no new rational cuts: the same field is complete at both objects, including for new bounded families at the terminal object. The individual type and the remaining finite types cannot carry a real structure. Thus the same-type ANA schema holds at every type. The writeup gives the type induction and the simultaneous admitted structure.

*Write-up: [stitched-countably-closed-subset](stitched-countably-closed-subset.html). Address: `stitched-countably-closed-subset-universe-constructible#fixed-real-fields-at-every-carrier`. By GPT-6 Astra, prompted by Daniel Kodsi, 2026-10-30.*

### Holds □Atoms are self-atoms, □Atoms are strong atoms, □Self-atoms are atoms, □Self-atoms are strong atoms.

The root sees itself and $C_0$ through one arrow each, and $C_0$ sees only itself. An entity at the root of a relational type is a pair $(E,D)$ of a root extension $E$ and a definable element $D$ of $C_0$, with transport $D$ along the arrow to $C_0$. It is an atom iff $E$ is a singleton and $D=\bot$, or $E=\varnothing$ and $D$ is a definable singleton of $C_0$; a self-atom likewise, since its transport along the identity is itself and along the arrow to $C_0$ is $D$, each of which must be an atom where the entity is instantiated. Each such entity is a strong atom, its two transports being an atom or bottom. At $C_0$, a one-world model with full extensional domains, the atoms are the singletons, which are self-atoms and strong atoms. So all four bridge principles hold at both worlds, at every type.

*From the group *Stitched forcing models*, shared argument `stitched-forcing#self-atoms-and-strong-atoms`. By Claude Fable 5.1 (Anthropic), prompted by Cian Dorr, 25 October 2026.*

### Holds □Rigid Comprehension.

Lemma 16 of the source, in the map's terms. Write a root relation as the pair of its root extension $E$, a set in $V$ of root tuples, and its $C_0$-extension $g$, a definable relation of $C_0$; transport along $h$ sends it to $g$, and $h[E]$, the set of $C_0$-components of the members of $E$, is definable from the set in $V$ of their names. The relation is persistent iff $h[E]\subseteq g$. It is weakly inextensible iff $g\subseteq h[E]$: the root relation with root extension $E$ and $C_0$-extension $h[E]$ necessarily holds of every member of $E$, so weak inextensibility gives $g\subseteq h[E]$; conversely, a root relation that necessarily holds of each member of $E$ has root extension including $E$ and $C_0$-extension including $h[E]$. So a root relation is weakly rigid iff $g=h[E]$, and then rigid, since at $C_0$, which sees only itself, every relation is rigid. Hence $(E,g)$ is coextensive with the rigid $(E,h[E])$, and Rigid Comprehension holds at the root; at $C_0$ it holds trivially.

*Source: Continuum Contingency, Lemma 16. From the group *Stitched forcing models*, shared argument `stitched-forcing#rigid-comprehension`. By Neil Barton and Zachary Goodsell; in the map's terms by Claude Fable 5.1 (Anthropic), prompted by Zachary Goodsell, 2026-10-19.*

### Holds □Relational Choice.

Lemma 17 of the source. A serial root relation $U$ has, by choice in $V$, a functional subrelation $E_S$ of its root extension; the root relation with root extension $E_S$ and the $C_0$-extension of $U$ is in the domain, lies within $U$ at the root and is functional there, which is all the unboxed principle asks. At $C_0$, $V[G]$ supplies a functional subrelation of any serial relation, and the full domain contains it.

*Source: Continuum Contingency, Lemma 17. From the group *Stitched forcing models*, shared argument `stitched-forcing#relational-choice`. By Neil Barton and Zachary Goodsell; in the map's terms by Claude Fable 5.1 (Anthropic), prompted by Zachary Goodsell, 2026-10-19.*

### Holds Axiom of Infinity (type e).

The individuals are the natural numbers at both objects (Lemma 15 of the source). At the root the finite cardinalities of type $(et)t$ are the numerals $\operatorname{Suc}^k\mathbf 0$: the root property of cardinalities whose root extension is the set of numerals, with the corresponding definable property at $C_0$, holds of $\mathbf 0$ and is closed under successor, so every finite cardinality is a numeral; and the $k$-th numeral holds of a root property of individuals iff its root extension has exactly $k$ members, which the universal property has not.

*Source: Continuum Contingency, Lemma 15. From the group *Stitched forcing models*, shared argument `stitched-forcing#axiom-of-infinity-e`. By Neil Barton and Zachary Goodsell; in the map's terms by Claude Fable 5.1 (Anthropic), prompted by Zachary Goodsell, 2026-10-19.*

### Holds □Atomicity (type t).

Theorem 21 of the source, with the trivial group. The root has four propositions, the pairs of a truth value at the root and one at $C_0$, ordered coordinatewise, and $C_0$ has two; both algebras are finite, hence atomic.

*Source: Continuum Contingency, Theorem 21. From the group *Stitched forcing models*, shared argument `stitched-forcing#atomicity-t`. By Neil Barton and Zachary Goodsell; in the map's terms by Claude Fable 5.1 (Anthropic), prompted by Zachary Goodsell, 2026-10-19.*

### Holds □BF (type t).

Both propositions of $C_0$ are transports of root propositions, so a property of propositions at the root that necessarily holds of every root proposition holds at $C_0$ of both propositions there; at $C_0$, which sees only itself, BF is trivial.

*From the group *Stitched forcing models*, shared argument `stitched-forcing#barcan-t`. By Claude Fable 5.1 (Anthropic), prompted by Zachary Goodsell, 2026-10-19.*

### Holds □Truths are ND-necessary.

At the root let $q$ be the proposition true at the root alone. $\Diamond q$ is true at the root and false at $C_0$, so for any truth $p$, $\Box(\Diamond q\to p)$ holds, and $q$ witnesses $\Box_{\ne}p$. At $C_0$, where necessity is truth, $\top$ witnesses $\Box_{\ne}p$ for every truth $p$.

*From the group *Stitched forcing models*, shared argument `stitched-forcing#distinctness-preserving-collapse`. By Claude Fable 5.1 (Anthropic), prompted by Zachary Goodsell, 2026-10-19.*

### Fails Infinity Schema (type t).

The root has four propositions, so the instance of the schema asking for five pairwise distinct ones fails.

*From the group *Stitched forcing models*, shared argument `stitched-forcing#infinity-t`. By Claude Fable 5.1 (Anthropic), prompted by Zachary Goodsell, 2026-10-19.*

### Fails B for pure sentences.

The pure sentence $\exists p_1\ldots p_n\bigwedge_{i<j}p_i\ne p_j$ is true at the evaluation object and false at the world $V$ after it and at every world after $V$; so $\Diamond$ of it is false at $V$, and $\Box\Diamond$ of it false at the evaluation object. (The chain's own argument of 25 September, stated once.)

*General argument `arguments/fewer-propositions-after`. It requires that For some $n$, the evaluation object has $n$ distinct propositions, while some world after it, and every world after that one, has fewer. Here: The root has four propositions; $C_0$, after which there is only itself, has two. By Claude Opus 5.5 (Anthropic), at Cian Dorr's direction, 2026-10-06.*

### Fails Possible Infinity (type t).

At a world with $n$ propositions, the numeral $\operatorname{Suc}^n_t\mathbf{0}_t$, a finite cardinality, holds of the universal property of propositions, so the Axiom of Infinity at type $t$ fails there. It fails at every world, so Possible Infinity at type $t$ fails.

*General argument `arguments/finitely-many-propositions-everywhere`. It requires that There are finitely many propositions at every object reachable from the evaluation point. Here: The root has four propositions and $C_0$ two. By Claude Opus 5.5 (Anthropic), at Cian Dorr's direction, 2026-10-06.*

### Fails Witnessed Possibility, Separated Structure, Independence (signature Σ), Maximalism (signature Σ).

Let $c\in\Sigma$ have relational type $\tau$, so $c=\top_\tau$ necessarily. Witnessed Possibility fails for the pure formula $x\ne\top_\tau$, witnessed by $\bot_\tau$ but impossible of $c$; Separated Structure fails since $\lambda x\, .\,x$ and $\lambda x\, .\,\top_\tau$ agree on $c$ and differ; Independence (signature Σ) fails since $c$ denotes what the closed pure term $\top_\tau$ denotes; Distinctness Maximalism (signature Σ) fails since $c=\top_\tau$ is a true identity that C(Σ) does not prove.

*General argument `arguments/sigma-top`. It requires that Every constant of Σ is relational, and each denotes the top element of its type. Here: This is the interpretation the definition fixes. By Claude Fable 5.1 (Anthropic), at Cian Dorr’s request, 2026-09-22.*

*Revised 2026-10-02 by Claude Opus 5.5 (Anthropic), at Cian Dorr's direction:* Moved from the group finite-support-one-object to the topic; it uses nothing about the model.


## Notes

Relative consistency in the usual ZFC forcing interpretation of the stitching construction. The group's necessary Rigid Comprehension and necessary Relational Choice apply without an adds-a-real hypothesis. This model supplies their joint compatibility with Analytic Necessitism; its fixed real fields actually exist, for example at et. No global ND, CH-stability assertion, or general all-type ANA transfer rule is used. This is distinct from the full Boolean-valued countably-closed-subset construction.

## Sources

- GPT-6 Astra, prompted by Daniel Kodsi, Finite-Type Necessitism and Analytic Non-Contingency, 30 October 2026, §7, A fixed continuum and a changing power, unpaginated.
- Neil Barton and Zachary Goodsell, Continuum Contingency, draft of 14 October 2026, §7.1 and §8, Definition 1 and Lemmas 11–19, for the underlying stitching construction.
- OpenAI Codex, prompted by Daniel Kodsi, Stitched forcing model with countably closed subset forcing, 30 October 2026, §§1–4 (unpaginated), for the explicit type induction, common carrier lifts, and canonical second-power obstruction.

<p class='cert'>Record: <code>topics/classicism/models/stitched-countably-closed-subset.yaml</code></p>

## Paper references

- **Background: Continuum Contingency.** Barton, Neil, and Zachary Goodsell. Continuum Contingency. Draft dated 14 October 2026, 47 pages. Stitches a ground model of set theory to the canonical model of a forcing extension to show that Classicism with □Rigid Comprehension, □Relational Choice and an axiom of infinity is consistent with first- and second-order continuum contingency, together with □Atomicity at type t (Theorem 21) or with Recombination (Theorem 22, which refutes Atomicity at type t, Corollary 23); formalizes the coin-toss argument (Theorem 9). Read directly on 19 October 2026; locators refer to this draft. — §7.1; §8, Definition 1 and Lemmas 11–19
