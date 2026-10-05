# Action model: a fork with an ultralimit world

<p class='cert'>Model — Source: Misc.; produced by Branden Fitelson, with Claude (Anthropic) and GPT-6 Astra (OpenAI), equally involved, construction and Isabelle/HOL verification, 1 October 2026; Cian Dorr, with Claude Opus 5.5 (Anthropic), the presentation as an intensional action model, 1 October 2026; recorded by Claude Opus 5.5 (Anthropic), 1 October 2026.</p>

## Package

- **□Atomicity.** Necessarily, every non-bottom entity of each relational type has an atom below it.
- **□Boolean Completeness.** Necessarily, every property of entities of a relational type has a greatest lower bound in that type.
- **□BF.** Necessarily, the Barcan Formula holds at every type. The predicate formulation closes the formula schema using lambda abstraction.
- **□Actuality.** Necessarily, there is a true proposition that entails every true proposition.
- **¬ Rigid Comprehension.** Every relation, including a proposition, is coextensive with a rigid one.
- **¬ Witnessed Possibility.** For pure-formulas P with free variables among a finite tuple x, and distinct matching nonlogical constants c, a witness to P entails that P at those constants is possible.
- **¬ Independence (signature Σ).** No constant of Sigma is a pure operation applied to other constants: for a closed pure term A and distinct constants c, d_1,…,d_n with n ≥ 0, c differs from A applied to the d’s. With n = 0, no constant denotes a pure entity.
- **¬ Separated Structure.** For each typed nonlogical constant c and closed same-typed terms F,G not containing c, equality after application to c implies equality of F and G.
- **¬ Distinctness Maximalism (signature Σ).** The Distinctness Maximalism schema for the fixed nonlogical signature Sigma.

## Definition

An intensional action model with one individual. The objects are the root $o$, $s$, $u$, and $n$ for each $n\ge1$; besides identities the arrows are $h_s\colon o\to s$, $j\colon s\to u$, $h_u:=j\circ h_s$ and $h_n\colon o\to n$, so the root reaches each object by exactly one arrow and worlds may be identified with objects. The domains at $s$, $u$ and each $n$ are full. Identify the domains at the terminal objects $u$ and $n$ with one finite full type structure $M$ over one individual. Fix a non-principal ultrafilter $\mathcal U$ on the positive integers. At the root, an element of a relational type is any element of the full intension space whose extension at $u$ is the $\mathcal U$-limit of its extensions at the worlds $n$; its extensions at $o$, at $s$ and at each $n$ are unconstrained. So a root proposition is any choice of truth values at $o$, $s$ and the $n$s, with its value at $u$ fixed as the limit. Evaluation point: the root. Interpretation of Σ, fixed for this record: each relational constant denotes the top element of its type and each individual constant the individual.

## Arguments

### Holds □Atomicity, □Boolean Completeness.

At the root, the map sending an element to its extensions at $o$, $s$ and the $n$s is an order isomorphism onto a product of powerset algebras, the extension at $u$ being recomputed as the limit. So every family has a meet and a join, computed coordinatewise except at $u$, and every nonzero element lies above an atom with one tuple in one free coordinate. The other worlds carry finite full powerset algebras. Hence Boolean Completeness and Atomicity hold at every world and every relational type.

*By Branden Fitelson, with Claude (Anthropic) and GPT-6 Astra (OpenAI), equally involved, construction and Isabelle/HOL verification, 1 October 2026; Cian Dorr, with Claude Opus 5.5 (Anthropic), the presentation as an intensional action model, 1 October 2026.*

### Holds □BF.

Every arrow acts surjectively at every type, so BF holds at every world (write-up, Proposition 4).

*By Branden Fitelson, with Claude (Anthropic) and GPT-6 Astra (OpenAI), equally involved, construction and Isabelle/HOL verification, 1 October 2026; Cian Dorr, with Claude Opus 5.5 (Anthropic), the presentation as an intensional action model, 1 October 2026.*

### Fails Rigid Comprehension.

At type $t\to t$ (write-up, Theorem 6). Let $A_0$ be the root propositions false at $s$ and at $u$, and $X$ the property with extension $A_0$ at the root and empty extensions elsewhere. A persistent property coextensive with $X$ contains both truth values at every world $n$, since members of $A_0$ take both values there; the limit condition then puts the true proposition in its extension at $u$. Rigidity at the root forces its extension at $s$ to be the proposition false at $s$ and $u$, and rigidity at $s$, tested against that proposition's haecceity, forbids the true proposition at $u$. The least upper bound of the haecceities of the $X$s, the candidate rigid coextension in the proof of Proposition 2.11, is weakly rigid but fails the rigidity condition at $s$. The model therefore refutes Proposition 2.11 (necessary-atomicity-completeness-bf-imply-rigid-comprehension); the gap is the normalization step of n. 42, part (iv), which the write-up runs inside the model (§5).

*By Branden Fitelson, with Claude (Anthropic) and GPT-6 Astra (OpenAI), equally involved, construction and Isabelle/HOL verification, 1 October 2026; Cian Dorr, with Claude Opus 5.5 (Anthropic), the presentation as an intensional action model, 1 October 2026.*

### Fails Witnessed Possibility, Independence (signature Σ).

Let $c\in\Sigma$ have relational type $\tau$, so $c=\top_\tau$ necessarily. Witnessed Possibility fails for the pure formula $x\ne\top_\tau$, witnessed by $\bot_\tau$ but impossible of $c$; Separated Structure fails since $\lambda x\, .\,x$ and $\lambda x\, .\,\top_\tau$ agree on $c$ and differ; Independence (signature Σ) fails since $c$ denotes what the closed pure term $\top_\tau$ denotes; Distinctness Maximalism (signature Σ) fails since $c=\top_\tau$ is a true identity that C(Σ) does not prove. Everything that implies these fails with them.

*Address: `ultralimit-fork#sigma-top`. By Branden Fitelson, with Claude (Anthropic) and GPT-6 Astra (OpenAI), equally involved, construction and Isabelle/HOL verification, 1 October 2026; Cian Dorr, with Claude Opus 5.5 (Anthropic), the presentation as an intensional action model, 1 October 2026.*

### Holds □Actuality. Fails Separated Structure, Distinctness Maximalism (signature Σ). In reserve.

*Source: A counterexample to Proposition 2.11 of 'Classicism', §§2–4. By Branden Fitelson, with Claude (Anthropic) and GPT-6 Astra (OpenAI), equally involved, construction and Isabelle/HOL verification, 1 October 2026; Cian Dorr, with Claude Opus 5.5 (Anthropic), the presentation as an intensional action model, 1 October 2026.*


## Notes

It is a model: the limit condition commutes with every finite operation, so every term denotes in the domains (write-up, Lemma 2).
Actuality holds at every world: at the root the proposition true at $o$ alone is a true atom.
Under the interpretation of Σ, the signature schemata fail.

## Sources

- **Fitelson 1 Oct** — Branden Fitelson, with Claude (Anthropic) and GPT-6 Astra (OpenAI), A proposed counterexample to Proposition 2.11, note communicated to Cian Dorr, 1 October 2026; Isabelle/HOL verification at github.com/fitelson/hom-isabelle, commit 4042cc0, Applications/2.11.
- **Intensional write-up 1 Oct** — Cian Dorr, with Claude Opus 5.5 (Anthropic), A counterexample to Proposition 2.11 of 'Classicism': Fitelson's model, as an intensional action model, draft of 1 October 2026, sources/prop-2-11-counterexample.pdf.

<p class='cert'>Record: <code>topics/classicism/models/ultralimit-fork.yaml</code></p>

## Paper references

- **Proof: [A counterexample to Proposition 2.11 of 'Classicism'](https://github.com/zwlgzwlg/Logical-Maps/blob/main/logical-maps/topics/classicism/sources/prop-2-11-counterexample.pdf).** Cian Dorr, with Claude Opus 5.5 (Anthropic). A counterexample to Proposition 2.11 of 'Classicism': Fitelson's model, as an intensional action model. Draft of 1 October 2026, reworking a construction by Branden Fitelson, with Claude (Anthropic) and GPT-6 Astra (OpenAI). — §§2–4
- **Proof: [Proposition 2.11 refuted (Isabelle/HOL)](https://github.com/fitelson/hom-isabelle/tree/4042cc0/Applications/2.11).** Branden Fitelson, with Claude (Anthropic) and GPT-6 Astra (OpenAI). Isabelle/HOL verification that Rigid Comprehension for properties of propositions is not derivable from Classicism with □Atomicity, Boolean Completeness and BF; theorem proposition_2_11_refuted. Commit 4042cc0, 1 October 2026. — theorem proposition_2_11_refuted. Verifies the failure of Rigid Comprehension under the hypotheses; the boxed forms of Boolean Completeness and BF are not formalized there.
- **Background: Boolean Completeness does not imply Rigid Comprehension.** Dorr, Cian. Boolean Completeness does not imply Rigid Comprehension. Unpublished draft in progress, 30 July 2026, 27 pages. All page, proposition and lemma locators for this source refer to that draft. Parts of the draft were drafted with AI assistance; its mathematical claims are attributed to the author. — §2. Definitions of intensional action models and the rigidity criterion used in the verification.
- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — Proposition 2.11 and n. 42. The proposition this model refutes.
