# Rigid Comprehension and Rigid Rigidity with an atomless propositional interval

The root satisfies necessary Rigid Comprehension, both necessary rigid powers and both necessary rigidity principles. Its propositions contain a nonzero interval without atoms. The example uses a complete Boolean algebra and a fixed finite terminal hierarchy. Work in ZFC.

## The root and its terminals

Take the complete Boolean algebra $B=\mathcal P(\omega)\times\operatorname{RO}(2^\omega)$, where the second factor consists of the regular open sets of Cantor space. Let $X$ be its Stone space. The closure of every open set in $X$ is clopen. Indeed, write the open as a union of basic clopens $[b_i]$; the least clopen covering them is $[\bigvee_i b_i]$, and every basic neighborhood inside the latter meets their union.

There is one root $r$, one classical terminal at each $x\in X$, one arrow $h_x$ to that terminal and only the identity arrows otherwise. All individuals belong to a singleton. Write $F$ for the common full one-world hierarchy over this singleton. Every $F_\sigma$ is finite. At relational type $\tau=\bar\sigma t$ a root entity consists of an arbitrary current subset of $D_{\bar\sigma}(r)$ and a locally constant map $X\to F_\tau$. The entrance $h_x$ evaluates that map at $x$. Interpret a single nonlogical propositional constant by a proposition with a leaf value outside the countable list of pure propositional denotations. There are continuum many choices in the first factor of $B$ alone. This does not affect the pure-language arguments.

At a terminal every term is computed in $F$. The terminal denotation of a lambda, including its whole row on all bound tuples, is determined by the transported values of its finitely many free parameters. It is locally constant because these parameters are, also when the body has quantified variables. Arbitrary root rows supply the current part. A difference of whole entities appears either in a current row or in the row at some terminal. These facts give the term closure and extensional identity conditions for an action model. Every typed value at a terminal has a root lift by a constant terminal section, so Barcan holds at all types at every point.

## The least rigid relation with a given current row

For a set $E$ of current tuples and a terminal tuple $b\in F_{\bar\sigma}$, put

$$ O_b(E)=\bigcup_{a\in E}\{x\in X:h_xa=b\}. $$

This set is open. Define $R_E$ to have current row $E$ and to contain $b$ at terminal $x$ exactly if $x\in\overline{O_b(E)}$. Each of these fibres is clopen. There are only finitely many tuples $b$, so the entire terminal section is locally constant. The definition includes propositions, with the empty argument tuple.

The relation $R_E$ is persistent. A tester holding necessarily of every member of $E$ has a closed $b$-fibre containing $O_b(E)$ and therefore contains its closure. Thus $R_E$ is weakly inextensible at the root. At the one-world terminals every relation is rigid, giving rigidity at the root. Conversely, any weakly rigid root relation with current row $E$ contains $R_E$ by persistence and closedness of its fibres, and is contained in $R_E$ by weak inextensibility against that tester. Thus $R_E$ is its unique weakly rigid coextension. Rigid Comprehension and Tame Rigidity hold necessarily.

Each subset $D$ of a terminal tuple domain is the terminal extension, simultaneously at every leaf, of a rigid root relation. For each $b\in D$ choose a root tuple with constant leaf value $b$ and form $R_E$ from these tuples. This lifts every member of the rigidity and weak-rigidity predicates at the terminals. The predicates are persistent, since all terminal entities are rigid, and their weak inextensibility follows by applying any tester at those lifts. Both rigidity principles hold necessarily.

## Rigid powers and Boolean completeness

Let $F=R_E$ and consider either power of $F$. Its root members are rigid subrelations of $F$, by the preceding characterization. Their membership persists at the terminals. Suppose a root tester necessarily accepts every one of them, and that $D\subseteq F_x$ is a terminal subrelation at $x$. For each of the finitely many $b\in D$, $O_b(E)$ is open dense in its clopen closure. Consequently, on an open dense subset of the neighborhood

$$ C_D=\bigcap_{b\in D}\overline{O_b(E)} $$

every $b\in D$ is the image of some member of $E$ there. More explicitly, $C_D\cap\bigcap_{b\in D}O_b(E)$ is dense in $C_D$. At any such point choose one old member for each $b$. The finite union of their tuple haecceities is a rigid subrelation of $F$ with terminal row exactly $D$ there. If $D$ is empty take bottom. The tester's $D$-fibre is clopen, so it contains $C_D$ and in particular $x$. This is weak inextensibility for each power. The terminals establish the hereditary assertions, giving both necessary powers.

At each root relational type the order on whole entities is the product of the powerset of the current tuple carrier with one copy of $B$ for each terminal tuple. Thus all its joins exist, even for arbitrary external families. The terminals are finite powersets. Boolean Completeness holds necessarily at every type.

## Atoms, choice and the inexact ordinals

The proposition algebra at the root is $\mathbf2\times B$. The interval confined to the regular open factor is nonzero and atomless. At every relational type an atom is a singleton tuple in the current factor, or a single terminal tuple over an isolated point of $X$. Such an atom goes to bottom or an atom at each proper target. The current-only truth is a true strong atom. Every nonzero relation contains a self-atom: use an occupied current singleton if available, and otherwise a single terminal tuple restricted to its nonempty clopen fibre, with empty current row. This latter relation is an atom wherever instantiated. A nonempty leaf-only proposition supported on the atomless factor is itself a self-atom which splits into two nonzero propositions at the root.

A chosen root well-order and a constant terminal well-order on each type form one necessarily well-ordering relation. The current-only truth witnesses ND-necessity of every actual truth because no proper continuation sees that current-only proposition. The root itself fails pure B: the pure sentence asserting that some true proposition can become false is true at the root and impossible at each terminal.

For the inexact ordinal benchmark over $e$, take the finite set $Z$ of ordinal-type entities that use an extensional truth table on the present order and field bits at the singleton root and another common table at all singleton terminals. Zero and successor preserve these tests by the definitions of well-order and strict initial segment. A rigid family with current members in $Z$ has finite current row, and is the finite union of their haecceities by persistence and weak inextensibility. The limit constructor therefore uses the same finite family of terminal tables at every leaf and stays in $Z$. This bounds the benchmark by a finite set. Any infinite current carrier contains a countably infinite power-closed subset above this benchmark: its strictly smaller subsets are finite and their finite powers can be coded in finite subsets by arbitrary current graphs. Every revised-small complete Boolean algebra is therefore finite. An algebra with $k$ atoms is represented below the proposition supported on any $k$ distinct isolated points from the $\mathcal P(\omega)$ factor, with its isomorphism supplied by current fullness. The trivial algebra uses bottom.

There are infinitely many current propositions and only two at each terminal. Full current tests restrict the root numbers at $t$ to standard numeral denotations and every finite target set fails the Peano guard. At every type admitting a real number structure in this cone, that structure must occur at the root; full current tests give the ordinary numbers and all sets of them, and admit all higher relations on these codes. Thus the sentence-level necessities of arithmetic and second-order analysis hold. Analytic Necessitism fails at type $t$. The root has continuum many propositions on which to place a full current real structure, but the two terminal propositions cannot carry one. The individual domain is a singleton throughout. The sole nonlogical name avoids all pure denotations; Witnessed Possibility nevertheless fails by the pure one-argument condition that the argument equal top and the Fregean axiom fail, which can hold only at the root.

Ordinary mathematical construction by OpenAI Codex (GPT-6), prompted by Daniel Kodsi, 27 November 2026. Two other GPT-6 agents independently checked the rigidification and finite-intersection arguments.
