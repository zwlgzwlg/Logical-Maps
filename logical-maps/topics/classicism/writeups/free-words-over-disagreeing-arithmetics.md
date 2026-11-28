# Free words over disagreeing arithmetics

Possibly Witnessed Possibility holds for every set-sized free signature in
a model where Necessity of Arithmetic fails at the individual type.
Necessary Strong Atomicity, necessary BF, necessary propositional Boolean
Completeness, necessary individual Infinity and Modal Well-Ordering hold
at the same root.

## The interpreting objects

Use the two-component method of Cian Dorr's
[coalesced arithmetics](coalesced-two-extensional-arithmetics-root.html),
with a free-word root as in the
[signature gluing construction](full-free-monoid-glued-constants.html).
Here every word has its own entrances to the components. Work in ZFC.

The first terminal $S$ has the full ordinary type hierarchy on $\mathbb N$.
For the second, choose a countable model $M$ of Zermelo set theory with
Choice and $\neg\operatorname{Con}(\mathrm{ZC})$. Such a model exists:
$V_{\omega+\omega}$ models ZC, which is effectively axiomatized and
interprets arithmetic, so Gödel's second incompleteness theorem gives
consistency of $\mathrm{ZC}+\neg\operatorname{Con}(\mathrm{ZC})$.
Completeness and downward Löwenheim–Skolem give $M$. At the terminal
$H$ use the hierarchy on $\omega^M$ formed inside $M$, using its
products and powersets for every standard finite type. External
satisfaction of each fixed typed formula agrees with satisfaction in
this internal hierarchy by induction on the formula. Separation gives
comprehension. Add the two classical Henkin components $H_+,H_-$ from the
[construction with disagreement on CH](stone-terminals-infinite-individuals.html):
one computes structural CH in its own hierarchy and the other computes
its negation. Their existence in ZFC and their construction from
countable models of ZC are given there. Write $J=\{S,H,H_+,H_-\}$.
Each terminal has only its identity arrow.

At a third object $r$ take a free monoid $W$ on
$\kappa=\max(\aleph_0,|\Sigma|)$ letters. The other arrows are
$h_{i,w}:r\to i$ for each $i\in J$ and each $w\in W$, with
$h_{i,w}u=h_{i,wu}$. A later word is prepended.
The individual sort of $r$ is the product
$I=(\prod_{i\in J}D_{i,e})^W$. Transport along $u$ sends an
array $a$ to the array $w\mapsto a(wu)$, and $h_{i,w}$ reads the
$i$-coordinate of $a(w)$. These maps are surjective.

At a relational type $\tau=\bar\sigma t$, a root entity consists of
an arbitrary row on $D_{r,\bar\sigma}$ for each word $w$, and a whole
entity of $D_{i,\tau}$ at each $h_{i,w}$. All coordinates are
independent. The current extension is the empty word's row.
Transport along $u$ reads rows and coordinates indexed by $wu$.
Transport to a terminal reads its specified coordinate. These
operations respect composition. A difference of source values is
observable at the differing word or terminal coordinate, using
one-world extensionality in each terminal. An abstract at a root word
takes its row from its body with the transported parameters and all
root arguments. At a terminal it takes the terminal denotation on the
transported parameters. All such root rows are admitted and terminal
term closure supplies all the required coordinates. Thus the
interpretation validates C.

## Realizing the signature

A source requirement is a pure matrix, a list of distinct matching
names, and the fact that some tuple realizes it at $r$. For each
such requirement choose one realizing tuple. A terminal requirement
specifies the same information with a witnessing tuple at one of the terminals. There are at most $\kappa$ requirements in total. Assign a
different letter $\alpha$ to each requirement.

For a source requirement, place each individual witness's array on the
suffix $\alpha$ of its matching individual name. Give each matching
relational name the root rows at $w\alpha$ and all terminal coordinates
at $h_{i,w\alpha}$ of its witness at $w$ and $h_{i,w}$, for every $w$.
After $\alpha$ each such constant is exactly its witness as a whole typed
entity. For a terminal requirement at $i$, put the terminal value of each
name into its single $h_{i,\alpha}$ coordinate, including the indicated
entry of an individual array. Distinct final letters keep these
prescriptions disjoint; use arbitrary defaults elsewhere.

Any possible witness to the pure matrix occurs at one of the
objects and hence has one of these requirements. At its chosen
entrance or word the assigned names realize the matrix. This proves
[Possibly Witnessed Possibility](../index.html#principle/possibly-witnessed-possibility-r),
including ordinary Witnessed Possibility.

## Arithmetic and the other principles

At each terminal the finite cardinalities of individual properties are
the cardinalities indexed by its own natural numbers. For each internal
$n$ the cardinality exists by separation and is distinguished by a
set of size $n$. The property consisting of these cardinalities is
inductive and available in that hierarchy. Conversely internal
induction shows that each lies in every inductive property. The Frege
arithmetic operations therefore compute the terminal's ordinary
arithmetic, and $I_e^*$ holds. Thus the arithmetical sentence
$\operatorname{Con}(\mathrm{ZC})$ holds at $S$ and fails at $H$.
The two terminal witnesses refute both alternatives in the root's
[Necessity of Arithmetic](../index.html#principle/necessity-of-arithmetic)
instance.

The same disagreement refutes first-order
[Necessity of Analysis](../index.html#principle/necessity-of-analysis) at
type $et$. In each terminal the individual powerset carries its internal
real number structure: take the singleton subsets as its numbers, all
subsets as reals, and use membership of the corresponding individual.
An internally available property of numbers corresponds to exactly one
subset, by separation. The first-order analytical sentence expressing
the same arithmetical consistency claim in the number sort differs
between these structures. The real structures at the same type in $H_+$
and $H_-$ disagree on CH; this refutes Non-contingency of CH.

At the root one can take a predicate of cardinalities with actual row
consisting exactly of the externally standard Frege numerals, since all
root rows are admitted. Its row contains zero and is closed under successor,
so every root finite cardinality equals a standard numeral. By external
finite induction the $n$th numeral holds of exactly those current properties
having $n$ instances. As $I$ is infinite, none counts the universal
property. The terminals satisfy the same axiom by their internal
arithmetic, yielding necessary Axiom of Infinity at $e$.

The Peano antecedent $\Box I_e^*$ holds, by the same numeral
calculation at the root and the internal arithmetic at the terminals.
Root numbers are standard numeral entities. Their $H$-images omit
each nonstandard number of $M$. A tester excluding one such entity at
$h_{H,\varepsilon}$ and nowhere else witnesses that $\mathbb N_e$
fails weak inextensibility. Thus Arithmetic Necessitism fails at $e$.
The same current cut proves the Axiom of Infinity at $t$ locally,
since there are infinitely many propositions supported on distinct
words. Potential Infinity at $t$ fails in each terminal, whose only
two propositions cannot supply arbitrarily many distinct values.

Every outgoing arrow is surjective on each type. A root-word map lifts a
higher-type target by writing its entire family on the corresponding
word suffix. A terminal entrance lifts a value by placing it in that
coordinate. At individuals, extend the requested suffix or single product entry. This
gives necessary BF at every type.

The root proposition algebra is the full powerset of the collection of
root words and terminal entrances, since each terminal has just two
propositions. All terminal algebras are complete. Thus necessary
Boolean Completeness holds at $t$. At any relational type a nonzero
root entity contains the single tuple at a single occupied word or
terminal coordinate. Even $H$ has these singleton predicates by
internal comprehension with parameters. A word shift has at most one
preimage of the chosen address by right cancellation. Therefore every
transport of a singleton of this kind is bottom or another single
tuple at one address; it decides every admitted tester. In both
terminals the same singleton argument is immediate. This proves
necessary Strong Atomicity at all relational types.

For each type put a fixed external well-order of its root domain in
every word row, the appropriate internal well-order in every terminal coordinate. The resulting
relation is necessarily a well-order in the required internal sense.
This gives [Modal Well-Ordering](../index.html#principle/modal-well-ordering-r).

The truth supported at the empty word can never become possible again
after a nonidentity arrow. It therefore witnesses that every actual truth
is ND-necessary. At a terminal the true proposition witnesses the same
claim, giving its necessary form. The proposition true at every terminal
and at no word is a self-atom: whenever it holds it is the top of a
two-valued terminal. Its support splits between terminal coordinates, so
it is not an atom at the root. The pure sentence $\exists p(p\land
\Diamond\neg p)$ holds at the root and cannot become true from a terminal.
Consequently pure B fails.

The revised Mathematical Possibilism schema fails at this root. Its
inexact ordinal benchmark contains the successively generated finite
ordinal thresholds; they are distinguished by external finite orders
on the infinite root individuals. The current rows and hence all
finite-order tests are available. The root has at least continuum many
propositions, so on a present subcollection represent the atomless
complete Boolean algebra of regular open subsets of Cantor space
(cardinality $2^{\aleph_0}$). This carrier is revised-small.
Indeed a subcollection $Y$ strictly above the ordinal benchmark must
be uncountable, since present cardinal comparisons have all maps.
A countably infinite subset of $Y$ has $2^{\aleph_0}$ subextensions,
all available at the root. Their power codes cannot fit in a proper
smaller-cardinality subcollection of $Y$, since $|Y|\le2^{\aleph_0}$.
Thus $Y$ cannot be power-closed. Every principal interval of the root
proposition algebra is a powerset and hence atomic, so none represents
this nontrivial atomless algebra.
[Ordinal thresholds and the power-coding test](singular-lottery-ordinal-thresholds.html)

## Rigid relations lift at every arrow

At the root, a relation $F$ with present row $E$ is weakly rigid
if and only if its row at every arrow $h$ is exactly $h[E]$.
Weak persistence gives one inclusion. To exclude a target tuple not
in $h[E]$, take a tester that is top everywhere except at $h$, where
it omits that tuple. Its relation at a terminal is available even in
$H$, by comprehension with the tuple as parameter. Weak inextensibility
of $F$ gives the reverse inclusion. Conversely these direct images
give both definitions immediately. Composition propagates the equality
through every further arrow, so a weakly rigid relation is rigid.
In every terminal every relation is rigid.

Every rigid relation $R$ at a specified word $u$ has a rigid root
preimage. At each argument sort choose a section of the shift by $u$:
copy the argument onto its suffix and assign fixed data at all remaining
addresses. This includes individual arrays. Apply these sections
coordinatewise to $R$'s current tuple set to get $E'$. Its direct
image at each terminal inside the suffix is the corresponding
terminal extension of $R$. At each outside terminal it is a singleton
or empty. Thus all the terminal projections of $E'$ are admitted in the
respective terminal, and all word rows are unrestricted. Taking those
direct images as the rows gives a rigid root relation whose transport
by $u$ is $R$. For an entrance to any terminal, lift each argument
by varying just that one terminal coordinate, using fixed data
elsewhere. The same proof produces a rigid preimage of every relation
at the terminal. Consequently, at every arrow the rigidity predicate
itself has exactly the images of its current members. This proves
necessary [Rigid Rigidity](../index.html#principle/rigid-rigidity-r) and
necessary Weakly Rigid Weak Rigidity.

## Both power principles fail

The map's [two-arithmetic counterexample](coalesced-two-extensional-arithmetics-root.html)
already separates Rigid Rigidity from Rigid Power. Here the failure
occurs with Possibly Witnessed Possibility for the given signature.

Use the sort $\sigma=et$, choose a single letter $d$, and write $h$ for
the $H$ entrance at the empty word. At distinct letters $j_n$ take the
propositions $p_n$ true just at that word and at no terminal. The
distinct unary individual properties $u_n=\lambda x^e.p_n$ form a
set $U$. Every terminal projects $U$ onto the singleton containing the
bottom individual property. Thus the relation $R_U$ with the direct
images of $U$ as its rows is admitted and rigid.

Let $V$ be the external family of singleton subsets of the standard
numerals in $\omega^M$. This family is not an admitted relation in
$H$: otherwise separation would define the standard cut in $M$, a
proper inductive subset of its naturals, contradicting internal
induction. The cut is proper since $M$ asserts the existence of a
proof of contradiction in the actually consistent theory ZC. Choose a
surjection $\beta:D_{r,et}\to D_{H,et}$ mapping $U$ onto $V$.
There are enough remaining inputs for surjectivity since $D_{H,et}$ is
externally countable and the root sort contains the unrestricted profiles.

Take $D=\{a:h a=\beta(d a)\}$. Every nonempty word projects $D$ onto
the full sort: first lift a desired value along that word, then set the
empty-word $H$-coordinate to $\beta(d a)$. This coordinate is outside
every nonempty-word suffix, so changing it preserves the prescribed
value and $d a$. Every entrance following a nonempty word is therefore
onto on $D$. Every other empty-word terminal coordinate is independent of the two
specified values; the empty-word $H$ coordinate attains every value
by surjectivity of $\beta$ and of the shift by $d$. Thus the relation
$R_D$ with row $D$ now and full rows everywhere else is an admitted
rigid relation.

At $d$, the rigid $R_U$ is a subrelation of the transported $R_D$,
which is top. If a weakly rigid subrelation $Y$ of $R_D$ had $dY=R_U$,
its current set $E$ would satisfy $E\subseteq D$ and $d[E]=U$.
Its $h$-row would be $h[E]=\beta[U]=V$, which is not admitted at $H$.
The tester that omits $R_U$ only at the word $d$ therefore holds
necessarily of every old eligible subrelation. It omits a new eligible
member at $d$. This refutes weak inextensibility of both canonical
powers of $R_D$, witnessing failure of [Rigid Power](../index.html#principle/rigid-power-r)
and [Weakly Rigid Power](../index.html#principle/weakly-rigid-power-r).

The free-word extension and its signature and model calculations are
by OpenAI Codex (GPT-6), prompted by Daniel Kodsi, 26 November 2026.
Two further GPT-6 research agents independently checked the arguments.
