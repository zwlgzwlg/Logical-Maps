# Agreement on analysis with disagreement on arithmetic

Second-Order Analytic Necessitism can hold with failure of Necessity of
Arithmetic, even with necessary Barcan and necessary Infinity at
propositional type. In this model no real number structure is possible.
A second model has actual real number structures, and all possible such
structures agree on every second-order analytical sentence. Its
arithmetical disagreement is the same. Both constructions work in ZFC.

## The two arithmetical components

Use a recursive many-sorted first-order presentation of one-object
group action models of C with singleton individuals. The sorts comprise
the group and the finite simple types; the language records the group
actions, application and evaluation of terms. For each term the action
and abstraction clauses are first-order schemata. In particular the row
of an abstract at a group element is computed from the transported
parameters and all current target arguments. Equality of relations is
agreement on all group translates and tuples. Equivalently one can
adjoin function symbols for the denotations of the countably many term
contexts and their compositional equations. The translation of any
fixed object-language sentence is effective; an ordinary box quantifies
over group elements.

Let $T$ extend these axioms by the Axiom of Infinity and the Peano
condition $I^*_t$ at propositional type, and by the assertion that no
real number structure exists at $\sigma$, for every simple type
$\sigma$. All these pure sentences hold at every arrow of a one-object
model when they hold at its object. The auxiliary group model of the
[symmetric Cohen-class construction](symmetric-cohen-classes-with-new-numbers.html)
is a countable model $K_0$ of $T$ with standard Frege arithmetic at
$t$. Countability here is external, since the ground used in that
construction is countable.

Let $T_{\rm ar}$ be the recursively enumerable theory consisting of
the arithmetical sentences whose translations at the Frege numbers of
type $t$ are provable in $T$. It extends Peano arithmetic, by the Peano
guard and the native induction schema. It is consistent because of
$K_0$. Encode enumerated axioms by finite computation certificates so
that $\operatorname{Con}(T_{\rm ar})$ is a fixed arithmetical sentence.
$K_0$ satisfies that sentence. If $T$ implied its translation then
$T_{\rm ar}$ would contain its own consistency statement, contrary to
Gödel's second incompleteness theorem. First-order completeness thus
supplies a countable model $K_1$ of $T$ whose Frege arithmetic at $t$
satisfies $\neg\operatorname{Con}(T_{\rm ar})$. This applies to a
recursive theory with an interpreted PA; no set-theoretic correctness
of $K_1$ is assumed.

Both points have singleton individuals and see no real number
structure at any type. Every arrow within either component acts
bijectively on every typed domain, since it has a group inverse.
Consequently all Barcan instances hold necessarily in each component.

## A source satisfying both Analytic Necessitisms

Code the two countable presentations, including the interpretation of
their term operations, by reals. In a fresh sufficiently large regular
$H_\theta$ take a countable elementary substructure containing both
codes and their enumerations, and collapse it. Its natural numbers
are standard and the coded presentations are preserved. Over this new
ground $M$ use the same finite labelled-partition forcing, generic
ultrafilter, Boolean algebra $B$ of finitely supported ground values,
and group $G$ of finite permutations of labels as in the
[one-exit construction](symmetric-cohen-classes-with-new-numbers.html).
The generic is chosen after both components.

The new source has singleton individuals. At each relational type
$\tau=\bar\sigma t$ its domain consists of triples
$$
 (d,a_0,a_1),\qquad
 d:D_{\bar\sigma}\longrightarrow B,\qquad a_j\in (K_j)_\tau ,
$$
where $d$ is a ground finitely supported function. Its source application
reads $d$ at the generic. Source loops $G$ act on current rows as in
the one-exit construction and leave the two old coordinates fixed.
There is an entrance to each $K_j$, with all its old postcomposites.
The entrance projects to the corresponding coordinate and absorbs
precomposition by every source loop. These prescriptions respect
composition; the old models keep their own outgoing arrows.

Compute a source abstract's current row by ground Boolean evaluation
over the new sorts, and its two old coordinates by the old term
operations on the two projections. Equality at the source compares
whole triples. Necessity of a scalar is equality of the whole scalar
with top, testing its current Boolean value and both old coordinates.
Every nonzero current Boolean difference is seen by a source loop;
every old-coordinate difference is distinguished after its entrance
by the old intensionality clause. The generic meets the ground
quantifier joins, and evaluating an abstract after an entrance uses
all arguments in the old model. These give the action-model and
term-closure clauses.

The no-real argument at the source is unchanged in its essential
step. For a candidate structure supported by $F$, the admitted ground
join of the rows of its standard successor iterates gives its entire
number orbit by induction. A permutation of labels within one
generic class preserves the generic. If it fixes $F$ then it fixes
each number individually, and by extensionality each current real
representative. The least finite ground support of each of these
entities must lie inside $F$: transposing one of its other labels
with a fresh label in the same class would move its least support.
For each such representative the sequence of Boolean truth values for
membership of the standard successive numbers is a ground sequence
supported by $F$. Its trace therefore belongs to the subextension
given by the restriction to $F$. The bits of a class missing $F$ give
an admitted numerical property with a fresh Cohen real as its trace.
Fullness cannot supply its representative. The two extra ground
coordinates are fixed by every label permutation; the locality and
freshness calculations apply to the triples just as to the previous
germs.

The source and both old points thus satisfy the universal absence of
real structures, giving both Analytic Necessitisms at the source.
The source has infinitely many scalar values, and the closed standard
numerals form an invariant inductive current row. Its Frege numbers
are exactly the standard numerals; usual finite counting gives $I^*_t$
and the Axiom of Infinity there. Both conditions also hold at the old
points. Every arrow from the source is surjective on every typed
domain, by the free old coordinates and the bijective loops.
This proves necessary Barcan.

$K_0,K_1$ disagree on the guarded sentence
$\operatorname{Con}(T_{\rm ar})$, so Necessity of Arithmetic fails.
Arithmetic Necessitism fails too. Choose a nonstandard number $m$ in
$K_1$. A source tester for numbers can have full current Boolean row,
top $K_0$-coordinate and $K_1$-coordinate $\lambda z.\,z\ne m$.
All standard numerals necessarily pass, since distinct numbers remain
distinct under the Peano guard. The $K_1$-number $m$ fails the tester.
This refutes weak inextensibility of the source numbers.

The absence of possible real structures is forced by either arithmetic failure in this model. With Analytic Necessitism, a possible real structure at any type would give both Arithmetic Necessitism and Necessity of Arithmetic by the [cross-type Peano matching lemma](analytic-necessitism-and-transversal-imply-arithmetic-necessitism.html#matching-numbers).

## A source with actual real number structures

Use the two arithmetical components above and a third component, a
full standard S5 model on countably infinitely many worlds with
singleton individuals, constant domains, identity transports and
all world-indexed rows. Add a new root with identity as its only
loop. At a relational type take an arbitrary current subset of the
argument tuples and one whole value from each of the three designated
component points. Individuals are singletons. Use the three coordinate
projections and their old postcomposites as exits. This is the ordinary
fullest [coalesced construction](coalesced-two-extensional-ch-models-root.html).
In particular all current tuple sets and functions at the root are
represented, and every arrow in the cone is surjective.

Every real structure at this root or in the full S5 component has
the standard naturals, all their subsets and all relations on the
resulting carriers, by fullness of current rows. All such structures
agree on every second-order analytical sentence. The other two
components contain no real structures at any type. Necessity of
Second-Order Analysis therefore holds, and its instances at $t$ are
nonvacuous: both the root and the S5 component have continuum many
propositions and full current rows, sufficient to code a real
structure. Such a structure cannot be necessarily real, because of
the other exits. Analytic Necessitism fails at this root. The same
two arithmetical exits again refute Necessity of Arithmetic and the
same nonstandard-number tester refutes Arithmetic Necessitism.
Surjectivity gives necessary Barcan. All points have infinitely many
propositions in the quantified Frege sense.

The root has a current well-order at every type by full current rows.
The scalar supported at the identity alone is a true strong atom.
Revised Mathematical Possibilism holds there as well. With a singleton
individual everywhere, the finite family of uniform extensional tables
on the individual order and field bounds the inexact ordinals, by the
[singleton table argument](two-colour-multisets-with-a-word-guard.html).
Full current rows give every infinite carrier a countably infinite
power-closed subset exceeding that finite bound. For finite Boolean
algebras use the scalar factor of the S5 component, $\mathcal P(\omega)$:
the union of $j$ singleton-world atoms, with every other coordinate
bottom, has the desired interval of $2^j$ propositions. The order
isomorphism is a current graph. Bottom gives the one-element interval.

## Relational Choice at the arithmetic components

The two-stage generic source and its first old component both fail even the instance of Relational Choice with scalar inputs and outputs. In the first old component this is the [generic-classmate obstruction](symmetric-cohen-classes-with-new-numbers.html). At the generic source take the same generic class-bit scalars and use bottom on both extra coordinates. They still distinguish all labels. Ask each such scalar to select a different label from its actual generic class, and use bottom as the only output for every other input. The current row with this demand is the same finitely supported ground Boolean-valued relation as at the auxiliary component, with bottom on the two old coordinates. It is actually serial. For any proposed selector choose an input from a class disjoint from its finite pin. A transposition in that class exchanges the selected output with a third classmate and fixes the input, pin and generic. It preserves the whole selector, including its two fixed old coordinates. This contradicts functionality. In the three-component coalesced model the outer full-current root does supply local Relational Choice by its actual well-order. Its entrance to the first generic-class component still refutes necessary Relational Choice, hence Modalized Relational Choice as well.

Checked independently by two OpenAI Codex (GPT-6) researchers, prompted by Daniel Kodsi, 27 November 2026.
