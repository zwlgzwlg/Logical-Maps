# Logical Necessity with new Frege numbers at a successor

**Theorem.** For each admissible set-sized signature there is a pointed C action
model of Logical Necessity in which $\Box I^*_e$ holds and the property
$\mathbb N_e$ is not weakly inextensible at the designated point.
Consequently Logical Necessity does not imply Arithmetic Necessitism.

## Worlds and ultrafilters

Fix a nonprincipal ultrafilter $U$ on $\mathbb N$ and an infinite set $A$
of individuals with $|A|\ge|\Sigma|$. Use two disjoint sets of edge labels.
The first consists of labels $i\in\mathbb N$ for the branches of an
ultrafilter node. The second consists of deterministic letters $j$. Provide,
for each map $f:A\to A$, at least $\max(\aleph_0,|\Sigma|)$ letters marked
by $f$. These marks will act on individuals. The one-proposition signature
already suffices for the implication, and all deterministic letters can
then act by the identity.

An object $T$ is a rooted, well-founded tree of finite strings of labels.
Every node is either a leaf, has exactly one child at a deterministic
letter, or has precisely the children $i\in\mathbb N$. No branch is
infinite. The tree consisting of the root alone is denoted by $o$.
Write $L(T)$ for its leaves and $U_T$ for the ultrafilter on its leaves
defined by well-founded recursion. At a leaf it is principal, at a
deterministic node it is its child's ultrafilter, and at a branching node
a leaf set is large when its intersection with the $i$th subtree is large
for $U$-almost all $i$.

An arrow from $T$ to $R$ is a refinement: substitute a tree $S_u$ at
each leaf $u\in L(T)$, retaining all existing edges. Write
$R=T[S_u]$. It is well-founded because an infinite path would first cross
a leaf of $T$ and then give an infinite path in a single $S_u$.
Composition is repeated substitution, with addresses concatenated, and
the identity substitutes $o$ everywhere. These objects and arrows form
sets. The defining recursion gives
$$
 B\in U_{T[S_u]}\quad\Longleftrightarrow\quad
 \{u:\{v:uv\in B\}\in U_{S_u}\}\in U_T.
$$

## The local types and their action

Set $E_e=A$. Along a path $s$, transport an individual by composing the
marks on its deterministic letters in path order; a branching edge acts
as the identity. At a relational type $\tau=\alpha_1\ldots\alpha_k t$,
suppose $E_{\alpha_i}$ already defined, and put
$D=\prod_i E_{\alpha_i}$ (a singleton for $k=0$). A raw profile $X$
assigns an arbitrary row $X_s\subseteq D$ to every finite string $s$.
Its section $X^s$ is given by $(X^s)_v=X_{sv}$. Form $E_\tau$ by
quotienting raw profiles by
$$
 X\sim Y \quad\Longleftrightarrow\quad
  \text{for every tree }T,\quad
      \{u\in L(T):X_u=Y_u\}\in U_T.
$$
In particular equivalent profiles have the same row at the empty string.
The row there supplies present application; equality of entities is
equality of their entire equivalence classes.

**Separation by refinement.** If $X\sim Y$, then for every $T$,
$X^u\sim Y^u$ for $U_T$-almost all $u$. Otherwise on a large set of
offending leaves choose $S_u$ separating $X^u,Y^u$ (unequal rows on a
large set of its leaves), and use $o$ at the other leaves. Substitution
and the ultrafilter equation contradict $X\sim Y$. Conversely the
statement about all sections implies the row criterion by testing their
empty-string rows.

At $T$ the sort $\tau$ is the ordinary ultrapower
$E_\tau^{L(T)}/U_T$. For $T\to T[S_u]$, represent a relation by a
family $X(u)$ of raw profiles; send it to the family which at $uv$ is
$[X(u)^v]$. Send an individual family $a(u)$ at $uv$ to the action of
the path $v$ on $a(u)$. The separation lemma makes this independent
of representatives, since at each good $u$ it applies to $S_u$.
Successive sections and the path actions compose, giving functoriality.
Interpret current application by ordinary ultrapower application, reading
the empty-string row in each factor. Truth uses the ultrafilter truth
value. At $o$ this gives exactly the local sorts and rows defined above.

Two different relational entities at $T$ are distinguished as profiles
by some future and tuple there. Indeed for a large set of $u$ their
chosen representatives have unequal rows at a large set of leaves of
some separating $S_u$. At each such leaf choose a tuple witnessing row
disagreement. On a large subset the orientation of the disagreement
is constant, by the ultrafilter law. On the remaining leaves use
arbitrary tuples. The resulting tuple of ultrapower entities at
$T[S_u]$ separates their extensions. Equal entities have identical
transported extensions by the well-definedness already proved.
This identifies the presentation with a typed intensional premodel
whose relational entities are the corresponding actual outgoing
profiles. The empty tuple case identifies proposition identity with
agreement of truth throughout the cone.

## Comprehension and truth at each object

Use the ordinary local classical operations and quantifiers on $E$.
Boolean operations, application and binders producing propositions can
equivalently be treated as the nullary case of the following profile
construction. To construct an abstract $\lambda\bar x.\phi(\bar x,\bar a)$
at $o$, fix raw representatives of its relational parameters. At each
finite string $s$ give it the row of all tuples $\bar b$ for which the
body holds locally on $E$ with arguments $\bar b$ and parameters
$\bar a^s$. Here $\bar a^s$ uses the path action on individuals and the
classes of the sections of the chosen representatives for relations.
Evaluation of the body uses only proper subterms. Replacing parameter
representatives changes none of the resulting profile classes, by
separation by refinement applied to the finite list of parameters.

For clarity, the same rule defines each compound proposition-valued
term: at $s$ compute its local Boolean operation, equality, application,
or quantifier on the shifted free parameters, evaluating proper
subterms locally. The output is the resulting nullary profile. Thus an
equality formula tracks entity equality at each stage, although its
current Boolean truth uses equality in $E$. Partial application, when used,
retains the remaining argument tuple in its raw row: apply the
section of the function to the shifted supplied arguments followed by
that tuple. The same section computation therefore applies.

The rule commutes with sections. With representatives held fixed,
taking the section at $s$ and constructing the abstract on the
$s$-shifted parameters give equivalent raw profiles: at a further $v$
the parameters are the iterated sections, and replacing the temporary
representatives of their classes changes further rows only on a small
set of leaves in each testing tree. This argument works separately for
each fixed initial string $s$; pointwise shift of an equivalence class
at a named branching index is not assumed to be intrinsic. At a
front the section families are intrinsic modulo its ultrafilter.

At $T$, interpret a term on parameter families by the family of its
values on $E$, modulo $U_T$. The section rule just proved shows that
this commutes with transport to every $T[S_u]$. Ordinary Łoś induction
gives, for every formula $\phi$ and tuple of parameter families,
$$
 T\models\phi([\bar a(u)])\quad\Longleftrightarrow\quad
 \{u:E\models\phi(\bar a(u))\}\in U_T .
$$
For quantifiers, witnesses at the good leaves assemble to an admitted
ultrapower object of that sort. For lambda, the constructed row at the
empty string has exactly the indicated application values. At every
further front the computation agrees by transport, so the admitted
profile is the required action-semantics denotation at all arrows.
Propositional equality and the defined box agree with the action
reading by separation. This proves term closure, including modal
formulas, and hence gives a C action model. In particular every object
has the same complete pure theory as $o$.

## The numerical counterexample

The root admits any specified current subset of any baseline sort:
assign it to the empty-string row of a raw profile. For $\nu=(et)t$, at type
$\nu t$ take the current row consisting of the denotations of the
standard Frege numerals. In the native
[definition of finite cardinality](../index.html#background/arithmetic), the
premises for an inductive property are current membership of zero and
closure under successor at the current point. The displayed row
satisfies both premises, and every inductive property
contains those denotations. Thus the actual $\mathbb N_e$ at $o$ is
exactly this set. The $k$th numeral counts exactly the current
individual properties with $k$ members by the ordinary finite
successor/removal induction. All finite individual sets occur as
current rows, and the individual domain is infinite, so the numerals
are distinct as entities: on a current property with exactly $k$
members the $k$th numeral applies and each different numeral fails.
It follows that zero is never a successor on the numbers and that
successor is injective there, so $I^*_e$ holds. Pure Łoś gives $\Box I^*_e$.

Define an admitted root tester $X^{\nu t}$ by taking every row full
except that its row at each one-edge branching address $i$ excludes
the $i$th standard numeral. Fix a current number, the $m$th numeral.
Its transport at any front is the constant family of $m$th numerals,
since the numeral is a closed term and term transport was proved
above. The tester can miss that family only if the leaf has the
one-edge address $m$. In any tree that leaf is absent or belongs
to a single branch of a $U$-node, hence has measure zero. Therefore
every current number necessarily satisfies $X$.

Take $T$ consisting of one branching node with leaves $i$. The
ultrapower element $b=[i\mapsto\text{the }i\text{th numeral}]$ is a
number by Łoś. At this front $X$ fails of $b$ at every leaf, hence at
the object. This witnesses failure of weak inextensibility at $o$.

## Logical Necessity

At $o$ assign distinct individuals to the individual names. For each
signature sentence realized at $o$ under some assignment select a
witnessing assignment. Choose a distinct deterministic letter $j$
whose mark sends the finitely many individual names' initially
assigned values to their required values. Distinct letters exist by the
multiplicities in the construction. For each relational constant, on
the entire subtree of strings beginning with $j$ put a raw
representative of its required value, with $j$ removed from the
address. Use empty rows for unused pieces. The assignment defines
a single admitted root profile for each constant. At the one-edge
deterministic front for $j$ these constants take the required values
exactly, since its ultrafilter is principal. Thus any realizable named
pure matrix is possible. Conversely, if a transported tuple at any
front satisfies a pure matrix, pure Łoś gives a local witness at
$o$ for its existential closure. This is the dual of the Logical
Necessity schema for every list of distinct matching constants.
Interpreting the constants globally over the rooted category amounts
to assigning their transported values at each object.


## Further consequences in this model

Every specified front transports onto each relational type. A target
family assigns one raw representative to every leaf. Put that profile
on the entire subtree below its leaf; distinct leaves are incomparable,
so the prescriptions agree. This gives a source relational entity
transporting to the whole target family. The same construction on each
local factor gives the lift across arbitrary refinements. Ordinary BF
therefore holds necessarily at every relational type. At individual
type it fails: choose distinct individuals $a_i$ and use a tester
which excludes $a_i$ at the one-edge branching path $i$, with all other
rows full. Every fixed individual necessarily satisfies it, while the
ultrapower individual $[i\mapsto a_i]$ fails it at the one-step front.

At each type choose an external well-order of $E_\sigma$. Give a
binary relation that same row at every string. Every section is the
same baseline well-order, which orders every nonempty admitted current
property at the baseline. Łoś then makes the one chosen relation a
well-order at every front. This gives Modal Well-Ordering, including
its individual instance.

The nullary profile true only at the empty string is a true atom at
the base. At every proper front its transport is bottom, because all
leaf addresses are nonempty. It is therefore a true strong atom; pure
Łoś gives necessary Strong Actuality. There are infinitely many
propositions: singleton deterministic-letter paths are nonzero and
pairwise disjoint. The numeral argument above therefore gives the
Axioms of Infinity both at $e$ and at $t$, necessarily.

## Strong Atomicity at every relational type

First compare any two fronts $T,R$. For every subset $B$ of their common
leaves, $B\in U_T$ if and only if $B\in U_R$. This follows by well-founded
induction on $T$. If both trees stop, the assertion is immediate.
If their root choices differ, they have no common leaves. At a matching
deterministic letter use the induction hypothesis for its child.
At matching ultrafilter nodes use it for each corresponding pair of
children and then take the same $U$-quantifier on their truth values.
In particular the common leaves are either null for both ultrafilters or
conull for both, and the two traces agree in the latter case.

For nonbottom $F$, choose a front $T$ whose $F_u$ are nonempty on
a large leaf set $H$. Choose one tuple $b_u\in F_u$ for each $u\in H$.
Build a raw profile $A$ having row $\{b_u\}$ exactly at those leaf
addresses, with all other rows empty. It is nonbottom and $A\le F$.
For any other relation $Y$, the ultrafilter $U_T$ decides whether
$b_u\in Y_u$ almost everywhere on $H$ or its complement there.
In the first case $A\le Y$: at any testing front $R$ the set of
counterexample leaves is a subset of $L(R)\cap L(T)$ which is null
for $U_T$, hence also for $U_R$ by the comparison just proved.
In the second case the same proof gives $A\le\neg Y$. Thus $A$ is
a Boolean atom.

Each section $A^s$ is bottom or has the same form at the subtree rooted
at $s$. For an address inside $T$, restrict to its descendant chosen
leaves: if they are null at that subtree the common-leaf comparison
makes the restriction bottom, and if conull the same decision argument
makes the restriction an atom. At an address outside $T$ it is
identically empty. By Łoś, every transport of $A$ satisfies the
disjunction of bottom and atom. This is exactly the persistence of
decisions in the map's [strong-atom definition](../index.html#background/atoms).
Hence $A$ is a strong atom; pure Łoś gives necessary Strong Atomicity
at every relational type.

The empty-string proposition above guards $\Box_{\ne}p$ for each truth
$p$ at the base, since it is impossible after every proper refinement.
This is the [identity-only guard argument](finite-multisets-free-words.html).
Pure Łoś transfers the resulting universal statement to every front.

## A countable family of propositions without a supremum

For $n\ge1$ take the front $T_n$ with exactly $n$ levels of branching
nodes and no deterministic steps. Let $p_n$ be the raw proposition true
exactly on its leaf addresses. These are distinct Boolean atoms by the
common-leaf argument. At the base the set of these propositions and a
graph pairing them with distinct standard Frege numerals are admitted
current rows. Thus this is countable in the map's internal relational
formulation.

Let $J$ be an upper bound and choose a raw representative. At each
$T_n$ its truth is large. Hence
$$
 D_n=\{i:\{v:iv\in J,\ |v|=n-1,\ v\text{ consists of branching
 labels}\}\text{ is large in }U_{T_{n-1}}\}\in U,
$$
where $T_0=o$. At each $i$ take the largest $k\le i$ such that
$i\in D_1\cap\cdots\cap D_k$, defaulting to $1$ if there is no positive
such $k$. Call it $n(i)$. For each fixed $m$, the common intersection
of $D_1,\ldots,D_m$ and $\{i:i\ge m\}$ belongs to $U$, so
$n(i)\ge m$ almost everywhere. Also $i\in D_{n(i)}$ almost everywhere.

Form the front $R$ with a branching root and the subtree $T_{n(i)-1}$
at child $i$. It sees $J$ true by the ultrafilter equation. The overlap
of its leaves with those of $T_n$ has measure zero for each fixed $n$,
since $\{i:n(i)=n\}$ has measure zero. The atom $p_R$ concentrated on
the leaves of $R$ is therefore disjoint from every $p_n$. Its complement
is an upper bound for the family. Yet $J\not\le\neg p_R$, since $R$
sees both $J$ and $p_R$ true. No upper bound is least. In particular
the propositional instance of Countable Boolean Completeness fails.

## Tame Rigidity and the failure of Rigid Power

Write $h[D]$ for the set of pointwise transports of tuples in a current
row $D$ along a specified arrow $h$. A relation $X$ with current row
$D$ is weakly rigid at the base if and only if for **every** front $T$,
the extension of its transport there is precisely $T[D]$.

For the forward direction, weak persistence gives the inclusion of
$T[D]$. For the reverse inclusion suppose a tuple
$b=[u\mapsto b_u]$ in the extension at $T$ is outside $T[D]$.
Form a root relation $A$ with row $\{b_u\}$ on each leaf $u$ of $T$ and
empty elsewhere. For any $a\in D$, the leaves of $T$ where the transported
value of $a$ equals $b_u$ form a $U_T$-null set. At any other testing
front $R$, coincidence with $A$ can occur only on the common leaves
and is contained in this same null set. The common-leaf comparison
makes it $U_R$-null. Thus every $a\in D$ necessarily satisfies
$\neg A$, but $b$ fails that tester at $T$. This contradicts weak
inextensibility. The converse follows directly from the definitions of
weak persistence and weak inextensibility: every future member comes
from a current member. Exact images compose along refinements, so this
description also proves that a weakly rigid relation at the base is
fully rigid. Pure Łoś gives necessary Tame Rigidity.

Fix $\nu=(et)t$, the type of individual cardinalities. Two countably
infinite subsets of $E_\nu$ have different behavior.

1. The set $V$ of standard Frege numeral entities cannot be the current row
   of a weakly rigid relation. If $Y$ with row $V$ is weakly persistent,
   at the one-step branching front the current row of $Y$ contains every
   transported fixed numeral. For a chosen raw representative this says
   $D_n=\{i:\mathbf n\in Y_i\}\in U$ for each standard $n$, where
   $\mathbf n$ is the baseline numeral entity. Choose $n(i)$ tending
   to infinity modulo $U$ with $i\in D_{n(i)}$ almost everywhere by
   the finite-intersection diagonal of the preceding section. Then
   $[i\mapsto\mathbf{n(i)}]$ belongs to the row there, and it is distinct
   from every transported standard numeral. This contradicts the exact
   image characterization.
2. A different countably infinite set $C\subset E_\nu$ is the current
   row of a rigid relation $B$. Choose distinct deterministic letters
   $l_n$ and let $p_n$ be the proposition true only on the one-edge
   address $l_n$. Embed propositions into $E_\nu$ by the constant-in-
   arguments relation $K(p)=\lambda Z^{et}.p$, and put
   $C=\{K(p_n):n\in\mathbb N\}$. The constant embedding preserves
   distinctness and commutes with transport. Give $B$ row $C$ at the
   empty string, row $\{\bot_\nu,K(q)\}$ at every one-edge $l_n$,
   and row $\{\bot_\nu\}$ elsewhere, with $q$ true only at the
   empty string. A front beginning with a branching node sends every
   element of $C$ to bottom. A front consisting of the sole edge $l_n$
   sends that element to $K(q)$ and all others to bottom. Every other
   proper front again sends them all to bottom. Thus these rows give
   exactly the transported images at every front, proving rigidity.

Choose a bijection $\beta:E_\nu\to E_\nu$ taking $C$ onto $V$.
Such a bijection exists: $E_\nu$ is uncountable since arbitrary subsets
of countably many deterministic-letter addresses give distinct
propositions, and $K$ embeds them. Choose two distinct deterministic
letters $j,k$. The section maps $\pi_j,\pi_k:E_\nu\to E_\nu$ are
well-defined on classes because these one-edge fronts have principal
ultrafilters. Arbitrary values at $j,k$ can be simultaneously
prescribed on raw profiles by prefixing representatives in their two
disjoint subtrees. Define
$$
 D=\{x\in E_\nu:\pi_k x=\beta(\pi_j x)\}.
$$
Let $F$ have current row $D$ and full row at every nonempty address.
It is rigid. Indeed $D$ maps onto the entire cardinality sort at every
proper front. At a front starting with $j$, lift a given target along
the residual front in the $j$-subtree, then prescribe its $\beta$-mate
in the $k$-subtree. For a front starting with $k$, use $\beta^{-1}$
in the other subtree. A front starting with a third deterministic
letter or a branching node uses neither subtree: choose both values
freely subject to the displayed equation. The lifting along the
specified front is available for the relational type $\nu$ by the
subtree prescription in the Barcan proof above. The root exact-image
calculation now gives rigidity of $F$.

At the deterministic $j$-front, the rigid relation $B$ with row $C$
is a subrelation of $\pi_j F=\top$. It cannot be the $j$-transport
of a weakly rigid $Y\le F$ at the root. For if $D_Y$ is its current
row, exact images would give
$$
 D_Y\subseteq D,\qquad \pi_j[D_Y]=C,\qquad
 \pi_k[D_Y]=\beta(\pi_j[D_Y])=V.
$$
The $k$-transport of $Y$ would then be rigid with current row $V$,
contradicting part 1. The property of being a rigid subrelation of $F$
is weakly persistent in C. Its $j$-transport nevertheless contains
$B$ outside the image of its current row, so by the exact-image test
it is not weakly rigid. This refutes Rigid Power. Weakly Rigid Power
fails as well, since weak and full rigidity agree throughout the
model.

## Analytic Necessitism at relational types

At every relational type $\sigma$, a real number structure is possible,
but none can have both rigid numbers and necessarily distinct numbers.
This refutes Analytic Necessitism and its second-order form; the instance
$\sigma=t$ suffices. We use the map's
[definition of a real number structure](https://github.com/zwlgzwlg/Logical-Maps/blob/4bb9287187ed7cb09567eb3a6302cb896c986ec4/logical-maps/topics/classicism/background/arithmetic.md).

First consider a countably infinite actual row $D=\{a_0,a_1,\ldots\}$
of pairwise distinct entities of any type. Suppose each pair is
necessarily distinct, and $D$ is the current row of a weakly rigid
property $N$. For each $m$ choose sections $a_{m,i}$ representing
the transport of $a_m$ to the one-step branching front. For each
fixed $k$, the set $G_k$ of indices $i$ where all of
$a_{0,i},\ldots,a_{k,i}$ are in $N_i$ and are pairwise distinct
is in $U$. This uses weak persistence for the fixed list, necessary
distinctness for its finitely many pairs, and the one-step
ultrapower truth rule. Define $k(i)$ to be the largest $k\le i$
with $i\in G_k$ when this set is nonempty, and $0$ otherwise. These
good sets are nested; $k(i)$ tends to infinity modulo $U$ and
$i\in G_{k(i)}$ almost everywhere. Thus $b=[i\mapsto a_{k(i),i}]$
is a number for $N$ at this front. For each fixed $m$, almost every
$i$ has $k(i)>m$ and $a_{k(i),i}\ne a_{m,i}$, so $b$ is different
from the image of each member of $D$. This contradicts exact images.
Consequently no such row of necessarily distinct entities can be the
number row of a rigid structure.

At the base, every real number structure has a countably infinite
number row. The actual orbit of zero under its successor function is
the current extension of an admitted property. Peano induction makes
this orbit exhaust the numbers; successor injectivity and exclusion
of zero from its range make all the ordinary iterates distinct.
Hence the preceding argument rules out any proposed rigid witness.

For existence, distinguish propositions by their truth values at
countably many deterministic one-edge fronts. Arbitrary subsets of
these letters give distinct propositions. At any other relational
type constant-in-arguments abstraction injects propositions into the
type, since its argument types are nonempty. Choose disjoint copies
of $\mathbb N$ and $\mathcal P(\mathbb N)$ in the baseline sort.
Their number and real predicates, successor graph and membership
graph are all admitted current rows. With ordinary zero this is a
real number structure: Peano induction holds, and every current subset
of the numbers is represented by its corresponding real. This proves
the antecedent already at the designated point. If the baseline
individual set $A$ is chosen with $|A|\ge 2^{\aleph_0}$, the same
argument refutes the individual instance too.
