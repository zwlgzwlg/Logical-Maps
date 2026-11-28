# Integer stages of paired individuals with glued constants

**Claim.** For any admitted signature consisting of relational constants, there is a C action model of Logical Necessity in which a proposition
is 5-necessary and fails to be two-hat necessary. In fact the pure reduct
has the same theory at every object, so the failure is necessary. A signature with a single propositional constant already witnesses the nonimplication.

The construction modifies Cian Dorr's
[paired-individuals two-object model](paired-individuals-two-object.html).
It makes the stages of the construction interchangeable in the pure language.
For the interpretation of the constant it adapts the
[free-word gluing construction](supported-product-free-monoids-glued-constants.html).

## Stages, arrows and domains

Let $W=\omega_1\times\{0,1\}$, partitioned into pairs, and let
$V=W\sqcup\{\star\}$, whose additional point is a singleton block.
At stage $n\in\mathbb Z$, coordinate $i\in\mathbb Z$ has the individual
set $V$ for $i\le n$ and $W$ for $i>n$. The full individual domain $D_e(n)$
is the disjoint union of these labelled coordinates. Take all arrows
$g:n\to m$ given by coordinate-preserving functions that send members
of any one block to members of a single block. Decorate each with any
finite word $w$ on a countably infinite alphabet. Composition of $(g,w)$
followed by $(h,v)$ is $(hg,vw)$. Identities have the empty word.
There is an arrow between every two objects. Evaluate at the identity of 0.

Induct on types. An entity $F$ of relational type $\sigma_1\ldots\sigma_k t$
at $n$ is a profile assigning to each arrow $(g,w):n\to m$ an arbitrary
subset $F_{g,w}$ of $D_{\sigma_1}(m)\times\cdots\times D_{\sigma_k}(m)$,
subject to one condition. Some countable set $S\subseteq D_e(n)$ pins the
profile: among arrows with common target and common word, individual maps
agreeing on $S$ give identical rows. At $k=0$ the row is a truth value.
Transport is precomposition, $((g,w)\cdot F)_{h,v}=F_{hg,vw}$. The set
$g(S)$ pins the transport. Arrows with equal target, word and restriction
to $S$ transport the *whole* entity $F$ equally: compare the two composites
with any common continuation. An individual is pinned by its singleton.

These domains contain the denotations of all terms. For a lambda with
parameters, its row at $(g,w)$ is given by evaluating its body at $m$ on
the argument tuple there and the transported parameters. The union of their
pins pins this entire profile, since comparison of arrows on it transports
all parameters equally. This is also the ordinary term-and-transport
induction, including the quantifiers over the admitted domains at each
object. Equality uses equality of entities; agreement at every continuation and
tuple gives equality of relational profiles. This is a set-sized C action
model under the standard pinned-profile semantics.

## Logical Necessity

Translation $n\mapsto n+1$, $i\mapsto i+1$ relabels coordinates,
individuals, arrows, pins and profiles. It induces an automorphism of the
pure interpretation. Thus every pure sentence has the same truth value at
all objects. In particular a pure formula with one proposition variable
has a satisfying assignment anywhere exactly when it has one at 0.

Enumerate the realizable pure formulas $\varphi_j(x^t)$ (including formulas
where $x$ does not occur), choosing a witness $p_j\in D_t(0)$ for each.
Use distinct alphabet letters $j$. Interpret $c$ at the root by
$c_{g,wj}=(p_j)_{g,w}$ whenever the final letter is $j$. Give the remaining
rows the value false. The union of a countable pin for each $p_j$ is
countable and pins $c$. At the loop $(1_0,j)$, its whole transported
intension is $p_j$. Hence for every such formula, if it is satisfiable at
any accessible object then $\Diamond\varphi(c)$. Conversely any truth of
$\varphi(c)$ at an accessible object gives a witness there; the translation
of objects gives a witness at 0. Thus the possible and converse witnessed
possibility schemata hold. The empty-parameter case is pure homogeneity.
These are all tuple cases in this signature. Equivalently, for each pure
matrix $P(x^t)$, $\forall x\,P(x)$ at 0 iff $\Box P(c)$ at 0, by negation.

For a set-sized purely relational signature $\Sigma$, take the alphabet of
size $\max(\aleph_0,|\Sigma|)$. In this fixed pure model choose one realizing
tuple for each realizable pure matrix and ordered variable-type list. There
are only countably many matrices and type lists. Give each matching tuple
of distinct named constants for each such matrix its own letter. On a row
whose word ends in that letter, the row for each participating constant is
the row of its chosen witness with that letter removed. Other rows can be
empty. Even if there are uncountably many letters, each fixed constant uses
only countably many distinct witness entities, so it has a countable pin.
The corresponding loop realizes the whole tuple simultaneously. This proves
Logical Necessity for the full schema. This gluing uses the relational form
of the constants. If global sections are used to present fixed constants,
take the rooted unfolding whose objects are arrows $k$ from stage 0.
Interpret each constant at $k$ by its transport along $k$. The resulting
section is coherent, and the future arrows and local typed evaluations over
$k$ are precisely those of the original target of $k$.

## A proposition which fails two-hat necessity

Let $P$ at 0 hold on exactly the arrows ending at $n<1$, i.e. on the
stages where coordinate 1 is $W$. It is pinned by the empty set. Recall

$$
\hat{\hat\Box}P\quad\leftrightarrow\quad
\exists q\,(q\land\Box(\Diamond_{\ne}q\to P)).
$$

At an arrow $k$, the condition $\Diamond_{\ne}q$ says that for every
currently true proposition $r$ at its target there are continuations
$v,x$ such that $q$ holds at $vk$ and $r$ holds at $xv$, the latter
evaluated as a proposition of the target of $k$.
Indeed it is $\forall r\,(r\to\Diamond(q\land\Diamond r))$ there.

Let $u:0\to1$ be the inclusion in coordinate 1 and identity in every
other coordinate, with empty word. At $u$, $P$ is false. Fix any $q$ true
at 0 and any $r$ true at 1. Choose a countable pin $T$ for $r$. In
coordinate 1 choose a pair $B$ disjoint from $T$. Let $v:1\to0$ be the
identity on the old individuals and send the added singleton at coordinate
1 to one member of $B$. Then $vu=1_0$. Let $x:0\to1$ send both members
of $B$ to the singleton and fix all other old individuals. All other
coordinates and words in $v,x$ are identities. The loop $xv$ fixes $T$
and has empty word, so $r$ is true there. Hence at $u$ we have
$\Diamond_{\ne}q$. This same $u$ defeats each possible true $q$, proving
$\neg\hat{\hat\Box}P$.

## The same proposition is 5-necessary

Define a root property $Y$ of propositions. On an arrow ending at $n<1$
its row contains every proposition. On an arrow ending at $n\ge1$ its
row contains exactly the propositions at $n$ admitting a countable pin
that omits the singleton of coordinate 1. These rows depend only on the
target, so the empty set pins $Y$. Moreover
$\big(\forall z\,Yz\big)=P$ as proposition entities. For $n\ge1$,
the local proposition consisting of endomorphisms at $n$ that fix that
singleton has a singleton pin and has no pin omitting it. Indeed the identity
and the endomorphism moving just that singleton to one old individual agree
on every set omitting it and have the same word and target.

For each current proposition $z$ choose a countable pin $S$. Add the
partners of all members of $S$ in coordinate 1 to obtain a countable
$N$. Let $q$ consist of the endomorphisms of 0 with empty word fixing
$N$ pointwise. This proposition is true and pinned by $N$. If
$\Diamond_{\ne}q$ at some $k$, then $\Diamond q$ there, so some return
$v$ has $vk$ fixing $N$. In particular $k$ is injective on $N$. Whenever
the target contains the coordinate-1 singleton, no coordinate-1 member
of $S$ can have been sent to it: its distinct partner was also in $N$,
and a block-respecting map hitting a singleton block must identify them.
Consequently $k(S)$ is a pin for $k\cdot z$ omitting the specified
singleton. Thus $Yz$ holds on every $k$ satisfying $\Diamond_{\ne}q$.
It follows that each current $z$ satisfies $\hat{\hat\Box}(Yz)$ and
hence $\Box_5(Yz)$.

The Barcan formula for $\Box_5$ at type $t$ now gives
$\Box_5\forall z\,Yz$, which is $\Box_5 P$. This uses a theorem of
C for the particular operator $\Box_5$ (Appendix D and
`Classicism.box5_barcan`); ordinary BF plays no role. The witnessed
failure is a pure existential sentence. Translation therefore gives a
failure of the implication at every accessible object.

## Two-hat necessity also differs from distinctness-preserving necessity

Let $T$ say that coordinate 0 has a singleton, so that its target is a
stage $n\ge0$. Write $a$ for this singleton at 0. Let $q$ consist of the
endomorphisms of 0 with empty word that fix $a$. For any arrow $k:0\to m$
with $m<0$, the image $b=k(a)$ belongs to a doublet with mate $b'$. Use
the true proposition $r$ at $m$ requiring an endomorphism to fix both
$b,b'$. Any $v$ with $vk\in q$ sends $b$ to $a$, so $v$ sends both
$b,b'$ to $a$. No subsequent $x$ can then have $xv\in r$. This defeats
$\Diamond_{\ne}q$ at $k$; hence $q$ witnesses $\hat{\hat\Box}T$ at 0.

For any true $r$ at 0, choose a countable pin $S$. Take a pair in
coordinate 0 outside $S$. Define $k:0\to-1$ to send $a$ to one member
of that pair and fix the ordinary individuals. Return $v:-1\to0$ by
collapsing this pair onto $a$ and fixing all other ordinary individuals.
Use identities in every other coordinate and empty words. Then $vk$
fixes $S$ and $a$, so $\Diamond r$ at $k$, but $T$ is false there.
No true $r$ witnesses $\Box_{\ne}T$. The two strict separations hold
at every stage by translation.

## Further properties

Every subset of the local tuple domain is the current row of a relation.
One can take that same row on all arrows ending at its stage and the empty
row elsewhere. In particular, choose external well-orders on the argument
domains of each type at each stage. The relation assigning the chosen
well-order to every arrow's target has empty pin and is necessarily a
well-order. This gives Modal Well-Ordering and its usual choice consequences.

Countable Boolean Completeness holds at every stage and counting type.
The current numbers consist of standard numeral denotations: their set
is an available current inductive row, and each standard numeral is in
every inductive row. Thus an internally countable family of relations has
at most countably many current members. Their pointwise union over all
arrows and tuples is a relation pinned by the countable union of their
pins, and is their least upper bound in the native order. Individuals are
uncountable at every stage, so no current number counts all individuals.
The Axiom of Infinity at $e$ holds necessarily.

The proposition algebra is atomless at every stage. For a nonzero
proposition, choose an arrow $h$ where it holds and a source pair disjoint
from its pin. In that pair choose $b$. Keeping the target and word fixed,
vary the function on the pair so that $b$ has a different image. Both
arrows lie in the given proposition. Intersecting it with the proposition
that the target is that of $h$ and that $b$ maps to $h(b)$ gives a
nonzero proper part.

Full Boolean Completeness at $t$ fails. In one source coordinate fix $d$
and choose uncountably many distinct pairs, disjoint from $d$ and its mate,
with representatives $a_j$. Choose distinct old target values $c_j$ and a
value $b$ in that same coordinate. Let $p_j$ hold on just the empty-word
root endomorphisms sending $d$ to $c_j$ and $a_j$ to $b$. These propositions
form an admitted current family. Suppose its join $L$ had countable pin $S$.
Choose $j$ whose $a_j$-pair misses $S$. There are two empty-word root
endomorphisms agreeing on $S$, both sending $d$ to $c_j$, one sending
$a_j$ to $b$ and the other elsewhere. The first lies in $p_j$, hence in $L$.
The cylinder of root endomorphisms sending $d$ to $c_j$ and $a_j$ elsewhere
is disjoint from every $p_i$, so its complement is an upper bound of the
family. The second endomorphism must therefore be outside $L$, contradicting
its pin. Translation repeats the failure everywhere.

The ordinary Barcan formula holds necessarily at every type. Fix an arrow
$(h,w):A\to B$, a tester $F$ at $A$ with countable pin $S$, and a target
argument $b$. For a relational argument let $T$ be a countable pin for $b$.
Modify $h$ off all source blocks meeting $S$ to a block-respecting $j$
whose image contains $T$. For each member of $T$ one may collapse a fresh
source pair in its coordinate onto that point. Choose a countable
$T'\subseteq D_e(A)$ mapping onto $T$. Define a source argument $y$ with
pin $T'$ as follows. On an arrow $(l,u):A\to C$, if some $(k,v):B\to C$
has $u=vw$ and $l|_{T'}=(kj)|_{T'}$, give $y$ the row $b_{k,v}$; otherwise
give it an empty row. Two such presentations have equal $v$ by right
cancellation of words, and their $k$ agree on $T$, so the row is well
defined. Then $(j,w)\cdot y=b$. For an individual argument send a fresh
source member directly to $b$. Since $j$ and $h$ agree on $S$ and have
the same word and target, they give the same row of $F$. If $F$ necessarily
holds of every current argument, use $y$ to show its row at $(h,w)$
contains $b$. This is the ordinary Barcan implication at every stage.
