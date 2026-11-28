# Symmetric integer stages of paired individuals

Necessary Boolean Completeness at every relational type is consistent with
a 5-necessary proposition that fails to be two-hat necessary. The same
example satisfies necessary Barcan at every type, necessary Atomlessness,
necessary Inextensible Comprehension, necessary Tame Rigidity, both
necessary rigid power principles, and Logical Necessity for a purely
relational signature. A second
proposition is two-hat necessary and fails distinctness-preserving necessity.

Use the stages, arrows and words of the [integer-stage model](integer-stages-paired-individuals-glued-constants.html).
The additional symmetry on admissible profiles makes the [Boolean join argument
for symmetric products](symmetric-surjection-products.html) applicable.

## The domains

The stages and coordinate labels are integers. In coordinate $i$, every stage
has $\aleph_1$ ordinary doublets; stage $n$ also has one singleton in that
coordinate if $i\le n$. Take the disjoint union of the coordinates as the
individual domain. Each arrow $(f,w):n\to m$ is a coordinate-preserving map
sending each block into a block, together with a finite word. Ordinary
doublets can collapse. Composition composes maps and prefixes words. Let
$G_m$ be the group of coordinate-preserving block automorphisms at $m$,
viewed as arrows with empty word. Its elements permute ordinary doublets,
can exchange the members of each, and fix the singletons.

At type $\alpha_1\ldots\alpha_d t$ an entity $X$ at $n$ assigns to
$(f,w):n\to m$ a subset $X_{f,w}$ of the product of the already constructed
argument domains at $m$. For $d=0$ it assigns a truth value. Require both
of the following.

- A single countable set of source individuals pins the rows: at fixed
  target and word, maps agreeing there have the same row.
- For each $\pi\in G_m$, $X_{\pi f,w}=\pi[X_{f,w}]$, with $\pi$ acting
  on the tuples by their typed transports.

Transport is precomposition. The image of a pin pins the transported
profile, and postcomposition preserves its symmetry. At the identity the
symmetry law makes each $\pi\in G_m$ an automorphism of the local typed
structure. For a lambda term, equal maps on the union of its parameter
pins at the same target and word transport the parameters equally as whole
entities. Its row is therefore pinned. The action of $G_m$ on the body
gives its equivariance, also for quantifiers and modal formulas. This
establishes term closure for C. Equality of relational entities is
agreement of their continuation rows on all target tuples.

## Why all admitted families have joins

At $n$ let $A$ be an admitted family of relations of one type and put
$E=A_{\mathrm{id},\epsilon}$. Enlarge a pin $N$ for $A$ to contain every
partner of its elements and every singleton block at $n$. There are only
countably many coordinates, so $N$ stays countable. If $\pi\in G_n$ fixes
$N$ pointwise, then $\pi[E]=E$ by pinning and equivariance.

For $(f,w):n\to m$ set
\[
 J_{f,w}=\bigcup\{X_{k,w}:X\in E,\ k:n\to m,\ k|_N=f|_N\}.
\]
This profile has pin $N$. Postcomposing by an automorphism of $m$ permutes
the eligible maps bijectively and transports their rows, giving equivariance.
The choice $k=f$ shows that $J$ is an upper bound of $E$.

Let $Z$ be any upper bound, with pin $T$, and consider a contribution
$X_{k,w}$ in the displayed union, with pin $L$ for $X$. Close $T$ and $L$
under partners. Choose $\pi\in G_n$ fixing $N$ pointwise and moving all
doublets of $L$ outside $N$ off $T$. There are $\aleph_1$ ordinary doublets
in every coordinate, and only countably many to avoid. Prescribe $r:n\to m$
on $T$ as $f$, and on $\pi[L]$ as $k\pi^{-1}$. On the overlap these
prescriptions agree, since the overlap lies in $N$ and $k|_N=f|_N$.
Their domains are unions of blocks, so extend them to a block-respecting
map on the remaining blocks. Now $\pi X\in E$ and
\[
 X_{k,w}=X_{r\pi,w}=(\pi X)_{r,w}\subseteq Z_{r,w}=Z_{f,w}.
\]
Hence $J\le Z$. This argument applies at every stage and every relational
type, including $t$, and proves necessary Boolean Completeness.

## Why Barcan and Atomlessness hold

Suppose a property has a witness at $(f,w):n\to m$. Close a pin for the
property under partners. Replace $f$ by a map $f'$ agreeing on this pin
and having a block-respecting right inverse $s:m\to n$. To do so, in each
coordinate reserve a fresh source doublet for each target block. Map it
bijectively onto a target doublet or constantly onto a target singleton.
There are enough fresh doublets even after the countably many blocks of
the pin have been assigned. Select the inverse on each target doublet and
one preimage per singleton. Fill the other source blocks arbitrarily.
Thus every typed target entity lifts along $(f',\epsilon)$ by transport
along $(s,\epsilon)$. It also lifts along an identity-map word $w$: on
words with suffix $w$ put its rows after removing $w$, and use empty rows
on the other words. This preserves the pin and symmetry. Factor $(f',w)$
into these two arrows. The property has the same row at $(f',w)$ as at
$(f,w)$, so its witness comes from a current entity, giving ordinary Barcan
at all types and stages.

For any nonzero proposition fix a nonempty row and a pin. In a doublet
outside the pin, the map can either separate the two members or identify
them while its target, word and values on the pin stay fixed. The test
that their images differ is pinned by the doublet and is equivariant under
every target automorphism. It divides the proposition into two nonzero
parts, proving necessary Atomlessness.

## Inextensible Comprehension

Fix $X$ at stage $n$, put $E=X_{\mathrm{id},\epsilon}$, and enlarge a
countable pin $N$ of $X$ to contain whole blocks and all source singletons.
The group fixing $N$ pointwise preserves $E$. Say a map embeds a union
of blocks when its restriction is injective and sends distinct blocks
into distinct blocks. A singleton is allowed to map to one member of an
ordinary doublet.

Define a relation $Y$ with empty rows on nonempty words. At $(f,\epsilon):n\to m$
put into its row every $t\cdot a$ such that $a\in E$, a countable union of
blocks $C\supseteq N$ pins the tuple $a$, and $t:n\to m$ agrees with $f$ on
$N$ and embeds $C$. Here and below maps without specified words have the
empty word. This row rule is pinned by $N$ and equivariant on the left. At
the source identity such a $t|_C$ extends to a source block automorphism
fixing $N$: singletons have already been fixed, and each remaining doublet
is carried bijectively onto a distinct doublet. It follows that $Y$ and
$X$ have exactly the same present members.

We show $hY$ is weakly inextensible after any $h:n\to m$. Let $Z$ be a
tester at $m$ which necessarily accepts every member of the present
$Y_h$. If a member $b$ occurs in $Y_{gh}$, both words are empty and
$b=t\cdot a$ for $a,C,t$ as above, with $t|_N=gh|_N$. Since $gh$ embeds
$N$, $h$ does also. Choose a pin $P$ for $Z$. Extend $h|_N$ to an
embedding of $C$ by mapping the additional ordinary doublets to fresh
doublets at $m$ outside the blocks meeting $P\cup h[N]$. No further source
singletons occur. Extend this prescription arbitrarily to an arrow $u$;
then $c=u\cdot a\in Y_h$. Let $g'$ agree with $g$ on all blocks meeting
$P\cup h[N]$, and on the fresh doublets prescribe $g'u=t$ on $C\setminus N$.
The prescriptions extend to a block-respecting map, with $g'u=t$ on all of
$C$. Thus $g'\cdot c=b$. By the tester hypothesis $b$ lies in $Z_{g'}$,
and $Z_{g'}=Z_g$ by pinning. This proves the required necessary inclusion.
The argument covers every word: if the composite has nonempty word its
$Y$-row was empty. Therefore $Y$ is an inextensible coextension at each
stage, giving necessary Inextensible Comprehension.

## Weak rigidity, rigidity and powers

For a set $E$ of current tuples and a countable union $P$ of source blocks
containing every source singleton, write
\[
 B_P(E)_{f,w}=
 \bigcup_{t|_P=f|_P}(t,w)[E],
\]
where $t$ has the same source and target as $f$ and the image uses typed
transport on tuples. This is a profile pinned by $P$; a target
automorphism bijectively postcomposes the eligible maps and transports
their images.

**Weak rigidity persists.** Suppose $F$ is weakly rigid, $P$ pins $F$,
and $E$ is its present extension. Then $F=B_P(E)$. For every eligible
$t$ weak persistence puts $(t,w)[E]$ into $F_{t,w}=F_{f,w}$. Conversely,
$B_P(E)$ necessarily accepts every current member of $E$, so weak
inextensibility gives $F\le B_P(E)$.

Indeed any such $F$ is rigid. After an arrow $h$, persistence follows by
postcomposing a witness $t$ to membership in $B_P(E)_h$: its composite with
$g$ still agrees with $gh$ on $P$. For weak inextensibility of $hF$, let
$Z$ necessarily accept all current $F_h$-members and take any tuple in
$F_{gh}$. This tuple is the image of $a\in E$ along a map $t$ agreeing with
$gh$ on $P$, at their common composite word. Take a countable block-closed
pin $C\supseteq P$ for $a$. As in the preceding factorization, extend $h|_P$
by sending the extra doublets of $C$ bijectively to fresh ordinary doublets
off the blocks meeting $h[P]$ or the pin of $Z$. This gives a new first
arrow $u$ with the word of $h$; no assumption that $h$ embeds $P$ is needed
here. Adjust the second map $g$ on these fresh doublets only, retaining its
word, to make $g'u=t$ on $C$. The intermediate tuple $u\cdot a$ belongs to
$F_h$. Its $g'$-image is the prescribed tuple, and $Z_{g'}=Z_g$. This proves
weak inextensibility at every arrow. Consequently necessary Tame Rigidity
holds.

We will also use the converse construction. If $E$ is closed under every
empty-word source endomap fixing $P$ pointwise, $B_P(E)$ has present
extension exactly $E$. It is weakly persistent by the defining union.
For weak inextensibility, use the just-given factorization at the identity
arrow: it produces an intermediary $u$ fixing $P$, so $u\cdot a$ lies in
$E$ by the closure assumption. Thus $B_P(E)$ is weakly rigid, and hence
rigid by Tame Rigidity.

**Testing the power property.** Let $F$ be rigid and let $Z$ necessarily
hold of every current rigid subrelation of $F$. Choose $N$ as above to
pin both $F$ and $Z$, and put $E=F_{\mathrm{id},\epsilon}$. At a given
$h:n\to m$ consider any rigid $X\le hF$, with row $E'$ at $m$. Enlarge
a pin $T$ of $X$ to a countable union of blocks containing all singletons
of $m$. We construct a rigid $Y\le F$ and an arrow $j$ whose map agrees
with $h$ on $N$, with the same word, such that $jY=X$.

Take a countable union $D$ of target blocks containing $T\cup h[N]$.
Choose a countable union $C\supseteq N$ of source blocks, adding a fresh
doublet for each block of $D$ in the same coordinate. Define $j$ to agree
with $h$ on $N$ and send each reserved doublet onto its assigned block.
Outside $C$ choose a block isomorphism onto the complement of $D$.
The complements in each coordinate still consist of $\aleph_1$ ordinary
doublets. The map part of $j$ is split epic, via a section on the reserved
doublets and the ordinary inverse outside $D$.

For every such split epimorphism the current row of $B_P(A)$ at $j$ is
$j[A]$, whenever $A$ is closed under the endomaps fixing $P$. Indeed for
$t|_P=j|_P$ use an endomap $u$ equal to the identity on $P$ and to the
chosen section of $j$ composed with $t$ off $P$. Since $P$ is a union of
blocks this is allowed. Then $ju=t$ with $u$ taking the empty word. Apply
this first to $F=B_N(E)$: weak persistence makes $E$ closed under the
indicated maps, and $F_j=j[E]$. Since $jF=hF$ as whole profiles by
pinning, $E'\subseteq j[E]$.

Set $A=\{a\in E:j\cdot a\in E'\}$. It has $j[A]=E'$ and is closed
under every source endomap $u$ of empty word fixing $C$ pointwise.
To see this, define $v$ at $m$ to fix $D$ pointwise, and off $D$ use
$v(jx)=j(ux)$; this is well-defined and block-respecting by the
isomorphism on the complements. Then $ju=vj$ and $v$ fixes $T$. By
weak persistence and pinning $u[E]\subseteq E$ and $v[E']\subseteq E'$,
proving closure. Hence $Y=B_C(A)$ is rigid. It is below $F$ since each
map with its specified restriction on $C$ has the specified restriction
on $N$, and $A\subseteq E$. At $j$ its current row is exactly $j[A]=E'$.
Both $jY$ and $X$ are rigid, so their current coextension gives entity
identity. Test each against the other: persistence gives boxed membership
for each current common member and weak inextensibility gives both inclusions.

The tester therefore accepts $X$ at $j$, hence also at $h$ by pinning.
This proves weak inextensibility of the rigid power property of $F$. Its
persistence follows because both rigidity and relation inclusion persist.
Tame Rigidity now makes the power property rigid. As weak rigidity and
rigidity coincide throughout the cone, the weak power property has the
same profile and its schema holds as well. These statements hold at every
stage, giving necessary Rigid Power and necessary Weakly Rigid Power.

## The two modal separations

At stage $0$ put $P(f,w)$ iff the target $n$ is below $1$. For every true
$q$ the coordinate inclusion $u:0\to1$ witnesses $\Diamond_{\ne}q$ but
falsifies $P$, as in the [original return-map proof](integer-stages-paired-individuals-glued-constants.html).
Indeed, given a true $r$ at $1$, take a doublet in coordinate $1$ outside
its pin. Return by fixing the ordinary elements and sending the new
singleton to that doublet; then $vu=1_0$. Go forward again by collapsing
the doublet onto the singleton. The resulting loop $xv$ fixes the pin for
$r$, giving $q$ at $vu$ and $r$ at $xv$. Thus $P$ is not two-hat
necessary.

At each target stage define a property $Y$ of propositions. Its row is
all propositions if $n<1$, and otherwise those admitting a countable pin
omitting the singleton in coordinate $1$. This uses existence of an
ordinary pin, independently of any optional enlargement used in the join
proof. It is a target-only row with empty source pin; target automorphisms
fix the distinguished singleton and carry pins to pins, so it is equivariant.
At $n\ge1$, the local proposition on empty-word endomorphisms that send
this singleton to itself is equivariant and has no pin omitting it.
Changing only that one input at the identity proves the latter claim.
Consequently $(\forall z\,Yz)=P$ as proposition entities.

For each current proposition $z$, expand its pin to a countable $N$
including the partners of all its members in coordinate $1$. Use for $q$
the empty-word endomorphisms of $0$ **injective on $N$**. This is a true
pinned proposition invariant under left target automorphisms. If
$\Diamond_{\ne}q$ at $k$, then $\Diamond q$ there, so some continuation
makes the composite injective on $N$. It follows that $k$ is injective on
$N$. A coordinate-$1$ member of the pin and its distinct partner cannot
then be sent into the target's singleton block. Hence $k$ carries a pin
of $z$ to one omitting that singleton whenever it exists. This gives
$\hat{\hat\Box}(Yz)$, hence $\Box_5(Yz)$, for every current $z$. The
Barcan formula for $\Box_5$, a theorem of C, gives $\Box_5P$.

For the other separation let $D$ select targets with a singleton at
coordinate $0$ and let $a$ be that singleton at $0$. Take for $q$ the
empty-word endomorphisms of $0$ fixing $a$, an equivariant true test.
If $k:0\to m$ has $m<0$, then $k(a)$ lies in a doublet. At $m$ the
test that an endomorphism with empty word separates that doublet is true
and equivariant. Any return $v$ with $vk\in q$ collapses the doublet to
$a$; no further continuation can satisfy the separation test. Thus
$\neg\Diamond_{\ne}q$ at $k$, giving $\hat{\hat\Box}D$. For each true $r$
at $0$ take an ordinary coordinate-$0$ doublet off its pin, send $a$ into
that doublet on an arrow to $-1$, and return by collapsing the doublet to
$a$. The loop fixes the pin for $r$, so $r$ is possible after this arrow
to a target falsifying $D$. This refutes $\Box_{\ne}D$.

Translation of all stages and coordinate labels by one respects the
automorphism groups and every domain condition. The two separations hold at
every stage. For the same reason the empty-parameter case of Logical
Necessity holds. For one propositional constant, or any set-sized purely
relational signature, use the [last-letter assignment](integer-stages-paired-individuals-glued-constants.html)
at stage $0$. All assigned profiles are equivariant and this is preserved
on each final-letter sector. For each pure matrix and ordered list of
variable types use the same realizing tuple across all choices of matching
names; each constant then uses only countably many witness pins.

OpenAI Codex (GPT-6), prompted by Daniel Kodsi, constructed the symmetric
variation on 26 November 2026, adapting the two models cited above.

## Second-Order Analytic Necessitism at every type

Consider the [symmetric integer-stage model](symmetric-integer-paired-stages.html). At every stage it satisfies Second-Order Analytic Necessitism, hence also Analytic Necessitism. The individual and relational instances have different explanations.

Suppose first that at some stage the individuals supported a [real number structure](../index.html#background/arithmetic) $(N,0,S,X,E)$. Take a countable set $P$ that pins its parameters, contains zero, contains the partners of all its elements, and contains every singleton block at the stage. Let $H$ consist of the block automorphisms fixing $P$ pointwise. Pinning and target equivariance imply that $H$ preserves all four current relation rows. The only individuals fixed by every element of $H$ belong to $P$, since an exchange within any ordinary doublet outside $P$ moves each of its members.

The standard iterates of $0$ under the current successor are individually fixed by $H$, by uniqueness of the successor. Their set $B$ is therefore contained in $P$. Every subset $U$ of $P$ is an admitted current individual property. At an arrow $(f,w)$ take the row $f[U]$. This profile is pinned by $P$ and is equivariant under all target automorphisms. In particular $B$ itself is an admitted current property containing zero and closed under successor, so the induction clause gives $N=B$ in current extension. These iterates are pairwise distinct by the Peano clauses. Every $h\in H$ fixes each number. For any current real $x$, preservation of $E$ then gives $x$ and $h x$ the same number members. Extensionality gives $x=h x$. Thus all reals also belong to $P$. Fullness would require a distinct real for each of the uncountably many subsets of $B$, although $P$ is countable. No stage supports a real number structure at type $e$, so the possibility antecedent there is false.

Now fix any relational type $\tau=\alpha_1\cdots\alpha_d t$, including $t$. For each $A\subseteq\mathbb Z$ and each stage $n$, take the entity $a_A^n$ whose row on a map into $m$ is the entire argument domain at $m$ for $m\in A$, and the empty row otherwise. These profiles are equivariant and have empty pin. Every arrow $n\to m$ carries $a_A^n$ to $a_A^m$. Distinct labels give distinct entities at every stage because every stage is reachable and every argument domain is nonempty. This gives a fixed family of continuum-many labels at type $\tau$.

For any external set $T$ of $k$-tuples of labels, let $R_T^n$ have at each arrow into $m$ the row consisting of exactly those labelled tuples $(a_{A_1}^m,\ldots,a_{A_k}^m)$ indexed by $T$. This too is an equivariant, empty-pinned profile. Every arrow takes its current row onto its future row and carries the whole profile to its namesake at the target. The same holds after each further arrow. Onto transport of the rows gives persistence and weak inextensibility directly: any future member is the image along the very arrow in question of a current member, so every tester necessarily accepting the current members accepts that future member. This proves rigidity. This is the codomain construction of the map's [full-continuum argument](https://github.com/zwlgzwlg/Logical-Maps/blob/4bb9287187ed7cb09567eb3a6302cb896c986ec4/logical-maps/topics/classicism/arguments/analytic-necessitism-full-continuum.yaml), here available at every relational type.

Choose disjoint labels for the standard naturals and their powerset. Use these profiles for the natural numbers, the reals, successor and membership, with the zero label as zero. At every target the resulting structure is isomorphic to the full standard number-and-set structure. Its labels remain distinct under every continuation and its relations are rigid. For each $k\ge1$ let the row of the power at a map into $m$ consist of all $R_T^m$ as $T$ ranges over subsets of the $k$-tuples of numbers and reals. This property has empty pin, is equivariant, and again has bijective transport on its current members, hence is rigid. Every current relation at $m$ restricts to some subset $T$ on the labelled tuples, where $R_T^m$ represents it. Thus every arity has a represented power, simultaneously at every stage. This proves the claimed schema.
