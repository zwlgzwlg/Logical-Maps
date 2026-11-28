# Graded maps with free words and glued constants

For each set-sized signature $\Sigma$ this one-object C action model satisfies
Logical Necessity, necessary Strong Actuality, necessary Self-Atomicity at all
relational types, necessary Countable Boolean Completeness and necessary Barcan
at every type. An admitted family of propositions lacks a join, and a nonzero
proposition has no atom below it. Every atom is strong. The universal
individual property is rigid, yet its family of rigid subproperties gains a
member, refuting Rigid Power. The same witness refutes Weakly Rigid Power.

## The action model

Let $\kappa=\max(\aleph_0,|\Sigma|)$ and let $A$ be the initial ordinal of
cardinality $\kappa^+$. There is one object with individual domain $A$. An arrow
is a triple $(f,n,w)$, where $w$ is a finite word on an alphabet of size
$\kappa$, $n$ is a natural number, and $f:A\to A$. At grade $n=0$ require
$f=\mathrm{id}_A$. At every positive grade allow all maps. Words are arbitrary
at every grade. Write $\epsilon$ for the empty word. Composition and identity are
\[
 (g,m,v)(f,n,w)=(g\circ f,m+n,vw),\qquad
 1=(\mathrm{id}_A,0,\epsilon).
\]
Individuals travel by $f$. Recursively, an entity $X$ of type
$\alpha_1\ldots\alpha_k t$ assigns to every arrow $h$ a subset $X_h$ of the
current product $D_{\alpha_1}\times\cdots\times D_{\alpha_k}$. For $k=0$ the
product has one member, so each row is a truth value. There must be a single
$S\subset A$ of size at most $\kappa$ such that at any fixed grade and word,
maps agreeing on $S$ give the same row. Call $S$ a pin. Define transport by
$(hX)_u=X_{uh}$. If $S$ pins $X$, then $f[S]$ pins $(f,n,w)X$.
Also, arrows with the same grade and word whose maps agree on $S$ transport
the *whole entity* $X$ equally, as may be seen by following both by any continuation.
An individual has its singleton for a pin in this latter sense.

For a lambda term with parameters, take the union of the parameters' pins.
Arrows agreeing there at a fixed grade and word give the same transported
parameters. The body is therefore evaluated at the same object with the same
parameters for each possible argument tuple. This proves admission of the
lambda profile, including for quantified and modal bodies. Application uses
the identity row, and entity equality is equality of all continuation rows on
all target tuples. This gives the action semantics of C. Order between two
relations is inclusion of every row. Every external subset of the current
tuple product occurs as an identity row, for example by putting that same
subset at every arrow. Every closed pure sentence true at the one object
holds necessarily.

## Self-atoms and a true strong atom

Given $X\ne\bot$ of any relational type, choose an arrow $(f,n,w)$ and a tuple
$b\in X_{f,n,w}$. Intersect each row with $\{b\}$ at grade $n$ and word $w$,
and put the empty row at every other grade or word. The resulting $Q$ has the
same pin as $X$, is nonzero, and satisfies $Q\le X$. Whenever an arrow $h$
instantiates $Q$, its grade is $n$ and its word is $w$. A continuation $u$
for which $uh$ still has grade $n$ and word $w$ must have grade zero and the
empty word. The sole such arrow is the identity. Consequently $hQ$ has
exactly one tuple in its identity row and is empty elsewhere. Every entity
below it is bottom or equals it, so $hQ$ is an atom. This is Self-Atomicity;
the same argument applies to the empty tuple at type $t$. It holds necessarily.

The proposition true precisely at $1$ is admitted with empty pin and is a
true atom. After every nonidentity arrow it becomes bottom, since there is
no continuation returning that arrow to $1$. At every arrow it therefore
entails each proposition or its complement. This supplies a true strong
atom at the sole object and gives necessary Strong Actuality.

In fact propositional Atomicity fails. Let $B$ select precisely the grade-one,
empty-word arrows. For any nonzero $Q\le B$ with pin $S$, take a witnessing
map $f$ and choose $a\in A\setminus S$. Change $f(a)$ while fixing $S$ to
obtain a second witness. The admitted cylinder requiring the original value
at $a$ cuts $Q$ into two nonzero parts. Hence no atom lies below $B$. The
failure holds necessarily by the one-object pure semantics.

The same splitting test classifies the atoms at every relational type. If a
row at a positive grade contains a tuple, changing the map at a fresh
individual preserves that occurrence; testing the map's value there splits
the original relation into two nonzero parts. An atom therefore has only
grade-zero occurrences. Each grade-zero word has just one map, so the
single-word, single-tuple profile obtained from any such occurrence is an
admitted nonzero subrelation. The atom must equal it. Along any arrow this
profile becomes bottom or another single-word, single-tuple profile: a
continuation at grade zero can occur only after grade zero and the word
suffix cancels. Every atom is consequently a strong atom, necessarily.

The identity-only proposition vanishes after every proper arrow: neither a
positive grade nor a nonempty word can be cancelled to the identity. It
therefore guards $\Box_{\ne}p$ for each current truth $p$, as in the
[finite multiset model](finite-multisets-free-words.html).

## The Barcan Formula

First take $h=(s,n,w)$ with $s$ surjective. Every typed entity at its target
lifts along $h$. At $e$ this is surjectivity of $s$. At a relational type let
$T$ pin a target entity $B$. Choose a preimage of each element of $T$ and let
$T'$ consist of the chosen preimages. Prescribe a source profile $L$ by
\[
 L_{g s,m+n,vw}=B_{g,m,v}
\]
for every allowed continuation $(g,m,v)$. At each grade and word extend a
prescription to all maps agreeing with its index map on $T'$. Fill all
remaining cases with empty rows. Two prescriptions at the same grade and word
have the same $m$ and $v$, by cancellation. Agreement on $T'$ of their
composite maps implies agreement on $T$ of the postmaps, so their prescribed
rows coincide. This defines an admitted $L$ with pin $T'$ and $hL=B$.

Now suppose a property $R$ has a possible witness $b$ at $(f,n,w)$. Take a pin
$S$ for $R$. At grade zero $f$ is already the identity. At a positive grade
choose a surjection $s$ agreeing with $f$ on $S$, using the $\kappa^+$ remaining
inputs. The row of $R$ is identical at $(s,n,w)$. Lift $b$ along this arrow
to an actual witness $a$. It follows that
$\Diamond\exists x\,R(x)\to\exists x\,\Diamond R(x)$, the dual of Barcan.
Lambda abstraction permits arbitrary matrices and the proof applies at
every type. The one-object pure reduct therefore satisfies necessary Barcan.

## Failure of both rigid powers

Call a set of individuals small here when it has size at most $\kappa$. Let
$R$ be any current weakly rigid individual property, with actual extension
$D$. If $D$ is small, the tester with row $f[D]$ at $(f,n,w)$ is pinned by
$D$ and necessarily holds of every actual member of $D$. Weak inextensibility
of $R$ then bounds each row of $R$ by $f[D]$. If $D$ is large, take $a\in D$
outside a pin for $R$. For any positive-grade arrow and any desired value
$b\in A$, change its map at $a$ to $b$ while fixing its grade, word and pin.
Persistence of $R$ puts $b$ in the unchanged row. Thus at every
positive-grade arrow every old weakly rigid property has a small or a full row.

For each large $B\subseteq A$, let $H_B$ have row $B$ at every grade-zero
arrow and full rows at positive grades. This profile has empty pin and is
persistent. If a tester $Y$ necessarily holds of each actual $b\in B$,
its grade-zero rows contain $B$. At every positive grade, change the map
at a member of $B$ outside a pin for $Y$ to obtain each desired value.
Hence its positive rows are full, proving $H_B\le Y$ and thus weak
inextensibility. At grade zero $H_B$ transports to itself; at positive
grades it transports to $H_A=\top_{et}$. The same proof with $B=A$
shows that top is weakly rigid at every stage. Consequently each $H_B$
is fully rigid.

Define a tester of individual properties whose grade-zero rows accept all
properties and whose positive-grade rows accept exactly those with small or
full present extension at the target. This is an admitted profile with empty
pin. By the first paragraph it necessarily accepts each actual weakly rigid
subrelation of $\top_{et}$, and hence each actual rigid subrelation as well.
Choose a large proper $B\subset A$. At any positive-grade target the rigid
relation $H_B$ is a subrelation of top and the tester rejects it there.
The canonical weakly rigid and rigid power properties of top travel to those
same canonical properties at that target. The tester thus witnesses failure
of weak inextensibility for both powers. Top itself is rigid, so both native
power schemata fail. The closed pure failures hold at the sole object.

## Countable Boolean Completeness

Every current tuple set is an admitted identity row in this one-object
model. In particular the standard numerals form an admitted successor-closed
row, so induction exhausts the current numbers at each counting type. The
[countability argument for finite multisets](finite-multisets-free-words.html)
therefore makes each internally countable family externally countable.
The union of its pins has size at most $\kappa$ and pins the rowwise union,
its least upper bound. With a single object the verdict holds necessarily.

## Logical Necessity

We adapt the [simultaneous gluing construction](symmetric-surjection-products.html).
In the fixed pure model, call a $\Sigma$-sentence realizable when it is true
under some assignment to its constants. Choose one such assignment $J_i$ and
one distinct letter $i$ for every realizable sentence. There are at most
$\kappa$ sentences. Interpret the individual constants initially by distinct
values $a_c$. For each $i$ choose a surjection $s_i:A\to A$ with
$s_i(a_c)=J_i(c)$ for every individual constant, using the remaining
$\kappa^+$ inputs for surjectivity.

For a relational constant $c$ lift $J_i(c)$ along $(s_i,1,\epsilon)$ to a
profile $L_{i,c}$ by the preceding argument. On $(f,n,vi)$ assign $c$ the
row $(L_{i,c})_{f,n,v}$, using empty rows on the empty word and on unused
last letters. The union of the at most $\kappa$ pins of these lifts still has
size at most $\kappa$. Along $(s_i,1,i)$ every constant takes its prescribed
value, as can be checked for relational constants after each further
continuation. Consequently every realizable sentence is possible under the
glued interpretation. Conversely, any assignment produced along an arrow
is already an assignment at the sole object. Applying this to a pure matrix
with its free variables replaced by distinct matching names, and taking the
classical dual, gives
$\Box P[\bar c]\leftrightarrow\forall\bar x\,P[\bar x]$, including the
empty tuple. Logical Necessity is asserted at the designated identity.

## An admitted family without a join

Fix $d,b\in A$, distinct $a_i\in A\setminus\{d\}$, and distinct $c_i\in A$,
for $i<\kappa^+$. Let $p_i$ hold precisely at grade-one, empty-word arrows
whose maps satisfy $f(d)=c_i$ and $f(a_i)=b$. It is pinned by $\{d,a_i\}$.
Use the external set $\{p_i:i<\kappa^+\}$ as an identity row of an admitted
property of propositions. Thus the native Boolean Completeness principle
requires a least upper bound of this family in the admitted proposition algebra.

Suppose $L$ were such a bound with pin $S$. Choose $j$ with $a_j\notin S$.
Take two maps $f,f'$ agreeing on $S\cup\{d\}$, with
$f(d)=f'(d)=c_j$, $f(a_j)=b$, and $f'(a_j)\ne b$. At grade one and word
$\epsilon$, the first arrow belongs to $p_j$ and must belong to $L$.
The second belongs to the admitted cylinder of maps at that grade and word
with $f(d)=c_j$ and $f(a_j)\ne b$. The cylinder is disjoint from every $p_i$,
so its complement is an upper bound. Leastness excludes the second arrow
from $L$, contradicting agreement on $S$. Propositional Boolean Completeness
therefore fails, and the closed pure failure repeats at the sole object.

The graded construction and its separation were developed by OpenAI Codex
(GPT-6), prompted by Daniel Kodsi, on 26 November 2026. Two additional
OpenAI Codex agents independently reviewed the argument.

## Tame Rigidity in the unrestricted graded model

Let $F$ be weakly rigid, $E$ its current row, and $N$ any set of size at most $\kappa$ containing a pin of $F$. At an arrow $h$ form the union of $t[E]$ over all $t$ of the same grade and word that agree with $h$ on $N$. These rows form an admitted tester pinned by $N$ which necessarily contains each member of $E$. Weak inextensibility puts $F_h$ inside the union. Weak persistence and pinning give the other inclusion. This description of the rows also gives hereditary persistence: if $y=t z$ with $z\in E$ and $t$ agrees with $h$ on $N$, then $k y=(k t)z$ lies in the row for $kh$.

For hereditary weak inextensibility, fix $h$ and a tester pinned by $P$ which necessarily accepts every member of $F_h$. Take a continuation $k$ and $y\in F_{kh}$. In the union just proved write $y=d z$ for $z\in E$, with $d$ matching $kh$ on $N$ at the same grade and word. Take a pin $L$ for $z$ (the union of its argument pins). We construct arrows $h',k'$ of the same grades and words as $h,k$. The coefficient of $h'$ agrees with $h$ on $N$ and that of $k'$ agrees with $k$ on $P$, and their composite agrees with $d$ on $L$.

If both grades are positive, keep the prescribed values of $h'$ on $N$ and send the points of $L\setminus N$ injectively to fresh intermediate points outside $P\cup h[N]$. Keep $k'$ equal to $k$ on $P\cup h[N]$. At the fresh intermediate points send $h'(a)$ to $d(a)$. These partial prescriptions extend to arbitrary functions. If $h$ has grade zero, its coefficient is the identity. Enlarge $N$ to contain $P$ before taking the representation by $d$, and use the coefficient of $d$ for $k'$. If $k$ has grade zero, keep its identity coefficient and take the coefficient of $d$ for $h'$. The grade-zero convention also covers the case of two zero grades. The word factors always retain the original split of the concatenation.

Now $h'z\in F_h$ and $k'h'z=d z=y$ by the whole-entity pin of $z$. The tester at $k'$ accepts $y$ and its row at $k$ is the same. Thus $hF$ is weakly inextensible. The argument applies at every arrow and every point, proving necessary Tame Rigidity.

A relation with the desired extension only at the identity is inextensible because all its proper transports are bottom. Constant-row well-orders are necessarily well-orders. Every carrier is infinite, and at $e$ and $t$ the standard numeral cut gives the necessary Axioms of Infinity. The earlier power tester, which concerns the universal bound, also refutes both rigidity predicates. The infinite individuals provide a small complete presentation of the Cantor regular-open algebra, while each nonzero scalar interval has a countably complete evaluation ultrafilter. The regular-open algebra has no such ultrafilter. [The scalar interval calculation](partitioned-graded-maps-with-free-words.html)
