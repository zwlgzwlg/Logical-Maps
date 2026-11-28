# Necessary Atomicity without Transversal

Every nonzero relation has an atom below it, at every point and every
relational type. Nevertheless there is no transversal of coextension
even for properties of individuals. The finite bound on an arrow's
domain supplies the atoms. Partial identities obstruct a transversal.

## The action

Partition a countable set $A$ into countably many infinite classes of
an equivalence relation $E$. Let $G=\operatorname{Aut}(A,E)$ and add
a point $*$ fixed by $G$. A coefficient is a partial injection
$f:A\rightharpoonup A$, extended to $A\cup\{*\}$ by sending $*$ and
all undefined inputs to $*$. An arrow $(f,k,w)$ has tag
$k\in\mathbb N\cup\{\infty\}$ and free word $w$. When $k$ is finite
require $|\operatorname{dom} f|\leq k$. Compose coefficients and words
and take the minimum of the tags. The composite of partial injections
has domain of size at most either finite rank bound. The identity is
$(1,\infty,\epsilon)$. Write $\pi$ for $(\pi,\infty,\epsilon)$ when
$\pi\in G$. There is one object, with individual domain $A\cup\{*\}$.

At a relational type a profile assigns a subset of the target argument
tuples to each arrow. It must satisfy two conditions. Some finite
$P\subset A$ and $b\in\mathbb N$ determine its row from $f|_P$,
$\min(k,b)$ and $w$. For $\pi\in G$, the row at $\pi h$ is the image
of the row at $h$ under the typed transport by $\pi$. Transport is
precomposition. Agreement of two arrows on $P$, the truncated tag
and the word persists when both are followed by the same arrow.
Consequently they transport an entity with that pin and bound to the
same whole entity. The image of the live part of $P$ pins a transported
profile. Permutations are automorphisms at every type by equivariance.
Abstraction uses the common pin and bound of its finitely many
parameters; its row is evaluated on all arguments at the target.
This proves term closure, including quantification. Two different
profiles differ at some row and target tuple, as required for identity
in an action model. Top interpretations of the names are preserved.

## Atoms

Suppose $X$ is nonzero at an arrow $(f,k,w)$ and tuple $\bar y$.
Take its pin $P$ and bound $b$. If $k<b$, keep $k'=k$. Otherwise
take any finite $k'\geq\max(b,|P\cap\operatorname{dom}f|)$.
Build a partial injection $f'$ agreeing with $f$ on $P$, of rank
exactly $k'$. Fill the remaining domain and image places with fresh
points. Then $X$ still holds at $h'=(f',k',w)$ and $\bar y$.

The orbit of the pair $(h',\bar y)$ under simultaneous postcomposition
and tuple transport by $G$ is itself an admitted relation. Its pin is
$\operatorname{dom} f'$ and its bound is $k'+1$. At tag $k'$, if the
values on those $k'$ inputs are all live and distinct, they exhaust the
domain, so matching them determines the entire coefficient. Other tags
and other words need no further information. The orbit lies below $X$
by equivariance, and any nonempty admitted subrelation contains the
whole orbit by the same equivariance. This proves Atomicity at every
relational type. Since this is a pure closed schema in a one-object
model it holds necessarily.

## The missing transversal

Suppose $\Phi$ selects one property of individuals from each current
coextension class. Take a finite pin $P$ of $\Phi$. Choose an
$E$-class $C$ disjoint from $P$ and some $c\in C$. The profile with
row $[f(c)]_E$ when $f(c)$ is live, and empty row otherwise, is
admitted with pin $\{c\}$. Its current extension is $C$. Let $Y$
be the unique selected representative of that extension.

Any $h\in G$ fixing $P$ pointwise preserves the whole $\Phi$: the
arrows $g$ and $gh$ agree on $P$ and on both other coordinates. If
$h$ also preserves $C$ setwise, $hY$ is selected with the same
current row, whence $hY=Y$. Enlarge a pin $S$ of $Y$ to contain $P$.
Within each infinite class choose such an $h$ moving $S\setminus P$
off $S$. The set $hS$ is another pin of $Y$, with the same tag bound.

Let $f$ be the partial identity on $S$, using tag $\infty$ and empty
word. It agrees with the identity on $S$, so $Y_f=C$. It sends every
member of $hS$ outside $P$ to $*$. A permutation $\pi$ fixing $P$
and exchanging $C$ with a fresh class therefore makes $\pi f$ agree
with $f$ on the second pin. Pinning gives $Y_{\pi f}=C$, whereas target
equivariance gives $Y_{\pi f}=\pi C\ne C$. This rules out $\Phi$.

Relational Choice fails as well. Use the invariant serial current
relation requiring each $x\in A$ to choose another member of $[x]_E$,
and $*$ to choose itself. A functional selector with a finite pin
cannot choose for $x$ from a fresh class: an automorphism fixing the
pin and $x$ moves the selected classmate. Transversal Choice also fails:
in each class disjoint from its pin a purported transversal of $E$
would have to be invariant under all permutations of that class.
An invariant set of current tuples gives an admitted constant row on
all arrows. Extend $E$ by the singleton class of $*$.

Both individual and propositional domains are infinite. The live-input
tests $p_a(f,k,w)\leftrightarrow a\in\operatorname{dom} f$ already give
infinitely many different propositions. At either counting type the
set of denotations of standard closed Frege numerals is invariant
under $G$ and gives an admitted inductive current row. All current
Frege numbers are therefore standard numerals, and none counts the
entire infinite domain. This proves both necessary Infinity Axioms.

## Singleton individuals and Logical Necessity

Make $A$ a set of auxiliary sites and use a singleton individual domain.
At propositional type the distinct live-input tests $p_a$ still represent
every $a\in A$. Transport by $\pi\in G$ gives $\pi p_a=p_{\pi(a)}$.
For the class of $c$ use the property with row
$\{p_z:z\mathrel E f(c)\}$ when $f(c)$ is live, and empty otherwise.
It has pin $\{c\}$. The two-pin proof above applies verbatim to its
selected representative, now a property of propositions. The relation
of being different codes in the same class gives the classmate
obstruction to Relational Choice, with all noncodes related to themselves.
For Transversal Choice use the equivalence classes of the codes and a
singleton class for each noncode. These current relations are invariant.
The orbit proof of necessary Atomicity and the propositional infinity
calculation are independent of the individual domain.

The free-word coordinate lets us add Logical Necessity for any fixed
set-sized signature. Consider the complete pure pointed theory of this
one-object model together with all instances of Logical Necessity.
For a finite list of these instances, use the dual existential form.
For each pure matrix and tuple of names in the list whose existential
closure holds, choose a witnessing tuple and a fresh final letter.
For a relational name on that tuple, prescribe its row on words ending
in that letter by the whole witness profile on the word with that final
letter removed, at the same coefficient and tag. Thus transport along
the identity coefficient with the new one-letter word sends the name to
the witness. Other entries may be bottom. Distinct final letters give
disjoint prescriptions. There are only finitely many witnesses for
each name in this interpretation, so a finite union of their pins and
the maximum of their tag bounds suffice. Individual names are forced
to the sole individual. Conversely, any possible named instance has
a current witness, since at every arrow the transported assignment is
an assignment in the same object. All pure sentences keep their original
truth values. Henkin compactness now gives one pointed model satisfying
the full theory. The necessity of Atomicity and the failures of all
three forms of selection recorded here are pure statements in that theory.

## Analysis and a missing countable join

Take the alphabet countably infinite. At each relational type and for
each set $S$ of letters let $L_S$ have full tuple row when the word is
nonempty and its leftmost letter belongs to $S$, and empty row otherwise.
These entities are invariant under the site automorphisms. After any
word $w$ their images are still pairwise distinct: a further one-letter
prefix $\ell$ tests exactly whether $\ell\in S$.

Choose distinct labels for the ordinary numbers and their powerset.
At each arrow give the number predicate, successors, real predicate and
membership their exact transported rows on these labels. The rows may
depend on the word and require no site pin. The labels are still
distinct and the current structures have the ordinary membership
relation. Every subset of the labelled numbers at that arrow is the
restriction of an admitted property, by the same construction. Thus
the structure is necessarily real; the exact image description, which
continues to hold after every transport, makes its relations rigid.
For each arity and each external subset of the corresponding tuples
of labels use the relation with precisely its successive image rows.
The family of all these relations has a predicate whose row at a word
consists of precisely their transported entities. The predicate has
empty pin, exact images and necessarily distinct instances. At each
arrow every current relation on the labels is represented by the
relation for its tuple subset. This supplies every required represented
power. At individual type in the moving-individual model no Peano
structure is possible: a common finite pin of the structure fixes all
its standard successor iterates individually, but only the points of
the pin and $*$ are individually fixed by its pointwise stabilizer.
At singleton individual type even two distinct numbers are impossible.
This verifies Second-Order Analytic Necessitism in both versions.

Arithmetic Necessitism also holds at every counting type. The invariant
current set of closed standard Frege numeral denotations is inductive,
so it contains every current Frege number. Every transport takes each
standard numeral to that same numeral. Under the necessary Peano guard
the numerals are distinct, and every future number is the image of one
of them. This is hereditary and gives rigidity of the number predicate.

For each external $n$ take the proposition true exactly at tag $2n$.
It has empty pin and cutoff $2n+1$. The current set of these propositions
and the graph sending each to its $n$th Frege numeral counted at $t$
are both invariant and hence admitted as current rows. The complements
of the individual odd-tag propositions are all upper bounds. A least
upper bound would have to hold at every even tag and fail at every odd
tag. Taking the empty coefficient and empty word at all sufficiently
large finite tags contradicts its finite cutoff. Thus unboxed Boolean
Completeness at $t$ and Countable Boolean Completeness both fail.

## Revised Mathematical Possibilism without Transversal

Use a singleton individual domain. Take $\aleph_1$ equivalence classes
of $\aleph_1$ auxiliary sites each, and allow a countable source pin.
Keep the finite cutoff bound and the same free-word coordinate. The
term closure proof is unchanged, since finite unions of countable
pins are countable. A countable pin still misses entire classes, and a
countable set in any class can still be moved off itself pointwise
outside a prescribed countable pin. The partial identity on the first
pin is an arrow at tag $\infty$, even when that pin is infinite. Thus
the scalar class obstruction to Transversal remains valid, as do the
choice counterexamples, the word-coded continuum, and the missing
even-tag join.

Suppose $Z$ is a set of current tuples invariant under all class
automorphisms fixing some countable $P$ pointwise. Use row $\pi[Z]$
when $f|_P=\pi|_P$ for an automorphism $\pi$, and the empty row
otherwise. Any two matching permutations differ on the right by one
fixing $P$. This gives an equivariant profile pinned by $P$, with
current row $Z$. In particular, for any countably many whole entities
there is one stabilizer fixing them all: take the union of their pins.
Every external set of tuples of these entities is available as a
current row.

For the ordinal bound use the
[singleton-individual table argument](two-colour-multisets-with-a-word-guard.html).
The entities given by a single finite extensional table on individual
orders and fields at every arrow form a finite invariant set. It is
therefore available as a current test. Zero and successor preserve the
test. A rigid family of members of this finite set is the union of
their tuple-haecceities, by persistence and weak inextensibility.
Its ordinal limit consequently uses one such table at every arrow.
The inexact ordinals are contained in this finite set.

For an externally infinite Boolean algebra carrier choose a countably
infinite subset $Y$. All subsets of $Y$, their graphs, and comparisons
with the finite ordinal bound are current rows by the common-pin result.
Thus $Y$ is strictly larger than the ordinal benchmark. Any internally
strictly smaller subset of $Y$ is finite, since an external bijection
from an infinite subset onto $Y$ would be admitted. For a finite
subset all its subcollections are coded on a finite subset of $Y$
with their membership graph. Hence $Y$ is power-closed. Only externally
finite Boolean algebras can satisfy revised smallness.

At tag zero the empty partial injection is the only coefficient.
Specifying this tag and one word gives a scalar atom, by postcomposition
equivariance or simply because it is a single arrow. The interval below
the union of $j$ such atoms is the Boolean algebra with $j$ atoms. Its
order isomorphism with any given finite Boolean algebra is a finite
current graph with a common pin. Use bottom for the one-element algebra.
This proves revised Mathematical Possibilism. It holds with Logical
Necessity by the finite gluing and compactness argument above, at a
point that still fails Transversal at propositional argument type.
