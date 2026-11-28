# Free words with supported flips of individual pairs

**Theorem.** Logical Necessity, necessary Rigid Comprehension, necessary
Rigid Power, ordinary Barcan at every type and necessary Strong Actuality
can hold together while Relational Choice and Transversal Choice fail.
The same witness refutes ordinary and Modal Well-Ordering. A signature with
one propositional constant suffices.

## The action model

Take one object with arrows the free monoid $M$ on an infinite alphabet.
Write $vh$ for the composite that first follows $h$. Its individuals are
$A=\omega_1\times\{0,1\}$, with pairs $\{(i,0),(i,1)\}$. Every arrow
acts as the identity on individuals. A separate group $G$ acts by all
independent flips within the pairs. This group fixes the words. A countable
atom support for an entity is a set of individuals whose pointwise
stabilizer in $G$ fixes the entity.

Recursively, for a relational type $\tau=\alpha_1\ldots\alpha_k t$, let
$T_\tau=D_{\alpha_1}\times\cdots\times D_{\alpha_k}$. An entity is a
profile of arbitrary subsets $F_v\subseteq T_\tau$, one for each word,
which as a whole has countable atom support. Put
$(gF)_v=g[F_v]$ for $g\in G$ using its componentwise action on tuples.
Arrow transport is $(h\cdot F)_v=F_{vh}$. It commutes with the group
action. In particular $D_t=\mathcal P(M)$, all its members having empty
atom support. Denotations of terms belong to these domains: $G$ preserves
application, equality, truth, quantification over the indicated invariant
domains and arrow composition; the union of the finitely many parameter
supports therefore supports the full profile of a lambda. The current
row of a relational entity has its support too. Conversely any supported
subset of the local tuple domain occurs as a current row, for instance in
a constant profile. This gives a C action interpretation.

The free monoid uses the usual
[gluing of constants](full-free-monoid-glued-constants.html).
The group action on individuals is a symmetry imposed on admitted profiles;
the words themselves carry no atom movement.

## Logical Necessity and the signature

A pure sentence has the same truth value at every word since there is one
object. For each realizable pure matrix and ordered list of variable types
choose one witnessing tuple at that object. There are countably many such
choices. Use an alphabet of size at least $\max(\aleph_0,|\Sigma|)$, supplying a
separate last letter for each instance with distinct matching constant
names. Interpret a participating relational constant on a word $v j$ by
the row at $v$ of its witness for that matrix, where $j$ labels the
instance; take unused rows empty. Each constant uses at most countably many
different witness supports, so their union supports its interpretation.
Transport along $j$ gives the whole witness entity. Thus every existential
pure instance true at the object is possible at the named tuple. Any
instance realized at an arrow conversely gives a witness at the same
object. These are the required directions of Logical Necessity. If global
assignments of constants are used, take the rooted unfolding and interpret
a constant at a history by transport of its designated root value.

This covers every purely relational signature. One individual name can
also be interpreted by a fixed atom $a$. Permuting the labels of pairs and
flipping within pairs acts transitively on atoms, normalizes $G$, and
preserves the supported hierarchy. A realizing tuple involving an individual
can therefore be chosen with that individual's value $a$ before gluing
the relational witnesses. Two individual names cannot be handled here:
their equality is fixed by every word, whereas the two matrices $x=y$ and
$x\ne y$ both have witnesses.

For a signature with only propositional constants the construction already
works with countably many pairs and finite atom supports: propositional
witnesses themselves all have empty support.

## Rigid comprehension and rigid power

Let $E$ be the current row of an admitted relation of type $\tau$. Define
$R_E$ by

$$
(R_E)_w=w[E],
$$

where $w$ transports each component of an argument tuple. The set $E$
has a countable support; the same set supports $R_E$ since arrow transport
commutes with $G$. The current row is $E$. At every history $h$, the
future row at $v$ is $v[h[E]]$. Thus current members persist. If a tester
$Y$ is necessarily true of each current member of $h[E]$, every member of
the row at $v$ is the $v$-image of such a member and satisfies $Y$ there.
This is weak inextensibility at every history. Hence $R_E$ is rigid.
Applying this construction to the current row of every relation gives
necessary Rigid Comprehension.

Conversely a rigid relation with current row $E$ is $R_E$, by uniqueness
of rigid coextensions (mutual inclusion from persistence and
inextensibility). If $F=R_E$ and a rigid $R_U$ at history $h$ lies below
$h\cdot F$, then $U\subseteq h[E]$. The set
$E'=E\cap h^{-1}[U]$ is supported since $h$ commutes with $G$, and
$h[E']=U$. Hence $R_{E'}$ is a rigid subrelation of $F$ and
$h\cdot R_{E'}=R_U$ as entire profiles. In the other direction every
image of a current rigid subrelation of $F$ is a rigid subrelation of
$h\cdot F$. The property of being a rigid subrelation of $F$ therefore
has at every history exactly the images of its current row. It is rigid
by the same characterization, giving necessary Rigid Power.

## Barcan, atoms and infinity

Every arrow transport is onto at every type. It is identity on individuals.
Given a relational entity $F$ and a word $h$, prescribe $H_{vh}=F_v$,
using the empty row at words outside that suffix. Right cancellation
makes the rows consistent, and $H$ retains an atom support of $F$.
Then $h\cdot H=F$. Quantifier surjectivity gives ordinary BF necessarily.

A profile with one tuple at one word $w$ and empty rows elsewhere is
admitted: the tuple has countable support. Under any transport it has
one tuple at one word or is bottom, by right cancellation. Thus it is a
strong atom, deciding each local relation or its complement at every
arrow. Every nonzero relation contains such an atom; this gives necessary
Strong Atomicity at every relational type. The singleton proposition
$\{\varepsilon\}$ is true and is a strong atom at the evaluation point.
The same construction can be used at each stage, giving necessary Strong
Actuality.

At any counting type, the external set of standard Frege numeral
denotations is invariant under $G$ because the numerals are closed terms.
Its constant profile is an admitted current inductive predicate. Current
numbers therefore consist exactly of standard numeral denotations.
The infinite individual and proposition domains have no finite Frege
count at any stage.

## Failure of choice

Let two individuals be equivalent just when they are in the same pair.
Its constant-profile graph is equivariant with empty support. For any
proposed transversal, take its countable support and flip a pair disjoint
from that support. The flip preserves the current row and interchanges the
two members of that pair, so the row cannot contain exactly one. Thus
Transversal Choice fails.

For Relational Choice consider the serial membership relation from
individual properties to individuals, permitting every output on an
empty property. If a functional subrelation selected from it, its current
row would be fixed by the flip of some unsupported pair. The constant
profile of that pair as an individual property is itself fixed by the flip.
The selected output must belong to the pair and be fixed by the flip,
which is impossible. Likewise no supported linear ordering of the
individuals can compare the two elements of a fresh pair antisymmetrically.
These failures hold at every stage.

## Intensional Choice and the number of words

Use the countable-support hierarchy on $\omega_1$ pairs described above.
With a countably infinite alphabet, Intensional Choice holds necessarily at
every type. With an uncountable alphabet, it already fails for a property
of individuals. One propositional constant suffices for Logical Necessity
in both cases.

Suppose first that the alphabet is countable. Its set of finite words is
countable. If $F$ is necessarily instantiated, use countable choice in the
metatheory to select $a_w\in F_w$ at every word $w$. At each word give $Y$
the row $\{a_w\}$. The union of countably many countable supports of the
$a_w$ supports this entire profile, since the flips fix the words. Thus
$Y\le F$ and $Y$ is necessarily uniquely instantiated. This works also
for tuples, taking the union of the finitely many component supports. The
argument applies at the unique object under every assignment.

For an uncountable alphabet, index the pairs by $i<\omega_1$, write them
as $C_i$, and fix distinct letters $j_i$. Define an individual property
$F$ by $F_{j_i}=C_i$ and $F_w=A$ at every other word. Every flip fixes
$F$, and all its rows are nonempty. If $Y\le F$ were necessarily uniquely
instantiated, a countable support of $Y$ would miss both members of some
$C_i$. The transposition of those two members fixes $Y$ and fixes the word
$j_i$. It exchanges the two elements of $C_i$, although it must preserve the
singleton $Y_{j_i}\subseteq C_i$. This refutes Intensional Choice
at the individual input type.

## Boolean completeness at every type

Let $E$ be the current extension of an admitted family of relations. The
pointwise stabilizer of the family's countable support preserves $E$ as a
set of entities. Define $L_w=\bigcup_{F\in E} F_w$ at every word. Each
permutation in this stabilizer fixes $w$ and permutes the relations in $E$,
so it preserves $L_w$. The common support therefore admits the entire
profile $L$. Entailment compares relations by inclusion at every word,
which makes $L$ the least upper bound of $E$. This proves necessary
Boolean Completeness at all relational types for either alphabet size.
