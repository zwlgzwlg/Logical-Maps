# Does Relational Choice imply Transversal Choice?

Christopher Sun observed that this implication is claimed in the literature
without proof. Zachary Goodsell passed the observation on and raised the
question here on 25 September 2026. The analysis below is by Claude Fable 5.1
(Anthropic) and has not been independently checked.

**Transversal Choice.** For every type $\sigma$ and every $R^{\sigma\sigma t}$
that is an equivalence relation,
$\exists F^{\sigma t}\, .\,\forall x\, .\,\exists y\, .\,(Rx)y\land Fy\land
\forall z\, .\,((Rx)z\land Fz)\to y=z$. Write $[x]$ for the cell
$\lambda z\, .\,(Rx)z$. Everything is unboxed and concerns the evaluation
point.

## The quotient argument and its gap

Apply Relational Choice at types $(\sigma t,\sigma)$ to the serial relation
$(UC)y:=Cy\lor\neg\exists z\, .\,Cz$, obtaining a functional $S$ below $U$, and
put $Fy:=\exists x\, .\,(S[x])y$.

Existence holds: the $y$ with $(S[x])y$ satisfies $[x]y$, because $[x]$ has
the instance $x$.

Uniqueness needs more. If $y$ and $y'$ are $F$-instances in the cell of $x$,
their witnesses $x_1,x_2$ lie in that cell, so $[x_1]$ and $[x_2]$ are
coextensive. Functionality of $S$ gives $y=y'$ only if $[x_1]=[x_2]$ as
properties. In C, identity of properties is necessary coextension
(Intensionality, *Classicism* §1.5), and the hypothesis supplies actual
coextension only. $R$ may be an equivalence relation contingently, and even a
necessary equivalence relation may relate $x_1$ and $x_2$ contingently. Then
$[x_1]\ne[x_2]$ and $S$ may choose differently from them.

No definable replacement for $[x]$ closes the gap. Any operation built by
$\lambda$-abstraction from $R$ and $x$ sends $x$ and $x'$ to the same value
only when the defining condition is necessarily equivalent for them, whereas
the hypothesis is actual indiscernibility with respect to $R$. The same
obstruction defeats a Zermelo-style well-ordering argument: the least family
closed under $A\mapsto A\setminus\{f(A)\}$ and under intersections contains
coextensive but distinct stages, which receive different chosen elements, so
the stages are not linearly ordered by inclusion.

## What does suffice

- **Extensionality** identifies $[x_1]$ with $[x_2]$ directly
  (`relational-choice-and-extensionality-imply-transversal-choice`).
- **Weak Rigid Comprehension** gives, for each cell, a weakly rigid
  coextensive property. Two weakly rigid coextensive properties are
  identical: weak inextensibility of one against weak persistence of the other
  gives necessary coextension, and Intensionality gives identity. Choosing from
  those canonical properties gives the transversal
  (`relational-choice-and-weak-rigid-comprehension-imply-transversal-choice`).
- Through recorded arrows, therefore also Gallin comprehension with BF, C5
  with Actuality, and boxed
  Functional Choice.

Conversely Transversal Choice implies Relational Choice over C, by rigid
pairs $\lambda uv\, .\,u=x\land v=y$
(`transversal-choice-r-implies-relational-choice-r`). So the question is
whether Transversal Choice is strictly stronger.

## Transversal (added 28 September 2026)

Christopher Sun isolated the missing ingredient on 26 September 2026 as the
principle Transversal: some $F^{(\sigma t)t}$ picks out exactly one property
from each coextension class. It is Transversal Choice for coextensiveness, and
with Relational Choice it gives Transversal Choice by running the quotient
argument on the $F$-representative of each cell
(`transversal-and-relational-choice-imply-transversal-choice`). The question
above is therefore equivalent to whether Relational Choice implies
Transversal. Actuality implies Transversal (Sun, `actuality-implies-transversal`),
and hence so does everything on the map that implies Actuality, including Weak
Rigid Comprehension; there weak rigidity itself also serves as $F$,
by the first paragraph of the proof of
`relational-choice-and-weak-rigid-comprehension-imply-transversal-choice`.

## Models

Every recorded model of Relational Choice is extensionally full at its
evaluation point: each set of tuples from the domains there is the extension
of a rigid element (full models, ideally full action models, full Henkin
models, and the free root components of the coalesced sums). That is how
Relational Choice is verified in them, by choice in the metatheory, and the
same choice of a transversal set verifies Transversal Choice. None separates
the two principles.

Symmetric Henkin models in the Fraenkel–Mostowski style cannot separate them
either. Let a group $G$ act on a set $W$ of worlds and on $D_e$, let
$\mathcal F$ be a normal filter of subgroups, and form the hereditarily
symmetric hierarchy: $D_t$ the symmetric subsets of $W$, and $D_{\sigma\tau}$
the symmetric functions $D_\sigma\to D_\tau$, where $(gf)(x)=g\,f(g^{-1}x)$
and symmetric means fixed by some member of $\mathcal F$. The value of a term
with symmetric parameters is symmetric, so this is a Henkin model of C.
Evaluate at $w_0$ with stabilizer $G_0$, and write $H_0:=H\cap G_0$.

Suppose Relational Choice holds at $w_0$, and let $S$, fixed by $K\in\mathcal
F$, be a functional subrelation of the relation $U$ above at types
$(\sigma t,\sigma)$. Take $H\in\mathcal F$ with $H\subseteq K$ and
$z_0\in D_\sigma$. Let $p$ be the orbit of $w_0$ under $H\cap\mathrm{Stab}(z_0)$,
a symmetric proposition, and let $f(z)$ be $gp$ for any $g\in H$ with
$gz_0=z$, and empty if there is none. This is well defined, $f$ is fixed by
$H$, each $f(z)$ is fixed by $H\cap\mathrm{Stab}(z)$, so $f\in D_{\sigma t}$,
and a short computation shows that the extension of $f$ at $w_0$ is the orbit
$H_0z_0$. The element $y$ chosen by $S$ from $f$ lies in that orbit and is
fixed by $K\cap\mathrm{Stab}(f)\cap G_0\supseteq H_0$. Hence
$H_0z_0=H_0y=\{y\}$, and $z_0$ is fixed by $H_0$. So $K_0$ acts trivially on
every domain. Then for an equivalence relation at $w_0$ take a transversal
$T$ of its extension there and put $F(z):=\{gw_0: g\in K,\ g^{-1}z\in T\}$:
$F$ is $K$-symmetric, each $F(z)$ is $(K\cap\mathrm{Stab}(z))$-symmetric, and
the extension of $F$ at $w_0$ is $K_0T=T$. Transversal Choice holds.

## What would settle the question

A proof must use the chosen relation $S$ itself to break the symmetry between
coextensive cells, not a canonical property definable from $R$. A countermodel
must be a model of C with Relational Choice that is not extensionally full at
its evaluation point and that escapes the symmetric-model argument above, for
example a Henkin model whose domains are the definable closure of a seed
relation, with definable choice for every definable serial relation but no
definable transversal. No construction of that kind is available in the
sources of the map. The expectation recorded here is that the implication
fails.

## A restriction on countermodels (26 November 2026)

Suppose Relational Choice holds from $\sigma t$ to $\sigma$ at the evaluation
point. If no finite Frege number at $\sigma$ counts the extension of a property
$A$, there is an admitted injection from the whole internal family
$\mathbb N_\sigma$ into $A$. In particular, $A$ admits an injective self-map
whose image omits one of its members. Here maps are represented by typed
relations that are total and single-valued on their stated domains at the
point. This includes $\sigma=e$.

Write $s$ for numerical successor. First, each $n\in\mathbb N_\sigma$ counts
some subproperty of $A$. The empty property witnesses zero. An $n$-counted
subproperty leaves an element of $A$ outside it, since counting respects
current coextension. Adjoin that element for the successor step. Impredicative
induction proves the claim. Every number and its successor therefore have an
instance. Zero differs from every successor. If $sn=sm$, remove one member
from an instance of their common successor. Both $n$ and $m$ count the
remainder, so they coincide by the common-instance lemma for finite numbers.

Apply the stated instance of Relational Choice to the serial relation

$$
U(B,a)\quad\leftrightarrow\quad (A(a)\land\neg B(a))\lor
                              \forall x\,(A(x)\to B(x)).
$$

Its chosen subrelation $G(B,a)$ determines a single update of each property
entity $B$, namely the entity $\lambda x\,(B(x)\lor x=a)$ for its selected
$a$. Define $T(n,B)$ by quantifying over all binary relations that contain
$(0,\lambda x\,\bot)$ and are closed under numerical successor paired with
this update. A pair belongs to $T$ just when it belongs to every such relation.
Every pair in $T$ is the base pair or an immediate image of a pair in $T$,
since that disjunction itself defines a closed relation containing the base.
The number indices of $T$ belong to $\mathbb N_\sigma$ by the same closure
argument. It follows by induction that each number $n$ occurs with exactly
one $B_n$. For uniqueness, use the decomposition, zero's disjointness from
successors, injectivity of $s$ on numbers, and functionality of the update
on property entities.

Induction gives $B_n\subseteq A$ and $n(B_n)$. Its chosen $a_n$ is therefore
in $A\setminus B_n$, and $B_{sn}$ contains both $a_n$ and $B_n$. For distinct
internal indices, one is $n+sr$ for the other $n$ and some number $r$.
Indeed, addition is defined by the same least-relation recursion with base
$n+0=n$ and step $n+sr=s(n+r)$. Induction gives $0+r=r$ and
$(sn)+r=s(n+r)$, and comparison follows by induction on one index, splitting
the other into zero or successor. Now $a_n\in B_{n+sr}$ by induction on $r$,
whereas $a_{n+sr}\notin B_{n+sr}$. Thus the admitted relation
$J(n,a)\leftrightarrow\mathbb N_\sigma(n)\land\exists B\,(T(n,B)\land G(B,a))$
is the claimed injection, including any nonstandard indices. Send $a_n$ to
$a_{sn}$ and fix the members of $A$ outside the image of $J$. This defines
an injective self-map of $A$ omitting $a_0$.

In particular, let $D$ be an admitted property meeting every equivalence
class of $R$. If each nonempty intersection $D\cap[x]$ has no such proper
self-injection, each intersection is Frege-finite. A finite property has a
rigid coextensive representative by induction on a count. At zero use the
empty property, and at a successor take the rigid representative after
removing one member and adjoin its rigid singleton. Two rigid coextensive
properties are identical. Hence equivalent $x$ determine the same representative
of $D\cap[x]$. Apply Relational Choice to pick a member of each nonempty
representative; their selected members form a transversal. Consequently, in
any separator **every admitted property meeting all classes meets at least one
class in a set containing a represented copy of the entire internal
$\mathbb N_\sigma$**. This leaves open whether such a separator exists.

At type $t$, Witnessed Possibility and No Pure Contingency yield the Axiom
of Infinity by the [necessary infinity result](witnessed-possibility-and-no-pure-contingency-imply-necessary-axiom-of-infinity-t.html).
With the current choice instance $(tt,t)$, the universal property of
propositions therefore admits the injection and the proper self-injection
above. A boxed choice instance gives the corresponding necessary conclusion.

This restriction and the represented iteration are due to OpenAI Codex
(GPT-6), prompted by Daniel Kodsi, 26 November 2026. A second OpenAI Codex
agent independently checked the argument. The finite representative argument
appears in the [October research notes, §13](https://github.com/dkodsi/Logical-Maps/blob/67b116acaf7cee286614307468f5361f6a195c6e/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/quotient-abstraction-lane.md).

### An internal family of infinite classes

Under full Relational Choice, the same argument gives a two-dimensional
restriction. Suppose $R$ has no transversal. Given any admitted cover $D$
meeting every class and any admitted partial transversal $T$, there is a
single admitted ternary graph assigning $d_{n,m}\in D$ to each
$n,m\in\mathbb N_\sigma$. Its entries are distinct, their classes avoid
all classes met by $T$, and $R(d_{n,m},d_{n',m'})$ holds exactly when
$n=n'$. Both coordinates range over the entire internal number family.

Indeed, let $U$ be any partial transversal extending $T$. Some class missed
by $U$ meets $D$ in an infinite property, i.e. one having no finite Frege
count. Otherwise the property containing $U$ together with the members of
$D$ in missed classes would meet each class in a nonempty finite property.
The preceding criterion would then provide a full transversal. In particular,
taking $U=T$ already supplies an infinite property and hence the realization
and successor-cancellation facts about $\mathbb N_\sigma$ used above.

Apply the same represented iteration, starting with $B_0=\varnothing$.
When $T\cup B$ is partial, the serial relation on $(B,a)$ asks for $a\in D$
in a missed class with $D\cap[a]$ infinite; for other $B$ allow any $a$.
Relational Choice from $\sigma t$ to $\sigma$ gives a deterministic update.
Induction and the comparison of internal indices proved above give a graph
of representatives $a_n$ in pairwise different classes missed by $T$, all
of whose $D$-intersections are infinite. For each $n$ the first theorem
therefore gives a represented injection from $\mathbb N_\sigma$ into
$D\cap[a_n]$. To choose these row graphs simultaneously, use Relational
Choice again, now from $\nu_\sigma=(\sigma t)t$ to $\nu_\sigma\sigma t$.
On non-number inputs allow any graph. Applying the selected graph at $n$
to $m$ gives the claimed single ternary relation. This last step uses the
additional choice instance of full Relational Choice; the original
one-row criterion uses only the instance from $\sigma t$ to $\sigma$.

The internal two-dimensional refinement was developed and independently
checked by two OpenAI Codex agents, prompted by Daniel Kodsi, 26 November 2026.

## Individual-map profiles with noninvertible arrows

The stabilizer-orbit argument for symmetric S5 models above also excludes a class of models with noninvertible arrows, several objects, or external coefficient sets. It needs only the instance of Relational Choice from properties of the sort in question to that sort.

Fix an object $o$ and a sort $\sigma$. At $o$ a group $G$ of coefficient permutations acts on the current entity domains. Suppose these permutations are allowed arrows, with the same auxiliary labels as the identity, and composition with them preserves the labels. A profile is pinned by a set $P$ of source coefficient labels if arrows into the same target, with the same labels and agreeing on $P$, have identical rows. Assume every admissible profile has an allowed pin, commutes with the action of target permutations, and that every profile satisfying these two conditions is admitted. The group acts on whole entities by precomposition with its arrows. The coefficient labels can be separate from the actual individuals.

Apply the instance of Relational Choice to ordinary membership, permitting every output on the empty property. Let $S$ be the selector and $P$ one of its pins. The current graph of $S$ is invariant under $H$, the subgroup fixing $P$ pointwise. Indeed, an $h\in H$ agrees with the identity on $P$, and target equivariance sends the identity row of $S$ to its row at $h$.

For any $H$-invariant set $E\subseteq D_\sigma(o)$, construct a property $Y$ as follows. On an arrow $f$ ending at $o$ with the identity labels, assign the row $g[E]$ when $f|_P=g|_P$ for some $g\in G$. Assign the empty row if there is no match, or if the arrow has a different target or labels. Two matching permutations differ on the right by a member of $H$, so give the same row. This profile is pinned by $P$, is equivariant under each target group, and has current row $E$. The whole property is fixed by $H$ because precomposing an arrow by $h\in H$ leaves its restriction to $P$ unchanged.

Apply this construction to $E=H\cdot x$, for any $x\in D_\sigma(o)$. The unique output selected at $Y$ lies in $E$ and is fixed by all of $H$. A transitive orbit with a fixed point is a singleton. Hence $H$ fixes every member of $D_\sigma(o)$. The same profile construction now represents every external subset of that sort, and works without change for tuples all of whose sorts $H$ fixes. In particular a transversal selected in the external set theory is represented at $o$. If $\sigma=e$ and the action of $G$ on the actual individuals is faithful, then $H$ is trivial, so every external current tuple row at every type is represented already from the single choice instance $(et,e)$.

The full-profile admission hypothesis matters: a more restricted Henkin domain need not contain the property constructed on matching coefficient maps. The unrestricted implication remains open.

Proof by OpenAI Codex (GPT-6), prompted by Daniel Kodsi, extending the symmetric-model argument earlier on this page, 26 November 2026. Two other OpenAI Codex agents independently checked the extension to noninvertible arrows.

A represented well-order on the quotient gives a further restriction. Relational Choice supplies a transversal whenever the quotient has computable external order type, and more generally when the same order type is represented on a domain of available labels. [Comparison of quotient orders and the standard Frege cut](#relational-choice-for-well-ordered-quotients)

## Relational Choice for well-ordered quotients

Suppose an equivalence relation $E$ on a represented set $X$ of type $\sigma$ has a represented strict ordering $<$ of its equivalence classes. If the actual ordered quotient has the order type of a computable well-order, local Relational Choice supplies a transversal. This covers every ordinal below the Church–Kleene ordinal $\omega_1^{\rm CK}$. The order type is an external hypothesis on this particular instance. The unrestricted [Relational Choice question](relational-choice-r-implies-transversal-choice-r.html) remains open.

### Comparing two well-orders

Suppose first that some represented subset $D$ of an admitted type $\tau$ carries an actual strict well-order $\prec$ isomorphic externally to $X/E$. Each point of $D$ is an individual entity of its type. There is an admitted relation that assigns each member of $X$ its unique point in the corresponding position of $D$.

To construct it, for an admitted relation $R$ define the following current condition on $x\in X$ and $d\in D$, taking it false off that product.

$$
\Phi(R)(x,d)\ \longleftrightarrow\
  \bigl(\forall y<x\,\exists b\prec d\,R(y,b)\bigr)
  \ \land\
  \bigl(\forall b\prec d\,\exists y<x\,R(y,b)\bigr).
$$

The variable $y$ ranges over $X$ and $b$ over $D$. This operation is monotone for inclusion of current extensions. Comprehension gives $L(x,d)$ asserting that $R(x,d)$ holds for every admitted $R$ with $\Phi(R)\subseteq R$, using current inclusion. For each such $R$, monotonicity gives $\Phi(L)\subseteq \Phi(R)\subseteq R$. Hence $\Phi(L)\subseteq L$. Applying monotonicity again shows that the admitted relation $\Phi(L)$ itself qualifies in the definition of $L$. Thus $L$ and $\Phi(L)$ have the same current extension.

Induct externally on the ordinal position of the class of $x$. The two clauses of $\Phi(L)$ say that the positions of the proper predecessors of $[x]$ and of $d$ form the same set. By the induction hypothesis, every match used in those clauses identifies equal predecessor positions. Two ordinals with precisely the same smaller ordinals are equal. This proves that $L(x,d)$ holds exactly when $[x]$ and $d$ occupy the same position.

Apply Relational Choice at $(\tau,\sigma)$ to select one $x$ for each $d\in D$ with $L(x,d)$, allowing arbitrary outputs off $D$. The range restricted to $D$ is an admitted property and contains exactly one member of every $E$-class. This argument uses the external isomorphism only to compare ordinal positions. The admissible relation $L$ was constructed within the model.

### When the comparison order can be represented in arithmetic

For a finite quotient, take one representative of each class and the finite disjunction of their haecceities. Now suppose $X/E$ is an externally infinite well-order. The classes that have only finitely many predecessors form its first segment of type $\omega$. This segment is definable on representatives. An $x$ belongs to it just if every nonleast class up to and including $[x]$ has an immediate predecessor. Every infinite closed initial segment contains the class in position $\omega$, which violates this test.

Let $N_\sigma$ be the Frege finite cardinalities. Define an admitted predicate $T$ of such cardinalities by requiring that, for some $x$ in this first segment, there be a property counted by $n$ whose extension consists of precisely one representative of each class strictly below $[x]$ and nothing else. Each of these finitely many representatives can be supplied by a finite disjunction of haecceities, including the empty property at the least class. If $[x]$ has precisely $j$ predecessors, every such choice has external size $j$, and hence is counted by the standard $j$th numeral. Two Frege finite cardinalities counting the same property coincide. Thus $T$ contains exactly the external standard numeral denotations. They are pairwise distinct since $X$ contains arbitrarily large finite sets. [Frege cardinality and arithmetic](../index.html#background/arithmetic)

The actual predicate $T$ contains zero and is closed under successor. The impredicative definition of $N_\sigma$ therefore gives $N_\sigma\subseteq T$. All the current numbers are standard. In particular the current sum and product have their ordinary values, by their defining recursion. Every computable presentation of a well-order on a subset of the natural numbers can now be represented at this point by its arithmetic definitions of the field and the order. Applying the comparison argument with $\tau=(\sigma t)t$ proves the result. It also applies to orderings computable relative to any admitted predicate of these numbers.

There is a related distinction in constructive type theory. Carlström proves that intensional choice, excluded middle and a weak extensionality principle yield extensional choice for setoids. The extensionality hypothesis concerns boolean-valued functions. His theorem is in a different theory from C. [Jesper Carlström, *EM + Ext⁻ + ACint ⇔ ACext*](https://www2.math.su.se/reports/2003/14/2003-14.pdf)

OpenAI Codex (GPT-6), prompted by Daniel Kodsi, obtained this restriction on 27 November 2026. Two other GPT-6 research agents independently checked the fixed-point construction, the standard-number argument and the use of local choice.

## Well-foundedness at a point with an unselectable well-ordered quotient

Suppose local Relational Choice holds and a represented equivalence relation on a domain $X$ of type $\sigma$ has no transversal. Suppose further that its quotient $Q$ has a represented ordering on the representatives which, externally, well-orders the classes. Let $\alpha$ be its order type. Then **every internally well-ordered linear order on a represented domain at any finite type is externally well-ordered**. At each type a single admitted tester recognizes the externally well-ordered inputs. In particular the numerical sets represented at this point form a $\beta$-model of full second-order arithmetic.

To prove this, first observe that every represented genuine well-order on labels of any type has order type strictly below $\alpha$. At equality, the preceding comparison lemma matches each class of $Q$ to its own label. Relational Choice then chooses a representative per label. In a longer order use the represented initial segment bounded by the label in position $\alpha$.

Fix any represented domain $D$ and any represented strict linear order $R$ on it. Use the preceding least pre-fixed-point definition of $L(x,i)$, with $x$ ranging over representatives of $Q$ and $i$ over $D$. In current extension it satisfies

$$
 L(x,i)\quad\longleftrightarrow\quad
 (\forall y<x\,\exists jRi\,L(y,j))
 \land (\forall jRi\,\exists y<x\,L(y,j)).
$$

External induction on the position $\xi$ of $[x]$ shows that $L(x,i)$ holds precisely when the predecessors of $i$ are well-ordered with type $\xi$. This works even when $R$ is ill-founded. The second clause makes each predecessor of $i$ have a well-ordered lower segment of rank below $\xi$. The entire lower segment is then well-ordered. Given a nonempty subset, pick one member. If there is a smaller member, take the least such member in the chosen member's well-ordered lower segment. The first clause realizes every rank below $\xi$, which gives the exact order type. Conversely, two well-orders of the same type have the same predecessor positions, giving both clauses by the induction hypothesis.

Test the whole of $D$ by asking whether for some $x$,

$$
 (\forall y<x\,\exists i\in D\,L(y,i))
 \land (\forall i\in D\,\exists y<x\,L(y,i)).
$$

The test succeeds precisely when $D$ has the order type of the predecessors of $[x]$. Every represented genuine well-order has length below $\alpha$, so each passes. The formula with $D,R$ as arguments defines one admitted tester per type. Apply it to the lower segment at each element of a given order. This gives the externally well-founded part as a single represented current property. In an ill-founded linear order its nonempty complement has no least member. A least member there would have a well-ordered predecessor segment and belong to the well-founded part. This refutes the internal well-order condition on every externally ill-founded input.

At the counting type $\sigma$, the standard-cut argument above makes the Frege numbers standard. Take as reals the **current traces** of admitted number predicates. Ordinary second-order comprehension holds for these traces by typed abstraction. In translating set equality one compares membership at each number. For an admitted tree of finite sequences of natural numbers, its Kleene–Brouwer order is a represented linear order and is well-founded exactly when the tree has no branch in the ambient mathematics. Apply the tester to the subtree at each node. Starting in an ill-founded subtree, recursively take the least child whose subtree is ill-founded. The graph of the branch is represented by testing finite sequences for this deterministic rule. Hence each externally ill-founded represented tree has a represented branch. This is the tree characterization of a $\beta$-model.

For example, let $a$ be any represented numerical real. Its actual hyperjump, coded by the indices of well-founded $a$-recursive trees, is represented by the same tester. In fact there is a represented real coding the entire hyperjump hierarchy along any represented genuine well-order on a subset of the numbers. A history through a position assigns each column the hyperjump of the join of $a$ and all earlier columns with their numerical labels. External induction gives uniqueness of the columns as current sets. At a limit, comprehension of the pairs $(j,k)$ for which some history through $j$ has $k$ in its $j$th column assembles all earlier histories. The tester yields the next hyperjump. Applying the same comprehension over the entire ordering collects the hierarchy in one real. Thus the earlier ordinal restriction applies also to the ordinals computable from these iterated hyperjumps. It already applies beyond all ordinary computable ordinals.

There is a further cofinality restriction. In a given set-sized point, take an unselectable externally well-ordered quotient of **least** order type among all such represented quotients at all types. Each proper initial segment then has a transversal. The induced order on that transversal represents its ordinal on a subset of $X$. Every $\beta<\alpha$ is therefore represented in this one sort. The ordinal $\alpha$ is a limit, since one representative from a last class could be adjoined to a transversal for its predecessors.

There is no represented cofinal family of classes indexed by a represented well-order of labels. Such a family need only be functional modulo the equivalence relation. For each label $i$, the segment through its assigned class has a transversal. Apply Relational Choice to select one whole such predicate $T_i$ for each $i$, allowing arbitrary outputs off the label domain. For each class use the first index whose segment covers it, and retain the member of the class selected by this $T_i$. This defines an admitted transversal of $Q$, a contradiction.

The external well-order on the original quotient is an additional hypothesis. The unrestricted Relational Choice conjecture remains open. These restrictions were obtained by OpenAI Codex (GPT-6), prompted by Daniel Kodsi, on 27 November 2026. Two additional GPT-6 researchers independently checked the order comparison on ill-founded inputs and the numerical tree argument. The hierarchy and cofinality refinements were checked separately.
