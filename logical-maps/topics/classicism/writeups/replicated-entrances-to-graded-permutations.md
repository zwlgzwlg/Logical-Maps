# Replicated entrances to graded permutations

At the root, every nonzero relation lies above a strong atom and every
type satisfies necessary BF. At an accessible point a nonzero
proposition has no atom below it. This separates Atomicity from
necessary Atomicity even in the presence of necessary BF and necessary
Strong Actuality.

## The upper point

Use a singleton individual sort. Let $A$ be an uncountable set used to
index arrows. At the upper point $s$, the endomorphism monoid $M$
contains $1=(1_A,0)$ and every $(g,n)$ with $g$ a permutation of $A$ and
$n$ a positive integer. Composition composes the permutations and adds
grades. For each relational type, give an entity a row of tuples of its
argument types at each $m$ in $M$. The whole profile must have a
countable pin $S\subseteq A$: at fixed grade, maps agreeing on $S$ have
identical rows. At propositions these rows are bits. The action is
right translation, $(mX)_k=X_{km}$. A pin for the translate by $(g,n)$
is $g[S]$. Two arrows of the same grade agreeing on $S$ transport $X$
to identical whole profiles. Hence the union of the pins of finitely
many parameters pins a lambda abstraction. This is the action semantics
of the [graded maps construction](graded-maps-free-words-glued-constants.html);
the coefficient set acts trivially on the singleton individual sort.

Each $m=(g,n)$ acts surjectively at every type. For $n>0$, lift a
relational target $B$ pinned by $S$ by giving its lift at grade $n$
the constant row $B_1$. At $(f,d)$ of grade $d>n$, use the row of $B$
at $(fg^{-1},d-n)$. At smaller grades use empty rows. The lift is
pinned by $g^{-1}[S]$ and its translate by $m$ is exactly $B$.
Surjectivity at individuals is immediate.

The proposition true exactly at the identity is a true strong atom.
By contrast, let $p$ be true throughout grade one and false elsewhere.
Any nonzero $q\le p$ has an occupied row at some $(g,1)$ and a
countable pin $S$. Choose distinct $a,b$ outside $S$. Swapping them
before $g$ preserves the row of $q$ and changes the image of $a$.
The grade-one test for that image to be $g(a)$ splits $q$ into two
nonzero propositions. Thus $p$ has no atom below it.

The upper point satisfies Self-Atomicity at every relational type.
For any nonzero profile choose an occupied tuple, and restrict the
profile to that tuple and its witnessing grade. Whenever this
restriction is instantiated after transport, the grade has already
reached that witnessing grade. All positive continuations then have
empty rows. The transported relation is supported on one current
tuple and is an atom.

## The root

Add a root $o$ whose only endomorphism is its identity. For each $m\in M$
give it entrances $(m,i):o\to s$ with $i\in\mathbb N\cup\{\infty\}$.
The identity of $s$ preserves the entrance. Every other continuation
$k$ yields $(km,\infty)$. This defines a category since two positive
grades compose to a positive grade. The root has the same singleton
individual sort.

A root relation consists of an unrestricted current row, a central
upper-point entity $x$, and upper-point tuple rows $L_{m,i}$ at the
finite-indexed entrances. For each fixed $m$, require $L_{m,i}$ to
equal the current row of $mx$ for all but finitely many $i$. At
$(m,\infty)$ use the current row of $mx$. This is a faithful
description of a profile: the entrance $(1,\infty)$ recovers $x$.
At $(m,i)$ for finite $i$, its whole transported entity is $mx$ with
its identity row changed to $L_{m,i}$. Such a change preserves
admission at $s$, since only its identity has grade zero. The rule for
continuations makes these transports functorial.

For a lambda abstraction at the root, take the upper-point denotation
on the central parameter values as its central entity. At every
$(m,\infty)$ naturality gives its required row, including on all upper
argument tuples. For a fixed $m$, outside the union of finitely many
finite exceptional sets all the parameters at $(m,i)$ coincide
*as whole upper entities* with those at $(m,\infty)$. Consequently
the entire row of the abstraction agrees there, including for formulas
with quantifiers or identity. The current root row is unrestricted.
Together with the upper-point term closure this supplies the action
interpretation of C. The argument uses pure principles and works
with arbitrary interpretations of the signature at the root.

## The root verdicts

Every entrance is onto at each sort: for a given upper value $b$ take
a central preimage $x$ under $m$ and choose no exceptional rows.
Every upper arrow is onto as well. Thus every future instance of a
predicate has a preimage along the witnessing arrow, proving necessary
[BF](../index.html#principle/necessary-barcan-r) at every type.

A single tuple confined to the current root row is an atom. So is a
single tuple confined to one finite-indexed entrance $(m,i)$: take the
central entry and all other rows empty. At that entrance it becomes an
upper atom supported on one current tuple. At all other entrances it
becomes bottom, since proper continuations only reach an
infinite-indexed entrance. Both sorts of atoms are strong. A nonzero
root relation has an occupied root row or an occupied finite-indexed
entrance row, since an occupied central row is also occupied at all
but finitely many copies. This proves [Strong Atomicity](../index.html#principle/strong-atomicity-r)
there. The root's identity-only truth and its counterpart at $s$ give
necessary [Strong Actuality](../index.html#principle/necessary-strong-actuality).
Self-Atomicity holds at both points. The failure of Atomicity at $s$
proves the failure of necessary propositional Atomicity at the root.

The root even fails Countable Boolean Completeness at propositions.
Take the family of singleton propositions at $(1,2i)$, for all
$i\in\mathbb N$. Its actual row and its graph to the corresponding
distinct Frege numerals counted at type $t$ are admitted. The numerals
are distinguished by current sets of propositions of every finite
size; arbitrary current rows supply these sets. This is the map's
[countability test](../index.html#background/arithmetic).
Any least upper bound must be true at every even copy and false at
every odd copy: the complement of each odd singleton is an upper
bound for the entire family. This violates eventual agreement with
the central bit at $m=1$.
