# Injective entrances to old and new individuals

At the designated root every nonzero relation lies above a strong atom.
Ordinary BF holds at every type there. A successor fails Inextensible
Comprehension on the universal property of individuals. Thus even
Strong Atomicity and local BF together do not imply necessary
Inextensible Comprehension.

## Three objects

Use the [symmetric old-and-new model](symmetric-old-new-individuals.html)
of Claude Fable 5.1, prompted by Cian Dorr, with a single new individual.
Write $E=\mathbb N$ and $O=\mathbb N\sqcup\{*\}$. Between the two
objects take the following maps on individuals.

| Source | Target | Arrows |
|---|---|---|
| $E$ | $E$ | All injections |
| $E$ | $O$ | All injections with range in $\mathbb N$ |
| $O$ | $E$ | All injections |
| $O$ | $O$ | The permutations fixing $*$, and the injections with range in $\mathbb N$ |

Add a root $R$ with countably infinitely many individuals. Its only
endomorphism is its identity. Take **all** injections $R\to E$ and
**all** injections $R\to O$. An entrance to $O$ may hit $*$. There
are no arrows into $R$ from either upper object. Composition is
ordinary composition. The target symmetry groups are
$G_E=\operatorname{Sym}(E)$ and $G_O=\operatorname{Sym}(O)_*$.
Use the trivial group at $R$.

At each relational type $\tau=\bar\sigma t$ a relation has a tuple row
$X_h$ at each arrow $h$ out of its object. At $h:U\to V$ require
$X_{gh}=g[X_h]$ for every $g\in G_V$. Require a finite pin $N$ of
source individuals: arrows with the same target and the same
restriction to $N$ have the same tuple row. The root's current row
is unrestricted. Individuals transport by the indicated injections;
relation transport is $(aX)_k=X_{ka}$. A pin $N$ for $X$ supplies
the pin $a[N]$ for $aX$. In particular every argument tuple at an
upper object has a finite support in the target group: take the union
of its relation pins and its individual entries.

For abstraction at a future arrow evaluate the body on all target
arguments with the transported parameters. Arrows agreeing on a
parameter's pin transport its entire entity identically, by composing
with every continuation. Target automorphisms preserve the same
evaluation, including equality and quantified formulas. Thus the
union of the parameter pins admits the abstraction. Distinct
relational profiles are distinguished by a tuple at an outgoing
arrow. These give the usual action interpretation of C. For the signature verdicts use one propositional name, interpreted
by a marked-preimage proposition as specified below. The pure verdicts are independent of this choice.

## Strong atoms at the root

An occupied current root row has a subrelation containing just that
tuple there and nothing elsewhere. It is a strong atom, since it
becomes bottom at every entrance. Otherwise let $X$ have an occupied
tuple $b$ at $h:R\to V$, $V=E$ or $O$. Choose a finite pin $N$ for
$X$ and a finite support $P$ for $b$ under $G_V$. Modify $h$ outside
$N$ to an injection $h'$ whose range covers $P$ and, when $V=O$,
also covers $*$. Finitely many fresh inputs suffice. Choose finite
$M\supseteq N$ containing preimages of those target points.

Define $Q$ to have empty rows at all other targets and at the root.
At $k:R\to V$ its row consists of the tuples $g b$ for
$g\in G_V$ such that $k|_M=g h'|_M$. Any occupied row is a singleton,
since $h'[M]$ supports $b$. The construction is $M$-pinned and
equivariant, and $Q\le X$ by pinning $X$ and applying target symmetry.

To see that $Q$ is an atom at $R$, consider a tester with any finite
pin $T$. For two occupied arrows $k_1,k_2$, the map taking
$k_1(a)$ to $k_2(a)$ for $a\in M\cup T$ is a bijection of the two
finite images. At target $E$ it extends to a permutation. At target
$O$ it extends to a permutation fixing $*$, because $M$ contains a
designated preimage of $*$ and injectivity makes all other images
old. This permutation transports the first occupied tuple to the
second, as $h'[M]$ supports $b$. Equivariance and agreement on $T$
therefore give the tester the same truth on every occurrence of $Q$.

Now take an entrance $a:R\to U$. If $V=E$, the nonempty rows of $aQ$
occur only on continuations $k:U\to E$. These are arbitrary
injections. Given a tester at $U$, align any two such continuations
on $a[M]$ and the tester's finite pin by extending the prescribed
finite bijection to an $E$-permutation. As above it takes the one
tuple to the other. Hence $aQ$ is an atom.

If $V=O$, the marked source individual must have image $*$. Any
continuation through $E$, and every nonpermutation endomorphism of
$O$, instead has old-only range. If $a$ already sends the marked
individual to $*$, the only contributing continuations are
$O$-permutations, with the one tuple transported by those permutations.
Every tester gives a uniform answer on this orbit. In all other cases
$aQ$ is bottom. This accounts for every composite entrance, so $Q$
is strong. We have proved
[Strong Atomicity](../index.html#principle/strong-atomicity-r) at every
relational type, including propositions.

Atomicity also holds at both upper points. The same finite marking
argument yields an atom below each occupied row of a relation there.
For target $E$, all maps of either source into $E$ are injections
into an unmarked set, so fresh source points can cover the tuple's
finite support and the finite alignment applies. For target $O$,
the point $*$ is already fixed by its symmetry group. From $E$ only
old points are reachable, so cover the old part of the tuple support;
all available arrows have old-only range. From $O$ also put the
source point $*$ in the marking. Its image distinguishes permutations
from old-range injections. Among permutations one may use the given
one and its inverses on the finite support. Among old-range injections
first cover the old part of the support off the prescribed pin.
In either class, an arbitrary extra tester pin has the same image
color pattern at any two occupied arrows, giving the atom by the same
finite alignment. Thus the root satisfies necessary Atomicity at
every relational type.

## Inextensible Comprehension fails at the upper point

At $E$, suppose $Y$ is inextensible and coextensive with the universal
individual property. For each injection $f:E\to E$, a permutation
agrees with $f$ on $Y$'s finite pin. Its row, and therefore $Y_f$,
is all of $E$. Let $\iota:E\to O$ be the old inclusion. The tester
that gives full rows at $E$ and the old individuals at $O$ necessarily
holds of every current individual. Weak inextensibility at $E$ forces
$Y_\iota$ to omit $*$.

At $O$, every member of $Y_\iota$ necessarily differs from $*$,
since every arrow is injective. Yet after any $m:O\to E$, the row
$Y_{m\iota}$ is all of $E$ and includes $m(*)$. Thus $\iota Y$ is
not weakly inextensible. This is the old-and-new model's obstruction
with one new individual; it applies unchanged after adding the root.
In particular necessary
[Inextensible Comprehension](../index.html#principle/necessary-inextensible-comprehension-r)
fails at $R$.

## Barcan and Boolean completeness

To prove BF at $R$, let a tester with pin $N$ have a possible instance
at an entrance $h:R\to V$. Replace $h$ by a bijection $h':R\to V$
agreeing with it on $N$; the same instance $b$ still belongs to the
tester's row. At individuals lift $b$ directly along $h'$. At a
relational type, take a pin $T$ for $b$ and set $S=(h')^{-1}[T]$.
At an entrance $l:R\to U$ give the lift the row $b_g$ if
$l|_S=(gh')|_S$ for some $g:V\to U$, and give it the empty row if
there is no match. All matching $g$ agree on $T$, so this is
well-defined. It has pin $S$ and is equivariant since the target
permutations and their inverses are arrows. Its transport by $h'$ is
exactly $b$. A current witness needs no lifting. This proves ordinary
BF at every type.

Propositional BF fails at $E$. Its four propositions observe only
whether an arrow ends in $E$ or in $O$: finite restrictions of two
maps to the same target from $E$ are equivalent under a target
permutation. At $O$, the proposition consisting of the permutations
fixing $*$ separates these from the old-range endomorphisms. No
proposition from $E$ can transport to it along any entrance to $O$.
An $E$-tester accepts all propositions on arrows to $E$ and all
except this one on arrows to $O$. It necessarily accepts every old
proposition and lacks an instance at the upper object. Hence
necessary propositional BF fails at $R$.

The root fails Countable Boolean Completeness already at $t$.
Enumerate $R$ as $a_0,a_1,\ldots$. Let $p_i$ be true precisely at
those $k:R\to O$ with $k(a_i)=*$. The even-indexed $p_i$ form an
admitted current family, with a current graph to distinct Frege
numerals counted at the infinite individual sort. These numerals are
distinguished by finite sets of every size, all admitted at the root.
If a least upper bound existed, it would be true at each entrance with
even marked preimage but false at each entrance with odd marked
preimage, since each odd singleton's complement is an upper bound.
Two injections agreeing on any proposed finite pin can send,
respectively, an even and an odd input outside it to $*$. This
contradicts pinning.

For distinct indices $i,j$, the union $p_i\lor p_j$ is a self-atom
at the root: whenever it is instantiated its entire transport is
the upper true atom $G_O$. Its two nonzero components separate it at
the root, so it is not an atom there. Interpret the single propositional
name by $p_0$. Permuting the root individuals acts on the three-object
model by reindexing each entrance, fixing the upper objects. It takes
$p_0$ to $p_i$ when it takes $a_0$ to $a_i$, whereas it fixes every
closed pure denotation at the root. This witnesses Independence for
the indicated signature.

The isolated root identity proposition is true and becomes impossible
after every proper entrance. It is therefore a guard for the ND-necessity
of every current truth. At $E$ and $O$, the [old-and-new verification](symmetric-old-new-individuals.html)
of two-hat and 5-necessity of truths uses exactly the two arrow classes
out of $E$ and three out of $O$ described above; the single new
individual still distinguishes the two endomorphism classes at $O$.
At $E$ the true atom is supported on arrows ending at $E$, and a
return from $O$ through $E$ cannot restore the truth of $G_O$, since
every entrance from $E$ has old-only range. At $O$ no proper exit
can restore the truth of the atom $G_O$. These are the two witnesses
in the cited two-hat calculation. With necessary Strong Actuality
this also gives 5-necessity. Thus every truth is 5-necessary at
every object.

## Intensional Choice and Modalized Relational Choice

At $R$ an arbitrary actual tuple row is admitted, by using empty rows
elsewhere. In particular every type has an actual well-order, and
Relational Choice holds there.

Intensional Choice holds throughout the model. At a given source,
take a necessarily inhabited $F$ with finite pin $N$. If the source
is $O$ include $*$ in $N$. Treat the root identity row separately
by choosing any one of its $F$-members. At each upper target, the
restrictions $f|_N$ have only finitely many orbits under target
permutations: there is one unmarked color in $E$, and in $O$ at
most one source point maps to $*$. For each realized pattern take
one arrow $f_0$ and a member $b\in F_{f_0}$ with finite target support
$T$. For this target put $T'=T\setminus f_0[N]$, omitting also $*$
when there is a marked point.

Choose an ordered finite list of additional source individuals
outside $N$ of length at least one more than the largest $|T'|$
over the finitely many choices. At an arrow $f$ of the same pattern,
send $f_0(x)$ to $f(x)$ on $x\in N$ and fix $*$ if present. Send the
points of $T'$ in a fixed order to the first $|T'|$ unmarked images
of the additional source individuals. There are enough, since $f$
is injective and at most one image is marked. These partial
prescriptions extend to a target permutation $g$. Every such $g$ has
the same value on $b$ because the prescriptions cover $T$. Choose $gb$
at $f$. It belongs to $F_f$ by target equivariance and the pin $N$.
This singleton row depends only on the enlarged finite pin, and
postcomposing $f$ with a target permutation transports its chosen
member by that permutation. Hence the rows are one admitted
subproperty of $F$, uniquely instantiated at every arrow.

Modalized Relational Choice nevertheless fails. Consider the
necessarily serial relation from individual properties $X$ to
individuals $y$ which requires $Xy$ when $X$ has exactly two
instances, and otherwise puts no condition on $y$. At $E$ the
property with rows $u[\{a,b\}]$ is admitted on the finite pin
$\{a,b\}$. If a functional subrelation of the serial relation existed
at $E$, choose distinct $a,b$ outside its finite pin. Swapping $a,b$
fixes its current graph and fixes the displayed pair property as a
whole entity, but exchanges its only two eligible outputs. Thus
Relational Choice fails at $E$. No root relation can select necessarily
from the displayed serial relation, since its transport to $E$ would
make this forbidden selection. This shows precisely where the
[known implication from necessary Relational Choice](../index.html#result/necessary-relational-choice-and-intensional-choice-imply-modalized-relational-choice)
uses its box. The existing
[swappable-pairs countermodel](coalesced-swappable-pairs-root.html) already
refutes that unboxed strengthening.

## The remaining mathematical verdicts

At either upper object $U$, every subset $D$ of a current type fixed by
the pointwise stabilizer of a finite $P$ occurs as a current row.
On endomorphisms whose restriction to $P$ agrees with a permutation
$g\in G_U$ take $g[D]$, and take the empty row elsewhere. Agreement on
$P$ makes this independent of the chosen $g$; if $U=O$, include $*$ in
$P$. This gives a finitely pinned equivariant profile.

In particular the external set of the standard Frege numeral entities
at any type is an admitted upper row, since its members are closed terms
fixed by every symmetry. The same cut is admitted by current fullness at
the root. Thus at every point every Frege number is a standard numeral,
and at Peano points these numerals are distinct and compute ordinary
arithmetic. This gives Necessity of Arithmetic. If the Peano condition
holds necessarily, each future number is the transport of its closed
standard numeral, and distinct numbers stay distinct. This exact
coverage gives hereditary weak inextensibility of the number property,
hence Arithmetic Necessitism. The individual domain is infinite
throughout, so no numeral counts its universal property. The root
proposition domain is infinite, whereas the two upper objects have
finite proposition domains and no successor with infinite proposition
domain.

Every real structure wherever it exists also realizes ordinary full
second-order analysis. At an upper object take a common finite support
of its data. The externally generated successor orbit of its zero is a
current row by the preceding argument. This cut is inductive, so it
exhausts the number sort. Its elements are individually fixed by the
stabilizer of the support. Every external subset of the number sort is
then a current row. Fullness and extensionality of the real structure
give exactly one real for each subset. These reals too are individually
fixed, since their memberships determine them. Consequently every
external relation on the numbers and reals is a current row. The root
case uses its unrestricted rows directly. Necessity of Second-Order
Analysis follows.

Analytic Necessitism fails at type $et$. The root's individual
properties include continuum many elements, since its current rows on
$R$ are unrestricted. They carry a standard real structure in the freely
chosen root graphs. At $E$, by contrast, only countably many individual
properties exist. For a fixed finite pin only finitely many target
patterns are possible, and a representative arrow's row is a subset
of individuals fixed by the permutations fixing its pin images. These
permutations have only finitely many individual orbits. Hence there are
only finitely many individual properties per pin and countably many
pins. No full standard real structure exists on this countable domain.
Thus no root structure is necessarily a real structure at this type.

No well-order of individuals exists at either upper point, since a
transposition of two old individuals outside a proposed order's pin
preserves its current row and exchanges the two elements. The pure
sentence $C$ asserting that $e$ can be well-ordered currently is true
only at $R$. Pure B fails, since $C$ cannot become true from $E$.
Witnessed Possibility fails for the two matrices $C\land x=\top$ and
$C\land x=\bot$ applied to the same propositional name: both have
current witnesses and the only possible witnessing arrow is the
identity of $R$.

Revised Mathematical Possibilism also fails. The root's finite ordinal
thresholds are pairwise distinct, by the finite well-order tests on its
infinite set of individuals. On a current subcollection of the root
individual-property sort one can therefore represent the complete
atomless regular-open algebra of Cantor space, of size continuum.
It is revised-small: a subcollection larger than the ordinal benchmark
is uncountable and contains a countably infinite smaller subset. All
its continuum many subextensions are present, requiring at least
continuum many power codes, which cannot lie in a subset of strictly
smaller cardinality than that subcollection. Every principal interval
of the root proposition algebra is atomic, since that algebra is
atomic. None is isomorphic to this nontrivial atomless algebra.
[Ordinal benchmarks and power coding](singular-lottery-ordinal-thresholds.html)

The new root and its proof are by OpenAI Codex (GPT-6), prompted by
Daniel Kodsi, 26 November 2026. Two further GPT-6 research agents
independently checked the construction and the core separation.
