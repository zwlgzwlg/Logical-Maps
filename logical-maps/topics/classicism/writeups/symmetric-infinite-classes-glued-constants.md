# Logical Necessity with no transversal of coextension

For each admissible set-sized signature, Logical Necessity can hold at a
point where Transversal fails at type $e$. The same model satisfies
necessary Boolean Completeness, ordinary BF, Tame Rigidity and both rigid
power principles at every relational type. Transversal here asks for a
property containing exactly one representative of every actual coextension
class of individual properties.

The construction combines Dorr's proposal of symmetric models over rich
individual structures, as implemented in the map's
[symmetric infinite classes model](symmetric-infinite-classes.html), with the
[word-coordinate gluing construction](symmetric-surjection-products.html).
The argument below replaces the finite model's least-pinning-set step by
a two-pin argument that works for infinite pinning sets.

## Action model

Fix an infinite cardinal $\kappa\ge|\Sigma|$. Individuals form a set $A$
partitioned into $\kappa^+$ classes, each of size $\kappa^+$. Write $a\sim b$
for membership in the same class. Let $G=\operatorname{Aut}(A,\sim)$.
There is one object with arrows $(w,s)$, where $w$ is a word in a free
monoid on $\kappa$ letters and $s:A\to A$ is any surjection. Composition is
$(v,t)(w,s)=(vw,ts)$. Individuals transport by $s$.

At a relational type $\tau$, an entity $X$ assigns a set of admitted
argument tuples $X_{(w,s)}$ to every arrow. It must satisfy two conditions.

- Some $P\subseteq A$, $|P|\le\kappa$, pins $X$: for fixed $w$ the row
  depends only on $s|_P$. The same $P$ works for every word.
- $X_{(w,gs)}=g[X_{(w,s)}]$ for $g\in G$, with the componentwise action
  on argument tuples. Here $g$ denotes transport by $(\varepsilon,g)$.

Transport of a relation is $(hX)_k=X_{kh}$. If $P$ pins $X$ then $s[P]$
pins $(w,s)X$. Agreement of two arrows of the same word on $P$ gives
equality of the whole transported entities, by composing on the left.
Transport preserves the symmetry condition. At the identity point each
$g\in G$ acts as an automorphism: it takes the current membership of
tuples in $X$ to current membership of their images in $gX$. Such a
bijection respects equality and quantification, and evaluation along an
arrow uses the transported parameters. The lambda profile with finitely
many parameters is therefore symmetric and pinned by the union of their
pins. This is the term-closure argument of the
[word-coordinate model](symmetric-surjection-products.html), §1.
A pure sentence has constant truth throughout this one-object model.

## Gluing the signature

Every arrow transports onto every type. For an individual this is the
definition. For a relation $X$ pinned by $P$ and a surjection $s$, choose
distinct preimages of $P$ and extend the resulting injection
$p\mapsto s^{-1}(p)_{\rm chosen}$ to a permutation $u$ of $A$.
Then $su$ fixes $P$ pointwise, so
$(\varepsilon,s)((\varepsilon,u)X)=X$. Transport by $u$ is admissible
for every permutation of $A$, even one which fails to preserve the classes:
all surjections are arrows, and the preceding term-closure argument
distinguishes those arrows from the symmetry group $G$. Along a word $w$
lift $X$ by placing its row at $(v,t)$ into the row at $(vw,t)$, with empty
rows off that suffix. Right cancellation makes this well-defined. The lift
has the original pin and symmetry. In particular ordinary BF holds at
every type at every point.

There are at most $\kappa$ signature sentences. For each one realized under
some assignment of its constants, choose such an assignment and a separate
letter $j$. Initially assign distinct individuals to the individual names.
Choose a surjection $s_j$ taking these individuals to their chosen values
for the given sentence; at most $\kappa$ prescriptions leave $\kappa^+$
points free. For each relational name $c$, lift the chosen value to
$B_{j,c}$ along $(\varepsilon,s_j)$. In the designated interpretation put
the row of $c$ at $(vj,t)$ equal to the $(v,t)$-row of $B_{j,c}$ and use
empty rows elsewhere. The union of the pins for $B_{j,c}$ has size at most
$\kappa$, and each profile is symmetric. Transport along $(j,s_j)$
simultaneously realizes the chosen assignment on the sentence's constants.
Conversely, truth at any arrow gives truth under the transported assignment
at the single object. This gives the dual Logical Necessity schema for
each pure matrix and each list of distinct matching constants. For a
global interpretation use the rooted unfolding with each history carrying
the transport of the designated constants.

## Two pins suffice to refute Transversal

If $P_1,P_2$ both pin a profile $Y$, then $P_1\cap P_2$ pins it. Indeed,
given $s,t$ agreeing on their intersection, combine $s|_{P_1}$ with
$t|_{P_2}$. The prescriptions agree and their entire domain has size at
most $\kappa$, so they extend to a surjection $u:A\to A$. At every fixed
word $Y_{(w,s)}=Y_{(w,u)}=Y_{(w,t)}$.

Suppose that $F$ selects exactly one individual property from each
current coextension class, and let $P$ pin $F$. Take a class $C$ disjoint
from $P$ and $a\in C$. The profile $X_a(w,s)=[s(a)]_\sim$ is symmetric,
pinned by $\{a\}$, and has current row $C$. Let $Y$ be the unique
$F$-selected representative with this row, and choose a pin $T$ for $Y$.
Write $H$ for the subgroup fixing $P$ pointwise and $C$ as a set.

For $g\in H$, pinning gives $gF=F$ and symmetry takes the current
membership of $Y$ to that of $gY$. The current row of $gY$ is $gC=C$, so
uniqueness gives $gY=Y$ as entire entities. Choose $g\in H$ moving
every element of $T\setminus P$ outside $T\cup P$. This is possible by
transposing those elements with fresh individuals in their own classes;
each class has size $\kappa^+$, and the forbidden set has size at most
$\kappa$. The set $g[T]$ pins $gY=Y$. The intersection lemma gives a
pin $T\cap g[T]\subseteq P$ for $Y$. Hence $P$ pins $Y$.

Every automorphism fixing $P$ now fixes $Y$ and its current row $C$.
Choose another class disjoint from $P$ and swap the two classes by a
bijection, fixing their complement. This contradicts invariance of $C$.
Thus Transversal itself fails. Its unboxed and necessary forms both fail
at the designated point.

## Additional verdicts

The [symmetric surjection product](symmetric-surjection-products.html),
§§4–8, supplies the proofs of the following positive verdicts. We spell
out where restricting the symmetry group matters.

- **Necessary Boolean Completeness.** Given the actual row $E$ of a
  $P$-pinned family, form the rowwise union of $a_{(w,t)}$ over $a\in E$
  and $t|_P=s|_P$ at $(w,s)$. This is symmetric and $P$-pinned. For a
  proposed upper bound with pin $Q$, and member $a\in E$ with pin $L$,
  choose $g\in G$ fixing $P$ and moving $L\setminus P$ off $Q$. Use
  within-class transpositions as above. Then $ga\in E$. Combine $s|_Q$
  with the prescription $u(g l)=t(l)$ on $g[L]$ to obtain a surjection
  $u$. Thus $a_{(w,t)}=(ga)_{(w,u)}$ is below the proposed bound at
  $(w,s)$. This proves leastness for every admitted family.
- **Necessary Tame Rigidity and the two rigid powers.** The exact-image
  argument and the power lifting argument of §§6–7 apply verbatim. Their
  hulls at $(w,s)$ are unions of $(w,t)$-images for $t$ agreeing with $s$
  on the pin; left composition by $g\in G$ gives their symmetry.
  Factorizations, bounded partial prescriptions and bijections between
  the complements of pins use arbitrary surjection arrows. No step
  requires such a bijection to be a member of $G$. In particular the
  power lifting argument chooses $j$ agreeing with $s$ on the tester's
  pin, bijective from its complement onto the complement of its image.
  The pullback of a rigid subrelation along $(w,j)$ is stable under
  all surjections fixing the tester's pin and the preimage of the
  target pin. Its direct-image profile is the required rigid witness.
- **Atomlessness and both Axioms of Infinity.** Split a nonzero
  proposition by whether a surjection identifies two individuals outside
  its pin. Both choices extend to surjections agreeing on the pin, and
  the splitting condition is symmetric. The profile whose rows are all
  the sets of standard numeral denotations at the indicated type is
  symmetric and empty-pinned. Its current row is inductive, and every
  inductive property contains those numerals. The infinite individual
  and proposition domains therefore have no finite Frege count.
- **Failure of Relational and Intensional Choice.** A selector for
  membership in nonempty individual properties has a pin $P$. Take two
  distinct individuals $a,b$ in a class outside $P$ and use the union
  of their haecceities. The transposition of $a,b$ fixes this property
  and the selector, and exchanges its two potential outputs. For
  Intensional Choice take the necessarily nonempty property
  $\lambda x.x\ne a$. If a uniquely instantiated subproperty has pin
  $P$, choose a surjection collapsing $P\cup\{a\}$ onto $b$. Its
  unique current output there is some $y\ne b$. A class automorphism
  fixing $b$ can move $y$ within its class. Composing that automorphism
  with the collapse preserves its restriction to $P$, contradicting
  symmetry of the singleton output.
