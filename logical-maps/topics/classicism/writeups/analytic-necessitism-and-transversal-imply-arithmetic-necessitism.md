# Transversal and Analytic Necessitism imply Arithmetic Necessitism

**Theorem.** Assume Transversal and first-order Analytic Necessitism at the
designated point. At every type $\sigma$, $\Box I^*_\sigma$ implies that
the canonical Frege numbers $N=\mathbb N_\sigma$ are rigid and their distinct
current instances are necessarily distinct. For each $\sigma$ it even
suffices that the coextension transversal for properties of
$\nu=(\sigma t)t$ exist at some accessible point.

The underlying categoricity construction is the natural-number part of
[the map's real-structures isomorphism proof](https://github.com/zwlgzwlg/Logical-Maps/blob/4bb9287187ed7cb09567eb3a6302cb896c986ec4/logical-maps/topics/classicism/background/arithmetic.md#L447).
The argument transfers weak inextensibility along this isomorphism, whose
values continue to match at later points.

## Realizing a real number structure

Fix $\sigma$ and assume $\Box I^*_\sigma$. Write $0,S$ for the canonical
zero and successor. Take a point with a coextension transversal $T$ at
type $\nu$: $T$ holds of exactly one entity from each current coextension
class of properties of $\nu$. This can be the designated point. The
Peano condition $I^*_\sigma$ holds there.

Construct a real number structure at type $\tau=\nu t$. For $n\in N$
put $h_n=\lambda m.m=n$. These haecceities are injective in $n$, by
application at $n$. Take as numbers the $h_n$ for $n\in N$, with
zero $h_0$ and successor $h_n\mapsto h_{Sn}$. The graph and number
predicate are definable by existential quantification over $N$.
The Peano axioms transfer along this bijection. For leastness, if a
property holds of $h_0$ and is closed under that successor, its
pullback $\lambda n.Y(h_n)$ is inductive for the Frege numbers.

Take as reals the entities $x$ satisfying $Tx$ and
$\forall n(xn\to Nn)$. For membership use the relation that holds of
$(h_n,x)$ when $n\in N$, $x$ is one of these reals and $xn$.
Two such reals with the same members agree on $N$ and both have empty
extension outside $N$. The transversal gives their identity as entities.
For any admitted property $Y$ of elements of type $\tau$, take the
unique selected representative of $\lambda n.Nn\land Y(h_n)$.
It is a real with exactly the required members. This proves fullness.
The construction uses only quantified predicates and lambda terms.
The definition permits the number and real sorts to overlap.

Thus $\Diamond\exists\mathfrak R\,\operatorname{Real}_\tau(\mathfrak R)$
at the designated point. This supplies the existence premise of the following lemma for the specified $\sigma$.

## Matching numbers through the cone {#matching-numbers}

**Lemma.** Suppose Analytic Necessitism holds at a point and a real number structure at some one type $\tau$ is possible there. Then both Arithmetic Necessitism and Necessity of Arithmetic hold at that point. The same $\tau$ works for every counting type $\sigma$ for which $\Box I^*_\sigma$ holds.

**Proof.** Analytic Necessitism at $\tau$ supplies a structure $\mathfrak B$ of that type which is rigid and necessarily a real number structure. Write $D,o,A$ for its number predicate, zero and successor graph. The relations $D$ and $A$ are rigid, distinct current $\mathfrak B$-numbers are necessarily distinct, and $(D,o,A)$ is necessarily a Peano system. Fix any counting type $\sigma$ satisfying $\Box I^*_\sigma$ and put $\nu=(\sigma t)t$. The two carrier types $\tau$ and $\nu$ may differ.

At each accessible point, match $o$ to $0$ and corresponding
successors to successors. More precisely let $J(a,n)$ assert
$Da\land Nn$ and membership of $(a,n)$ in every relation containing
$(o,0)$ and closed under $(a,n)\mapsto(a',Sn)$ whenever $Aaa'$.
These variables have types $a:\tau$ and $n:\nu$. The Peano axioms
and the least-relation construction give a bijection between $D$
and $N$ sending $o$ to $0$ and matching successors. This is exactly
the first half of the cited isomorphism lemma, which uses only
the two Peano systems. In particular $J$ is single-valued and onto
in both directions at every accessible point. Use the same defining
formula with the transported parameters of $\mathfrak B$ throughout.

**Matched pairs persist.** At each point in the cone, use Frege induction
on $n$ for
$$
 \forall a\,(J(a,n)\to\Box J(a,n)).
$$
For zero, $a=o$ by the Peano match, identity persists and $J(o,0)$
holds throughout the cone. For $Sn$, let $a$ be its match. The match
$a_0$ of $n$ has $Aa_0a$, by successor preservation and uniqueness
of the match of $Sn$. By induction $J(a_0,n)$ is necessary, and
$Aa_0a$ is necessary by the persistence of the rigid successor graph.
The successor equation then gives $J(a,Sn)$ at every future point.
The induction predicate is an admitted modal formula, so the argument
includes nonstandard current Frege numbers.

**Transfer of weak inextensibility.** At any point in the cone suppose
$X$ is an admitted tester such that each current $n\in N$ necessarily
satisfies $X$. For each current $a\in D$, take its unique matched
$n$. At every future point this same pair still satisfies $J$ and
that $n$ satisfies $X$. Since the match is single-valued there,
$$
 \Box\forall m\,(J(a,m)\to Xm).
$$
Apply weak inextensibility of $D$ with the tester
$\lambda a.\forall m(J(a,m)\to Xm)$. It gives
$\Box\forall a(Da\to\forall m(J(a,m)\to Xm))$.
Each future $m\in N$ has some matching $a\in D$ there, and hence
$\Box\forall m(Nm\to Xm)$. This proves weak inextensibility of $N$
at the arbitrary point. The hypotheses for this transfer, including
the rigid structure and the Peano guard, continue to hold at each
point in the cone. Thus $N$ is inextensible. It is persistent by
[the Frege-number persistence lemma](pure-possibility-implies-axiom-of-infinity-t.html);
together these give rigidity.

Finally, distinct old $m,n\in N$ have distinct $\mathfrak B$-matches.
Those matches stay distinct by rigid structure, and the two matching
pairs persist. Injectivity of the match at every future point forces
the transported $m,n$ to remain distinct. This completes the native
Arithmetic Necessitism conclusion.

For the sentence-level claim, take any fixed arithmetical sentence $P$ at $\sigma$ and any accessible point satisfying the local guard $I_\sigma$. By the [equivalent forms of Potential Infinity](../index.html#background/arithmetic), $I^*_\sigma$ holds there. The ordinary two-type Peano isomorphism identifies the truth of $P$ there with its number-only reading in the transported real structure $\mathfrak B$. Analytic Necessitism gives [Necessity of Analysis](analytic-necessitism-implies-necessity-of-analysis.html). The reading of $P$ in $\mathfrak B$ consequently has the same truth value throughout the cone, since $\mathfrak B$ is necessarily a real structure. This gives $\Box(I_\sigma\to P)\lor\Box(I_\sigma\to\neg P)$ and requires only the *local* guard at each point being compared. [Application to models with disagreeing arithmetic](analysis-with-disagreeing-arithmetic.html)

## Possible Actuality

A reachable point satisfying Actuality supplies the required local
transversals by the [Actuality implication](https://github.com/zwlgzwlg/Logical-Maps/blob/4bb9287187ed7cb09567eb3a6302cb896c986ec4/logical-maps/topics/classicism/results/actuality-implies-transversal.yaml).
Concretely, if $p$ entails every current truth, mask any property $X$
by $\lambda n.p\land Xn$. When $X,Y$ are currently coextensive, $p$
entails the whole sentence $\forall n(Xn\leftrightarrow Yn)$, so the masks
are necessarily coextensive and hence identical. The mask is currently
coextensive with its argument, since $p$ is true. The official schema
also follows with Self-Atomicity at $t$ in place of Transversal, since
[Self-Atomicity at $t$ gives necessary Actuality](https://github.com/zwlgzwlg/Logical-Maps/blob/4bb9287187ed7cb09567eb3a6302cb896c986ec4/logical-maps/topics/classicism/results/self-atomicity-t-implies-necessary-actuality.yaml).
In particular necessary Strong Atomicity and Second-Order Analytic
Necessitism suffice.
