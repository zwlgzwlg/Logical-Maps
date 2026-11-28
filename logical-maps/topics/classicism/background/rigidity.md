# Rigidity

::: definition {#rigidity-predicates}
title: persistence, inextensibility and rigidity
---
For a relation $Y$ with a finite argument tuple, including the empty tuple,
the comprehension predicates are:

$$
\begin{aligned}
\operatorname{Persistent}(Y)&:=Y\le\lambda\bar x\, .\,\Box Y[\bar x],\\
\operatorname{Inextensible}(Y)&:=\Box\forall X\, .\,
  (\forall\bar x\, .\,Y[\bar x]\to\Box X[\bar x])\to Y\le X,\\
\operatorname{Rigid}(Y)&:=\operatorname{Persistent}(Y)\land
  \operatorname{Inextensible}(Y).
\end{aligned}
$$
:::

This is the rigidity convention of §2.3, p. 28. Gallin's alternative
convention has its own principle.

::: definition {#weak-rigidity-predicates}
title: the weak variants
---
Since $Y\le Z$ is itself the necessary universal closure of the pointwise
implication, $\operatorname{Persistent}(Y)$ unpacks as
$\Box\forall\bar x\, .\,Y[\bar x]\to\Box Y[\bar x]$, and both
conjuncts of $\operatorname{Rigid}$ carry a leading $\Box$. Dropping it
gives the weak variants:

$$
\begin{aligned}
\operatorname{WeaklyPersistent}(Y)&:=\forall\bar x\, .\,
  Y[\bar x]\to\Box Y[\bar x],\\
\operatorname{WeaklyInextensible}(Y)&:=\forall X\, .\,
  (\forall\bar x\, .\,Y[\bar x]\to\Box X[\bar x])\to Y\le X,\\
\operatorname{WeaklyRigid}(Y)&:=\operatorname{WeaklyPersistent}(Y)\land
  \operatorname{WeaklyInextensible}(Y).
\end{aligned}
$$
:::

$\operatorname{Rigid}$ is thus necessary weak rigidity {lean: Classicism.rigid_iff_box_weaklyRigid}. These are the
conventions of Dorr, *Boolean Completeness does not imply Rigid
Comprehension*, pp. 2 and 12. By T, rigidity implies weak rigidity, persistence weak
persistence, and inextensibility weak inextensibility
{lean: Classicism.weaklyRigid_of_rigid, Classicism.weaklyPersistent_of_persistent, Classicism.weaklyInextensible_of_inextensible}.

::: lemma {#rigid-necessary}
title: rigidity, if true, is necessary
lean: Classicism.rigid_necessary
---
If $X$ is rigid, then $\Box\operatorname{Rigid}(X)$.

*Proof.* $\operatorname{Rigid}(X)$ is $\Box\operatorname{WeaklyRigid}(X)$, and
[[modal-four|4]] gives $\Box\Box\operatorname{WeaklyRigid}(X)$, which is
$\Box\operatorname{Rigid}(X)$. $\square$
:::

::: lemma {#weakly-rigid-persistent}
title: weakly rigid relations are persistent
lean: Classicism.persistent_of_weaklyRigid
sources: Dorr, Boolean Completeness does not imply Rigid Comprehension, draft of 30 July 2026
---
A weakly rigid relation is persistent: weak
inextensibility applied to $\lambda\bar x\, .\,\Box Y[\bar x]$, whose
hypothesis $Y[\bar x]\to\Box\Box Y[\bar x]$ holds by weak persistence and 4,
gives $Y\le\lambda\bar x\, .\,\Box Y[\bar x]$. So weak rigidity is equivalently
persistence together with weak inextensibility, the combination used in the
draft's Proposition 1.
:::

::: lemma {#coextensive-weakly-rigid-identical}
title: coextensive weakly rigid relations are identical
lean: Classicism.eq_of_weaklyRigid_coext
---
If $F$ and $G$ are weakly rigid and coextensive, then $F=G$.

*Proof.* Each is below the other: $F\le G$ by weak inextensibility of $F$, since each
instance of $F$ is an instance of $G$ and so, by weak persistence of $G$, necessarily one;
and $G\le F$ likewise. Since $\le$ is antisymmetric, $F=G$. $\square$
:::

## Closure properties

The lemmas below use no BF, choice, ND or comprehension. That BF at $\sigma$ makes
$\lambda z^\sigma\, .\,\top$ weakly rigid, and □BF makes it rigid, are forms of
[[barcan-r|BF]] and [[necessary-barcan-r|□BF]].

::: lemma {#haecceities-rigid}
title: haecceities are rigid
lean: Classicism.Rigidity.singleton_rigid
credit: GPT-6 Astra (OpenAI), prompted by Daniel Kodsi, 22 October 2026
---
For every $x^\sigma$, the haecceity $H_x=\lambda y\, .\,y=x$ is rigid.

*Proof.* It is persistent by [[identity-necessary-r|NI]]. For inextensibility, suppose,
at any world, that $\forall y\, .\,y=x\to\Box Zy$. Then $\Box Zx$, and so
$\Box\forall y\, .\,y=x\to Zy$, which is $H_x\le Z$. $\square$
:::

::: lemma {#rigid-indexed-union}
title: rigid unions of rigid families
lean: Classicism.Rigidity.indexed_union_rigid
credit: GPT-6 Astra (OpenAI), prompted by Daniel Kodsi, 22 October 2026
---
If $R^{\sigma t}$ is rigid and $F^{\sigma\tau t}$ is such that $Fx$ is rigid for every $x$
with $Rx$, then the union $U:=\lambda y\, .\,\exists x\, .\,Rx\land(Fx)y$ is rigid.

*Proof.* First, necessarily every instance of $R$ has a rigid fiber. For each $x$ with
$Rx$, $Fx$ is rigid and so, by [[rigid-necessary]], necessarily rigid; so by the
inextensibility of $R$, $R\le\lambda x\, .\,\operatorname{Rigid}(Fx)$. Now argue at an
arbitrary world, where $R$ is weakly rigid and each instance of $R$ has a rigid fiber.
*Weak persistence:* if $Uy$, take $x$ with $Rx$ and $(Fx)y$; then $\Box Rx$ and
$\Box(Fx)y$, so $\Box Uy$. *Weak inextensibility:* suppose $\forall y\, .\,Uy\to\Box Zy$.
For each $x$ with $Rx$, $\forall y\, .\,(Fx)y\to\Box Zy$, so $Fx\le Z$ by the
inextensibility of $Fx$; that is, $\Box(\forall y\, .\,(Fx)y\to Zy)$. By the weak
inextensibility of $R$, $R\le\lambda x\, .\,\forall y\, .\,(Fx)y\to Zy$, which gives
$U\le Z$. Both hold at every world, so $U$ is rigid. $\square$
:::

::: lemma {#rigid-direct-image}
title: rigidity is preserved by direct images
lean: Classicism.Rigidity.direct_image_rigid
credit: GPT-6 Astra (OpenAI), prompted by Daniel Kodsi, 22 October 2026
---
If $R^{\sigma t}$ is rigid and $f^{\sigma\tau}$ is an operation ($\tau\ne e$), then
$\lambda y\, .\,\exists x\, .\,Rx\land y=fx$ is rigid.

*Proof.* It is the union of the haecceities $H_{fx}$ over the instances of $R$, rigid by
[[haecceities-rigid]] and [[rigid-indexed-union]]. $\square$
:::

::: lemma {#rigid-inverse-image}
title: rigidity is preserved by inverse images under necessarily injective operations
lean: Classicism.Rigidity.inverse_image_rigid
credit: GPT-6 Astra (OpenAI), prompted by Daniel Kodsi, 22 October 2026
---
If $P^{\tau t}$ is rigid, every instance of $P$ is a value of $f^{\sigma\tau}$
($\tau\ne e$), and $f$ is necessarily injective, then $\lambda x\, .\,P(fx)$ is rigid.

*Proof.* Persistence is inherited from $P$. Being a value of $f$ is necessary if true, by
[[identity-necessary-r|NI]], so the inextensibility of $P$ makes every instance of $P$
necessarily a value of $f$. For inextensibility, suppose, at a world,
that $\forall x\, .\,P(fx)\to\Box Zx$, and put $Z':=\lambda y\, .\,\forall x\, .\,y=fx\to Zx$.
If $Py$, then $y=fx_0$ for some $x_0$, so $\Box Zx_0$; since $f$ is necessarily injective,
necessarily every $x$ with $fx=fx_0$ is $x_0$, so $\Box Z'y$. By the inextensibility of
$P$, $P\le Z'$, and so $\Box\forall x\, .\,P(fx)\to Zx$. Both the range condition and
injectivity keep their modal scopes. $\square$
:::

## Internally finite bounds

::: lemma {#internally-finite-rigid-power}
title: both canonical powers are rigid for a Frege-finite weakly rigid bound
credit: OpenAI Codex (GPT-6), prompted by Daniel Kodsi, 26 November 2026
---
Write $\operatorname{Fin}(A)$ for the assertion that some Frege finite
cardinality counts the current extension of $A$. For a weakly rigid
$F^{\sigma t}$ with $\operatorname{Fin}(F)$, C proves
$\Box\operatorname{Fin}(F)$ and the identity and rigidity of its two canonical
power predicates
$$
 P(F)(X)=\operatorname{Rigid}(X)\land X\le F,\qquad
 Q(F)(X)=\operatorname{WeaklyRigid}(X)\land X\le F.
$$
This includes nonstandard finite counts. For a finite argument tuple,
use Frege finiteness of its tuple codes as explained below.

*Finite rigid representatives.* Every internally finite predicate $A$ has a
rigid predicate with the same current extension. Induct on a number $n$
counting $A$, universally over $A$. At zero use bottom. At a successor
remove the witnessing member $a$, apply induction, then adjoin the rigid
haecceity of $a$. A binary union of rigid predicates is rigid: persistence
distributes over the union, and at any point a test necessary on the members
of the union is necessary on the members of each constituent. By
[[coextensive-weakly-rigid-identical]] the representative is unique and a
weakly rigid $A$ already equals it. A subproperty of an internally finite
current extension is internally finite, by the same induction: delete the
chosen $a$ from the subset if it occurs, and use cardinal addition to
restore it. These assertions concern actual coextension and Frege
counting. They use neither BF nor a choice operation selecting the
representatives; see [[finite-cardinality-arithmetic]].

*Induction for the power.* Induct on the number counting $F$, with $F$
universally quantified and weakly rigid. Prove together
$\Box\operatorname{Fin}(F)$ and $\operatorname{Rigid}(P(F))$. At zero,
$F$ is bottom as a whole intension by weak inextensibility, and $P(F)$ is
the haecceity of bottom. At a successor choose a member $a$ and take a
rigid representative $G$ of $F$ with $a$ removed from its *current*
extension. Coextensive predicates have the same finite counts, so the
induction hypothesis gives $\Box\operatorname{Fin}(G)$ and rigidity of
$P(G)$. The two weakly rigid predicates $F$ and $G\lor H_a$ have the same
current extension, hence $F=G\lor H_a$ as intensions. At each future
point adjoining its transported $a$ to the finite extension of $G$
either leaves that extension intact or adds one member. Thus
$\Box\operatorname{Fin}(F)$.

At every future point, including the identity, let $X$ be a rigid
subrelation of $F$. If $Xa$ is false there, then $X$ is currently
contained in $G$. Since $G$ is persistent, weak inextensibility of $X$
gives $X\le G$. If $Xa$ is true, $X\land G$ at this point is a subproperty
of the internally finite $G$. Let $Y$ be a rigid representative of its
current extension. Then $Y\le X,G$ by weak inextensibility of $Y$ and
persistence of $X,G$. The rigid predicates $X$ and $Y\lor H_a$ are
currently coextensive, hence identical. Conversely every rigid
$Y\le G$ and every $Y\lor H_a$ of this form are rigid and below $F$.
Therefore $P(F)$ is, as a whole intension, the union of $P(G)$ and its
direct image under $Y\mapsto Y\lor H_a$. Both are rigid by the induction
hypothesis and [[rigid-direct-image]], completing the induction. The
case division is made anew at each world and allows distinct individuals
or relations to merge later.

At any future world each weakly rigid $X\le F$ has internally finite
extension, since $F$ does there. The finite representative argument makes
$X$ rigid. Thus $Q(F)=P(F)$ by Intensionality.

*Tuple inputs.* Code $\bar a$ by its tuple-haecceity
$i(\bar a)=\lambda\bar y\, .\,\bigwedge_j(y_j=a_j)$ at the admitted
relation type of the tuple. C proves, also necessarily, that equal codes
have equal coordinates: evaluate both codes on $\bar a$. Define
$F^\#(z)=\exists\bar x\, .\,F(\bar x)\land z=i(\bar x)$.
Take $\operatorname{Fin}(F^\#)$ as the finiteness condition. Coding a
relation this way and pulling a code predicate back along $i$ are
inverse on the subrelations of $F$ and of $F^\#$ throughout the cone.
They transfer weak persistence by necessity of identity. For weak
inextensibility a test on codes pulls back along $i$; in the other
direction extend a tuple test $T$ to
$\lambda z\, .\,\forall\bar x\, .\,z=i(\bar x)\to T(\bar x)$.
Necessary injectivity of the codes transfers the test hypothesis.
Applying this equivalence in each future transfers full rigidity as
well. The canonical powers correspond by these same two term operations
on *relations*. They are direct images of one another, so the established
rigidity at $F^\#$ gives rigidity at $F$ by [[rigid-direct-image]].
This also covers the empty tuple, whose code is top. $\square$

The internal finite-representative lemma appeared in
[relational-coding-recursion, §19.1](https://github.com/dkodsi/Logical-Maps/blob/67b116acaf7cee286614307468f5361f6a195c6e/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/relational-coding-recursion-20261022.md#L732).
The earlier [finite-power calculation, §25.1](https://github.com/dkodsi/Logical-Maps/blob/67b116acaf7cee286614307468f5361f6a195c6e/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/frege-infinity-20261022-1726.md#L885)
establishes *current finiteness* of the property of rigid subsets of a
finite predicate. The earlier [finite-list power proof](https://github.com/dkodsi/Logical-Maps/blob/67b116acaf7cee286614307468f5361f6a195c6e/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/maximalism-modal.md#L348)
establishes rigidity for externally finite bounds. The induction above
gives rigidity for all internally finite weakly rigid bounds.
:::


::: lemma {#finite-subrelations-of-rigid-bounds}
title: testing finite subrelations of arbitrary weakly rigid bounds
---
Work at a point with a weakly rigid unary predicate $F$ on type $\sigma$.
Let $N=\mathbb N_\sigma$ denote Frege numberhood and put
$$
 L_F(Z):=\operatorname{WeaklyRigid}(Z)\land Z\le F\land
                 \exists n\in N\, .\, n(Z).
$$
Suppose $W$ necessarily holds of each **current** member of $L_F$.
For every **current** $n\in N$,
$$
 \Box\forall Z\, .\,
    (\operatorname{WeaklyRigid}(Z)\land Z\le F\land n(Z))\to W(Z).
 \tag{1}
$$
In particular, at every future $W$ covers every externally finite
weakly rigid subrelation, irrespective of the availability of names
for its tuples. It also covers a subrelation counted by the transport
of a nonstandard current number. The bound $F$ itself can be infinite.

*Proof.* Write $C_n(Z)$ for the three conjuncts in (1). Induct
internally on $n$ with (1) generalized over **all** current testers
$W$ satisfying its hypothesis; $F$ is a fixed parameter. The Frege
induction predicate is an admitted lambda term, including the tester
quantifier and its conditional hypothesis. Numberhood persists.
At zero, a weakly rigid relation with empty current extension is
bottom by weak inextensibility. Bottom is a current member of $L_F$.

For the successor, fix such a tester $W$. For every current $a$ in
$F$ the term $W_a(Y)=W(Y\lor H_a)$ is another tester satisfying the
hypothesis, where $H_a$ is the haecceity of $a$. Indeed every current
member $Y$ of $L_F$ is rigid by [[internally-finite-rigid-power]],
its union with $H_a$ is rigid and internally finite, and $H_a\le F$
by weak persistence. At $n$ the induction hypothesis therefore gives
$$
  \Box\forall Y\, .\,C_n(Y)\to W(Y\lor H_a).
$$
Apply weak inextensibility of $F$ to the tester
$\lambda x\, .\,\forall Y\, .\,C_n(Y)\to W(Y\lor H_x)$.
The implication now holds for **every** $a\in F$ at **every** future
point, with $n,F,W$ transported there.

At such a point let $C_{\operatorname{Suc}(n)}(Z)$ hold. Take an
$a\in Z$ whose deletion leaves a current predicate counted by $n$,
as in the definition of successor. The finite representative
construction in [[internally-finite-rigid-power]] gives a rigid $Y$
coextensive with that deletion; the transported $n$ counts $Y$ by
invariance under current coextension. Since $Z$ is weakly persistent,
every current $Y$-member necessarily belongs to $Z$. Weak
inextensibility of $Y$ gives $Y\le Z\le F$. Thus $C_n(Y)$ holds.
Now $Z$ and $Y\lor H_a$ are coextensive weakly rigid predicates:
weak inextensibility of each and weak persistence of the other yield
both entailments, hence identity. The displayed implication gives
$W(Z)$, completing the Frege induction. For each ordinary finite
cardinality its numeral is already present and correctly counts an
extension of that size at every point. $\square$

If $N$ is currently weakly inextensible, apply its defining property
to $n\mapsto\forall Z\, .\,C_n(Z)\to W(Z)$ in (1). This gives
$L_F\le W$, also for subrelations counted by newly available numbers.
The property $L_F$ is weakly persistent in bare C: its current members
are fully rigid and necessarily finite by [[internally-finite-rigid-power]],
and their entailment of $F$ persists. Thus $L_F$ is weakly rigid. If
$F$ and $N$ are both rigid, the same reasoning at every future gives
full rigidity of $L_F$. For a polyadic bound use the tuple-haecceity
coding and the corresponding Frege numbers on codes as in
[[internally-finite-rigid-power]].

For the unrestricted Rigid Power, any failing test must miss a
**proper** rigid subrelation of the future bound, whose extension no
transported current Frege number counts. Indeed all current finite
members are rigid and so pass the test, while the bound itself is a
current rigid member of its own power and necessarily passes as well.
This deduction applies at the point where weak inextensibility of the
power is tested, which may be a successor of the original point.
For Weakly Rigid Power the same exclusion of finite missed members
applies to its weak-inextensibility test. The additional weak
persistence condition concerns whether a current weak subrelation
can lose weak rigidity. Every internally finite weak subrelation
is already fully rigid.
:::

::: lemma {#rigid-power-unary-tower}
title: testing the power principles on a unary type tower
---
Put $A_0=et$ and $A_{n+1}=A_n t$. For each of Rigid Power and Weakly
Rigid Power, its instances for bounds *of type* $A_m$, as $m$ ranges
over any unbounded subset of the natural numbers, entail every instance
at the same point in C. In particular, a failure at any type implies
a failure at every sufficiently high level of this one tower.

*Coding types.* Every original type admits a closed-term injection into
some $A_n$ whose injectivity is a theorem of C. At $e$ use
$x\mapsto H_x=\lambda y\, .\,y=x$. At $t$ use
$p\mapsto\lambda x^e\, .\,p$. Raise any code to a higher tower level
by iterating the haecceity injection. For a nonempty tuple of already
coded types, raise its coordinates to a common level and use iterated
ordered-pair coding. For two objects of a common type the code is
$$
K(a,b)=\lambda X\, .\,(X=H_a\lor X=(H_a\lor H_b)).
$$
This is necessarily injective. Evaluating equal outer codes on their
singleton and doubleton members gives $a=c$ and $b=d$ from
$K(a,b)=K(c,d)$, including when either doubleton is a singleton. The
[explicit finite calculation](https://github.com/dkodsi/Logical-Maps/blob/67b116acaf7cee286614307468f5361f6a195c6e/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/followup/finite-functional-choice.md#L139)
uses only application of identities. Higher pairing increases the level
by two each time, and the next coordinate can be raised accordingly.
Code the empty tuple by a fixed closed member of $A_0$.

For the inductive step at $\rho=\bar\sigma t$, let
$i(\bar x):A_n$ be the resulting tuple code for its argument types.
Define closed operations, with the indicated arguments abstracted, by
$$
 j(F)=\lambda z^{A_n}\, .\,\exists\bar x\, .\,
          z=i(\bar x)\land F(\bar x),\qquad
 d(B)=\lambda\bar x\, .\,B(i(\bar x)).
$$
At every future point $d(j(F))$ and $F$ have the same extension,
even on arguments first available there. Necessary injectivity and
Intensionality yield $d(j(F))=F$ in C, giving the required injection
into $A_{n+1}$. Repeat this last construction with the tuple code
raised to any higher $A_k$ to get a bound code at $A_{k+1}$.
This construction encodes membership directly at every relational
type. It uses neither Functionality nor Plenitude.

*Transfer of powers.* Put $G=j(F)$. For $X\le F$ the map $j$ has
inverse $d$ on the subrelations of $G$. Indeed $B\le G$ entails
$j(d(B))=B$, since every member of $B$ in every future is then a
tuple code. The operations transfer both weak and full rigidity on
these subrelations, also for the whole bounds. Forward weak persistence
uses necessity of identity for a tuple code, and for weak
inextensibility a tester on codes pulls back along $i$. Conversely
extend a tester $T$ on tuples by
$\lambda z\, .\,\forall\bar x\, .\,z=i(\bar x)\to T(\bar x)$.
Necessary injectivity gives the required test on all transported
members. Doing this at every future gives the full-rigidity equivalence.

Consequently the canonical power at $F$ and that at $G$, using the
same rigidity variant, are each the direct image of the other under
the relation-level terms $j,d$. This holds as an identity of
intensions because the bijection on eligible subrelations works
at each future point. Direct images of rigid relations are rigid
by [[rigid-direct-image]]. The weak version follows by applying a
tester to the image via the defining term and using weak
inextensibility on the source. Thus power at $G$ implies power at
$F$. Here the encoded *argument* type is $A_n$ and the encoded
*bound* type is $A_{n+1}$. $\square$
:::
