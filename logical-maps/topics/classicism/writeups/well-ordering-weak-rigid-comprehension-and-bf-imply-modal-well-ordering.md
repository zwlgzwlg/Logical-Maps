# Well-Ordering, Weak Rigid Comprehension and BF imply Modal Well-Ordering

Cian Dorr sketched the argument on 7 October 2026: from a well-order, build a
rigid property of rigid initial segments, and hope that it is *necessarily*
well-ordered by inclusion. Claude Opus 5.5 (Anthropic) filled in the steps
the same day. The new idea is in Step 4, where separation is handled by
applying weak inextensibility to the strict segments. Cian Dorr checked the
argument as first written. This version reorganizes the notation and has not
been independently checked.

**Claim.** For each type $\sigma$:
$$
\exists R^{\sigma\sigma t}\, .\,\operatorname{WO}(R),\quad
\text{Weak Rigid Comprehension at }\sigma t\text{ and }(\sigma t)t,\quad
\text{BF at }\sigma
\ \vdash_{\mathrm C}\ 
\exists R'^{\sigma\sigma t}\, .\,\Box\operatorname{WO}(R').
$$

WO, Trans, Antisymm, Total, WellFounded and WeaklyRigid are as in
Background. $A\le B$ is entailment, $\Box\forall y\, .\,Ay\to By$. It is
necessary when true, by 4, and at any world it implies inclusion there, by T.
$A<B$ means $A\le B\land A\ne B$.

## Two facts about weak rigidity

**(F1) Inclusion.** If $A$ and $B$ are weakly rigid and $\forall y\,
.\,Ay\to By$, then $A\le B$. *Proof.* Each instance $y$ of $A$ is an instance
of $B$, so $\Box By$ by weak persistence of $B$. Weak inextensibility of $A$
with $X:=B$ gives $A\le B$.

**(F2) Identity.** Coextensive weakly rigid properties are identical. By (F1)
each entails the other, and Intensionality applies.

## Setup

Let $R$ be a well-order and write $x\preceq y$ for $(Rx)y$, and $x\prec y$ for
$x\preceq y\land x\ne y$. Define relations of type $\sigma\to(\sigma t)\to t$:
$$
\begin{aligned}
JxY&:=\operatorname{WeaklyRigid}(Y)\land\forall y\, .\,Yy\leftrightarrow y\preceq x,\\
KxY&:=\operatorname{WeaklyRigid}(Y)\land\forall y\, .\,Yy\leftrightarrow y\prec x.
\end{aligned}
$$
By Weak Rigid Comprehension at $\sigma t$ and (F2), each $x$ bears $J$ to
exactly one property and $K$ to exactly one property. These are two
*relations*. No function from $\sigma$ to $\sigma t$ is defined, and none is
needed: everything below quantifies over pairs $x,Y$ with $JxY$.

By (F1), if $JxA$, $KxB$ and $JyC$, then
- $B\le A$;
- $C\le B$ when $y\prec x$;
- $A\le C$ when $x\preceq y$.

These are necessary, by 4.

Separately, Weak Rigid Comprehension at $(\sigma t)t$ gives a weakly rigid
$R^*$ coextensive with $\lambda Y\, .\,\exists x\, .\,JxY$. At any world, a
*member* is an instance of $R^*$ there. Actually, the members are exactly the
$Y$ with $JxY$ for some $x$, and by weak persistence each of them is
necessarily a member.

Weak inextensibility of $R^*$ is used repeatedly in the following form. If
$\Box\psi(A)$ whenever $JxA$, then $\Box\forall M\, .\,R^*M\to\psi(M)$: apply
it with $X:=\lambda M\, .\,\psi(M)$.

## Step 1: necessarily, the members form a chain under $\le$

If $JxA$ and $JyC$, then $A\le C$ or $C\le A$, since $R$ is total, and this is
necessary by 4. Fix $A$ with $JxA$. Weak inextensibility of $R^*$ gives
$\Box\forall M\, .\,R^*M\to(A\le M\lor M\le A)$. This holds for every such
$A$, so applying weak inextensibility again, to
$\psi(M):=\forall M'\, .\,R^*M'\to(M\le M'\lor M'\le M)$, gives
$$\Box\forall M\,M'\, .\,R^*M\land R^*M'\to M\le M'\lor M'\le M.$$

## Step 2: necessarily, every nonempty family of members has a $\le$-least instance

Let $\psi(M)$ say: every $\mathcal Z^{(\sigma t)t}$ such that $\mathcal Z M$
holds and every instance of $\mathcal Z$ is a member has a $\le$-least
instance. We show $\Box\psi(A)$ whenever $JxA$, by induction on $x$ along $R$.
The induction applies WellFounded, at the evaluation point, to
$\lambda x\, .\,\exists A\, .\,JxA\land\neg\Box\psi(A)$.

Fix $x$ and $A$ with $JxA$. Suppose $\Box\psi(C)$ whenever $JyC$ with
$y\prec x$. If instead $x\preceq y$, then $A\le C$ necessarily, so $C<A$ is
impossible. So $\Box(C<A\to\psi(C))$ for every $C$ with $JyC$, whatever $y$
is. Weak inextensibility of $R^*$ gives
$$\Box\forall W\, .\,R^*W\land W<A\to\psi(W).$$

At a world $w$, let $\mathcal Z$ be as in $\psi(A)$.
- If some instance $W$ of $\mathcal Z$ satisfies $W<A$, then $\psi(W)$
  supplies a least instance.
- Otherwise every instance $W$ is a member and is comparable with $A$, which
  is a member at $w$, by Step 1. Since $W<A$ fails, $A\le W$. So $A$ is
  least.

So $\Box\psi(A)$, and by weak inextensibility of $R^*$,
$\Box\forall M\, .\,R^*M\to\psi(M)$.

Members may become identical at other worlds, but this does not matter:
the argument only ever looks strictly below $A$ at $w$ itself.

## Step 3: necessarily, every individual belongs to a member

For each actual $t$, take $A$ with $JtA$. Then $At$, so $\Box At$ by weak
persistence, and $\Box R^*A$. So $\forall t\, .\,\Box\exists M\, .\,R^*M\land
Mt$, and BF at $\sigma$ gives $\Box\forall t\,\exists M\, .\,R^*M\land Mt$.

## Step 4: necessarily, distinct individuals are separated by a member

Let
$$\operatorname{Good}(M):=\forall a\,b\, .\,Ma\land Mb\land a\ne b\to
\exists N\, .\,R^*N\land(Na\leftrightarrow\neg Nb).$$
We show $\Box\operatorname{Good}(A)$ whenever $JxA$, by induction on $x$ along
$R$ as in Step 2. Fix $x$, $A$ with $JxA$ and $B$ with $KxB$, and suppose
$\Box\operatorname{Good}(C)$ whenever $JyC$ with $y\prec x$.

(i) *Weak inextensibility of $A$*, with $X:=\lambda t\, .\,t=x\lor Bt$. An
actual instance $t$ of $A$ satisfies $t\preceq x$. Either $t=x$, and
$\Box\, t=x$ by the necessity of identity, or $t\prec x$, and then $Bt$, so
$\Box Bt$ by weak persistence of $B$. Hence
$$\Box\forall t\, .\,At\to t=x\lor Bt.$$

(ii) *Weak inextensibility of $B$*, with
$X:=\lambda t\, .\,\exists M\, .\,R^*M\land Mt\land M\le B\land
\operatorname{Good}(M)$. An actual instance $t$ of $B$ satisfies $t\prec x$.
Take $C$ with $JtC$. Then $\Box R^*C$ and $\Box Ct$ by weak persistence;
$C\le B$, and so $\Box\,C\le B$; and $\Box\operatorname{Good}(C)$ by the
induction hypothesis. Hence
$$\Box\forall t\, .\,Bt\to\exists M\, .\,R^*M\land Mt\land M\le B\land
\operatorname{Good}(M).$$

At a world $w$, let $a\ne b$ be instances of $A$.
- **Both are instances of $B$.** By (ii) they lie in Good members $M_1$ and
  $M_2$. By Step 1 one of these, say $M_2$, includes the other. It contains
  both, and its Goodness gives a separating member.
- **One of them, say $a$, is not an instance of $B$.** Then $a=x$, by (i).
  Since $b\ne a$, (i) gives $Bb$, and (ii) gives a member $M_2$ with $M_2b$
  and $M_2\le B$. So $M_2a$ fails, and $M_2$ separates $a$ from $b$.
- **Neither is an instance of $B$.** This cannot happen: then $a=x=b$, by (i).

So $\Box\operatorname{Good}(A)$. By weak inextensibility of $R^*$, necessarily
every member is Good.

This is where the obvious argument fails. If $x$ is identified at $w$ with
some $y\prec x$, then $A$ and $B$ can coincide at $w$. The induction cannot
then be run through members strictly below $A$, and applying weak
inextensibility to $B$ avoids the problem.

## Step 5: the necessary well-order

Put
$$R':=\lambda x\,y\, .\,\forall M\, .\,R^*M\land My\to Mx.$$
At any world $w$:
- **Trans.** Immediate.
- **Total.** Suppose $(R'x)y$ fails: some member $M$ has $My$ but not $Mx$.
  Let $N$ be any member with $Nx$. By Step 1, $N\le M$ or $M\le N$. The first
  would give $Mx$, so $M\le N$, and $Ny$. Hence $(R'y)x$.
- **Antisymm.** Let $(R'x)y$ and $(R'y)x$ with $x\ne y$. By Step 3, $x$ and $y$
  lie in members, and by Step 1 the larger of these contains both. By Step 4
  some member contains exactly one of them. That contradicts one of the two
  hypotheses.
- **WellFounded.** Let $X$ be instantiated at $w$. The family
  $\mathcal Z:=\lambda M\, .\,R^*M\land\exists y\, .\,Xy\land My$ consists of
  members and is instantiated, by Step 3. By Step 2 it has a least instance
  $M_0$, which contains some $y_0$ with $Xy_0$. Let $y$ be any instance of
  $X$. Every member containing $y$ belongs to $\mathcal Z$, so it includes
  $M_0$ and therefore contains $y_0$. So $(R'y_0)y$. Thus $y_0$ is $R'$-least
  among the instances of $X$, and by Antisymm it is $R'$-minimal.

So $\Box\operatorname{WO}(R')$, as required.

## What is used

- Well-Ordering, only at the evaluation point: totality in Step 1, and
  well-foundedness for the two inductions.
- Weak Rigid Comprehension at $\sigma t$ (for $J$ and $K$) and at
  $(\sigma t)t$ (for $R^*$).
- BF at $\sigma$, once, in Step 3.
- From C itself: necessity of identity, 4, T, Intensionality, and
  comprehension for the properties used in the inductions.

With boxed premises the same argument gives the boxed conclusion. That
conclusion already follows, because Modal Well-Ordering implies its own
necessitation by 4.
