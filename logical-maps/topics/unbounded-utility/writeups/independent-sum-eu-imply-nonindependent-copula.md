# Nonindependent copulas, mixtures, and invariance

The product copula is the unique copula whose sum operation commutes with
every mixture of marginal laws. But this identity of **laws** is not necessary
for sum invariance of a **preference relation**. There are whole families of
nonindependent copulas satisfying invariance in total DU models. Consequently
a recipe refuting every nonindependent copula cannot exist in this framework.

Zachary Goodsell proposed the question on 3 October 2026. The binary
commutation test and interior-perturbation theorem below are GPT-6 (Codex)'s
arguments from that session. The separate quarter-shuffle witness in §4
was already supplied by the earlier AI report communicated by Branden
Fitelson. No independent checker or literature-priority claim is asserted.

For a copula $C$, let

$$T_{C,\nu}(\mu)=\mathcal L(Q_\mu(U)+Q_\nu(V)),\qquad(U,V)\sim C.$$

Under Stochastic Equivalence, the fixed-copula invariance principle says
that every $T_{C,\nu}$ preserves and reflects comparisons. This is different
from requiring $T_{C,\nu}$ to preserve convex combinations as measures.

## 1. A complete binary test for mixture commutation

Suppose for all laws $\mu_0,\mu_1,\nu$ and $0<p<1$,

$$T_{C,\nu}(p\mu_0+(1-p)\mu_1)
 =pT_{C,\nu}(\mu_0)+(1-p)T_{C,\nu}(\mu_1).\tag{1}$$

Choose $\mu_0=\delta_0$, $\mu_1=\delta_2$, and
$\nu=q\delta_0+(1-q)\delta_1$. In the left-hand law, the probability
of zero is $H_C(p,q)$. In the right-hand law it is $pq$, because a
constant summand leaves no dependence choice. Thus (1) implies
$H_C(p,q)=pq$ for every $p,q$, and $C=\Pi$.
Conversely, independent convolution is linear, so the product copula
satisfies (1).

This is an explicit recipe for witnessing **failure of mixture commutation**
for any $C\ne\Pi$: select a point where $H_C(p,q)\ne pq$ and use those
two binary lotteries. Both resulting sum laws nevertheless have the same
finite mean, $2(1-p)+(1-q)$. Simple EU makes them indifferent, so this law
inequality by itself gives no preference contradiction.

For example, the quarter shuffle has $H_C(1/4,1/4)=0\ne1/16$.
The interior perturbation below has $H_C(1/2,1/2)=9/32\ne1/4$.

## 2. Bounded zero-mean signed differences are indifferent

Assume Expected Utility, Stochastic Equivalence and Mixture Independence.
Suppose two probability laws $\alpha,\beta$ have difference
$\eta=\alpha-\beta$ supported in a bounded interval, with

$$\eta(\mathbb R)=0,\qquad\int x\,d\eta(x)=0.$$

Write $\eta=\eta^+-\eta^-$ for its Jordan decomposition, with common
mass $m\in[0,1]$. If $m=0$, the laws coincide. If $m>0$, the normalized
laws $A=\eta^+/m$ and $B=\eta^-/m$ are bounded, have the same finite
mean, and are indifferent by Expected Utility. Moreover

$$\rho=\alpha-\eta^+=\beta-\eta^-$$

is a positive measure of mass $1-m$. If $m=1$, the desired indifference
is precisely that of $A,B$. Otherwise both laws are mixtures of $A,B$
with the common law $\rho/(1-m)$, so Mixture Independence gives
$\alpha\sim\beta$.

This uses Expected Utility on bounded, possibly nonsimple laws. It does
not assume that DU by itself implies that axiom. No expectations of
$\alpha$ or $\beta$ are required to exist.

## 3. A fixed nonindependent copula equivalent to independence in preference

Put

$$f(u)=\mathbf1_{[1/4,1/2)}(u)-\mathbf1_{[1/2,3/4)}(u),\qquad
c(u,v)=1+\tfrac12 f(u)f(v).$$

The density $c$ lies between $1/2$ and $3/2$, and both its marginals are
uniform since $\int f=0$. It therefore defines a copula $C$, chosen once
for all marginals. It differs from the product on sets of positive measure.

For arbitrary real laws $\mu,\nu$, the difference

$$\eta=T_{C,\nu}(\mu)-T_{\Pi,\nu}(\mu)$$

is the pushforward of $\tfrac12 f(u)f(v)\,du\,dv$ under
$(u,v)\mapsto Q_\mu(u)+Q_\nu(v)$. That signed density is supported
inside $[1/4,3/4]^2$. Quantiles of real laws are bounded on that square,
so $\eta$ is supported in a bounded interval. It has mass zero, and

$$\begin{aligned}
\int x\,d\eta(x)
&=\tfrac12\iint[Q_\mu(u)+Q_\nu(v)]f(u)f(v)\,du\,dv\\
&=\tfrac12\left(\int Q_\mu f\right)\left(\int f\right)
 +\tfrac12\left(\int f\right)\left(\int Q_\nu f\right)=0.
\end{aligned}$$

All integrals on the right are finite. By §2,

$$T_{C,\nu}(\mu)\sim T_{\Pi,\nu}(\mu)\quad\text{for every }\mu,\nu.\tag{2}$$

With Rich Outcomes, all intermediate real laws are available. Stochastic
Equivalence identifies any actual pair admitting a copula with the
corresponding quantile sum law. Independent triples can be realized on the
standing atomless space. Consequently, under the assumptions of §2,
Independent Sum Invariance and $\operatorname{SC}(C)$ are equivalent,
by applying (2) to each side of a comparison.

In particular,

$$\text{Rich Outcomes + EU + Stochastic Equivalence + Mixture Independence
 + Independent Sum Invariance}$$

implies **Existential Nonindependent Copula Sum Invariance**. The proved
[total independent-sum extension](conjectured-total-independent-sum-extension.html)
satisfies these assumptions, so this gives a total DU consistency witness.

More generally, the same proof works whenever $C-\Pi$ is supported in an
interior square $[a,1-a]^2$, $0<a<1/2$. Its signed marginals vanish because
both measures are copulas, which supplies the zero first moment. For instance,
replace $1/2$ above by any nonzero coefficient $\epsilon$ with
$|\epsilon|\le1$. These copulas can be arbitrarily close to independence.

## 4. Another family already present: copulas avoiding simultaneous tails

The earlier report's adjacent-quarter shuffle sends

$$\sigma(u)=\begin{cases}
u+1/4,&0\le u<1/4,\\
u-1/4,&1/4\le u<1/2,\\
u+1/4,&1/2\le u<3/4,\\
u-1/4,&3/4\le u<1.
\end{cases}$$

The copula of $(U,\sigma(U))$ is manifestly nonindependent. Its already
recorded [full proof](calibrated-geometric-continuous-ultrafilter.html#shared-clipping-and-shuffle-copula-proof)
shows that continuous clipped-expectation preferences satisfy its invariance.

The reason generalizes: if a fixed copula is supported where at least one
coordinate belongs to $[a,1-a]$ for some $a>0$, then for each pair of
marginals $\min(|Q_\mu(U)|,|Q_\nu(V)|)$ has a finite uniform bound.
For clipping $q_i$ to any windows expanding to both infinities,

$$|q_i(x+z)-q_i(x)-q_i(z)|\le2\min(|x|,|z|).$$

Dominated convergence therefore gives

$$E q_i(X+Z)-E q_i(X)-E q_i(Z)\longrightarrow0.$$

The continuous ultrafilter comparison ignores this vanishing error in both
directions. Thus every such copula gives full invariance in those total
DU models. This sufficient support condition is not asserted to be necessary.

## 5. What remains of a counterexample recipe

There is a general **sufficient certificate**, but no guarantee of finding it
for every nonindependent copula. For a proposed comparison $\mu\succeq\lambda$,
choose background laws $\nu_1,\ldots,\nu_n$ and nonnegative weights summing
to one. If

$$\sum_j a_j T_{C,\nu_j}(\lambda)$$

strictly stochastically dominates
$\sum_j a_jT_{C,\nu_j}(\mu)$, then fixed-copula weak preservation and
Mixture Independence rule out the proposed comparison. A zero background
may include the untransformed pair. The St Petersburg proof is an explicit
certificate of this kind for the diagonal copula, with an additional
equal-mean connection handling the reverse orientation.

For other copulas, the remaining substantive task is to find such dominance
certificates or other inconsistent comparison cycles, respecting any needed
cancellation directions. Failure of (1) does not supply them: the binary
test in §1 produces equal-mean bounded laws, and §§3–4 give copulas for
which a universal impossibility theorem would be false.
