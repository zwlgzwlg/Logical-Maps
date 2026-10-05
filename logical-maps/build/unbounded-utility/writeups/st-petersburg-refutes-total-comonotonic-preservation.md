# St Petersburg gambles force comonotonic incompleteness

Let $S$ be the ordinary St Petersburg game,
$\Pr(S=2^k)=2^{-k}$ for $k\ge1$. The simple witness is

$$\mathcal L(X_1)=\tfrac15\delta_3+\tfrac45\mathcal L(3S),\qquad
\mathcal L(Y_1)=\tfrac25\delta_4+\tfrac35\mathcal L(4S).$$

Thus $X_1$ offers an 80% chance of playing $3S$, otherwise 3;
$Y_1$ offers a 60% chance of playing $4S$, otherwise 4.
The coefficients describe randomized selection, not pointwise sums.

**Theorem.** With Rich Outcomes, Simple EU, Stochastic Dominance and
Mixture Independence:

1. Comonotonic Sum Weak Preservation and Comonotonic Sum Cancellation
   force $X_1$ and $Y_1$ incomparable, without assuming Totality.
2. Totality and Comonotonic Sum Preservation, including its **strict**
   clause, are inconsistent. Cancellation need not be separately assumed.

Stochastic Dominance includes its weak clause and hence supplies Stochastic
Equivalence. Under DU, Simple EU is a derived consequence, so the second
statement excludes comonotonic preservation under DTU. All random variables
used here are finite almost surely; all displayed utility values are
nonnegative. No expectations of unbounded gambles are subtracted.

**Attribution.** The original incompleteness theorem and two-pair mechanism
come from *Comonotonic Sum Invariance Forces Incompleteness*, dated
2 October 2026, an AI-generated proof communicated by Branden Fitelson;
the producing AI was not identified. Fitelson is credited as communicator,
not producer or checker. GPT-6 (Codex) supplied this simpler witness and
three-background identity on 2 October, and the exact preservation/cancellation
audit and direct preservation proof on 3 October 2026. No independent
checker, priority claim, or Lean verification is asserted.

## 1. The two pairs in quantile coordinates

Besides the pair above, use

$$\begin{aligned}
\mathcal L(X_2)&=\tfrac15\delta_0+\tfrac15\delta_5+
                         \tfrac35\mathcal L(4S),\\
\mathcal L(Y_2)&=\tfrac15\delta_0+\tfrac25\delta_6+
                         \tfrac25\mathcal L(6S).
\end{aligned}$$

For $s\in\{1,2\}$ partition $(0,1)$, in order, into
$O,H,P_1,N_1,P_2,N_2,\ldots$. The following table defines increasing
quantile realizations of $X_s,Y_s$. In a tail row put $t=2^k$.
For $s=1$, the initial block $O$ is empty.

| Block | Length | $X_s$ | $Y_s$ |
|---|---|---|---|
| $O$ | $(s-1)/5$ | $0$ | $0$ |
| $H$ | $1/5$ | $2s+1$ | $2s+2$ |
| $P_k$ | $2/(5t)$ | $(s+2)t$ | $(s+1)t$ |
| $N_k$ | $2/(5st)$ | $(s+2)t$ | $2(s+1)t$ |

The lengths sum to one in either case. Each quantile is nondecreasing;
in particular the $Y_s$ value on $N_k$ equals its value on $P_{k+1}$.
The table gives the claimed marginal laws by

$$\mathcal L(aS)=\tfrac12\delta_{2a}+
                       \tfrac12\mathcal L(2aS),\qquad a>0.\tag{1}$$

Quantile representatives and all identities below are understood up to
null endpoints. The standing atomless space realizes every required law.

## 2. One three-background obstruction for both pairs

For each $s$, define $Z_0,Z_1,Z_2$ on the same quantile blocks by the
following table. An entry $(a,b)$ means $a$ on the first half of that block
and $b$ on the second half. Single entries apply on the entire block.

| Block | $Z_0$ | $Z_1$ | $Z_2$ |
|---|---|---|---|
| $O$ | $0$ | $0$ | $0$ |
| $H$ | $2s$ | $(2s+1,2s+2)$ | $(2s+1,2s+2)$ |
| $P_k$ | $st$ | $((s+1)t,2st)$ | $((2s+1)t,3st)$ |
| $N_k$ | $st$ | $2st$ | $(3st,(2s+2)t)$ |

All three columns are nondecreasing for $s=1,2$. For example, in the
last column the within-block inequalities are $2s+1\le3s\le2s+2$;
the last value on $N_k$ is at most the first on $P_{k+1}$ because
$2s+2\le2(2s+1)$. For $Z_1$, use $s+1\le2s\le2(s+1)$.
The head-to-tail inequalities follow on setting $t=2$; $Z_0$ is immediate.
Consequently every background is comonotonic with both $X_s$ and $Y_s$.

The exact signed-law identity is

$$\sum_{j=0}^2\bigl[\mathcal L(X_s+Z_j)-\mathcal L(Y_s+Z_j)\bigr]
   =\tfrac15(\delta_{4s+1}-\delta_{4s+2}).\tag{2}$$

Here is a direct verification, without truncating any tail. The head blocks
contribute $(\delta_{4s+1}-\delta_{4s+4})/5$; the initial zero block
cancels. Write $\mu_a=\mathcal L(aS)$. The tail contributions before
collecting are:

| $s$ | Background | Tail signed measure |
|---|---|---|
| 1 | $Z_0$ | $(4\mu_4-2\mu_3-2\mu_5)/5$ |
| 1 | $Z_1$ | $(4\mu_5-2\mu_4-2\mu_6)/5$ |
| 1 | $Z_2$ | $(3\mu_6-2\mu_5-\mu_8)/5$ |
| 2 | $Z_0$ | $(3\mu_6-2\mu_5-\mu_8)/5$ |
| 2 | $Z_1$ | $(2\mu_8-\mu_6-\mu_{10})/5$ |
| 2 | $Z_2$ | $(2\mu_{10}-\mu_8-\mu_{12})/5$ |

Their sum is, in either case,

$$\tfrac25\mu_{2s+2}+\tfrac15\mu_{4s+2}
 -\tfrac25\mu_{2s+1}-\tfrac15\mu_{4s+4}
 =\tfrac15(\delta_{4s+4}-\delta_{4s+2}),$$

where the equality is two applications of (1). Adding the head contribution
proves (2). These are equalities of finite signed measures, regardless of
the infinite expectations of the positive games.

Suppose $X_s\succeq Y_s$. **Weak preservation** gives
$X_s+Z_j\succeq Y_s+Z_j$ for $j=0,1,2$. Mixture Independence and
transitivity preserve this comparison under equal mixtures of the three
laws. Indeed, componentwise mixture monotonicity follows by replacing one
branch at a time, using law invariance to interchange branches as needed.
After division by three, (2) says that the $Y$ mixture raises mass $1/15$
from $4s+1$ to $4s+2$ relative to the $X$ mixture. Strict Stochastic
Dominance gives the opposite strict comparison. Hence

$$X_1\not\succeq Y_1,\qquad X_2\not\succeq Y_2.\tag{3}$$

**No cancellation, strict preservation, Totality, or Simple EU was used
in this obstruction.**

## 3. The equal-mean connection can be made by preservation alone

Use the same uniform coordinate for both pairs and put
$h_s=Q_{X_s}-Q_{Y_s}$. Their differences are:

| Consecutive interval length | $1/5$ | $1/5$ | $1/5$ | $1/10$ | $1/10$ | $1/20$ | $1/20$ | $\cdots$ |
|---|---|---|---|---|---|---|---|---|
| $h_1$ | $-1$ | $2$ | $-2$ | $4$ | $-4$ | $8$ | $-8$ | $\cdots$ |
| $h_2$ | $0$ | $-1$ | $2$ | $-4$ | $4$ | $-8$ | $8$ | $\cdots$ |

After the first two intervals the tail differences cancel exactly.
Define nondecreasing simple gambles on that coordinate by

$$A(u)=\begin{cases}0&u<1/5,\\2&u\ge1/5,\end{cases}
\qquad
B(u)=\begin{cases}1&u<2/5,\\2&u\ge2/5.\end{cases}$$

Both means are $8/5$, so Simple EU gives $A\sim B$. The table says
$h_1+h_2=A-B$. More concretely, set

$$R=Q_{X_1}+Q_{X_2}-A=Q_{Y_1}+Q_{Y_2}-B.$$

This common remainder is **nondecreasing**. On the first three intervals
of length $1/5$ its values are $3,9,12$. Thereafter $A=B=2$ and both
quantile sums are nondecreasing, with the next value of $R$ equal to 18.
Thus weak preservation applied to $A\sim B$ gives directly

$$X_1+X_2=R+A\sim R+B=Y_1+Y_2.\tag{4}$$

All additions in (4) are comonotonic. This explicit increasing remainder
avoids cancellation in the equal-mean connection itself.

## 4. Exactly where cancellation or strict preservation enters

**Forced incomparability without Totality.** Assume weak preservation and
cancellation. If $Y_1\succeq X_1$, adding $X_2$ gives

$$Y_1+X_2\succeq X_1+X_2\sim Y_1+Y_2.$$

Now **cancel the common comonotonic summand $Y_1$** to obtain
$X_2\succeq Y_2$, contrary to (3). Along with the first part of (3), this
proves $X_1,Y_1$ incomparable. This proof needs cancellation only at this
last comparison transfer, not in the finite-mixture certificates or (4).

**Contradiction with Totality using preservation only.** Suppose preservation
includes both its weak and strict clauses. By (3) and Totality,
$Y_1\succ X_1$ and $Y_2\succ X_2$. Strict preservation for the first
comparison and weak preservation for the second give

$$Y_1+Y_2\succ X_1+Y_2\succeq X_1+X_2,$$

contradicting (4). There is no cancellation step in this version.

There is also a general order-theoretic explanation: under Totality,
strict preservation supplies weak cancellation. If $X+Z\succeq Y+Z$
but $X\not\succeq Y$, then $Y\succ X$, so strict preservation gives
$Y+Z\succ X+Z$, a contradiction. This reasoning does not follow from
weak preservation alone.

The audit establishes sufficient assumptions and pinpoints their uses.
It does **not** establish inconsistency of weak preservation alone or
cancellation alone with DTU, nor assert that every ingredient is necessary
for every possible proof. The result excludes the silver total comonotonic
extension proposal without requiring its CDF-area clause.

## 5. Exact executable check

`checks/st_petersburg_comonotonic.py` checks the infinite-law identity by
symbolically reducing St Petersburg laws with (1), using rational
coefficients. It also checks all background monotonicity inequalities and
the exact dyadic pattern for the quantile differences. These are supporting
calculations for the proof above, not a Lean certificate or an independent
referee report.

## Paper references

- **Origin: Comonotonic Sum Invariance Forces Incompleteness.** AI-generated report, 2 October 2026, 10 pages; communicated by Branden Fitelson. The producing AI was not identified. Fitelson is the communicator, not the credited producer or checker. — §§2–7
