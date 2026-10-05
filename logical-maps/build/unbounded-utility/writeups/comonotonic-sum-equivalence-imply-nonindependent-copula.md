# Comonotonic Sum Invariance ∧ Stochastic Equivalence ⇒ Existential Nonindependent Copula Sum Invariance

<p class='cert'>Result — Source: Misc.; produced by GPT-6 (Codex); recorded by GPT-6 (Codex).</p>

## Premises

- **Comonotonic Sum Invariance.** If X and Z are comonotonic, and Y and Z are comonotonic, then $X \succeq Y$ iff $X+Z \succeq Y+Z$. A pair is comonotonic when its members admit nondecreasing representations in one common uniform random variable.
- **Stochastic Equivalence.** If X and Y have the same probability law over outcomes, then $X \sim Y$. The variables remain distinct objects; indifference is an additional axiom.

## Conclusion

- **Existential Nonindependent Copula Sum Invariance.** There exists one copula $C\ne\Pi$ such that $\operatorname{SC}(C)$ holds for all eligible X,Y,Z, where $\Pi$ is the product (independence) copula. The copula is chosen once for the preference relation, independently of the triple and its marginal laws. A copula is a Borel probability measure on $[0,1]^2$ with uniform marginals. Write $H_C(u,v)=C([0,u]\times[0,v])$. A real-utility pair (A,B) admits C when $P(A\le a,B\le b)=H_C(F_A(a),F_B(b))$ for every real a,b. Define $\operatorname{SC}(C)$: whenever both (X,Z) and (Y,Z) admit this same C, $X\succeq Y$ iff $X+Z\succeq Y+Z$.

## Proof

Choose the diagonal copula, whose joint CDF at (1/2,1/2) is 1/2 rather than the product value 1/4. Every pair admitting it has the joint law of its increasing marginal quantiles on one common uniform. Replace an eligible triple by X'=Q_X(U), Y'=Q_Y(U), Z'=Q_Z(U), apply comonotonic invariance, and transfer both comparisons and sum laws by Stochastic Equivalence. The copula is fixed for all triples.

## Sources

- **GPT-6 connecting proof 3 Oct** — GPT-6 (Codex), 3 October 2026: elementary connecting proof recording Zachary Goodsell’s requested preservation/cancellation split and nonindependent copula principle.

<p class='cert'>Record: <code>topics/unbounded-utility/results/comonotonic-sum-equivalence-imply-nonindependent-copula.yaml</code></p>
