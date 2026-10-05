# Universal Copula Sum Invariance ⇒ Existential Nonindependent Copula Sum Invariance

<p class='cert'>Result — Source: Misc.; produced by GPT-6 (Codex); recorded by GPT-6 (Codex).</p>

## Premises

- **Universal Copula Sum Invariance.** For every copula $C, \operatorname{SC}(C)$ holds. A copula C is a Borel probability measure on $[0,1]^{2}$ with both marginals uniform. Write $H_C(u,v)=C([0,u]\times [0,v])$. A real-utility pair (A,B) admits C when $P(A\le a,B\le b)=H_C(F_A(a),F_B(b))$ for every real a,b. Define $\operatorname{SC}(C)$: for every eligible triple X,Y,Z for which both (X,Z) and (Y,Z) admit this same $C, X \succeq Y$ iff $X+Z \succeq Y+Z$.

## Conclusion

- **Existential Nonindependent Copula Sum Invariance.** There exists one copula $C\ne\Pi$ such that $\operatorname{SC}(C)$ holds for all eligible X,Y,Z, where $\Pi$ is the product (independence) copula. The copula is chosen once for the preference relation, independently of the triple and its marginal laws. A copula is a Borel probability measure on $[0,1]^2$ with uniform marginals. Write $H_C(u,v)=C([0,u]\times[0,v])$. A real-utility pair (A,B) admits C when $P(A\le a,B\le b)=H_C(F_A(a),F_B(b))$ for every real a,b. Define $\operatorname{SC}(C)$: whenever both (X,Z) and (Y,Z) admit this same C, $X\succeq Y$ iff $X+Z\succeq Y+Z$.

## Proof

Choose the diagonal copula, which is not the product copula: its joint CDF at (1/2,1/2) is 1/2 rather than 1/4. The universal premise supplies its invariance.

## Sources

- **GPT-6 connecting proof 3 Oct** — GPT-6 (Codex), 3 October 2026: elementary connecting proof recording Zachary Goodsell’s requested preservation/cancellation split and nonindependent copula principle.

<p class='cert'>Record: <code>topics/unbounded-utility/results/universal-copula-implies-nonindependent-copula.yaml</code></p>
