# Finite-Type Necessitism: principle, consequences, and exact-height independence

**Daniel Kodsi, with assistance from GPT-6 Astra (OpenAI). 30 October 2026.**

**[Read the complete paper (PDF, 12 pages)](../papers/finite-type-necessitism.pdf) · [LaTeX source](../papers/finite-type-necessitism.tex)**

This guide locates the definitions, principal results and model family in the supplied paper. The PDF and source are unchanged; Figure 1 (p. 8) gives the entailment diagram.

## 1. The principle and its scope

Work over Classicism C in its relational simple-type system, with native modalities. Let

$$
\operatorname{Arith}^{\tau}_n(\mathcal A)
:=\operatorname{Peano}(X_0,z,S)\land
\bigwedge_{i<n}\operatorname{Pow}(X_i,X_{i+1},E_i).
$$

Every level has the same carrier type: $X_i:\tau t$, $z:\tau$, and $S,E_i:\tau\tau t$. The levels may overlap. The formula $\operatorname{Pow}(X,Y,E)$ requires support on $X\times Y$ and exactly one member of $Y$ coding each admitted extension on $X$:

$$\forall F^{\tau t}\exists!y\in Y\;\forall x\in X\;(E(x,y)\leftrightarrow Fx).$$

**Finite-Type Necessitism** is, for every carrier type $\tau$ and finite height $n$,

$$
\Diamond\exists\mathcal A\,\operatorname{Arith}^{\tau}_n(\mathcal A)
\ \longrightarrow\
\exists\mathcal A\Bigl[
\operatorname{Arith}^{\tau}_n(\mathcal A)
\land\operatorname{RigidStr}(\mathcal A)
\land\operatorname{RepPower}_1(\mathsf P(X_n),X_n)
\Bigr].
$$

Here $\mathsf P(X)=\lambda B\,(\operatorname{Rigid}(B)\land B\le X)$, with necessary inclusion. Rigid structure includes necessary distinctness of each carrier's members. The **extra represented power is at the native predicate type**; it need not fit into $\tau$. Types and heights index schemas and are not object-language quantifiers. The principle does not assert that an arithmetic hierarchy is possible. Nor does it put necessary correctness into the antecedent or consequent: **Lemma 2.3 derives necessary correctness** from the displayed witness.

Write $F_n$ for the exact-height schema, with all carrier types still included. Thus $\mathrm{FTN}=\{F_n:n\in\mathbb N\}$. An exact height is not a cumulative fragment.

## 2. The principal positive results

**The arithmetic fragment.** Theorem 3.1 and Theorem 4.4 establish

$$F_0\ \Longrightarrow\
\text{Arithmetic Necessitism},\quad
\text{Necessity of Arithmetic},\quad
\text{Necessity of Analysis}.$$

For Arithmetic Necessitism, retain the existing canonical-arithmetic guard. A height-zero witness becomes necessarily Peano by Lemma 2.3; Peano matching transfers rigidity and necessary distinctness to the canonical numbers. For arithmetic truth, apply categoricity and the rigid-reference argument. For analytical truth, the native power of the rigid number carrier yields a Dedekind-cut reference field, possibly **at another type**; cross-type categoricity transfers first-order analytical truth. This last conclusion is not same-carrier Analytic Necessitism.

**Height one is exactly SOAN.** Theorem 4.3 proves, at each carrier type,

$$F_1\quad\longleftrightarrow\quad
\text{Second-Order Analytic Necessitism}.$$

Lemma 4.2 identifies the same-type possibility antecedents for a height-one arithmetic presentation and a real structure. Dedekind cuts convert a rigid height-one witness into a real field with a full unary represented power. Conversely, the number subcarrier and Cantor coding in a rigid real field give same-type subset codes. Lemma 4.1 explains why the unary power supplies all finite relation arities. These are equivalences with the existing SOAN formulation, not changes to that formulation.

**The seven existing principles.** Already $F_0\land F_1$ entails Arithmetic Necessitism, Necessity of Arithmetic, Analytic Necessitism, SOAN, Necessity of Analysis, Necessity of Second-Order Analysis, and non-contingency of CH. Full FTN therefore entails them all, without a separate existence premise. The existing arrows from AN to Necessity of Analysis, from SOAN to Necessity of Second-Order Analysis, and from the latter to non-contingency of CH are used as background connections, not reintroduced as new results.

**Finite-type truth.** Section 5 gives the exact non-contingency schema for first-order sentences in a hierarchy's many-sorted arithmetic-and-membership signature, with sort-respecting equality and quantifiers restricted to the displayed levels. It also explains finite iteration through native powers. The claimed extension to extensional finite-type mathematics retains the requirement that higher predicates respect agreement of their lower-type arguments. It does not include arbitrary intensional formulas or an infinite tuple of witnesses.

Section 3 also records the background guard-transfer implication

$$\Box I^*_{\rho}\longrightarrow\Box I^*_{et}$$

for every finite type $\rho$, without using FTN. It is a theorem about the native canonical-arithmetic guards, not an extra assumption in Definition 1.1. The optional assumption [[necessary-arithmetic-infinity]] is the node $\Box I^*_{\rho}$ itself. The displayed conditional is retained as a [supporting transfer lemma](necessary-arithmetic-infinity.md), not as a node or an empty-premise proof of arithmetic infinity.

## 3. Exact-height independence and the lattice

**Theorem 6.1:** for every finite $j$, there is a model of C satisfying every $F_n$ with $n\ne j$ and falsifying $F_j$.

This is stronger than successive strictness of a cumulative chain. Even **all the other exact heights together** fail to entail the missing one. In the set-theoretic metatheory used for the models, Corollary 6.2 establishes

$$C+\{F_n:n\in S\}\vdash F_m\quad\Longleftrightarrow\quad m\in S.$$

Consequently the cumulative fragments $G_n=F_0\land\cdots\land F_n$ form a strict chain, with $G_0=F_0$ and $G_1=F_0\land\mathrm{SOAN}$. No finite collection of heights entails FTN. In particular:

* $F_0$ and SOAN are incomparable, and $F_0$ does not entail Analytic Necessitism.
* The seven existing mathematical non-contingency principles, **jointly**, do not entail FTN.

The paper uses one uniform full two-point construction, with $A\subseteq B$ as the two individual domains. At terminal point $s$ take the full extensional hierarchy over $B$. At root $r$, for a flattened relational type $\tau=\sigma_1\cdots\sigma_k t$, use

$$D_\tau^r=\mathcal P\Bigl(\prod_iD_{\sigma_i}^r\Bigr)\times D_\tau^s,$$

with second projection as transport, and the equality and quantifiers of equations (6.2)–(6.3). In this model rigidity is precisely $E_s=\pi[E_r]$, and necessary distinctness is injectivity of projection on the carrier. Projection-bijective carriers have full native rigid powers. Taking cardinalities $(1,\beth_0)$ for $j=0$, or $(\beth_{j-1},\beth_j)$ for $j\ge1$, isolates the missing height at individual type. Relational-type instances hold by the capacity and section argument in the proof. Choice here belongs to the model-building metatheory; it is not an added object-theory premise.

The map records $F_0$ and $F_2$, with $F_1$ as an equivalent formulation of the existing SOAN node. Three records instantiate this **one construction** at $j=0,1,2$, making the principal separations queryable. Theorem 6.1, not the three examples alone, establishes independence at every finite height.

## 4. Attribution

**Daniel Kodsi suggestion:** Finite-Type Necessitism. The exact-height equivalence, uniform independence construction and lattice are attributed to Daniel Kodsi with the assistance credited on the paper's title page. The standing Classicism framework, Goodsell's arithmetic interpretation, the existing Barton–Goodsell principles, and Bacon's categoricity arguments retain the paper's references and their original attribution.

The supplied paper is an informal mathematical proof. The accompanying record and graph checks check transcription, dependencies, consistency of the recorded verdicts, and packaging; they are not independent human verification or Lean certification. No new Lean proof is claimed.

## 5. Supporting invariant variant

Appendix A supplies [[invariant-finite-type-necessitism]]. Its map connections are invariant FTN → FTN and FTN + C5 → invariant FTN. The exact converse to C5 retains the possible-Peano-presentation guard in Theorem A.1; there is no unguarded invariant-FTN-to-C5 arrow.

Two specializations of the shared two-point construction make the distinctions queryable. With $A=B=\omega$, ordinary FTN holds and invariant FTN fails. With $A=B=\{*\}$, invariant FTN holds vacuously and C5 fails. The paper also gives a nonvacuous invariant model with contingent propositions; its proof remains in Appendix A without a further graph record duplicating the currently recorded separation profile.

These are supporting map entries, not additional headline claims.
