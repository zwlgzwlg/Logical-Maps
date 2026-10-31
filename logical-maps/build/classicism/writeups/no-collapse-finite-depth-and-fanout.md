# Hat iteration and No Collapse

Logical Maps research campaign, 30 October 2026.

Iterating the hat operation raises a concrete question: must some finite iterate equal its successor? We describe models whose first possible stopping point moves arbitrarily far out, then assemble them into one model with an admitted family of nonfixed iterates.

## 1. The return game

Use the native operation from *The Bounds of Possibility*, Appendix D [1]:

\[
\widehat X(p):=\exists q\,[q\land\Box(\neg X(\neg q)\to p)],
\qquad O_0=\Box,\qquad O_{n+1}=\widehat{O_n}.
\]

Our models use the different Appendix D of Bacon and Dorr's *Classicism*: the ideally full construction over a small category of sets and functions, with finite sets as pins [2]. Every finite-pinned profile is admitted at every relational type. Quantification at a future object uses its full admitted domain.

For an object \(A\) and finite \(S\subseteq A\), let \(U_A(S)\) contain exactly the endomorphisms fixing \(S\). It is an admitted true proposition. Every true proposition contains some such \(U_A(S)\), because arrows agreeing with the identity on its pin give it the same truth value. For \(h:A\to B\), define

\[
R_0(A,S)=\{\text{all arrows out of }A\},
\]
\[
h\in R_{n+1}(A,S)\quad\Longleftrightarrow\quad
\forall T\subseteq_{\mathrm{fin}} B\;\exists k:B\to A\;
[kh|_S=\operatorname{id}|_S\land k\in R_n(B,T)].
\]

Then \(O_np\) holds at \(A\) exactly when \(R_n(A,S)\subseteq p\) for some finite \(S\). For the inductive step, replace a true hat witness by \(U_A(S)\), using monotonicity of the dual of \(O_n\). Its truth after a composite \(kh\) says precisely that the composite returns to \(A\) and fixes \(S\). Thus the return may depend on the challenge \(T\); one return need not answer every challenge. This is the source's finite-pin game in convenient notation [3].

## 2. A capacity that takes more rounds to detect

Fix an external integer \(d\ge1\). A level-zero node \(U_0(n)\) has \(n\) leaves, for positive finite \(n\), while \(U_0(\infty)\) is countably infinite. Inductively, \(U_j(m)\) has exactly \(m\) children of type \(U_{j-1}(\infty)\), together with countably infinitely many children of every finite parameter type. Here \(m\) may be finite or infinite; zero is allowed above level zero. Even \(U_j(0)\) remains nonempty.

The object \(A_d\) contains countably infinitely many copies of every finite-parameter top node \(U_{d-1}(m)\). The object \(B_d\) additionally contains countably infinitely many infinite-parameter top nodes. Arrows are all total leaf maps preserving the \(d\) nested equivalence relations given by common containing nodes. They may merge nodes or collapse leaves. Identities and composites are allowed, and images of finite pins are finite, so the cited C-model construction applies.

Call a node *anchored* if it meets the pin \(S\), and write \(\lambda(v)\) for its parameter. Let \(P(h,S)\) mean that \(h\) is injective and reflects every equivalence relation on \(S\). The exact calculation is

\[
\begin{aligned}
R_1 &: P;\\
R_{2j+2} &: P,\quad \lambda(v)=\lambda(hv)\quad(\text{levels}<j),\\
&\hspace{2.5em}\lambda(v)\ge\lambda(hv)\quad(\text{level }j);\\
R_{2j+3} &: P,\quad \lambda(v)=\lambda(hv)\quad(\text{levels}\le j),
\end{aligned}
\]

where all node conditions concern anchored nodes and \(0\le j<d\).

Why does each level require two further rounds? A finite source capacity smaller than its target is exposed by selecting too many target leaves, or too many distinct infinite child nodes. The required return is anchored to the original source node; reflection prevents it merging the challenged children. The next round reverses the inequality, forcing equality.

The positive direction matters equally. Enlarge a challenge by \(h[S]\) and retain its forced inverse. Infinitely many copies of each finite type provide fresh places for the remaining finite trace. An unanchored infinite node can use a sufficiently large finite approximation until equality is required at its own level. Above that level, new children have finite parameters, so the finite-type reservoirs suffice. Finally extend the partial map to a total arrow by collapsing unassigned leaves inside their assigned ancestors. This respects overlapping pins and proves the table uniformly in \(d\) [4].

For every finite pin at \(A_d\), matching its anchored top types into \(B_d\) gives a cross-arrow in \(R_{2d+1}\). No cross-arrow survives \(R_{2d+2}\): a challenge in an infinite top node would require a return preserving a type absent from \(A_d\). Therefore the empty-pinned proposition \(p_d\), true exactly on arrows targeting \(A_d\), satisfies

\[
\neg O_{2d+1}p_d,\qquad O_{2d+2}p_d.
\]

This is a truth-value distinction, hence a whole-operator inequality. The exact return table also gives \(O_{2d+2}=O_{2d+3}\) throughout this particular model: at \(B_d\), adding one infinite-top-node anchor eliminates the remaining cross-returns. Thus \(d=2\) separates the fifth and sixth hats, and each finite-depth model eventually stops.

## 3. One root and an actual family

**Theorem.** In external ZFC, the construction below satisfies ordinary No Collapse.

Take the disjoint union of all finite-depth categories. Add a new object \(R\) with individuals \(\mathbb N\), only its identity endomorphism, and all functions from \(R\) to every old object. There are no old-to-\(R\) arrows. Composition is closed, and the full finite-pin construction again applies. Old outgoing categories, typed domains and witnesses are unchanged.

Closed terms commute with transport. If \(O_n^R=O_{n+1}^R\), congruence under hat gives equality at every later adjacent step. Transport to an \(A_d\) with \(2d+1\ge n\) contradicts its retained separator. Hence every adjacent pair differs as whole operators at \(R\). No root preimage of the separating future proposition is needed.

That external sequence alone is insufficient. Supply the required family explicitly: at every arrow \(h:R\to V\), including the identity, set

\[
\mathcal F_h=\{O_n^V:n\in\mathbb N\}.
\]

These are sets of already admitted whole \(tt\)-entities. The row depends only on its target, so the profile has the empty pin and is admitted at type \((tt)t\). Its transports have the same description. There is no circular type construction or assumed internal enumeration of the natural numbers. At \(R\), this family contains \(\Box\), is closed under hat, and has no fixed member. It witnesses exactly the native sentence [3, 5]

\[
\exists\mathcal F^{(tt)t}\,[\mathcal F\Box\land
\forall X\,((\mathcal FX\to\mathcal F\widehat X)
\land(\mathcal FX\to X\ne\widehat X))].
\]

The clauses are current, not necessary. Moreover this root does not witness Extensional No Collapse: its root-only proposition makes every \(O_n\), \(n\ge1\), currently coextensive with truth. Their whole profiles differ in the old components. No Strong Possibility result is asserted. The finite-pin semantics and game are inherited methods; the nested capacity calculation and explicit family step are supported by the research artifacts cited below.

## References

[1] C. Dorr, J. Hawthorne and J. Yli-Vakkuri, *The Bounds of Possibility* (2021), Appendix D, pp. 400–409.

[2] A. Bacon and C. Dorr, *Classicism* (2024); 16 May 2023 draft, Appendix D, Definitions D.1–D.3 and Proposition D.4.

[3] *Logical Maps*, pinned source `f038af7c335b`: `CANDIDATES.md`, No Collapse; `background/varieties.md`; and the paired-individuals game.

[4] Research artifacts (30 October 2026): `general-depth-proof.txt`, `proof-route.txt`, and `hat-depth-independent-campaign-review.md`.

[5] Research artifacts (30 October 2026): combined construction and coordinator review; independent fanout and family reconstruction.
