# Suslin-tree truth with Analytic Necessitism and necessary CH

Daniel Kodsi, with ChatGPT assistance. 30 October 2026.

## Statement and scope

Relative to the consistency of ZFC, there is a model of Classicism with **Analytic Necessitism at every carrier type** and the **positive necessary-CH alternative at every carrier type**, but with one failed instance of **Necessity of Second-Order Analysis**, at the carrier type $et$. The negative instance has a fixed necessarily real field as its witness; it is not vacuous.

The native record has exactly the positive seeds `analytic-necessitism` and `non-contingency-of-ch`, and the negative seed `necessity-of-second-order-analysis`. The stronger positive-CH assertion is stated here because the map has no separate necessary-CH node. No additional model flags are assumed or imported. In particular, this is not a new claim about represented powers merely being enlarged, and it is not a failure at every carrier type or a necessary failure of the schema.

The construction uses classical consistency and forcing theorems, together with the existing Boolean-valued interpretation and its all-type Analytic Necessitism criterion. It does not claim a new forcing theorem or historical priority for those ingredients. The argument below is an informal mathematical proof; no independent human verification or formal proof is claimed.

## 1. Classical set-theoretic inputs

Use the classical theorem $\operatorname{Con}(\mathrm{ZF})\Rightarrow\operatorname{Con}(\mathrm{ZFC}+\mathrm{GCH}+\mathrm{SH})$, where SH is Suslin's Hypothesis. A precise primary reference is Keith Devlin and Håvard Johnsbråten, *The Souslin Problem*, Lecture Notes in Mathematics 405 (1974), chapter “Con(ZF) → Con(ZFC+GCH+SH),” pp. 113–121, DOI [10.1007/BFb0065989](https://doi.org/10.1007/BFb0065989). This is an invoked classical theorem; the full proof of that chapter has not been reconstructed for this writeup.

Consequently, relative to $\operatorname{Con}(\mathrm{ZFC})$, first-order completeness and downward Löwenheim–Skolem supply an ordinary countable model $M$ of $\mathrm{ZFC}+\mathrm{CH}+\mathrm{SH}$. Neither transitivity nor external well-foundedness is assumed. All set-theoretic constructions and forcing statements below are performed **inside $M$**.

Use Jech's original forcing $P$ of regular ramified graphs of all countable lengths. A condition is a reflexive transitive relation on $\omega\times\alpha$, for any $\alpha<\omega_1$, respecting levels. Every node has a predecessor at every earlier level; distinct nodes at one level have no common upper bound. Regularity requires every node to have at least two extensions at each later available level. Stronger conditions extend the graph on its initial levels. The predecessor clauses imply uniqueness and prevent changes between old nodes. No unique-root or additional Hausdorff-limit convention is inserted.

The source is Tomáš Jech, “Non-provability of Souslin's hypothesis,” *Commentationes Mathematicae Universitatis Carolinae* 8(2) (1967), 291–305 ([article](https://dml.cz/handle/10338.dmlcz/105112)): definitions in §§2.3 and 4.2–4.3; length extension and countable closure in Lemmas 4.7–4.8; the generic chain and antichain exclusions in §§4.18–4.19. The modern research article John Krueger and Šárka Stejskalová, [*Forcing Over a Free Suslin Tree*, arXiv:2402.00226v2](https://arxiv.org/html/2402.00226v2), Introduction, also states the countably closed Suslin-tree-adding theorem, in a modern tree presentation. The construction here uses the original graph presentation rather than identifying all conventions of the two presentations.

For all countable heights, the union of an increasing countable sequence of graphs is a condition: its height is countable, and each finite configuration and each required pair of levels appears at some stage. Thus $P$ is countably closed. Recursively deciding the entries of a name for a countable ordinal sequence and taking a lower bound shows that $P$ adds no such sequences. In particular, it adds no reals and preserves $\omega_1$. The ground CH bijection therefore remains a bijection onto the extension's reals. Jech's theorem, not closure alone, supplies a Suslin tree. If a root is desired, take a cone above a level-zero node; regularity and length-extension density preserve height $\omega_1$.

Thus $M$ verifies

$$
1_P\Vdash\mathrm{CH}+\text{“there is a Suslin tree”},\qquad
1_P\Vdash\mathcal P(\omega)=\check{\mathcal P(\omega)^M}.
$$

References below to a forcing interpretation abbreviate these internal assertions. No externally existing countable transitive model or external generic extension is required. The starting SH assumption is important: an arbitrary CH ground need not have the opposite Suslin-tree truth value.

## 2. One finite second-order analytical sentence

Fix a real-structure tuple $\mathfrak R$ at carrier type $\tau$. Write $X$ for its field carrier and $N$ for its field natural-number predicate. Individual variables have type $\tau$, unary variables $T,C,D,Y$ have type $\tau t$, and binary variables $E,J$ have type $\tau\tau t$. Every individual quantifier in this section is restricted to $X$. Equality is only equality between carrier elements, never equality between relations.

Let $\operatorname{Ct}(Y)$ abbreviate

$$
\exists J\Bigl[
\forall x\in X\,(Yx\to\exists n\in X\,(Nn\land J(x,n)))
\ \land\
\forall x,n,m\in X\,((Yx\land Nn\land Nm\land J(x,n)\land J(x,m))\to n=m)
\ \land\
\forall x,y,n\in X\,((Yx\land Yy\land Nn\land J(x,n)\land J(y,n))\to x=y)
\Bigr].
$$

This says that $Y\cap X$ injects into $N$. Values of $J$ outside $(Y\cap X)\times N$ are irrelevant; finite and empty traces are allowed.

Put $\operatorname{Sub}(C,T):=\forall x\in X(Cx\to Tx)$ and $\operatorname{Pred}_t(x):=Tx\land E(x,t)$. Let $\operatorname{Tree}(T,E)$ be the conjunction of

$$
\forall x\in X\,(Tx\to\neg E(x,x)),
$$
$$
\forall x,y,z\in X\,((Tx\land Ty\land Tz\land E(x,y)\land E(y,z))\to E(x,z)),
$$
$$
\forall t,x,y\in X\,((Tt\land\operatorname{Pred}_t(x)\land\operatorname{Pred}_t(y))\to(x=y\lor E(x,y)\lor E(y,x))),
$$
$$
\forall t\in X\,\Bigl(Tt\to\forall D\bigl[
(\exists x\in X\,(Dx\land\operatorname{Pred}_t(x)))\to
\exists m\in X\,(Dm\land\operatorname{Pred}_t(m)\land
\forall x\in X\,((Dx\land\operatorname{Pred}_t(x))\to\neg E(x,m)))
\bigr]\Bigr).
$$

These assert a strict partial order on $T\cap X$ whose strict predecessor sets are linearly well-ordered. Define

$$
\operatorname{Chain}_E(C):=\forall x,y\in X\,((Cx\land Cy)\to(x=y\lor E(x,y)\lor E(y,x))),
$$
$$
\operatorname{Anti}_E(C):=\forall x,y\in X\,((Cx\land Cy\land x\ne y)\to(\neg E(x,y)\land\neg E(y,x))).
$$

The desired single sentence is

$$
\operatorname{ST}(\mathfrak R):=\exists T\exists E\Bigl[
\neg\operatorname{Ct}(T)\land\operatorname{Tree}(T,E)\land
\forall C\bigl(\operatorname{Sub}(C,T)\to
((\operatorname{Chain}_E(C)\to\operatorname{Ct}(C))\land
(\operatorname{Anti}_E(C)\to\operatorname{Ct}(C)))\bigr)
\Bigr].
$$

Expanding the finitely many abbreviations gives a second-order analytical sentence with only unary and binary relation quantifiers. Every application is to field elements. There is no modality, external parameter, relation identity, or quantifier over a collection of relations. In particular, $\forall C\exists J$ remains ordinary second-order quantification.

## 3. Why ST expresses Suslin-tree existence

Work in full set-theoretic semantics in ZFC. Categoricity of complete ordered fields identifies $\mathfrak R$ with the real field and $N$ with its natural numbers. Consequently $\operatorname{Ct}(Y)$ says exactly that $Y\cap X$ is at most countable.

Suppose $\operatorname{ST}(\mathfrak R)$. Each predecessor set is a well-order and a chain, hence countable by the chain clause. Assign to a node the order type of its predecessors; this is below $\omega_1$. The predecessors of a predecessor form the corresponding initial segment, by transitivity and predecessor linearity. Thus the order strictly increases height, and nodes of equal height are incomparable. Each level is countable by the antichain clause.

If all heights were bounded below a countable ordinal, the tree would be a countable union of countable levels, contradicting $\neg\operatorname{Ct}(T)$. Its height is therefore $\omega_1$, with countable levels and no uncountable chain or antichain. It is a Suslin tree.

Conversely, a Suslin tree has $\omega_1$ nodes. Since $\omega_1\leq2^{\aleph_0}$, inject it into the field and transport its ordering. Full unary and binary quantification supplies every subset and every graph of an injection into $N$. The displayed sentence follows. Thus ZFC proves, uniformly over complete ordered fields,

$$\operatorname{ST}(\mathfrak R)\quad\Longleftrightarrow\quad\text{a Suslin tree exists}.$$

This equivalence does not require CH. It is used inside $M$ and its Boolean-valued interpretation; it is not asserted for arbitrary Henkin fields.

## 4. Boolean interpretation and full relation quantification

Inside $M$, let $A=\operatorname{RO}(P)$ and $B=2\times A$. Use the internally full typed hierarchy

$$D_e=\omega^M,\qquad D_t=B,\qquad D_{\alpha\to\beta}=(D_\beta)^{D_\alpha}\quad(\beta\ne e).$$

Application, abstraction, Boolean operations, and quantifier meets and joins are internal. For each standard finite type and formula, externalize the corresponding internal domains and operations. Evaluate at the isolated coordinate $v_0(\epsilon,a)=\epsilon$. This is the established Boolean interpretation of C: singleton characteristic predicates make native identity crisp, so the defined operator $\Box p$, namely $p=\top$, is the test for equality to the whole top element of $B$.

The first coordinate satisfies classical quantifier clauses over exactly the externalized internal members. “Full” here means internal fullness, not every external subset of an externally countable domain. Boolean soundness and typed abstraction closure are inherited from Bacon's Boolean construction and its previously recorded development; see the existing [repeated-forcing writeup](full-boolean-valued-repeated-forcing.md), together with the source credits below.

For completeness, the transfer needed for the analytical formulas has the following precise scope. If $L$ is an internal set, every internal $A$-name for a subset of $\check L$ is equivalent to the normalized name with coefficients

$$a_l=\Vert\check l\in\dot Y\Vert_A\quad(l\in L).$$

Conversely, every internal coefficient function $L\to A$ defines such a name. With $L=D_\tau^k$, these functions are exactly the second coordinates of the admitted $k$-ary relation domain. First coordinates can be chosen independently. Relation quantifiers therefore range over all the relevant names, not merely checked ground subsets.

Induction matches application, carrier-label equality, and Boolean connectives. Quantification over the checked carrier matches quantification over labels by Boolean substitution: mixed element names add no values beyond the relevant joins and meets. Restricting a quantifier by a possibly varying $X$ gives quantification over its corresponding subset name. This establishes transfer for Real, CH, and the displayed ST sentence. It does not equate intensional identity between relations with identity of their extensions.

If a tuple is real only below a nonzero support $b\in A$, apply the interpretation below $b$. Completeness there ranges over all subset names, and the least-inductive-$N$ clause has its full interpretation. Field categoricity and Section 3 therefore apply below that support. These are fixed internal set-theoretic assertions and require no external well-foundedness of $M$.

## 5. All-type AN, not just a single real-field witness

The previously established no-new-reals criterion for this exact hierarchy with $D_e=\omega^M$ gives full AN. The sufficiency argument needed here can also be stated directly.

If $M$ regards $D_\sigma$ as large enough to contain its real field, choose an internal injection and transport the field structure with all relations valued at the two endpoints of $B$. The endpoint rigidity calculation makes this a rigid structure. It remains complete in the forcing interpretation: a new nonempty bounded subset of the old field determines a rational lower cut; because no reals were added, that cut is old and its old supremum serves as the supremum of the subset. The least inductive natural-number predicate is unchanged. Full transfer consequently gives a necessarily real rigid field on that carrier.

It remains to cover every other type, rather than assuming one witness supplies a uniform domain-size bound. If $B$ is infinite, ZFC produces a countably infinite disjoint family of nonzero elements of $B$. Taking joins of its subfamilies embeds $\mathcal P(\omega)$ into $B$. Constant functions then embed $B$ into every non-$e$ type, recursively. Each such carrier is large enough for the preceding construction. The remaining carrier $D_e=\omega^M$ cannot support a complete ordered field, in either coordinate or below a positive forcing support.

If $B$ is finite, induction on types shows that every non-$e$ type is either finite or at least continuum-sized. The codomain always has at least two elements; an infinite input admits continuum many endpoint-valued functions, and a continuum-sized codomain gives continuum many constant functions. Finite carriers and $D_e=\omega^M$ cannot possibly support a complete ordered field. The large carriers again admit the endpoint construction. Thus every AN instance has whole value top.

For the negative instance, fix the carrier $et$. Endpoint-valued functions $\omega^M\to B$ contain an internal copy of the ground reals. Transport the complete field, its operations, ordering and least natural-number predicate to such a copy, all with endpoint values; call it $\mathfrak R_0$. The preceding cut argument, including new subset names, gives

$$\Vert\operatorname{Real}_{et}(\mathfrak R_0)\Vert=(1,1_A)=1_B.$$

This supplies a particular necessarily real field without imposing a separate size assumption on $D_t$.

## 6. Failure of the exact native truth schema

Ground SH and Section 3 give the first coordinate of $\operatorname{ST}(\mathfrak R_0)$ as zero. The forcing theorem and full transfer give the second coordinate as $1_A$. Hence

$$\Vert\operatorname{ST}(\mathfrak R_0)\Vert=(0,1_A),\qquad
\Vert\neg\operatorname{ST}(\mathfrak R_0)\Vert=(1,0_A).$$

The relevant native instance is a disjunction of **boxed universals**, not merely an assertion about a named field. Put

$$U_+:=\forall\mathfrak R\,(\operatorname{Real}_{et}(\mathfrak R)\to\operatorname{ST}(\mathfrak R)),\qquad
U_-:=\forall\mathfrak R\,(\operatorname{Real}_{et}(\mathfrak R)\to\neg\operatorname{ST}(\mathfrak R)).$$

Instantiation at $\mathfrak R_0$ alone yields

$$\Vert U_+\Vert\leq(0,1_A),\qquad \Vert U_-\Vert\leq(1,0_A).$$

Both upper bounds are proper elements of $B$. Since native $\Box$ tests for whole top, both $\Box U_+$ and $\Box U_-$ have value $0_B$. Their disjunction is false at the isolated evaluation. This refutes one instance of Necessity of Second-Order Analysis at $et$, with its necessarily real witness explicit.

Indeed, all-tuple transfer also gives the equalities $\Vert U_+\Vert=(0,1_A)$ and $\Vert U_-\Vert=(1,0_A)$: every ground real field satisfies $\neg\operatorname{ST}$, and every field real below a forcing support satisfies ST there. These stronger equalities are not needed for the negative conclusion.

## 7. Positive necessary CH at every carrier

Fix any carrier $\sigma$ and any admitted real-data tuple. Its first-coordinate real trace, when real, is an internally complete ordered field in $M$ and satisfies CH. In the $A$ coordinate, let $b$ be the Boolean value of its Real predicate. Below $b$, transfer and categoricity identify a complete ordered field in the forcing interpretation. Since $P$ forces CH, $b$ is below the CH value. Therefore each implication $\operatorname{Real}_\sigma(\mathfrak R)\to\operatorname{CH}(\mathfrak R)$ has whole value top.

Taking the universal meet and applying the top-test box gives, at **every** carrier,

$$\Box\forall\mathfrak R\,(\operatorname{Real}_\sigma(\mathfrak R)\to\operatorname{CH}(\mathfrak R)).$$

This includes tuples that are real only on a proper Boolean support and types with no possible real structure. It is not inferred solely from $\mathfrak R_0$. Sections 5–7 establish the stated three-seed joint model.

## 8. Attribution and distinction from earlier examples

Jensen's consistency result, as presented by Devlin and Johnsbråten, and Jech's forcing theorem are classical inputs. The Boolean-valued interpretation, crisp identity/top-test calculation, and full-name transfer are inherited from Andrew Bacon's construction and Daniel Kodsi's prior Boolean-model work with AI assistance. The earlier rigid-ground-field/new-Dedekind-cut obstruction in the map retains its credit to the Goodsell/Dorr-associated source record; the positive all-type capacity argument is not attributed as a new forcing theorem.

The new contribution recorded here is the explicit finite unary/binary analytical sentence and this precise combination of its truth variation with all-type AN and necessary positive CH. The earlier countably closed AN-plus-CH example with failed SOAN concerns represented powers; it does not supply this changing analytical truth witness. The theory-preserving repeated-forcing examples instead choose a prepared ground that fixes parameter-free analytical theory. They are not substitutes for the present ground satisfying SH.

Only one model with ID `suslin-analytic-truth-separation` is to be inserted. No conditional predecessor is inserted alongside it. No new principle, unrestricted implication, choice assertion, Boolean-completeness assertion, or direct SOAN flag is added by this record. Consequences of the map's existing proved rules remain the responsibility of its ordinary inference engine.
