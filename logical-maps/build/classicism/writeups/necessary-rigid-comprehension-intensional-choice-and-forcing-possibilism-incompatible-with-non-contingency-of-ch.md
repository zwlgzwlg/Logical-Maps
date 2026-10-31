# Forcing Possibilism and the cardinality repair for CH

**Research proof for review, 30 October 2026.** Developed by Daniel Kodsi with assistance from ChatGPT (GPT-6 Astra, prompted by Daniel Kodsi). No independent human check or Lean certification is claimed.

The original four-premise conjecture remains refuted. The repaired implication below has additional size and necessary-arithmetic premises; it does not change the status of that original statement.

The forcing argument and the cloud construction are Andrew Bacon's. The proposed cardinality repair is Cian Dorr's suggestion of 25 October 2026. The work added here concerns the exact size bound, the necessary-arithmetic and real-structure interfaces, counterexamples to incomplete repairs, and the derivation that makes the weaker size premise sufficient.

## The result in map language

Work in Classicism. Let the following size condition hold for a current real-number structure:

> There is no injective relation from the propositions into the rigid properties of its real numbers.

Then

$$
\boxed{
\Box\text{Rigid Comprehension}
+\text{Intensional Choice}
+\text{Forcing Possibilism}
+\Box\text{Axiom of Infinity (type }e\text{)}
+\text{the displayed size condition}
\ \Longrightarrow\ \text{Contingency of CH}.}
$$

The conclusion says that, at one fixed sufficiently high carrier type, a real-number structure satisfying CH is possible and a real-number structure failing CH is possible. Consequently the package is incompatible with the map's Non-contingency of CH schema.

Here FP is the **original map principle**: every current complete Boolean algebra that is Dedekind finite or strictly smaller than the propositions is isomorphic to a **full proper principal entailment interval**. IC and FP are current assumptions. Infinity is the map's **quantified exact-cardinality axiom on individuals**, under a box; the separate schema asserting at least each standard finite number of individuals is not substituted for it.

The direction of the size condition matters. Dorr's intended “more propositions than sets of reals” excludes an injection **from propositions to sets of reals**. The quoted gloss excluding an injection in the opposite direction expresses a different premise, and that literal premise does not suffice even with necessary Infinity.

## Exact statement and the weak-to-strict comparison

Let $N$ be a definitionally least zero/successor-closed number carrier, with its Peano zero and successor-injectivity laws holding necessarily. Necessary RC makes this definitional carrier rigid. Put

$$
S=\mathcal P_r(N),\qquad T=\mathcal P_r(S),\qquad
C_N=\forall X\subseteq S\;(X\precsim N\lor X\approx S).
$$

Here $\mathcal P_r(A)$ consists of the unique rigid representatives of the **current** subproperties of $A$. It does not assert that this whole collection is rigid. The relations $\precsim$ and $\approx$ mean current relational injection and bijection. Write

$$
A\prec B\quad\Longleftrightarrow\quad
A\precsim B\ \land\ \neg(B\precsim A),
$$

and let $\Pi$ be the proposition carrier. Under

$$
\Gamma=C+\Box RC+IC+FP_<+\Box\operatorname{Peano}(N),
$$

the additional theorem is

$$
\boxed{
\neg(\Pi\precsim T)
\ \Longrightarrow\
T\prec\Pi\ \land\ \Diamond C_N\ \land\ \Diamond\neg C_N.
}
$$

The new comparison is the forward injection $T\precsim\Pi$. Thus the weak size condition $\neg(\Pi\precsim T)$ and the strict size condition $T\prec\Pi$ are equivalent under $\Gamma$. No current well-order of the reals, ordinary global Choice principle, inaccessible carrier, boxed FP, or boxed IC is added.

The displayed size condition involving a current real structure is a fixed-type instance: current comparison identifies its carrier with $S$, and hence its rigid powerset with $T$. Types are schema indices, not object-language variables.

For the countermodel comparisons, $L$ abbreviates the corresponding strict condition
$$
\exists\mathfrak R\,
\bigl(\operatorname{Real}_{\sigma}(\mathfrak R)
\land\mathcal P_r(X_{\mathfrak R})\prec\Pi\bigr)
$$
at the fixed carrier type in question. The countermodels below can use $\sigma=t$ for their current real structure.

## Proof guide

Part I supplies the necessary arithmetic and real-structure comparisons, verifies the map's exact quantified Infinity interface, and checks the repair using singleton-base and infinite-base instances of Bacon's cloud construction and the existing countable S5 model. Part II proves that Boolean-algebra coverage through the second rigid powerset suffices for both CH possibilities. Part III proves that the correctly directed non-injection already gives that coverage under original FP: first by diagonal coding along the current countable order types, and then by stationary coding indexed by the old reals. The preliminary result with a well-orderable continuum is subsumed by this final argument.

All claims about the earlier inaccessible-bound development refer to [commit 163d1d8](https://github.com/zwlgzwlg/Logical-Maps/commit/163d1d8b6112a52d532696a9732402b8a8680fd1), not to the current database. That principle has a different size convention; an inaccessible witness supplies the bounded coverage used here, but the present theorem requires no such witness.

---

# Part I. Arithmetic, real structures, and the countermodels

## Scope and conventions

These sections work in Classicism $C$, with the relational simple types generated from $e,t$ by $\sigma\to\tau$ only when $\tau\ne e$. Maps, operations on a carrier, and isomorphisms are represented by relations. No function type with output $e$, Functional Choice, or Functional Plenitude is assumed.

Write
$$
\Box p:=(p=\top),\qquad
\Diamond p:=(p\ne\bot),\qquad
X\subseteq Y:=\forall x(Xx\to Yx),\qquad
X\le Y:=\Box(X\subseteq Y).
$$
The rigidity convention is persistence plus inextensibility:
$$
\begin{aligned}
\operatorname{Pers}(X)&:=\Box\forall x(Xx\to\Box Xx),\\
\operatorname{Inext}(X)&:=\Box\forall Y
 \bigl[(\forall x(Xx\to\Box Yx))\to\Box(X\subseteq Y)\bigr],\\
\operatorname{Rig}(X)&:=\operatorname{Pers}(X)\land\operatorname{Inext}(X).
\end{aligned}
$$
The analogous definitions apply to tuples of arguments. Rigid Comprehension, RC, supplies a rigid relation currently coextensive with any given relation. Its boxed form is $\Box RC$.

For a carrier $A$, put
$$
\mathcal P_r(A):=\lambda U.\operatorname{Rig}(U)\land U\subseteq A.
$$
This denotes the rigid representatives of the **current** subproperties of $A$. The collection $\mathcal P_r(A)$ is not thereby asserted rigid.

All uses of the Logical Equivalence schema retain its theoremhood restriction. In particular, current coextension is not promoted directly to identity. When identity of representatives is needed below, it follows from rigidity, or from necessity of their coextension.

## 1. The at-least natural-number carrier

To match the interface recorded in commit
[163d1d8b6112a52d532696a9732402b8a8680fd1](https://github.com/zwlgzwlg/Logical-Maps/commit/163d1d8b6112a52d532696a9732402b8a8680fd1),
fix
$$
\nu=(et)t,\qquad z:=\lambda A^{et}.\top,
$$
and use the cardinal successor operation
$$
(\operatorname{Suc}n)(A):=
\exists x^e\bigl(Ax\land n(\lambda y^e.Ay\land y\ne x)\bigr).
$$
Define
$$
N:=\lambda n^\nu.\forall Z^{\nu t}
\bigl[(Zz\land\forall m^\nu(Zm\to Z(\operatorname{Suc}m)))\to Zn\bigr].
$$
Thus $N$ is the at-least carrier called LowerNat in that interface. It is not definitionally the exact-cardinality carrier used elsewhere in the map.

Let $\operatorname{Peano}(N)$ abbreviate the two additional conditions
$$
\begin{aligned}
&\forall n\in N\;(z\ne\operatorname{Suc}n),\\
&\forall m,n\in N\;
  (\operatorname{Suc}m=\operatorname{Suc}n\to m=n).
\end{aligned}
$$
The arithmetic hypothesis in the main application is
$\Box\operatorname{Peano}(N)$, exactly the commit's necessary-lower-Peano principle. Membership of $z$, successor closure, and induction follow from the definition of $N$.

The arguments about numberhood in this section are parametric in the chosen closed zero and successor terms. They do not depend on zero being the at-least-zero quantifier. Their rigidity conclusion applies to the **definitionally least** carrier just displayed, including LowerNat and its exact-cardinality counterpart. It is not a claim that an arbitrary parameter carrier satisfying only current Peano axioms must be rigid. A theorem stated with an arbitrary parameter carrier should retain explicit stability/rigidity hypotheses, or assume enough necessary induction to identify that carrier necessarily with the definitional least one.

### Lemma 1.1. Unique rigid representatives and restricted Barcan

Coextensive rigid relations are identical. For rigid $A$,
$$
\forall x\in A\,\Box\phi(x)
\ \longrightarrow\
\Box\forall x\in A\,\phi(x),
\tag{1}
$$
and, contrapositively,
$$
\Diamond\exists x\in A\,\phi(x)
\ \longrightarrow\
\exists x\in A\,\Diamond\phi(x).
\tag{2}
$$

**Proof.** For uniqueness, let rigid $F,G$ be currently coextensive. If $Fx$, then $Gx$, hence $\Box Gx$ by persistence. Inextensibility of $F$ gives $F\le G$; symmetrically $G\le F$. Intensionality in $C$ gives $F=G$. The polyadic proof is identical.

For (1), instantiate inextensibility of $A$ with $\lambda x.\phi(x)$. Formula (2) is its classical contrapositive. No unboxed principle has been necessitated. $\square$

Under RC, $F^\dagger$ may consequently abbreviate the unique rigid current representative of $F$. This is eliminable unique-existence notation, not a term selecting representatives by Functional Choice.

### Lemma 1.2. Persistence and rigidity of $N$

Classicism proves
$$
\forall n(Nn\to\Box Nn)
\quad\text{and}\quad
\operatorname{Pers}(N).
$$
RC at the type of properties of $\nu$ implies $\operatorname{Rig}(N)$.

**Proof.** Apply the defining induction principle to the property
$\lambda n.\Box Nn$. The base $\Box Nz$ follows by necessitating the theorem $Nz$. The necessitated successor-closure theorem takes $\Box Nn$ to $\Box N(\operatorname{Suc}n)$. Thus $Nn\to\Box Nn$ is a theorem of $C$. Necessitating this theorem gives the displayed persistence condition, including its leading box.

For rigidity, choose rigid $A$ currently coextensive with $N$. Every current $A$-member necessarily belongs to $N$, so (1) gives $A\le N$.

Also $Az$, hence $\Box Az$. If $An$ currently, then $Nn$, then $N(\operatorname{Suc}n)$, then $A(\operatorname{Suc}n)$. Persistence of $A$ gives $\Box A(\operatorname{Suc}n)$. Apply (1), now to the property $\lambda n.A(\operatorname{Suc}n)$, to obtain
$$
\Box\forall n(An\to A(\operatorname{Suc}n)).
$$
At every possibility, therefore, $A$ contains $z$ and is successor-closed. The defining minimality of $N$ gives $N\subseteq A$ there. Formally, this uses the necessitated minimality theorem of $C$, instantiated at the current parameter $A$; Converse Barcan, available in $C$, licenses the instantiation. Hence $N\le A$.

Intensionality gives $N=A$, so $N$ is rigid. This proof applies directly to LowerNat; it does not identify at-least and exact cardinalities. $\square$

Goodsell's *Arithmetic is Necessary*, draft §5, Lemmas 3 and 8, provides a separate literature route to persistence and restricted Barcan for the number carrier. The direct RC proof above is sufficient here.

The direct rigidity argument is also the mechanism used in Lemma 2.2 of Bacon's [general forcing proof draft](https://andrew-bacon.github.io/techdoc/CH_contingency_general_forcing.pdf), made explicit here with the leading box in persistence and the scope of its definitional carrier. It is not presented as a new result of this note.

### Lemma 1.3. Necessary distinctness and the arithmetic base

Under $\Box\operatorname{Peano}(N)$,
$$
\forall m,n\in N\;(m\ne n\to\Box(m\ne n)).
\tag{3}
$$
Together with the preceding lemmas, $N,z,\operatorname{Suc}$ supplies a rigid Peano base with necessarily valid Peano laws.

**Proof.** The definition of $N$ gives
$$
Nn\to
\bigl(n=z\lor\exists k(Nk\land n=\operatorname{Suc}k)\bigr).
$$
Induct on $n$, using
$\forall m\in N(n\ne m\to\Box(n\ne m))$ as the induction property.

For $n=z$, any distinct $m$ is a successor. Its predecessor's membership in $N$ persists by Lemma 1.2, so the necessary zero law gives the necessary distinction.

For $n=\operatorname{Suc}k$, the case $m=z$ uses that same law. Otherwise write $m=\operatorname{Suc}\ell$. Current distinctness of the successors implies $k\ne\ell$. The induction hypothesis gives $\Box(k\ne\ell)$; necessary successor injectivity, together with persistence of $Nk,N\ell$, gives
$\Box(\operatorname{Suc}k\ne\operatorname{Suc}\ell)$. Substitution by the relevant current identities is legitimate; those identities are themselves necessary in $C$.

Addition, multiplication, finite sequences, pairing, and rational codes can now be developed by the usual relational recursions on $N$. These recursions use uniquely determined next values and induction; they do not require choosing a function object. $\square$

### Lemma 1.4. Current relational recursion does not require Functional Choice

Assume the current Peano conditions and defining induction for $N$. Let $X$ be a current carrier of any admitted type, let $b\in X$, and suppose a current relation $T(n,x,y)$, supported on $N\times X\times X$, gives exactly one $y\in X$ for each $n\in N,x\in X$. Then there is a current total functional relation $D:N\to X$ with $D(z,b)$ and the recursion rule
$$
D(n,x)\land T(n,x,y)\ \longrightarrow\
D(\operatorname{Suc}n,y).
$$

**Proof.** Define $D$ as the intersection, expressed by quantification over relations, of all relations containing $(z,b)$ and closed under the displayed rule; restrict it to $N\times X$. Its base and closure follow directly. Every $D$-pair is either $(z,b)$ or obtained by one application of the rule from another $D$-pair: the relation of pairs satisfying this alternative is itself closed and contains the base, and is included in $D$.

Induction on $N$ gives existence of an output. For uniqueness, a pair with first coordinate $z$ must be the base pair, by the zero law. A pair with first coordinate $\operatorname{Suc}n$ must come from a predecessor pair; successor injectivity identifies its first coordinate with $n$. The induction hypothesis identifies its second coordinate, and functionality of $T$ identifies the next output. Thus $D$ is functional.

All quantifiers used to define $D$ are over an admitted relation type $\nu\tau t$, even when $X$ has type $e$. No identity between coextensive graphs, and no function object with output type $\tau$, is inferred. Extra parameters may occur throughout. $\square$

## 2. Real structures and the precise modal bridge

The following construction is deliberately local first. This avoids an unnecessary demand for a single field, or a single comparison map, to persist unchanged through all possibilities.

### Lemma 2.1. Current real existence at a fixed type

RC and the current Peano conditions for $N$ imply the existence of a real-number structure at
$$
\rho:=\nu t.
$$

**Proof.** Code the rationals by natural-number codes for signed reduced fractions, using a positive denominator and a canonical sign convention. Primitive-recursive arithmetic on the Peano base gives a definable rational-code carrier $Q\subseteq N$, with its ordered-field operations represented relationally. Canonical reduced codes avoid any choice of representatives of a quotient.

A real object is a rigid property $F^{\nu t}$ such that its current extension on $Q$ is nonempty, proper, downward closed, and has no greatest member. It holds of no current object outside $Q$. RC supplies a rigid representative for every current rational cut. Lemma 1.1 makes that representative unique.

Order cuts by current inclusion. Distinct cuts have different current extensions, by Lemma 1.1, and the usual comparison of rational lower cuts makes this a linear order.

For addition, form the rational predicate
$$
q\in F+G
\quad\Longleftrightarrow\quad
\exists a,b\in Q\,
(Fa\land Gb\land q<a+b).
$$
The corresponding rigid representative is a cut and is unique. The operation graph says that its third argument is this rigid representative. Negation is similarly obtained from
$$
q\in -F
\quad\Longleftrightarrow\quad
\exists r\in Q\,(\neg Fr\land q<-r).
$$
For nonnegative cuts, multiplication is obtained from the lower closure of the products of positive members, together with all negative rationals; multiplication at arbitrary signs uses this positive operation and the preceding negation graph. The zero and one cuts are the rigid representatives of $q<0$ and $q<1$.

For a **strictly positive** cut $F$, the reciprocal is the rigid representative of
$$
Qq\land
\left[
q\le0\ \lor\
\exists r\in Q\,
\left(r>0\land\neg Fr\land q<\frac1r\right)
\right].
\tag{Rec}
$$
The positive-cut guard is essential. A positive rational member $a$ of $F$ gives an upper bound $1/a$ for this predicate, while a positive rational $r$ outside $F$ shows that it contains some positive rationals. Downward closure and absence of a greatest member follow by rational density. The strict inequality in (Rec) excludes the reciprocal endpoint: when the boundary of $F$ is a positive rational $x$, a candidate $q=1/x$ cannot satisfy $q<1/r$ for any $r\ge x$. Conversely, for positive $q<1/x$, density supplies a rational $r$ with $x\le r<1/q$.

Here is a direct check of $F\cdot F^{-1}=1$, requiring no pre-existing real boundary for $F$. If $a>0$ belongs to $F$ and $b>0$ belongs to its reciprocal, choose $r>0$ outside $F$ with $b<1/r$. Downward closure gives $a<r$, hence $ab<1$. This proves inclusion in the one cut.

Conversely, fix $0<q<1$, choose $a_0>0$ in $F$ and $r_0>0$ outside $F$, and take a positive rational $\delta<(1-q)a_0$. By rational Archimedeanness and the least-number principle, there is a least positive natural $k$ such that $r=a_0+k\delta$ lies outside $F$. Then $a=r-\delta$ lies in $F$, and
$$
a=r-\delta>qr.
$$
Choose a rational $b$ with $q/a<b<1/r$. It belongs to the reciprocal cut and $ab>q$, so $q$ belongs to the product cut. Negative $q$ belong by definition, and $q=0$ belongs because both positive cuts contain positive rationals. This proves the reverse inclusion. Inverses of negative cuts are obtained by negating the inverse of their positive negation. Thus the construction includes multiplicative inverses of every nonzero cut, not merely the ring operations.

All these are current predicates on $Q$, and each is rigidified separately by its unique-existence condition. The operation graphs are therefore total and functional on the cut carrier without Functional Choice. The usual rational-cut identities establish the ordered-field laws: comparisons are comparisons of the displayed rational predicates, and equality of the resulting cut objects follows from Lemma 1.1. No identity is inferred from current coextension of arbitrary, nonrigid relations.

For Dedekind completeness, let $Y$ be a nonempty current family of cuts with an upper bound. Its union is the predicate
$$
U(q):=Qq\land\exists F(YF\land Fq).
$$
It is nonempty, proper because of the upper bound, downward closed, and has no greatest member. Its rigid representative is an upper bound of every member of $Y$, and is included in every upper bound, hence is the supremum.

This construction is the ordinary choice-free Dedekind construction with an explicit representation step. Every current cut predicate has a unique representing object; relation graphs express the operations. These are exactly the points at which a construction using arbitrary intensional predicates instead would fail to give functional operations on objects.

Finally define the natural-number subcarrier of this field as its least subproperty containing zero and closed under addition of one. This gives the $N_{\mathfrak R}$ component required by the map's definition of a real-number structure. All carrier and relation types used are admitted. $\square$

The preceding proof does not need the rational-code carrier to be rigid, or one chosen tuple of field parameters to remain a field elsewhere. It needs their current arithmetic properties and current RC. This matters for the necessitation below.

### Lemma 2.2. Current comparison with every real-number structure

Under RC and the current Peano conditions, for every real-number structure $\mathfrak R$ at any admitted carrier type $\sigma$,
$$
N\approx N_{\mathfrak R},
\qquad
\mathcal P_r(N)\approx X_{\mathfrak R},
\tag{4}
$$
where $X_{\mathfrak R}$ is its real carrier. Consequently,
$$
\operatorname{CH}(\mathfrak R)\leftrightarrow C_N,
\tag{5}
$$
where
$$
C_N:=\forall Y^{(\nu t)t}
\bigl(Y\subseteq\mathcal P_r(N)
\to(Y\precsim N\lor Y\approx\mathcal P_r(N))\bigr).
$$

**Proof.** First, the least subcarrier of an ordered field containing zero and closed under addition of one satisfies the Peano conditions. The field laws imply $1>0$. Induction on this subcarrier proves that every one of its members is nonnegative: zero is nonnegative, and adding one preserves nonnegativity. Consequently every successor is strictly positive, so zero is not a successor. Successor injectivity follows from additive cancellation. Induction itself is the subcarrier's defining minimality.

Form the least relation containing the pair of zeros and closed under simultaneous successors. Induction on both natural-number carriers proves that this relation is total, functional, injective, and surjective. For example, every member of the generated relation is either the zero pair or the simultaneous successor of a preceding pair. Induction and successor cancellation then give uniqueness of the second coordinate, and the symmetric argument gives uniqueness of the first. This proves the first comparison in (4), without a function term having output type $\sigma$.

The usual supremum argument makes the field Archimedean: if its natural subcarrier had an upper bound, its supremum $b$ would have a natural member greater than $b-1$, whose successor would exceed $b$. The resulting rational subfield is dense.

For an injection $X_{\mathfrak R}\to\mathcal P_r(N)$, code rationals by $N$, take the rational lower cut of each field element, and rigidify it. Density gives injectivity. Functionality is uniqueness of rigid representatives.

For an injection in the other direction, send $U\in\mathcal P_r(N)$ to the supremum of the finite partial sums of its ternary expansion with digits $0,2$:
$$
\sum_{k<n}\frac{2\,\mathbf 1_U(k)}{3^{k+1}}.
$$
This notation abbreviates a relationally defined sequence of field elements. Its graph exists by recursion on $N$; no choice of values is needed because the next value is unique. The partial sums are bounded, so field completeness supplies their supremum.

If two rigid subproperties of $N$ are distinct, they have a current member in their symmetric difference by Lemma 1.1. That witness lies in $N$, because both properties are currently included in $N$. The least-number principle derived from induction supplies the first differing index $k$. Suppose the first property has digit $0$ there and the second digit $2$, and let $a$ be their common sum before $k$. The two supremum values $u,v$ satisfy
$$
u\le a+\frac{1}{3^{k+1}},
\qquad
v\ge a+\frac{2}{3^{k+1}},
$$
and hence
$$
v-u\ge\frac{1}{3^{k+1}}>0.
$$
The first bound is obtained by bounding each remaining finite tail by the geometric sum with all digits $2$, then using the supremum property; no independently defined infinite series is assumed. Lemma 1.4 supplies the parameterized partial-sum graphs. This proves injectivity.

The relational Cantor--Bernstein construction gives the second comparison in (4). Transport a subproperty through that bijection, and use the first comparison to transport countability. Injections and bijections compose relationally. This proves (5), in both directions and for every current subproperty. $\square$

No well-orderability of the continuum is asserted here. In particular, (5) concerns the subset-cardinal formulation $C_N$, not the stronger-looking comparison $\mathcal P_r(N)\approx H(N)$ without further choice assumptions.

### Theorem 2.3. Necessary real existence and necessary comparison

Under $\Box RC+\Box\operatorname{Peano}(N)$,
$$
\Box\exists\mathfrak R\,\operatorname{Real}_{\rho}(\mathfrak R),
\qquad \rho=\nu t,
\tag{6}
$$
and, for every admitted carrier type $\sigma$,
$$
\Box\forall\mathfrak R
\left[
\operatorname{Real}_{\sigma}(\mathfrak R)
\to
\bigl(\operatorname{CH}(\mathfrak R)\leftrightarrow C_N\bigr)
\right].
\tag{7}
$$

**Proof.** Lemmas 2.1 and 2.2 prove conditional theorems of $C$, with current RC and current Peano conditions as antecedents. Necessitate those conditional theorems, then apply K to the boxed hypotheses. $\square$

The quantifier scope is essential. The intermediate result has the form
$$
\Box\forall\mathfrak R\,\exists f,g\,
\bigl(\text{$f,g$ are the current comparison bijections}\bigr).
$$
It does **not** assert $\exists f,g\,\Box(\cdots)$. Likewise (6) is
$\Box\exists\mathfrak R\,\operatorname{Real}_\rho(\mathfrak R)$, not
$\exists\mathfrak R\,\Box\operatorname{Real}_\rho(\mathfrak R)$.

IC is unused in this theorem. Rigidity of $N$, useful in the forcing arguments, follows separately from Lemma 1.2; it need not be added to obtain the local-to-necessary bridge.

### Corollary 2.4. The two non-contingency principles are equivalent

Under the hypotheses of Theorem 2.3,
$$
\Box C_N\lor\Box\neg C_N
$$
implies, at every real-carrier type $\sigma$,
$$
\Box\forall\mathfrak R
(\operatorname{Real}_\sigma(\mathfrak R)\to\operatorname{CH}(\mathfrak R))
\ \lor\
\Box\forall\mathfrak R
(\operatorname{Real}_\sigma(\mathfrak R)\to\neg\operatorname{CH}(\mathfrak R)).
$$
Conversely, the latter principle at $\rho=\nu t$ implies
$\Box C_N\lor\Box\neg C_N$.

**Proof.** The forward direction follows from (7). For the converse, use (6) to ensure that the real-structure universal is nonvacuous at every possibility, and then use (7). $\square$

Thus a proof of $\Diamond C_N\land\Diamond\neg C_N$ yields structural CH contingency at the one fixed type $\rho$. The bridge supplies the two directions recorded as conjectured in the cited comparison commit.

## 3. Relation to the map's exact-cardinality Infinity axiom

Define the separate exact-cardinality carrier by
$$
0_{\mathrm{ex}}:=\lambda X^{et}.\forall x^e\,\neg Xx,
$$
with the same successor operation, and let $N_{\mathrm{ex}}$ be its least successor-closed carrier. The map's quantified Infinity axiom is
$$
\operatorname{Inf}_{\mathrm{ex}}
:=
\neg\exists n^\nu
\bigl(N_{\mathrm{ex}}n\land n(\top_e)\bigr).
$$

### Proposition 3.1. A sufficient arithmetic consequence

$\operatorname{Inf}_{\mathrm{ex}}$ implies the Peano zero and successor-injectivity conditions for $N_{\mathrm{ex}}$. Consequently, the boxed Infinity hypothesis supplies a necessary Peano base to which the preceding parametric arguments apply.

**Proof.**

First, induction on $N_{\mathrm{ex}}$ shows that each exact finite-cardinality predicate respects relational bijections. Zero respects them because bijective carriers are empty together. For the successor step, restrict a witnessing bijection after removing an element and its image. In particular, these predicates respect current coextension.

Second, under $\operatorname{Inf}_{\mathrm{ex}}$, every $n\in N_{\mathrm{ex}}$ has a current instance. Zero has the empty instance. If $nX$, then $X$ cannot contain every individual: otherwise coextension invariance would give $n(\top_e)$. Choose $a\notin X$; then $X\cup\{a\}$ instantiates $\operatorname{Suc}n$. Formally, use the induction predicate
$N_{\mathrm{ex}}n\land\exists X\,nX$, so the step retains the numberhood premise needed to invoke Infinity.

Third, two exact finite-cardinality predicates sharing an instance are identical. This is proved by induction. Every such number is zero or a successor. Zero cannot share an instance with a successor. If $\operatorname{Suc}k$ and $\operatorname{Suc}\ell$ share the instance $X$, choose their removed-element witnesses $a,b$. The carriers $X\setminus\{a\}$ and $X\setminus\{b\}$ are bijective by the explicit swap of $a,b$, with the other elements fixed. Bijection invariance puts $k,\ell$ on a common instance. Induction gives $k=\ell$, and congruence gives equality of their successors. This is identity obtained inductively, not an illicit use of Logical Equivalence on a conditional coextension.

Now suppose $\operatorname{Suc}m=\operatorname{Suc}n$. Instantiate $m$ by $X$, choose $a\notin X$, and let $Y=X\cup\{a\}$. It instantiates both successors. Removing the witness for $\operatorname{Suc}n$ leaves a carrier bijective with $X$, so $nX$. The preceding uniqueness result gives $m=n$.

Finally, $0_{\mathrm{ex}}\ne\operatorname{Suc}n$ already follows in $H$ by testing both predicates on the empty property. This proves the current conditional theorem. Necessitate it to obtain the consequence of
$\Box\operatorname{Inf}_{\mathrm{ex}}$. $\square$

This is an alternative **instantiation** of the arithmetic base. It does not identify $N_{\mathrm{ex}}$ with LowerNat, nor assert that the two displayed Infinity principles are definitionally or logically equivalent. The structural conclusion is independent of that notational choice: run the parametric proof with $N_{\mathrm{ex}}$, then use its structural bridge.

The quantified axiom matters. A schema asserting, separately for every standard natural $k$, that at least $k$ individuals exist does not automatically provide the internal statement used above, namely instantiation of every member of $N_{\mathrm{ex}}$. The proof does not replace the quantified hypothesis by that weaker schema.

## 4. Why current largeness alone is insufficient

The following countermodel separates the repaired current cardinal bound from necessary arithmetic. It validates the original strict-propositional-size, proper-interval FP principle.

### Theorem 4.1. Singleton-base root-and-cloud countermodel

In ZFC there is a model of
$$
C+\Box RC+\Box IC+FP+\mathrm{NC\mbox{-}CH}
$$
with a current real-number structure $\mathfrak R$ such that
$$
\mathcal P_r(X_{\mathfrak R})\prec\mathrm{Prop}.
\tag{8}
$$
It also satisfies boxed BF. The actual proposition domain can be made arbitrarily large. It fails the necessary arithmetic hypotheses above.

**Construction.** This model has one ordinary world, the root, together with cloud possibilities; its individual base is a singleton. Put $\mathfrak c=2^{\aleph_0}$. Choose a strong-limit cardinal $\mu$ of countable cofinality such that
$\mu>2^{\mathfrak c}$. For example, start above $2^{\mathfrak c}$ and take the supremum of its finite beth iterations.

Let $\mathcal P_\mu=(P_i)_{i\in I}$ contain one representative of every isomorphism class of nonempty partial orders of size below $\mu$. Take the rooted sum of their forcing frames: the root $r$ is isolated under refinement and sees every point, while each cloud point sees exactly its refinements within its component. Use the full modalized-domain construction with the constant individual domain
$$
D_e=\{*\}.
$$
This is $M(\mathcal P_\mu,\{*\})$ in Definition 4.1 of Bacon's
[Modalized Domains on Possibility Frames](https://andrew-bacon.github.io/techdoc/modalized-domains.pdf).
Its restriction to the admitted relational types is a model in the present language.

For clarity, the propositional domain is the regular-open algebra of the frame. At a point $x$, two propositions are identified when their restrictions to the points seen from $x$ agree. At a function type, the full set-function space is equipped with the corresponding identity relation: outputs must agree on every accessible point whenever the inputs agree there. An entity exists at a point when it is self-related there. The quantifiers and equality are those of the full modalized-domain construction. Thus the raw function domains should not be confused with their identity classes at an evaluation point.

**Classicism, comprehension, and choice.** The source's Theorems 3.12, 3.14 and 4.4 apply to every nonempty individual domain, including a singleton. They give $C,\Box RC,\Box IC,\Box BF$. Rigidification at the root is the check-closure of the current extension:
$$
\check E(x)=\bigvee_{a\in E}\llbracket x=a\rrbracket.
$$
Choice uses selection at the root and Boolean mixing in the cloud.

If the RC schema includes the empty argument tuple, that extra instance is harmless: at the bivalent root a proposition is currently equivalent to either $\top$ or $\bot$, both rigid; in the cloud every relation, including a proposition, is rigid because the box is idle.

The root proposition algebra is
$$
B\cong\mathbf2\times\prod_{i\in I}\operatorname{RO}(P_i),
\qquad |B|=2^\mu.
\tag{9}
$$
For the upper bound, there are at most $\mu$ poset representatives, and each regular-open algebra has size less than $\mu$, by strong limit. Their product has size at most $\mu^\mu=2^\mu$. For the lower bound, choose antichains of cardinalities cofinal in $\mu$. Their regular-open algebras are powersets, and the product of these factors has size $2^\mu$.

**Root fullness and the finite-domain qualification.** At the root every external relation on the root identity classes is represented. In particular, give the desired relation its chosen root extension and the empty cloud extension. It respects the identity relations and exists at the root.

The source's Lemma 6.8 is stated with an infinite individual domain. Only the portions of its proof concerning the specific individual-based countable and inaccessible predicates use that hypothesis. Its conclusions about current complete Boolean algebras, relational injections, interval isomorphisms, and the number of rigid subproperties use root fullness and unique check-closures only. Those arguments apply unchanged here. The FP predicate Fin in the present map means Dedekind finiteness via relational injections; it does not refer to the finite-cardinality coding based on the individual domain.

**Forcing Possibilism.** Root fullness makes an internally complete Boolean algebra an external complete Boolean algebra on its root identity classes, and makes internal cardinal comparisons the corresponding external injection comparisons.

For an infinite complete Boolean algebra $A$, Pierce's cardinality theorem gives
$$
|A|^{\aleph_0}=|A|.
$$
Our choice of $\mu$ gives $\mu^{\aleph_0}=2^\mu$: if $\mu_n$ increases cofinally to $\mu$, strong limit gives $2^\mu=\prod_n2^{\mu_n}\le\mu^{\aleph_0}\le2^\mu$. Hence no complete Boolean algebra has cardinality in $[\mu,2^\mu)$. Indeed, a cardinal $\lambda$ in that interval satisfies
$\lambda^{\aleph_0}\ge\mu^{\aleph_0}=2^\mu>\lambda$.

Consequently every complete Boolean algebra finite or strictly smaller than $B$ has cardinality below $\mu$. Every nontrivial such algebra occurs as the regular-open algebra of a lottery component: use its nonzero elements as a forcing poset. The proposition supported exactly on that component has the required principal interval. It omits the root, so it is different from $\top$. The degenerate algebra is represented below $\bot$. Root fullness supplies the relational isomorphism. This proves the exact strict-size, proper-interval FP required here. The cardinal argument is the one in Remark 6.12 of the source.

**The repaired largeness premise.** By (9), choose a subset of the root proposition domain of cardinality $\mathfrak c$, and transport the ordinary real field onto it. Root fullness supplies all its relations, and makes it a real-number structure in the map's current sense.

Every subset of this carrier has a rigid current representative. Two such representatives are identical precisely when their current extensions agree. Thus the root identity classes in $\mathcal P_r(X_{\mathfrak R})$ have cardinality
$$
2^{\mathfrak c}<2^\mu=|\mathrm{Prop}|.
$$
Root fullness supplies the required internal injection into propositions, and excludes the reverse injection by the external cardinal comparison. Thus (8) is an internal strict inequality, not just a heuristic external bound.

**Non-contingency of CH.** In every cloud component, the box is idle and extensionality holds. Internally there are exactly two propositions. Since the individual domain is a singleton, induction on the fixed simple types makes every type internally finite in the cloud. Finite bounds may be taken recursively as
$$
n_e=1,\qquad n_t=2,\qquad
n_{\sigma\to\tau}=n_\tau^{\,n_\sigma}.
$$
Extensionality makes a function determined by its finite table. Boolean mixtures can give many raw representatives, but internally each is equal to one of those finitely many tables. This is a claim of internal finite enumeration, not a claim that the raw function sets are finite.

No finite carrier supports an ordered field. Hence no real-number structure exists at any fixed type anywhere in the cloud.

At the root, by fullness, every real-number structure is an ordinary complete ordered field on its root identity classes, and its CH verdict agrees with the ambient ZFC universe. If ambient CH holds, the boxed universal asserting CH of all real structures holds at every carrier type: it is true at the root and vacuous in the cloud. If ambient CH fails, the opposite boxed universal holds instead. Thus NC-CH holds at every type in either case.

**Failure of the arithmetic hypotheses.** In the cloud every fixed type is internally finite. The exact quantified Infinity axiom therefore fails there, and the at-least successor eventually stabilizes, violating successor injectivity on LowerNat. Accordingly neither of the necessary arithmetic packages used above holds at the root.

For the individual carrier $e$, the unboxed exact Infinity axiom already fails at the root: there is exactly one individual, so the exact cardinality-one predicate holds of $\top_e$. Thus this example does **not** independently separate actual $\operatorname{Inf}_{\mathrm{ex},e}$ from its necessitation. It refutes the implication to CH contingency from comprehension, choice, FP and the stated current real/powerset largeness condition, without an added arithmetic hypothesis.

This verifies the countermodel. In particular, actual real existence and even arbitrarily large actual powerset bounds do not ensure that infinite mathematical structures survive into the possibilities represented by the forcing intervals. $\square$

### Proposition 4.2. Necessary Infinity alone is also insufficient

There is a model of
$$
C+\Box RC+\Box IC+FP_<+\Box\operatorname{Inf}_{\mathrm{ex},e}
+\mathrm{NC\mbox{-}CH}_{\mathrm{str}}.
$$
It has necessarily available real structures at a fixed type, and it fails the corrected largeness premise $L$. This is a specialization of an existing construction, not a claim of a new model family.

**Construction and sources.** Work in ZFC. Use the map's [full infinite S5 construction](https://github.com/zwlgzwlg/Logical-Maps/blob/163d1d8b6112a52d532696a9732402b8a8680fd1/logical-maps/topics/classicism/models/full-infinite-s5.yaml), attributed there to Cian Dorr, with world set $W=\omega$ and the [group's fixed-infinite individual setting](https://github.com/zwlgzwlg/Logical-Maps/blob/163d1d8b6112a52d532696a9732402b8a8680fd1/logical-maps/topics/classicism/groups/full-action-models.yaml), taking $D=\omega$. The generic record permits arbitrary infinite $W$; the FP argument here specifically requires the countable choice $W=\omega$. It is not asserted for every infinite-world variant.

Fullness at every world supplies boxed RC, and the metatheoretic choice argument supplies boxed IC, as in the recorded arguments [full-rigid-comprehension](https://github.com/zwlgzwlg/Logical-Maps/blob/163d1d8b6112a52d532696a9732402b8a8680fd1/logical-maps/topics/classicism/arguments/full-rigid-comprehension.yaml) and [intensional-choice-well-ordering](https://github.com/zwlgzwlg/Logical-Maps/blob/163d1d8b6112a52d532696a9732402b8a8680fd1/logical-maps/topics/classicism/arguments/intensional-choice-well-ordering.yaml).

The **exact quantified** individual Infinity axiom holds at every world. Extensional fullness supplies the property of cardinalities that hold only of properties with finite current extensions. It contains exact zero and is successor-closed; hence every internally finite cardinality has this property and none holds of the infinite individual domain. This is the recorded [infinitely-many-individuals argument](https://github.com/zwlgzwlg/Logical-Maps/blob/163d1d8b6112a52d532696a9732402b8a8680fd1/logical-maps/topics/classicism/arguments/infinitely-many-individuals.yaml). Since its conditions hold at every world, its conclusion is necessary. This verifies the boxed exact axiom directly, rather than identifying it with the LowerNat premise.

**Original FP.** The proposition algebra is $\mathcal P(\omega)$, of cardinality $\mathfrak c=2^{\aleph_0}$. In ZFC, an infinite complete Boolean algebra has a countably infinite disjoint family of nonzero elements; taking all joins of subfamilies embeds $\mathcal P(\omega)$ into it. Therefore every complete Boolean algebra strictly smaller than the proposition algebra is finite. An algebra with $n$ atoms is represented by the interval below a proposition true at exactly $n$ worlds. That interval is proper since $W$ is infinite. The degenerate algebra is represented below bottom. Fullness represents the isomorphisms and makes the internal completeness and cardinal comparisons agree with the external ones. This is exactly the recorded [forcing-possibilism-countably-many-arrows argument](https://github.com/zwlgzwlg/Logical-Maps/blob/163d1d8b6112a52d532696a9732402b8a8680fd1/logical-maps/topics/classicism/arguments/forcing-possibilism-countably-many-arrows.yaml).

**CH and largeness.** At every world, extensional fullness makes every current real structure an ordinary complete ordered field in the metatheory, and makes its second-order quantifiers full. Its CH verdict therefore agrees with the ambient universe, independently of the world or carrier type. This is the recorded [second-order-analysis-extensionally-full argument](https://github.com/zwlgzwlg/Logical-Maps/blob/163d1d8b6112a52d532696a9732402b8a8680fd1/logical-maps/topics/classicism/arguments/second-order-analysis-extensionally-full.yaml). Thus structural NC-CH holds whether ambient CH is true or false. Real structures do exist throughout at a fixed type: for example, ordinary rational cuts can be represented by rigid properties of the fixed individual domain, at type $et$. The result does not depend on vacuous real-structure quantification.

Every real carrier has current cardinality $\mathfrak c$. Fullness and unique rigid representatives give
$$
|\Pi|=\mathfrak c,
\qquad
|\mathcal P_r(X_{\mathfrak R})|=2^{\mathfrak c}>\mathfrak c.
$$
Hence $L$ fails. Moreover, the **literal reversed gloss**
$$
\neg\bigl(\mathcal P_r(X_{\mathfrak R})\precsim\Pi\bigr)
$$
holds. Thus the same model refutes the repair using that literal gloss even after necessary Infinity is added. Correcting the direction is a substantive change to the premise. $\square$

Relative to the common base $C+\Box RC+IC+FP_<$, the two checks can be summarized as follows:

| Model | Corrected strict $L$ | $\Box\operatorname{Inf}_{\mathrm{ex},e}$ | Structural NC-CH |
| --- | --- | --- | --- |
| Large singleton-base root-and-cloud model | True | False | True |
| Full S5 with $W=D=\omega$ | False | True | True |

This shows that neither of the two additions can simply be omitted from the repaired package proved here. It does not establish that every part of their formulations is minimal.

### Proposition 4.3. Joint consistency of the repaired assumptions

**Proposition.** Relative to ZFC, the package
$$
C+\Box RC+IC+FP_<+\Box\operatorname{Inf}_{\mathrm{ex},e}+L
$$
is consistent. Here $FP_<$ is the original principle with the finite-or-strictly-fewer-than-propositions bound; $\operatorname{Inf}_{\mathrm{ex},e}$ is the map's quantified infinity assertion using the exact-cardinality natural-number carrier; and $L$ is the strict comparison $\mathcal P_r(X_{\mathfrak R})\prec\Pi$ for a current real-number structure. Thus the refutation of NC-CH under these assumptions is nonvacuous.

**Proof.** Work in ZFC and choose a strong-limit cardinal $\mu$ of countable cofinality with $\mu>2^{2^{\aleph_0}}$. For example, start the sequence of finite beth iterates above $2^{2^{\aleph_0}}$ and take its supremum. Let $P_\mu$ contain one representative of each isomorphism class of nonempty partial orders of size below $\mu$, and use the cloud model
$$
M=M(P_\mu,\omega).
$$
Theorem 4.4 and Remark 6.12 of *Modalized Domains on Possibility Frames* give $C+\Box RC+\Box IC+\Box BF+FP_<$ in this model, with $FP_<$ evaluated at the isolated root. Remark 6.12 also gives
$$
|\Pi|=2^\mu.
$$
Its proof uses Pierce's cardinality theorem to show that every infinite complete Boolean algebra of size below $2^\mu$ already has size below $\mu$, so the stated lottery family represents every required algebra as a proper principal interval. Since the metatheory here is ZFC, Dedekind finiteness agrees with ordinary finiteness.

The source's Theorem 6.5 establishes boxed infinity for its at-least cardinal successor carrier. To check the exact quantified assertion used here, let
$$
0_{\mathrm{ex}}(X)=\neg\exists x\,Xx,
\qquad q_n=\mathrm{Suc}^{\,n}(0_{\mathrm{ex}}),
$$
and let $N_{\mathrm{ex}}$ be the definitionally least collection containing $0_{\mathrm{ex}}$ and closed under the same cardinal successor. Write $\mathbf 1_e=\lambda x^e.\top$.

The proof of source Lemma 6.4(c) applies with this closed zero term. More explicitly, the check-closure
$$
Z(Q)=\bigvee_{n<\omega}\operatorname{id}(q_n,Q)
$$
exists at the root and at every cloud point. It contains $q_0$ everywhere. Congruence of the everywhere-existing successor operation gives
$$
\operatorname{id}(q_n,Q)
\le\operatorname{id}(q_{n+1},\mathrm{Suc}(Q)),
$$
so $Z$ is successor-closed everywhere. The least-carrier definition therefore yields
$$
\llbracket N_{\mathrm{ex}}(Q)\rrbracket\le Z(Q).
\tag{JC.1}
$$
This step uses the check-closure argument itself, rather than identifying the exact and at-least zero quantifiers.

All individuals are the ordinary members of $\omega$; they exist everywhere and their identity is literal at every point. By induction on each external natural number $n$, the exact quantifier $q_n$ has value bottom on every crisp infinite property: exact zero is false on a nonempty property, and deleting one member from an infinite crisp extension leaves it infinite. In particular,
$$
q_n(\mathbf 1_e)=\bot
\quad\text{for every }n<\omega.
\tag{JC.2}
$$
At every point and for every eligible $Q$, application congruence, (JC.1), distributivity of a finite meet over an arbitrary join, and (JC.2) give
$$
\begin{aligned}
\llbracket N_{\mathrm{ex}}(Q)\rrbracket\wedge Q(\mathbf 1_e)
&\le\bigvee_{n<\omega}
 \bigl(\operatorname{id}(q_n,Q)\wedge Q(\mathbf 1_e)\bigr)\\
&\le\bigvee_{n<\omega}q_n(\mathbf 1_e)
=\bot.
\end{aligned}
$$
Hence no exact finite cardinal quantifier applies to the total individual carrier, at any point. This is precisely the quantified $\operatorname{Inf}_{\mathrm{ex},e}$ assertion. It is valid throughout the model, so its box is valid as well (source Corollary 3.7(e)).

Finally, root fullness, source Lemmas 6.7–6.8, makes the internal current powersets and injection comparisons agree with their external counterparts. At the root the natural carrier has size $\aleph_0$, the rigid binary-real carrier has size $\mathfrak c=2^{\aleph_0}$, and its rigid powerset has size $2^{\mathfrak c}$. The local real-structure construction and comparison proved in Part I therefore give a current real-number structure $\mathfrak R$ for which
$$
|\mathcal P_r(X_{\mathfrak R})|
=2^{\mathfrak c}
<2^\mu
=|\Pi|.
$$
Root fullness represents the forward injection and excludes the reverse injection internally, establishing $L$. This verifies the entire package. $\square$

**Source and provenance.** Andrew Bacon with Claude Opus 5.5, *Modalized Domains on Possibility Frames*, draft dated 23 October 2026, [author's PDF](https://andrew-bacon.github.io/techdoc/modalized-domains.pdf), Theorem 4.4, Corollary 3.7(e), Lemma 6.4(c), Lemmas 6.7–6.8, and Remark 6.12. The cloud construction and original strict-FP consistency are source results. The paragraph checking the map's exact quantified infinity assertion is an explicit adaptation of the source's check-closure proof, not a quotation of Theorem 6.5.

---

# Part II. The bounded forcing proof

## B.0. Statement and scope

Use the number carrier in commit [163d1d8](https://github.com/zwlgzwlg/Logical-Maps/commit/163d1d8b6112a52d532696a9732402b8a8680fd1):

$$
\nu=(et)t,\qquad z=\lambda U^{et}.\top,
$$
$$
N=\lambda n^\nu.\forall Z^{\nu t}
 \bigl((Zz\land\forall m^\nu(Zm\to Z(\operatorname{Suc}_e m)))\to Zn\bigr).
$$

Thus $N$ is the at-least number carrier, LowerNat. No identification with the map's exact-cardinality carrier is assumed. The necessary Peano hypothesis is

$$
\Box\left[
 \forall n\in N\ z\ne\operatorname{Suc}_e n
 \ \land\
 \forall m,n\in N\
 (\operatorname{Suc}_e m=\operatorname{Suc}_e n\to m=n)
\right].
\tag{B.1}
$$

Induction and successor closure are supplied by the definition of $N$.

For a carrier $A$, define its current rigid power by

$$
\mathcal P_r(A)=\lambda U.\bigl(\operatorname{Rigid}(U)\land U\subseteq A\bigr).
$$

Put

$$
S=\mathcal P_r(N),\qquad T=\mathcal P_r(S),
\tag{B.2}
$$
$$
C_N=\forall X\,
\bigl(X\subseteq S\to(X\precsim N\lor X\approx S)\bigr).
\tag{B.3}
$$

Here $\subseteq$ is current pointwise inclusion, $\precsim$ is existence of a current relational injection, and $\approx$ between carriers is existence of a current relational bijection. Coextension of two relations will instead be written $\equiv_{\mathrm{ext}}$. All quantifiers in (B.2) and (B.3) have fixed admitted types.

The bounded forcing premise is the following schema, with the carrier type of $B$ fixed externally in each instance:

$$
\begin{split}
FP_{\precsim T}:\quad
\forall B,E\ \bigl[
  \operatorname{CBA}(B,E)\land B\precsim T
  \ \to\
  \exists p^t\exists h\
  \operatorname{OrderIso}(h;B,E;\downarrow p,\le)
\bigr],
\end{split}
\tag{B.4}
$$

where

$$
\downarrow p=\lambda q^t.\Box(q\to p).
$$

The isomorphism in (B.4) is a current relational isomorphism onto the full principal interval. The premise permits $p=\top$. A nontrivial Boolean algebra has $p\ne\bot$, which is the only nonzero requirement used below. Neither the size comparison nor the isomorphism is asserted necessary.

**Bounded forcing theorem.** In Classicism, assume:

1. Necessary Rigid Comprehension, at the finitely many relational types used below.
2. Intensional Choice, unboxed, at the finitely many types used below.
3. The necessary Peano conditions (B.1).
4. Rigidity of $N$.
5. $FP_{\precsim T}$.

Then

$$
\boxed{\Diamond C_N\land\Diamond\neg C_N.}
\tag{B.5}
$$

Rigidity of $N$ is retained explicitly to match the reported formal endpoint. Its mathematical derivation from Rigid Comprehension and the least-successor-closed definition is discussed in the foundations part; it can be substituted once that derivation is accepted.

The proof of (B.5) is entirely at the cardinal level. No real-number field, necessary Dedekind construction, or cardinal-to-structural bridge is needed for this part.

### Relation to the original Forcing Possibilism

Let $FP_{\mathrm{Prop}}$ be the original principle: every finite complete Boolean algebra, and every complete Boolean algebra strictly smaller than propositions, is represented by a proper principal interval. If

$$
T\prec\mathrm{Prop},
\qquad
A\prec B\ \text{means}\ A\precsim B\land\neg(B\precsim A),
\tag{B.6}
$$

then $FP_{\mathrm{Prop}}$ implies every instance of (B.4). Indeed, $B\precsim T$ gives $B\precsim\mathrm{Prop}$; an injection $\mathrm{Prop}\to B$ would compose to an injection $\mathrm{Prop}\to T$, contradicting (B.6).

Once the real/cardinal comparison in the foundations part is supplied, (B.6) is the intended assertion that there are more propositions than rigid current properties of a real-number structure. Its direction is important: it excludes an injection **from propositions into those properties**, and includes an injection in the other direction. The opposite non-injection does not express the intended largeness condition.

For comparison, the inaccessible package recorded at commit 163d1d8 also implies (B.4). Its regularity clause first bounds an image of $N$ in a proper initial segment. Two applications of its rigid-power strong-limit clause then bound $S$ and $T$ in proper initial segments. The present argument requires only the range $B\precsim T$. This is a reduction in the coverage needed for the application; no equivalence between the global FP schemata is asserted.

## B.1. Relational conventions and foundational dependencies

We use only finite relational types. Finite products and tagged finite unions are abbreviations for fixed typed encodings. For example, a pair of objects $a^\alpha,b^\beta$ can be represented by

$$
\lambda H^{\alpha\beta t}.H[a,b].
$$

Current equality of these pair codes is equivalent to equality of both coordinates, by comprehension. On necessarily distinct factors the codes are necessarily distinct. Relations on tuples are alternatively written with several arguments, without introducing product sorts.

Every map in this proof is a relation satisfying totality, functionality, and the stated injectivity or surjectivity conditions. Before rigidifying a graph from $A$ to $B$, restrict it to $A\times B$; irrelevant pairs outside its stated domain and codomain are discarded. Notation such as $f(a)$ abbreviates the unique current output of such a relation. It does not assert that a corresponding function term exists. Recursion is recursion for graphs.

A domain will be called **stable** in this part if it is rigid and its current members are necessarily distinct:

$$
\forall x,y\in A\ (x\ne y\to\Box(x\ne y)).
\tag{B.7}
$$

This is an abbreviation for the two displayed properties, not an additional primitive principle. A collection of all current objects of some specified kind need not itself be rigid. When a stable collection is required, we take its unique rigid current representative and verify (B.7).

The following foundational facts are used. They are proved in the foundations part or in the indicated portions of Bacon's [general forcing draft](https://andrew-bacon.github.io/techdoc/CH_contingency_general_forcing.pdf).

**B.1.1. Unique rigid representatives and restricted Barcan.** Rigid Comprehension gives every current relation a unique coextensive rigid representative. For rigid $A$,

$$
\forall x\in A\,\Box\varphi(x)
\ \Longrightarrow\
\Box\forall x\in A\,\varphi(x),
\tag{B.8}
$$
$$
\Diamond\exists x\in A\,\varphi(x)
\ \Longrightarrow\
\exists x\in A\,\Diamond\varphi(x).
\tag{B.9}
$$

These are the inextensibility argument and its classical contrapositive, not an unrestricted Barcan principle. The notation $U^\dagger$ for a rigid representative abbreviates a uniquely specified relation; it introduces no function choosing representatives. See the draft, Lemma 2.1.

**B.1.2. Arithmetic.** Under (B.1), rigidity of $N$, and the defining induction principle, $N$ is a necessarily Peano carrier and satisfies (B.7). The usual finite tuple coding, order on $N$, finite counting, and relational recursion are available. Necessary Distinctness follows by induction: zero is necessarily distinct from every successor, and necessary injectivity of successor propagates necessary inequalities. See the draft, Lemma 2.2.

**B.1.3. Transport on stable domains.** Rigidification of a current relation on a finite product of stable domains preserves both its positive and negative current atomic facts necessarily. For a negative fact about a tuple $\bar a$, each current tuple in the relation differs from $\bar a$ in a necessarily distinct coordinate; inextensibility excludes $\bar a$ at every possibility. Restricted Barcan then preserves current first-order relational laws on those domains. Distinct rigid subproperties of a stable domain are necessarily distinct, because a current member of their symmetric difference continues to distinguish them. See the draft, Lemma 5.1.

**B.1.4. Necessary preservation of well-orders.** If a current well-order on a stable domain is rigidified, it is necessarily a well-order. Here is the additional argument beyond first-order transport. Let $\operatorname{Bad}(a)$ say that the segment through $a$ is not well-founded. In a linear order, $\operatorname{Bad}(a)$ implies that some predecessor $b<a$ is bad: restrict a nonempty set with no least member to a suitable member below $a$. If a bad segment were possible, restricted Barcan would give a current $a$ with $\Diamond\operatorname{Bad}(a)$. Choose the least such current $a$ in the current well-order. Restricted Barcan applied to the possible bad predecessor, and stability of the ordering facts, give a smaller current member with the same property, a contradiction. A possible failure of well-foundedness of the whole order gives a possible bad segment. This is the proof in draft Lemma 5.1.

**B.1.5. Current well-order comparison.** Two current well-orders are isomorphic, or one is isomorphic to a proper initial segment of the other, and such isomorphisms are unique. One relational proof defines the comparison graph by declaring two elements related exactly when their predecessor segments are isomorphic. A well-order cannot be isomorphic to a proper initial segment of itself, by the usual least-disagreement argument. Consequently the comparison graph is functional and injective, and its domain and range are initial segments. If neither were the whole order, their respective least omitted members would have isomorphic predecessor segments, contradicting their omission. This proves comparison without a simultaneous choice of isomorphisms: the comparison relation is defined by comprehension, and witnesses on overlapping segments are unique. The usual Cantor–Bernstein proof also works for relational injections, by taking the least successor-closed subcarrier in its standard decomposition.

Only this current comparison argument is needed below. Section B.3 constructs the particular first uncountable carrier directly from countable well-order codes, rather than assume a general typed Hartogs construction.

Under these facts, $N$ is stable. So is $S_0:=S^\dagger$: its current members are rigid subproperties of stable $N$, and hence necessarily distinct. Currently $S_0$ and $S$ have exactly the same members. In particular,

$$
\mathcal P_r(S_0)\equiv_{\mathrm{ext}}T
$$

currently. $S_0$ is the stable collection of old binary-real codes; at another possibility $S$ may have additional members. We do not identify these two collections necessarily.

## B.2. Atomic intervals yield ordinary relational choice

This is the first new ingredient.

### B.2.1. Representing a current proposition-valued graph

Let $I$ be stable, and let $H(i,q)$ be a current total functional relation from $I$ to propositions. There is a relation $E$ on the type of $I$ such that

$$
\Box(E\subseteq I),\qquad
\forall i\in I\ \forall q\,(H(i,q)\to E i=q).
\tag{B.10}
$$

The equalities in (B.10) are propositional identities.

**Proof.** First replace $H(i,q)$ by $Ii\land H(i,q)$, so that every current pair has its first coordinate in $I$. Rigidify this restricted graph to $H^\dagger$, and set

$$
E i=I i\land\exists q\,(H^\dagger(i,q)\land q).
$$

For current pairs $H(i,q)$ and $H(j,r)$,

$$
\Box(i=j\to q=r):
$$

if $i=j$, current functionality gives $q=r$, and necessity of identity applies; otherwise Necessary Distinctness of $I$ makes the antecedent necessarily false. Restricted Barcan over the rigid graph transports this conditional functionality. For a current $H(i,q)$, persistence of the graph gives $q\le E i$, while the transported functionality gives $E i\le q$. Persistence of $I i$ gives $I i=\top$ for that current member. Hence $E i=q$. Its necessary support in $I$ follows from the definition. This is the argument of draft Lemma 6.3, with a stable domain in place of $N$. $\square$

### B.2.2. Atomic choice lemma

Suppose $I,Y$ are stable and $\mathcal P_r(I)\precsim T$. Every current serial relation

$$
R\subseteq I\times Y,\qquad
\forall i\in I\ \exists y\in Y\,R(i,y),
\tag{B.11}
$$

has a current choice graph.

**Proof.** An empty $I$ has the empty choice graph, so assume $I$ nonempty. The rigid current subsets of $I$, ordered by inclusion, form a complete atomic Boolean algebra. Its atoms are the singleton subsets, and its cardinality satisfies the bound in (B.4). Apply FP and write $p_i$ for the image of the singleton at $i$, and $p$ for the top of the resulting interval. Then

$$
p_i\ne\bot,\qquad p_i\wedge p_j=\bot\quad(i\ne j),
\qquad \bigvee_{i\in I}p_i=p.
\tag{B.12}
$$

These are current facts about the full propositional interval, and each $p_i$ is a propositional atom: any proposition below it is also in that full interval.

Lemma B.2.1 supplies $E$ with $E i=p_i$ for every current $i\in I$. Rigidify $R$; its positive and negative facts on current $I\times Y$ persist by B.1.3. Continue to call this rigid graph $R$. Define

$$
F(y)=Yy\land
\left(\neg p\lor
  \exists i\in I\,(E i\land R(i,y))\right).
\tag{B.13}
$$

The join of the propositions $E i$, restricted to $I$, is $p$. One inequality follows from persistence and the individual inequalities $p_i\le p$; the other follows from (B.12), since each $p_i$ entails the existential with witness $i$. Seriality supplies a persistent current $R(i,y)$ separately for every current $i$, so every $p_i$ entails that $F$ is instantiated. Their join does too. Outside $p$, a current member of $Y$, supplied by any fibre of (B.11), persists and satisfies $F$. Hence

$$
\Box\exists y\,F(y).
$$

Apply IC to obtain $G\le F$ with $\Box\exists!y\,Gy$.

Fix a current $i\in I$. Disjointness in (B.12), equality $E j=p_j$ for current $j$, and restricted Barcan for $I$ give

$$
p_i\le
\forall j\in I\,(E j\to j=i).
\tag{B.14}
$$

Consequently, on $p_i$, any $G$-witness lies in $Y$ and in the $i$-th $R$-fibre. Since $p_i\ne\bot$, restricted Barcan for rigid $Y$ pulls such a witness back to a current $y\in Y$ with

$$
p_i\land Gy\ne\bot.
$$

Atomhood makes $p_i\le Gy$. By (B.14) and $G\le F$, also $p_i\le R(i,y)$. A current negative $R(i,y)$ would persist, which is impossible below nonzero $p_i$; therefore $R(i,y)$ holds currently.

Define

$$
C(i,y)\quad\Longleftrightarrow\quad
Ii\land Yy\land p_i\le Gy.
\tag{B.15}
$$

The notation $p_i$ in (B.15) is shorthand for the unique output of the current atomic-image graph, so (B.15) defines a relation by comprehension. Existence has just been proved. If it held of two distinct current $y,y'\in Y$, necessary uniqueness of $G$ would give $p_i\le(y=y')$, while Necessary Distinctness of $Y$ would make that equality impossible. Thus the output is unique. This proves the lemma. $\square$

### B.2.3. Quotient-indexed choice

If $I$ is stable and there is a current surjection $S_0\twoheadrightarrow I$, then the conclusion of B.2.2 holds for every stable target $Y$.

Indeed, inverse image along the surjection gives a current injection

$$
\mathcal P_r(I)\hookrightarrow\mathcal P_r(S_0)\approx T.
\tag{B.16}
$$

The inverse image is taken extensionally and then rigidified. Surjectivity gives injectivity; uniqueness of rigid representatives makes the graph functional. A surjection is sufficient for (B.16). A simultaneous choice of its inverse fibres is not assumed.

In particular, we obtain ordinary countable relational Choice into any stable target. There is an explicit surjection $S_0\twoheadrightarrow N$, using natural-number codes and a default value. We also obtain Choice indexed by $S_0$, and by any stable quotient of $S_0$.

This is not a claim that IC alone entails ordinary Choice. The relevant atomic FP instance is essential to this derivation.

## B.3. A stable presentation of the current $\omega_1$

We require a stable $A$, with a rigid strict order $<$, such that:

$$
(A,<)\text{ currently has order type }\omega_1,
\tag{B.17}
$$
$$
\Box\operatorname{WO}(A,<),
\qquad
\Box\forall a\in A\ (A_{<a}\precsim N),
\tag{B.18}
$$

and there is a current surjection

$$
S_0\twoheadrightarrow A.
\tag{B.19}
$$

This construction refines draft Lemma 5.2 by recording (B.19).

Code a well-order on a subcarrier of $N$ by a rigid binary relation on $N$, using its diagonal for its field and its off-diagonal part for its strict order. The decoded field is taken with its unique rigid representative; transport on $N$ makes it necessarily coextensive with the diagonal. Let $W_0$ be the rigid representative of the collection of all current such codes. Its current members are necessarily distinct, by B.1.3. Each remains a well-order, by B.1.4; restricted Barcan gives that assertion necessarily for all members of $W_0$.

For current codes, a witnessing isomorphism or proper-initial-segment isomorphism can be rigidified on $N^2$, so it remains such necessarily. The negations of these comparisons persist as well: current well-order comparison gives the appropriate alternative, and necessarily well-founded orders cannot be isomorphic to their own proper initial segments.

For each current isomorphism class in $W_0$, take its unique rigid representative as a subproperty of $W_0$. Let $A$ be the rigid collection of these class representatives. Since $W_0$ is stable, distinct class representatives are necessarily distinct. Rigidify the current proper-initial-segment comparison on the classes to obtain $<$.

Here are the current properties of this class order, without an appeal to a general Hartogs construction.

First, $<$ linearly orders $A$, by B.1.5. For a fixed current $a\in A$, choose one code for that class. The members of its field correspond exactly to the proper initial-segment classes below $a$: a field member is sent to the class of its predecessor segment. This is an order isomorphism

$$
A_{<a}\approx\text{the field of that code},
\tag{B.18a}
$$

and the field is a subcarrier of $N$. The correspondence is defined by the unique class of each initial segment, not by a selection of codes for all classes.

The class order is well-founded. Given a current nonempty $Y\subseteq A$, choose one $a\in Y$. If $Y\cap A_{<a}$ is empty, $a$ is its least member. Otherwise (B.18a) transfers that intersection to a nonempty subset of the field of the chosen well-order code, which has a least member. Its class is least in $Y$, since any member of $Y$ outside the segment is at least $a$.

Finally $A\nprecsim N$. If it injected into $N$, transport its current well-order to the image and rigidify the resulting binary code on $N$. Let $a\in A$ be that code's class. Equation (B.18a) would make $A_{<a}$ isomorphic to all of $A$, which is impossible for a well-order. Thus $A$ is uncountable and all its proper initial segments are countable. This proves (B.17).

The well-order transport argument B.1.4 now gives the first clause of (B.18).

For a fixed current $a\in A$, (B.18a) supplies a current injection $A_{<a}\to N$. Rigidifying its graph on the stable product $A\times N$ makes it necessarily an injection of that segment. Restricted Barcan for $A$ yields the second clause of (B.18). Choosing a witness separately for each fixed $a$ in this proof does not assert a simultaneous family of injections.

Finally, binary relations on $N$ are coded by binary reals using $N^2\approx N$. A valid real code for a well-order determines its unique member of $A$; send invalid codes to the zero order type. This is a current total surjection $S_0\twoheadrightarrow A$, proving (B.19).

By B.2.3, Choice indexed by $A$ is now available. Applying it to the nonempty sets of real codes for the members of $A$ gives a section of (B.19), and hence

$$
A\precsim S_0.
\tag{B.20}
$$

Applying it to injections of proper initial segments into $N$ also supplies, when required, a simultaneous current family

$$
e_a:A_{<a}\hookrightarrow N\qquad(a\in A).
\tag{B.21}
$$

The target domains here are stable: real codes lie in $S_0$, and injection graphs are rigid relations on the stable product $A\times N$. No ordering of $S_0$ or its power set has been assumed.

## B.4. Boolean-algebra and modal transfer tools

These tools are shared with the earlier forcing proof. They are included to specify exactly what is transferred, rather than invoke a general forcing truth lemma.

### B.4.1. Regular-open completion

Let $Q$ be a current nonempty partial order. Downward closed subsets are regularized by

$$
j(V)=\{q:\forall r\le q\ \exists s\le r\ (s\in V)\}.
$$

The fixed points, represented rigidly, form the current complete Boolean algebra $\operatorname{RO}(Q)$. Joins are regularized unions; meets of finite families are intersections; the complement of $U$ consists of the conditions having no extension in $U$. These definitions use comprehension and unique rigidification, not Choice.

If $Q_0=Q^\dagger$, then

$$
\operatorname{RO}(Q)\precsim\mathcal P_r(Q_0).
\tag{B.22}
$$

If $S_0\twoheadrightarrow Q_0$, inverse image strengthens this to

$$
\operatorname{RO}(Q)\precsim T.
\tag{B.23}
$$

For both partial-function orders below, every basic cone $[q]$ is regular open, and every nonzero regular open contains a cone. If a condition does not extend $q$, it already conflicts with it or can be extended to disagree on a still-unset coordinate of $q$. This proves regularity of the cone. See draft Lemma 6.1.

When FP supplies an isomorphism $h:B\cong\downarrow p$, its current graph preserves joins and meets that exist, and

$$
h(\neg b)=p\wedge\neg h(b).
\tag{B.24}
$$

Notation $h(b)$ asserts no modal functionality of that current isomorphism.

### B.4.2. Density becomes entailment

If below every nonzero $b\in B$ there is nonzero $c\le b$ with $h(c)\le\varphi$, then $p\le\varphi$. Otherwise the preimage of the nonzero proposition $p\wedge\neg\varphi$ would have a nonzero refinement whose image entails both $\varphi$ and $\neg\varphi$. The same argument works below a fixed nonzero Boolean element. This is draft Lemma 6.2.

### B.4.3. Local selection of a relation

Suppose $\Phi(I)$ is necessarily invariant under current coextension of the relational variable $I$. If

$$
q\le\exists I\,\Phi(I),
$$

there is a current $I_*$ such that $q\le\Phi(I_*)$.

Necessarily some relation satisfies $q\to\Phi$: on $q$ use the hypothesis, and off $q$ use any relation of the inhabited type. Apply IC to obtain a necessarily unique selector $V$ of such relations. Define

$$
I_*(\bar x)=\exists J\,(VJ\land J(\bar x)).
$$

Necessarily this relation is coextensive with the unique selected $J$, so coextension invariance gives the conclusion. This is draft Lemma 6.4. It is used for injection graphs, whose defining formulas are extensional in the graph variable. It is never applied directly to the assertion that the selected relation itself is rigid.

### B.4.4. No new rigid subsets from simultaneous decisions

Suppose $B$ has the following current countable binary decision property: for every current relational sequence $(b_n)_{n\in N}$ and every nonzero $b$, there is nonzero $c\le b$ such that, for every current $n$, either $c\le b_n$ or $c\le\neg b_n$. If $h:B\cong\downarrow p$, then

$$
p\le\forall U\,(SU\leftrightarrow S_0U).
\tag{B.25}
$$

To prove this, fix a current property $X$ and $0\ne q\le p$. Pull back the propositions $p\wedge Xn$ through $h$. Simultaneous decision gives $0\ne r\le q$ deciding every $Xn$. Let $V$ be the unique rigid representative of

$$
\{n\in N:r\le Xn\}.
$$

Positive and negative membership facts of $V$ on stable $N$ persist. Restricted Barcan for $N$ therefore gives

$$
r\le\forall n\in N\,(Xn\leftrightarrow Vn).
\tag{B.26}
$$

Every current member of $S_0$ is necessarily rigid and necessarily included in $N$. Restricted Barcan gives the forward inclusion $S_0\subseteq S$ necessarily.

If the reverse inclusion in (B.25) failed on a nonzero $q\le p$, local selection B.4.3 could be applied to

$$
\Phi(X)=
\exists U\,(\operatorname{Rigid}(U)\land U\subseteq N
\land U\equiv_{\mathrm{ext}}X\land\neg S_0U).
$$

This formula is extensional in $X$. Obtain a current $X$ satisfying it throughout $q$, and apply (B.26) below $q$. Since $q$ entails $X\subseteq N$, the resulting nonzero $r$ entails full coextension $X\equiv_{\mathrm{ext}}V$. Its witness $U$ is rigid and coextensive with rigid $V$, so $U=V$. But $V$ is a current member of rigid $S_0$ and remains one, a contradiction. This proves (B.25); compare draft Lemma 6.8.

## B.5. Positive forcing with real-coded conditions

Let $Q$ be the current partial order of rigid graphs of partial functions

$$
q:A\times N\rightharpoonup 2
$$

whose domains inject into $N$, ordered by extension. Here $2=\{z,\operatorname{Suc}_e z\}$, and the countability condition is current. Let $Q_0=Q^\dagger$. Its current members are rigid relations on a stable finite product, hence necessarily distinct; $Q_0$ is stable.

### B.5.1. Conditions are a quotient of the binary reals

There is a current surjection

$$
S_0\twoheadrightarrow Q_0.
\tag{B.27}
$$

Fix a section assigning a real well-order code to each $a\in A$, supplied by B.3. A condition's domain has an injection into $N$. Its inverse on its image enumerates the coordinate pairs with possible gaps. Record, at each used natural index, the real code of its $A$-coordinate, its natural coordinate, and its bit. A sequence of binary reals and these natural-number data can be coded by one subset of a fixed finite power of $N$, hence by one member of $S_0$.

Conversely, a proposed code has a uniquely determined decoded graph when its rows are valid well-order codes and its assignments are consistent. Its domain is an image of a subcarrier of $N$, and hence injects into $N$ by taking least natural preimages. Rigidify this graph. Send invalid codes to the empty condition. This defines a current total functional decoder, and the preceding paragraph proves its surjectivity.

This proof chooses a domain enumeration separately for a fixed condition only to show that it has a code. It does not choose an enumeration simultaneously for every condition. That distinction is why surjection, rather than injection, is used in (B.27).

By B.4.1,

$$
B_+:=\operatorname{RO}(Q)\precsim T.
\tag{B.28}
$$

FP therefore supplies a current $h_+:B_+\cong\downarrow p_+$, with $p_+\ne\bot$.

### B.5.2. Closure and simultaneous binary decisions

Every current descending $N$-sequence $(q_n)$ has a lower bound. Its graph union is functional. Apply countable Choice from B.2.3 to choose injections

$$
i_n:\operatorname{dom}(q_n)\hookrightarrow N.
$$

Their graphs can be taken in a stable domain of rigid relations on $A\times N\times N$. Send a member $x$ of the union domain to the pair consisting of the least $n$ with $x\in\operatorname{dom}(q_n)$ and $i_n(x)$. This injects the union into $N^2\approx N$, so the union is a condition.

Now fix a current Boolean sequence $(b_n)$ in $B_+$. For every pair $(q,n)$, there is an extension $d\le q$ with

$$
[d]\le b_n\quad\text{or}\quad[d]\le\neg b_n.
\tag{B.29}
$$

If $[q]$ meets $b_n$, take a condition in the intersection; otherwise $[q]\le\neg b_n$.

The stable index $Q_0\times N$ is a surjective image of $S_0$, by (B.27) and ordinary finite coding of binary reals with naturals. Apply B.2.3 to select such a $d$ simultaneously for every $(q,n)$. Relational recursion starting with a prescribed condition gives a descending sequence deciding $b_n$ at step $n$. Its lower bound has a nonzero cone deciding every $b_n$.

Thus $B_+$ has the countable binary decision property. Neither a well-order of $Q_0$ nor Dependent Choice as an extra axiom has been used. The selection relation is obtained from an atomic FP instance before the recursion.

### B.5.3. The row relation

For current $a\in A,n\in N$, let $b_{an}$ be the regular open of conditions assigning $1$ to $(a,n)$. The graph

$$
n\longmapsto h_+(b_{an})
$$

is currently total and functional. B.2.1, applied to stable $N$, supplies a unique row name $X_a$ with

$$
\Box(X_a\subseteq N),\qquad X_a n=h_+(b_{an})
\quad(n\in N\text{ current}).
\tag{B.30}
$$

Uniqueness follows from restricted Barcan for $N$, the necessary support in $N$, and Intensionality. The assignment $a\mapsto X_a$ is a current functional relation, not an assumed function term.

Restrict its graph to the stated domain $A$, and rigidify it to $J^\dagger$. Necessary Distinctness of $A$, current functionality, and necessity of identity give

$$
\Box(a=a'\to X=X')
$$

for any two current pairs. Restricted Barcan over the graph makes it necessarily functional; persistence and restricted Barcan for $A$ make it necessarily total. Its values necessarily are subsets of $N$.

Define

$$
L(a,U)\ \Longleftrightarrow\
Aa\land\operatorname{Rigid}(U)\land
\exists X\,(J^\dagger(a,X)\land U\equiv_{\mathrm{ext}}X).
\tag{B.31}
$$

Necessary RC gives exactly one rigid representative at every possibility. Thus $L$ is necessarily a total functional relation $A\to S$. This is the construction in draft Lemma 8.2.

### B.5.4. Every old real appears in a row

For every current $V\in S_0$,

$$
p_+\le\exists a\in A\,L(a,V).
\tag{B.32}
$$

Below an arbitrary nonzero Boolean element choose a condition $q$. Its used $A$-rows form a countable set: for each used row choose its least natural coordinate, which maps the row into $\operatorname{dom}(q)$. Since $A$ is currently uncountable, some row $a$ is unused. Extend $q$ by assigning the entire $a$-row the characteristic function of $V$. The new graph is a condition, since its domain is the union of two countable sets, explicitly coded in disjoint parts of $N$.

The image of its cone is nonzero. For every current $n$, (B.30) and stability of $V$'s membership facts show that it entails $X_an\leftrightarrow Vn$. Restricted Barcan and necessary inclusion in $N$ give full coextension, hence $L(a,V)$. Density B.4.2 proves (B.32).

Restricted Barcan for rigid $S_0$ makes (B.32) universal over $S_0$ throughout $p_+$. B.4.4 identifies $S_0$ with all of $S$ there. Therefore

$$
p_+\le\text{“$L:A\twoheadrightarrow S$”}.
\tag{B.33}
$$

### B.5.5. The positive cardinal conclusion

Throughout $p_+$, $A$ is well ordered and each proper initial segment injects into $N$, by (B.18). Taking least preimages in (B.33) gives $S\precsim A$.

Cantor's diagonal argument gives $S\nprecsim N$ at every possibility under the background assumptions. An injection $S\to N$ would give a surjection $N\to S$, using the empty subset off the injection's range; rigidify the diagonal subset of $N$ to contradict surjectivity.

Hence $A$ is uncountable throughout $p_+$. Every uncountable subcarrier $Y\subseteq A$ has the same cardinality as $A$. Indeed, compare its inherited well-order with $A$: $Y$ cannot be isomorphic to a proper initial segment of $A$, since those are countable. In either remaining comparison case there is an injection $A\to Y$; inclusion gives the converse injection, so Cantor–Bernstein gives $Y\approx A$. Since $S\precsim A$ is uncountable, $S\approx A$; every subcarrier of $S$ is therefore countable or equinumerous with $S$. Thus

$$
p_+\le C_N,\qquad\Diamond C_N.
\tag{B.34}
$$

This completes the positive application without an inaccessible bound.

## B.6. The negative forcing: first assume current Cardinal CH

If $\neg C_N$ already holds currently, then $\Diamond\neg C_N$ follows by the reflexive modal laws of C. To obtain the other case, assume $C_N$ for the remainder of B.6–B.8.

By (B.20), $A\precsim S$. Its image is uncountable. Cardinal CH applied to that image gives

$$
S\approx A.
\tag{B.35}
$$

Fix a current well-order $W_S$ of $S_0$ transported along such a bijection, and fix the current injections $e_a$ in (B.21). These are legitimate choices of individual witnesses and a family supplied by B.2.3. A well-ordering of $\mathcal P_r(A)$ is not assumed.

Let

$$
X=\mathcal P_r(A),\qquad X_0=X^\dagger.
\tag{B.36}
$$

The domain $X_0$ is stable, by B.1.3. Its current members are the rigid current subsets of $A$. Define

$$
C=\operatorname{Fn}(X_0\times N,2,{<}\omega),
\tag{B.37}
$$

using rigid graphs of finite partial functions and ordering by extension. Let $C_0=C^\dagger$. It is stable, since its current members are rigid relations on a stable finite product. The algebra to be represented is

$$
B_-=\operatorname{RO}(C).
$$

The new task is to prove

$$
B_-\precsim X\approx T.
\tag{B.38}
$$

The second comparison follows from (B.35), by transporting current rigid subproperties along a current bijection and rigidifying their images. The first comparison is the essential-support argument below.

### B.6.1. A fixed linear order on finite conditions

The well-order $<$ on $A$ gives a lexicographic linear order on $X_0$: compare distinct members at the least coordinate of $A$ on which their memberships differ. Such a coordinate exists, since distinct rigid subproperties have distinct current extensions.

This gives a linear order on $X_0\times N$. Represent a finite condition by its finite sequence of coordinate–bit pairs, sorted by that coordinate order, and compare these finite sequences lexicographically, with the usual prefix convention. Fix this linear order of $C_0$.

It need not be a well-order. We will only use it to enumerate finite collections and to rank members of finite antichains.

### B.6.2. Finite incompatibility bounds

A pairwise incompatible family of conditions whose domains all have size at most $n$ has at most $2^n$ members.

For a finite subfamily, let $D$ be the finite union of its domains. If $|D|<n$, its incompatible conditions already have disjoint nonempty sets of extending total assignments on $D$, so their number is at most $2^{|D|}\le2^n$. Otherwise a condition with domain size $m\le n$ is extended by exactly $2^{|D|-m}$ total assignments on $D$, at least $2^{|D|-n}$ assignments. Those sets of assignments are disjoint, so again there can be at most $2^n$ conditions. If the original family had more members, a finite subfamily of size $2^n+1$ would contradict this calculation. This proof uses only finite selection and finite counting.

Consequently, for every current regular open $U$ and every $n$, the collection

$$
U\cap C_{\le n}
$$

has a finite maximal incompatible subfamily $A_n$. If it is nonempty, repeatedly add an incompatible condition whenever possible; the preceding bound proves by finite induction that the process must stop by $2^n$ steps. If it is empty, take the empty family.

### B.6.3. Every regular open has a countable generating family

Fix one current $U$. Apply countable Choice B.2.3 to the nonempty collections of possible $A_n$'s in B.6.2. Their members are taken as rigid finite subproperties of stable $C_0$, so the target of this choice instance is stable.

Let

$$
G=\bigcup_{n\in N}A_n.
$$

This union is countable. The fixed linear order of $C_0$ orders each finite $A_n$, and hence gives a uniform finite enumeration; pairs consisting of $n$ and the finite rank supply a countable enumeration of the union. Least natural preimages remove repetitions if an injection is wanted.

The family $G$ need not be an antichain, and no such assertion is needed. It is predense in $U$. Indeed, if $c\in U$ and $|\operatorname{dom}(c)|=m$, maximality of $A_m$ within $U\cap C_{\le m}$ gives a member of $A_m$ compatible with $c$. Applying the same observation to every extension of $c$ shows that

$$
U=\bigvee_{g\in G}[g]
\tag{B.39}
$$

in the regular-open algebra.

This proves existence of a countable generating family separately for every $U$. We do not choose one simultaneously for all $U$.

### B.6.4. A uniquely defined countable support

For a coordinate $j\in X_0\times N$, let $\pi_j$ flip the bit at $j$, leaving a condition unchanged if $j$ is outside its domain. This is an involutive automorphism of $C$, and hence induces an automorphism of its regular-open algebra.

Define the essential support of $U$ by

$$
E(U)=\{j:\pi_j(U)\ne U\}.
\tag{B.40}
$$

This support is specified uniquely from $U$.

Choose a countable generating family only for the purpose of the following existence proof. The union of its finite domains is countable, using their finite enumerations from the coordinate order. Outside that union, every generator cone is fixed by the flip. Equation (B.39) implies that $U$ is fixed too. Thus $E(U)$ is countable.

Moreover, $U$ depends only on $E(U)$. If $[c]\le U$ and $j\in\operatorname{dom}(c)\setminus E(U)$, then also $[\pi_j(c)]\le U$. In the regular-open algebra,

$$
[c]\vee[\pi_j(c)]=[c\setminus\{j\}].
\tag{B.41}
$$

To see (B.41) directly, deciding the bit at $j$ is dense below the shortened condition. The equality is a regular-open join equality; it is not asserted to be the literal union of the two poset cones.

Delete the finitely many coordinates outside $E(U)$ one at a time. Then

$$
[c\restriction E(U)]\le U.
\tag{B.42}
$$

Thus the cones whose finite domains lie in $E(U)$ and which lie below $U$ determine $U$ completely.

Let

$$
F(U)=\{x\in X_0:\exists n\in N\ (x,n)\in E(U)\}.
\tag{B.43}
$$

It is countable. For example, select the least natural coordinate at which a given $x$ occurs to inject it into $E(U)$. A code for $U$ using coordinates from $F(U)\times N$ is sufficient, even if this product contains inessential coordinates.

### B.6.5. Canonical natural labels for countable families of subsets of $A$

The next lemma is what avoids a choice of a countable support enumeration for every $U$.

**Labeling lemma.** Relative to the fixed current well-order $W_S$ of $S_0$ and the fixed family $(e_a)_{a\in A}$, every current countable subcarrier $F\subseteq X_0$ has a uniquely specified injection

$$
\ell_F:F\hookrightarrow N.
\tag{B.44}
$$

The assignment is definable by a current relation with $F$ as a parameter.

**Proof.** For distinct $x,y\in F$, let $d(x,y)$ be their least differing $A$-coordinate. The set of these coordinates is countable. To prove this, temporarily use an injection $F\to N$; its square codes the pairs by $N$, and least natural preimages inject the image of $d$ into $N$. No such injection is selected uniformly over all $F$.

A countable subset of the current $\omega_1$ is bounded. Here that fact is justified by the available countable Choice, or directly by the fixed family (B.21): a countable cofinal collection of initial segments, with their chosen injections into $N$, would make their union $A$ countable. Thus there is $\beta\in A$ such that restriction to $A_{<\beta}$ distinguishes all members of $F$.

Take the least such $\beta$ in $A$. For a family of size at most one, the zero segment may be used. For $x\in F$, code its restriction to $A_{<\beta}$ by

$$
r_\beta(x)=
\{e_\beta(a):a<\beta\text{ and }x(a)\},
\tag{B.45}
$$

taking the unique rigid representative of this subset of $N$. This is a member of $S_0$ currently. By the defining property of $\beta$, (B.45) is injective on $F$.

Pull back $W_S$ along (B.45). This gives a uniquely specified well-order of $F$. Since $F$ is countable, its order type is some unique $\theta\in A$; the unique order isomorphism

$$
\operatorname{rank}_F:F\longrightarrow A_{<\theta}
$$

is supplied by current well-order comparison. Existence can be proved by transporting this countable well-order to a subcarrier of $N$; its isomorphism class in $A$ and the resulting rank map are independent of that temporary transport.

Set

$$
\ell_F=e_\theta\circ\operatorname{rank}_F.
\tag{B.46}
$$

This is the required injection. All the defining objects are unique relative to $F,W_S,(e_a)$. The empty family has the empty label relation. Consequently comprehension defines one relation $\operatorname{Label}(F,x,n)$ expressing (B.46) for every countable $F$; no function choosing arbitrary enumerations has been introduced. $\square$

An enumeration, if desired, is obtained by increasing natural labels. It may have gaps. The following coding keeps the domain of the labels explicitly, so it does not confuse a missing entry with an entry equal to the empty subset of $A$.

### B.6.6. Coding every regular open by a single subset of $A$

For $U\in B_-$, apply B.6.5 to $F(U)$. Define

$$
D_U=\{\ell_{F(U)}(x):x\in F(U)\}\subseteq N,
\tag{B.47}
$$
$$
M_U=
\{(a,n)\in A\times N:
 \exists x\in F(U)\,[\ell_{F(U)}(x)=n\land x(a)]\}.
\tag{B.48}
$$

Thus $M_U$, together with $D_U$, records the labeled family of subsets of $A$. Every label has exactly one member of $X_0$, determined by its column and uniqueness of rigid representatives.

Finite partial functions $N\times N\rightharpoonup2$ have fixed natural-number codes. Let $H_U\subseteq N$ consist of the codes of those finite conditions whose first coordinates lie in $D_U$ and whose translations along the labeled family have cones below $U$. Invalid codes are excluded. The translated conditions have domains in $F(U)\times N$.

The triple

$$
(M_U,D_U,H_U)
\tag{B.49}
$$

determines $U$. It first recovers the labeled coordinate family from $M_U,D_U$. Then $H_U$ identifies all the cones on those coordinates lying below $U$. By (B.42), these cones determine every member of $U$.

Current cardinal arithmetic for the well-ordered infinite carrier $A$ gives a fixed injection

$$
(A\times N)\ \sqcup\ (N\times\{0,1\})
\hookrightarrow A.
\tag{B.50}
$$

For an explicit injection, in countable-order-type notation send $(a,n)$ to $\omega\cdot(a+1)+n$. The corresponding ordered product and finite addition are countable, so determine a unique member of $A$; distinct pairs have distinct outputs. These outputs are infinite order types. Use the finite order types $2n$ and $2n+1$ for the two remaining tags. This also proves the needed injection $A\times N\to A$; the converse injection is immediate, so $A\times N\approx A$ by Cantor–Bernstein. All constructions use countable order codes and relational comparison, not Choice for arbitrary sets. Use the tags in (B.50) to encode (B.49) by one subset of $A$, and take its unique rigid representative. Since (B.49) determines $U$, the resulting graph is a current injection

$$
B_-\hookrightarrow\mathcal P_r(A)=X.
\tag{B.51}
$$

Everything in this encoding is specified uniquely from $U$ and the fixed parameters. The countable generating families from B.6.3 were used only to prove that $F(U)$ is countable. They are not part of the code and are not chosen uniformly in $U$.

Combining (B.51) and (B.35) proves (B.38). FP supplies

$$
h_-:B_-\cong\downarrow p_-,
\qquad p_-\ne\bot.
\tag{B.52}
$$

### B.6.7. Uniform CCC

The completion $B_-$ has a uniform current injection of each antichain of nonzero elements into $N$.

For nonzero $U$, $H_U$ is nonempty: any cone below $U$ can be shortened to its essential support by (B.42), and then expressed in the labeled coordinates. Take the least natural code in $H_U$, and let $c_U$ be its translated condition. This defines $c_U$ uniquely for every nonzero $U$, with

$$
[c_U]\le U.
\tag{B.53}
$$

Let $Z$ be a current Boolean antichain. Its selected conditions $c_U$, $U\in Z$, are pairwise incompatible. For each $m$, the members with $|\operatorname{dom}(c_U)|=m$ form a collection of size at most $2^m$, by B.6.2.

Rank this finite collection of selected conditions using the fixed linear order of $C_0$. Send $U$ to the pair consisting of $m$ and its finite rank. Pair coding gives an injection into $N$.

This construction is uniform in $Z$. In particular, if a current parameter $y$ defines a family of antichains $Z_y$, one and the same formula gives the injections of their members into $N$. No family of arbitrary choices is made here. This is the uniformity needed in the two counting arguments below.

## B.7. Direct modal transfer for the negative forcing

The transfer follows the pattern of draft Section 7, but uses $X=\mathcal P_r(A)$ as the full coordinate index and a copy of $A$ as the intermediate index. The final contradiction is Cantor's theorem, rather than a comparison of the first and second Hartogs cardinals.

For $x\in X_0$ and $n\in N$, let $b_{xn}$ be the regular open of conditions assigning $1$ at $(x,n)$. For each fixed current $x$, B.2.1 gives a unique current name $Z_x$ with

$$
\Box(Z_x\subseteq N),\qquad
Z_x n=h_-(b_{xn})\quad(n\in N\text{ current}).
\tag{B.54}
$$

Again this is a current functional naming graph, not an assumed function term.

### B.7.1. Separation of different rows

For distinct current $x,x'\in X_0$,

$$
p_-\le\neg(Z_x\equiv_{\mathrm{ext}}Z_{x'}).
\tag{B.55}
$$

Below any nonzero Boolean element, choose a condition $c$. There is a natural $n$ unused in both its $x$- and $x'$-rows, because its domain is finite. Extend it to assign $1$ at $(x,n)$ and $0$ at $(x',n)$. The image of the new cone is nonzero and entails

$$
Z_xn\land\neg Z_{x'}n
$$

by the propositional identities (B.54). Density B.4.2 gives (B.55). In particular, distinct current indices have distinct current names: identical names would be necessarily coextensive.

Embed $A$ into $X_0$ by its singleton subsets. Let $D$ be the rigidification of the current collection of all names in (B.54), and $E$ the rigidification of the current collection of names at these singleton indices. Current unique naming and (B.55) give

$$
D\approx X,\qquad E\approx A.
\tag{B.56}
$$

Transport a current well-order of $A$ to $E$. No current well-order of $D$ is required. Neither $D$ nor $E$ is asserted to satisfy Necessary Distinctness outside $p_-$.

Their members necessarily are subsets of $N$: this holds of every current name by (B.54), and restricted Barcan applies to the rigid collections. Define

$$
G(U)\ \Longleftrightarrow\
\operatorname{Rigid}(U)\land U\subseteq N
\land\exists Z\in E\,(U\equiv_{\mathrm{ext}}Z).
\tag{B.57}
$$

Thus $G\subseteq S$. At every possibility, each member of $E$ has a unique rigid representative of its extension, by necessary RC. Definition (B.57) uses the fixed rigid collection $E$, not the condition of being an index in the current naming graph re-evaluated at another possibility.

### B.7.2. A current counting lemma

Suppose $J\subseteq U\times V$ is current and serial, $V$ is currently well ordered, and a specified current relation injects every fibre

$$
\{u\in U:J(u,v)\}
$$

into $N$, uniformly in $v$. Then

$$
U\precsim V\times N.
\tag{B.58}
$$

Send $u$ to its least $J$-related $v$, paired with its code in that fibre. This is a uniquely specified relation and is injective. There is no simultaneous selection of a fibre injection, since those injections are already supplied uniformly. This is draft Lemma 6.5.

### B.7.3. The intermediate collection is uncountable

$$
p_-\le\neg(G\precsim N).
\tag{B.59}
$$

Suppose otherwise, and let

$$
q=p_-\land\exists I\,\operatorname{Inj}(I;G,N)
$$

be nonzero. The injection property is extensional in its graph variable. Local selection B.4.3 gives a current $I$ such that

$$
q\le\operatorname{Inj}(I;G,N).
\tag{B.60}
$$

For current $Z\in E$ and $n\in N$, define

$$
d_{Zn}
=q\land\exists U\,
 \bigl(GU\land U\equiv_{\mathrm{ext}}Z\land I(U,n)\bigr),
\tag{B.61}
$$
$$
J(Z,n)\ \Longleftrightarrow\ d_{Zn}\ne\bot.
$$

For each current $Z$, throughout $q$ its rigid extension is in $G$ and has an $I$-image in $N$. Since $q$ is possible, restricted Barcan for $N$ gives a current $n$ with $d_{Zn}\ne\bot$. Hence $J$ is current and serial from $E$ to $N$.

For a fixed current $n$, the nonzero $d_{Zn}$'s are pairwise incompatible. If two for distinct current $Z,Z'\in E$ held together, (B.60) would identify their rigid representatives. This would give $Z\equiv_{\mathrm{ext}}Z'$, contradicting separation (B.55) on $p_-$.

Pull the nonzero $d_{Zn}$'s back through $h_-$. They form an antichain in $B_-$, and their indexing by the corresponding $Z$'s is injective. Uniform CCC, B.6.7, gives an injection of each $J(-,n)$-fibre into $N$, uniformly in $n$. Apply (B.58) with the usual well-order of $N$:

$$
E\precsim N\times N\approx N.
$$

This contradicts $E\approx A$ and current uncountability of $A$, proving (B.59).

### B.7.4. The continuum cannot inject into the intermediate collection

$$
p_-\le\neg(S\precsim G).
\tag{B.62}
$$

Suppose the contrary possibility is nonzero, and use B.4.3 to obtain a current graph $I$ and $0\ne q\le p_-$ with

$$
q\le\operatorname{Inj}(I;S,G).
\tag{B.63}
$$

For current $Z\in D$, $W\in E$, put

$$
\begin{split}
d_{ZW}=q\land\exists U,V\,
\bigl(&SU\land GV
\land U\equiv_{\mathrm{ext}}Z\\
&\land V\equiv_{\mathrm{ext}}W
\land I(U,V)\bigr),
\end{split}
\tag{B.64}
$$
$$
J(Z,W)\ \Longleftrightarrow\ d_{ZW}\ne\bot.
$$

Throughout $q$, the rigid extension of each current $Z\in D$ belongs to $S$. Its $I$-image is in $G$, so (B.57) supplies some member of $E$ with that extension. Possibility and restricted Barcan for rigid $E$ give a current such $W$ with $d_{ZW}\ne\bot$. Thus $J$ is serial from $D$ to $E$.

For fixed current $W$, the nonzero $d_{ZW}$'s are pairwise incompatible. Two simultaneous output witnesses are rigid and coextensive with $W$, so unique rigid representation identifies them. Injectivity in (B.63) then identifies the input representatives, making the corresponding distinct names coextensive, contrary to (B.55).

Pullbacks through $h_-$ form antichains. Uniform CCC injects each $J(-,W)$-fibre into $N$, uniformly in $W$. The current well-order of $E$ and (B.58) give

$$
D\precsim E\times N\approx A\times N\approx A.
$$

By (B.56), this is an injection $\mathcal P_r(A)\to A$. Cantor's diagonal argument, with rigid representatives, rules it out. This proves (B.62).

### B.7.5. The negative cardinal conclusion

Throughout $p_-$, $G\subseteq S$, $G\nprecsim N$, and $S\nprecsim G$. If $C_N$ held there, applying it to $G$ would give $G\approx S$, hence $S\precsim G$, a contradiction. Therefore

$$
p_-\le\neg C_N,\qquad\Diamond\neg C_N.
\tag{B.65}
$$

This concludes the case where $C_N$ holds currently.

## B.8. Completion of the bounded theorem and the exact dependencies

The positive argument B.5 always gives $\Diamond C_N$. If $\neg C_N$ holds currently, reflexivity gives $\Diamond\neg C_N$. If $C_N$ holds currently, B.6–B.7 give $\Diamond\neg C_N$. Classical case analysis proves (B.5).

The theorem directly produces the two cardinal possibilities under the stated assumptions; its proof does not assume NC-CH. Through a separately proved necessary real/cardinal comparison and necessary real-structure existence, it yields the corresponding structural possibilities. Those bridge results have not been used anywhere in B.1–B.8.

### B.8.1. Where each assumption is used

| Ingredient | Uses in this proof |
|---|---|
| Necessary RC | Unique rigid representatives at the current point and throughout the represented intervals; restricted Barcan for rigid carriers; stable coding domains; replacement of names by rigid extensions; diagonal arguments. |
| Necessary Peano conditions and rigidity of $N$ | Stable necessarily distinct naturals, finite and countable coding, recursion, fresh natural coordinates, and the stable countable-order construction. |
| Current IC | Atomic choice B.2.2; local selection B.4.3 for extensional graph formulas. No boxed IC instance is used. |
| Atomic FP instances within $T$ | Choice indexed by $N$, $A$, and the stable quotient $Q_0\times N$, with the required stable target domains. These replace the inaccessible proof's available well-orderings. |
| The positive non-atomic FP instance | $\operatorname{RO}(Q)$, covered because conditions are a surjective image of $S_0$. |
| The negative non-atomic FP instance | $\operatorname{RO}(\operatorname{Fn}(\mathcal P_r(A)\times N,2,{<}\omega))$, covered by canonical essential-support coding in the current-$C_N$ case. |
| Current $C_N$, only in the negative case | Converts $A\precsim S$ into $S\approx A$, supplying the fixed well-order of the binary reals and identifying $\mathcal P_r(A)$ with the bound $T$. |
| Current well-ordered cardinal arithmetic | $N^2\approx N$, $A\times N\approx A$, and coding finitely many tagged countable data sets into $A$. No arithmetic for arbitrary non-well-orderable cardinals is assumed. |

### B.8.2. What has not been assumed

No ordinary global Choice principle, well-ordering of an arbitrary power set, inaccessible carrier, necessary FP, or necessary IC is assumed. No general Boolean-valued forcing theorem is invoked. The represented Boolean algebras are used directly through their full principal entailment intervals.

Every use of ordinary selection has a specific source:

- Selecting one witness while proving a fixed existential statement is ordinary existential reasoning.
- Simultaneous selections over $N$, $A$, and a real-coded quotient use B.2.3.
- Least choices use an explicitly supplied well-order.
- Choices from finite sets use finite induction.
- The labels and encodings in B.6 are unique definitions relative to fixed parameters; they do not choose arbitrary representatives from a family indexed by $B_-$.

No current isomorphism supplied by FP is silently assumed necessarily functional. Propositional identities such as (B.30) and (B.54), restricted Barcan, and the separately rigidified name graphs perform the modal work.

### B.8.3. Relation to Bacon's forcing argument

The shared machinery is Bacon's general forcing draft: rigid representatives and arithmetic in Section 2; well-order comparison used in Section 3; stable countable order types in Section 5; Boolean completion, naming and local selection in Section 6; and the two direct transfer arguments in Sections 7–8. Section B.3 gives the required countable class-order construction directly, so the general typed Hartogs construction is not an additional dependency of this part.

The new work in this part is:

1. The generalized atomic-interval choice argument B.2.
2. Using quotient real codes to obtain the positive completion bound and the required simultaneous choices, B.5.1–B.5.2.
3. Replacing the double-Hartogs Cohen index by a power-set index, and coding its completion by canonical countable essential supports under current Cardinal CH, B.6.
4. The resulting Cantor-based negative counting argument and the finite-bound theorem.

---

# Part III. From weak non-injection to the required size bound

Assume
$$
\Gamma=C+\Box RC+IC+FP_<+\Box\operatorname{Peano}(N),
\qquad S=\mathcal P_r(N),\quad T=\mathcal P_r(S),\quad
W:\neg(\Pi\precsim T).
$$
Here the arithmetic carrier is the definitional one from Part I. All maps below are current relational graphs at fixed finite types. The aim is to prove $T\precsim\Pi$ from this package, which makes the comparison strict and allows Part II to apply.

## C.1. The current propositional algebra is complete

Classicism makes propositions, with the entailment order, a Boolean algebra. Rigid Comprehension supplies its current completeness.

Given any current property `F` of propositions, take its unique rigid current representative `F†` and set

$$
j_F=\exists p\,(F^\dagger p\land p).
$$

For each current member `p` of `F†`, persistence of that membership gives `p ≤ j_F`. If `q` is a current upper bound, then every current `F†`-member satisfies `□(p → q)`. Restricted Barcan for the rigid carrier `F†` gives

$$
\Box\forall p\,(F^\dagger p\to(p\to q)),
$$

and hence `j_F ≤ q`. Thus `j_F` is the least upper bound of the current `F`-members. Necessary Distinctness of propositions is not used. This establishes the current `CBA(Π,≤)` needed for the next step.

## C.2. Original FP makes propositions Dedekind-infinite

Suppose `Fin(Π)`, where `Fin` is the map's Dedekind-finiteness condition: every current injective self-map is surjective. Apply the finite alternative of original FP to the complete Boolean algebra `Π` itself. It supplies a current relational isomorphism

$$
h:\Pi\longrightarrow[\bot,p],\qquad p\ne\top.
$$

Regarded as a self-map of `Π`, this is injective and omits `⊤`: membership of `⊤` in the interval would imply `⊤ ≤ p`, hence `p = ⊤`. This contradicts `Fin(Π)`.

Consequently there are a current injective self-map `f` of `Π` and a proposition `b` outside its range. Choose these two witnesses once. Current relational recursion on the Peano carrier gives

$$
b_0=b,\qquad b_{n+1}=f(b_n).
$$

The `b_n` are pairwise distinct. An equality with indices `n < m` could be cancelled through the injective map `f`, putting `b` in the range of `f`. Thus

$$
N\precsim\Pi.
$$

This is a witnessed Dedekind-infinitude argument. It does not use the generally invalid choiceless inference from mere infinitude to the existence of a countable subset. Recursion here is current recursion for relations; its target need not be stable.

## C.3. An enumerated infinite Boolean family yields a disjoint sequence without Choice

The following lemma is sufficient.

**Lemma.** If a Boolean algebra has a specified sequence of pairwise distinct elements, it has a specified countable sequence of pairwise disjoint nonzero elements. No Choice principle is needed.

**Proof.** Given the distinct `b_n`, for each finite binary word `s` form

$$
a_s=\bigwedge_{i<|s|}b_i^{s(i)},
$$

where `b_i^1 = b_i` and `b_i^0 = ¬b_i`. Retain exactly the words with `a_s ≠ 0`. This is a finitely branching tree of finite binary words. Its nodes at level `n` are the atoms of the finite Boolean algebra generated by the first `n` values of the sequence. The two children of a node have disjoint values whose join is the value of that node; at least one child is retained.

There are infinitely many splitting nodes. Otherwise, beyond the largest level containing a split, all these finite generated algebras would have the same finite partition into atoms. Every `b_n` would then belong to one fixed finite Boolean algebra, contradicting pairwise distinctness.

Call a node productive when it has infinitely many splitting descendants. The root is productive. A productive node has a productive child: if both child subtrees contained only finitely many splits, so would their union. Choose its `0` child when that child is productive, and its `1` child otherwise. This rule is unique, so relational recursion defines an infinite branch of productive nodes without dependent choice.

That branch contains infinitely many splitting nodes. More explicitly, from any productive node take the least distance to a splitting descendant. Until that descendant, every node has only one retained child, so the recursively selected branch must reach a split. Enumerate the branch's splitting levels by repeated least-natural-number selection.

At each such level, take the Boolean value of the child not followed by the branch. It is nonzero. At every later splitting level, the sibling value lies below the previously followed child and is therefore disjoint from the earlier sibling value. This gives the required sequence `d_n`. All selections in the construction are unique choices from a two-element list or least choices in `N`. ∎

The lemma applies to the current Boolean algebra `Π`. No assertion of necessary distinctness of the `b_n` or `d_n` is needed.

## C.4. Completeness now embeds the first rigid powerset into propositions

For `U ∈ S`, let

$$
e(U)=\bigvee\{d_n:n\in N\text{ and }Un\}.
$$

This defines a current relational graph: the displayed current collection exists by comprehension, and its least upper bound is unique. Unique definition of the value is not an application of ordinary Choice.

If `U ≠ V`, uniqueness of rigid representatives gives a current natural number in their symmetric difference. Suppose `k ∈ U \ V`. Then `d_k ≤ e(U)`, while `d_k ∧ e(V) = 0`, since `d_k` is disjoint from every generator used in the latter join. The latter inference is the ordinary complete-Boolean-algebra law that a fixed meet distributes over an arbitrary join; equivalently, `¬d_k` is an upper bound for all those generators. As `d_k ≠ 0`, the two joins differ. Hence

$$
e:S\hookrightarrow\Pi.
$$

There is also a current injection `S → T`, sending each member of `S` to the unique rigid representative of its singleton within `S`. Consequently `W` implies `¬(Π ≼ S)`. Combining these facts gives

$$
\boxed{S\prec\Pi.}
$$

The weak premise has supplied a genuine strict size bound, but at the first powerset level only.

## C.5. Every complete Boolean algebra bounded by `S` is covered

If `B ≼ S`, compose with `S ≼ Π`. An injection `Π → B` would compose with `B → S → T`, contradicting `W`. Thus `B ≺ Π`, and original FP applies.

In particular it applies to:

- the complete atomic Boolean algebra `S = P_r(N)`;
- the completion of Cohen forcing on a countable fixed condition set, which injects directly into `P_r(N)` by its current membership code;
- any other complete Boolean algebra for which a current injection into `S` has actually been constructed.

A real-coded condition set alone is insufficient for the last clause. It bounds its regular-open completion by `T`, and a surjection from real codes onto the completion does not by itself provide the required injection back into `S`.

## C.6. Countable Choice follows from the atomic instance

The atomic-choice argument B.2.2 requires only representation of `P_r(I)` for its chosen stable index `I`; its reference to the uniform bound `T` was solely a way to obtain that representation.

Take `I = N`. The preceding section already supplies the exact required representation of `P_r(N)`, whose singleton images are nonzero propositional atoms. Intensional Choice and restricted Barcan therefore yield a current choice graph for every current serial relation

$$
R\subseteq N\times Y
$$

with `Y` stable. The target may be arbitrarily large; the Boolean-algebra size bound concerns `P_r(N)`, not the target.

This derives ordinary countable relational Choice before either `T ≼ Π` or a well-order of `S` has been proved. At this stage it does not supply Choice indexed by `S`, or by the countable-order-type carrier `A`, merely from a surjection `S ↠ A`. Section C.8 later obtains the required coverage of `P_r(A)` by a separate diagonal construction and then derives Choice indexed by `A`.

## C.7. A canonical choice-free bound for the coding completions

The completion bound below is uniform in the coded real set and uses no well-order of the continuum. It is the input needed for the diagonal argument in C.8.

### C.7.1. Statement and conventions

Work in the current mathematics of Classicism with Rigid Comprehension and the necessarily Peano, stable natural-number carrier $N$ used in this note. Put
$$
S=\mathcal P_r(N),\qquad S_0=S^\dagger.
$$
Thus $S_0$ is the stable collection of the current rigid binary reals. All orders, completions, codes, and cardinal comparisons in this lemma are **current**. No well-order of $S$, ordinary Choice, Intensional Choice, or FP is used to prove the lemma.

Fix the usual arithmetic coding of finite binary words by members of $N$. For $x\in S_0$, let
$$
D_x=\{\operatorname{code}(x\mathbin{\upharpoonright}m):m\in N\}.
\tag{C.7.1}
$$
These are infinite subsets of $N$. Distinct binary reals have only finitely many common initial segments, so $D_x\cap D_y$ is finite for $x\ne y$. For each fixed $n\in N$, the predicate $n\in D_x$ depends on only a finite initial segment of $x$: decode $n$ as a finite word $w_n$, and test whether $w_n$ is an initial segment of $x$. Invalid codes, if the chosen coding has any, simply give the constantly false predicate.

Let $R$ be any current subcollection of $S_0$; in the intended application it is a rigid representative of a current subset. Define $P_R$ as follows. A condition is
$$
q=(s,F),
$$
where $s$ is a finite binary word and $F$ is a finite subcollection of $R$. Here finite means equinumerous with a finite initial segment of $N$. Its subcollections are represented by their unique rigid current representatives. Put
$$
(t,G)\le(s,F)
$$
when $s$ is an initial segment of $t$, $F\subseteq G$, and every newly specified 1-position avoids the protected sets:
$$
\forall n\bigl[|s|\le n<|t|\ \land\ t(n)=1
 \ \longrightarrow\ n\notin\bigcup_{x\in F}D_x\bigr].
\tag{C.7.2}
$$

**Lemma.** There is a canonical current relational injection
$$
\operatorname{RO}(P_R)\hookrightarrow S.
\tag{C.7.3}
$$
The construction is uniform in the parameter $R$. In particular, its proof does not select a generator, a maximal antichain, or a real code from an arbitrary equivalence class.

### C.7.2. The finite compatibility test

For $p=(s,F)$ and $q=(t,G)$, incompatible stems make the conditions incompatible. If $s\subseteq t$, then
$$
p\text{ is compatible with }q
\quad\Longleftrightarrow\quad
\forall n\in[|s|,|t|)\,
\bigl[t(n)=1\longrightarrow n\notin\bigcup_{x\in F}D_x\bigr].
\tag{C.7.4}
$$
Necessity follows because any common extension must already extend $s$ through the 1-positions specified by $t$. For sufficiency, $(t,F\cup G)$ is a common extension. The case $t\subseteq s$ is symmetric. Equal stems are always compatible, independently of the finite side conditions.

Fix a condition $q=(t,G)$, a stem $s$, and a natural number $k$. Parametrize conditions with that stem and with a side condition given by a $k$-tuple by
$$
(x_0,\ldots,x_{k-1})\longmapsto
\bigl(s,\{x_0,\ldots,x_{k-1}\}\bigr),
\qquad x_i\in R.
\tag{C.7.5}
$$
Repetitions in the tuple are allowed. This is useful: there is no need to choose an enumeration consistently for all finite side conditions.

Compatibility with $q$, on this slice, is a clopen condition on the tuple of binary reals. Concretely:

- For incompatible stems it is constantly false.
- If $t\subseteq s$, it depends only on $s,t,G$, so is constant as a function of the tuple.
- If $s\subseteq t$, (C.7.4) is a finite conjunction of tests $n\notin D_{x_i}$. Each such test is decided by a finite prefix of $x_i$, by (C.7.1).

We need only the following consequence, stated without topological terminology:

> If a condition represented by a tuple in (C.7.5) is compatible with the fixed $q$, there are finite binary prefixes $w_i\subseteq x_i$, for $i<k$, such that every tuple $(y_i)_{i<k}$ from $R$ extending those prefixes represents a condition with stem $s$ compatible with $q$.

One can take every $w_i$ to have a common length large enough to decide membership in all the finitely many $D_{x_i}$-coordinates tested in (C.7.4). The maximum of those finitely many required word lengths is a uniquely defined natural number. If there are no tests, the empty prefixes suffice. This construction uses no choice principle.

### C.7.3. The code

For a current regular open $U\subseteq P_R$, define a subset $C_U$ of the natural-number codes of triples
$$
(s,k,(w_0,\ldots,w_{k-1}))
$$
by putting the triple in $C_U$ exactly when
$$
\exists x_0,\ldots,x_{k-1}\in R\;
\left[
 \bigwedge_{i<k}w_i\subseteq x_i
 \ \land
 \bigl(s,\{x_0,\ldots,x_{k-1}\}\bigr)\in U
\right].
\tag{C.7.6}
$$
Take the unique rigid current representative of this subset of $N$. It is an element of $S$, and the rule $U\mapsto C_U$ defines a current relational map by comprehension and uniqueness.

For intuition, fix $s$ and $k$. The corresponding portion of $C_U$ records exactly the basic clopen boxes meeting
$$
\{(x_i)_{i<k}\in R^k:
       (s,\{x_i:i<k\})\in U\}.
$$
It is therefore a code for the closure of this slice in the finite power of binary-real space. The actual definition (C.7.6) is enough for the proof; no topological representation theorem or choice of a dense subset is used.

### C.7.4. Injectivity

Suppose $C_U=C_V$, and assume for a contradiction that there is $p\in U\setminus V$. Write $p=(s,F)$. Because $V$ is regular open, there is an extension $q\le p$ whose cone misses $V$:
$$
\forall r\le q\;(r\notin V).
\tag{C.7.7}
$$
Indeed, for a downward closed set $V$, regularization is
$$
j(V)=\{p:\forall q\le p\ \exists r\le q\;(r\in V)\};
$$
since $V=j(V)$ and $p\notin V$, (C.7.7) follows by classical logic. Downward closure then implies that $q$ is incompatible with every member of $V$: a common extension would itself belong to $V$, contrary to (C.7.7).

Choose one finite enumeration $(x_i)_{i<k}$ of $F$. Such an enumeration exists by the definition of finiteness; choosing this one witness inside a proof is not simultaneous choice for a family. As $q\le p$, the tuple represents a condition compatible with $q$. By the finite compatibility test, choose the prefixes $(w_i)_{i<k}$ that preserve this compatibility.

The triple $(s,k,(w_i)_{i<k})$ belongs to $C_U$, witnessed by the tuple $(x_i)$ and $p\in U$. Equality of the two codes puts the same triple in $C_V$. By (C.7.6), there is a tuple $(y_i)_{i<k}$ from $R$, extending those prefixes, for which
$$
r=\bigl(s,\{y_i:i<k\}\bigr)\in V.
$$
The prefixes ensure that $r$ is compatible with $q$, contradicting (C.7.7). Thus $U\subseteq V$. The same argument with the variables interchanged gives $V\subseteq U$.

The Boolean-algebra carrier consists of rigid current representatives of regular opens, so equal current extensions imply identity. Therefore $U=V$, proving (C.7.3). $\square$

### C.7.5. Fixed types and rigid representatives

The variable-length tuple notation in (C.7.6) does not require variable simple types or quantification over types. A finite list of binary reals is represented at a fixed type by a rigid binary relation on $N^2$, together with its length $k$. Its $i$-th row, for $i<k$, has a unique rigid representative in $S_0$. Pairing $N^2\approx N$ codes the matrix by one binary real. A finite list of finite binary prefixes is coded arithmetically by one member of $N$. Consequently the triples used in (C.7.6) have a fixed natural-number coding, and (C.7.6) is an ordinary formula with only the fixed relation types already available in the note.

Finite side conditions can likewise be treated at the fixed type of rigid subproperties of $S_0$. The assertion that they have an enumeration of length $k$ is relational. Alternatively, the canonical lexicographic linear order on binary reals sorts each finite side condition uniquely; finite sorting needs no well-order of the whole real carrier. This also gives the separate, choice-free bound $P_R\precsim S$, although that bound alone would not prove (C.7.3).

The coding map is a **current** map. It is not claimed to be a necessarily injective map between all possible completions or all possible reals. Current RC is used for unique rigid representatives of code sets and regular opens. The stable arithmetic carrier and its coding operations supply the finite combinatorics. No assertion of necessary current well-orderability is made.

The next section uses the current complete-algebra coding pattern directly. Its first use of a modal representation is the application of original FP to the resulting algebras.

### C.7.6. Regularized cones

The raw cones of $P_R$ need not be regular open. For example, a protected coordinate can force a bit to be zero before that bit appears in the stem. Throughout the Boolean completion use
$$
b_q=j(\downarrow q),
$$
not an unsupported identification of $\downarrow q$ with a Boolean element. These regularized cones are nonzero, form a dense family, and preserve compatibility and incompatibility. If $q\in U$ and $U$ is regular open, then $b_q\subseteq U$. The proof of injectivity above uses only the regular-open definition, so it does not presuppose raw-cone regularity or separativity of the presented order.

## C.8. Well-ordered quotient choice

The canonical completion bound, the first-powerset bootstrap and the atomic-choice lemma together supply the ordinal-indexed choice used in C.9. No current well-order of the reals is assumed.

### C.8.1. Assumptions and statement

Assume the weak package of this part: Classicism, necessary Rigid Comprehension, unboxed Intensional Choice, the stable necessarily Peano carrier `N`, original proper-interval Forcing Possibilism, and
$$
 W:\qquad \neg(\Pi\precsim T).
$$
Write
$$
 S=\mathcal P_r(N),\qquad S_0=S^\dagger,
 \qquad T=\mathcal P_r(S).
$$
The bootstrap gives
$$
 S\prec\Pi,
\tag{C.8.1}
$$
so FP represents every current complete Boolean algebra whose carrier injects into `S`.

Let `(A,<)` be the stable carrier of current countable order types constructed in Section B.3. Only the part of that construction preceding its appeal to Choice indexed by `A` is used initially. In particular,
$$
 \operatorname{WO}(A,<),\qquad A\nprecsim N,
 \qquad d:S_0\twoheadrightarrow A
\tag{C.8.2}
$$
are already available. The map `d` sends a real coding a well-order on a subcarrier of `N` to its order-type class and sends invalid codes to the zero class. No section of `d` is assumed.

**Proposition.** Under this package there is a current family
$$
 (q_a)_{a\in A}
$$
of pairwise disjoint nonzero propositions. Consequently:

1. `P_r(A) ≺ Π`;
2. ordinary relational Choice indexed by `A` holds for every stable target;
3. `A ≼ S`.

The construction of the antichain uses (C.8.1), but no current well-order of `S`, no section of `d`, and no simultaneous choice of representations supplied by FP.

### C.8.2. Uniform almost-disjoint coding algebras

Fix the arithmetic coding of finite binary words. For each old real `x∈S_0`, let
$$
 D_x=\{\operatorname{code}(x\restriction m):m\in N\}.
$$
This is the fixed infinite almost-disjoint family of C.7. For each current rigid `R⊆S_0`, let `P_R` be the almost-disjoint coding order and let
$$
 B_R=\operatorname{RO}(P_R).
$$
All these orders and Boolean algebras can be presented at fixed relational types, uniformly in `R`: conditions consist of a natural-number stem code and a rigid finite subproperty of `S_0`; regular opens are rigid predicates on that fixed ambient condition type. The parameter `R` changes the defining carrier predicate, not its type.

The canonical prefix-box construction supplies a **uniform current injection**
$$
 c_R:B_R\hookrightarrow S_0.
\tag{C.8.3}
$$
Here one may use `S_0` as codomain because it has exactly the current members of `S`. Uniformity means that a single current formula with parameter `R` defines the graph; it does not mean that one is selecting an injection for each `R`.

For later use, define a total current decoder
$$
 \delta_R:S_0\longrightarrow B_R
$$
by sending a real in the image of `c_R` to its unique preimage and every other real to `0_{B_R}`. Thus every current sequence of elements of `B_R` has a real code: apply `c_R` to its entries, flatten the resulting binary matrix using `N^2≈N`, and rigidify the one resulting real. This is unique definition, not countable Choice.

Every `B_R` is nontrivial: `P_R` contains the empty-stem, empty-side-condition condition, and the whole order differs from the empty regular open.

#### C.8.2.1. The exact Boolean coding property

For a complete Boolean algebra `B`, a sequence `b=(b_n)_{n∈N}` in `B`, and `x∈S_0`, put
$$
 F_x^B(b)=
 \bigvee_{m\in N}
 \bigwedge_{\substack{n\in N\\n\ge m,\ n\in D_x}}
 \neg_B b_n.
\tag{C.8.4}
$$
This is the Boolean value of the assertion that the represented set of 1-positions meets `D_x` only below some natural-number bound.

There is a canonical sequence `g^R=(g_n^R)` in `B_R` for which
$$
 F_x^{B_R}(g^R)=
 \begin{cases}
 1_{B_R},&x\in R,\\
 0_{B_R},&x\notin R.
 \end{cases}
\tag{C.8.5}
$$
For the definition, use regularized cones
$$
 b_q=j(\mathord\downarrow q),\qquad
 g_n^R=\bigvee\{b_{(s,F)}:n<|s|\text{ and }s(n)=1\}.
$$
Raw cones need not be regular open.

Here is a direct Boolean proof of (C.8.5). If `x∈R`, conditions whose finite side condition contains `x` are dense. If `q=(s,F)` is one of them, then for each `n≥|s|` belonging to `D_x`, its regularized cone is disjoint from `g_n^R`. Hence
$$
 b_q\le
 \bigwedge_{\substack{n\ge |s|\\ n\in D_x}}\neg g_n^R
 \le F_x^{B_R}(g^R).
$$
The join of these dense cone values is `1`, giving the first case.

If `x∉R`, then for any condition `(s,F)` and bound `m`, almost-disjointness supplies an `n∈D_x` above `m` and the stem length, outside every `D_y` with `y∈F`. Extending the stem with a 1 at `n` gives a condition below the original one whose cone lies below `g_n^R`. Consequently
$$
 \bigvee_{\substack{n\ge m\\n\in D_x}}g_n^R=1
$$
for every `m`. By complementation the corresponding meet in (C.8.4) is `0`, proving the second case. These arguments use only completeness and the explicit dense conditions; they do not require a forcing theorem or any modal selection principle.

#### C.8.2.2. Restriction and isomorphism

If `c>0` in a complete Boolean algebra `B`, the relative interval `B↾c` has top `c` and relative complement `c∧¬b`. Completeness gives
$$
 F_x^{B\restriction c}((c\wedge b_n)_n)
   =c\wedge F_x^B((b_n)_n).
\tag{C.8.6}
$$
Indeed relative meets have the form `c∧⋀`, and meeting with `c` distributes over arbitrary joins.

Suppose some nonzero interval of `B_R` is isomorphic to a nonzero interval of another complete Boolean algebra `B`:
$$
 \theta:B_R\restriction c\ \cong\ B\restriction b,
 \qquad c,b>0.
$$
An isomorphism of complete Boolean algebras preserves arbitrary joins and meets because it preserves the order and hence the unique least upper and greatest lower bounds. Transfer the restricted generic sequence:
$$
 h_n=\theta(c\wedge g_n^R).
$$
Equations (C.8.5)–(C.8.6) imply
$$
 R=\{x\in S_0:b\le F_x^B(h)\}
\tag{C.8.7}
$$
as current extensions. For `x∉R`, they give `b∧F_x^B(h)=0`; since `b>0`, the displayed inequality cannot hold. Thus (C.8.7) recovers both membership and nonmembership in `R`.

### C.8.3. A real catalogue of every earlier algebra's possible pattern

Let `h` be any current partial functional graph from `A` to the current rigid subproperties of `S_0`. Define a total map
$$
 G_h:S_0\longrightarrow T
$$
as follows. Use the fixed even/odd and matrix codings to decode an input real `s` into
$$
 (w,z_0,z_1,z_2,\ldots),
$$
where all components are current members of `S_0`. Put `β=d(w)`.

If `β` is outside the domain of `h`, output the empty rigid property. Otherwise let `R=h(β)`, decode
$$
 b=\delta_R(z_0),\qquad b_n=\delta_R(z_{n+1}),
$$
and output the empty property when `b=0`. When `b>0`, output the unique rigid current representative of
$$
 \{x\in S_0:b\le F_x^{B_R}((b_n)_n)\}.
\tag{C.8.8}
$$
This is a total uniquely defined current map. The membership condition uses the Boolean operations of `B_R`, not an inference from current logical equivalence to propositional identity.

The catalogue has the following coverage property:

> For every `β∈dom(h)`, every `b>0` in `B_{h(β)}`, and every current `N`-sequence `(b_n)` in that algebra, some `s∈S_0` has `G_h(s)` equal to the rigid representative of (C.8.8).

To prove this, choose one code `w` with `d(w)=β`, which exists by (C.8.2), and combine it with the canonical codes
$$
 c_{h(\beta)}(b),\quad
 c_{h(\beta)}(b_0),\quad c_{h(\beta)}(b_1),\ldots.
$$
One witness is chosen inside the proof of coverage for one given triple. No family of codes `w_β` is selected.

In particular, this catalogue does **not** require a chosen enumeration of the domain of `h`, or even require that domain to be countable. The fixed surjection `d:S_0→A` supplies the first coordinate of the code. This is why it works uniformly throughout the recursion below.

Now define the diagonal output
$$
 D(h)=\{s\in S_0:\neg G_h(s)(s)\}^{\dagger}.
\tag{C.8.9}
$$
This is again a current rigid subproperty of `S_0`, and for every current `s∈S_0`,
$$
 D(h)\ne G_h(s).
\tag{C.8.10}
$$
If equality held, substitution at the argument `s` would give a contradiction. Current coextension is converted to identity only for the unique rigid representatives already provided by RC.

The rule `D` depends only on the current extension of the history graph: histories that give the same values on the same domain give the same `G_h` values and hence the same rigid diagonal output. No conditional instance of Logical Equivalence is being used here.

### C.8.4. Fixed-type transfinite recursion

Use the current well-order of `A` to define
$$
 R_a=D((R_b)_{b<a})\qquad(a\in A).
\tag{C.8.11}
$$
This unique relational recursion is available in the restricted type system. All its values belong to one fixed current carrier: the rigid subproperties of `S_0`. If desired, use the rigid current representative of that carrier itself as a stable codomain. This changes none of its current members. Histories are binary relations between that fixed carrier and `A`; neither the domain type nor the value type grows with `a`.

For completeness, one can construct (C.8.11) directly. Call a partial graph admissible if it is functional, its domain is an initial segment of `A`, and at each member of its domain it obeys (C.8.11). Any two admissible graphs agree on their overlap: otherwise the current well-order supplies a least argument at which they differ; their prior histories agree there, and the uniquely defined rule `D` gives the same output, a contradiction.

By comprehension form the union of all admissible graphs. It is functional by compatibility. Its domain is an initial segment, and it obeys (C.8.11), since at any argument it agrees up to that argument with an admissible graph containing it. If its domain omitted some member of `A`, let `a` be the least omitted member. The union then has domain exactly `A_{<a}`; adjoining the uniquely specified value `D(h)` at `a` makes an admissible larger graph, contrary to the definition of the union. Its domain is therefore all of `A`.

This proof uses fixed-type comprehension and uniqueness. It does not use Replacement, Functional Choice, or Choice indexed by `A`. Identity is needed only for the uniquely rigidified values and graphs; extensional agreement of arbitrary raw histories is used as extensional agreement, not identified by an unlicensed Logical Equivalence instance.

### C.8.5. Pairwise absence of isomorphic nonzero intervals

If `b<a`, no nonzero interval of `B_{R_a}` is isomorphic to a nonzero interval of `B_{R_b}`.

Suppose there were such an isomorphism. By (C.8.7), a nonzero element of `B_{R_b}` and a sequence of elements of that algebra would recover `R_a` by formula (C.8.8). The coverage property of the catalogue for the prior history `(R_c)_{c<a}` would then put `R_a` in the range of that catalogue, contradicting (C.8.10) and (C.8.11).

Thus the current family `(B_{R_a})_{a∈A}` is pairwise nowhere interval-isomorphic in the precise sense required: two distinct members have no isomorphic nonzero principal intervals. The proof is symmetric in a pair after comparing its two indices in the well-order.

### C.8.6. Canonical supports in the propositional algebra

For each `a∈A`, define
$$
 q_a=\bigvee\left\{p\in\Pi:
   p\ne0\ \land\
   \exists c\in B_{R_a}\left[
    c\ne0\ \land\
    B_{R_a}\restriction c\cong\Pi\restriction p
   \right]\right\}.
\tag{C.8.12}
$$
The quantified isomorphisms all have fixed types, since the algebras `B_R` have a fixed uniform presentation. Boolean Completeness gives the join, and its unique value defines a current relational graph `a↦q_a`.

Every `q_a` is nonzero. By (C.8.3) and (C.8.1), `B_{R_a}≺Π`; original FP therefore gives an isomorphism of the full algebra `B_{R_a}` with a proper principal interval of `Π`. Its top is nonzero because `B_{R_a}` is nontrivial, and so occurs in the set joined in (C.8.12).

For `a≠b`, let `p` and `r` be any two propositions occurring in the respective sets in (C.8.12). If `p∧r` were nonzero, the two interval isomorphisms could be restricted to inverse images of `p∧r`. Composing one with the inverse of the other would give an isomorphism between nonzero intervals of `B_{R_a}` and `B_{R_b}`, contrary to Section C.8.5. Hence `p∧r=0`. Distributing finite meets over arbitrary joins gives
$$
 q_a\wedge q_b=0.
\tag{C.8.13}
$$
This establishes the claimed `A`-indexed propositional antichain. No interval supplied by FP was selected simultaneously: the definition joins **all** eligible interval tops for each index.

### C.8.7. Cardinal bound and ordinal-indexed choice

Sending a rigid current `X⊆A` to
$$
 \bigvee_{a\in X}q_a
$$
gives a current injection
$$
 \mathcal P_r(A)\precsim\Pi.
\tag{C.8.14}
$$
Indeed if `X` and `Y` differ at `a`, then `q_a>0` is below one of the two joins and disjoint from the other.

Inverse image under the fixed surjection `d:S_0→A`, followed by unique rigidification, gives
$$
 \mathcal P_r(A)\precsim\mathcal P_r(S_0)\approx T.
\tag{C.8.15}
$$
Thus `Π≼P_r(A)` would contradict `W`. Combining (C.8.14)–(C.8.15),
$$
 \mathcal P_r(A)\prec\Pi.
\tag{C.8.16}
$$

The atomic complete Boolean algebra `P_r(A)` is therefore covered by original FP. Apply the established atomic-choice lemma, with stable index carrier `A`, to obtain ordinary relational Choice indexed by `A` into every stable target. In particular apply it to the serial relation
$$
 d(s)=a\qquad(a\in A,\ s\in S_0).
$$
The resulting choice graph is a section of `d`, so
$$
 A\precsim S_0\approx S.
\tag{C.8.17}
$$

## C.9. Stationary coding and the forward injection

The construction is inspired by the stationary and ladder coding in Saharon Shelah, *Why There Are Many Nonisomorphic Models for Unsuperstable Theories*, ICM Vancouver 1974, Theorem 1.2, [author-hosted paper](https://shelah.logic.at/files/203572/Sh-51.pdf). The proof here supplies an explicit projection onto completed initial subalgebras. It does not import the paper's brief assertion that its coding invariant survives completion, nor assume its ordinary Choice background.

### C.9.1. The theorem and the available choice

Retain
$$
\Gamma=C+\Box RC+IC+FP_<+\Box\operatorname{Peano}(N),
\qquad
S=\mathcal P_r(N),\quad S_0=S^\dagger,\quad T=\mathcal P_r(S),
$$
with the definitional stable arithmetic base used throughout the note, and let
$$
W=\neg(\Pi\precsim T).
$$

**Theorem.**
$$
\boxed{\Gamma+W\ \vdash\ T\precsim\Pi.}
\tag{C.9.1}
$$
Consequently,
$$
\boxed{\Gamma+W\ \vdash\
T\prec\Pi\ \land\ \Diamond C_N\ \land\ \Diamond\neg C_N.}
\tag{C.9.2}
$$
Under $\Gamma$, the weak non-injection premise and the strict cardinality premise are therefore equivalent. Neither a current well-order of $S$ nor an inaccessible carrier is an extra assumption. IC and FP remain unboxed.

**Available parameters.** C.8 supplies a stable current first uncountable order-type carrier $A=H(N)$ and
$$
\mathcal P_r(A)\prec\Pi,\qquad
\mathrm{Choice}_A\text{ into every stable target}.
\tag{C.9.3}
$$
Countable Choice into stable targets is also available. Write $\kappa=\omega_1$ for the current well-order on $A$, using ordinal notation only for this fixed carrier. All constructions below are current.

We shall construct, uniformly for $r\in S_0$, nontrivial complete Boolean algebras $B_r$ such that
$$
B_r\precsim\mathcal P_r(A)
\quad\text{and}\quad
r\ne s\ \Longrightarrow\
\text{no nonzero interval of }B_r\text{ is isomorphic to one of }B_s.
\tag{C.9.4}
$$
The interval-support argument of C.8 then gives an $S_0$-indexed antichain in $\Pi$. Subfamily joins supply (C.9.1).

### C.9.2. Stationary parameters with an explicit choice bound

Every proper initial segment of $\kappa$ is countable. Choice indexed by $A$ supplies a fixed family of injections
$$
e_\beta:\beta\hookrightarrow N\qquad(\beta<\kappa).
$$
Countable Choice, or this chosen family applied to a purported countable cofinal sequence, shows that $\kappa$ is regular. All sequence graphs, clubs, and stationary subsets used below are rigid relations or rigid subproperties of fixed stable carriers.

**Pressing down.** Fodor's lemma holds with the available choice. If every fibre of a regressive map on a stationary subset of $\kappa$ were nonstationary, $\mathrm{Choice}_A$ would select a club avoiding each fibre. The diagonal intersection of those clubs is club: closure is immediate from the definitions, and unboundedness follows by a countable increasing recursion followed by regularity. A member of the stationary set in that diagonal intersection contradicts regressiveness. The choice target here is the stable carrier of current rigid subsets of $A$.

**Disjoint stationary sets.** For $\alpha<\kappa$ and $n\in N$, define the Ulam matrix
$$
U(\alpha,n)=
\{\beta\in\operatorname{Lim}(\kappa):
\alpha<\beta,\ e_\beta(\alpha)=n\}.
\tag{C.9.5}
$$
For each $\alpha$, these sets partition a club tail as $n$ varies. At least one is stationary: otherwise countable Choice supplies clubs avoiding every cell, and their countable intersection contradicts the covering of that tail. Let $n(\alpha)$ be the least stationary-cell index.

Some value $n_*$ occurs for uncountably many $\alpha$. Otherwise $\kappa$ would be a countable union of countable sets. For those $\alpha$, the sets $U(\alpha,n_*)$ are pairwise disjoint, by injectivity of each $e_\beta$. Their uncountable index subset of $\kappa$ has order type $\kappa$. Reindex using $N\times2\times\kappa\approx\kappa$ to obtain disjoint stationary sets
$$
S_{n,i,\alpha}\subseteq\operatorname{Lim}(\kappa)
\qquad(n\in N,\ i<2,\ \alpha<\kappa).
$$

Fix an enumeration $(t_\alpha)_{\alpha<\kappa}$ of all finite syntactically consistent literal assignments on variables
$$
x_\xi,\ y_\eta\qquad(\xi,\eta<\kappa),
$$
and fix an injective code for these assignments into $\kappa$. An assignment is a finite partial $0$–$1$ map on two tagged copies of $\kappa$; syntactic consistency means that it never assigns both bits to one variable. The required finite-product and finite-sequence codings are elementary arithmetic on this well-ordered carrier. They do not enumerate the reals.

Trim each $S_{n,i,\alpha}$ above every variable index occurring in $t_\alpha$, and above $\alpha$. Removing a bounded initial segment preserves stationarity and disjointness.

For every $\delta$ in their union, choose a strictly increasing cofinal $\omega$-sequence
$$
L_\delta\subseteq\delta
$$
whose first element exceeds every index in the associated $t_\alpha$. These sequences exist because the marked ordinals are nonzero countable limits. This is one choice indexed by a subset of $A$, into the stable carrier of sequence graphs. Distinct ladders have finite intersection: if $\delta<\gamma$, then $L_\gamma\cap\delta$ is finite and $L_\delta\subseteq\delta$.

All these parameters are fixed independently of $r$. Identify an old binary real $r\in S_0$ with its current $0$–$1$ membership function on $N$, and put
$$
E_r=\bigcup_{n\in N,\ \alpha<\kappa}S_{n,r(n),\alpha}.
\tag{C.9.6}
$$
An ordinal is **active for $r$** if it belongs to $E_r$. Every marked ordinal $\delta$ has a unique associated finite label $t(\delta)=t_\alpha$, since the stationary sets are disjoint.

### C.9.3. The finite-condition orders and their completions

A condition $p\in P_r$ is a finite consistent literal assignment satisfying:

1. If $p(y_\delta)=1$, then $\delta$ is active for $r$ and $t(\delta)\subseteq p$.
2. If $p(y_\delta)=1$ and $p(x_\xi)=0$, then $\xi\notin L_\delta$.

Order conditions by extension: $q\le p$ means $q\supseteq p$.

The closure of a finite assignment under its positive-$y$ labels is finite. Each positive-$y$ dependency has strictly smaller ordinal index. By induction on that index, the closure of each single positive-$y$ literal is a finite union of previously finite closures; a finite initial assignment then has finite closure. Equivalently its finitely branching dependency tree cannot have an infinite descending ordinal branch. Reject the closure if it has conflicting literals, a positive inactive $y$, or a negative $x$ on the ladder of a positive $y$. This closure is uniquely defined.

Two conditions are compatible exactly when their union has no conflicting literals and no forbidden negative-$x$/positive-$y$ ladder pair. Each condition is already closed under its labels, so their union is closed; if the compatibility test passes, it is a common extension.

The condition set is a subset of the fixed well-ordered carrier of finite assignments, uniformly in $r$. Hence $P_r\precsim A$. Let
$$
B_r=\operatorname{RO}(P_r).
$$
A regular open is represented by its rigid current membership set. The fixed code of conditions therefore gives, uniformly,
$$
B_r\hookrightarrow\mathcal P_r(A).
\tag{C.9.7}
$$
The algebra is nontrivial: the single-literal conditions $x_\xi=0$ and $x_\xi=1$ are valid and incompatible. Write $[p]=j(\mathord\downarrow p)$ for a regularized cone. No separativity of the presented poset is assumed.

Define
$$
X_\xi^r=\bigvee\{[p]:p\in P_r,\ p(x_\xi)=1\}.
$$
Conditions deciding $x_\xi$ are dense. If an existing positive-$y$ ladder requires the bit, assign $1$; otherwise either assignment is valid unless the bit has already been decided. Conditions deciding $y_\eta$ are dense as well, since an unset $y_\eta$ can always be assigned $0$.

Let $X^+(p)$ and $Y^+(p)$ be the finite sets of explicitly positive $x$- and $y$-indices of $p$. Then
$$
[p]\le X_\xi^r
\quad\Longleftrightarrow\quad
\xi\in X^+(p)\ \cup\
\bigcup_{\gamma\in Y^+(p)}L_\gamma.
\tag{C.9.8}
$$
If $\xi$ is outside this union, adjoining $x_\xi=0$ is a valid nonzero extension, so the inequality fails. If $\xi$ is inside it, every decision below $p$ has positive bit, so density gives the inequality.

In particular, the indices of all positive $x$-bits forced by any one finite condition are bounded in $\kappa$. Take a bound above its finitely many variable indices; every ladder protected by that condition lies below its corresponding positive-$y$ index.

### C.9.4. Countable chain condition

Suppose there is an uncountable antichain in $P_r$. The condition set injects into the well-ordered $\kappa$, so take a $\kappa$-sized subfamily. Apply the finite $\Delta$-system lemma to its finite ordinal supports. Thin so that the variable types and assigned bits agree on the root, and so that the disjoint petals lie in successive blocks above the root.

The $\Delta$-system lemma here concerns finite subsets of a fixed well-ordered carrier. Its usual induction on support size uses regularity and least choices in that carrier; it assumes no well-order of an arbitrary family of sets. The block thinning is likewise obtained recursively by taking the least remaining petal above the current bound.

Choose countably infinitely many early petals and an ordinal $\eta<\kappa$ strictly above their union. Choose a further condition $q$ whose petal lies entirely above $\eta$. Every positive $y_\gamma$ in that later petal has $\gamma>\eta$, so its ladder meets $\eta$ in only finitely many points. The finitely many such ladders of $q$ therefore meet only finitely many of the chosen early petals. Select an early condition $p$ whose petal they miss.

No positive $y$ in the earlier petal can create a conflict with a negative $x$ in the later one: its ladder lies below its own index. A positive $y$ in the root also cannot reach a petal. Conflicts involving a root negative literal were already excluded by the validity of each condition separately. The common root and disjoint petals exclude literal conflicts. Thus $p\cup q$ is a valid condition, contradicting the antichain.

The order is therefore ccc. Its completion is ccc as well. To see this without presupposing that a Boolean antichain is well-orderable, send each of its nonzero members to the least coded condition whose cone lies below that member. These conditions are distinct and pairwise incompatible. This injects the Boolean antichain into a well-ordered poset antichain, which is countable.

### C.9.5. A projection respecting completed old subalgebras

Fix an ordinal $\delta$ that is inactive for $r$. Let $P_r\restriction\delta$ consist of conditions all of whose variable indices are below $\delta$. For $p\in P_r$, define $\pi_\delta(p)$ by:

1. retaining all literals of $p$ with indices below $\delta$;
2. adding $x_\xi=1$ for every $\xi\in L_\gamma\cap\delta$ whenever $p(y_\gamma)=1$ and $\gamma>\delta$.

There is no positive $y_\delta$, since $\delta$ is inactive. Each added ladder intersection is finite, and only finitely many ladders occur. The result is a finite old condition. Labels of retained positive $y$-variables stay below $\delta$. Old label literals of discarded positive $y$-variables were already present in $p$ and are retained. An added positive $x$ cannot conflict with a retained negative literal, by the validity of $p$.

The key reduction property is
$$
u\in P_r\restriction\delta,\quad u\le\pi_\delta(p)
\quad\Longrightarrow\quad
u\text{ is compatible with }p.
\tag{C.9.9}
$$
An old negative $x$ in $u$ cannot fall on a ladder from a positive $y$ of $p$ above $\delta$: all relevant old ladder points were added positively to the projection. A positive $y$ newly introduced by $u$ has its whole ladder below $\delta$, so it cannot conflict with a discarded negative $x$ of $p$; retained negatives are already in the projection. All literal conflicts are similarly excluded. Thus $u\cup p$ is a condition.

Also
$$
[p]\le[\pi_\delta(p)]
\tag{C.9.10}
$$
in the ambient completion. Retained literals belong to $p$, and its positive-$y$ ladders imply every added positive $x$-literal by (C.9.8).

Incompatibility of old conditions is unchanged by the inclusion into $P_r$. Every predense subset of the old order stays predense in the full order: apply old predensity below $\pi_\delta(p)$ and then (C.9.9). The inclusion is therefore regular, and the old completion embeds as a complete subalgebra
$$
C_\delta^r\subseteq B_r.
$$
Explicitly, send an old regular open to the ambient regularization of the union of its cones. Preservation of incompatibility and predensity gives preservation of complements and arbitrary joins, without a further choice principle. Old condition cones have their ambient cone values under this embedding.

The essential strengthening is
$$
b\in C_\delta^r,\quad[p]\le b
\quad\Longrightarrow\quad
[\pi_\delta(p)]\le b.
\tag{C.9.11}
$$
If the conclusion failed, density of old conditions in $C_\delta^r$ would give an old $u$ with a nonzero cone below
$[\pi_\delta(p)]\wedge\neg b$.
That $u$ is compatible with $\pi_\delta(p)$. Replacing it by the old common extension $u\cup\pi_\delta(p)$ puts it syntactically below the projection. By (C.9.9) it is then compatible with $p$, contradicting $[p]\le b$.

This proves the required statement about every Boolean value in the **completed** initial algebra. It is stronger than preservation of finite formulas in a dense presentation.

### C.9.6. Canonical countable supports and a closure club

For each $b\in B_r$, run through the fixed well-order of $P_r$ and admit a condition exactly when its cone lies below $b$ and it is incompatible with every previously admitted condition. Fixed-type relational recursion gives this family uniquely. It is a maximal antichain below $b$, and its join is $b$. By C.9.4 it is countable. The union of its finite ordinal supports is therefore countable and bounded below $\kappa$.

This definition is uniform in $b$ and selects no arbitrary maximal antichains. Thus, for a given sequence $(b_\xi)_{\xi<\kappa}$ of Boolean values, there is a uniquely defined support-bound function $g:\kappa\to\kappa$. On the club of limit ordinals $\delta$ closed under $g$, every $b_\xi$ with $\xi<\delta$ is a join of conditions supported below $\delta$. If $\delta$ is inactive, it follows that
$$
b_\xi\in C_\delta^r\qquad(\xi<\delta).
\tag{C.9.12}
$$
A fixed additional Boolean value can be included by requiring $\delta$ to exceed its support bound.

There is also a club of $\delta$ closed under the fixed coding of finite literal assignments:
$$
\operatorname{supp}(p)\subseteq\delta
\quad\Longrightarrow\quad
\operatorname{code}(p)<\delta.
\tag{C.9.13}
$$
For each $\alpha<\kappa$, the assignments supported below $\alpha$ form a countable set, so their codes have a bound below $\kappa$. Take the club closed under this bound function. Intersecting these finitely many clubs retains a club.

### C.9.7. Distinct real indices give no isomorphic nonzero intervals

Let $r\ne s$, choose $n$ with $r(n)\ne s(n)$, and suppose toward a contradiction that
$$
f:B_r\restriction a\ \cong\ B_s\restriction b
\qquad(a,b>0).
\tag{C.9.14}
$$
Choose a source condition $c$ with $[c]\le a$, and choose its label index $\alpha$ so that $t_\alpha=c$.

For each $\delta\in S_{n,r(n),\alpha}$, the ordinal $\delta$ is active for $r$ and inactive for $s$. Its label is $c$, it exceeds every index in $c$, and its ladder starts above those indices. Consequently
$$
c_\delta=c\cup\{y_\delta=1\}
$$
is a valid closed condition. Put $d_\delta=[c_\delta]>0$. Then
$$
d_\delta\le[c]\le a,\qquad
d_\delta\le X_\xi^r\quad(\xi\in L_\delta).
\tag{C.9.15}
$$

Apply C.9.6 in the target algebra to the sequence
$$
\bigl(f(a\wedge X_\xi^r)\bigr)_{\xi<\kappa}
$$
and to the additional value $f([c])$. Intersect its support club with the finite-coding club. For every $\delta$ in this club that is also in $S_{n,r(n),\alpha}$, the values $f([c])$ and $f(a\wedge X_\xi^r)$, for $\xi<\delta$, belong to $C_\delta^s$. The set of such $\delta$ remains stationary.

For each of those $\delta$, take the least target condition $p_\delta$ with
$$
[p_\delta]\le f(d_\delta)
$$
and put $e_\delta=\pi_\delta(p_\delta)$. These choices are unique least choices in the fixed condition well-order. The completed projection property (C.9.11) and (C.9.15) yield
$$
[e_\delta]\le f([c]),\qquad
[e_\delta]\le f(a\wedge X_\xi^r)\quad(\xi\in L_\delta).
\tag{C.9.16}
$$

Each $e_\delta$ is a nonzero finite old condition. By (C.9.13), its code is below $\delta$. Fodor's lemma therefore supplies a stationary subset on which $e_\delta$ is one fixed condition $e$.

The first inequality in (C.9.16) places $[e]$ below $b$, inside the target interval. Hence $q=f^{-1}([e])$ is a well-defined nonzero source element. Take a finite condition $p$ with $[p]\le q$. For every $\delta$ in that stationary subset, the second inequality gives
$$
[p]\le X_\xi^r\qquad(\xi\in L_\delta).
\tag{C.9.17}
$$
Choose a bound above every index in $p$, then choose one of these stationary $\delta$ above that bound, and finally a point $\xi\in L_\delta$ above it. No positive $y$ of $p$ can require $x_\xi=1$, since its ladder is below its own index. Nor does $p$ explicitly mention $x_\xi$. Thus adjoining $x_\xi=0$ is a valid nonzero extension, contradicting (C.9.17).

This rules out (C.9.14) for all nonzero $a,b$ and proves the nowhere-isomorphism assertion (C.9.4). $\square$

### C.9.8. The propositional antichain and the final injection

All $B_r$ are presented on one fixed relational carrier type. By (C.9.7) and (C.9.3), each is strictly smaller than $\Pi$: a reverse injection from $\Pi$ into $B_r$ would compose to the prohibited injection into $\mathcal P_r(A)$. Original FP therefore applies separately to every $B_r$.

For each $r\in S_0$, define
$$
q_r=
\bigvee\left\{p\in\Pi:
p\ne0\ \land\
\exists c\in B_r\,
\bigl(c\ne0\land B_r\restriction c\cong\Pi\restriction p\bigr)
\right\}.
\tag{C.9.18}
$$
This is a unique Boolean join, so comprehension defines its graph uniformly in $r$. FP represents the whole nontrivial $B_r$ as a full proper principal interval, whose top occurs among the joined terms. Thus $q_r\ne0$.

For $r\ne s$, any eligible tops occurring in the two joins have zero meet. A nonzero overlap would, by restricting the two full interval isomorphisms, give isomorphic nonzero intervals of $B_r$ and $B_s$, contrary to C.9.7. Finite meets distribute over arbitrary joins in a complete Boolean algebra, so
$$
q_r\wedge q_s=0\qquad(r\ne s).
\tag{C.9.19}
$$
No simultaneous family of FP representations has been selected: each $q_r$ joins **all** eligible tops.

For a rigid current subproperty $R$ of $S_0$, put
$$
J(R)=\bigvee_{r\in R}q_r.
\tag{C.9.20}
$$
If $R\ne R'$, a member in their symmetric difference has a nonzero $q_r$ below one join and disjoint from the other. Thus $J$ is injective. Since $S_0$ and $S$ have the same current members, unique rigid representatives give $\mathcal P_r(S_0)\approx T$. This proves
$$
T\precsim\Pi.
$$
The assumed $W$ makes the comparison strict. Original FP now covers every current CBA whose carrier injects into $T$. The bounded forcing theorem (B.5) gives both possibilities in (C.9.2).

The necessary real-structure bridge in Part I then gives both structural CH possibilities at the fixed type with necessary real existence. The resulting structural theorem permits the correctly directed weak premise
$$
W_\sigma:=
\exists\mathfrak R\,
\left(
\operatorname{Real}_\sigma(\mathfrak R)
\land
\neg\bigl(\Pi\precsim\mathcal P_r(X_{\mathfrak R})\bigr)
\right).
\tag{C.9.21}
$$
Current real comparison transports $W_\sigma$ to $W$. Thus the correctly directed non-injection, necessary arithmetic, and the original map principles already contradict structural non-contingency of CH. The same conclusion follows using the map's boxed quantified exact individual Infinity axiom to supply the arithmetic base.

### C.9.9. Fixed types and dependencies

Assignments are finite relations on tagged copies of $A$, with tags and bits in a fixed finite subcarrier of $N$. Ladders are relations on $N\times A$. Clubs and stationary sets are rigid subproperties of $A$. A regular open is a rigid subproperty of the fixed finite-assignment carrier; varying $r$ changes a carrier predicate, not its type. Families and isomorphisms consequently have fixed finite relational types.

The ordinal and greedy recursions take values in fixed carriers and can be constructed by the union of compatible admissible partial histories, as in C.8.4. They use no Replacement or object-language quantification over types. The initial enumeration and ladder data, and the choices in the Ulam and pressing-down arguments, use at most the already derived $\mathrm{Choice}_A$ into stable targets. Every subsequent selection across parameters is by a unique definition or a least member of the fixed well-order of conditions. No choice indexed by the reals is inserted.

This proves the repaired implication for the original map FP. The two added premises have distinct roles: largeness supplies the forcing coverage, and necessary arithmetic supplies the structures and comparisons throughout the represented intervals. The countermodels in Part I show that neither addition can simply be omitted.

## Paper references

- **Origin: [Could the truths of mathematics have been different?](https://andrew-bacon.github.io/papers/Could%20mathematics%20have%20been%20different.pdf).** Bacon, Andrew (2025). Could the truths of mathematics have been different? Draft dated 9 October 2025, with online appendix; published in Philosophical Review 135(3), 2026, pp. 221–285, as cited by Barton and Goodsell. Locators refer to the draft. The full Boolean-valued construction is in appendix §B.2, pp. 7–9 of the separately paginated appendix (PDF pp. 41–43); Theorem 4.4 and its proof (Appendix C.1) and Lemma C.6 (Appendix C.2) were read directly on 19 October 2026. — §6, Theorem 6.1, p. 27. □Rigid Comprehension, Intensional Choice and Mathematical Possibilism (the map's Forcing Possibilism) entail structural contingency about the continuum hypothesis, $\Diamond\exists X(\operatorname{Real}X\land\operatorname{CH}(X))\land\Diamond\exists X(\operatorname{Real}X\land\neg\operatorname{CH}(X))$, which contradicts both disjuncts of the Non-contingency of the Continuum Hypothesis at that type.
