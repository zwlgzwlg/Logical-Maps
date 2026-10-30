# Completeness and choice: restrictions on three constructions

Daniel Kodsi, with ChatGPT assistance. 30 October 2026.

The first two results below rule out specified classes of proposed models.
The third identifies a missing step in a proposed proof from Functional Choice
to Boolean Completeness. Their hypotheses concern the represented scalar
algebra, the admission of operations or predicates, and the interpretation of
quantifiers. They are not unrestricted implications between the map's
principles.

The metatheory is ZFC. Unless a box is displayed, assertions concern the chosen
evaluation point. Scalar equality is equality of whole propositions, and scalar
order is necessary implication. In the concrete algebras below these are
literal equality and inclusion. Quantifiers have their ordinary material
meaning over the full admitted domain at the evaluation point. No independent
human check or Lean certificate is claimed.

## 1. Uniform coordinate bounds do not permit scalar completeness and a selector

Let \(L\) be a nontrivial free monoid with identity \(\epsilon\), let \(I\) be a
set, and let \(\lambda\leq |I|\) be an infinite cardinal. Put \(M=L^I\).
Suppose the scalar domain is exactly
\[
B=\{b\subseteq M:b\text{ depends on fewer than }\lambda
                  \text{ coordinates}\}.
\tag{1}
\]
Boolean operations are set operations. In addition to the ordinary typed
lambda and quantifier clauses of C, assume that a predicate \(E^{tt}\) is
admitted whose current instances are exactly
\[
b_i=\{m\in M:m_i\ne\epsilon\},\qquad i\in I.
\tag{2}
\]
No support condition is imposed on the other admitted higher-type entities.

Consider the admitted serial relation
\[
D(p,c)\ \equiv\
\bigl(p\ne\top\land E(c)\land c\not\leq p\bigr)
\ \lor\ \bigl(p=\top\land c=\bot\bigr).
\tag{3}
\]
It is serial: if \(p\ne\top\) has support \(S\), choose \(i\notin S\) and
an arrow outside \(p\); changing only its \(i\)-coordinate to a nonempty word
shows \(b_i\not\leq p\).

**Theorem.** Under these hypotheses, Boolean Completeness at \(t\) is
incompatible with a total functional selecting subrelation \(K^{ttt}\) of
\(D\). Consequently it is incompatible with the \((t,t)\) instance of
Relational Choice in this class.

The assertion concerns a selecting *graph*. It does not assume an operation
that realizes the graph.

### 1.1. Finite coordinate support

First take \(\lambda=\omega\). For any admitted predicate \(A\) whose
instances are markers, the formula
\[
\operatorname{BoundFin}(A)\ \equiv\
\exists p^t\bigl(p\ne\top\land
                 \forall a^t(Aa\to a\leq p)\bigr)
\tag{4}
\]
holds exactly when its current marker extension is externally finite.
A finite family is bounded by its finite union, which is proper because it
omits the all-identity arrow. Conversely, if a proper scalar \(p\) with finite
support \(S\) bounds the family, every marker in it has its coordinate in
\(S\): changing a coordinate outside \(S\) cannot turn an arrow outside \(p\)
into an arrow inside \(p\).

Assume such a graph \(K\) exists. Define externally
\[
p_n=\bigvee_{r<n}c_r,\qquad K(p_n,c_n),\qquad n<\omega.
\tag{5}
\]
Every displayed finite union is an admitted proper scalar. Formula (3) makes
each \(c_n\) a new marker. This auxiliary recursion does not assert that the
whole sequence is admitted.

For \(H^{ttt}\), let its field be \(A_H(a)\equiv H(a,a)\).
The formula \(\operatorname{FinHist}(H)\) says that:

- the field is contained in \(E\), and \(H\) has no pairs outside that field;
- \(H\) is a reflexive total order, including transitivity and antisymmetry;
- \(\operatorname{BoundFin}(A_H)\) holds;
- each field member is \(K\)'s output at the scalar least upper bound of
  its strict predecessors.

These conditions are finite formulas at the stated types. The last condition
uses the native upper-bound and leastness quantifiers; it assumes no join
operation. By (4), any such history has an externally finite field.
Induction through its order identifies its entries with
\(c_0,\ldots,c_{n-1}\): at the \(r\)-th step the predecessor family has the
unique whole scalar least upper bound \(p_r\), so functionality of \(K\)
forces the same output \(c_r\).

Conversely, every finite prefix is admitted. For a fixed external \(n\), the
finite lambda formula
\[
H_n(a,b)=\bigvee_{0\leq r\leq s<n}(a=c_r\land b=c_s)
\tag{6}
\]
has the required current table. Thus the single admitted relation
\[
O(a,b)=\exists H^{ttt}
       \bigl(\operatorname{FinHist}(H)\land H(a,b)\bigr)
\tag{7}
\]
has precisely the reflexive \(\omega\)-order on the \(c_n\). All admitted
histories are compatible finite prefixes, and every pair of positions occurs
in one of them. This uses the fixed model's quantifier domain throughout;
there is no assumption that an arbitrary union profile is admitted.

We next define a suitable subfamily of cells without assuming a native
standard numerical domain. For a finite predicate \(A\), let
\(\operatorname{Even}(A)\) assert that an admitted graph on its field is
symmetric, functional, total, and has no fixed points or pairs off the field.
Such a graph exists exactly when the finite field has even cardinality:
one direction partitions the field into pairs, and a finite matching in the
other direction is represented by a finite equality-disjunction lambda term.

For \(c_n\), the property of its strict \(O\)-predecessors has exactly \(n\)
members and unique least upper bound \(p_n\). Lambda abstraction therefore
admits the family consisting exactly of
\[
z_n=c_n\land\neg p_n\qquad(n\text{ even}),
\tag{8}
\]
by quantifying over a position \(c\), its predecessor least upper bound,
and the displayed matching condition.

The cells \(z_n\) are pairwise disjoint nonzero scalars. For every odd \(m\),
\(\neg z_m\) bounds the whole family (8). Suppose its least upper bound \(s\)
had finite support \(S\). Write \(c_n=b_{i_n}\), with all \(i_n\) distinct,
and choose an even \(n\) and odd \(m\) with \(i_n,i_m\notin S\).
The arrows active only at \(i_n\) or only at \(i_m\) agree on \(S\).
The first lies in \(z_n\), so must lie in \(s\); leastness below
\(\neg z_m\) excludes the second. This contradicts support in \(S\).
The family is admitted but has no scalar least upper bound.

### 1.2. Every larger infinite threshold, including singular thresholds

Let \(\lambda>\omega\), viewed as its initial ordinal. Every countable
marker family \(J\) has its raw union \(u_J\) in \(B\), and
\[
E_J(a)\equiv E(a)\land a\leq u_J
\tag{9}
\]
selects exactly that family. Hence any admitted order on markers which
satisfies the native well-order condition is externally well-founded.
Otherwise an external descending \(\omega\)-sequence would have the
admitted range predicate (9), with no least member.

Define (5) for \(\alpha<\lambda\) in place of \(n<\omega\).
At each stage the union of the \(\alpha\) earlier markers depends on
\(|\alpha|<\lambda\) coordinates and is an admitted proper scalar.
Let \(\operatorname{Hist}(H)\) require a well-ordered marker field, no
pairs off the field, and the same predecessor-join and \(K\)-output clause
as before. External well-foundedness and functionality imply that every
valid history is an initial segment of the canonical sequence.
It has no entry at position \(\lambda\): \(\lambda\) distinct markers have
only \(\top\) as a scalar upper bound in (1), whereas \(K(\top)=\bot\)
is not a marker.

Let \(\Theta\) be the supremum of the lengths of admitted valid histories.
The analogue of (7) collects their compatible tables into the exact
\(\Theta\)-order. Every pair of positions occurs together in one history.
This collected relation is itself a valid history: its actual order is an
ordinal, so it satisfies all admitted well-order tests; each position is
below \(\lambda\), and its predecessor join is the already existing
\(p_\alpha\). If \(\Theta<\lambda\), a finite lambda expression appending
the parameter \(c_\Theta\) gives a longer valid history. Therefore
\(\Theta=\lambda\). No arbitrary short history table was assumed admitted.

The immediate-predecessor test now admits precisely the successor cells
\[
z_\alpha=c_\alpha\land\neg p_\alpha
\qquad(\alpha<\lambda\text{ a successor}).
\tag{10}
\]
Every nonzero limit cell is omitted, and its complement bounds (10).
If \(s\) were a least upper bound with support of size below \(\lambda\),
choose one successor marker and one nonzero limit marker outside that
support. There are \(\lambda\) positions of each kind. The two arrows active
only at the selected coordinates agree on the support, but boundedness
includes the first while leastness excludes the second.

This last argument does not require the support positions to be bounded in
\(\lambda\). It uses coordinates *outside* the support, so it applies when
\(\lambda\) is singular as well.

The theorem covers changes to higher admission which preserve (1), (2),
and the stated semantic clauses. It does not cover nonuniform support
ideals, omission of \(E\), or a change of scalar equality or order. It
supplies no unrestricted implication from scalar Boolean Completeness and
Relational Choice to Actuality, and no same-type Zorn conclusion.

## 2. A Scott-ultrafilter algebra cannot admit all finitely supported operations

Let \(U\) be a nonprincipal ultrafilter on \(\mathbb N\), and give \(W=U\)
the topology with basic opens
\[
\{w\in U:F\subseteq w\},\qquad F\subseteq\mathbb N\text{ finite}.
\]
Let \(A\) be any nontrivial externally complete Boolean algebra, and put
\(B=A^W\). For \(P\subseteq W\), let \(j(P)\) be its endpoint-valued
indicator. Define
\[
\operatorname{core}(b)=\{w:b_w=1_A\},\qquad
Jb=j\bigl(\operatorname{int}(\operatorname{core}(b))\bigr).
\tag{11}
\]
For \(b,c\in B\), put
\[
\delta(b,c)=j\bigl(\operatorname{int}\{w:b_w=c_w\}\bigr).
\]

**Theorem.** There is no faithful interpretation of C with whole scalar
algebra \(B\), native necessity \(J\), ordinary material quantifier truth,
and an operation domain containing every map \(f:B\to B\) which:

- is nonexpansive, meaning \(\delta(b,c)\leq\delta(f(b),f(c))\);
- has finite support by scalar parameters under
  \(\operatorname{Aut}(B,J)\), or under any chosen subgroup of that group.

Here scalar support means that every automorphism fixing the finitely many
parameters commutes with \(f\). Full scalar availability is not by itself
the prohibited hypothesis; the conclusion concerns the displayed admission
rule for operations.

### 2.1. A strictly inflating operation on proper opens

Partition \(W\) into the sets
\[
C_n=\{w\in U:\min w=n\}.
\]
For an open \(O\), set
\[
H(O)=\bigcup_{n\in\mathbb N}\operatorname{int}(O\cup C_n).
\tag{12}
\]
If \(O\ne W\), then \(O\subsetneq H(O)\subsetneq W\).
For strictness, choose the least possible minimum \(n\) of a point
\(s\notin O\). Every point containing \(n\) either has smaller minimum
and lies in \(O\), or has minimum \(n\) and lies in \(C_n\).
This is an open neighborhood of \(s\) contained in \(O\cup C_n\).

For properness, fix any \(s\notin O\), and put
\(t=s\setminus\{\min s\}\). Then \(t\in U\) and \(t\notin O\), because
opens are upward closed for inclusion. For \(n\ne\min t\), the point
\(t\) itself excludes membership in \(\operatorname{int}(O\cup C_n)\).
For \(n=\min t\), every neighborhood of \(t\) contains \(s\), which is
outside both \(O\) and \(C_n\). Thus this one \(t\) is outside every
summand of (12); merely knowing that each summand is proper would not
suffice.

Now define
\[
K(b)=j\bigl(H(\operatorname{int}(\operatorname{core}(b)))\bigr).
\tag{13}
\]
It sends every proper \(J\)-fixed element to a strictly larger proper
\(J\)-fixed element. It is nonexpansive: on an open set where \(b\) and
\(c\) agree, their cores, interiors, unions with each fixed \(C_n\),
and the interior and union operations in (12) agree on that open set.

### 2.2. One scalar parameter supports this operation

The complete Boolean subalgebra generated by the \(J\)-fixed elements is
exactly \(j(\mathcal P(W))\). The positive-coordinate opens and their
complements isolate each point of \(W\) by external meets; joins then
give every subset. An automorphism of \(B\) commuting with \(J\) preserves
this subalgebra, since order automorphisms preserve all existing joins
and meets. It induces a homeomorphism of \(W\).

The specialization order of \(W\) is inclusion. Its top is \(\mathbb N\),
and its coatoms are \(\mathbb N\setminus\{n\}\). A homeomorphism therefore
induces a permutation of \(\mathbb N\); comparison with the coatoms
determines its action on every \(w\in W\). The induced base group has
cardinality at most \(2^{\aleph_0}\). Automorphisms fixing the base act
within the factors \(A\), preserving their endpoints and hence the core
operation in (11).

Every nonidentity induced base permutation moves \(2^{\aleph_0}\) points
of \(W\). Indeed, if it sends \(n\) to a different \(m\), there are
continuum many members of \(U\) containing \(n\) and omitting \(m\);
all are moved. Enumerate the nonidentity base permutations in an initial
cardinal order. At each stage choose a new point and its distinct image,
both outside the earlier selected pairs. Fewer than continuum many
points are forbidden at that stage, including when the continuum is
singular. Let \(d\subseteq W\) contain each selected source and none of
the selected targets. Its setwise stabilizer in the base group is trivial.

An automorphism fixing the one scalar \(j(d)\) must therefore fix the
base. Its factor actions preserve cores and fix every endpoint-valued
scalar, so they commute with \(K\). This proves the required support under
the full group, and hence under every subgroup.

### 2.3. The C fixed-point contradiction

The C lemma proved in
[Full-powerset Alexandroff algebras and Actuality](alexandroff-full-powerset-actuality.md),
Section 1, says that an admitted operation taking each proper persistent
proposition to a proper persistent proposition above it has a fixed point
among those propositions.

For completeness, write \(f\) for such an operation and set
\[
u(x)=f(\Box x)\land\neg\Box x,\quad
Q=\exists x^t\,u(x),\quad r=\Box Q.
\]
Every current \(u(x)\) is false: if \(\Box x=\top\) it is bottom;
otherwise \(f(\Box x)\) is proper persistent and hence false.
Thus \(r\) is proper persistent. Existential introduction gives
\(u(r)\leq Q\), and inflationarity gives
\[
f(r)=r\lor u(r)\leq Q.
\]
Persistence then gives \(f(r)=\Box f(r)\leq\Box Q=r\), so \(f(r)=r\).
No existential proposition is identified with an arbitrary Boolean join.

The stipulated admission rule admits (13), which has no such fixed
point. This is the contradiction. Neither a special ultrafilter, a more
homogeneous Boolean factor, nor a smaller symmetry group repairs that
admission rule. An interpretation admitting fewer operations is outside
the theorem.

## 3. A representative operation does not supply a completeness bound

This section extends the algebraic diagnostic in
[Functional Choice and current-instance hulls](functional-choice-current-instance-hulls.md).
It separates an admitted selection of representatives from the least-upper-bound
property needed for full Boolean Completeness.

### 3.1. What Functional Choice supplies

At a relational type \(\tau=\sigma_1\cdots\sigma_n t\), define
\[
R\sim S\ \equiv\
\forall\bar x\text{ current}\;(R[\bar x]=S[\bar x]).
\tag{14}
\]
The displayed identities compare whole scalar values. This is a Boolean
congruence, usually finer than mere current truth coextension, and it
need not be whole relational identity.

Functional Choice supplies Plenitude and Actuality. If \(w\) is an
Actuality witness, the admitted code
\[
c(R)=\lambda S^\tau.\,w\land(R\sim S)
\]
satisfies, for current \(R,T\),
\[
c(R)=c(T)\quad\Longleftrightarrow\quad R\sim T.
\tag{15}
\]
For the forward direction evaluate at \(S=R\). For the reverse direction,
the current universal statement saying that \(R\) and \(T\) have the same
equivalence class is true. Actuality makes that *whole universal
statement* necessary below \(w\); above \(\neg w\) both masked codes are
false. Intensionality yields the whole identity in (15).
There is no interchange of a universal quantifier and a box.

The code-image predicate \(\exists R(Y=c(R))\) is admitted.
Apply Functional Choice to its preimage graph, with output
\(\bot_\tau\) off the image. This graph is serial on the entire existing
type \(\tau t\), and its output type \(\tau\) is relational.
The resulting operation \(d\) gives \(q=d\circ c\) with
\[
qR\sim R,\qquad
qR=qS\ \Longleftrightarrow\ R\sim S,\qquad
q(qR)=qR
\tag{16}
\]
for current inputs.

The image \(F(a)\equiv\exists R(qR=a)\) carries induced Boolean operations,
such as \(q(a\land b)\), with zero \(q(\bot_\tau)\).
This is a quotient algebra on chosen representatives. Its order is the
order on equivalence classes of (14). The representative inclusion need
not preserve ambient order, complement or zero.

### 3.2. Even an ambient Boolean section and all individual adjoints do not suffice

Let \(\Omega=O\sqcup E\), with \(O,E\) countably infinite, and let
\[
B=\operatorname{FinCoFin}(\Omega),\qquad
C=\operatorname{FinCoFin}(O),\qquad
\pi(b)=b\cap O.
\]
Choose a bijection \(f:O\to E\). Then
\[
s(Q)=Q\cup f[Q]
\]
is an ambient Boolean section of \(\pi\). The operation \(s\pi\) is Boolean,
monotone and idempotent. It selects one representative for each fibre.
Every visible evaluation \(\operatorname{ev}_o:B\to2\), \(o\in O\),
has a right adjoint
\[
0\longmapsto\Omega\setminus\{o\},\qquad
1\longmapsto\Omega,
\]
and a left adjoint \(0\mapsto\varnothing,\ 1\mapsto\{o\}\).
Agreement of all visible evaluations is exactly equality of \(\pi\)-images.

Nevertheless their common zero kernel is
\[
\ker\pi=\operatorname{Fin}(E),
\]
which has no greatest member. The visible singleton family
\(\{\{o\}:o\in O\}\) has no join in \(B\): an upper bound must contain
\(O\) and all but finitely many points of \(E\), and deleting one of those
remaining points gives a smaller upper bound.

This is an ordinary Boolean-algebra example. It supplies no full typed
hierarchy or interpretation of C, and therefore is not a countermodel to
Functional Choice implying Boolean Completeness. It shows that an ambient
Boolean representative operation, even together with every individual
evaluation adjoint, does not establish the needed common bound.

### 3.3. A joint adjoint asks for precisely the missing hull

Return to (14) and let
\[
K_\tau=\{R:\forall\bar x\text{ current},\ R[\bar x]=\bot_t\}.
\]
Suppose an admitted \(g\) satisfies the joint adjunction
\[
q(R)\leq_F a\quad\Longleftrightarrow\quad R\leq g(a).
\tag{17}
\]
At \(a=0_F\), this makes \(g(0_F)\) the greatest element of \(K_\tau\).
It bounds \(K_\tau\); substituting \(R=g(0_F)\) shows that it belongs to
\(K_\tau\) as well.

Conversely, if \(k=\max K_\tau\), then
\[
g(a)=a\lor k
\]
supplies (17). Indeed \(q(R)\leq_F a\) means
\(R\land\neg a\in K_\tau\), which is equivalent to \(R\leq a\lor k\).
Thus adding a joint right adjoint does not bridge the gap: it asserts the
missing greatest kernel element itself.

By the existing current-instance-hull result, \(\neg k\) is precisely the
least relation necessarily containing all current tuple haecceities.
The type shift in that result remains essential: a hull at \(\tau t\)
supplies Boolean Completeness at \(\tau\); a same-type shortcut is not
being asserted.

## Relation to the existing results and attribution

The full-powerset Alexandroff theorem already has its own
[proof](alexandroff-full-powerset-actuality.md). The
[unique-root-retraction theorem](unique-root-retractions-plenitude-completeness.md)
and the [current-instance-hull reductions](functional-choice-current-instance-hulls.md)
also retain their separate hypotheses and proofs. None is counted again here.

Section 1 builds on Daniel Kodsi's supported-product constructions and the
canonical-history and disjoint-increment methods used for choice and
completeness. The additional restrictions proved here are the precise
marker-family obstruction with arbitrary higher admission, the finite
proper-bound and matching argument, and the uniform support-threshold
consolidation. The elementary finite-matching fact carries no novelty claim.

Section 2 combines the Scott-ultrafilter topology with the persistent
fixed-point method already credited in the Alexandroff write-up. Its
additional step is a scalar parameter fixing the whole base automorphism
group, which forces the obstructing operation to be admitted under the
specified full support rule.

Section 3 uses the Actuality-masked quotient-code argument and the previously
recorded evaluation-adjoint and hull reductions. The split finite/cofinite
diagram checks the failed inference even with an ambient Boolean section
and both adjoints for every individual evaluation.

These arguments were developed by Daniel Kodsi, with ChatGPT assistance,
30 October 2026. They do not settle unrestricted Functional Choice versus
Boolean Completeness, scalar Boolean Completeness with Relational Choice
versus Actuality, or the separate same-type Zorn question.
