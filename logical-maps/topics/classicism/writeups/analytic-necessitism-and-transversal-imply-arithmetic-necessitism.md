# Transversal representatives connect analytic and arithmetic necessitism

OpenAI Codex, prompted by Daniel Kodsi, 30 October 2026. The current cut construction and its
composition are given below. The fixed Peano reference lemma is from
GPT-6 Astra, prompted by Daniel Kodsi, *Finite-type necessitism*, companion
proof notes, 29 October 2026, §6 (unpaginated), and is proved in §4 below.
Christopher Sun's Transversal principle supplies current coextension representatives.

## 1. Exact types and the current existence lemma

For an externally fixed source type \(\sigma\), put

\[
\nu_\sigma=(\sigma t)t,\qquad \rho_\sigma=\nu_\sigma t.
\]

Let \(\mathrm{Tr}_\alpha\) denote the native Transversal **instance**
whose properties have type \(\alpha t\): a property of properties selects
exactly one literal entity from each current coextension class on
\(\alpha\). The following is a C theorem for each \(\sigma\):

\[
 I^*_\sigma\land\mathrm{Tr}_{\nu_\sigma}
 \ \longrightarrow\
 \exists\mathfrak R\,\operatorname{Real}_{\rho_\sigma}(\mathfrak R).
\tag{1}
\]

The host on the right is explicit. There is no quantifier over types.
Neither the guard nor Transversal is boxed in (1). Real has the native
definition: literal equality, an antisymmetric linear order, functional
**relational graphs** for field operations, completeness for every admitted
bounded subproperty of its carrier, and its least inductive number property.

Write \(N=\mathbb N_\sigma\). Its canonical leastness already gives
induction over all admitted predicates. With \(I^*_\sigma\), zero is
not a successor and successor is injective. Thus it is a current Peano
structure at the host \(\nu_\sigma\). The usual least recursion graphs
give current addition, multiplication and finite coding. This uses the
ordinary canonical-arithmetic interpretation, not an external assumption
that the numbers are standard.

For explicit rational codes, use the injective numerical pairing graph
\(c=(a+b)^2+a\). All displayed arithmetic expressions abbreviate finite
compositions of the canonical Sum and Prod **relations**. If \(u=a+b\),
the code lies in \([u^2,u^2+u]\); these intervals are disjoint for different
\(u\), and the value within one interval determines \(a\), then \(b\).
This is an internal Peano proof, with no operation object extracted.

A raw rational code is a nested pairing code of \((a,b,d)\), representing
\((a-b)/(d+1)\). Two triples are equivalent exactly when

\[
a(d'+1)+b'(d+1)=a'(d+1)+b(d'+1).
\]

Take as \(Q\subseteq N\) the valid codes that are least in their
classes. Each class is an admitted nonempty numerical predicate, so
internal least-number induction gives a literally unique least code.
Cross-multiplication defines order. Fraction addition, multiplication,
negation and reciprocal are relational graphs followed by this least-code
normalization. Their ordinary laws follow by internal cross-multiplication.
A positive denominator has a predecessor by the Peano theorem; it is
introduced through its successor graph. No choice of quotient objects
or operation-valued representatives is required.

This internal rational field has the precise bound needed below: for
rational \(q\) and \(\epsilon>0\), some internal natural \(m\) satisfies
\(m\epsilon>q\). A positive fraction \(a/b\), with \(b\ge1\), is below
\(a+1\); apply this observation to \(q/\epsilon\). This does not claim
that the numbers are externally standard or the rational field externally
Archimedean. Induction is available for admitted predicates with arbitrary
typed parameters, including a cut parameter.

## 2. Literal cut representatives and field operations

Choose a witness \(F^{(\nu_\sigma t)t}\) to
\(\mathrm{Tr}_{\nu_\sigma}\). Define \(\operatorname{Cut}(A)\) to
say that \(A^{\nu_\sigma t}\) is supported on \(Q\), nonempty,
proper, downward closed in the rational order, and has no greatest member.
Put

\[
X(A):=F(A)\land\operatorname{Cut}(A).
\]

For each admitted rational-cut predicate \(D\), Transversal gives one
and only one \(A\in X\) agreeing with \(D\) on the entire host
\(\nu_\sigma\). Conversely any two \(X\)-members with equal cut
extensions are **identical**, by uniqueness in \(F\). This is the step
that cannot be replaced by mere comprehension in an intensional model.
It is current equality, not a claim that coextensive arbitrary properties
are identical or necessarily coextensive.

Define \(A\leq_X B\) by cut inclusion, with both arguments in \(X\).
This order is antisymmetric because of literal representative uniqueness.
The predicates of rationals below 0 and 1 have unique representatives;
take these as the two field constants. Addition is the supported graph
specifying that the result represents the lower cut

\[
q\longmapsto Qq\land
 \exists r,s\in Q\,[Ar\land Bs\land q<r+s].
\tag{2}
\]

Additive inverse represents
\(q\mapsto Qq\land\exists r\in Q(\neg Ar\land q<-r)\).
For nonnegative cuts the product represents

\[
q\longmapsto Qq\land
 \bigl(q<0\ \lor\
   \exists r,s\in Q\,[0<r\land0<s\land Ar\land Bs\land q<rs]\bigr).
\tag{3}
\]

Use additive inverse for the remaining sign cases. For a positive cut,
its reciprocal represents
\(q\mapsto Qq\land[q<0\lor\exists r\in Q(0<r\land\neg Ar\land q<1/r)]\);
negative reciprocals follow by sign. These are finite admitted formulas.
Every specified output cut has exactly one representative. Consequently
their graphs are total and functional on \(X\). No operation-valued
choice or Plenitude is used.

The internal small-gap argument is essential. Given an admitted cut
\(A\) and rational \(\epsilon>0\), choose \(a\in A\), \(b\notin A\),
put \(\delta=\epsilon/2\), and find an internal natural \(m\) with
\(a+m\delta>b\). The admitted predicate \(a+n\delta\notin A\)
has a least positive member. Its predecessor gives \(l\in A\) and
\(u\notin A\) with \(u-l=\delta<\epsilon\). The arithmetic values
are expressed by their unique relational graphs. Thus induction uses
an admitted predicate with parameter \(A\), rather than an external
enumeration or a sequence of cut-valued outputs.

Write \(L_r\) for the rational principal cut below \(r\). If
\(l\in A,u\notin A,m\in B,v\notin B\), the raw formulas give

\[
L_{l+m}\subseteq\operatorname{AddRaw}(A,B)\subseteq L_{u+v},
\qquad
L_{-u}\subseteq\operatorname{NegRaw}(A)\subseteq L_{-l}.
\]

For positive lower endpoints, the product bounds are \(L_{lm}\) and
\(L_{uv}\), and the reciprocal bounds are \(L_{1/u}\) and \(L_{1/l}\).
These are weak principal-cut inclusions: for example \(-u\) need not
belong to the negative cut. Add arbitrarily small rational slack before
requiring strict endpoint membership. Zero inputs give the zero cut in
the nonnegative product formula; strictly positive inputs have positive
members and positive outside bounds, which make the reciprocal a
nonempty proper rounded cut. Negation supplies the remaining sign cases.

For completeness about the field laws, the common-approximation invariant
is as follows. Every fixed finite expression in the raw operations has
rational brackets of arbitrarily small width, obtained from sufficiently
small brackets for its finitely many inputs. On a rationally bounded
region \(|x|,|y|\le M\), sum error is at most \(2\delta\) and product
error at most \((2M+\delta)\delta\). For inversion first fix a positive
rational lower bound \(d\); reciprocal error is at most \(\delta/d^2\).
Signed cases follow from negation. These are finite rational inequalities,
valid internally. Finite induction on an expression chooses sufficiently
small input widths; it does not form an infinite approximation sequence.

For each field identity, evaluate both sides on the same rational
approximants. Rational algebra makes the centers agree, and the preceding
bounds put the two output cuts in a common arbitrarily narrow bracket.
If they differed, choose \(q\) in one and not the other, then \(q'>q\)
in the first by roundedness. A common bracket \(L_l\subseteq A,B\subseteq
L_u\) with \(u-l<q'-q\) would force \(l\le q<q'<u\), a contradiction.
Thus the outputs are currently coextensive; selected-representative
uniqueness makes them literally identical. This proves the ring laws,
additive inverse and the nonzero reciprocal law. Inclusion is total on
cuts; addition and positive multiplication preserve it directly, and
cancellation gives strictness. The positive-member test gives positive
products, so these are the ordered-field laws.

The explicit coding and weak-bracket estimates are from GPT-6 Astra,
prompted by Daniel Kodsi, *Current Transversal supplies a literal real
field*, 30 October 2026, §§2–5 (unpaginated). They refine the details of
this current construction without changing its hypotheses or types.

## 3. Completeness for every admitted subproperty

Let \(Y^{\rho_\sigma t}\) be any admitted nonempty subproperty of
\(X\), bounded above by \(B\in X\). Comprehension forms

\[
U(q):=Qq\land\exists A\,[XA\land YA\land Aq].
\tag{4}
\]

This is a cut: it is nonempty because \(Y\) is; it is proper because
its union is contained in the proper upper cut \(B\); downward closure
and absence of a greatest element follow from a witnessing member cut.
Transversal supplies its unique representative \(C\in X\).
Each \(Y\)-member is below \(C\), and every upper bound includes (4),
so \(C\) is its least upper bound. The argument covered an **arbitrary
admitted** \(Y\), not just a definable or externally listed family.

Define the field's number predicate by the least subproperty of \(X\)
containing its zero and closed under its addition-by-one graph. The
impredicative comprehension formula supplies exactly that property.
It is the numberhood clause of native Real. With the preceding supported
order and operation graphs, we have a full tuple satisfying
\(\operatorname{Real}_{\rho_\sigma}\), proving (1).

All representatives were requested one existential witness at a time.
Transversal itself supplies their common extensional carrier, so neither
Relational Choice nor a uniform choice operation is hidden in the proof.
All conclusions in (1) are current; no rigidity or future fullness has
yet been claimed.

## 4. The fixed Peano reference lemma, with proof

This section spells out the source's transport argument. A carrier is
*fixed* when it is rigid and its current members are necessarily distinct.
Let \((K,o,S)\) be a presentation at an admitted carrier type \(\kappa\),
with \(K\) fixed, \(S\) rigid, and
\(\Box\operatorname{Peano}(K,o,S)\). Peano here includes support of
\(S\) on \(K\), a unique successor for each member, zero not a successor,
injectivity of successor, and induction for every admitted predicate.
Fix \(\sigma\) and assume \(\Box I^*_\sigma\).

Define \(J^{\kappa\nu_\sigma t}\) to be the least relation containing
\((o,0_\sigma)\) and closed under simultaneous successors. Explicitly,
\(J(a,b)\) says that every admitted \(R^{\kappa\nu_\sigma t}\) satisfying

\[
R(o,0_\sigma)\ \land\
\forall x,x',y\,[R(x,y)\land S(x,x')
                 \to R(x',\operatorname{Suc}_\sigma y)]
\]

also satisfies \(R(a,b)\). Comprehension admits this relation and its
boxed-instance predicate. Leastness, base membership and successor
closure follow directly by universal instantiation. In particular,
base membership is a universally closed theorem of the definition;
its necessitation uses the same parameter \(o\), without assuming a
separate rigidity predicate for an individual.

The predicate \(\lambda a,b\,\Box J(a,b)\) contains the base pair.
If \(\Box J(a,b)\) and \(S(a,a')\), persistence of \(S\) gives
\(\Box S(a,a')\), and the necessary closure theorem for \(J\) gives
\(\Box J(a',\operatorname{Suc}_\sigma b)\). Thus this predicate is
closed under simultaneous successors. Leastness gives
\(J(a,b)\to\Box J(a,b)\). This proves weak persistence from the
persistence of \(S\). Necessitate that **closed conditional theorem**
and use the necessary persistence of \(S\): \(J\) is persistent in
the map's full, boxed sense.

The ordinary second-order Peano matching argument gives the following
facts. The product \(K\times N_\sigma\) is closed under the matching
operator, so \(J\) is supported on it. Induction on \(K\) gives an
image for each of its members, and induction on \(N_\sigma\) gives a
preimage for each of its members. For uniqueness, the base pair cannot
be confused with a successor pair; in the successor step, injectivity
on both sides reduces a possible pair of matches to the preceding
matches. Induction therefore gives uniqueness on both sides. This is
the usual second-order proof that the least simultaneous-successor
matching is a bijection. It uses the admitted matching and comparison
predicates, so it applies to these Henkin Peano structures without an
external standardness assumption. The proof is a closed theorem with
the two Peano conditions as hypotheses. Since both hypotheses are
necessary, necessitation and K make support, totality, functionality
and bijectivity necessary as well.

Here is the needed functional-graph step, including inextensibility.
Suppose \(D\) is rigid, \(L\) persistent and necessarily a total
functional relation with domain \(D\). Assume a test relation \(Q\)
satisfies \(\forall a,b(L(a,b)\to\Box Q(a,b))\). For a current
\(a\in D\), take its unique current \(L\)-image \(b\). Persistence
gives \(\Box L(a,b)\), the test hypothesis gives \(\Box Q(a,b)\),
and necessary functionality yields

\[
\Box\forall b'\,[L(a,b')\to b'=b],
\qquad
\Box\forall b'\,[L(a,b')\to Q(a,b')].
\]

Apply inextensibility of \(D\) to
\(T(a):=\forall b(L(a,b)\to Q(a,b))\). With necessary support,
this yields \(\Box\forall a,b(L(a,b)\to Q(a,b))\). It proves weak
inextensibility of \(L\). Rigidity of \(D\), persistence of \(L\),
and the boxed functional-domain condition imply their own necessity
by modal 4. Necessitating the proved conditional therefore gives full
inextensibility. Hence \(L\) is rigid. The argument chooses only an
individual existential witness for a fixed \(a\), not a choice function.

Apply this step to \(D=K\) and \(L=J\). Its range
\(B(b):=\exists a\,J(a,b)\) is rigid: persistence follows from a
witness; for inextensibility pull any test \(Q(b)\) back to the
relation \(\lambda a,b\,Q(b)\) and apply inextensibility of \(J\).
Necessary surjectivity gives
\(\Box\forall b(B(b)\leftrightarrow N_\sigma b)\).
In C this is \(B\le N_\sigma\) and \(N_\sigma\le B\), so
antisymmetry gives **literal identity** \(B=N_\sigma\). Rigidity of
\(N_\sigma\) now follows; it was not assumed in the identification.

For completeness, necessary distinctness of the canonical numbers
follows already from \(\Box I^*_\sigma\). Canonical numberhood is
persistent: the predicate \(\lambda n\,\Box N_\sigma n\) contains
zero and is successor-closed by the necessary least-inductive laws,
so leastness gives its weak persistence and necessitation gives the
full version. Induct on \(n\in N_\sigma\) to prove
\(\forall m\in N_\sigma(n\ne m\to\Box(n\ne m))\).
Every number is zero or a successor. Necessary non-successorhood
handles the zero case; in the successor case necessary injectivity
and the induction hypothesis separate the predecessors. Necessary
identity preserves each chosen predecessor equation, and persistence
of numberhood keeps its parameters within the necessary Peano axioms.
Thus the required necessary distinctness holds with no global ND axiom.

Finally, a rigid necessarily-real tuple supplies this reference.
Its number predicate \(K\) is rigid by RigidStr and inherits ND from
the fixed real carrier. Its successor is the supported addition-by-one
graph on \(K\); persistence follows from the rigid field operation
and number predicate. The boxed Real condition makes this graph
necessarily total and functional, so the functional-graph step makes
it rigid. The ordinary real-field theorem gives Peano's axioms for the
least inductive number subproperty; necessitating that theorem and
using boxed Real gives \(\Box\operatorname{Peano}(K,o,S)\).
This proves the fixed-reference lemma from precisely the stated
hypotheses, without a represented-power or Transversal assumption.

## 5. The map edge

Now assume ANA and the full native Transversal schema. To prove Arithmetic
Necessitism, fix any \(\sigma\) and assume its unchanged guard
\(\Box I^*_\sigma\). By T, current \(I^*_\sigma\) holds; the
Transversal instance in (1) gives a current real structure at
\(\rho_\sigma\). It is possible, so the ANA instance at exactly
that host supplies a rigid necessarily-real structure. Section 4
supplies its fixed Peano reference and transports rigidity and
necessary distinctness to \(N_\sigma\), under precisely that guard.
Since \(\sigma\) was arbitrary, this is the existing Arithmetic
Necessitism schema:

\[
\mathrm{ANA}+\mathrm{Transversal}\longrightarrow\mathrm{AR}.
\]

The fixed-reference lemma and native definitions are inherited. The
current Transversal-to-cut construction and this map composition are
due to OpenAI Codex, prompted by Daniel Kodsi, 30 October 2026.

For the symmetric Cohen arithmetic-growth model, the
[separate consequence supplement](symmetric-cohen-arithmetic-growth-consequences.md)
spells out the stronger guarded conclusions \(\Box\neg\mathrm{Tr}_{(et)t}\)
and \(\Box\neg\mathrm{Actuality}\), and the exact schema equivalence
between ANA, SOAN and NoReal relative to a failed AR instance.

The same current existence lemma also gives
[[analytic-necessitism-and-transversal-imply-necessity-of-arithmetic]].
That proof retains the different arithmetic-truth guard inside each box.
