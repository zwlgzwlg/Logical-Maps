# Analytic Necessitism and Transversal give Necessity of Arithmetic

GPT-6 Astra, prompted by Daniel Kodsi, 30 October 2026. The proof combines
*Current Transversal supplies a literal real field*, §§7–8, and
*Nonvacuous Analytic Necessitism forces Arithmetic Necessitism*, “Arithmetical truth
corollary” (both unpaginated). Goodsell's arithmetic guard lemma and the
given-field stability proof of Claude Fable 5.1, prompted by Zachary
Goodsell, are included below with their original roles preserved.

## 1. Exact target and the current field-existence lemma

Work in C. Assume the current Analytic Necessitism and Transversal schemas.
Fix an external counting type \(\sigma\) and a native arithmetical
sentence \(A_\sigma\). Put

\[
\nu=(\sigma t)t,\qquad \rho=\nu t,\qquad
I_\sigma=\Diamond I^*_\sigma.
\]

The target is exactly

\[
\Box(I_\sigma\to A_\sigma)\ \lor\
\Box(I_\sigma\to\neg A_\sigma). \tag{1}
\]

It does not assume \(\Box I^*_\sigma\). Types and arithmetic sentences
are external schema indices.

The current cut construction in
[[analytic-necessitism-and-transversal-imply-arithmetic-necessitism]],
§§1–3, proves the discharged C theorem

\[
I^*_\sigma\land\mathrm{Tr}_{\nu}
\ \longrightarrow\ \exists\mathfrak R\,
                         \operatorname{Real}_{\rho}(\mathfrak R). \tag{2}
\]

It uses one current Transversal witness, of type \((\nu t)t\), selecting
literal representatives of admitted rational cuts. Its relational field
operations and its least-upper-bound proof cover every admitted bounded
family. No future correctness of the selector is needed. We use (2)
only at the current evaluation point.

## 2. The arithmetic guard facts are theorems of C

Goodsell's Lemma 5, reproduced in
[[countable-boolean-completeness-implies-necessity-of-arithmetic]], gives

\[
I_\sigma\to I^*_\sigma. \tag{3}
\]

This part uses no Countable Boolean Completeness. Here is the guard
argument. Canonical numberhood is persistent by its least-inductive
definition. Double number induction proves

\[
m,n\in N_\sigma\land m\ne n
\ \longrightarrow\ \Box(I^*_\sigma\to m\ne n).
\]

The zero case uses non-successorhood, and the successor step uses
injectivity under \(I^*_\sigma\), with persistence of numberhood.
If current \(I^*_\sigma\) fails by a successor being zero, numberhood
persistence and necessary identity preserve that obstruction. If it
fails by equal successors of distinct numbers, necessary identity
preserves their successor equality, while the displayed conditional
distinctness says that any future \(I^*_\sigma\) would preserve their
difference. Thus \(\neg I^*_\sigma\to\Box\neg I^*_\sigma\), which
is (3). All these statements are discharged C theorems and can be
necessitated.

Also, S4 gives

\[
\neg I_\sigma\to\Box\neg I_\sigma: \tag{4}
\]

indeed \(\Diamond I_\sigma\to I_\sigma\) is
\(\Diamond\Diamond I^*_\sigma\to\Diamond I^*_\sigma\).

## 3. A given rigid real field fixes arithmetic truth

Suppose, at an admitted host \(\tau\), that a tuple \(\mathfrak R\)
satisfies \(\operatorname{RigidStr}(\mathfrak R)\) and
\(\Box\operatorname{Real}_\tau(\mathfrak R)\). We prove (1) from this
given tuple without assuming \(\Box I^*_\sigma\).

Write \(B=N_{\mathfrak R}\) for its number property and define the
relational successor

\[
\operatorname{Next}(y,z):=By\land Bz\land
                         +_{\mathfrak R}(y,1_{\mathfrak R},z).
\]

Under current Real, its least-inductive number property and the ordered
field axioms give the Peano conditions for \((B,0_{\mathfrak R},
\operatorname{Next})\): successor is total, functional and injective,
and cannot be zero. The last assertion follows by induction that all
members of \(B\) are nonnegative and \(0<1\).

### Current matching and preservation of arithmetic

Under **current** \(I^*_\sigma\) and Real, define
\(E^{\nu\tau t}\) as the intersection of all admitted relations
containing \((0_\sigma,0_{\mathfrak R})\) and closed under

\[
E(x,y)\land\operatorname{Next}(y,z)
              \ \Longrightarrow\ E(\operatorname{Suc}_\sigma x,z).
\]

This means one impredicative lambda formula, not an external intersection
assumption. Its base pair and closure follow from its defining universal
quantifier. For its unfolding, let \(U\) consist of the base pair and
one-step paired successors of \(E\). Closure gives \(U\subseteq E\);
this inclusion makes \(U\) itself pair-inductive, so minimality gives
\(E\subseteq U\). These are pointwise implications, with no inference
from current coextension to identity of arbitrary relations.

The product \(N_\sigma\times B\) is pair-inductive, hence supports
\(E\). Number induction gives a unique image of each canonical number:
at zero, the successor alternative of the unfolding is impossible; at a
successor, injectivity identifies the predecessor, and the induction
hypothesis and functionality of Next identify the image. The range
predicate is inductive in \(B\), so it contains every \(B\)-member.
Induction in \(B\), using injectivity of Next and the zero case, gives
unique preimages. Thus \(E\) is a current bijection preserving zero and
successor. These inductions apply to all admitted numbers, including
nonstandard ones, and use arbitrary typed parameters.

It also preserves the native Sum and Prod graphs. For a fixed first
argument \(m\), the canonical sum graph is the least pair relation
starting at \((0,m)\) and closed under successor in both coordinates.
The product graph starts at \((0,0)\) and advances its second coordinate
by addition of \(m\) when its first coordinate advances by one. Pull an
admitted relation on \(B\) back through \(E\) by lambda abstraction;
push a canonical relation forward by existential quantification through
\(E\). Current bijectivity transfers these base and closure clauses in
both directions. Their universal defining clauses therefore transfer
Sum and Prod. Internal induction on \(B\) identifies the resulting
graphs with restricted field addition and multiplication. In particular,
the product base pair is \((0,0)\), not \((0,m)\).

Translate \(A_\sigma\) to a first-order analytical sentence
\(A^{\mathfrak R}\): number quantifiers become field quantifiers guarded
by \(B\), arithmetic predicates become the corresponding field graphs,
and each successor term is eliminated by finitely many relational
successor equations. Numberhood, equality and zero are preserved as well.
Finite induction on the syntax gives the **discharged** C theorem

\[
\forall\mathfrak R\,
 [I^*_\sigma\land\operatorname{Real}_\tau(\mathfrak R)
       \to(A_\sigma\leftrightarrow A^{\mathfrak R})]. \tag{5}
\]

No modal persistence of \(E\) is needed for this current categoricity
argument. No numerical operation of forbidden output type is extracted.

Necessitate (5), instantiate the fixed tuple by boxed universal
instantiation, and use \(\Box\operatorname{Real}_\tau(\mathfrak R)\).
Necessitate (3) as well. Modal K then gives

\[
\Box[I_\sigma\to
              (A_\sigma\leftrightarrow A^{\mathfrak R})]. \tag{6}
\]

### Stability on the given field

We use the argument of Lemmas 1–2 of
[[analytic-necessitism-implies-necessity-of-analysis]], composed by
Claude Fable 5.1 (Anthropic), prompted by Zachary Goodsell, 23 October
2026, after Barton–Goodsell and Bacon.

For a rigid field relation \(S\), a true atomic instance persists.
If \(S\bar a\) is false at field elements \(\bar a\), every tuple
satisfying \(S\) differs from \(\bar a\) in a coordinate; necessary
distinctness of field members makes that difference necessary.
Inextensibility of \(S\), applied to the complement of the haecceity of
\(\bar a\), gives \(\Box\neg S\bar a\). Equality is persistent by
necessary identity, and its negation by the carrier's ND clause.

An induction on first-order analytical formulas now preserves both
truth and falsity. Boolean steps use K. If
\(\forall x\in X\,\varphi(x,\bar a)\) is true, the induction hypothesis
gives \(\forall x(Xx\to\Box\varphi(x,\bar a))\); inextensibility of
\(X\) gives the necessary universal statement, including all future
members. If it is false, a current counterexample persists in \(X\)
and its negated formula persists by induction, yielding the necessary
counterexample. No exchange of an arbitrary universal quantifier with
Box is used.

At the sentence \(A^{\mathfrak R}\), excluded middle therefore yields
\(\Box A^{\mathfrak R}\lor\Box\neg A^{\mathfrak R}\).
Combine either sign with (6) to obtain the corresponding disjunct of
(1). This proves the given-field arithmetic-truth lemma.

## 4. Obtain the reference field with the exact current premises

Return to current ANA and Transversal, and split on current \(I_\sigma\).

If it holds, (3) supplies current \(I^*_\sigma\). Apply (2) using the
one Transversal instance at \(\nu\); a current real field at \(\rho\)
exists and is therefore possible. ANA at **that same host** supplies a
rigid necessarily-real tuple there. Apply §3 with \(\tau=\rho\) to
obtain (1). The chosen tuple is eliminated because (1) does not mention it.

If \(I_\sigma\) is false, (4) makes it necessarily false. Both guarded
disjuncts of (1) then hold vacuously.

These cases prove the required instance. Since the counting type and
arithmetical sentence were arbitrary external indices, this is the full
Necessity of Arithmetic schema. The argument never necessitates ANA,
Transversal, a current selector or an existential witness choice. Its
truth guard remains \(I_\sigma\) inside each box; the separate
Arithmetic Necessitism result retains its own \(\Box I^*_\sigma\) guard.
