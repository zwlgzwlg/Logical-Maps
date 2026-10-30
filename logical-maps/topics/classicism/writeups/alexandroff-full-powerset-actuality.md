# Full-powerset Alexandroff scalars force Actuality

GPT-6 Astra, prompted by Daniel Kodsi. 30 October 2026.

**Theorem.** Work in external ZFC. Suppose a C-valid typed interpretation
has actual Boolean algebra of whole propositions exactly the full powerset
of a nonempty set P. Suppose its necessity operation is the downset
interior of a preorder on P:

\[
I(A)=\{x\in P:\mathord\downarrow x\subseteq A\}.
\tag{1}
\]

Then the preorder quotient has a greatest class, and the interpretation
satisfies current Vicinity and Actuality. Higher types may be restricted;
ordinary C lambda and quantifier closure suffices.

Consequently Actuality also holds if the scalar Boolean algebra is
**externally complete and atomic** and necessity preserves **every
external meet**. Section 6 proves the required representation. These
external hypotheses are stronger than native Boolean Completeness and
Atomicity: the proof needs a particular externally chosen scalar subset,
and the representation needs an arbitrary external intersection.

## 1. A fixed-point lemma of C

Write \(O(p)\) for \(p=\Box p\), and \(O^-(p)\) for
\(O(p)\land p\ne\top\). Order is the whole-proposition Boolean order.
A proper persistent proposition is currently false: if \(p=\Box p\)
were true, then \(\Box p\) would be true, which says \(p=\top\).
Finite joins of persistent propositions are persistent by the S4 laws.
Finite joins of proper persistent propositions are therefore proper,
since their disjuncts are currently false.

We use the following fixed-point lemma from *Persistent fixed points and
cofinal chains*, Section 1; its proof is included here.

**Lemma.** If an admitted operation \(f:tt\) satisfies, currently,

\[
O^-(p)\ \Longrightarrow\ O^-(f(p))\land p\le f(p),
\tag{2}
\]

then it has a fixed point in \(O^-\).

Define admitted terms

\[
u(x)=f(\Box x)\land\neg\Box x,\qquad
B=\exists x^t\,u(x),\qquad r=\Box B.
\]

For every current x, \(\Box x\) is persistent. If it is top,
\(u(x)\) is bottom. Otherwise (2) makes \(f(\Box x)\) proper
persistent and hence false. Thus every current \(u(x)\) is false,
so B is false and r is proper persistent.

Unconditional existential introduction gives \(u(r)\le B\).
Also \(r\le B\) and \(\Box r=r\). Applying (2) at r gives

\[
f(r)=r\lor(f(r)\land\neg r)=r\lor u(r)\le B.
\]

Since \(f(r)\) is persistent, monotonicity of necessity yields

\[
f(r)=\Box f(r)\le\Box B=r.
\]

Together with \(r\le f(r)\), this proves equality. The proof uses
the inequalities supplied by existential introduction, without treating
the material existential B as an algebraic join. Monotonicity of f,
Boolean Completeness and Choice are not premises of the lemma.

## 2. C forces the external preorder to be directed

The persistent scalar elements of (1) are precisely the downsets. If
x,y had no common upper bound, the two proper downsets

\[
P\setminus\mathord\uparrow x,
\qquad P\setminus\mathord\uparrow y
\]

would have union P. Scalar fullness admits both as propositions. This
contradicts Section 1's finite-join property. Thus the preorder, and its
partially ordered quotient, are directed.

We first work with a directed partial order P. Section 5 treats the
quotient of a preorder.

## 3. A cofinal coloring without well-foundedness

Suppose P has no greatest element. Let \(\kappa\) be the least
cardinality of an external cofinal subset, and fix one such subset T.
It is infinite: a finite cofinal set in a directed order has a common
upper bound, which would be greatest. Regard \(\kappa\) as its
initial ordinal, and partition it into sets \(C_0,C_1\), each of
cardinality \(\kappa\). Choose a schedule
\((t_\alpha)_{\alpha<\kappa}\) whose values on each \(C_i\)
enumerate T.

Recursively choose \(s_\alpha\). The earlier set
\(\{s_\beta:\beta<\alpha\}\) has cardinality less than
\(\kappa\), so it is not cofinal. Choose \(x_\alpha\) below
none of its members. Directedness gives \(s_\alpha\) above both
\(x_\alpha\) and \(t_\alpha\). Then

\[
s_\alpha\not\le s_\beta\quad(\beta<\alpha).
\tag{3}
\]

Each of the two subfamilies indexed by \(C_i\) is cofinal, since
it dominates the corresponding enumeration of T. Define the external
ordinal rank

\[
r(p)=\min\{\alpha<\kappa:p\le s_\alpha\}.
\]

It is defined everywhere and is monotone. Equation (3) gives
\(r(s_\alpha)=\alpha\). Consequently the color

\[
b=\{p\in P:r(p)\in C_0\}
\tag{4}
\]

and its complement are both cofinal above every point of P.

The argument also covers singular \(\kappa\): for every
\(\alpha<\kappa\), \(|\alpha|<\kappa\) because
\(\kappa\) is an initial ordinal. No increasing cofinal chain
or regularity assumption was used. The choices and rank are external;
only the final subset b will be needed as a scalar parameter.

## 4. The color gives a forbidden admitted operation

Full scalar powerset admission supplies b. Ordinary lambda closure
therefore supplies the operation

\[
h_b(U)=I(U\cup b)\cup I(U\cup(P\setminus b)),
\tag{5}
\]

the interpretation of
\(\lambda p.\,\Box(p\lor b)\lor\Box(p\lor\neg b)\).
We show that it strictly increases every proper downset and remains
a proper downset, contradicting Section 1.

Let U be a proper downset. Choose x outside U with least rank among
the ranks attained outside U. If \(y\le x\) also lies outside U,
monotonicity gives \(r(y)\le r(x)\), while the choice of x gives
the reverse inequality. Thus every such y has the same rank and color
as x. For the color c containing x,

\[
\mathord\downarrow x\subseteq U\cup c.
\]

It follows that \(x\in I(U\cup c)\subseteq h_b(U)\), while
\(x\notin U\). Every downset U is contained in both interiors
in (5), so \(U\subsetneq h_b(U)\). The selection uses a least
ordinal rank, not a minimal point of \(P\setminus U\); P need
not be well founded.

To check properness, start with any x outside U. Choose
\(y\ge x\) in b and \(z\ge y\) outside b, using the two
cofinal colors. Both y and z remain outside U because U is a downset.
The point z is outside \(I(U\cup b)\), since z itself is in
neither U nor b. It is also outside \(I(U\cup(P\setminus b))\),
since its predecessor y is in neither U nor \(P\setminus b\).
Thus z is outside \(h_b(U)\). Its value is a proper downset,
being the union of two downsets.

Hence the admitted operation (5) preserves and is inflationary on all
proper persistent propositions, but has no fixed point there. Section 1
rules it out. The directed partial order P must have a greatest element.

## 5. From a greatest point or class to Actuality

In the partially ordered case let m be greatest. Then
\(P\setminus\{m\}\) is a proper downset and is currently false.
Its complement \(\{m\}\) is therefore true. It is a Boolean atom
of the scalar powerset. For any currently true q, its intersection with
this true singleton is true and hence nonempty. Thus
\(\{m\}\subseteq q\). The singleton witnesses Actuality: it is
a true proposition below every current truth.

For a preorder, pass externally to its quotient by mutual comparability.
Downsets are exactly inverse images of quotient downsets. If the quotient
had no greatest element, pull back its color (4); Section 4 would give
the same forbidden operation on P. Thus there is a greatest equivalence
class M. Its complement g is the greatest proper downset, hence the
greatest proper persistent proposition. It is false, so
\(v=\neg g\) is true.

For any current truth q, \(\Box\neg q\) is proper persistent.
It is therefore below g, giving

\[
v\le\neg\Box\neg q=\Diamond q.
\]

This is the native Vicinity condition. The class M need not be a scalar
atom when it contains several points. Instead use the existing theorem
[[vicinity-and-atomicity-t-imply-actuality]], due to Cian Dorr with
Claude Opus 5.5, prompted by Cian Dorr. Its premises are current Vicinity
and current propositional Atomicity. Scalar fullness verifies the latter:
every nonempty subset of P contains an admitted singleton, and that
singleton is an atom against every current scalar subset. The theorem
therefore gives Actuality also for preorders.

This last step uses propositional Atomicity, not a claim that some
specified singleton was already true. The theorem's native proof and
attribution remain those of the existing record.

## 6. Representation from external complete atomicity

Suppose the actual scalar Boolean algebra is externally complete and
atomic, and \(\Box\) preserves every external meet. Let W be its
set of atoms. External complete atomicity identifies the algebra with
\(\mathcal P(W)\): each subset of atoms has an admitted scalar join,
and each scalar is the join of its atoms. This representation carries
ordinary Boolean operations and order to the set operations.

For each \(w\in W\), define externally

\[
S_w=\bigcap\{A\subseteq W:w\in\Box A\}.
\]

The indexed family is nonempty because \(\Box W=W\).
Preservation of this external meet gives \(w\in\Box S_w\).
Consequently

\[
w\in\Box A\quad\Longleftrightarrow\quad S_w\subseteq A.
\tag{6}
\]

The forward direction is the definition of the intersection; the reverse
is monotonicity from \(w\in\Box S_w\). Modal T gives
\(w\in S_w\). If \(v\in S_w\), modal 4 gives
\(w\in\Box\Box S_w\), so (6) implies \(v\in\Box S_w\)
and then \(S_v\subseteq S_w\).

Define \(v\preceq w\) iff \(v\in S_w\). The preceding facts
make this a reflexive transitive relation, with principal downset
\(S_w\). Equation (6) is exactly its downset-interior representation
(1). Sections 2–5 now give Vicinity and Actuality.

The representation uses preservation of an arbitrary external meet at
the step \(w\in\Box S_w\); finite modal meet laws do not supply
it. Likewise native Boolean Completeness only concerns admitted families,
and does not assert that all subsets of W have admitted scalar joins.
The conclusion here is a theorem about this external semantic class,
with no unrestricted Boolean-Completeness-to-Actuality implication.

## Sources

- GPT-6 Astra, prompted by Daniel Kodsi, *Full powerset Alexandroff scalars:
  a C-specific model-class obstruction*, 30 October 2026, Sections 1–8
  (unpaginated): the arbitrary directed-order rank coloring and external
  complete-atomic representation consequence.
- OpenAI Codex, prompted by Daniel Kodsi, *Persistent fixed points and
  cofinal chains*, 26 October 2026, opening and Section 1 (unpaginated):
  the proper-persistence facts and admitted-operation fixed-point diagonal
  reproduced in Section 1 above.
- Cian Dorr, with Claude Opus 5.5, prompted by Cian Dorr, 28 October 2026,
  [[vicinity-and-atomicity-t-imply-actuality]], proof (unpaginated): the
  current Vicinity and propositional Atomicity bridge used in Section 5.

The rank-coloring argument removes the well-foundedness restriction from
this application of the fixed-point method. It uses external ZFC and a
set-sized scalar algebra throughout.
