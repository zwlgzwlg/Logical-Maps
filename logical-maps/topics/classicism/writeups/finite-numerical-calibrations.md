# Finite predecessor demands and numerical protection

Daniel Kodsi, with ChatGPT assistance, 30 October 2026.

These are exact finite consequences of the existing interpolation and
numerical-overflow arguments. They record no new native principle or
model seed. Every finite index and counting type is externally fixed;
different existential operations need not have the same witness.
No independent human check or Lean proof is recorded.

Fix a counting type \(\sigma\), put \(\nu=(\sigma t)t\), and write
\(b=\bot_\nu\). Standard numerals are denoted by their indices.

## 1. Finite interpolation and the exact prefix cutoff

For relational outputs the existing finite-interpolation theorem is

\[
 \exists F\,\bigwedge_i F(x_i)=y_i
 \quad\longleftrightarrow\quad
 \Box\bigwedge_{i,j}(x_i=x_j\to y_i=y_j).
 \tag{1}
\]

Necessity follows from necessary identity and congruence. For sufficiency,
take the finite union of the output relations, masking each by equality
to its prescribed input. At each future evaluation and every full future
argument tuple, boxed compatibility identifies all active prescribed
outputs. Intensionality gives their whole identities. This uses finite
lambda terms and does not extract an operation from an arbitrary graph.

For external \(i<j\), the finite cardinality definitions prove
\(i\wedge j=b\) in C: a property cannot have both fixed finite sizes.
As \(S(b)=b\), they also give

\[
 i=j\quad\longleftrightarrow\quad i=b.
 \tag{2}
\]

This holds even when two distinct indices denote the same overflow
entity. No current noncollapse premise is inserted.

Let \(F_{\sigma,k}\), for \(k\ge1\), prescribe
\(P(1)=0,\ldots,P(k)=k-1\). Then

\[
 F_{\sigma,k}\quad\longleftrightarrow\quad\Box(k-1\ne b).
 \tag{3}
\]

For \(k=1\), constant zero works and zero is necessarily nonbottom.
For \(k\ge2\), if \(k-1=b\) were possible, k would also be b.
The last two transported prescriptions force \(k-2=b\); repeating
backwards forces \(0=b\), a contradiction. Conversely, protection of
\(k-1\) protects every smaller numeral, since overflow propagates
upward. Equation (2) makes the inputs \(1,\ldots,k\) necessarily
distinct, so (1) applies. Protection of k is unnecessary.

The minimum full one-world type capacities are

\[
 m_e=1,\qquad m_t=2,\qquad
 m_{\alpha\beta}=m_\beta^{m_\alpha}\quad(\beta\text{ relational}).
\]

C supplies \(m_\sigma\) necessarily distinct \(\sigma\)-entities.
Inductively, necessarily distinct inputs and outputs give the indicated
finite number of distinct table operations by finite equality masks.
Finite unions of their haecceities instantiate each numeral from 0
through \(m_\sigma\) at every future evaluation. Those numerals are
therefore protected from b. The full singleton-individual one-world
hierarchy has exactly these capacities and makes \(m_\sigma+1=b\).

Consequently \(k\le m_\sigma+1\) is the C-provable prefix range,
and \(k=m_\sigma+2\) is the first prefix refuted by pure Maximalism.
Pure Max makes the closed, C-consistent overflow sentence possible,
contradicting (3). At e the first two equations form a C theorem; at t
the first three do. The relevant capacity belongs to the counting type
\(\sigma\), not the numerical-object type \(\nu\).

## 2. Protection under pure Max includes arbitrary current numbers

Put \(\delta=(m_\sigma+1=b)\). At any evaluation satisfying
\(\delta\), the finite lambda-defined set
\(\{0,\ldots,m_\sigma,b\}\) contains zero and is successor closed.
Numerical leastness puts every number in that set, including any
nonstandard numerical object admitted there.

Let n be a current number different from every \(0,\ldots,m_\sigma\).
The numerical Exclusivity theorem makes \(n\wedge j=b\) a whole
identity for each displayed lower numeral j. Those identities and
numberhood persist. At a \(\delta\)-evaluation, n cannot equal such
a j, since j is protected. Hence n equals b there. Pure Max applies only
to the closed pure sentence \(\delta\), which the singleton model
realizes. It follows that, under pure Max,

\[
 \forall n\in\mathbb N_\sigma\,
 \left[\Box(n\ne b)\ \longleftrightarrow\
        \bigvee_{j=0}^{m_\sigma}n=j\right].
 \tag{4}
\]

The converse uses necessary identity and the protected finite segment.
This is a statement about arbitrary current numbers. It assumes neither
their external standardness nor parameterized Maximalism.

## 3. Sparse pairs at counting type t

For external \(0\le a<c\), consider only

\[
 D_{\sigma,a,c}:=
  \exists P\,[P(a+1)=a\land P(c+1)=c].
\]

Equations (1) and (2) give the exact reduction

\[
 D_{\sigma,a,c}\quad\longleftrightarrow\quad
 \Box((a+1=b)\to a=b).
 \tag{5}
\]

The controlling index is the smaller **output** a. The larger output c
has no further role. At counting type t, the pair is refuted by pure
Max exactly when \(a=2^r\) for an external \(r\ge1\); in every other
case it is already a theorem of C.

For the positive direction, suppose \(a+1=b\) but \(a\ne b\).
Necessary identity preserves the first equality. No future evaluation
can have \(a+1\) distinct propositions: their finite haecceity union
would instantiate that numeral. The second inequality need not give a
current instance. Contraposed Intensionality gives a *possible* instance
of a, hence a possible evaluation with exactly a whole propositions.

The whole proposition domain is a nontrivial Boolean algebra. Every
finite such algebra has \(2^r\) elements for some \(r\ge1\). For
each fixed a this is finite first-order reasoning: choose the finitely
many atoms by finite descent, express each element as their join, and
count the distinct subset joins. It needs no Boolean Completeness
principle or arbitrary admitted powerset. Thus, outside those sizes,
C proves \((a+1=b)\to a=b\). Necessitate the discharged theorem and
apply (5). In particular a=0 and a=1 are positive cases.

For sharpness, take the full hierarchy on the indiscrete groupoid with
r objects and singleton individuals. At each object there are exactly
r outgoing arrows, so its whole proposition domain has \(2^r=a\)
members. Every reachable object has this size. The numeral a has a
current instance, while \(a+1\) is whole bottom. This is a C model
of the closed pure overflow sentence. Pure Max makes that sentence
possible and refutes (5).

For example, separate operations realizing \(P(4)=3,P(5)=4\) and
\(P(4)=3,P(6)=5\) are supplied by C. One operation realizing both
would also realize \(P(5)=4,P(6)=5\), the Max-forbidden pair with
smaller output 4. Separate existential witnesses must not be pooled.
No finite-capacity spectrum at higher counting types follows from the
proposition-type classification.

## 4. One full-star strictness example at every type

There is also a C model with current \(I^*_\sigma\) and
\(\Box(m_\sigma+1\ne b)\) at every type, but no full numerical
predecessor at any type.

Take a root R with countably infinitely many individuals and only its
identity endomorphism. For each natural index add a disjoint two-object
indiscrete groupoid, with two individuals at each object and coherent
bijective transport. From R to each terminal object take one constant
individual map, choosing distinguished individuals coherently. There
are no returns or arrows between terminal components.

Use the full action hierarchy. At a flattened relational type, an entity
is an arbitrary subset of all pairs consisting of an outgoing arrow
and a tuple of arguments at its target. Transport precomposes the arrow
coordinate; application inserts transported arguments; abstraction and
quantifiers use every full target domain. This is the existing full
action construction of C, with no covariance or finite-support restriction.

At a terminal object the whole type capacities are finite:

\[
 M_e=2,\qquad M_t=4,\qquad
 M_{\alpha\beta}=M_\beta^{M_\alpha}.
\]

Equivalently, a flattened relation with argument capacities
\(M_{\alpha_i}\) has \(2^{2\prod_i M_{\alpha_i}}\) profiles.
Transport inside its groupoid is bijective. Induction gives
\(M_\sigma>m_\sigma\) at every type.

At R every fixed type is infinite: individuals are infinite, outgoing
arrows give infinitely many propositions, and constant relations inject
propositions into every other relational type. Full current rows make
each numerical field exactly its standard orbit and distinguish all its
numerals. Thus every current \(I^*_\sigma\) is true. The numeral
\(m_\sigma+1\) has a finite-subset instance at R and every terminal,
so it is necessarily nonbottom.

In any terminal, however, \(M_\sigma+1\) and \(M_\sigma+2\) are
whole bottom while \(M_\sigma\) is nonbottom. A root predecessor's
two corresponding equations would transport to equal inputs with
unequal outputs. No such operation exists. This is one simultaneous
all-type example. It is not a Max model: no accessible object has
exactly one individual, though that pure sentence is C-consistent.

## Sources and boundary

The finite-interpolation theorem and predecessor-overflow mechanism are
prior OpenAI Codex work prompted by Daniel Kodsi, *Relational coding and
recursion*, Sections 13 and 38. The minimum capacities and their
necessarily distinct witnesses are from *Finite type capacities*,
Sections 1–3. The numerical orbit test and one-way star are from
*Numerical models*, Sections 2 and 5.2; the full action construction is
Bacon and Dorr's. The exact prefix cutoff, quantified protected segment,
sparse classification and two-object-terminal adaptation are the bounded
calibrations recorded here.

The C-positive finite demands coexist in any existing Max model because
they are C theorems, with separately quantified operation witnesses.
No new Max construction or consistency-strength improvement is claimed.
The [protected numerical-growth model](protected-numbers-and-numerical-growth.md)
addresses the separate all-type boxed-guard comparison with Arithmetic
Necessitism.
