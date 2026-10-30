# Predecessor operations with a growing numerical field

Daniel Kodsi, with ChatGPT assistance, 30 October 2026.

There is one C model in which, at every externally fixed counting type,
numerical noncollapse holds necessarily and a total predecessor operation
exists on the numerical successors. Nevertheless **Arithmetic Necessitism**
fails at counting type t with its guard true. The distinction concerns
stability of the current numerical objects and acquisition of further
members by their whole numerical predicate.

This note records an unencoded theorem and model. It introduces no new
principle node. All type indices below are external schema indices;
there is no quantifier over types. No independent human check or Lean
proof is recorded.

## 1. Exact formulas and a C theorem

Fix an admitted counting type \(\sigma\), including e, and put
\(\nu=(\sigma t)t\). Write N, zero and S for its canonical numerical
predicate, zero and successor. Let

\[
 \operatorname{Pred}_\sigma:=
 \exists P^{\nu\nu}\,\forall n(Nn\to P(Sn)=n).
\]

This is a total operation with prescribed numerical-successor values.
A total functional graph alone does not supply it. The operation type is
admitted even at \(\sigma=e\), since its output \(\nu\) is relational.
The relation bottom \(\bot_\nu\) is distinct from numerical zero.

The following already follows in C:

\[
 \Box I^*_\sigma\longrightarrow\operatorname{Pred}_\sigma.
 \tag{1}
\]

For a direct proof define the admitted pooling operation

\[
 D(y)=\lambda X^{\sigma t}\,
   \exists m^\nu(Nm\land Sm=y\land mX).
\]

Fix a current number n. Numberhood persists in C. At any future
evaluation, n is still numerical, and the boxed guard makes successor
injective on all the numerical objects there. Therefore the witnesses
in \(D(Sn)X\) are exactly n, for every full future argument X.
Necessarily, \(D(Sn)X\leftrightarrow nX\). Intensionality gives the whole
identity \(D(Sn)=n\). The same D works for all current n. No choice of
preimages, standardness assumption or restriction to transported arguments
was used.

The proposed *current*-guarded sentence
\(I^*_\sigma\to\operatorname{Pred}_\sigma\) has a different strength.
The established numerical-protection results identify predecessor with
protection of current numbers from \(\bot_\nu\), equivalently numerical
noncollapse together with their necessary distinctness. Their all-type
canonical transport, inverse and section formulations require both the
numerical domain and numerical output restrictions. They do not provide
decoding of arbitrary nonnumerical images. These are source equivalences,
not separate new nodes or new incompatibility mechanisms.

## 2. A component with an additional numerical member

Use the countable finitary Henkin presentation of the fixed C language,
retaining every standard finite parameterized lambda template and the
actual H-only Logical Equivalence rule. Add, for every counting type
\(\sigma\), the sentence \(\Box I^*_\sigma\). At
\(\nu_t=(tt)t\), add a constant c and a predicate Q with

\[
 \mathbb N_t(c),\quad c\ne\bar n_t\ (n\in\omega),\quad
 \Box Q(\bar n_t)\ (n\in\omega),\quad \neg Q(c).
 \tag{2}
\]

Q is not required to be inductive. No compactness argument would justify
an inductive predicate containing all standard numerals and omitting a
number.

Every finite fragment is satisfiable in a full constant-domain S5
intensional hierarchy with countably infinitely many worlds and
individuals. Every fixed type has an infinite domain; full current rows
make its canonical numbers the standard numeral orbit, noncollapsed at
every world. Choose c to be a standard numeral beyond all numeral indices
mentioned in the fragment. Choose Q to be a constant finite initial
segment containing all the mentioned numerals and omitting c. The full
hierarchy admits Q and verifies the boxed requirements.

Finitary Henkin compactness therefore yields a pointed C component K
satisfying (2) and every boxed noncollapse instance. Its original
application, quantification and lambda operations are retained. K need
not be an externally full or extensional action model. No optional
property of the full S5 models used for finite satisfiability is
transferred to K.

## 3. Add a full present while keeping every component quantifier

Use the existing pair construction with current individuals
\(R_e=\omega\), projected constantly to one K individual. At every
flattened relational type take

\[
 R_{\alpha_1\cdots\alpha_k t}
 =\mathcal P(R_{\alpha_1}\times\cdots\times R_{\alpha_k})
       \times K_{\alpha_1\cdots\alpha_k t}.
\]

Application and abstraction calculate the arbitrary current row and the
original K denotation separately. The K coordinate of a quantifier uses
the **whole K domain**, including elements outside the projection image.
H-valid lambda equivalences agree in both coordinates. This is the
full-present C construction, not an attempt to reinterpret K as an
ordinary terminal Kripke world. The same construction is described in
[the C5-component writeup, Section 2](full-current-c5-arithmetic-root.md);
the C5 assumption is used there for its later power arguments, not for
the pair construction itself.

For each \(\sigma\), the root admits an induction-test predicate whose
current extension is exactly the closed numeral orbit. Every current
inductive predicate contains that orbit. Thus

\[
 \operatorname{ext}_R(\mathbb N_\sigma)
   =\{\bar n^R_\sigma:n\in\omega\}.
\]

Closed terms project correctly. The K images of these numerals are
distinct, with zero not a successor, because K satisfies \(I^*_\sigma\).
An equality between root numeral entities would project to an equality
between those images. Therefore the root also satisfies
\(I^*_\sigma\). Its K coordinate is the whole top because K satisfies
\(\Box I^*_\sigma\). The whole root value is consequently
\((\mathrm{true},\top_K)\), proving \(\Box I^*_\sigma\) at R.
Equation (1) now gives every \(\operatorname{Pred}_\sigma\) in the
same model.

## 4. The whole numerical predicate gains members

At counting type t, pair the root's current numerical orbit with K's Q
to obtain an admitted predicate Z. Every current root number is a
standard numeral, and (2) makes its Q-value the whole component top.
Thus each such number has whole Z-value
\((\mathrm{true},\top_K)\), and

\[
 R\models\forall n(\mathbb N_t(n)\to\Box Z(n)).
\]

But K's c is numerical and lacks Q. The original K quantifier sees c,
so the necessary inclusion \(\mathbb N_t\le Z\) fails at R. Hence
\(\mathbb N_t\) is not weakly inextensible and is not rigid. The
Arithmetic Necessitism instance at t fails with
\(\Box I^*_t\) true. The model supplies the asserted all-type
predecessors without asserting any analytic-necessitism verdict.

## 5. Attribution and related finite tests

OpenAI Codex, prompted by Daniel Kodsi, supplied the source
predecessor/protection and canonical-transport equivalences in
*Relational coding and recursion*, Sections 13 and 38 and its later
numerical-protection sections, and the pair construction in *Classical
present over an arbitrary model*, 25 October 2026, Sections 1–2.
Goodsell's *Arithmetic is Necessary*, Lemmas 3–4, supplies the numerical
persistence and guarded-distinctness lemmas used here.

The earlier fixed-e comparison occurs in the public
`coalesced-pinned-substitutions-nonstandard-root` construction, recorded
by Claude Opus 5.5, prompted by Cian Dorr, on 29 October 2026, extending
Dorr's 19 October construction. The contribution here is simultaneous
boxed noncollapse and predecessors at all types with the active numerical
growth failure at t.

The separate [finite calibrations](finite-numerical-calibrations.md)
give the exact predecessor-prefix cutoff, sparse proposition-type pairs
and a full-star strictness example. They also explain why current
noncollapse cannot simply replace the boxed guard in (1). The pure-Max
predecessor obstruction is already source work; it is not a new result
of this construction.
