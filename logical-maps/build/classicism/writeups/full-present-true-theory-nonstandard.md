# Stable analytical truth with a nonstandard numerical component

Daniel Kodsi, with ChatGPT assistance, 29–30 October 2026.

There is a model of C with full **Necessity of Second-Order Analysis** in which
**Arithmetic Necessitism** and **Analytic Necessitism** both fail. The numerical
failure occurs with its boxed noncollapse guard true. The construction is in
ambient ZFC and gives a consistency upper bound relative to Con(ZFC).

The proof combines the existing full-present construction with a component
having the complete theory of a standard full hierarchy. Its canonical number
field nevertheless contains a nonstandard member. No independent human check
or Lean proof is recorded.

## 1. A countable component with the right complete theory

Let F be the full one-world extensional hierarchy with individual domain
\(\omega\), truth values \(\{0,1\}\), and all functions at every admitted
relational type. Necessity is the identity. There are countably many finite
type expressions and standard finite parameterized lambda templates.
Represent F in the corresponding countable many-sorted first-order Henkin
language, with application and the operation for every such template.

Let \(T=\operatorname{Th}(F)\). This complete theory is a set; it need not be
recursive. Put \(\nu=(et)t\), add a constant \(c:\nu\), and require

\[
 \mathbb N_e(c),\qquad c\ne\bar n_e\quad(n\in\omega).
\]

Every finite part holds in F by choosing a standard numeral outside its
finite list of exclusions. Compactness and downward Löwenheim–Skolem give
a model H with every sort countable, elementarily equivalent to F in the
original language, and with the displayed c. In particular H satisfies
\(I^*_e\), has infinitely many individuals, and preserves all parameterized
Henkin operations. Its extensionality identifies each relation entity with
its function on the appropriate H domains.

H is not asserted to be an elementary substructure of F. Its admitted
predicates cannot include the external set of its standard numerals: that
set would be inductive and omit its numerical c. Compactness was applied
to a first-order presentation, without imposing full second-order semantics
on H.

## 2. The full present

Take \(R_e=H_e\), with identity projection. For each flattened relational
type \(\tau=\alpha_1\cdots\alpha_k t\), including \(k=0\), set

\[
 R_\tau=\mathcal P(R_{\alpha_1}\times\cdots\times R_{\alpha_k})\times H_\tau.
\]

A pair \((S,a)\) has current extension S and projects to a. Application
and lambda abstraction calculate the current row and the H denotation
separately. A quantified formula uses the entire R domain currently and
the entire original H domain in its H coordinate. In particular, old
quantifiers are never restricted to images of current arguments.

These are the standard full-present operations, as also displayed in
[Full present over a C5 component, Section 2](full-current-c5-arithmetic-root.md).
Their C-validity uses the original component operations. For a
theoremhood-qualified equivalence of the base logic H, the current lambda
rows agree, and C-validity in the component identifies the second
coordinates. Every finite parameterized lambda term remains admitted.
No additional optional premise
enters the Logical Equivalence rule. In the present case H is a one-world
extensional Henkin model, so the construction is also the ordinary
one-component coalesced root, with one nonidentity arrow \(h:R\to H\).

Root identity is literal identity: arbitrary current singleton predicates
separate distinct root entities. Terms commute with h. A formula at R is
necessary exactly when it is true both currently and after transport to H,
with the latter's own full quantifier domains. Thus the root has four whole
propositions, although its designated current truth is classical.

## 3. Every second-order analytical sentence has a fixed sign

Fix a standard finite sentence A in the native analytical grammar, and
let \(\epsilon\) be its truth value in the ordinary full real field with
its natural-number predicate. For each admitted carrier type \(\sigma\),
the sentence

\[
 U_{\sigma,A,\epsilon}:=
 \forall\mathfrak R\,
  (\operatorname{Real}_\sigma(\mathfrak R)\to A(\mathfrak R)^\epsilon)
\]

holds in F by categoricity of full complete ordered fields and invariance
under isomorphism. Here the superscript means A or its negation according
to the selected sign. This is a single finite sentence of the Henkin
language, even when no field is available at that carrier. It belongs to
T and therefore holds in H. What transfers is the sentence; no claim that
H's internal real fields are externally complete is needed.

At R, every current real-field tuple is an external complete ordered
field. Every subset of its carrier, and every finite-arity relation on it,
is the current restriction of an admitted row: choose that row freely and
any H component. The least inductive field predicate is consequently the
ordinary natural-number part. The native analytical grammar uses relations
only by applying them to field elements and uses identity only between
those elements. It cannot distinguish two relation entities that have the
same current row. Induction on this grammar therefore gives full external
analytical semantics at R, with the same sign \(\epsilon\).

Both R and H satisfy \(U_{\sigma,A,\epsilon}\), so its box holds at R.
This proves the whole Necessity of Second-Order Analysis schema, at every
carrier and for every standard finite analytical sentence. It also covers
fields that can occur at R but not at the corresponding type of F; the
root argument uses their external categoricity directly.

## 4. The numerical field is not weakly inextensible

Let \(\bar n_R\) be the root's closed e-numerals. Every inductive property
contains their orbit. Conversely, R admits a property with precisely that
orbit as its current row, and any H component. It is currently inductive.
The definition of numberhood therefore gives

\[
 \operatorname{ext}_R(\mathbb N_e)=\{\bar n_R:n\in\omega\}.
\]

The root individual domain is infinite and has all current unary rows.
The current row of \(\bar n_R\) therefore counts exactly the n-element
properties, distinguishing these numeral entities. Zero is not a successor,
and successor is injective on their orbit. Thus \(I^*_e\) holds at R;
it holds at H by T, so \(\Box I^*_e\) holds at R.

Parameterized Henkin comprehension in H admits
\(X_H(x)=\mathbb N_e(x)\land x\ne c\). Form the root pair X whose
current row is the standard numeral orbit and whose H component is
\(X_H\). Each current root number is a standard numeral, and its image
is the corresponding H numeral, different from c. Hence

\[
 R\models\forall n(\mathbb N_e(n)\to\Box X(n)).
\]

But \(\mathbb N_e\le X\) fails, since H has the number c and lacks
\(X_H(c)\). This is exactly a weak-inextensibility countertest for the
whole numerical predicate. Its rigidity, and hence Arithmetic Necessitism
at e, fails while the required boxed guard is true.

## 5. Analytic Necessitism fails nonvacuously

Since \(R_e\) is countably infinite and \(H_{et}\) is countable,
\(R_{et}=\mathcal P(R_e)\times H_{et}\) has continuum many members.
Current fullness supplies a complete real field at et. Any current
complete real field there has continuum many elements, by categoricity.

If a rigid necessarily-real field witnessed Analytic Necessitism, its
carrier's necessary distinctness would make h injective on those current
elements: two elements with equal H images would fail necessary
distinctness. But \(H_{et}\) is countable. Thus no possible witness can
have the required rigidity and necessary realhood. AN fails at et with a
true possible-real antecedent; the recorded implication from SOAN to AN
also gives SOAN failure.

## Sources and scope

The full-present pair construction and its current analytical truth lemma
are due to OpenAI Codex, prompted by Daniel Kodsi, *Classical present over
an arbitrary model*, 25 October 2026, Sections 1–2 and 5. The companion
*Classical present conservation*, Section 4, supplies the complete-theory
Henkin method. Cian Dorr's existing
`coalesced-two-extensional-arithmetics-root` supplies the
standard-current/nonstandard-component numerical-growth countertest;
Bacon and Dorr supply the coalesced model framework.

The addition here is the matching complete theory that keeps analytical
truth fixed in the same numerical-growth model. No Necessity of Arithmetic,
C5, No Pure Contingency, choice or completeness verdict is added. Neither
the common complete analytical theory nor the countable component implies
agreement on the complete pure intensional language.

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — Sections 1.3 and 2.3; Theorem 3.26 and Appendix E. The fixed C language and coalesced action-model framework.
- **Formulation: Arithmetic is Necessary.** Goodsell, Zachary William Lee. Arithmetic is Necessary. Draft dated 5 June 2024, 28 pages. Derives the necessity of arithmetic in the logic HKC (H plus K plus Countable Boolean Completeness) and shows that Boolean Completeness is inconsistent with the maximalization of any recursively enumerable extension of HK consistent with I, answering the question of Classicism, §2.6. Locators refer to this draft. — Definitions 3–8. The canonical numerical objects and noncollapse guard.
