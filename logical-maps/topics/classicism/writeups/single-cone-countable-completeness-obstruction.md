# A single-cone obstruction to current countable completeness

Daniel Kodsi, with ChatGPT assistance, 30 October 2026.

This is a conditional theorem about a specified model geometry. A point
with current Countable Boolean Completeness cannot lie above the stated
numerical countermodel through a single cone if its transport admits a
whole lift of the countertest. The result gives no general implication
from current CBC to Arithmetic Necessitism or Actuality, and constructs
no CBC predecessor. No independent human check or Lean proof is recorded.

## 1. A separate standardness lemma

Let \(h:R\to K\) be total typed transport that respects the closed
numerical terms, literal current identity, and evaluation of boxed
formulas along h. Fix a counting type \(\sigma\). Assume K satisfies
current \(I^*_\sigma\) and its current numerical objects are exactly
its standard numeral orbit. Then the same is true at R.

Goodsell's C lemmas give numerical persistence and guarded distinctness:

\[
 N(a)\to\Box N(a),\qquad
 N(a)\land N(b)\land a\ne b
   \to\Box(I^*_\sigma\to a\ne b).
\]

For any current root number a, persistence makes \(h(a)\) numerical
at K. Thus \(h(a)=\bar n_K=h(\bar n_R)\) for some external finite n.
If \(a\ne\bar n_R\), guarded distinctness evaluated along h would
contradict this equality, since K has current \(I^*_\sigma\).
Therefore \(a=\bar n_R\). Conversely every standard root numeral is
numerical. Their images are distinct, so the root standard orbit also
satisfies current \(I^*_\sigma\).

This argument needs no CBC, external orbit predicate at R, full current
domains, surjectivity at other types, or converse direction of modal
semantics. The original symmetric Cohen arithmetic-growth application
supplies the standard-current hypothesis at **e**. Applying the lemma
at another counting type requires that hypothesis there as well.

## 2. Stronger assumptions for the obstruction

For the rest, require a complete arrow presentation of the modal
semantics: at R and its continuations, a boxed formula is true if and
only if it is true along **every** outgoing arrow, including identity,
with all its transported parameters. There are no hidden coordinates or
omitted continuations. Every nonidentity arrow from R must factor
through the chosen \(h:R\to K\). Transport respects all admitted
lambda terms and the full closed formulas used below.

Put \(\nu=(\sigma t)t\) and \(\rho=\nu t\). Suppose K has

\[
 I^*_\sigma,\qquad
 \Box\neg\operatorname{HasReal}_\rho,
\]

and an admitted whole predicate \(X:\rho\) with

\[
 K\models\forall n(Nn\to\Box Xn),
 \qquad K\not\models N\le X.
 \tag{1}
\]

The conclusion is that R cannot satisfy the single current
\(\mathrm{CBC}_{\sigma,\rho}\) instance and also admit any
\(Y:\rho\) with \(hY=X\) as a **whole-entity identity**.
In particular the \(\rho\)-transport of such a CBC entrance cannot
be surjective. The proof of this conclusion does not assume standard
current numbers at either point.

## 3. Current CBC supplies the isolating proposition

Assume temporarily that R has that CBC instance. Access to K's current
\(I^*_\sigma\) gives \(\Diamond I^*_\sigma\) at R: its negation
would be \(\Box\neg I^*_\sigma\), contradicting boxed soundness
along h. The C numerical theorem
\(\Diamond I^*_\sigma\to I^*_\sigma\) gives current noncollapse
at R.

The [current field-existence lemma, Section 3](analytic-necessitism-and-countable-completeness-imply-arithmetic-necessitism.md)
uses exactly this CBC instance and gives

\[
 I^*_\sigma+\mathrm{CBC}_{\sigma,\rho}
   \longrightarrow\operatorname{HasReal}_\rho.
\]

Its proof forms joins of guarded rational cuts. Goodsell's parameterized
arithmetic stability controls the entire quantified cut comparison at
future points; it does not exchange box and universal quantification.
Literal uniqueness of the joins supplies a current cut-section family,
without selecting a join operation or assuming boxed CBC.

Let Q be the whole closed sentence
\(\operatorname{HasReal}_\rho\). It is currently true at R. At K,
\(\Box\neg Q\) makes Q the **whole bottom proposition**. Hence
closed-term naturality gives \(hQ=\bot\). Every nonidentity root
arrow factors through h, so Q is false along each of them. No extra
root-only predicate or Actuality premise has been added: Q is a closed
sentence already forced by the hypothetical CBC premise.

## 4. Any whole lift normalizes to a countertest

Suppose \(hY=X\). Lambda comprehension admits

\[
 Z=\lambda n^\nu(Q\lor Yn).
\]

For an arbitrary current root number a, Z(a) is true at identity
because Q is true. At any other arrow, factor through h. Persistence
makes \(h(a)\) a current K-number, and (1) makes X true of it along
every continuation. Thus Z(a) is true along every root arrow. The
**converse** direction of modal adequacy now yields

\[
 R\models\forall a(Na\to\Box Za).
\]

Whole transport and \(hQ=\bot\) give \(hZ=X\). This identity
uses C-valid Boolean/lambda identities with whole parameters, without
applying Logical Equivalence to an optional current premise.

If \(N\le Z\) held at R, it would say
\(\Box\forall a(Na\to Za)\). Modal 4 gives a further outer box;
boxed soundness along h would then give
\(K\models\Box\forall a(Na\to Xa)\), contradicting (1).
The extra box is essential: transporting only a current universal
could miss newly available target or later numerical arguments.

Goodsell's Lemma 8 derives weak inextensibility of N from precisely
the current \(\mathrm{CBC}_{\sigma,\rho}\) instance. Its countable
family consists of numerical haecceities with a lambda-defined
shared-numeral coding relation. Applied to Z, it gives the inclusion
just refuted. This proves the claimed obstruction without assuming
preservation of arbitrary joins or surjectivity of quantified domains.

## 5. Conditional Actuality and the remaining scope

Even without a lift Y, the same hypothetical CBC premise makes Q true
at identity and false along every other root arrow. For every current
true proposition p, modal adequacy gives \(\Box(Q\to p)\).
Therefore Q witnesses current Actuality in this geometry. This is
neither necessary Actuality nor an unrestricted CBC-to-Actuality rule.

The public [symmetric Cohen arithmetic-growth construction](symmetric-cohen-arithmetic-growth.md)
provides the original e-number countertest; its
[consequences proof](symmetric-cohen-arithmetic-growth-consequences.md)
establishes whole nonexistence of real fields. Those facts alone do not
supply the adequate arrow presentation or single-cone entrance assumed
here. A transport image omitting X, or a separately controlled branching
geometry, is outside this obstruction and still needs its own C and CBC
proof.

The numerical persistence, guarded distinctness and CBC-to-weak-
inextensibility steps are Goodsell's *Arithmetic is Necessary*,
Lemmas 3–5 and 8. The current field-existence lemma is the linked
Kodsi-prompted proof. The added argument is the closed field-existence
marker and normalization of any whole lifted test in this exact
single-cone geometry. No native node, model verdict or unrestricted
implication is inferred from it.
