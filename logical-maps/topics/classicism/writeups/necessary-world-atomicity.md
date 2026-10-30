# Atomicity by necessarily-world propositions

OpenAI Codex, prompted by Daniel Kodsi, 28 October 2026.

Every possible proposition is entailed by a proposition that is
necessarily a world. Here “world” means a propositional Boolean atom:

\[
\forall p^t\bigl(p\ne\bot\to
  \exists w^t(\Box\operatorname{Atom}_t(w)\land w\le p)\bigr).
\tag{W}
\]

The requirement includes \(\Box(w\ne\bot)\). It does **not** assert
\(\Box w\): a proposition can remain a nonzero atom while being false.
A strong world, by contrast, necessarily decides propositions but may
become bottom. Thus (W) is stronger than Strong Atomicity.

Over the fixed framework C,

\[
\text{(W)}\quad\Longleftrightarrow\quad
\Box\text{Plenitude}\quad\Longleftrightarrow\quad
\Box\text{Gallin Extensional Comprehension}.
\]

The proof identifies coverage by necessarily-world propositions with the
existing boxed Plenitude and Gallin theories.

## 1. Coverage gives necessary availability of a true necessary atom

Put
\[
\chi:=\exists w^t\bigl(w\land\Box\operatorname{Atom}_t(w)\bigr).
\]

Suppose \(\neg\chi\ne\bot\). Apply (W) to obtain \(w\) with
\(\Box\operatorname{Atom}_t(w)\) and \(w\le\neg\chi\).
Modal 4 preserves its necessary atomhood at every accessible evaluation.
At any such evaluation, if \(w\) is true, that same \(w\) witnesses
\(\chi\). Hence \(\Box(w\to\chi)\), or \(w\le\chi\).
The two bounds force \(w=\bot\), contradicting its atomhood by T.
Therefore \(\neg\chi=\bot\), equivalently \(\Box\chi\).

## 2. A true necessary atom gives Actuality and propositional ND

We first prove the closed C implication
\[
\chi\ \to\ \operatorname{Actuality}\land ND_t.
\tag{1}
\]

Let \(w\) be true and necessarily atomic. A current atom decides each
proposition \(q\): \(w\le q\) or \(w\le\neg q\). If \(q\) is true,
the latter contradicts the current truth of \(w\). Thus \(w\) entails
every current truth, exactly the required Actuality witness.

For ND, suppose \(p\ne q\) currently and let \(d\) be the proposition
\(p=q\). Since \(d\) is false and \(w\) true, its Boolean decision gives
\(w\le\neg d\). This bound is a literal Boolean identity and persists
by NI. If \(d\) held at any accessible evaluation, NI there would give
\(\Box d\), hence \(d=\top\). The persistent bound would then force
\(w=\bot\), contradicting \(\Box\operatorname{Atom}_t(w)\).
Consequently \(\Box(p\ne q)\), proving \(ND_t\).

Necessitate the closed implication (1), then apply \(\Box\chi\).
This yields necessary Actuality and \(\Box ND_t\). The recorded
type-transfer theorem turns \(\Box ND_t\) into all-type boxed ND, or
C5. The recorded C5 + necessary Actuality theorem gives all-type
Atomicity, and C5 + Atomicity gives boxed Plenitude. This proves
(W) → □Plenitude.

## 3. Boxed Plenitude gives necessarily-world witnesses

Boxed Plenitude gives C5 and all-type Atomicity by the native results.
Let \(w\) be any current propositional atom. Its nonzeroness remains
necessary by propositional ND. For each \(q\), atomhood gives
\(w\le q\) or \(w\le\neg q\). Each disjunct is a literal identity,
so NI preserves whichever disjunct holds. Hence
\[
\forall q\,\Box(w\le q\lor w\le\neg q).
\]
C5 supplies BF, giving
\(\Box\forall q(w\le q\lor w\le\neg q)\).
Together with necessary nonzeroness, this is
\(\Box\operatorname{Atom}_t(w)\).

Now take any \(p\ne\bot\). Propositional Atomicity supplies an atom
\(w\le p\); the preceding argument makes that same witness necessarily
atomic. This proves □Plenitude → (W).

## 4. The boxed Gallin connection

The recorded implications from □Gallin Extensional Comprehension give
C5 and □Rigid Comprehension. Necessary Rigid Comprehension gives
necessary Actuality; C5 + necessary Actuality gives Atomicity; and C5 +
Atomicity gives □Plenitude.

Conversely □Plenitude gives C5 and Atomicity. Those imply □Rigid
Comprehension, and C5 + □Rigid Comprehension implies □Gallin
Extensional Comprehension.

## Sources

Direct source: OpenAI Codex, prompted by Daniel Kodsi,
*Adjunctions, atom projection, and persistent worlds*, 28 October 2026,
§§2–5, and *Pure uniformity and one necessary atom*, §§3–4,
both unpaginated. The proof is also reproduced, with its relational
generalization, in [the boxed-Plenitude write-up](necessary-plenitude-r.md).

The background implications are from
Bacon–Dorr, *Classicism*, draft of 16 May 2023, Proposition 2.2,
p. 22 (type transfer), Proposition 2.6, pp. 25–26 (C5 and necessary
Actuality), and §2.3, concluding equivalences, p. 33 (boxed Plenitude).
The Gallin routes are the recorded September 2026 deductions from
Cian Dorr's suggestion, using the Gallin formulation in *Classicism*,
§2.3, n. 37, p. 28. Bacon, *A Philosophical Introduction to Higher-Order
Logics*, §8.2, pp. 165–166, supplies the weak/strong-world terminology.
