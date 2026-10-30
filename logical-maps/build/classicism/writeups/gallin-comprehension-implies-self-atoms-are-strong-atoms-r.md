# Gallin comprehension makes every current self-atom strong

GPT-6 Astra, prompted by Daniel Kodsi, 30 October 2026.

Over the fixed logic C,

\[
\mathrm{Gallin\ Extensional\ Comprehension}
\ \Longrightarrow\
\forall Q^\tau\bigl(\operatorname{SelfAtom}_\tau(Q)
\to\operatorname{SAtom}_\tau(Q)\bigr)
\qquad(\tau\ne e).
\]

The conclusion concerns every **current** self-atom at every admitted
relational type, including propositions. Its strongness must settle all
predicates at every future point, including newly available predicates.
The additional device is to apply a bivalent evaluator to the atom's
**order-character**, rather than to its current instances. That retains
information about a self-atom even where it is not instantiated.

## 1. Evaluator and current atomicity

Apply Gallin's type-\(tt\) instance to the truth predicate. It supplies an
admitted operation \(E:t\to t\) coextensive with truth, with both \(E\)
and its pointwise negation persistent. Hence

\[
\forall p\,(Ep\leftrightarrow p),
\qquad
\Box\forall p\,(Ep=\top\lor Ep=\bot). \tag{1}
\]

For the second assertion, at any accessible point and any proposition
there, either \(Ep\) or \(\neg Ep\) holds. Persistence of the
corresponding relation makes that truth or falsity necessary, so the
value is literally the corresponding endpoint. This includes propositions
first available at that point. Equation (1) does not assert future
correctness of \(E\).

Gallin also gives current all-type ND by
[[gallin-comprehension-implies-nd]], and therefore current B. If \(Q\)
is a current self-atom, ND makes it an ordinary atom. Indeed, suppose
\(P\le Q\), \(P\ne\bot\) and \(P\ne Q\). ND preserves the two
inequalities, and necessary inclusion preserves \(P\le Q\).
Nonbottom \(Q\) has a possible instance. There its self-atom clause
makes it an atom, contradicting the preserved proper nonzero part.
This also follows from [[modal-five-implies-self-atoms-are-atoms-r]].

## 2. Endpoint Boolean laws survive new future arguments

Let \(J:\tau\to t\) satisfy

\[
\Box\forall X^\tau\,(JX=\top\lor JX=\bot). \tag{2}
\]

Suppose that it currently preserves the Boolean constants, complement
and binary meet. Under current B these laws hold necessarily, including
for future arguments that are unavailable now.

For complement, let

\[
\varphi:=\forall X\,[J(\neg X)=\neg JX].
\]

It is true now. If it fails at a future point, choose a counterexample
\(X\) there. Both sides are endpoints by (2); necessity of identity
preserves their different endpoint assignments. The same witness
therefore keeps \(\varphi\) false at every later point. This proves

\[
\Box(\neg\varphi\to\Box\neg\varphi).
\]

Current B, applied to the **whole** current proposition \(\varphi\),
gives \(\Box\Diamond\varphi\). A future failure would contradict
this, so \(\Box\varphi\). For meet use
\(\varphi:=\forall X,Y[J(X\land Y)=JX\land JY]\); the same argument
works with its two future witnesses. The constant equations persist
by necessity of identity.

No box is exchanged with a quantifier. The range condition (2) already
covers the full future domain, and the proof rules out a future
counterexample to each universally quantified law.

## 3. Normalize the atom's order-character

For the current self-atom \(Q\), now known to be an ordinary atom, put

\[
J_Q:=\lambda X^\tau\, .\,E(Q\le_\tau X). \tag{3}
\]

Its type \(\tau t\) is admitted. Equation (1) gives its necessary
endpoint range, even on new future \(X\). Current correctness gives
\(J_QX\leftrightarrow Q\le X\).

The characteristic map of a nonzero Boolean atom preserves top,
bottom, complement and binary meet:

\[
\begin{gathered}
Q\le\top,\qquad Q\not\le\bot,\\
Q\le\neg X\ \leftrightarrow\ \neg(Q\le X),\\
Q\le (X\land Y)\ \leftrightarrow\ (Q\le X\land Q\le Y).
\end{gathered}
\]

Since all outputs of \(J_Q\) are endpoints, these current truth
conditions give literal equalities expressing its Boolean laws.
Also \(J_QQ=\top\). Section 2 makes the laws necessary; the latter
identity persists by necessity of identity.

The order here is **necessary inclusion**. In particular
\(X\le Y\) is equivalent in C to the literal Boolean identity
\(X\land Y=X\). Current coextension is never substituted for this
identity. We have made the laws of a normalized operation necessary,
not the current atomicity of \(Q\).

## 4. The character decides every future predicate

Fix any accessible point \(v\) and any \(Z^\tau\) available there.
Its value \(J_QZ\) is an endpoint. That endpoint identity persists
along every continuation, as does \(J_QQ=\top\).

Suppose first \(J_QZ=\top\). At any later point \(u\), let
\(\bar a\) be a tuple satisfying \(Q\bar a\). Self-atomhood makes
\(Q\) an ordinary atom there, so

\[
Q\le Z\quad\text{or}\quad Q\le\neg Z.
\]

The second alternative would give the literal identity
\(Q\land\neg Z=Q\). Applying \(J_Q\) and its necessary Boolean
laws yields

\[
\top=J_QQ=J_Q(Q\land\neg Z)
       =J_QQ\land J_Q(\neg Z)=\top\land\neg J_QZ,
\]

contradicting \(J_QZ=\top\). Thus \(Z\bar a\). Since \(u\) and
its full-domain tuple were arbitrary, \(Q\le Z\) already at \(v\).

If instead \(J_QZ=\bot\), the same calculation using
\(Q\land Z=Q\) rules out \(Q\le Z\) at every later instance of
\(Q\). The atom's other decision gives \(\neg Z\bar a\), and
therefore \(Q\le\neg Z\) at \(v\).

We have proved

\[
\Box\forall Z^\tau\,(Q\le Z\lor Q\le\neg Z).
\]

Together with \(Q\ne\bot\), already part of self-atomhood, this is
\(\operatorname{SAtom}_\tau(Q)\). The empty argument tuple gives
\(\tau=t\). Since the original \(Q\) was any current self-atom,
the claimed schema follows.

The proof only uses atomicity of \(Q\) at later points **where it is
instantiated**. It neither asserts atomicity at an unoccupied point nor
requires a preimage of the future predicate \(Z\).

## 5. Exact boundary and sources

The result leaves the quantifier over \(Q\) outside the box. It does
not make every future self-atom strong from current Gallin alone, and it
does not make arbitrary ordinary atoms strong. The equivalent premise
ND + Strong Actuality follows through the existing Gallin
characterization.

Direct source: GPT-6 Astra, prompted by Daniel Kodsi, *Gallin comprehension
makes every current self-atom strong*, 30 October 2026, Lemmas 1–3 and
“The theorem” (unpaginated). The evaluator and persistent-counterexample
method are from *Gallin comprehension as a unique Boolean evaluator*,
22 October 2026, §§2–3 and 5 (unpaginated). Cian Dorr's Gallin-to-ND
proof is dated 20 September 2026; the self-atom definition and bridge
principles are his, dated 25 October 2026. Gallin's convention is stated
in Bacon and Dorr, *Classicism*, draft of 16 May 2023, §2.3, note 37,
p. 28.

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — section 2.3, note 37, p. 28
