# Analytic Necessitism without Arithmetic Necessitism

OpenAI Codex, prompted by Daniel Kodsi, 30 October 2026. This is a separate consequence supplement
to GPT-6 Astra, prompted by Daniel Kodsi, *Symmetric Cohen model:
arithmetic growth*, 29 October 2026, §§7.2–7.4. The model construction
and its original proof are unchanged.

## The contribution and its implications

Analytic Necessitism (AN) can hold while Arithmetic Necessitism (AR) fails,
but **only because no real-number structure is possible at any admitted
carrier type**. This is a characterization of every such case, not just
an additional verdict about the symmetric Cohen model. Write NoReal for
the schema asserting that necessary absence. Relative to a failed AR
instance, Section 2 proves

\[
\boxed{\mathrm{AN}\ \Longleftrightarrow\ \mathrm{SOAN}
       \ \Longleftrightarrow\ \mathrm{NoReal}.}
\]

Here SOAN is **Second-Order Analytic Necessitism**. The symmetric Cohen
arithmetic-growth construction realizes these conditions while its
necessary arithmetic guard is true. Thus the analytic principles hold
vacuously, while the arithmetic failure is substantive. An actual rigid,
necessarily real structure would supply a fixed Peano reference and
prevent that failure.

In particular,

\[
\mathrm{AN}+\neg\mathrm{AR}\ \Longrightarrow\ \mathrm{SOAN}.
\]

Necessity of Second-Order Analysis and Non-contingency of CH then follow
by the existing SOAN implications. Here these conclusions hold because
there are no possible real structures; they do not assert real existence.
Failure of AR is distinct from failure of Necessity of Arithmetic.

The new native result AN + Transversal → AR also yields failure of
Transversal and Actuality under AN + ¬AR. Existing connections further
exclude current Rigid Comprehension, Plenitude, Functional Choice and
Transversal Choice.

These are the current, all-type principles where a type schema is
involved. Relational Choice is not among the consequences proved here.
There are also stronger necessary failures: if the failed AR instance
is at \(\sigma_0\), then

\[
\Box\neg\mathrm{Tr}_{\nu_{\sigma_0}}
\qquad\text{and}\qquad
\Box\neg\mathrm{Actuality},
\quad \nu_{\sigma_0}=(\sigma_0t)t.
\]

The proof of Section 1 works at that source because a failed AR instance
includes \(\Box I^*_{\sigma_0}\). It proves necessary failure of one
specified Transversal instance, not of every typed instance. In the
symmetric Cohen model the source is \(e\).

**Map coverage.** Selecting AN and the negation of AR in the map gives
the displayed negative consequences through the AN + Transversal
result. In the graph, show the negated forms of the target principles
to display those arrows. The positive implications from this signed
premise set to SOAN and its consequences are proved in this write-up;
they are not currently encoded as graph rules. NoReal is an abbreviation
in this proof, not an additional principle node. The distinction matters:
the graph's negative arrows are present, but they do not by themselves
display the full characterization above.

## 1. Necessary failures and the arithmetic guard

For every externally specified host \(\tau\), the model's original
§7.2 proves that the **entire** proposition
\(\exists\mathfrak R\operatorname{Real}_\tau(\mathfrak R)\) is
bottom. Thus it proves the schema

\[
\Box\neg\exists\mathfrak R\operatorname{Real}_\tau(\mathfrak R)
\quad\text{for each admitted }\tau. \tag{NoReal}
\]

Section 7.3 separately proves \(\Box I^*_e\): both the current and
component coordinates of the Peano condition are top. The guard is true,
not vacuous, despite numberhood's inextensibility failure in §7.4.

The C theorem proved in
[[analytic-necessitism-and-transversal-imply-arithmetic-necessitism]], §1,
is, with \(\nu=(et)t\) and \(\rho=\nu t\),

\[
I^*_e\land\mathrm{Tr}_{\nu}
\ \to\ \exists\mathfrak R\operatorname{Real}_{\rho}(\mathfrak R).
\tag{1}
\]

Necessitate this **closed theorem**, not an optional premise. With
\(\Box I^*_e\) and the \(\rho\)-instance of NoReal, modal K gives

\[
\boxed{\Box\neg\mathrm{Tr}_{(et)t}}. \tag{2}
\]

This is one explicit Transversal instance failing necessarily. It
therefore makes the full Transversal schema fail at every accessible
evaluation. It does **not** say that every typed Transversal instance
fails. Types remain external indices; there is no object-language
existential or universal quantifier over types.

Christopher Sun's existing [[actuality-implies-transversal]] theorem
gives \(\mathrm{Actuality}\to\mathrm{Tr}_{(et)t}\). Necessitate that
closed instance and combine with (2):

\[
\boxed{\Box\neg\mathrm{Actuality}}. \tag{3}
\]

Statements (2) and (3) are stronger than \(\neg\Box\mathrm{Tr}_\nu\)
and \(\neg\Box\mathrm{Actuality}\). The implication
ANA + Transversal → AR also derives the model's **current** Transversal
failure from SOAN and failure of AR. Current Actuality failure follows
from Actuality → Transversal.

NoReal **alone** does not give these failures. A one-world full finite
extensional model has only finite domains at every admitted type, so
there is no ordered field at any type. It satisfies NoReal, Transversal
(coextension is already identity) and Actuality. Its canonical arithmetic
guards fail. This is the reason the genuine arithmetic assumption in
(1) and the necessary guard used for (2) must be kept.

## 2. The exact conditional equivalence when AR fails

This is GPT-6 Astra, prompted by Daniel Kodsi, *Finite-type consequences*,
29 October 2026, §5 (unpaginated), with its schema scope made explicit. Suppose a particular externally fixed source
\(\sigma_0\) witnesses failure of Arithmetic Necessitism:

\[
\Box I^*_{\sigma_0}\land
\neg\bigl(\operatorname{Rigid}(N_{\sigma_0})\land
                 \operatorname{ND}(N_{\sigma_0})\bigr). \tag{4}
\]

Relative to this failure, the full ANA schema, full SOAN schema, and
all-type NoReal schema are equivalent.

First assume ANA. If a real structure were possible at any specified
host \(\tau\), ANA at that host would give a fixed necessarily-real
structure. Its number carrier supplies a fixed necessary Peano reference.
The fixed-reference lemma (*Finite-type necessitism*, companion proof
notes, 29 October 2026, §6)
then gives rigidity and ND of \(N_{\sigma_0}\) under the guard in
(4), a contradiction. Thus there is no possible real structure at
that \(\tau\), exactly the \(\tau\)-instance of NoReal. Since
\(\tau\) was arbitrary, the whole NoReal schema follows.

Conversely, NoReal makes each ANA and SOAN possible-real antecedent
false, so both schemas hold. SOAN implies ANA by its existing native
result. These are all directions of the claimed equivalence.

The phrase “AR fails” means a specified failed instance such as (4),
or metatheoretically that some instance fails. It is not an added
type-quantified sentence or finite-conjunction node. The equivalence
uses no represented power beyond what the source fixed-reference lemma
requires, and no Transversal premise. Transversal enters only the
additional guarded necessary-failure argument in §1.

The arithmetic-growth construction supplies exactly (4) at \(e\)
and every NoReal instance. Its ANA and SOAN truth is consequently
vacuous on the analytic side while its necessary arithmetic guard
is nonvacuous. Nothing here asserts contingency of an arithmetic
sentence or turns failure of Arithmetic Necessitism into failure
of the separate Necessity of Arithmetic principle.
