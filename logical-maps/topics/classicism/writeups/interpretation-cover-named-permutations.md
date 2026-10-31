# Interpretation cover: named permutations

The unrestricted permutation construction is from OpenAI Codex, prompted by
Daniel Kodsi, *Observer covers and Boolean completeness*, 26 October 2026, §§8.2–8.3, after Cian Dorr's
interpretation-root machinery. The Atomlessness and Vicinity arguments are by
GPT-6 Astra, prompted by Daniel Kodsi, 29 October 2026; the explicit fixed-
signature expansion is dated 30 October 2026.

## 1. Category and domains

Work in ZFC. Use the source interpretation-root construction's action-model
existence input to choose a set-sized family of pointed C action models
witnessing every C-consistent pure sentence. The finitary language has only
a set of sentences, so Collection and Choice supply such a family once
the source representation theorem is given. This inherited input is not
a new completeness theorem or an exact consistency-strength claim.

Keep all old objects, arrows, typed domains and semantics unchanged. For
each type \(\sigma\), choose an infinite auxiliary name set \(C_\sigma\)
large enough to dominate the old domains. Take a large enough common
cardinality that there are onto interpretations with infinite fibres and
distinct name coordinates for the given set-sized signature \(\Sigma\).
Only \(C_e\) is a root entity domain: higher auxiliary names are indices,
whereas root higher-type entities are the profiles defined below.

Add a root \(o\). Its loops are all typed permutations of the name sets.
Every typed interpretation \(I_\sigma:C_\sigma\to D_\sigma(V)\) into
every old object is an arrow \(o\to V\). Interpretations need not be
onto or injective. Composition is permutation composition, \(Ig\), or
old transport \(kI\). There is no old-to-root arrow. The designated
symmetry group at the root is **trivial**; the permutation arrows are
not an extra equivariance constraint.

At a relational type \(\rho=\sigma_1\cdots\sigma_m t\), a root
entity is a bit profile \(A(h,\bar a)\) for every outgoing arrow and
every tuple in its target. Admit exactly the profiles satisfying:

- A finite typed set of names pins it: same-target arrows agreeing on
  that set give the same rows on **all** target tuples. This applies to
  every root loop, including identity.
- At every old interpretation \(I:o\to V\), the whole section
  \((k,\bar a)\mapsto A(kI,\bar a)\) is an already admitted entity
  of \(D_\rho(V)\).

Root transport is precomposition, \((g_*A)(h,\bar a)=A(hg,\bar a)\).
Old transport is its admitted section. Individuals transport by the
corresponding name map. Evaluate at the root identity.

If \(S\) pins \(A\), then \(gS\) pins its transport. More strongly,
arrows agreeing on \(S\) give equal **whole transported entities**:
every future composite still agrees on \(S\). For individual parameters
include their singleton name pins. Thus at arrows agreeing on the union
of a term's parameter pins, the whole transported environment is identical.
The term is evaluated in the same target structure with the same assigned
bound arguments. All bound quantifiers retain the entire target domains.
At an old target the term's full section is the old admitted denotation.
This verifies pinning and landing for application, abstraction, equality,
quantification and the native modal terms. The usual action-model proof
therefore validates C, with Logical Equivalence's theoremhood restriction.
No higher Henkin domain is completed and no current truth bit is added
independently at identity.

For a relational name \(c\), its named lift \(\widehat c\) has empty
rows at root loops and interpreted rows at old arrows. At \(I\), its
whole transport is \(I(c)\), because every later row is the corresponding
row of \(k_*I(c)\). Its pin is \(\{c\}\). At individual type use the
literal name. Root permutation transport sends the named lift to the
lift of the permuted name.

## 2. Current BF and Relational Choice

The source's current BF proof is the dual form
\(\Diamond\exists x\,Fx\to\exists x\,\Diamond Fx\), at every
admitted type. If a witness occurs at a root loop, that loop has an
inverse and is onto at every type. Lift the witness along the loop.

If it occurs at an old interpretation \(I\), let \(S\) pin \(F\).
Match \(I\) on \(S\) by finitely modifying an onto infinite-fibre
baseline interpretation \(b\). This remains onto on each name set.
Named lifts show that \(b\) is onto on the actual root typed domains
as well: any old entity is the value of an appropriate name. The future
row of \(F\) is unchanged because the pin is matched, so lift its witness
along \(b\). This proves current all-type BF, with no assumption that
every old interpretation or old arrow is onto.

Every external relation on the current typed domains is the current
extension of an admitted relation: use that same table at every root
loop and empty rows at all old targets. It has empty pin and bottom old
landing. In external ZFC, choose an output for every input of a current
serial relation and represent its graph by such a table. This is exactly
current Relational Choice, including individual outputs as relational
graphs. It is not Functional Choice and is not a boxed assertion. The
existing RC-to-Zorn consequences need not be separately listed.

## 3. Vicinity and Atomlessness

Let \(v\) be true at all root loops and false at every old arrow. It is
empty-pinned and lands as bottom. It is currently true. For any current
truth \(q\), each root loop \(g\) has the continuation \(g^{-1}\)
returning to identity, so \(\Diamond q\) holds there. At old arrows
\(v\) is false. Hence \(v\leq\Diamond q\) for every current truth
\(q\), the native Vicinity condition.

For Atomlessness let a nonbottom proposition \(p\) have finite pin
\(S\). There are two exhaustive cases for a coordinate witnessing it.

If \(p\) is true at a root permutation \(g\), choose distinct individual
names \(a,b\) outside \(S\). Both \(g\) and \(g(a\ b)\) agree
on \(S\), so \(p\) is true at both. The proposition with root row
\([h(a)=g(a)]\) and zero old rows is \(\{a\}\)-pinned, lands as
bottom, and separates those two coordinates. Intersecting it with \(p\)
gives a nonzero proper part of \(p\).

If \(p\) is witnessed at an old interpretation \(I:o\to V\), take
a fresh propositional name \(c\notin S\). Modify only its value in
\(I\), once to top and once to bottom. Both interpretations are allowed
and agree on \(S\), so \(p\) stays true. The named lift \(\widehat c\)
separates them. Its entire old section lands, not merely its truth value
at these two witnesses. Again intersection gives a nonzero proper part.

Thus every possible proposition splits, including those supported only
in old components. This is stronger than merely refuting Actuality.

## 4. The fixed signature and Possibility+

Assign each constant of \(\Sigma\) its own typed name coordinate.
Use the literal name at \(e\) and the named lift otherwise. Constants
need not be invariant under root loops. Distinct relational named lifts
can have equal empty current extensions while being different whole
intensions, distinguished by their independent old values.

Let \(P(\bar x)\) be a \(\Sigma\)-formula consistent with fixed
\(C(\Sigma)\), with only the displayed individual variables free.
Replace its finitely many constants by matching fresh variables and
existentially close all of them and \(\bar x\). The resulting pure
sentence is C-consistent: a C-refutation would, by universal instantiation,
refute the original formula. This uses the native free-constant convention;
there are no extra nonlogical axioms on the signature.

An unchanged old component therefore supplies whole typed values for
the constants and values for \(\bar x\). Now let \(\bar u\) satisfy
the exact Possibility+ signature antecedent at the root: its individuals
are pairwise distinct and differ from every individual constant occurring
in \(P\). They are distinct auxiliary coordinates, disjoint from the
constant coordinates on which a potentially conflicting prescription
would be made. Assign the component's constant and variable values to
these coordinates and extend to an arbitrary typed interpretation.
The target values may coincide; interpretations are not required to be
injective. Unused constant names impose no restriction.

Along that interpretation, named lifts land as precisely the chosen
whole constant values, so the unchanged target semantics makes
\(P(\bar u)\) true. Thus \(\Diamond P(\bar u)\) holds. The empty
tuple case supplies signature Maximalism; pure Maximalism and the other
recorded weaker possibility consequences follow by existing closure.

A fixed signature exceeding the name supply requires a larger size instance,
not merely a new label on the same set structure. Strong Possibility,
Boolean Completeness, observer conditions and boxed variants are not
asserted.
