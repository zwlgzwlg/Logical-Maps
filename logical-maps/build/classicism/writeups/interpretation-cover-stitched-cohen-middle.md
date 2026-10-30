# Interpretation cover: identity-only over the stitched Cohen middle

GPT-6 Astra, prompted by Daniel Kodsi. 30 October 2026.

There is a model satisfying **current Barcan at every type and necessary Barcan
at propositions, while necessary Barcan fails at type et**. Thus even current
full Barcan does not let necessary propositional Barcan propagate to all
relational types.

This is one application of Dorr's existing interpretation-root construction to
the existing stitched Cohen model with a coalesced middle world. Only the
identity loop is needed at the new root.

## 1. The fixed old component and its forcing assumptions

Use the entire four-object model [[stitched-cohen-coalesced-middle]] in its
stipulated ambient Cohen extension V[G] of a ground model V of ZFC. Let
c be the new Cohen subset of the natural numbers. The old category is

    r --h--> s --a--> A
               --b--> B,

together with identities and the two composites ah and bh. There are no
other arrows. The old domains and transports are retained at every type.

A is the full extensional finite-type hierarchy over the natural numbers
built in V; B is the corresponding hierarchy built in V[G]. At s the
individuals are pairs of natural numbers, with a and b the projections.
For a relational type sigma_1 ... sigma_n t, an s-entity consists of an
arbitrary current extension in V[G], an admitted A-entity, and an admitted
B-entity. Its three components give its current and terminal profiles.
This includes n=0, the propositional case.

The individuals at r are those of s, and h is the identity on them. A root
relation is a pair (E,[u]): E is a ground set of current root tuples, and
u is a Cohen name for a whole s-entity which is forced by 1 to be invariant
under all finite bit-flips. Names are identified when their equality is
forced by 1. Transport along h is u evaluated in G. Every such pair is
admitted. These are exactly the old construction's domains; the cover
below neither enlarges them nor their futures.

Here are the old facts used in the proof, including the admitted witness
behind Barcan failure.

**Propositions.** At r,s,A,B the proposition domains are the full powersets
of the outgoing-arrow sets, with respectively 16,8,2,2 elements. For any
old arrow k:v->w, the map sending an arrow l out of w to lk is injective.
Precomposition of subsets is consequently onto the whole proposition
domain at w. Thus every old proposition transport is surjective.

**Invariant names and exact images.** Weak homogeneity under finite
bit-flips makes every sentence with ground and invariant parameters
decided by 1. In particular an invariant name for a subset of a ground
set names a ground subset, and an invariant name forced into a ground
set is forced equal to a ground element. Equality of invariant names
evaluated at G is exactly equality forced by 1. These facts supply the
old profile identity and its term-closure proof. Evaluation at A is
absolute in its fixed ground hierarchy: quantifiers still range over A's
old domains, not new subsets in the ambient extension.

For any ground set E of r-tuples, let hE be its image at s. It has an
invariant name, a(hE) is a ground set, and b(hE) is admitted at the full
terminal B. Hence the triple

    R_E = (hE, a(hE), b(hE))

has an invariant name and the old r-entity Y_E=(E,[R_E]) is admitted. At
each old future it contains exactly the transported members of E.

Take E to be the whole ground domain D_et(r). Then

    h[D_et(r)] = P^V(N x N) x P^V(N) x P^V(N).

The inclusion from left to right follows from the invariant-name facts;
the reverse uses the constant names for arbitrary ground triples. But

    X = (c x {0}, empty, empty)

is an admitted et-entity at s outside this image. Therefore the admitted
property H=Y_E of et-entities satisfies at r

    forall R^et Box H(R),

while at the accessible s, H(X) is false. This is a direct counterexample
to BF_et at r. Mere non-surjectivity without this admitted tester would
not suffice.

Given the stipulated old component in its ambient forcing universe,
the added root is a ZFC set construction.

## 2. The identity-only interpretation root

For each admitted type sigma fix a countably infinite set C_sigma of
auxiliary names. These are labels chosen before the new domains, not a
putative enumeration of those domains. Add one object o, with only the
identity endomorphism and with individuals C_e.

For every old object v include every total typed interpretation

    I_sigma : C_sigma -> D_sigma(v)

as an arrow I:o->v. For an old k:v->w, composition kI applies k's typed
transports to the assigned entities. All interpretations into **every**
old object are included, so this composition is closed. There are no
old-to-o arrows and no new old-to-old arrows.

At a relational type alpha=sigma_1 ... sigma_n t, a root entity F assigns
to each arrow out of o a subset of the full product of its target's
sigma_i domains. Admit exactly the profiles satisfying:

1. There is a finite set S of typed auxiliary names such that old
   interpretations into the same object agreeing on S have equal F-rows.
2. At each old interpretation I:o->v, the whole section
   (F_(kI)) indexed by arrows k out of v is an entity of D_alpha(v).

The identity row is unrestricted. The construction is recursive in type
complexity: root argument domains have proper subtypes, and all old
domains were given beforehand. A finite pin may mention higher-type
names, but these are the independent auxiliary labels and cause no
circularity. All row sets and interpretation sets are sets in the given
ambient universe. Transport is precomposition. Relational signature
constants may be top; no completeness assumption on the old component
is made.

For a name c of type sigma define its current lift hat(c). If sigma=e,
it is the individual c. At a relational type, give it empty identity
row and at an old interpretation I the current extension of I(c).
It is pinned by {c}, and for each old future k,

    hat(c)_(kI) = extension of k(I(c)) at k's target.

Its whole section at I is therefore the whole admitted entity I(c).
Thus it is admitted and I(hat(c))=I(c), as entity identity rather than
current coextension.

## 3. Closure and preservation of the old model

If two old interpretations into v agree on a parameter's finite pin,
then their composites with every arrow out of v also agree on that pin.
The transported parameter profiles agree at all those future rows, so
they are identical as whole old entities. For a term with finitely many
parameters, use the union of their pins and of the individual parameter
names. At same-target interpretations agreeing there, evaluation has
exactly the same whole environment. Its rows therefore agree. Bound
variables in abstractions and quantifiers still range over the full
target domains; none is restricted to images of root entities.

At each old interpretation the whole section of a term is its old term
denotation with those transported parameters. Old term closure proves
landing. At the root the identity row of an abstraction is unrestricted,
so the row defined by the formula is admitted. Application and transport
commute by their definitions. Singleton identity rows with empty old
sections are admitted predicates separating distinct root entities.

These are the finite-pin and whole-landing checks in Dorr's original
interpretation-root verification. They give the ordinary action-model
semantics of H and C: H-equivalent lambda bodies have equal rows and
therefore identical admitted profiles. No optional BF hypothesis is used
to justify Logical Equivalence. The C-complete family used elsewhere to
obtain Maximalism is not used for any of these closure checks.

No old domain or outgoing category has changed. Consequently every old
formula, including one quantified over old higher types, has exactly
its old interpretation. In particular H and X from Section 1 remain the
same admitted counterexample at r and s.

## 4. Current all-type Barcan

Fix an admitted type sigma and any root predicate F of sigma-entities.
Use the native dual form

    Diamond exists x^sigma F(x) -> exists x^sigma Diamond F(x).

Choose a finite name pin S for F. If a possible witness occurs at the
identity, it is already a current witness and proves the conclusion.
Otherwise let b belong to the F-row at an old interpretation I:o->v.
Choose a sigma-name c outside S. Change just the value of I(c) to b,
obtaining another allowed interpretation I' into v. It agrees with I
on S, so F has the same full row there. In particular F_I'(b) holds.

The current entity hat(c) transports along I' to b. Hence I' witnesses
Diamond F(hat(c)), proving the conclusion. The argument covers sigma=e
and every relational type, all admitted predicates, and all future
witnesses. Only one fresh name is needed at a time, so countably many
names at each type suffice regardless of the sizes of the old domains.

The proof relocates an old witness to a suitable interpretation with the
same predicate row. It does not require any fixed interpretation to be
onto. The identity-only choice also removes the separate loop-preimage
construction needed by a surjective-loop cover.

## 5. Necessary propositional Barcan

BF_t holds at o by Section 4. At each old object, Section 1 gives
surjectivity of every proposition transport. For an arbitrary old
predicate of propositions and a possible future witness, choose a
preimage of that proposition under the witnessing arrow. Application
and transport then give a current witness to the dual BF conclusion.
Thus BF_t holds at each old object, with all admitted tt tests.

Every object accessible from o is o itself or one of r,s,A,B. BF_t has
just been verified at every such object in its unchanged full domains.
Therefore Box BF_t holds at o. This is direct evaluation of the boxed
sentence, not necessitation of a merely current premise.

## 6. Necessary relational Barcan fails

There is a typed interpretation from o to r because every old domain is
inhabited. At its target, the Section 1 H/X counterexample refutes BF_et.
Section 3 preserves its interpretation, including quantification over
all old predicates. Hence Box BF_et fails at o.

Since et is relational, necessary relational BF fails, and the existing
necessary-all-type-BF implication derives failure of necessary all-type
BF. The question whether current all-type BF plus necessary relational BF
entails necessary all-type BF remains distinct.

## Sources

- GPT-6 Astra, prompted by Daniel Kodsi, *Fixed-component interpretation
  cover: a typed Barcan propagation corollary*, 30 October 2026,
  Sections 1, 3, 5–7 (unpaginated).
- GPT-6 Astra, prompted by Daniel Kodsi, *Independent review: fixed-component
  Barcan cover*, 30 October 2026, Sections 1, 3–6 (unpaginated), with the
  identity-only specialization in Section 5.
- Cian Dorr, interpretation-root construction, 19 October 2026;
  [[coalesced-pinned-interpretations-root]], sections “The construction,”
  “The entities hat c,” “It is a model of C,” and “BF holds at every type.”
  The whole-domain landing condition was added by Claude Opus 5.5, prompted
  by Cian Dorr. This supplies the existing root mechanism and fresh-name
  Barcan proof.
- GPT-6 Astra, prompted by Daniel Kodsi, *Stitched forcing model with a
  coalesced middle world*, 22 October 2026, Sections 1–7 (unpaginated);
  [[stitched-cohen-coalesced-middle]], “The forcing lemma,” “It is a model
  of C,” and “Verdicts at r.” The native account was integrated by OpenAI
  Codex, prompted by Daniel Kodsi, and written by Claude Opus 5.5, prompted
  by Cian Dorr.
- Neil Barton and Zachary Goodsell, *Continuum Contingency*, draft of
  14 October 2026, Section 7.1 and Section 8, Definition 1, for the inherited
  stitching framework.

## Paper references

- **Background: Continuum Contingency.** Barton, Neil, and Zachary Goodsell. Continuum Contingency. Draft dated 14 October 2026, 47 pages. Stitches a ground model of set theory to the canonical model of a forcing extension to show that Classicism with □Rigid Comprehension, □Relational Choice and an axiom of infinity is consistent with first- and second-order continuum contingency, together with □Atomicity at type t (Theorem 21) or with Recombination (Theorem 22, which refutes Atomicity at type t, Corollary 23); formalizes the coin-toss argument (Theorem 9). Read directly on 19 October 2026; locators refer to this draft. — Section 7.1; Section 8, Definition 1. The stitching framework of the retained old component, not the new fixed-component cover corollary.
