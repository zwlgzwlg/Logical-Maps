# A signature-Maximalist point with both local power principles

OpenAI GPT-6, prompted by Daniel Kodsi, found the construction on 26 November 2026. Two independent AI research agents checked the ordinary proof. The model works for any fixed set-sized
signature Σ of free nonlogical constants. It realizes every instance
of signature Possibility/Maximalism and every instance of Weakly Rigid
Power and Rigid Power at the *same* designated point. It does not claim
the boxed power schemata there.

## The auxiliary point theory

Expand Σ by an individual marker if the language otherwise has no
individual term. For each nonempty finite argument tuple of admitted
types τ add an uncountable set of fresh relation constants b^τ_i of
that arity. All of these are auxiliary. Let Θ be the expanded language.
Take the pointed C theory

    T = C(Θ) + { □¬b_i(t) : b_i auxiliary, t any closed Θ-tuple of its input types }.

Terms may involve the very predicate being tested, any other auxiliary,
and arbitrary typed quantifiers or lambdas. The axioms are persistent
by S4. Every pointed Σ-model expands to a model of T by giving every
b_i its constantly bottom value and choosing any available individual
as marker. In particular each C(Σ)-consistent closed Σ-sentence stays
consistent with T. No maximality is required for Θ.

For a theory U of this kind, choose a set of pointed models witnessing
each U-consistent closed Θ-sentence. Retain their old cones: U consists
of boxed conditions besides C, so their successor evaluations still
satisfy U. Adjoin a new root with one independent entrance into each
chosen point and distinct arrows for its old postcomposites; its only
internal arrow is its identity. As individuals take the individual
names; in this application distinct names are separable by models of
U, since all b_i can be bottom and Σ is free. Every relational entity
at the root has an arbitrary current extension and the old trace of a
single closed Θ-term of its type, evaluated with the designated constants
at each exit. Identify old descriptors iff U proves their identity.
The choice of components makes this exactly equality of traces on all
old entrances and their continuations. Individual tuples are compared
coordinate by coordinate.

Assign each relational symbol its own descriptor and a chosen actual
row. This construction is the signature-definable root with its
component family restricted to U. Term transport follows by induction:
a lambda has its actual extension on all current arguments, and on
every old exit has its old lambda value with the finitely many
parameters replaced by their descriptors. A quantified formula
therefore uses the entire old target domain, including newly
available arguments. The designated old cones, their internal arrows,
and their domains are unchanged. For clarity on the size of the auxiliary language, compactness here can
be obtained by taking an ultraproduct of pointed models for its finite
fragments. In a many-sorted presentation take objects, arrows and the
fibre of each admitted type, with transport, application, current truth
and the distinguished point and assignments. Existence of a separating
future row for unequal relational entities is first-order at each type.
The action laws and each fixed term-closure instance pass to the
ultraproduct; quantifiers translate to quantification over the target
fibre and necessity to quantification over arrows from that target.
Łoś's theorem for this set-sized language gives the required Henkin
action point. Thus no countability assumption on the whole auxiliary
signature or external powerset fullness is needed.

Let R be this root for U=T and interpret every auxiliary b_i with
empty current row. For every actual tuple a of the matching types,
choose its old descriptor t. Then b_i(a) is false at the identity and
at every old arrow, since the old points satisfy □¬b_i(t). Thus
□¬b_i(a) holds at R. R satisfies T, and it satisfies signature
Maximalism since its old entrances realize every C(Σ)-consistent
closed Σ-sentence. In the final Σ-reduct all auxiliary entities remain
in their carriers; their names are unnecessary for quantifying over
them.

## A fresh predicate at a second root

We prove that a weakly rigid F at R can have only finitely many
different old descriptor tuples among its current members. Write u
for its old descriptor. Each represented s satisfies T ⊢ u(s) by
weak persistence and completeness of the old family. For every b_i
of this arity, the preceding necessary nonmembership is a true test
on every current F-member. Weak inextensibility gives F≤¬b_i, hence

    T ⊢ ∀x (u(x) → ¬b_i(x)).

All tuples in this proof can have mixed argument types. For empty
input arity there is at most one represented tuple already.

Suppose infinitely many different descriptors are represented. Choose
a countable list s_1,s_2,… pairwise inequivalent modulo T. Pick one
auxiliary b of the required arity absent from u and all of these terms.
The uncountable supply is used only here. Set

    T₀ = T + □∀x ¬b(x).

The s_i remain pairwise inequivalent modulo T₀. To see this, start
with any T-model separating two of them and change just the chosen
constant b to the constantly bottom relation. For every other
auxiliary c the new condition □¬c(t) is the old ground instance
□¬c(t[b:=bottom]); all axioms for b now hold directly. Replacing
b throughout an arbitrary term by the closed bottom lambda is valid
under all typed binders. Since s_i,s_j do not use b, their distinction
survives. Every T-theorem u(s_i) is still true in T₀.

Form an independent root K over a T₀-complete family by the same
recipe, with all auxiliary current rows empty. It satisfies T₀:
the root part of each original ground nonmembership has empty current
row, all proper exits satisfy it, and b vanishes throughout the cone.
In particular K satisfies u(s_i) for each i. We keep this underlying
action model fixed during the following reinterpretation.

Take any finite subset of T, and write t_1,…,t_l for the finitely
many tuple arguments occurring in the listed □¬b(t_j) axioms. No
restriction is put on occurrences of b in these t_j or in other
predicates' ground axioms. Choose i with s_i not T₀-equivalent to
any t_j[b:=bottom]. Alter only the assigned value of b at K: its
current row is now the singleton whose unique tuple is the current
value of s_i, while its proper old trace is still constantly bottom.
Every such row is an available relation. The carriers, arrows and all
other designated values remain unchanged. In particular u(s_i)
remains true, as it is b-free. Also b(s_i) now holds.

On every proper entrance the denotation of each t_j under this
assignment is the denotation of t_j[b:=bottom]. Since the old T₀
family separates its trace from that of s_i, the entire current
tuple t_j differs in some coordinate from s_i. This checks each of
the finitely many challenged □¬b(t_j), at the identity and on all
old futures. Every ground condition for every other c holds even if
its argument mentions b: at the identity c's current row is empty
and at every proper exit all the original assignments remain. The
new point therefore satisfies the chosen finite fragment and
∃x(u(x) ∧ b(x)).

Compactness yields a point of all T where this existential is true.
It is a closed Θ-sentence and so is witnessed in the original old
component family of R. This contradicts the displayed entailment
forced by weak inextensibility. Therefore the represented descriptor
support of F is finite.

## Both powers at the designated point

Let a_1,…,a_m be actual F-tuples representing its now-finite
support. Give a root tester full actual extension and old descriptor
the union of the tuple-haecceities of their descriptors, using bottom
when m=0. Every actual F-tuple passes the test necessarily. Weak
inextensibility bounds F by the tester; conversely weak persistence
carries every a_i through every future. At any proper arrow h the
whole transported F is consequently the finite union of the
haecceities of h(a_i). This statement includes all old
postcomposites; it does not assert a finite actual extension at R.
Each such old transport is fully rigid. Thus the originally weakly
rigid F is fully rigid, since rigidity is necessary weak rigidity.

The same reasoning applies to each current weakly rigid X≤F, whose
current support is a subset of that of F. At any old point h, every
weakly rigid X≤hF is literally the union of the haecceities of its
finite actual extension: use that finite union as its own
weak-inextensibility test, with the other inclusion by persistence.
It is rigid and is the transport of a current rigid subrelation of
F: for each of its finitely many distinct tuples choose one of the
a_i mapping to it and take the union of those original haecceities.
By persistence this original rigid union entails F, even when
different original tuples later merge.

It follows that the canonical weak and full power predicates agree
as intensions at R. The full version is persistent since both
rigidity and necessary entailment persist. For weak inextensibility
at R, a test necessary on each current power member covers the old
members through precisely the preimages just constructed. At any
old point the bound itself has a finite actual extension and is rigid;
the same finite-union and preimage argument there makes its power
fully rigid. Thus the common power is fully rigid at R. In particular
all instances of both requested local power principles hold.

## Other local verdicts

The individual names at the root give the signature Possibility+ instance
as well. For an instance with free individual variables, a root tuple
satisfying its side condition is a tuple of distinct names absent from
the formula. Substituting those names preserves consistency over the
marked public language, and assigning all the auxiliary predicates
bottom supplies the required old pointed component. With an empty tuple
this is signature Maximalism in its possibility form.

Barcan at $t$ fails. In the fresh-predicate proof take $u$ to be the
universal property of propositions and choose the $s_i$ to assert exactly
$i$ individuals, $i\ge 1$. These pure propositions have pairwise
inequivalent $T$-traces by finite classical models with all auxiliaries
bottom. Hence some component has a proposition instantiating the fresh
auxiliary $b$. Every current proposition necessarily satisfies its
complement at the root, so this complement refutes the unboxed Barcan
instance there. All results concern the designated point.

The [ordinary signature-definable root](coalesced-definable-root-signature.html)
supplies the independent-component architecture. The October
[finite-bound argument](https://github.com/dkodsi/Logical-Maps/blob/67b116acaf7cee286614307468f5361f6a195c6e/submissions/classicism-results-2026-10-24-v2/source/research/2026-10-22/notes/maximalism-modal.md#L348)
treats each externally finite bound. The auxiliary ground nonmembership
theory and the second-root compactness argument ensure simultaneous
finite descriptor support here.
