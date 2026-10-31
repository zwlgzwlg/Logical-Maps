# Stitched forcing model with countably closed subset forcing

Source construction and separation: **GPT-6 Astra, prompted by Daniel Kodsi**, *Finite-Type
Necessitism and Analytic Non-Contingency*, 30 October 2026, §7, “A fixed continuum and a
changing power” (unpaginated).

The explicit carrier induction and the canonical-power details below were written by
OpenAI Codex, prompted by Daniel Kodsi, 30 October 2026. The underlying action-model
construction and its necessary Rigid Comprehension are Barton and Goodsell's *Continuum
Contingency*, draft of 14 October 2026, §7.1 and §8, Definition 1 and Lemmas 11–19.

## 1. The exact construction

Use the `stitched-forcing` group with trivial root symmetry and
\[
P=\operatorname{Fn}((\omega_1)^V,2,{<}(\omega_1)^V),
\]
the ground set of countable partial binary functions, ordered by reverse inclusion. The
union of a descending countable chain is a condition; the usual fusion deciding each
coordinate of an omega sequence shows that forcing adds no subsets of omega. Bit-flip
automorphisms make any two conditions compatible after an automorphism, so the forcing
is weakly homogeneous and meets the group's ground-definability requirement. The union
of the generic filter is a total binary function on the ground omega_1. For every ground
subset, densely some fresh coordinate disagrees with it; its support is therefore new.

The terminal object C_0 is the full extensional relational hierarchy of V[G], with omega
as its individual domain and two truth values. The root and transport h are exactly the
group's construction. At each relational type a root relation consists of an arbitrary
ground set E of root tuples and a terminal relation D definable from ground parameters.
Its transport is D. The group's construction supplies the compatible curried function
coordinates. In particular, “empty root extension” below refers to its current truth
extension, not a claim that all higher curried coordinates are bottom.

The shared rigidity criterion is
\[
(E,D)\text{ is rigid}\quad\Longleftrightarrow\quad D=h[E].
\]
This uses both objects and the leading box in rigidity; at the terminal object every
relation is rigid. A carrier with injective transport additionally has necessarily
distinct instances. These are the concrete stitching criteria, not an assumed general
rule about preserving real structures.

The construction is understood with the same relative-consistency forcing conventions
as the existing stitched records. All natural numbers, ground sets and finite type
hierarchies in this proof are internal to that construction; no external omega-standardness
or extra large-cardinal premise is used. The generated constructible-ground variant uses
exactly the same argument.

## 2. Same-type rigid real structures at every relevant type

Write R for the ground real field, coded by rational Dedekind cuts. Since no subsets of
omega are added, V[G] has exactly these reals and these cuts. The individual type has
internally countably many members at both objects and cannot carry a complete ordered
field with full predicates. The types whose terminal domains are finite likewise cannot
carry one. Their root domains are also finite: this follows by induction for types built
only from t. Thus ANA's antecedent is false at those types.

For completeness, every other admitted type is relational and has a uniformly
ground-definable embedding j_tau:R→D_tau(C_0). This assertion includes types with e in
higher argument positions. Prove it by induction on the type, along with the existence
of a uniformly defined countable sequence of distinct elements at every infinite type.
The base e has its natural-number sequence. Every relational type has two distinct
uniform elements, constantly false and constantly true, recursively at a functional
codomain. At tau=alpha→beta:

* If D_beta is infinite, beta is relational (the type rule forbids beta=e), so by
  induction it already has an embedded R. Constant functions give an embedded R in
  D_tau and a countable sequence there.
* Otherwise D_beta is finite and has at least two distinct uniform elements. If
  D_alpha is infinite, use its ground-defined distinct sequence a_n. A subset u of
  omega is sent to the function taking the second selected value exactly at those
  a_n with n in u, and the first value elsewhere. Rational-cut coding embeds R into
  this family and also supplies a countable sequence.
* If both domains are finite, the function domain is finite, the excluded case.

The recipes use ground parameters and are uniform in r; they remain formulas on the
whole terminal domains, including new arguments, with the indicated default value.
They do not suppose that a ground function already had new arguments in its domain.

For each r choose the root lift x_r whose current relational extension is empty and
whose terminal extension is j_tau(r). The construction supplies this lift, and the
uniform recipes give a ground-coded set of these lifts. Injectivity of j_tau ensures
that distinct r have distinct lifts and that h is injective on this set. Let the root
carrier be E={x_r:r∈R}; pair it with the ground-definable terminal carrier j_tau[R].
Pair the transported ground field's order, addition graph, multiplication graph and
natural-number subproperty on E with their exact images under j_tau. All these current
extensions are ground sets, all their terminal extensions are definable from ground
parameters, and all are admitted simultaneously. The rigidity criterion proves that
the carrier and all four structural relations are rigid. Injectivity on E gives ND
for the carrier's instances. No global ND claim is needed.

At the root, every admitted predicate restricted to E is a ground subset; the ground
real field proves the complete-ordered-field conditions. At the terminal object,
a nonempty bounded family B of old reals may itself be new, but
\[
\{q\in\mathbb Q:\exists b\in B\ (q<b)\}
\]
is a rational cut in V[G], hence belongs to V. Its old real is the least upper bound
of B. Therefore the field remains complete for every admitted terminal subproperty,
not merely for ground families. The field laws and order are unchanged. Its selected
natural-number subproperty is the least inductive subproperty at each object, by
induction on the same internal omega. Thus the paired structure is necessarily a
real structure with RigidStr, at the original type tau. This proves the full all-type
ANA schema. At et the binary-function construction gives an actual real structure,
so the positive verdict is not entirely vacuous.

## 3. A genuine canonical second-power obstruction

For source e the canonical counting arithmetic is the ground natural-number structure
at both objects. The induction characterization of the canonical number property
uses the admitted pair of the ground numerals with their terminal numeral images;
all canonical numbers are those numerals, and transport matches them bijectively.
The successor is injective and omits zero at both objects, so Box I*_e holds.
Put H_0=N_e and H_(k+1)=P(H_k), using the native canonical rigid power.

A root member of H_1 is the paired predicate (A,h[A]) for a ground subset A of H_0;
conversely every such pair is a member. Since forcing adds no subsets of omega,
these exhaust the terminal members of H_1. Transport on H_1 is therefore bijective,
and H_1 is rigid. At the root, members of H_2 are exactly the analogous pairs for
ground subsets of the ground H_1. Terminally every subset of that fixed H_1 is an
available predicate and is rigid, since the terminal object sees only itself.

Choice in V gives an injection i:(omega_1)^V→H_1, since H_1 codes all ground subsets
of omega. If S is the new generic subset of omega_1, i[S] is a new subset of H_1:
a ground i[S] would recover S by the ground inverse. Hence it determines a terminal
member of H_2 which is not the image of any current member.

Form the root predicate K whose current extension is all the current H_2 and whose
terminal extension is exactly h[H_2(root)]. This is admitted: the latter set is
definable from the ground set of all subsets of the ground H_1, together with the
uniform numeral and predicate recipes. Every current H_2 member necessarily has K,
but the terminal member corresponding to i[S] does not. This directly violates
inextensibility of H_2 at the root. The n=1 FTN instance requires its rigidity,
so that instance fails despite its true Box I*_e antecedent.

## 4. Native scope

Record only ANA and failure of FTN as this model's new arguments. The existing
stitched group supplies necessary Rigid Comprehension, necessary Relational Choice,
and its other unconditional verdicts. In particular this gives the joint package
Box RC + ANA + not FTN, and the FTN implication derives failure of Rigid Power.
No adds-a-real condition is claimed. No arbitrary-ground CH preservation is claimed:
no new reals alone does not preclude changing their cardinal arithmetic.

This is the two-object ground/extension action model. It is not the separately
recorded full Boolean-valued model with algebra 2×RO(P), whose semantics, carriers,
and native positive package differ. No verdict is transferred between them.

## Paper references

- **Background: Continuum Contingency.** Barton, Neil, and Zachary Goodsell. Continuum Contingency. Draft dated 14 October 2026, 47 pages. Stitches a ground model of set theory to the canonical model of a forcing extension to show that Classicism with □Rigid Comprehension, □Relational Choice and an axiom of infinity is consistent with first- and second-order continuum contingency, together with □Atomicity at type t (Theorem 21) or with Recombination (Theorem 22, which refutes Atomicity at type t, Corollary 23); formalizes the coin-toss argument (Theorem 9). Read directly on 19 October 2026; locators refer to this draft. — §7.1; §8, Definition 1 and Lemmas 11–19
