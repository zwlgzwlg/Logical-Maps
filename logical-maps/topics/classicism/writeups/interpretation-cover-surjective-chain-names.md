# Interpretation cover: surjective chain names

GPT-6 Astra, prompted by Daniel Kodsi, 30 October 2026.

In ZFC, using the C action-model existence/completeness input of Dorr's
interpretation-root construction, this model satisfies pure and fixed-signature
Maximalism, Atomlessness, current Barcan at every admitted type, and current
Truths are ND-necessary. It fails Weakly Inextensible Comprehension at type tt.

The old component models may have arbitrary Henkin domains and nononto transports.
The construction leaves them unchanged. Its completeness input is the same as in
the interpretation cover; no additional large-cardinal hypothesis is used. The
Max schemas refer to C and C(Sigma), where Sigma is a prescribed set-sized
free-constant signature. The Barcan and modal-collapse assertions are current.

## 1. Old components and typed names

Work with the relational type system of C: individuals have type e; every other type is a finite tuple of argument types followed by output t, including the empty tuple t itself. The type constructors are well-founded. A relation of type `(tau_1,...,tau_n)t` has an extension at an object that is a subset of the full product of its n argument domains. At t this is a truth value, identified with a subset of the singleton empty tuple.

Choose a set-sized family of C action models complete for closed pure C-consistent sentences, and make their objects and arrows disjoint. Every such sentence is true at a specified object in some member. This family is available from the source completeness input and set-theoretic Collection and Choice. Retain every object, outgoing arrow, typed domain, transport, and designated old symmetry of these components. Denote an old object by V and its domains by D_sigma(V).

For each admitted type sigma choose an infinite cardinal kappa_sigma, at least the cardinality of the Sigma constants of that type. The auxiliary sigma-name set is

    C_sigma = {sigma} x kappa_sigma x N.

Its chains are the sets with fixed sigma and fixed kappa_sigma coordinate. Thus each type has infinitely many disjoint N-chains. Choose an injection of the Sigma constants of each type into C_sigma. Auxiliary names are semantic coordinates; they do not introduce axioms or enlarge the reference theory C(Sigma).

There is no requirement that C_sigma dominate any old carrier or the new higher-type root domains. All types and name sets form sets, so the subsequent products and profile spaces are sets.

## 2. The enlarged category

Add a root object o. Its endomorphism monoid M consists of all typewise, chain-preserving maps f such that on each N-chain f is a nondecreasing surjection N -> N. There is no requirement that f be nonidentity on only finitely many chains. Every f is surjective on every C_sigma.

The identity and composites belong to M. On each chain a nondecreasing surjection starts at 0 and successive values increase by at most one, since a larger jump omits a natural number. Consequently

    f(n) <= n.

If g f fixes a name with level n, the inequalities n >= f(n) >= g(f(n)) = n force both f and g to fix that name. Therefore, for every finite typed name set S,

    g f fixes S  iff  f fixes S and g fixes S.             (1)

For every old object V and every total typed interpretation I, consisting of arbitrary maps I_sigma:C_sigma -> D_sigma(V), add an arrow I:o -> V. All such interpretations are retained, without an onto condition. If f is a root loop, set I f to be precomposition on names. If k:V -> W is an old arrow, set k I to be postcomposition by old transport on each assigned entity. Both are among the allowed interpretations. Along with the unchanged old compositions these operations are associative, since name-map composition and old transport are functorial.

There are no arrows from an old object to o, and no arrows between distinct old components. Evaluation is at the identity of o. The designated root symmetry group is trivial. Monoid arrows and designated symmetries are separate parts of the action-model data; no nontrivial root invariance condition is imposed on profiles.

## 3. Recursive root domains and transports

Put D_e(o)=C_e. A loop f transports an individual by f_e, and an old interpretation I transports it by I_e.

Recursively, at relational type sigma=`(tau_1,...,tau_n)t`, start with all profiles A assigning to each arrow a:o -> V a row

    A_a subseteq D_tau_1(V) x ... x D_tau_n(V).

If V=o, every argument domain in this formula is the previously defined root domain at the relevant lower type. If V is old, use its full pre-existing component domain. The arrow set was already defined using only auxiliary names and old domains, so this recursion is not circular.

Admit exactly those profiles satisfying both conditions:

**Finite typed pinning.** There is a finite set S of auxiliary typed names such that any two arrows a,b from o to the same object which agree on S give A the same row. For root loops agreement means equality of the images of these names. For old interpretations it means equality of the assigned whole old entities. This condition applies to all root loops, including the identity; the identity row is not freely isolated.

**Whole old landing.** For every interpretation I:o -> V, the entire profile over the old futures k:V -> W given by

    (rho_I A)_k = A_(k I)

is an element of D_sigma(V). Thus landing is not just a requirement about the extension at V. It includes every old future and every admission condition, including old symmetries, of that component.

For a root loop f define transport by the same reindexing formula `(rho_f A)_a=A_(a f)`. If S pins A, then f(S) pins rho_f A: agreement of a,b on f(S) makes a f,b f agree on S. Its old section at I is the already admitted old section of A at I f. Hence root transport lands back in the root domain. Old transport lands by the admission condition. Reindexing and the old functor laws prove identity and composition laws for these transports.

There are no additional root admission conditions. In particular, no arbitrary target tuple is replaced by a tuple transported from o.

## 4. Term closure and the C structure

Here is the whole-parameter fact needed for closure. Let a,b have the same target and agree on a finite pin S of a relational root entity A. For every arrow k out of that common target, k a and k b still agree on S: equality of names or of whole old assigned entities is preserved by postcomposition. Thus

    rho_a A = rho_b A

as entire entities at that target, rather than only as their current rows. For an individual root parameter c, include c in S; then its transported values agree directly.

Consider a term with finitely many free parameters. Treat the finitely many nonlogical constants occurring in it as additional parameters as well; their denotations have the singleton pins proved directly in §5. Include the finite pins of all relational parameters and the names of all individual parameters, including these constants, in one finite S. In particular, a closed Sigma term need not be empty-pinned. When two arrows agree on S, their entire transported free environments are identical in the same target model. Evaluate the term there with that environment. A lambda abstraction assigns its bound variables arbitrary elements of the full target argument domains. Quantifiers range over those entire domains. Since both evaluations have the same target and the same whole free environment, they give the same extension row. This proves finite pinning of the resulting term denotation.

For an old interpretation I, the entire future section of the term denotation is the ordinary old denotation of that term with the transported free parameters. This is proved by structural induction on the term, using reindexing for transport and the unchanged component operations. Because the old component is a C model, this denotation belongs to its existing domain. Hence the term lands at every old object and future.

The same argument covers application, Boolean operations, quantifiers and the modal operations. For example, the truth of Box phi at an arrow a is computed over every future k from its target, with the whole transported free environment; equality of those environments controls every such evaluation. There is no onto assumption in this closure proof. The all-type onto lemma below is an additional property, not a premise used to define the operations.

For clarity about current identity, every external singleton of an existing root typed domain has an admitted predicate: give that singleton the same row at every root loop and give it empty rows at every old interpretation. This is empty-pinned and has bottom old sections. It separates any two distinct whole root entities at the identity. Conversely, identical entities have identical membership in every predicate. Thus the Leibniz equality interpreted at o agrees with literal identity of individuals or whole profiles. Old identity and all its operations are inherited from the old models. Transport preserves identities by being a function on each domain.

Beta and eta follow from the standard profile interpretation on full argument rows. Necessary coextension at all future rows yields equality of the whole relation profiles; the Logical Equivalence axioms are validated as in the source action-model semantics. Together with closure and the unchanged old C structures, these checks establish a C action model, by the same action-model verification used in Dorr's cover. No extra optional principle from the claim is used to justify term closure or Logical Equivalence.

## 5. Named lifts and the fixed signature

For c in C_e its named lift is the individual c itself. For c in a relational C_sigma define hat(c) by empty rows at every root loop and, at every old interpretation I:o -> V, the current extension of the whole old entity I(c).

The singleton {c} pins hat(c). At every old I and every subsequent k,

    hat(c)_(k I) = the current extension of k_*(I(c)).

Thus its entire old section is I(c), so it lands. In particular,

    rho_I hat(c) = I(c).

At a root loop f, the root rows of both rho_f hat(c) and hat(f(c)) are empty, while their old sections are I(f(c)). Therefore `rho_f hat(c)=hat(f(c))` as whole entities. The analogous identity for individuals is immediate.

Interpret each Sigma constant by the named lift of its designated auxiliary name. No claim that these constants are fixed by root loops is made. Their transport along an old interpretation is precisely its assigned whole value, at every type.

## 6. Whole-entity lifting along a surjective root loop

Fix h in M. Since each h_sigma is onto, choose typed set-theoretic right inverses r_sigma and write r for their union, so h r=id. The map r is not required to be an allowed root loop; it need not be onto, and only its type preservation and right-inverse equation are used. For this particular h it in fact preserves chains and is strictly increasing on each chain, since distinct preimage fibres are ordered. ZFC supplies the choices.

At type e, h_e is onto D_e(o). Now let Q be an arbitrary admitted relational root entity, with a finite typed pin S. Construct a profile P as follows.

At a root loop g, ask whether an allowed root loop u agrees with g r on S. If one does, set P_g equal to the entire extension row Q_u. Any two such u agree on S and hence have the same Q row, so this is well-defined without choosing a distinguished u. If no such u exists, set P_g to the empty row. Notice that g r itself is not assumed to be allowed; only its finite restriction on S enters the matching test.

At an old interpretation I:o -> V, set

    P_I = Q_(I r)

as a row on the full V argument domains. This is meaningful because every typed interpretation into V is allowed, so I r is an available arrow.

**Pinning.** If g and g' agree on r(S), then g r and g' r agree on S. They have the same possible matching u restrictions and hence the same existence outcome and row. If old I and I' agree on r(S), then I r and I' r agree on S and Q gives equal rows. Thus the finite set r(S) pins P.

**Whole old landing.** At any old I and subsequent old k,

    P_(k I) = Q_((k I) r) = Q_(k (I r)).

The entire old section of P at I therefore equals the already admitted old section of Q at I r. This checks every future, not just the row at I, and preserves every old symmetry. It introduces neither a new old subset nor an externally decided equality guard. Since root symmetry is trivial, all of P's admission conditions are satisfied.

**Transport identity.** At a root future g after h, `(g h) r=g`, so g is an allowed match and

    P_(g h)=Q_g.

At an old interpretation I after h, `(I h) r=I`, so

    P_(I h)=Q_I.

Both equalities hold on every full target argument tuple. Thus `rho_h P=Q` as entire root entities. No induction assuming preimages of row arguments occurs: the rows on both sides are already on identical full target domains. The recursive construction of those domains is unchanged.

We have proved that every root loop acts onto at every admitted type, including e. The proof actually applies to any root monoid of typewise-surjective name maps under precisely this full finite-pin/whole-old-landing admission and trivial root symmetry. The monotone chain condition will instead be used for no-return and Atomlessness.

## 7. Current BF at every type: two witness cases

Use the native dual formulation. Fix an admitted root predicate F of type sigma-t and suppose `Diamond exists x^sigma F(x)` holds at o. Let S pin F. A witness is either at a root loop or at an old interpretation; these exhaust the arrows out of o.

If it is b in the entire root target domain at a loop h, the lifting lemma supplies a current root entity a with rho_h a=b. The same arrow h then witnesses `Diamond F(a)`.

If it is b in the entire old domain D_sigma(V) at I:o -> V, choose c in C_sigma outside the finite S. Define I' to agree with I on all names except c, and set I'(c)=b. This is an allowed typed interpretation. Since I and I' agree on S, their complete current F rows are equal; hence b is in F_I'. The root entity a=hat(c) transports under I' to b. For sigma=e this is the literal name; for relational sigma it is the admitted named lift of §5. Thus I' witnesses `Diamond F(a)`.

It follows that `Diamond exists x F(x) -> exists x Diamond F(x)` for every admitted sigma and every F. By the native dual equivalence, this is current full BF, `barcan-r`. The proof never asserts that an arbitrary old interpretation arrow is onto. Its fresh-name replacement argument is a distinct step, and no necessary BF statement is drawn from the current result.

## 8. Pure and fixed-signature Maximalism

For a closed pure C-consistent sentence phi, the chosen old family has an object V where phi holds. Any typed interpretation I into V is an arrow from o, and transported evaluation of the closed pure sentence is its unchanged old evaluation. Hence Diamond phi holds at o.

For a closed C(Sigma)-consistent sentence phi, only finitely many signature constants occur. Replace those constants by fresh variables of the same types and existentially close. The resulting pure sentence is C-consistent: a C-refutation would, by substitution of the original constants, give a C(Sigma)-refutation of phi. Therefore some old object V satisfies this pure existential closure. Choose its witnessing whole typed values for those finitely many constants. Assign these values to their designated auxiliary names and extend arbitrarily to a total typed interpretation I into V. Such extensions are available since all old typed domains are nonempty.

By §5, the transported interpretation of every constant occurring in phi is exactly its chosen whole old value. It follows that phi holds along I, so Diamond phi holds at o. This argument works for each sentence of the prescribed set-sized free-constant signature, however many constants it contains overall; each sentence uses only finitely many.

We have proved both native possibility forms. Their recorded C equivalences give the official distinctness forms `distinctness-schema-r` and `distinctness-signature-r`. The reference theories are fixed C and C(Sigma), not those theories augmented by Atomlessness, BF, or modal collapse. The old components and all their operations remain unchanged.

## 9. Atomlessness at every possible witness location

The native formula is

    forall p (Diamond p -> exists q (Diamond q and q<=p and q!=p)).

Let p be any root proposition with a true row somewhere, and let a finite typed P pin it. We construct an admitted splitter r for which p is true at both a true-r and a false-r row; then q=p AND r is a nonzero proper part of p. Here `q<=p` is entailment over all future rows, and distinctness follows from a row where p is true and q false.

**Root-loop witness.** Suppose p_f is true at a root loop f. Choose an entire individual chain containing no member of P; there is one because P is finite and there are infinitely many individual chains. Let a be its level-1 name. The value f(a) is either its level-0 or level-1 name, since f on this chain is nondecreasing and surjective. Replace f on this one chain by identity if f(a) has level 0, and by the surjection `n -> max(n-1,0)` if f(a) has level 1. Leave all other chains and types unchanged. The resulting f' is still an allowed loop, agrees with f on P, and changes the value at a. Thus p is true at both f and f'.

Define r to be true at a root loop g exactly when g(a)=f(a), and false at every old interpretation. This is {a}-pinned and has bottom old sections, hence is admitted. It is true at f and false at f', providing the required split. Changing an arbitrary single name would not in general preserve monotonicity; using an entirely fresh chain is essential.

**Old-interpretation witness.** Suppose p_I is true at an old interpretation I:o -> V. Choose a propositional auxiliary name c in C_t outside P. Alter I only at c, assigning the old whole top proposition once and bottom once, to obtain I_top and I_bottom. Both interpretations agree with I on P, so p is true at both. The admitted named lift hat(c) is true at I_top and false at I_bottom. It is the required splitter r.

These cases exhaust all possible true rows of p and yield the native universal Atomlessness principle, including propositions supported entirely on old components. The argument is not confined to currently true propositions.

## 10. Current Truths are ND-necessary

For a finite typed name set S define q_S by

    (q_S)_f is true iff the root loop f fixes S pointwise;
    (q_S)_I is false at every old interpretation I.

This is S-pinned, its whole old sections are bottom, and it is true at the root identity. By equation (1), a root loop f has a future root loop g with q_S true at g f exactly when f already fixes S. If f fixes S, identity supplies such a future. If it does not, deflationarity makes return impossible. Every old interpretation and all its old futures have q_S false. Therefore

    Diamond q_S = q_S

as whole propositions at o. This is an equality with Diamond; no equality with Box is used.

Let p be any currently true root proposition and choose a finite S pinning it. Every root f fixing S agrees with identity on S, so p_f is true. At all old arrows q_S is false. Hence q_S<=p throughout the whole profile, and therefore `Box(Diamond q_S -> p)` is true at o. Together with the actual truth of q_S, this witnesses the exact native `Box_ne p`.

Since p was arbitrary, `forall p (p -> Box_ne p)` holds at the root. This is `distinctness-preserving-collapse`, the current Truths are ND-necessary principle. All of the conjunction in the initial claim has now been proved at the same root in the same model.

## 11. Weakly Inextensible Comprehension fails at tt

The exact native clause is

    WeaklyInextensible(Y) := forall X ((forall p (Yp -> Box Xp)) -> Y<=X).

Choose individual level-1 names c_n in pairwise distinct chains. Let p_n be the proposition whose root truth row says that the loop fixes c_n, with false old rows. They are admitted, nonzero and pairwise distinct: collapsing the first step of one chain distinguishes its proposition from the others. For every root loop g,

    rho_g p_n = p_n if g fixes c_n, and bottom otherwise;

every old transport of p_n is bottom. This is a whole-profile calculation: if g lowers c_n to its level 0, subsequent root maps cannot return it to level 1; old rows are always false.

Let E have extension {p_n : n in N} at every root loop and empty old rows. It is empty-pinned and lands as bottom. Suppose Y is currently coextensive with E and weakly inextensible, and let S be a finite typed pin of Y. Choose k whose ENTIRE individual chain is disjoint from S. Let h collapse that chain's first step by n -> max(n-1,0), leaving all other chains and types unchanged. It fixes S, so Y_h has the same full row as Y_id; in particular Y_h(p_k) holds.

Define X at tt by the full root rows

    X_g = D_t(o)                     if g fixes c_k;
    X_g = D_t(o) minus {p_k}         otherwise.

At every old object V give it extension {bottom_V}. The root rule is {c_k}-pinned. Its whole old section is the old closed term lambda q.(q=bottom), at every subsequent old future, so X is admitted. This old landing is a whole old entity, not merely a selected current subset.

Every current Y-member is some p_n and necessarily has X. At loops fixing c_k this is immediate. At any other root loop, rho_g p_n is p_n or bottom; for n=k it is bottom, and for n different from k neither option equals p_k. At old arrows every transported p_n is bottom, which belongs to X. Hence forall p(Yp -> Box Xp) holds.

But at h, the full target argument p_k belongs to Y_h and does not belong to X_h. Thus Y<=X fails, contradicting the native clause. E therefore has no currently coextensive weakly inextensible representative, proving failure of the tt instance of Weakly Inextensible Comprehension.

There is no conflict with current full BF. The lifting theorem gives a preimage of the future p_k under h, but none of E's actual members is such a preimage: their h-images are bottom or other p_n. BF does not force that new preimage into Y. The obstruction specifically retains the full target-domain quantifier rather than restricting it to the transported actual family.

## Sources

- GPT-6 Astra, prompted by Daniel Kodsi, *Surjective-name interpretation cover*,
  30 October 2026, §§1–10 (unpaginated), for the complete construction and proofs;
  *Surjective-name lifting with old landing*, same date, §§1–3, for the all-type
  right-inverse row-completion argument; and *The surjective-name cover fails weak
  IC at tt*, same date, for §11's direct same-model obstruction.
- Cian Dorr, interpretation-root and pinned-substitution constructions,
  19 October 2026, especially “BF holds at every type”, for the complete old
  family, arbitrary interpretation arrows, finite typed pins, whole old landing,
  named lifts and fresh-name Barcan argument.
- OpenAI Codex, prompted by Daniel Kodsi, *Observer covers and Boolean completeness*, 26 October 2026,
  §8 (unpaginated), for the unrestricted cover with unchanged Henkin targets
  and trivial root symmetry.
- Andrew Bacon and Cian Dorr, *Classicism*, draft of 16 May 2023, Appendix D,
  Proposition D.5(2), pp. 74–75, construction pp. 76–77; Proposition D.6, p. 76,
  for monotone-surjection action models and the surjective-action Barcan method.
  The fixed-initial-segment no-return argument is also recorded for the
  finite-support monotone-surjection model by Claude Fable 5.1, prompted by
  Cian Dorr, 23 September 2026.
- The fixed-pin cylinder method also occurs in the supported product of free
  monoids with glued constants, argument of 25 October 2026, and in the
  progressive interpretation cover. The argument above verifies its use with
  this different root monoid and proves whole-old-landing preservation explicitly.
