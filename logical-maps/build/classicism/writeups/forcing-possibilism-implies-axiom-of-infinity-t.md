# Forcing Possibilism implies Axiom of Infinity at t

The theorem is already credited to Andrew Bacon, *Could the truths of mathematics have been different?*, 9 October 2025 draft, §6, p. 27. The native record retains its original proof and certificate. The supplement below handles internal finite cardinalities directly, including those which are externally nonstandard in a Henkin model.

## Internal-finiteness proof supplement

OpenAI Codex, prompted by Daniel Kodsi, 25 October 2026, §§1–4 of *Forcing Possibilism implies quantified Infinity: internal proof* (unpaginated; direct source `misc`).

1. Exact target and scope
-------------------------

Work in the map's fixed relational Classicism C. Let

  U := lambda p:t. top.

The existing result forcing-possibilism-implies-axiom-of-infinity-t has
premise the database's unboxed strict Forcing Possibilism and conclusion

  not exists N:((tt)t).
      FiniteCardinality_t(N) and N(U).

Use the precise impredicative Frege definition from background.md:

  0(X) := forall x. not X(x),
  Suc(Y)(X) := exists a. X(a) and Y(X-a),
  X-a := lambda x. X(x) and x != a,

  FiniteCardinality_t(N) := forall W.
    [W(0) and forall Y (W(Y) -> W(Suc(Y)))] -> W(N).

Object predicates, the induction predicates below, and graph relations
are admitted lambda abstractions in the original type system. No new
symbols or infinitary logic are needed. All reasoning below is unboxed
unless a box is explicitly displayed (none is needed in the proof).

Write DedFin(X) for the database's Fin(X): every admitted total injective
binary relation from the current Xs to the current Xs is surjective.
This is GRAPH-Dedekind-finiteness, not operation-Dedekind-finiteness.
No operation with individual output is used or required.

For propositions, x <= y abbreviates the algebraic entailment order
x and y = x. Classicism proves the Boolean-algebra laws for this order.
In particular bottom is least, top is greatest, and

  s or a <= z iff (s <= z and a <= z).

The proof uses only FP's carrier-t instance, its finite disjunct, and its
requirement that the representing interval be proper (p != top). It does
not use the strict cardinal bound. It therefore also works if that bound
is replaced by the non-strict variant, with the finite disjunct and proper
interval requirement retained. This observation does not identify the two
full forcing principles or refine the further FP proposal.

2. Internal finiteness implies graph-Dedekind-finiteness
--------------------------------------------------------

At any fixed admitted carrier type, form the induction predicate

  V := lambda Z. forall X (Z(X) -> DedFin(X)).

The zero case holds because 0(X) says there are no current Xs. Every
injective self-relation on such a carrier is vacuously surjective.

For the successor step assume V(Y), and suppose Suc(Y)(X). Its definition
supplies a with X(a) and Y(X-a). Thus DedFin(X-a) by the induction
hypothesis. Let R be any admitted total single-valued injective graph on X.
Choose b in X with R(a,b); this is one existential witness, not Choice.

The transposition graph

  T_ab(u,v) :=
      (u=a and v=b)
   or (u=b and v=a)
   or (u!=a and u!=b and v=u)

is an admitted relation. It is a bijection and its own inverse, including
when a=b. Since a,b belong to X, it restricts to a permutation of X.
Define the admitted composite graph

  G(x,y) := exists z (R(x,z) and T_ab(z,y)).

On X this is a total single-valued injection, and G(a,a). If x belongs
to X-a, its G-value cannot be a: injectivity together with G(a,a) would
give x=a. Therefore

  G'(x,y) := (X-a)(x) and (X-a)(y) and G(x,y)

is an injective self-relation of X-a. The induction hypothesis makes G'
surjective on X-a. Together with G(a,a), this makes G surjective on X.
As T_ab is a permutation, R is also surjective on X. Thus DedFin(X).

We have V(0) and forall Y(V(Y) -> V(Suc(Y))). The exact impredicative
definition now yields

  FiniteCardinality(N) and N(X) -> DedFin(X).

This is one internal induction, not an argument by external enumeration.
The graph constructions impose no necessity-of-distinctness condition:
their required mapping properties are current, as in FP's definition.

3. Every subfamily of an internally finite propositional carrier has a join
-------------------------------------------------------------------------

For admitted X,F:tt and s:t, define

  J(X,F,s) := forall z:t.
    [s <= z iff forall x:t ((X(x) and F(x)) -> x <= z)].

This says exactly that s is the least upper bound of the current members
of X satisfying F. To see both parts, set z=s for the upper-bound claim;
the displayed equivalence then gives leastness for any other upper bound.

Use the single admitted induction predicate

  W := lambda Z. forall X:tt.
       Z(X) -> forall F:tt. exists s:t. J(X,F,s).

For Z=0, X has no members, so s=bottom satisfies J(X,F,s) for every F.

For the successor step assume W(Y), and suppose Suc(Y)(X). Choose a with
X(a) and Y(X-a). For any F, the induction hypothesis supplies s with
J(X-a,F,s). The current Xs are precisely a together with the X-a members.

If F(a), their F-selected members are the old family plus a. For every z,

  (s or a <= z)
    iff (s <= z and a <= z)
    iff forall x ((X(x) and F(x)) -> x <= z).

Thus s or a is the required join. If not F(a), the selected members are
exactly the old family, so s is the required join. Ordinary classical case
analysis gives the existential witness in either case. No uniform choice
function selecting these joins has been asserted.

Hence W(0) and forall Y(W(Y) -> W(Suc(Y))). The exact Frege definition
proves W(N) whenever FiniteCardinality_t(N).

In particular, if N(U), every admitted property F of propositions has an
algebraic join. Together with C's Boolean-algebra laws, this is precisely
the internal CBA(U,<=) condition required by FP. It does not assert that
every external subset is admitted or that the algebra is externally
complete in a Henkin model.

4. Apply FP to the proposition algebra itself
-------------------------------------------

Suppose, for contradiction, that FiniteCardinality_t(N) and N(U).
Section 2 gives DedFin(U). Section 3 gives CBA(U,<=).

Apply the carrier-t instance of FP to X=U and R=(<=). Its finite disjunct
applies. We obtain p != top and an admitted order-isomorphism graph

  H : U -> [bottom,p].

Regard H as a binary relation on the universal proposition carrier U.
It is total, single-valued and injective on U. But top is not in its
range: any value of H lies below p, whereas top <= p implies p=top.
This contradicts DedFin(U).

Consequently no internal finite cardinality counts all propositions:

  C + Forcing Possibilism |- Axiom of Infinity (type t).

The original conclusion survives unchanged. The proof applies to internal
finite cardinalities even when their denotations are not externally finite
in a Henkin model. It uses neither an external finite list nor an admitted
power-set algebra of cardinality 2^N. No ND, Choice, Actuality, Barcan,
global Boolean Completeness, or full model assumption is added.
No optional premise has been necessitated, and no currently coextensive
properties have been identified. Boolean identities used above are C
theorems; the other constructions are ordinary formula abstractions.


## Original recorded proof

Suppose some finite cardinality holds of the universal property of propositions, say there are exactly $N$ propositions, $q_1,\dots,q_N$ (with $N\ge2$, as $\top\ne\bot$). At type $tt$ the properties $\lambda p\, .\,p=q_{i_1}\lor\dots\lor p=q_{i_k}$, one for each subset of $\{q_1,\dots,q_N\}$, are pairwise distinct, since two of them differ at some $q_i$, and under inclusion they form a complete Boolean algebra with $2^N$ elements: a finite Boolean algebra is complete, and its carrier, order, meets and joins are given by abstraction. It is finite, hence small. Forcing Possibilism gives a proposition $p\ne\top$ whose entailment algebra is isomorphic to it, so there are at least $2^N>N$ propositions, those entailing $p$. Contradiction. Hence no finite cardinality holds of the universal property of propositions.

## Paper references

- **Origin: [Could the truths of mathematics have been different?](https://andrew-bacon.github.io/papers/Could%20mathematics%20have%20been%20different.pdf).** Bacon, Andrew (2025). Could the truths of mathematics have been different? Draft dated 9 October 2025, with online appendix; published in Philosophical Review 135(3), 2026, pp. 221–285, as cited by Barton and Goodsell. Locators refer to the draft. The full Boolean-valued construction is in appendix §B.2, pp. 7–9 of the separately paginated appendix (PDF pp. 41–43); Theorem 4.4 and its proof (Appendix C.1) and Lemma C.6 (Appendix C.2) were read directly on 19 October 2026. — §6, p. 27. Stated there for the axiom of infinity in the form that the finite numerical quantifiers over propositions form a natural number structure; the map's Axiom of Infinity (type t) says that no finite cardinality holds of the universal property of propositions.
