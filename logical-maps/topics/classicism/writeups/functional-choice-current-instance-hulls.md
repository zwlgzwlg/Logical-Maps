# Functional Choice and current-instance hulls

GPT-6 Astra, prompted by Daniel Kodsi. 30 October 2026.

These reductions isolate the remaining content of Functional Choice implying
Boolean Completeness. They do not prove that implication. Over a current bivalent
evaluator, all-type Boolean Completeness is equivalent to the existence, at each
relational type, of a least relation necessarily containing every actual tuple.
The higher-type shift is essential: a hull at the family type tau-t supplies
Boolean Completeness at tau. A hull at tau alone does not do so.

All unboxed quantifiers below are current. Equality of proposition values is
identity of whole propositions; Boolean order is necessary implication. The
hull and ideal predicates are auxiliary definitions in the proof, not new
principle nodes. The statements retain each additional premise explicitly.

## 1. Bare-C evaluation, zero kernels, and the universal hull

Fix a relational type tau=sigma_1...sigma_n t, with n possibly zero. Define the admitted predicate

    K_tau(R) := forall current xbar. R[xbar]=bottom_t.

It is an ideal in the whole Boolean algebra at tau. Evaluation at any fixed current tuple a has the bare-C right adjoint

    A_a(p) := lambda zbar. (zbar=a -> p),
    R[a] <= p  iff  R <= A_a(p).

The forward direction necessitates the unconditional equality-substitution theorem, then applies K to the supplied boxed antecedent. It does not box a current universal statement or invoke BF. The conditional zbar=a handles arbitrary new future tuples. The reverse direction is necessary evaluation at a. Therefore an existing represented join preserves each fixed evaluation; in particular a join of K-members remains in K.

Let H_a=lambda zbar.(zbar=a). The adjunction gives

    R belongs to K_tau iff R is disjoint from every ACTUAL H_a.

The family of all these haecceities is admitted as lambda S.exists a.S=H_a. Thus the following are equivalent in bare C:

1. K_tau has a greatest member k.
2. The admitted family of all current tuple-haecceities has a join H.
3. There is a least relation H with H[a]=top_t for every current tuple a.
4. Top_tau has a weakly rigid current coextension.

The complements are H=not k. For example, a test Z necessary of every current tuple has not Z in K, hence H<=Z; H's current values are top, giving weak persistence. Conversely the weak persistence of a universal coextension gives its top-valued actual evaluations, and weak inextensibility makes its complement bound every K-member. These proofs do not presuppose any arbitrary joins.

The universal-property interpretation appears in *Rigidity, actualization and evaluation*, section 9, which identifies weak rigidity with being the join of the haecceities of one's actual instances. The present hull is its universal-instance specialization.

## 2. BE masks arbitrary instances; the family-type shift is real

Let BE(E) mean that for each current proposition p, E(p) is literally top when p is true and literally bottom when p is false. Plenitude at (t,t) supplies E by representing the admitted functional graph

    (p and q=top) or (not p and q=bottom).

Only current Plenitude is used. E need not be correct on arbitrary new future propositions or preserve whole quantifier operations.

Given k=max K_tau and any X^tau, set

    A_X=lambda xbar.E(X[xbar]),
    H_X=A_X and not k.

At current tuples, H_X has the endpoint values of E and is coextensive with X, so it is weakly persistent. Suppose Z necessarily holds of each actual H_X-instance. For each current tuple, either X is false and A_X has value bottom, or X is true and Z has value top. Thus A_X and not Z belongs to K and lies below k. Intersecting with not k gives H_X<=Z. This proves weak inextensibility against every admitted Z, without BF or Functionality.

Consequently, at a fixed tau, BE + Hull_tau is equivalent to WRC_tau; the converse does not need BE. Native WRC-to-BC applies a weakly rigid representative to an admitted FAMILY X^(tau t). Its existential union yields the join at tau. Thus it needs Hull_(tau t), exactly as the note says.

As all-type schemata over BE:

    Hull_all iff WRC_all iff BC_all.

Forward BC implies every hull by applying BC_tau to the admitted haecceity family. Reverse uses the shifted instance above. The argument does not assume BC_t in advance. Full FC provides BE through Plenitude, but the existence of the hulls is still the unsolved step.

## 3. The same-type kernel-completeness reduction

Let KComp_tau mean that every admitted current subfamily of K_tau has a least upper bound WITHIN K_tau. This relative formulation is sufficient. Applying it to K itself supplies its greatest member k: instantiate the defining upper-bound biconditional at b=k.

Over Plenitude + BC_t, each admitted family X^tau has an admitted scalar assembly J whose value at every current tuple is the scalar join of {R[xbar]:X(R)}. Both upper-bound and leastness errors lie in K:

    X(R) => R and not J belongs to K;
    UB_X(Y) => J and not Y belongs to K.

Take the represented relative K-join a of {R and k:X(R)} and put

    L=(J and not k) or a.

Finite Boolean algebra gives every X-member <=L, and L<=every ambient upper bound. No inference from current pointwise inequality directly to whole relation order occurs; the K error is explicitly removed. Thus

    C + Plenitude + BC_t proves: BC_tau iff KComp_tau.

The equivalence leaves open whether Functional Choice supplies KComp.

## 4. The represented well-ordered-chain reduction

Use the recorded preorder form of Zorn. Full FC yields it through Plenitude -> Actuality -> Transversal, plus FC -> Relational Choice, followed by Transversal Choice -> Zorn. The Transversal premise is supplied by Actuality.

For predicate codes C^tau t, let Pos(C) say that C is contained in K and internally well ordered by the Boolean order. Order valid codes by current initial-segment inclusion. Distinct coextensive predicates need not be identical, so this is correctly a preorder. The extension

    P(C,D) := not Pos(C) or (Pos(D) and I(C,D))

puts all invalid codes in a bottom equivalence class and is a preorder on the whole sort. There is no hidden quotient selection.

For an admitted comparable family A of codes, the existential union of its valid members is admitted, belongs to K, and is internally well ordered. To check least elements, choose one member C0 meeting an arbitrary nonempty admitted test set, take its least meeting point, and compare C0 by initial segments with any other witness chain. This proves global leastness without an external ordinal or simultaneous choice. Every valid family member is an initial segment of the union; invalid members lie below it automatically. This supplies more than the antisymmetric-chain hypothesis required by native Zorn.

If K has no greatest member, a maximal such chain cannot have a K-upper bound b: choose s in K with s not<=b, append d=b or s, and obtain a strictly larger admitted well-ordered initial extension. Nor can the chain have an ambient Boolean join j, since the evaluation adjoint puts j in K.

Hence full FC + not Hull_tau yields an admitted internally well-ordered K_tau-chain with no K-bound and no ambient join. In fact the argument only needs the appropriate Zorn instance at tau t, together with bare C's ideal facts. Under that instance:

    Hull_tau iff every admitted internally well-ordered K_tau-chain
                has an upper bound IN K_tau.

An ambient join for every such chain is sufficient, but has NOT been derived from FC or BC_t. An arbitrary ambient upper bound is insufficient: top_tau always supplies one and need not belong to K. Evaluating the chain at any actual tuple produces only zeros, so scalar BC sees no obstruction and cannot reconstruct the missing bound by itself.

## Sources

- GPT-6 Astra, prompted by Daniel Kodsi, *Scalar to full Boolean Completeness*,
  *Canonical hull and Functional Choice*, and *Scalar kernel critical analysis*,
  30 October 2026 (unpaginated), sections on zero-evaluation ideals, the family-type
  shift and represented well-ordered chains.
- GPT-6 (OpenAI), *Rigidity, actualization and evaluation: research notes*,
  22 October 2026, section 9 (unpaginated): the haecceity hull interpretation;
  the evaluation-adjoint argument supplies the fixed-tuple adjunction used above.
- The native Plenitude, Weak Rigid Comprehension, Relational Choice,
  Transversal and preorder Zorn definitions, and their recorded connecting proofs.
