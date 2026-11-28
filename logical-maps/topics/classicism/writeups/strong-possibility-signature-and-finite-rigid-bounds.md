# Signature Strong Possibility, strong atoms and finite rigid bounds

Fix any set-sized signature $\Sigma$ admitted by the map. At a point of signature Strong Possibility no proposition is a strong atom, every rigid relation has internally finite current extension, and Rigid Power holds. The sentence asserting the absence of strong propositional atoms is itself two-hat necessary there and fails to be ND-necessary. All consistency tests below use Maximalism in this same signature.

## An atomless signature-Maximalist point

Take a set-sized pointed signature Possibility+ model $K,v$, for instance the [signature-definable coalesced root](coalesced-definable-root-signature.html). Write $G$ for the Cantor group $2^\omega$ under addition, and $X$ for a second copy of its underlying space. Give the new root $o$ the individuals of $v$ and group $G$ of loops, fixing these individuals. For each $x\in X$ add a copy of the old component with an entrance to its designated point $v$. Each entrance absorbs all root loops and is the identity on the common individual domain; include all its old postcomposites. Fixing an identification with $K$ for each copy lets us compare its values with the values of the other copies.

At a relational type $\tau=\bar\sigma t$ a root profile consists of two independent functions. The first is a locally constant map $G\to\mathcal P(D_{\bar\sigma}(o))$ to the discrete set of current rows. The second is a locally constant map $X\to D_\tau(v)$ to the discrete set of **whole** old entities. Loops right-translate the first function and fix the second. Entrances evaluate the second function at their index. Give each relational name arbitrary constant loop rows and the constant section of its prescribed old value. The individual names have their old interpretations.

By compactness, a locally constant loop table has a common finite prefix length that determines its whole row. Translating by an element of the corresponding open subgroup leaves its entire profile fixed. Thus the transported list of parameters for an abstract is constant on a finite clopen partition of the loops. Evaluating the abstract on all current target tuples gives a locally constant row table. At an entrance use old abstraction on the finite list of transported parameter values. The list is locally constant in $x$, giving a locally constant section of whole old values, including for formulas quantifying over all old arguments. Application and equality respect transport; any profile difference is witnessed on a loop row or in an old component. These are the action-model clauses. Each eligible tuple of individuals for signature Possibility+ is still eligible at an old entrance. All its old witnesses remain accessible, so the root satisfies signature Possibility+ and signature Maximalism.

At scalar type the order is coordinatewise inclusion on
$$
 \operatorname{Clop}(G)\ \times\ \operatorname{LC}(X,D_t(v)),
$$
where the second factor is ordered by pointwise old entailment. Each nonzero element has two disjoint nonzero parts. In the first coordinate split a nonempty clopen patch on which it is true. In the second, a section with nonzero value on a clopen patch can be restricted to either half of a clopen splitting of that patch, with bottom elsewhere. Nonzero old values are witnessed after old postcomposition. The same split works for relations, retaining the entire row or old value on the chosen half. In particular no strong atom exists at the scalar type. All current relations on tuples are available as constant loop tables, so the root admits ordinary well-orders. Actuality fails by the same clopen splitting around the identity. The cylinders whose first one is at position $2n$ have no supremum in the loop algebra: any clopen upper bound contains the all-zero sequence and hence contains some entire odd-position cylinder, which can be removed. They are a current family countably indexed by standard Frege numerals. Restricting to the loop coordinate gives failures of propositional Boolean Completeness and local Countable Boolean Completeness. [Cantor loop calculation](stone-terminal-cantor.html)

## Reflection through ND possibility

Let $D(w)=\forall p\,(w\le p\lor w\le\neg p)$, and let
$$
 U=\forall w\,(w=\bot\lor D(w)\ne\top).
$$
This says that no proposition is a strong atom. The comparison with $\top$ tests the necessary universal decision property of the atom. In particular $U$ is a universal Boolean combination of identities *between terms*. For any sentence of this form C proves $\Diamond_{\ne} U\to U$. If a tuple violates its matrix, take as guard the conjunction of the failures of the identities which are false. Identities that are true persist by necessity of identity, and at any point where this guard is still possible none of the failed identities can have become true. This keeps the same tuple a counterexample wherever the guard is possible. The argument is uniform in the signature. [Universal reflection for strong atoms](../index.html#result/strong-possibility-and-strong-actuality-incompatible)

The Cantor construction witnesses consistency of $U$ with signature Maximalism. Thus signature Strong Possibility gives $\Diamond_{\ne}U$, and reflection gives $U$. In particular Strong Actuality is impossible. On the other hand, signature Maximalism plus Strong Actuality holds in the [identity-loop descriptor model](coalesced-finite-support-rigid-root.html), whose root-only scalar is a true strong atom. Signature Strong Possibility therefore also gives $\Diamond_{\ne}\neg U$. Necessitating the reflection theorem gives $\Box(\Diamond_{\ne} U\to U)$. Together with the truth of $U$, this is the two-hat guard for $U$ itself. Hence $\hat{\hat\Box}U$ holds and $\Box_{\ne}U$ fails. [Modal operators](../index.html#background/varieties)

## The finite-bound return

For any finite tuple type let $\mathrm{Fin}(F)$ mean that the current property of tuple-haecceity codes of $F$ is counted by some Frege finite cardinal. In the identity-loop descriptor model every proper transport of a currently rigid $F$ is a finite union of tuple haecceities, including after all old postcomposites. At the root itself Strong Actuality holds. Thus for each arity the closed pure sentence
$$
 \Psi=\forall F\big(\operatorname{Rigid}(F)\to
       \Box(\neg\mathrm{StrongActuality}\to\mathrm{Fin}(F))\big)
$$
is consistent with signature Maximalism. Take any current rigid $F$ at a signature Strong Possibility point. If $F$ is not internally finite, the true parameterized guard $\neg\mathrm{StrongActuality}\land\neg\mathrm{Fin}(F)$ requests a return after reaching $\Psi$, using $\Diamond_{\ne}\Psi$. Rigidity persists through the intermediate point. Its boxed conditional gives $\mathrm{Fin}(F)$ at the return, contradicting that guard.

The [internally finite rigid-power theorem](../index.html#background/rigidity) now makes the canonical power rigid at every type, including mixed tuples and nonstandard finite bounds. With Tame Rigidity every weakly rigid relation is rigid already; the same finite theorem gives its weak power as well. [Pure finite-bound proof and arity details](strong-possibility-implies-rigid-power.html)
