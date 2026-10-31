# Analytic Necessitism: carrier-sensitive corrections

By GPT-6 Astra, prompted by Daniel Kodsi, 29 October 2026.

The proofs use ZFC, the stated type schemata and full action semantics where
required. They concern Analytic Necessitism and Second-Order Analytic
Necessitism in the existing model constructions.

## 1. Statement and scope of the correction

At each carrier type sigma, AN says that if a real field is possible at sigma,
there is a rigid necessarily-real field at **that same sigma**. SOAN adds
represented powers there. Producing a real field at tt does not answer an e or t
instance. Identity remains identity of whole entities, rather than current
coextension. A failed shared sufficient-condition proof does not make every
formerly supported model a countermodel.

The following six shared arguments are refuted by countermodel C below:
`analytic-necessitism-codomain-fixed`, `analytic-necessitism-codomain-fixed-individuals`,
`analytic-necessitism-codomain-fixed-infinite-individuals`,
`analytic-necessitism-codomain-everywhere`, `analytic-necessitism-full-continuum`,
and `second-order-analytic-necessitism-full-continuum-codomain`.
Countermodel S refutes `analytic-necessitism-collapse-orbits` and
`second-order-analytic-necessitism-full-continuum` as their conditions are stated.
The local `analytic-necessitism-codomain-chain` is refuted by section 3.
Original texts are retained as withdrawn arguments; their selected-carrier lemmas
and the earlier withdrawn tt counterargument are not reinstated or rewritten.

## 2. Counterexamples to the shared arguments

### Full action semantics

Start with a small category and a nonempty covariant individual-set functor. At a relational type `sigma_1 ... sigma_k t`, an entity at v assigns to each arrow h out of v an arbitrary subset of the product of the `sigma_i` domains at the codomain of h. For k=0 this is a subset of the arrows out of v. Transport along g takes the row at h to the old row at `h composed with g`. This recursion is over type complexity. Composition of transports follows from associativity. Taking every such intension makes the domains closed under the semantic interpretations of terms, including abstraction and quantification; there is no injectivity or faithfulness condition on the individual functor. This is the full action-model construction used by the cited local sources.

In particular every actual relation on any domain has an intension realizing it: prescribe its identity row and choose arbitrary rows elsewhere. Actual identity is genuine identity of domain elements, not mere actual coextension. One way to see separation is that fullness supplies a property with any prescribed singleton identity extension. The same observation applies at every target object. Consequently two distinct propositions can have the same truth value while remaining distinct entities; a transport can subsequently make them identical as entire intensions.

We work in ZFC. This suffices to refute a claimed choice-free sufficient condition: a countermodel in a setting with choice is already a countermodel. No claim about constructing these cardinalities in arbitrary choice-free metatheories is needed.


### C. The absorbing-zero model


Let `M = N disjoint-union {z}`. On N composition is addition, with unit the natural number 0; let z be absorbing on both sides. These laws define an associative countably infinite monoid. Regard it as a one-object category. Put `D_e=N` and let **every** arrow act as the identity on individuals. This is a valid, nonfaithful individual action. Use full relational domains.

Then `D_t=P(M)` has continuum cardinality. Fullness makes all finite-arity actual relations on it available, so an ordinary real field can be installed on this domain at the identity. Thus the antecedent of AN_t holds.

For every proposition p, transport by z is

`z.p = {u in M : u composed with z is in p}`.

Since `u composed with z = z` for every u, this is M if z belongs to p, and the empty set otherwise. The image of transport by z on propositions consequently has exactly two elements. Therefore any set of propositions whose distinct members remain distinct along every arrow has cardinality at most two: restriction of transport by z to that set must be injective.

If an AN_t consequent held, its actual carrier would be an ordered field by the identity case of `necessarily Real_t`. Any ordered field has at least three distinct elements (0,1,1+1 are distinct because an ordered field has characteristic zero). Its `RigidStr` clause would require injective transport of this carrier along z. An injection of three distinct propositions into `{empty set,M}` is impossible. This contradicts the consequent.

Thus C fails AN_t and SOAN_t. Notice that the whole target type is still of continuum size: the obstruction is collapse of assigned carrier elements, not a small target domain. Newly quantified target propositions do not repair the necessary distinctness of the assigned elements. The target-quantifier issue emphasized in the idempotent-monoid source therefore causes no gap here.

The model satisfies all of the following literal conditions:

| Condition | Reason |
| --- | --- |
| `one-object-action-model` | The category is the one-object monoid M. |
| `codomain-intensions` | Every intension is admitted. |
| `infinitely-many-propositions` | `P(M)` has continuum cardinality. |
| `infinitely-many-propositions-everywhere` | There is only one object, with this same domain. |
| `infinitely-many-individuals` | Individuals are N. |
| `fixed-infinite-individuals` | Every arrow acts identically on N. |
| `full-continuum-everywhere` | At the only object use `D=P(M)` at type t; all finite-arity relations are available by fullness. |

It follows that C is a common countermodel to the **all-type conclusions** of these six argument records:

1. `analytic-necessitism-codomain-fixed` (AN and SOAN);
2. `analytic-necessitism-codomain-fixed-individuals` (AN and SOAN);
3. `analytic-necessitism-codomain-fixed-infinite-individuals` (AN and SOAN);
4. `analytic-necessitism-codomain-everywhere` (AN and SOAN);
5. `analytic-necessitism-full-continuum` (AN);
6. `second-order-analytic-necessitism-full-continuum-codomain` (SOAN).

The fixed-individual condition controls only type e. It does not make the proposition transport injective. Conversely, the canonical constant-intension real structures at types et or tt are compatible with this countermodel: the collapse of proposition arguments does not collapse all higher-type intensions. The positive arguments can therefore contain useful existence lemmas despite their false schema-level conclusions.


### S. Trivial symmetry and finite pinning


The following additional countermodel addresses the two remaining positive records, `analytic-necessitism-collapse-orbits` and `second-order-analytic-necessitism-full-continuum`.

Take one object, the monoid of all functions `R->R`, and its natural action on individuals R. At each relational type admit exactly those arrow-indexed profiles F whose row `F_h` depends only on the restriction of h to some finite set N of individuals. Use the trivial symmetry group `G={identity}`. Profiles are defined recursively using the admitted argument domains, rather than by first constructing full higher-type domains and restricting only their outermost row indices.

### Transport and closure obligations

If F is pinned by N, its transport along h is pinned by h[N]: if k and k' agree on h[N], their composites kh and k'h agree on N, so `F_(kh)=F_(k'h)`. Hence precomposition transports every admitted profile to an admitted profile.

Moreover, if h and h' agree on N, then the **entire transported profiles** h.F and h'.F are identical: for every k, kh and kh' agree on N. Individuals have the same finite determination property, since the image of a is determined by the value of an arrow on the singleton {a}. Every admitted parameter thus has a finite set on which arrow agreement determines its complete transported value.

For a term or formula with finitely many assigned free parameters, take the union N of these finite determining sets. At two arrows h,h' agreeing on N the parameters have identical transported values, and both arrows have the same target object. For an abstraction, evaluate the body at that target under any chosen tuple of bound arguments. Its value is the same in both cases because its target assignments are the same. Consequently the rows of the abstraction agree. This argument applies also when the body contains quantifiers or modality: the target domains and outgoing category are the same, and modal continuation transports start from identical parameters. Equivalently, the standard induction proving the substitution/transport lemma for action semantics gives precisely this equality of rows. The abstraction is therefore pinned by N and admitted. Application and the logical operations likewise preserve finite determination. With signature constants taken to be relational top elements, closure under the entire term language follows.

This supplies the relevant admissibility argument; it does not merely assume that an arbitrary restriction of full domains is a model. The semantic proof that H-equivalent abstractions have the same intension is unchanged. It is also the general finite-ideal construction described in `groups/finite-support-one-object.yaml`, whose proof of extensional fullness uses empty-pinned constant profiles and does not depend on the pinning base being countable.

### Literal condition checks

`symmetric-domains` in `conditions.yaml` says that a group G acts on the individuals and that every admitted profile is symmetric under G and finitely pinned. It does not require G to be nontrivial, transitive, or the entire permutation group. For the trivial group its symmetry implication is tautological. Thus S satisfies this condition literally; no extra symmetry requirement may be inferred from the title of a particular existing model group.

By construction S also satisfies `finitely-pinned-domains`, including both finite determination of transported entities and admission of every finitely pinned profile. It is a one-object action model.

For each finite set N with n>=2 elements, choose a in N and define j to send every member of N to a and fix every point outside N. This j is an arrow, is constant on N, is injective off N, and its off-N values differ from a. Thus `exact-collapses-of-every-size` holds, without any additional construction of injections.

Every ordinary set of k-tuples of individuals is the row of a constant profile, pinned by the empty set, and hence admitted. With D=R at type e this proves `full-continuum-everywhere` at the only object. In fact the same constant-profile argument proves full actual extensions at every admitted relational type. It also separates actual domain elements, so the equality used below is genuine equality.

### Failure of the all-type conclusions

The ordinary real carrier, order, operation graphs and natural-number predicate are admitted as constant profiles at the corresponding relational types. Together with the ordinary 0 and 1 they give an actual `Real_e` structure. Full actual extensions ensure that the completeness and least-inductive-subproperty clauses have their intended ordinary meanings.

An AN_e witness would have an actual ordered-field carrier with at least two distinct individuals, and `RigidStr` would make those individuals necessarily distinct. A constant self-map of R collapses them. Therefore AN_e fails, and SOAN fails as well.

S consequently refutes the current all-type conclusions of both `analytic-necessitism-collapse-orbits` and `second-order-analytic-necessitism-full-continuum`. Combined with C this gives explicit countermodels covering all eight positive records under discussion. This does not restore the withdrawn type-tt proof in `analytic-necessitism-exact-collapses-symmetric`: S fails at e, and its fixed type-tt structures remain entirely compatible with that failure.

## 3. The existing free-loop entrance fails AN at t


`models/full-two-object-chain-free-loop.yaml`, `settings.construction`, specifies objects W_0,W_1, the unique arrow h:W_0->W_1, freely iterated loops s^n at W_1, and s^n h=h. The only arrows out of W_0 are its identity and h. Its `meets.finitely-many-propositions` explicitly records four propositions at W_0. The file's first local argument, for `possible-infinity-t`, explicitly uses the infinitely many outgoing loops at W_1 and its full proposition domain.

Consequently `D_t(W_0)=P({id,h})` has four elements, while `D_t(W_1)=P({s^n:n>=0})` has continuum cardinality. By fullness there is an actual real structure of type t at W_1, so `possibly exists Real_t` holds at W_0. But no actual ordered field can have its carrier in the four-element root domain. Any AN_t consequent would imply an actual Real_t structure by the identity case of its necessity clause. Therefore AN_t fails at W_0, as does SOAN_t. This proof does not use inextensibility at all.

The proposition domains depend only on the category, so this failure persists with the group's fixed infinite individuals and either signature setting. It is a concrete failure in an existing source model, not merely a counterexample to an overly broad general rule.


This new negative argument is stated only for the group's ZFC settings, with
singleton or fixed-infinite individuals and either generated signature. The
argument does not reopen the old tt proof. Failure of SOAN follows from the
existing SOAN-to-AN result, so only failure of AN is recorded explicitly.

## 4. The full-action carrier criterion and represented powers


Work in ZFC. Let a full action model have evaluation object v, and fix a carrier type sigma. Fullness is required at every object reachable from v. Write D_sigma(w) for the entities of type sigma at w and c for the external continuum cardinal.

The following are equivalent:

1. AN_sigma holds at v.
2. For every finite n >= 1, SOAN_sigma,n holds at v.
3. Either no reachable object w has a subset of D_sigma(w) of cardinality c, or there is a set S contained in D_sigma(v), of cardinality c, such that every arrow h with source v is injective on S.

In fact each individual SOAN_sigma,n is equivalent to (1) and (3). Thus AN and SOAN, including their full type schemata, have identical truth values in full action models. This is a semantic theorem about full action models, not a derivation of AN -> SOAN in C, and not a claim about arbitrary Henkin or finitely supported models.

For a one-object full action model, (3) reduces to: either |D_sigma| < c, or D_sigma has a continuum-sized subset on which every monoid action map is injective. Injectivity is required separately for every arrow on the same set S; no uniform injectivity on the rest of D_sigma is required.

## Semantic conventions

An entity of relational type is an intension. Its extension at an arrow h:v->w is a set of tuples from the appropriate domains at w. If E is a set of tuples at v, hE denotes its componentwise direct image under the action. Transport of a relation Y along h has extension at j:w->u equal to Y(jh). Identity at a target object is literal equality of domain elements; full relational domains in particular separate different entities.

These are the intension conventions of `conditions.yaml` (`finitely-pinned-domains` for notation), `groups/full-action-models.yaml`, and the direct-image argument in `groups/finite-support-one-object.yaml` under `tame-rigidity`. AN, SOAN, Real, RigidStr, and RepPower are read exactly as in their principle records and `background/arithmetic.md`, lines 69-108. Both conjuncts of rigidity include their leading boxes, as explained in `background/rigidity.md`.

## Direct-image lemma

Given any set E of tuples at v, define Y_E(h)=hE. Fullness admits Y_E. It is rigid, including at all subsequent objects.

For persistence, if a tuple is in Y_E(h)=hE, its j-image is in jhE=Y_E(jh). For inextensibility at h, suppose a relation Z at w necessarily holds of every member of hE. Then at every j:w->u, Z(j) contains every tuple ja with a in hE, hence contains j(hE)=Y_E(jh). This is exactly the inclusion required by weak inextensibility at h. Since h was arbitrary, the boxed inextensibility condition holds. The argument also shows that h·Y_E is the direct-image relation at w generated by hE.

This proof uses images of members in the correct direction. It does not infer that an entity whose image enters hE was already in E; that inverse-image inference was the gap in the withdrawn AN arguments.

## Proof of the theorem

First, at any reachable w, a Real_sigma structure exists iff D_sigma(w) contains a subset of cardinality c. In one direction, full domains represent every subset of its carrier, so the Real axioms assert actual external Dedekind completeness. A complete ordered field is isomorphic to the external real field and has cardinality c. In the other direction, carry the real field to a c-sized subset of D_sigma(w). Fullness admits carrier, order, addition, multiplication, and natural-number intensions with precisely the prescribed current extensions. All subset quantification then has the standard truth value, so the resulting tuple satisfies Real_sigma at w.

Consequently the antecedent of AN_sigma is false exactly in the first alternative of (3). This also makes every SOAN_sigma,n vacuously true.

Suppose the antecedent is true and AN_sigma holds. Its witness is an actual real field because the frame is reflexive. Let S be its actual carrier. The preceding paragraph gives |S|=c. The necessary-distinctness clause of RigidStr states that every two distinct members of S remain different under every arrow h from v. Thus each h is injective on S. This proves (1) -> (3).

Conversely, suppose the second alternative of (3), and choose a bijection from the external reals to S. At the identity, put the usual real field structure and natural numbers on S. For each carrier or field relation E, use Y_E(h)=hE. Transport 0 and 1 as the corresponding two selected entities. All relational components are rigid by the direct-image lemma. For each h, the restriction h|S is a bijection from S to hS, so the transported structure on hS is isomorphic to the external real field. Full domains at the target allow all subsets of hS, but no such subset defeats completeness or the characterization of the natural numbers. Thus Box Real_sigma holds. Every h is injective on S, so the carrier is necessarily distinct. This proves AN_sigma's consequent.

For each k >= 1 and every T contained in S^k, let Q_T=Y_T. Let F_k be the set of all Q_T, and define P_k(h)=hF_k={h·Q_T:T contained in S^k}. Fullness admits both Q_T and P_k. The lemma makes every Q_T rigid and makes P_k rigid. At v each Q_T relates only tuples in S; after h it relates only tuples in hS.

To check representation at h:v->w, take any k-ary relation R at w and let U be its current extension restricted to (hS)^k. Define T to be the inverse image of U under the componentwise bijection h|S. Then hT=U. The relation h·Q_T belongs to P_k(h), and its current extension is exactly U, so it agrees with R on hS. This proves the required boxed representation clause. The construction works simultaneously for all finite arities, and in particular for any prescribed finite n. Thus (3) -> (2). Finally SOAN_sigma,n includes the same rigid necessarily-real structure as AN_sigma, proving (2) -> (1) and the individual-n strengthening.

## Consequences and boundaries

* A common separating continuum, not a continuum of fixed entities at some unrelated type, is the correct criterion. Fixed points provide a sufficient special case, but moving carriers are permitted.
* If an outgoing h has image of cardinality less than c on D_sigma(v), and a real structure is possible at sigma, AN_sigma and SOAN_sigma,n fail. This includes constant collapse of individuals and absorbing-arrow collapse of propositions to two values.
* The obstruction applies even when codomain-only intensions create arbitrarily rich fixed structures at higher types. It rules out a general downward type-transfer theorem under those hypotheses.
* In an invertible action category, every arrow is injective on every type. If any reachable object has a c-sized carrier, transporting it backwards gives one at v. Hence the criterion gives all instances in a full groupoid action model.
* ZFC is stated explicitly. The witness-form sufficiency proof is choice-free once S and its real-field labeling are supplied. A separate ZF formulation should use explicit injections and externally full real carriers instead of silently comparing arbitrary cardinals.


## 5. Exact full-action restorations


The classification is:

> Let M be a nonempty countable monoid, acting arbitrarily on a nonempty countable individual domain. Take the full one-object action model. Then the all-type AN schema and the all-type SOAN schema are equivalent, and hold exactly when M is finite or every principal left ideal Mh is infinite.

Here countable includes finite. The same statement remains correct with an arbitrary nonempty individual set if every arrow acts on individuals as the identity. This extension uses ZFC and must not be automatically applied to the map's `socks` or other choiceless variants.

For the extension, the only change is the individual carrier: it is either too small for a real structure, or has a continuum-sized subset fixed pointwise by every arrow. Higher types are treated exactly as below.

## Type-by-type proof

In a full action model a carrier admits an actual real structure precisely when it has cardinality at least the continuum c. Full actual extensions make internal Dedekind completeness ordinary Dedekind completeness. If a real structure is rigid in the recorded sense, its carrier's distinct elements must stay distinct under every arrow. Conversely a c-sized set with this separation property can carry a real structure by assigning at each arrow the direct images of the chosen carrier and its field relations. Fullness admits these profiles and the corresponding represented-power profiles. This is the same-carrier criterion proved in section 4. The local `groups/full-action-models.yaml`, `meets.rigid-haecceity-disjunctions`, explicitly records the direct-image characterization of rigidity supporting the sufficiency step.

### Infinite countable M

At type t the domain is P(M). Transport by h is inverse image under `u -> uh`; two propositions have the same transport exactly when their restrictions to Mh coincide. Therefore a finite Mh makes the transport image finite. Since P(M) has size c, an actual real structure exists, but no c-sized set can remain separated under h. AN_t and SOAN_t fail.

If every Mh is infinite, enumerate M x N in order type omega. At stage i choose the point assigned to its pair (h,n) from Mh outside the finitely many earlier choices. The exclusions really are finite, not merely countable: this is the point that makes the diagonal construction work even when distinct left ideals overlap heavily or coincide. One can use a fixed enumeration of M to choose the first available point.

Write these globally distinct points as x(h,n), and put B_n = {x(h,n): h in M}. The B_n are pairwise disjoint and every B_n meets every Mh. For A subset N set p_A to the union of B_n for n in A. If A and A' differ at n, then x(h,n) distinguishes p_A and p_A' on Mh for every h. Hence the p_A form a c-sized family whose members remain distinct under every transport. The same-carrier criterion gives AN_t and SOAN_t.

The higher-type lift is valid. Write any relational carrier type as `tau = sigma_1 ... sigma_k t`, including k=0 for t. For p_A define F_A to have the entire tuple domain as its row at u when u belongs to p_A, and the empty row otherwise. Every argument domain is nonempty, so the tuple domain is nonempty, including the singleton empty-tuple product when k=0. Fullness admits F_A. The profile h.F_A has the same truth coding as h.p_A. Since distinct h.p_A differ at some u, the corresponding h.F_A differ at that u between a nonempty universal row and the empty row. Thus the family remains c-sized and separated at **every relational carrier type**, rather than only at a convenient higher type.

The individual carrier is vacuous in the stated countable-domain theorem: it cannot carry R anywhere in a one-object model. In the fixed-individual extension it is handled as stated above. This completes the positive all-type argument for infinite countable M.

### Finite M

For a relational carrier type tau, let T be the product of its argument domains at the sole object. Its full domain is exactly the set of arbitrary M-indexed rows in P(T). If T is finite, the whole domain has size `2^(|M| |T|)`, hence is finite, and AN_tau is vacuous. If T is infinite, choose distinct t_n in T. For A subset N let F_A be the constant profile with value {t_n: n in A}. These profiles are pairwise distinct and fixed as entire entities by every arrow, since precomposition of a constant row function is unchanged.

It does not matter that an arrow can move the tuple arguments: transport of the relational entity is row precomposition, not direct-image transport of its constant row. Confusing these two operations would obscure the proof. The represented real structure is subsequently built on the fixed **entities** F_A, where direct images supply rigidity. There are continuum many such fixed entities, so the same-carrier criterion applies at tau.

No cardinality gap is left: ZFC supplies a countable subset of any infinite T. No uniform finite bound on the sizes of all finite-type domains is required. Every finite type is considered separately. In particular, when M and the individual domain are both finite, induction makes every type finite and the entire schema holds vacuously.

## Recovery of the existing full-action-models group

The eleven constructions below use singleton or fixed infinite individuals. The claims concern their ZFC settings, for either signature interpretation. AN/SOAN are pure, so adding the group's signature constants does not alter these arguments.

The countable-monoid classification directly settles three records. The same-carrier criterion plus the short extensions proved below settles the other eight. Overall, ten constructions satisfy both schemata and the free-loop entrance fails both.

| Source model record | AN and SOAN in the indicated ZFC settings | Reason |
| --- | --- | --- |
| `full-idempotent-monoid.yaml` | Hold | Finite two-element monoid. |
| `full-involution-group.yaml` | Hold | Finite two-element group. |
| `full-monoid-ac-equals-bc.yaml` | Hold | Countable word monoid; every Mh is infinite. |
| `full-infinite-s5.yaml` | Hold | Every arrow is invertible, so every type transport is bijective. |
| `full-permutation-group-infinite-set.yaml` | Hold | A group; every type transport is bijective. Countability of this group is not asserted. |
| `full-surjection-monoid.yaml` | Hold | Explicit separated proposition family given below; higher-type lift applies. |
| `full-three-object-fork.yaml` | Hold | Finite-category, fixed-individual argument below. |
| `full-two-object-chain.yaml` | Hold | Finite-category, fixed-individual argument below. |
| `full-two-object-double-retraction.yaml` | Hold | Finite category with the listed normal forms; fixed-individual argument. |
| `full-two-object-retract.yaml` | Hold | Finitely many outgoing arrows at both objects; fixed-individual argument. |
| `full-two-object-chain-free-loop.yaml` | Fail at type t | Only four propositions at the root, continuum many at an accessible object. |

For `full-monoid-ac-equals-bc`, the source gives normal forms with no factor ac and the length-preserving relation ac=bc. For any fixed h, the elements a^n h have different lengths as n varies. Thus Mh is infinite. This is enough; cancellativity is not required.

For either group/groupoid record, invertibility supplies a bijection on every type. All reachable domains at a given type have the same cardinality. If a real structure is possible, a root c-sized carrier is available and is separated by every arrow. The one-object permutation model may have uncountably many arrows, so this is an application of the carrier criterion, not of the countable theorem.

### Surjection monoid

Let X be its infinite base set. Fix x_0 in X and distinct b_n in X. For A subset N write E_A={b_n:n in A} and define the proposition p_A = {f in M:f(x_0) in E_A}. Given h in M and A,A' differing at n, choose a permutation u of X with u(h(x_0))=b_n. Such a permutation exists (a transposition suffices), and is an arrow of the surjection monoid. Then uh belongs to exactly one of p_A,p_A'. Therefore h.p_A differs from h.p_A', for every h. This is a universally separated continuum of propositions, irrespective of the cardinality of M. The universal/empty-row lift above supplies one at every relational type. The fixed individual domain satisfies its instance separately.

This argument applies to the group's fixed/singleton individual settings. It does not assert the same all-type result for an uncountable **natural** individual action of the surjections: that different setting needs a separate AN_e analysis. The source record explicitly changed its individual settings to those of the group.

### Finite-category extension with fixed individuals

More generally suppose the category has finitely many arrows out of every object and individuals form the same fixed nonempty set D throughout. If D is finite, every finite-type domain is finite everywhere, by induction. Thus all AN/SOAN antecedents are false.

If D is infinite, prove inductively the following dichotomy for every type: either its domain is finite at every object, or there is a coherent sequence a_n(v) of distinct entities at every object, with h.a_n(v)=a_n(w) for h:v->w. For e use a fixed countable subset of D; for t use the finite alternative. At a relational type, if all argument types have finite domains everywhere, there are finitely many rows and finite tuple domains, hence the relational domain is finite at every object. Otherwise choose a coherent distinct sequence in one argument type and coherent fillers in the other argument types. Coherent fillers always exist: a fixed individual for e and the universal intension for each relational type. This produces coherent distinct tuples t_n(v).

For each A subset N and each object v define F_A(v) by the row `{t_n(w): n in A}` at every arrow v->w. These are admitted by fullness, satisfy h.F_A(v)=F_A(w), and are pairwise distinct by their identity rows. This actually gives a coherent **continuum**, strengthening the induction alternative. Thus every relational type is either finite everywhere or has a root continuum separated by all arrows. The individual type is either too small everywhere or has a fixed continuum. The carrier criterion yields all-type AN and SOAN.

This proof covers the finite-category rows in the table. It supplies the missing same-type information; an unrelated fixed continuum at et or tt would not suffice.


### Scope of the positive conclusions

The preceding table classifies ten positive constructions, not ten newly needed
records. The invertible families `full-involution-group`, `full-infinite-s5`, and
`full-permutation-group-infinite-set` already have valid AN/SOAN support after
the withdrawals; no duplicate argument is added. Finite singleton cases also
retain their existing vacuity proof.

New positive arguments are therefore confined to the ZFC fixed-infinite variants
of `full-idempotent-monoid`, `full-three-object-fork`, `full-two-object-chain`,
`full-two-object-double-retraction`, and `full-two-object-retract`, and to both
ZFC individual settings of `full-monoid-ac-equals-bc` and
`full-surjection-monoid`. Each records SOAN alone; AN is derived. Both generated
signature interpretations are included because the proof is pure and their
constants do not alter domains or transport.

No new positive verdict is asserted here for choiceless variants, supported or
symmetric models, glued monoids, or a natural uncountable individual action of
surjections. The countable principal-ideal diagonal is not extended to uncountable
monoids. The surjection proof uses its separate explicit separators. In the finite
category cases, the current source's normal forms give finitely many outgoing
arrows at each object; for the retract these are id,h at W0 and id,j,k at W1,
with jh=id, hj=k, k squared=k.

## 6. Sources

The counterexamples, carrier criterion and classification above are reproduced
with their hypotheses and proofs. Their sources are:

- GPT-6 Astra, prompted by Daniel Kodsi, *Independent counterexamples to the
  all-type AN arguments*, 29 October 2026, “Exact target” and countermodel C;
  the finite-pin countermodel S is the supplement of the same date.
- GPT-6 Astra, prompted by Daniel Kodsi, *Carrier-sensitive repair*,
  29 October 2026, carrier criterion and countable-monoid consequence.
  The full direct-image proof and the classification of the eleven constructions
  are reproduced in §§4–5 above.

These proof notes are unpaginated. The semantic framework and original
constructions are due to Bacon and Dorr, *Classicism*, §3.5, pp. 58–61,
Appendix D, pp. 73–74, and the sources cited in the individual model entries.
The eight withdrawn sufficient-condition arguments retain their original
attribution; the counterexamples concern their all-type conclusions.
