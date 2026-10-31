# Full Boolean-valued model with a no-new-reals collapse

GPT-6 Astra, prompted by Daniel Kodsi. All-type analytic verdict proof dated 29 October 2026. The underlying Boolean construction, mixed-field transfer and no-new-reals forcing are prior work, credited below. Evaluation in this record is the isolated atom; generic evaluation is also described as an available alternative. Relative consistency upper bound: Con(ZFC).

## Boolean hierarchy, C5 and necessary relational choice

Take a countable M satisfying the stated ZFC ground theory; M need not be transitive or externally well founded. All sets, forcing calculations and type domains below are internal to M until externalized at each standard finite type. Put B=2×A, D_e=omega^M, D_t=B and D_(sigma→tau)=D_tau^(D_sigma) for tau different from e, using the entire internal function set. Evaluate truth by the first coordinate, the isolated atom. Quantifiers are internal meets and joins, and application is internal function application. First-coordinate projection preserves these internally coded meets and joins, so external truth of every fixed finite formula has the ordinary classical quantifier clauses on the externalized domains.

The internal Boolean soundness induction verifies every fixed finite H proof. H-equivalent formulas have identical Boolean values at every assignment, and internal function extensionality identifies their lambda abstractions. This is exactly C's theoremhood-restricted Logical Equivalence rule. Singleton characteristic predicates make Leibniz identity crisp at every type. Necessity is the global top test: Box b=1 iff b=1, and is 0 otherwise. Thus distinctness and its box hold at every type, giving C5. No optional premise is necessitated.

For every predicate F, both forall x Box F(x) and Box forall x F(x) are 1 exactly when every internal F(x)=1, and otherwise are 0. Hence necessary all-type BF holds. For relational choice, internally well-order the output carrier and set

    S(x,y)=U(x,y) and not join_(z<y) U(x,z).

Choice and Replacement in M admit this relation. The S-row values are pairwise disjoint, lie below U, and have the same join as the U-row. Hence S is single-valued with value 1, has totality equal to Serial(U), and is included in U with value 1. The seriality-to-existence-of-functional-subrelation implication has value 1 for every U, so its universal closure and its box have value 1. This uses relation graphs even for individual outputs, without forming a forbidden function type ending in e. These common construction and choice arguments are the prior Bacon/Kodsi Boolean machinery, not new all-type AN arguments.

## 1. Model and exact native semantics

Inside M put kappa=2^aleph0, P={countable partial functions omega1 -> kappa}, ordered by extension, A=RO(P), and B=2 x A. Write a=(1,0), b=(0,1). P is countably closed, preserves omega1, adds no reals, and forces a surjection omega1 -> kappa. Thus P forces CH, while M satisfies not-CH. P is weakly homogeneous and atomless. The antichain of assignments to one fixed coordinate has size kappa, so kappa injects into A and hence into B.

Define internally D_e=omega and D_t=B; D_(sigma->tau) is the full internal function set D_tau^D_sigma whenever tau is not e. Externalize each such internal set. Connectives use B, quantifiers use internal meets/joins, and application is internal function application. Defined Leibniz identity is crisp: it is top exactly for equal labels, because all singleton characteristic predicates are admitted. Consequently box p is top exactly when p=top, and bottom otherwise.

The underlying C soundness, lambda closure and generic quantifier lemma are in *Generic-point Boolean models: observer separation with contingent CH and analysis*, sections 2–3. For clarity, the only external genericity needed is an M-generic ultrafilter G on A. For each internal family f:I->A, the internally dense set of nonzero c satisfying c<=not(join f) or c<=f(i) for some i ensures join f belongs to G iff some f(i) belongs to G. Complements yield the meet version. Thus evaluation by the A-coordinate in G has ordinary classical quantifier truth clauses. The isolated evaluation via the 2-coordinate also has those clauses, directly. All fixed formula evaluations and families are internal to M. C5 and necessary BF follow directly from crisp identity and the global top test; the necessary Relational Choice proof disjointifies each row along an internal well-order.

## 2. Rigidity lemma

Let T be any finite product of admitted internal type domains, including the empty product, and let Y:T->B be admitted. Then the native Rigid(Y) has Boolean value top exactly when all values of Y are endpoints 0_B or 1_B. If it does not have top value it has bottom value, since both defining conjuncts have a leading box.

Necessity: persistence says box forall x (Y(x)->box Y(x)). If Y(x) is neither endpoint, box Y(x)=0 and the indicated implication has value not Y(x), which is not top. The universal meet cannot then be top. Thus persistence of value top requires endpoint values.

Sufficiency: suppose Y=chi_E for an internal subset E of T. Persistence is immediate. For each admitted Z:T->B, the antecedent forall x (Y(x)->box Z(x)) has endpoint value top precisely if Z(x)=top for every x in E; otherwise it has endpoint value bottom. The consequent Y<=Z is box forall x(Y(x)->Z(x)), also top precisely under that very condition. Hence the implication in the inextensibility definition is top for every Z. Its universal quantification and outer box are top. This checks the map's full inextensibility clause, rather than merely stability of membership.

Distinct labels have necessarily distinct identity, so every endpoint-valued carrier automatically meets RigidStr's distinctness requirement. The same lemma applies separately to its order, ternary addition and multiplication graphs, and natural-number predicate.

## 3. Capacity at every non-individual type

Every internal D_sigma is nonempty. For each admitted sigma other than e there is an internal injection i_sigma:B->D_sigma, constructed by external induction on the finite output spine:

- i_t is the identity on B.
- If sigma=alpha->beta, where beta is not e, put i_sigma(q) equal to the constant function with value i_beta(q). It is admitted by internal fullness and is injective because D_alpha is nonempty.

Compose i_sigma with the injection of the ground real set into B supplied by the size-kappa antichain. This gives a ground injection j_sigma:R^M->D_sigma, for EVERY non-e sigma, including types with individual arguments and types built from t alone. No operation ending in e is formed. This is a metatheoretic internal injection; its graph and all field relations are admitted in the permitted relational types.

Transport the ground real field along j_sigma. Let its carrier, order, addition graph, multiplication graph and N predicate all be characteristic functions with values 0_B and 1_B, and let zero and one be j_sigma(0),j_sigma(1). Every component is internal, admitted and rigid by section 2. All fields and chosen injections may depend on sigma; a type schema does not require a single object-language witness spanning types.

## 4. Necessary completeness, including new subproperties

The extensional forcing-transfer lemma applies to box-free formulas whose relation variables are used only by application to labels from D_sigma, with identity between carrier labels. In particular it applies to all field laws, the nonempty bounded-subproperty completeness clause, and the least-inductive N clause. It does NOT identify intensional identity of higher relations with equality of forcing extensions.

For any internal T, every forcing name for a subset of check T normalizes to the internal coefficient function t |-> ||check t belongs to Ydot||_A. Conversely each internal T->A supplies a subset name. At T=D_sigma^k these coefficient functions are precisely the available A-projections of the k-ary relation domain. Their first coordinates can be chosen independently. Quantification over check T reduces to meets/joins over ground labels, including mixed names by Boolean substitution. Therefore the native relation quantifiers in Real see all forcing subsets, not just the old subsets.

We must consequently prove that the CHECK of the old field is complete after forcing. P adds no subsets of omega, so its reals and rationals are unchanged. For an arbitrary new nonempty subset S of the old reals bounded above, form the rational lower cut L={q in Q: some s in S has q<s}. This cut is coded by a subset of omega and hence is old. Its corresponding old real r is the least upper bound of S. The usual rational-density proof verifies both properties in the extension. Although S may be new, its supremum is old. Equivalently the old real field is the entire extension's real field; this argument spells out the quantifier issue.

The old N predicate is also still the least inductive subproperty: the forcing universe retains the same omega, and ordinary induction there proves every inductive subset contains each natural. Thus the endpoint tuple has Real value top in both the ground and forcing coordinates, so Real itself has B-value top. Its box and RigidStr likewise have value top.

For nonstandard M these are fixed theorems of ZFC, including the forcing statements and coefficient-function translations, interpreted in M. No external identification of its naturals or reals is used. Internal Replacement supplies all coefficient maps for each standard finite formula and type expression. Thus external ill-foundedness creates no additional recursion requirement.

It follows that the existential consequent of AN has Boolean value top at every sigma other than e, regardless of its antecedent.

## 5. The individual-type antecedent is impossible

At e the carrier labels form omega^M. In the first coordinate, every Real_e tuple would be a complete ordered field on a subset of omega. Full relation quantifiers make this the usual internally full second-order field definition. ZFC proves no such field exists.

In the forcing coordinate the same transfer sends a Real_e tuple to a complete ordered field on a subset of check omega. A forcing extension also has no such field: a countable complete ordered field would contradict the standard uncountability theorem for the reals. This argument applies below any positive Boolean support on which Real_e might hold. Thus each Real_e tuple has A-value zero, and its B-value zero; the existential join is zero. Hence diamond exists Real_e is bottom. The e instance of AN is therefore top by vacuity. This is a specific impossibility proof, not an inference from absent witnesses.

Combining sections 3–5 proves every AN instance with value top. In fact each closed instance is necessary because box is the top test.

## 6. Separation from SOAN

At sigma=t, the tuple above is necessarily real. By full extensional transfer and complete-field categoricity, the universal CH assertion U_CH=forall R (Real_t(R)->CH(R)) has B-value b=(0,1): CH is false in M and forced true by P. The universal opposite assertion U_notCH has value a=(1,0). Neither is top, so box U_CH and box U_notCH are bottom. The native non-contingency instance fails at both designated evaluations.

SOAN implies Necessity of Second-Order Analysis and thence Non-contingency of CH in the existing map. The proof uses represented powers for the finitely many relation arities of CH, rigidity to propagate restricted quantifiers, and field categoricity. Therefore SOAN fails in this model. This is the clean headline separation; a separate direct represented-power argument is being audited to identify its sharper unary boundary.


## Direct unary represented-power obstruction (independent audit §5)

This check strengthens the negative conclusion to failure already at sigma=t, n=1.

Internally fix an injection code: omega_1 x kappa -> R; it exists because kappa=|R| > omega_1 and infinite cardinal multiplication gives omega_1*kappa=kappa. Let dot f be the generic surjection omega_1 -> kappa and dot Y its graph encoded as a subset of the ground reals. For every old U subset R,

    ||dot Y = check U||_A = 0.

Indeed a nonzero condition forcing equality would force that the fixed old decoding of U is a surjection omega_1 -> kappa. That property of a fixed ground graph and fixed ground sets is absolute, and the ground cardinal inequality rules it out. This argument is uniform internally over the set of all old U.

Now take any candidate rigid necessary real tuple at t. If its RigidStr or boxed Real conjunct has value 0, it cannot witness SOAN. Otherwise the endpoint-rigidity lemma says its field predicates are endpoint-valued; its first coordinate says that its ground carrier S and operations form a complete ordered field. There is an internal ground isomorphism R -> S. Transfer dot Y along it and extend by zero off S, obtaining an admitted A-valued predicate on D_t; choose its first coordinate arbitrarily.

For a proposed unary represented power P, Rigidity(P) again forces P endpoint-valued, or else the conjunction has value 0. If a selected relation is not rigid, the qualification conjunct has value 0. All selected qualified relations are therefore endpoint-valued predicates supported on S, i.e. ground subsets of S. (If one has support outside S the support qualification likewise has value 0.) The A-coordinate of agreement of any such selected relation with the transferred dot Y is 0, by the preceding calculation. Their existential join is 0 in the A-coordinate. The required boxed universal representation clause is consequently 0. No P witnesses RepPower_1 for any candidate field tuple.

Thus the existential SOAN_(t,1) consequent is 0, while its possible-real antecedent is 1 by the explicit rigid necessary field already constructed. **SOAN_(t,1) has value 0.** This proof also explains the distinction: preserving reals preserves complete field structure, but need not preserve subsets of that field.

## Sources

- GPT-6 Astra, prompted by Daniel Kodsi, A fixed continuum at every carrier type, 29 October 2026 (unpaginated), Sections 1–6.
- GPT-6 Astra, prompted by Daniel Kodsi, Independent audit: all-type AN in the no-new-reals collapse model, 29 October 2026 (unpaginated), Sections 1–5.
- Andrew Bacon, Could the truths of mathematics have been different?, draft of 9 October 2025, online Appendix B.2, pp. 7–9 (PDF pp. 41–43), construction and Lemmas B.1–B.4, for the Boolean hierarchy.
- OpenAI Codex, prompted by Daniel Kodsi, Full Boolean-valued carrier and premise audit, 25 October 2026, Sections 5 and 7 (unpaginated), for fixed-label mixed fields, exact extensional transfer and endpoint rigidity.
- OpenAI Codex, prompted by Daniel Kodsi, Generic-point Boolean models: observer separation with contingent CH and analysis, 25 October 2026, Sections 2–3, 6 and 7.2; Generic evaluation of a Boolean model: independent observer and forcing audit, same date (unpaginated), for internal C soundness, necessary BF/relational choice and the no-new-reals collapse.
