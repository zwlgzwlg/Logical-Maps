# Full Boolean-valued model with countably closed subset forcing

GPT-6 Astra, prompted by Daniel Kodsi. All-type analytic and represented-power verdicts dated 29 October 2026. Work inside a countable M satisfying ZFC+CH and evaluate by the isolated atom. The common Boolean construction is prior work credited below. Relative consistency upper bound: Con(ZFC).

## Boolean hierarchy, C5 and necessary relational choice

Take a countable M satisfying the stated ZFC ground theory; M need not be transitive or externally well founded. All sets, forcing calculations and type domains below are internal to M until externalized at each standard finite type. Put B=2×A, D_e=omega^M, D_t=B and D_(sigma→tau)=D_tau^(D_sigma) for tau different from e, using the entire internal function set. Evaluate truth by the first coordinate, the isolated atom. Quantifiers are internal meets and joins, and application is internal function application. First-coordinate projection preserves these internally coded meets and joins, so external truth of every fixed finite formula has the ordinary classical quantifier clauses on the externalized domains.

The internal Boolean soundness induction verifies every fixed finite H proof. H-equivalent formulas have identical Boolean values at every assignment, and internal function extensionality identifies their lambda abstractions. This is exactly C's theoremhood-restricted Logical Equivalence rule. Singleton characteristic predicates make Leibniz identity crisp at every type. Necessity is the global top test: Box b=1 iff b=1, and is 0 otherwise. Thus distinctness and its box hold at every type, giving C5. No optional premise is necessitated.

For every predicate F, both forall x Box F(x) and Box forall x F(x) are 1 exactly when every internal F(x)=1, and otherwise are 0. Hence necessary all-type BF holds. For relational choice, internally well-order the output carrier and set

    S(x,y)=U(x,y) and not join_(z<y) U(x,z).

Choice and Replacement in M admit this relation. The S-row values are pairwise disjoint, lie below U, and have the same join as the U-row. Hence S is single-valued with value 1, has totality equal to Serial(U), and is included in U with value 1. The seriality-to-existence-of-functional-subrelation implication has value 1 for every U, so its universal closure and its box have value 1. This uses relation graphs even for individual outputs, without forming a forbidden function type ending in e. These common construction and choice arguments are the prior Bacon/Kodsi Boolean machinery, not new all-type AN arguments.

## 2. Rigidity lemma

Let T be any finite product of admitted internal type domains, including the empty product, and let Y:T->B be admitted. Then the native Rigid(Y) has Boolean value top exactly when all values of Y are endpoints 0_B or 1_B. If it does not have top value it has bottom value, since both defining conjuncts have a leading box.

Necessity: persistence says box forall x (Y(x)->box Y(x)). If Y(x) is neither endpoint, box Y(x)=0 and the indicated implication has value not Y(x), which is not top. The universal meet cannot then be top. Thus persistence of value top requires endpoint values.

Sufficiency: suppose Y=chi_E for an internal subset E of T. Persistence is immediate. For each admitted Z:T->B, the antecedent forall x (Y(x)->box Z(x)) has endpoint value top precisely if Z(x)=top for every x in E; otherwise it has endpoint value bottom. The consequent Y<=Z is box forall x(Y(x)->Z(x)), also top precisely under that very condition. Hence the implication in the inextensibility definition is top for every Z. Its universal quantification and outer box are top. This checks the map's full inextensibility clause, rather than merely stability of membership.

Distinct labels have necessarily distinct identity, so every endpoint-valued carrier automatically meets RigidStr's distinctness requirement. The same lemma applies separately to its order, ternary addition and multiplication graphs, and natural-number predicate.


Construction and forcing checks
-------------------------------
Inside M let P be the set of countable partial functions omega_1 -> 2,
ordered by extension, and A=RO(P). Set B=2 x A, D_e=omega, D_t=B and use
all internally full relational function domains. Externalize and evaluate by the first-coordinate projection, as specified in
the Boolean hierarchy section above.

1. P is countably closed: a decreasing omega-sequence has its countable
union as a condition. The standard recursive decision argument shows that
it adds no omega-sequences of ordinals, in particular no reals, and preserves
omega_1. These are internal ZFC theorems.

2. Ground CH plus unchanged reals and preserved omega_1 implies forced CH.
The old bijection omega_1 ~ R remains a bijection to all extension reals.

3. A has at least continuum many elements. For every ground real r in 2^omega,
take the condition with domain omega and values r. Distinct such conditions
are incompatible, producing an antichain of size continuum in A. Thus
ground R injects into B. All non-e type domains inherit an injection of B
by iterated constant functions, exactly as in the parent's all-type AN proof.

4. The generic union g:omega_1->2 is total and differs from every old function
T:omega_1->2 with Boolean value 1. For a fixed old T and any condition p,
choose alpha outside its countable domain and extend p with value 1-T(alpha).
This is a dense set of conditions forcing disagreement. Hence the subset
H={alpha:g(alpha)=1} satisfies ||H=check(T)||_A=0 for every old subset T of
omega_1. This is a genuinely new subset, not just a mixture of old subsets.

Positive AN and CH verdicts
---------------------------
Since P adds no reals, the old field remains complete against every new
bounded subset: the supremum is determined by a rational cut, which is old.
At every non-e type transport that field along the ground injection; give
its carrier and field relations endpoint values. They are rigid by the
exact rigidity lemma and necessarily real by the full extensional forcing
transfer. At e, a field on a subset of omega cannot be complete in either
coordinate, so the possible-real antecedent is bottom. Thus full AN holds
with top value. This uses the detailed argument in the endpoint-rigidity and necessary-completeness proofs included here,
replacing only the forcing and its capacity check.

For any carrier sigma, consider U_sigma=forall R(Real_sigma(R)->CH(R)).
In the first coordinate, every complete ordered field is internally
isomorphic to the ground reals and satisfies CH. In the forcing coordinate,
the extensional forcing-transfer lemma sends all relation quantifiers to
all subset/relation names on the ground label set; every complete ordered
field is again isomorphic to the extension reals and satisfies CH. The same
argument works below any Boolean support on which a candidate Real tuple
holds. Therefore every Real->CH implication has value top; U_sigma has
value top, and box U_sigma has value top. Hence the exact native all-type
Non-contingency-of-CH schema holds, by its first disjunct. No possible-real
existence assumption is being smuggled into this universal claim; separate
AN gives nonvacuous examples at each non-e type.

Negative SOAN verdict
---------------------
For ANY rigid necessarily-real tuple at any carrier, its endpoint-valued
ground support S is a complete ordered field in M and has cardinal
continuum=omega_1. Transfer the generic new subset H along an old bijection
omega_1->S. Its name K is forced unequal to every old subset of S.
The representation criterion of the endpoint calculation applies:
the join of agreement values over all rigid supported old representatives
has A-coordinate 0, so cannot be top in B. Its box is 0. Every candidate
unary represented power fails; the SOAN existential consequent has value 0
uniformly over all possible rigid necessarily-real structures. At type t
the possible-real antecedent is top, so SOAN_(t,1) is bottom.


## 4. Necessary completeness, including new subproperties

The extensional forcing-transfer lemma applies to box-free formulas whose relation variables are used only by application to labels from D_sigma, with identity between carrier labels. In particular it applies to all field laws, the nonempty bounded-subproperty completeness clause, and the least-inductive N clause. It does NOT identify intensional identity of higher relations with equality of forcing extensions.

For any internal T, every forcing name for a subset of check T normalizes to the internal coefficient function t |-> ||check t belongs to Ydot||_A. Conversely each internal T->A supplies a subset name. At T=D_sigma^k these coefficient functions are precisely the available A-projections of the k-ary relation domain. Their first coordinates can be chosen independently. Quantification over check T reduces to meets/joins over ground labels, including mixed names by Boolean substitution. Therefore the native relation quantifiers in Real see all forcing subsets, not just the old subsets.

We must consequently prove that the CHECK of the old field is complete after forcing. The countably closed forcing adds no subsets of omega, so its reals and rationals are unchanged. For an arbitrary new nonempty subset S of the old reals bounded above, form the rational lower cut L={q in Q: some s in S has q<s}. This cut is coded by a subset of omega and hence is old. Its corresponding old real r is the least upper bound of S. The usual rational-density proof verifies both properties in the extension. Although S may be new, its supremum is old. Equivalently the old real field is the entire extension's real field; this argument spells out the quantifier issue.

The old N predicate is also still the least inductive subproperty: the forcing universe retains the same omega, and ordinary induction there proves every inductive subset contains each natural. Thus the endpoint tuple has Real value top in both the ground and forcing coordinates, so Real itself has B-value top. Its box and RigidStr likewise have value top.

For nonstandard M these are fixed theorems of ZFC, including the forcing statements and coefficient-function translations, interpreted in M. No external identification of its naturals or reals is used. Internal Replacement supplies all coefficient maps for each standard finite formula and type expression. Thus external ill-foundedness creates no additional recursion requirement.

It follows that the existential consequent of AN has Boolean value top at every sigma other than e, regardless of its antecedent.


## 5. The individual-type antecedent is impossible

At e the carrier labels form omega^M. In the first coordinate, every Real_e tuple would be a complete ordered field on a subset of omega. Full relation quantifiers make this the usual internally full second-order field definition. ZFC proves no such field exists.

In the forcing coordinate the same transfer sends a Real_e tuple to a complete ordered field on a subset of check omega. A forcing extension also has no such field: a countable complete ordered field would contradict the standard uncountability theorem for the reals. This argument applies below any positive Boolean support on which Real_e might hold. Thus each Real_e tuple has A-value zero, and its B-value zero; the existential join is zero. Hence diamond exists Real_e is bottom. The e instance of AN is therefore top by vacuity. This is a specific impossibility proof, not an inference from absent witnesses.

Combining sections 3–5 proves every AN instance with value top. In fact each closed instance is necessary because box is the top test.

## Sources

- GPT-6 Astra, prompted by Daniel Kodsi, AN and necessary CH without SOAN, 29 October 2026 (unpaginated), construction and both verdict proofs.
- GPT-6 Astra, prompted by Daniel Kodsi, Independent audit: all-type AN in the no-new-reals collapse model, 29 October 2026 (unpaginated), Section 7.
- Andrew Bacon, Could the truths of mathematics have been different?, draft of 9 October 2025, online Appendix B.2, pp. 7–9 (PDF pp. 41–43), construction and Lemmas B.1–B.4, for the Boolean hierarchy.
- OpenAI Codex, prompted by Daniel Kodsi, Full Boolean-valued carrier and premise audit, 25 October 2026, Sections 5 and 7 (unpaginated), for fixed-label mixed fields, exact extensional transfer and endpoint rigidity.
- OpenAI Codex, prompted by Daniel Kodsi, Generic-point Boolean models: observer separation with contingent CH and analysis, 25 October 2026, Sections 2–3, 6 and 7.2; Generic evaluation of a Boolean model: independent observer and forcing audit, same date (unpaginated), for internal C soundness, necessary BF/relational choice and the no-new-reals collapse.
