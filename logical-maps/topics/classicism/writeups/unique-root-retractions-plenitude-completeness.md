# Plenitude and completeness with unique root retractions

GPT-6 Astra, prompted by Daniel Kodsi. 30 October 2026.

**Theorem.** In a C-valid restricted typed profile hierarchy with natural
transports and application, ordinary lambda, quantifier and modal clauses,
and faithful whole-profile identity, suppose every arrow h from the evaluation
object v has a unique categorical left inverse j_h. Current all-type Plenitude
at v implies current all-type Rigid Comprehension and Boolean Completeness.

Faithfulness means that equality of all future profile rows is literal identity
of admitted entities and agrees with the native identity predicate. The theorem
does not require external fullness. It is a theorem about this specified class;
its categorical hypothesis is not a premise node in the map. Accordingly it
adds no unrestricted Plenitude-to-completeness arrow. Both conclusions are
current and Boolean Completeness is internal, over admitted families.

## 1. Categorical hypotheses and the ND mask

For h:v -> u, `j_h h=id_v` implies that h acts injectively on every admitted typed carrier. Thus the closed type-specific sentence

    ND_tau := forall x,y^tau (x!=y -> Box(x!=y))

is true at v. In the stated semantics, ND_tau at any object z says exactly that every outgoing transport from z is injective on its current tau-carrier: its quantifiers range over that entire carrier, identity is literal, and Box checks every outgoing arrow.

For h:v -> u and r:u -> z, put f=rh. The composite j_f r is a categorical left inverse of h, so uniqueness gives

    j_f r = j_h.                                        (1)

The categorical condition is equivalent to coherent root retractions. Unique inverses yield (1). Conversely, if a coherent chosen family exists and q is any left inverse of h, coherence at qh=id_v gives `j_id q=j_h`; since j_id=id_v, q=j_h. This is a condition on actual category arrows, not a newly admitted object-language operation choosing arrows.

The mask `w_tau=ND_tau` is a closed admitted sentence. It is true at v and is evaluated anew at each future object by the normal closed-term semantics. It is not inferred to be true everywhere. The recorded result [[plenitude-r-implies-distinctness-necessary-r]] already supplies source ND from Plenitude independently; this does not remove the use of actual coherent return arrows later in the proof.

## 2. Decoder admission and its exact quantifier scope

Fix a relational output type tau. Ordinary lambda closure admits

    c(y) = lambda z^tau (ND_tau and z=y).

At v its current extension is the singleton {y}, so equality of two whole codes forces equality of their arguments by evaluation at y. Thus c is actually injective. The inverse-on-range relation

    U(A,y) iff A=c(y)
       or ((not exists z A=c(z)) and y=Bottom_tau)

is an admitted lambda term and is actually total and single-valued. Bottom_tau exists because tau is relational. The native Plenitude instance with input type tau-t and output type tau supplies an admitted operation d with

    d(c(y))=y                                           (2)

for every actual root y. No individual-valued operation is requested, no external selector graph is admitted, and no future instance of Plenitude is used.

Equation (2) is equality of whole entities at v, pointwise under a current universal quantifier. For any one source y it can be transported along h. The proof never transports the universal quantifier as though it ranged over new entities at h's target.

## 3. The decisive comparison checks every future row

Fix h:v -> u and arbitrary Y in the full admitted D_tau(u). Compare the two admitted property entities

    (h*c)(Y)  and  h*(c(j_h*Y)).                         (3)

Take an arbitrary arrow r:u -> z and set f=rh. Their rows are empty if ND_tau is false at z. If it is true, the rows are respectively the singletons of rY and f(j_h Y).

The arrow j_f:z -> v exists because f is an outgoing root arrow. ND_tau at z makes j_f injective on D_tau(z). Since `j_f f=id_v`, for every Z in that target carrier,

    j_f(f(j_f Z))=j_f Z,

and cancellation yields `f(j_f Z)=Z`. With Z=rY and (1), this gives

    rY=f(j_f(rY))=f(j_h Y).

Hence the two rows in (3) agree for every r and every target argument, whether the mask is false or true there. Faithful whole-profile identity gives (3) as an entity equality. This does not infer identity from current coextension. It uses neither a source-only argument domain nor an assumed isolating mask.

Apply h*d to (3), and instantiate (2) only at `j_h Y`, which really is in D_tau(v). Naturality then gives

    (h*d)((h*c)(Y)) = h*(j_h*Y).                       (4)

The resulting value is the return projection h j_h Y, not necessarily Y. Thus the argument does not silently assert that h is onto or that d is a strong inverse on all future inputs. This distinction is essential for the exact-retract examples.

## 4. Source-image predicates are admitted terms

For any input type sigma, including e, use the previous construction at the relational type tau=sigma-t. Its decoder output is therefore admissible even when sigma=e. The haecceity `H_x=lambda z(z=x)` is admitted, natural under transport, and injective as a code: `H_a=H_b` iff a=b, by current evaluation.

Define the admitted predicate

    P_sigma(x) := d(c(H_x))=H_x.

At a target u after h, apply (4) to the full target entity H_x. Its truth condition becomes

    H_(h j_h x)=H_x  iff  h j_h x=x.

Because j_h h=id, these fixed points are exactly the image of the root carrier under h. All target x are included in this verification; new x outside that image make the predicate false.

For a finite tuple, conjunction of the coordinate predicates defines an admitted tuple predicate H whose row at h is precisely the image of the full actual tuple domain. A finite product of image sets is the image of the tuple transport; no infinitely indexed choice or comprehension is hidden here. The empty tuple case is Top_t.

The tuple hull is also the Boolean join of the admitted family `A(R):=exists a_bar (R=H_a_bar)`. Every current family member lies below it, and any whole-profile upper bound contains every transported source tuple at every row. This proves the join's leastness. It is not an external-union admission argument: the predicate H was already built by lambda terms and the decoder before its rows were identified. The complementary zero-evaluation ideal has this hull's complement as its greatest element.

## 5. Bivalent evaluation and full rigidity

For completeness, Plenitude supplies the ordinary source bivalent evaluator directly. The admitted relation

    V(p,q) iff (p and q=Top_t) or (not p and q=Bottom_t)

is currently total and single-valued. Plenitude at input t, output t gives E such that E(p) is literally Top or Bottom according to p's current truth. No assertion about correct future evaluation of arbitrary new propositions is licensed or used.

Given any admitted current relation X with actual extension A, define

    Y = H and (lambda x_bar E(X[x_bar])).

Its row at h is exactly h[A]. Indeed H restricts the row to tuples h(a_bar) from the actual source domain. Naturality makes the other factor `h(E(X[a_bar]))`, which is the transported literal endpoint recording the source truth. Root transports are injective, so a target image tuple cannot represent two source tuples with conflicting X-membership. At the identity this gives current coextension with X.

To check the full native rigidity definition, fix any h:v -> u. The current extension of hY is h[A], and its row at every subsequent r is r[h[A]]. Every current member therefore persists along every r. If an arbitrary admitted test relation Z at u necessarily holds of every current member of h[A], then its r-row contains r[h[A]] for every r. It follows that hY<=Z. Thus hY is both weakly persistent and weakly inextensible at u, with all the native target quantifiers.

Since h was arbitrary, Y is necessarily weakly rigid, exactly the native Rigid(Y) clause. The argument establishes current Rigid Comprehension for every admitted X at v; it does not choose rigid coextensions for all new relations at every future object. This is why the schema has not been proved necessary.

## 6. BC and the type shift

The recorded theorem [[weak-rigid-comprehension-r-implies-boolean-completeness-r]] applies. For an internally admitted family F of tau-entities, weak rigid comprehension is needed at its property type tau-t. The construction above supplies rigid, hence weakly rigid, coextensions at all those higher types. The source existential-union proof then supplies the tau-join. The necessary type shift is present; the argument does not confuse a hull at tau with comprehension of arbitrary tau-indexing predicates.

BC here is the native internal completeness schema, over admitted families. Neither arbitrary external joins nor powerset closure follows from the proof.

## Sources

- GPT-6 Astra, prompted by Daniel Kodsi, *Unique root retractions: Plenitude and
  Boolean Completeness*, 30 October 2026, sections 1–6 (unpaginated): the masked
  decoder and restricted-profile theorem.
- The map's `coherent-retractions` condition and argument: the categorical
  coherence condition and its earlier externally full construction.
- *Gallin comprehension as a unique Boolean evaluator*, 22 October 2026, section 7
  (unpaginated research notes): coherent return maps.
- OpenAI Codex, prompted by Daniel Kodsi, *Choice and uniformization: research notes*, 22 October 2026
  (unpaginated): inverse-on-range representation.
- GPT-6 (OpenAI), *Rigidity, actualization and evaluation: research notes*,
  22 October 2026, section 9 (unpaginated): haecceity hulls.
