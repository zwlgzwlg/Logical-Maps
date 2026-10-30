# Qualitative-link model with a translation clock

GPT-6 Astra, prompted by Daniel Kodsi. Construction and proof dated 30 October 2026. The recursive old-domain injection and every-new-test slicing argument preserve the singleton qualitative-link Tame counterexample while the clock supplies all-carrier represented real powers. Actual individuals remain singleton; the auxiliary pinning base is separate.

1. Exact target and why full completion is the wrong extension
--------------------------------------------------------------
Native Tame Rigidity is forall F(WeaklyRigid(F)->Rigid(F)), at every
relational type. A witness is persistent and weakly inextensible at the
evaluation point but loses weak inextensibility later. Nullary propositions
cannot witness this failure; the chosen witness has type (tt)t.

Unrestricted full action completion will not preserve this witness in
general. In a fully admitted profile hierarchy, the exact direct-image
relation of any actual extension is admitted and rigid. Every weakly rigid
relation is coextensive with such a rigid relation and hence identical to
it, so Tame Rigidity follows. This is the obstruction explained in Kodsi
homogeneity-amalgamation-lane.md section 22. Merely applying the full-action
carrier criterion to a completion would therefore destroy the negative
side of the intended separation.

The extension below enlarges only an independent translation coordinate
while keeping a uniform finite pin on the old coordinate. Its preservation
proof addresses every new test, rather than presuming that an old weak-
rigidity verdict survives additional predicates.

2. Old model and its concrete negative witness
-----------------------------------------------
Let B be the auxiliary qualitative-link base, M its monoid, and G its
symmetry group, exactly as in native symmetric-qualitative-links.yaml.
Use its singleton-individual variant. The actual individual sort is a
singleton; it is separate from B. Relational domains D_tau contain exactly
the external G-symmetric, finitely B-pinned row profiles at that type.

The native tame-rigidity argument records U:(tt)t as follows. Let a,b be
the distinguished point pair, V the nonpoints, q_uv={h:hu=hv}, and C_z the
rigid exact-image star of {q_zw:w in V}. The map z -> C_z is injective and
transports by h to C_hz. Put

    U_h = {C_z : z in R(ha,hb)}.

It is symmetric and pinned by {a,b}. It is weakly persistent because arrows
preserve the qualitative relation R. Here is the weak-inextensibility
argument relevant to preservation. For a test Z with finite pin S which
necessarily holds of every initial C_z in the a,b link fibre, enlarge S
to a finite closed set including a,b. At a symmetry h, every member of
the future fibre is an image of an initial member. At a collapsing h, a
fresh initial link outside the closed finite pin can be sent to either
desired companion of ha=hb by an arrow h' agreeing with h on S. The test
holds there by its premise, and pinning makes its h and h' rows equal.
Thus the test contains every U_h. This uses the source's finite coherent-
prescription extension step (draft Proposition 50), exactly the step
already used in the recorded negative verdict.

At a collapse h the U_h fibre consists of the two companion codes C_d0,
C_d1. Their finite union of haecceities is rigid and necessarily holds of
both. A further allowed collapse k merges d0,d1; the test then holds only
of their single image code, while U_kh still contains both distinct
companion codes of the new point. Thus h.U is not weakly inextensible.

The source dependence is precise: existence of those finite-prescription
extensions, injectivity of the C_z codes, and the recorded model-of-C
construction. No field-existence or AN verdict from that source is used.

3. Product category and its exact admitted domains
--------------------------------------------------
Form the disjoint auxiliary base B'=B disjoint-union omega. Let

    M' = M x (omega,+).

The arrow (m,n) acts as m on B and as k -> k+n on the added omega. Let
G'=G x {0}, acting trivially on that omega. Use the finite-set pin ideal
and singleton actual individuals. Form the symmetric ideally-full model
with these data; write its recursively generated domains D'_tau.

Composition is (l,r)(m,n)=(lm,r+n). Images of finite pins are finite, the
symmetries are invertible and preserve the ideal, and every actual
individual has the empty pin. These are ordinary data for the same
symmetric ideally-full construction as the old model.

An exact useful description of the new domains is:

    a profile is G'-symmetric and has ONE finite spatial pin S subset B
    which pins its rows at every fixed clock coordinate n.

There is no restriction on its dependence on n. For sufficiency adjoin
the singleton pin {0_clock}: agreement there forces the two clock shifts
to be equal, and agreement on S then forces equal rows. For necessity
take the B-part of any finite pin: at the same clock coordinate all clock
pin values automatically agree. This equivalence is at each recursively
defined type, with rows on the NEW argument domains. In particular it is
not a construction that simply restricts the outermost row indices of
an already full higher-type model.

The optional relational signature constants can be top, with any
individual constants denoting the sole individual. No extra landing or
Henkin conditions are imposed.

4. Embedding old profiles and slicing EVERY new test
----------------------------------------------------
Define injections i_tau:D_tau -> D'_tau by induction on types. At e use
the singleton identity. For a relation F with tuple arguments of types
sigma_1,...,sigma_k, define

    (i F)_(m,n) = { (i x_1,...,i x_k) : (x_1,...,x_k) in F_m }.

For k=0 this is simply the old proposition independent of the clock.
If F is pinned by S, iF is pinned by the same S and is symmetric by the
inductive equivariance of the i_sigma. The injections are injective
because an old distinguishing row and tuple remain distinguishing. They
satisfy, as WHOLE entities,

    (m,n).i_tau(x) = i_tau(m.x).

This follows by evaluating both sides at every further (l,r); both rows
are the i-image of the old row at lm. In particular G'-equivariance holds.
These maps need not preserve arbitrary logical operations or unrestricted
quantifiers. They are equivariant injections of profile domains; the
preservation argument below does not assume more.

Now let Z be ANY admitted new test of a relation's tuple type. For each
fixed external n define an old profile by

    Z[n]_m = { x_tuple : i(x_tuple) belongs to Z_(m,n) }.

The exact domain description in section 3 gives it a finite old spatial
pin. It is old G-symmetric: the i maps commute with G, and invertibility
of g ensures membership in the image of i is preserved in both directions.
Therefore Z[n] is admitted in the OLD domain. This is the crucial check
which rules out newly available tests silently defeating old weak rigidity.

Suppose F is old weakly rigid. The image iF is weakly persistent, by
equivariance and old weak persistence. If a new test Z necessarily holds
of all members i(x) of its current extension, then for every x in F_1,
every m, and every n,

    i(m.x) belongs to Z_(m,n).

Thus each old Z[n] necessarily holds of every current F-member. Old weak
inextensibility gives F_m subset Z[n]_m for every m. Consequently

    (iF)_(m,n) subset Z_(m,n)

for every (m,n), proving new weak inextensibility. The same reasoning
applies at all transported old profiles. Thus rigid old profiles also
remain rigid.

If old h.F fails weak inextensibility with an old test Q, then at (h,0)
the lifted test iQ has the same premise on the lifted current extension.
All clock shifts are irrelevant to iQ. The old later omitted tuple lifts
to a new omitted tuple, so the failure survives. Applying this to section
2 proves that iU is weakly rigid but not rigid. No elementary/conservative
embedding claim for the entire language is needed or made.

5. A continuum whose members survive every clock shift
-------------------------------------------------------
Partition omega into infinite unbounded sets

    B_j = {2^j(2l+1)-1 : l in omega},  j in omega.

For A subset omega let s_A=union_{j in A} B_j. If A!=A', their two sequences
disagree at arbitrarily large coordinates. Therefore EVERY common shift
n leaves them distinct: some k has k+n in their symmetric difference.

The proposition p_A in the new model is defined by

    (m,n) belongs to p_A iff n belongs to s_A.

It is symmetric and pinned by {0_clock}. For each arrow (m,n), the map
A -> (m,n).p_A is injective: its values at later clock shifts k detect
the arbitrarily late disagreement. This establishes the same-type
separation needed at t, not merely continuum size of the domain.

For EVERY relational carrier tau=sigma_1...sigma_k t, including k=0,
define F_A^tau by putting the universal tuple row at (m,n) when n is in
s_A, and the empty row otherwise. All argument domains are nonempty,
so the two rows differ. These profiles are admitted with the same single
clock pin and are fixed by every (g,0). Their whole transports depend
only on the clock shift, and

    A -> (m,n).F_A^tau

is injective for every arrow. This checks the carrier construction at
each tau separately, including types whose arguments themselves involve
e or arbitrarily high relational types.

6. Field and power admission, not just a full-model criterion
------------------------------------------------------------
Fix an external injection r -> A_r from R into P(omega). At each chosen
relational carrier tau put

    j_n(r) = (1_M,n).F_(A_r)^tau.

Every j_n is injective and (m,k).j_n(r)=j_(n+k)(r). All j_n(r) are fixed
by G'. Define the field carrier row at (m,n) as j_n[R], with order,
addition and multiplication the j_n-images of the ordinary real-field
relations, and natural row j_n[N]. Zero and one at the source are j_0(0)
and j_0(1).

Each predicate profile depends only on n, so {0_clock} pins it. Its rows
are G'-invariant since their members are G'-fixed. Thus the profiles are
admitted. They have exact-image transport at every intermediate point.
That gives persistence and the native leading-box inextensibility: every
future member is the image of a current member, so any test necessarily
true of all current members covers every future extension. The j_n
injections give necessary distinctness. At each point the current field
is externally R, complete against all admitted subsets and with its
specified natural predicate least. Hence the tuple is rigid and
necessarily real at THIS SAME tau.

For each external T subset R^k define Q_T with row j_n^k[T] at (m,n).
It has the same pin and symmetry proof and the same exact-image rigidity.
Define the representing family at (m,n) to be

    { (m,n).Q_T : T subset R^k }.

This is a set of whole relation entities. It depends only on n, its
members are fixed by G', and its further transport is exactly the family
at the sum of the clock coordinates. Thus it too is admitted and rigid.
At a target with clock n, restrict ANY target relation to j_n[R]^k and
pull it back by j_n. The resulting external subset T has transported
representative (m,n).Q_T in the family. This verifies the boxed arbitrary-
target representation clause, not only representation of transported
source relations. All finite arities use the same chosen field.

Therefore the construction supplies the SOAN consequent at every
relational carrier type, without needing to inspect its antecedent.
At e there is a singleton at every point, so no ordered real field is
possible and the e instances are vacuous. This proves full SOAN and AN. It does not infer all-type AN from one real-bearing
carrier.

## Sources

- GPT-6 Astra, prompted by Daniel Kodsi, SOAN does not imply Tame Rigidity: a translation-coordinate model, 30 October 2026 (unpaginated), Sections 1–6.
- Cian Dorr, symmetric ideally-full model construction and qualitative-link model; Logical Maps symmetric-qualitative-links.yaml, singleton-individual tame-rigidity argument dated 11 October 2026 (unpaginated).
- Daniel Kodsi, Integer-shift predecessor with contingent Barcan, Sections 1–3; Central-map complete gluing; and Logical Maps supported-product-free-monoids-glued-constants, Section 9 (unpaginated), for the translation-coordinate and exact-image code-field methods.
