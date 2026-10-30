# Nominal cofinite entrance over sections and projection

GPT-6 Astra, prompted by Daniel Kodsi. Construction and proof dated 30 October 2026. The following proof gives internal Boolean Completeness and Strong Atomicity at every relational type in ZFC. The prior nominal closure, supported-family joins and sections/projection tail retain their source attribution.

## Conclusion and exact assumptions

In ordinary ZFC, the construction satisfies at its new root O:

    Strong Atomicity at every relational type;
    Boolean Completeness at every relational type;
    failure of necessary Inextensible Comprehension.

No measurable cardinal or other large-cardinal assumption is used. Boolean Completeness is INTERNAL: joins exist for every admitted current family. The root Boolean algebras are not asserted to be externally complete. Root relational fullness, BF, choice, or boxed completeness are not asserted.

The old tail is the established finitely pinned sections/projection model. All its objects, arrows, typed domains and truths remain unchanged.

## 1. Category and common finite pin

Write A=N, B=N×2, f_T(n)=(n,T(n)), p(n,i)=n, and e_T=f_T p. The tail has only id_A at A→A, all f_T at A→B, only p at B→A, and id_B plus all e_T at B→B. The relations are

    p f_T=id_A, e_U f_T=f_U, e_U e_T=e_U, p e_T=p.

Fix finite S⊆N containing 0, and put E=2^S, a FINITE set. S={0} suffices. Choose representatives T_eta extending eta for every eta∈E.

Add O with no incoming arrows except its identity. Its outgoing arrows are y:O→A; x_T=f_T y:O→B; and fresh z_(eta,n):O→B for eta∈E,n∈N. Set

    p z_(eta,n)=y, e_U z_(eta,n)=x_U,
    p x_T=y, e_U x_T=x_U.

The tail equations verify associativity. Give O one individual *, sent by y to 0, by x_T to (0,T(0)), and by z_(eta,n) to (0,T_eta(0)). These maps respect composition. When T|S=eta the x_T and z_(eta,n) individual images agree, since 0∈S.

## 2. Replica permutation group

Let G=product_(eta∈E) Sym(N). It permutes replica indices within each eta-class, fixes O,A,B and all old arrows, fixes y and all x_T, and sends z_(eta,n) to z_(eta,g_eta(n)). This is a category automorphism preserving the individual functor. It fixes every old typed entity; its root action is defined recursively below.

A finite support J is a finite subset of E×N. G_J is the subgroup fixing each index in J. A subset of a root tuple domain is finitely supported when some G_J preserves it setwise. The group consists of all permutations, not just finite permutations; G_J acts transitively on N minus its finite fixed indices in each eta-class.

## 3. Recursive root domains

The root individual * is G-fixed. For tau=bar sigma t, assuming the smaller root argument domains and their G-actions have been defined, a root entity has the following data:

- A FINITELY SUPPORTED current extension E_O⊆D_O(bar sigma).
- An arbitrary old A-table E_A⊆D_A(bar sigma).
- For every eta∈E, a sequence of arbitrary old B-tables C_(eta,n)⊆D_B(bar sigma), required to be eventually constant. Write its unique eventual value R_eta.

There is no common finite bound on the exception positions of different entities. There is no restriction on the cardinality of E_O, E_A, C_(eta,n), or R_eta beyond being subsets of the appropriate SETS. Only E_O must have finite group support.

Define a at A and b_(eta,n) at B by the whole raw profiles

    a_idA=E_A,       a_fT=R_(T|S),

    (b_(eta,n))_idB=C_(eta,n),
    (b_(eta,n))_p=E_A,
    (b_(eta,n))_eU=R_(U|S).

These are admitted old entities. The A profile is S-pinned. The B profile is pinned by S×2, which contains a complete fibre to distinguish id_B from every e_U. Agreement of e_U,e_V on this pin gives U|S=V|S and equality of their whole transported profiles. The sole p arrow has a different target. Consequently arbitrary identity-row modifications at B are permitted.

Root transports are

    yX=a, x_T X=f_T a, z_(eta,n)X=b_(eta,n).

They satisfy p b_(eta,n)=a and e_U b_(eta,n)=f_U a. Also

    b_(eta,n)=f_Teta a

as WHOLE B-entities for all but finitely many n. The profile's current root row is E_O. These data uniquely determine its intension at every root arrow.

The root G-action is

    E_O(gX)=g[E_O(X)],
    E_A(gX)=E_A(X),
    C_(eta,n)(gX)=C_(eta,g_eta^(-1)(n))(X).

Eventual values R_eta are unchanged. This is a well-defined group action and preserves the domain. If E_O has support J and the union of the finite exception positions of the sequences is K, then J union K supports the WHOLE entity X. E is finite, so K is finite. Therefore every root entity has finite support, by induction on type. In particular every finite root tuple has finite support, and its singleton current extension is admitted at the next relational type.

The action intertwines transport with arrow relabeling:

    rho_(g h)(gX)=rho_h(X)

for each outgoing root arrow h into an OLD target (h != id_O); old target domains carry the trivial G-action. At h=id_O the correct formula is rho_idO(gX)=g(rho_idO(X)). At the root current row the tuple action gives the usual interpretation isomorphism.

## 4. All-type language closure, including full quantification

Let t have finitely many root free parameters. At A their images are all S-pinned; individual parameters become 0. Thus two sections agreeing on S transport the complete environment equally. Evaluation of the whole term in the unchanged tail gives an S-pinned A-value a_t.

For fixed eta, outside the union of the finitely many exceptional index sets of its free parameters, the full B-environment at z_(eta,n) equals that at x_Teta. Hence the entire target value of t, including an abstraction, equals f_Teta a_t for all sufficiently large n. Target bound variables range over the complete original old domain. Agreement of the finitely many free parameters gives equality of the entire abstraction; there is no restriction to source images or infinite conjunction over possible bound values. Compatibility under p/e_U follows from old term naturality.

It remains to show that t's CURRENT root extension is finitely supported. The recursively defined domains are invariant under G, with the transport equivariance just displayed. Structural induction on semantic interpretation gives

    [[t]]_O(g rho)=g([[t]]_O(rho)),

with the corresponding arrow-relabeling interpretation at future coordinates. Application, equality and Boolean operations are equivariant. In the root quantifier/abstraction steps, G bijectively permutes the ENTIRE already defined root argument domain; in old rows it fixes the old domains and relabels only the entrance. Thus quantifiers and lambda terms are equivariant at all types.

Choose the union J of finite WHOLE-ENTITY supports of the free parameters. Every g∈G_J fixes the environment, so it preserves the current extension of t. That extension is therefore finitely supported. Together with the preceding tail and cofinite checks, t lies in the stipulated root domain.

This proves closure under the ordinary C language. The standard restricted-profile proof then verifies beta/eta, identity, Boolean and quantifier rules, and Logical Equivalence for H-theorem equivalences at every arrow/tuple coordinate. Optional assumptions are not used as Logical Equivalence premises. This is the same proof format as Kodsi's restricted-entrance soundness argument, now with the additional current-row support check.

## 5. Entailment order on free coordinates

Root X≤Y holds exactly when

    E_O(X)⊆E_O(Y), E_A(X)⊆E_A(Y),
    C_(eta,n)(X)⊆C_(eta,n)(Y) for every eta,n.

The forward direction reads the actual rows at id_O,y,z_(eta,n). For the reverse direction, choose n beyond the two finite exception sets in each eta. Inclusion of C_(eta,n) then gives R_eta(X)⊆R_eta(Y), so all derived x_T rows are included too. Hence the free-coordinate order is exactly whole-intension entailment.

Boolean finite operations use the corresponding free-coordinate operations. Complements preserve support because G permutes the full root argument domain; cofinite values are complemented. This is a Boolean algebra, but not the unrestricted product of powersets: its current rows must be supported and its replica rows cofinite.

## 6. Joins of EVERY admitted family

Fix a relational type tau and let Y^(tau t) be an admitted root property. Let F⊆D_tau(O) be its CURRENT extension. By definition F is finitely supported; choose a finite support J. Thus gF=F for every g∈G_J. This is a statement about the entire actual family, with no bound on its size and no uniform support bound on its individual members.

Form candidate free coordinates by EXTERNAL union:

    E_O^* = union_(X∈F) E_O(X),
    E_A^* = union_(X∈F) E_A(X),
    C_(eta,n)^* = union_(X∈F) C_(eta,n)(X).

The current extension E_O^* is G_J-invariant: g permutes F and sends each current extension to the current extension of gX. Hence it is finitely supported.

The replica sequence is CONSTANT outside J_eta={n:(eta,n)∈J}. Indeed for n,m outside J_eta choose g∈G_J with g_eta(n)=m. Old B-tuples are fixed by G, while replica equivariance and gF=F give

    union_(X∈F) C_(eta,m)(X)
      = union_(X∈F) C_(eta,n)(X).

This equality is of whole old extension TABLES, not just their truth at selected arguments. Thus C_(eta,n)^* has an eventual constant value, even though the family members' own exceptional indices may be unbounded. The arbitrary E_A^* is permitted. These free coordinates therefore define an admitted root entity L.

Every X∈F lies below L by section 5. If Z bounds every X∈F, each of its free coordinates contains the displayed unions, so section 5 gives L≤Z. Hence L is the native least upper bound of Y's actual instances.

The same argument with intersections gives greatest lower bounds directly; alternatively use Boolean complementation and the definable negated family. Empty families cause no problem. Therefore INTERNAL Boolean Completeness holds at EVERY relational type.

The step that fails for arbitrary external families is exact: their current instance-set F need not have finite support. For example the family of replica atoms at the even n is not invariant under any G_J, and its free-row union need not be eventually constant.

## 7. Strong atoms are admitted and dense at EVERY type

For tau=bar sigma t there are three admitted singleton-profile kinds:

(i) One current root tuple, no tail coordinates. The tuple has finite support by section 3, so its singleton current extension is allowed. Every future transport is bottom.

(ii) One tuple at y, no other free coordinates. E_A is that singleton, all C rows and all eventual R values are empty. Its A-transport is the identity-only singleton profile; every B-transport is the corresponding p-only singleton. These profiles are admitted with finite pins and have at most one arrow/tuple pair after every further transport.

(iii) One tuple at one z_(eta,n), no other free coordinates. This is one finite exception to the zero sequence, so its eventual values and A-component are zero. Its only nonzero target transport is an identity-only singleton at B, which becomes bottom under every nonidentity arrow from B.

Each decides every full target-domain relation or its complement, because every transport is bottom or a singleton arrow/tuple profile. Hence each is a STRONG atom with the native quantifier inside the box. There is no G-fixed restriction on old tuples; case (ii) works even for target tuples with trivial external symmetry stabilizer.

Every nonbottom root entity has a nonempty free coordinate: if all E_O,E_A,C coordinates vanish, the eventual R coordinates vanish as well. Choose a tuple in one nonempty coordinate and use the corresponding singleton above. By section 5 it lies below the entity. Thus all-type Strong Atomicity holds.

## 8. The separation

A is accessible through y and its entire tail submodel is unchanged. Its universal individual property has no inextensible coextension, by the established finite-pin graph(T) argument. Therefore necessary IC fails at O.

## 9. Explicit failures of BF_t and necessary Atomicity_t

Choose k outside S. Let q be the old A-proposition with false identity row and section truth q_fT iff T(k)=1. It is finitely pinned by {k}, but is not S-pinned: sections can agree on S and differ at k. In particular q is not the y-image of any root proposition.

Define root F^(tt) by universal current root extension, E_A(F)=D_t(A) minus {q}, and every replica table C_(eta,n)(F)=D_t(B). These constant tables are admitted and the universal current extension has empty support. For every root proposition P, F(P) is true at O; its y-value is true because yP differs from q; its x_T and z_(eta,n) values are true because the corresponding current B extensions of F are universal. Thus O satisfies forall P Box F(P). At y, however, the full old quantifier includes q and F(q) is false. Consequently O does not satisfy Box forall P F(P), and BF_t fails. This uses full target quantification and does not infer any transported witness from an identity-only singleton parameter.

For the boxed Atomicity failure, take the old A-proposition r with false identity row and every section row true. It is nonbottom. If 0<q'<=r, q' has a true section row and is pinned by some finite K subset N. Choose j outside K. Intersect q' with the finitely pinned section-coordinate proposition testing T(j)=1, and with its complement. Both intersections are nonbottom: from a section witnessing q', change only its j coordinate; the K-pinned q' remains true. Both are proper subpropositions of q'. Hence no atom lies below r at A. Since y reaches A, O fails necessary Atomicity_t, and therefore also necessary Strong Atomicity_t.

## Sources

- GPT-6 Astra, prompted by Daniel Kodsi, A finitely supported cofinite entrance, 30 October 2026 (unpaginated), Sections 1–9.
- Logical Maps, finite-support-sections-and-projection, definition and Inextensible Comprehension argument (unpaginated).
- Daniel Kodsi, Strong worlds do not control modal domains, 26 October 2026, Sections 2.2 and 4 (unpaginated), for the typed entrance-profile method.
- OpenAI Codex, prompted by Daniel Kodsi, Structural algebraic core, 22 October 2026, Section 2, evaluation-and-choice version, lines 92–112 (unpaginated); and GPT-6 Astra, prompted by Daniel Kodsi, Old/new Boolean completeness and rigidity separation, 22 October 2026, Full Boolean Completeness at E, lines 29–67 (unpaginated), for prior finite-support closure and supported-family joins.
