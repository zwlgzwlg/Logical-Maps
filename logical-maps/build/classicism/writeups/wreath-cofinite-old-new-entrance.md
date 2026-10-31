# Wreath-supported cofinite entrance over old and new individuals

GPT-6 Astra, prompted by Daniel Kodsi, 30 October 2026.

This ZFC construction has Strong Atomicity and internal Boolean Completeness at every
relational type, necessary Atomicity and necessary Rigid Power at every relational type,
necessary Boolean Completeness at type t, and current propositional Barcan. Necessary Inextensible
Comprehension, necessary all-type Boolean Completeness, relational Barcan, and necessary
propositional Barcan fail. The exact witnesses and their modal scopes are given below.

The tail is the base-individual model [[symmetric-old-new-individuals]]. The entrance
uses a global old-point action and independent new-point actions on its replicas.
Completeness quantifies over admitted families, rather than arbitrary external subsets.
All types are the map's fixed relational types; write a relational type as bar-sigma t.
A table at that type is a subset of the full product of its already constructed argument
domains, with the empty tuple used at type t. Equality compares whole entities. A
relational signature, if present, is interpreted by top at every constant.

## 1. The unchanged tail and the modification lemma

Let E have individuals N and O have N disjoint union N', with the first summand called
old. Let i:E→O be inclusion. The arrows E→E are all injections, E→O all injections with
old range, O→E all injections, and O→O the disjoint classes G_O and K, where G_O consists
of sort-preserving permutations and K of old-range injections. At E use all permutations
as symmetries, and at O use G_O. The old relational domains consist of the symmetric
profiles pinned by a finite set of individuals, as in the cited tail construction.
Transport is precomposition of the outgoing-arrow rows, including typed argument
transport. Old outgoing arrows, domains, application and quantification remain fixed.

Here are the tail facts used to define the entrance. An E-entity a is determined by
\[
 A=a_{1_E},\qquad B=a_i,
\]
where, for some finite S⊆E, A is invariant under Fix_E(S) and B under Fix_O(iS).
Conversely every such pair is admitted. For h:E→E, extend h restricted to S to an E
permutation and take its image of A; for h:E→O extend the corresponding finite old
partial map to an O symmetry and take its image of B. Invariance makes these definitions
independent of the extensions. They prove the pair characterization and
\[
 a\le a'\quad\Longleftrightarrow\quad A\subseteq A'\ \hbox{and}\ B\subseteq B'.
\]
Every finite tuple of old entities has a finite pin; individual arguments pin themselves.

**Modification lemma.** Given a and any O-table C invariant under Fix_O(Q) for some
finite Q, define an O-profile b by
\[
 b_g=g[C]\quad(g\in G_O),\qquad
 b_h=a_{hi}\quad(h:O\to E\hbox{ or }h\in K).
\]
These rows are symmetric. They are pinned by iS union Q union {v}, where v is any new
individual. For O-target arrows the point v distinguishes G_O from K; within G_O use
Q, and within an exiting class use iS. E-target arrows are all exiting. Thus b belongs
to the actual old O-domain, not a larger raw-profile domain. Every further composite
following an exit is still exiting, so as whole entities
\[
 h_*b=(hi)_*a\quad(h\hbox{ exiting}).
\]
If C=B, covariance supplies the good rows too, hence b=i_*a. This default entity is
independent of the auxiliary marker v and is fixed by every new-point permutation.
Every singleton tuple table qualifies, using the union of the tuple entries' finite pins.

## 2. Entrance category and root domains

Add R, with no nonidentity arrow ending there. Its individuals are E=N. Add distinct
arrows y_u:R→E for every u:E→E, x_u:R→O for every u:E→O, and z_(n,g):R→O for every
n∈N and g∈G_O. The y/x arrows postcompose as the corresponding arrows out of E. Set
\[
 k z_{n,g}=z_{n,kg}\quad(k\in G_O),\qquad
 h z_{n,g}=y_{hgi}\ \hbox{or}\ x_{hgi}\quad(h\hbox{ exiting}),
\]
according to the target. Before the first exit, the G_O labels multiply; at the first
exit insert i and forget n. Exits cannot return to G_O, so both bracketings of every
composite give the same rule. This proves associativity. Individual maps are u on
y/x and gi on z. They respect composition. Distinct x_i and z_(n,1_O) may have the
same individual function; the category is not required to act faithfully on individuals.

A root entity X at a relational type has:

* a current table E_R;
* an admitted E-entity a, with pair (A,B);
* O-tables C_n, each with some finite old/new pin, such that C_n=B outside a finite set.

The current table is required to have the support specified in §3. Apply the modification
lemma to a and each C_n, obtaining b_n. Define whole-entity transports by
\[
 (y_u)_*X=u_*a,\qquad (x_u)_*X=u_*a,\qquad
 (z_{n,g})_*X=g_*b_n.
\]
The modification lemma gives precisely the first-exit equation; all other composition
laws follow from the tail's transport. Outside the finite exceptional set, b_n=i_*a
as whole entities. These rules define the root domain recursively on argument types.

## 3. Wreath action, finite supports and C closure

For s∈Sym(N), write shat for its action on old O-individuals, fixing new ones. Conjugate
old arrows by s and shat. Act on root individuals by s, on a by s_*a, on C_n by shat[C_n],
and on E_R by the recursively defined image action. Relabel the entrance arrows by
\[
 y_u\mapsto y_{sus^{-1}},\quad x_u\mapsto x_{\widehat s u s^{-1}},\quad
 z_{n,g}\mapsto z_{n,\widehat s g\widehat s^{-1}}.
\]
The equation shat i=is verifies composition and individual compatibility. Old symmetry
covariance identifies conjugation of a whole typed profile with its typed transport;
the modified O-entity is shat_*b_n. Thus transport is equivariant at every type, including
higher-type arguments. At the root identity the target action is the recursive root
action, not the trivial action.

Independently let pi permute N, the replica indices, and choose an arbitrary sequence
nu_n of permutations of N', extended by identity on old points. These fix the old tail,
root individuals and y/x arrows, and act by
\[
 z_{n,g}\mapsto z_{\pi n,g\nu_n^{-1}},\quad
 C'_{\pi n}=\nu_n[C_n],\quad a'=a.
\]
On E_R use the recursive image action. Since nu_n i=i, every exiting composite and
individual map is unchanged. The new auxiliary entity is nu_n*b_n, so
(g nu_n^{-1})_*(nu_n*b_n)=g_*b_n. Postcomposition by a good symmetry is multiplication
on the left and commutes with the inverse factor on the right. Composition of two local
actions (pi,nu), then (sigma,mu), has index sigma pi and local factor mu_(pi n) nu_n.
This also gives inverses. Global old actions commute with these local new actions.
There is no finite restriction on the sequence of new permutations.

A finite support is (P,J,(Q_n)), where P⊆N, J⊆N and each Q_n⊆N' for n∈J are finite.
Its stabilizer fixes P pointwise under s, fixes each n∈J under pi, and fixes Q_n pointwise
under nu_n. Outside J the new permutations are unrestricted. This is an actual subgroup;
unions and conjugates of finite supports again have this form. Require E_R to be fixed
by one such stabilizer, on the product of the already defined root argument domains.

Every whole root entity has finite support. Combine a pin of a, a support of E_R and
the finitely many pins of exceptional C_n. Include their old parts in P, their indices
in J and their new parts in Q_n. Default tables are fixed by every new permutation.
The resulting support fixes all the data. Root individuals have singleton old supports,
so every finite tuple has finite support. The actions preserve the recursively defined
domains and act bijectively on them.

To check term closure, fix a finite environment of free root parameters. Its value at
y_(1_E) is an admitted old E-entity a_t. Outside the finite union of those parameters'
exceptional replica sets, the whole O-environment is the i-image of the E-environment.
Old term naturality therefore makes the whole term value i_*a_t there. This assertion
also applies to an abstraction before any bound argument is selected: its quantified
arguments range over the full old target domain. At exceptional indices the ordinary
old term value has a finite pin, and naturality at exits gives exactly the rows required
by the modification lemma. Hence the resulting replica tables are admitted and eventually
equal to the table of i_*a_t.

At the root, the established interpretation automorphisms give term equivariance by
induction. Application, identity and Boolean clauses respect the actions; quantifiers
reindex the entire appropriate root or old domain, and modality reindexes arrows.
A finite support for the free environment therefore supports the current term table.
No common support for all quantified entities is imposed. This proves lambda and
full-quantifier closure. The usual restricted-profile action semantics then validates
the H laws, beta/eta and Logical Equivalence for H-theorem equivalences, establishing C.
No optional model principle is used to satisfy Logical Equivalence's theoremhood condition.

## 4. Exact order and internal Boolean Completeness

The free coordinates determining entailment at R are E_R, A and every C_n. Inclusion
in all these coordinates is necessary. It is sufficient: choose n outside the two
entities' finite exceptional sets to get B⊆B'; the old pair criterion gives a≤a', and
all the modification and symmetry rows preserve the inclusions. Thus it checks every
future row as well as the current one.

Let K be the current instance-set of an admitted family of entities of any fixed
relational type. Let (P,J,Q) support that family. Form the coordinate unions
\[
 E_R^*=\bigcup_{X\in K}E_R^X,\qquad A^*=\bigcup_{X\in K}A_X,\qquad
 D_n=\bigcup_{X\in K}C_n^X.
\]
A stabilizer element permutes K, so E_R^* retains its finite support. Global old
permutations fixing P make A^* invariant under Fix_E(P). Replica transpositions outside
J show D_n=D_m as whole tables whenever n,m are outside J; call this common table B^*.
An arbitrary new permutation acting only at such an n also fixes the support and permutes
K. Consequently B^* is invariant under every new-point permutation. Together with global
old Fix(P) invariance this is exactly Fix_O(iP) invariance. At an exceptional n∈J, D_n
is invariant under Fix_O(iP union Q_n). Therefore (A^*,B^*) is an admitted old E-pair,
and the D_n form an allowed eventually constant sequence. These data define a root entity.

Every member of K lies below it. Any admitted upper bound contains each coordinate union,
so the exact order criterion makes it the least upper bound. Complements give greatest
lower bounds, also for empty families. This is native internal Boolean Completeness at
all relational types. It does not assert that transport preserves these joins, or that
an arbitrary externally chosen family is admitted.

## 5. Strong Atomicity and necessary Atomicity

In the old tail, the proposition w_E=Hom(E,E) is strong: an E→E transport preserves it,
and an E→O transport gives Hom(O,E), which returns to w_E along O→E and remains itself
along either kind of O→O arrow. Each nonzero image is an atom of the full proposition
algebra. Similarly w_O=G_O stays itself along G_O and becomes bottom after an exit.
Both propositions are true at their own objects.

If w is a strong proposition and H_alpha the tuple haecceity, any nonzero w∧H_alpha
is a strong relation. At a successor, take any admitted target relation Z. The strong
proposition there decides the target proposition Z(transported alpha). Necessary equality
substitution gives entailment of Z or its complement for the relation at every further
coordinate. This places the universal quantifier over Z inside the box and uses the
full target domain, without requiring a source preimage for Z or alpha.

The three coordinate-atom forms at R are:

* one current root tuple, with all future data empty;
* one E tuple in A, with B, all C_n and E_R empty;
* one O tuple in a single C_m, with every other free coordinate empty.

They are admitted. In the first case use the root tuple's finite full-group support.
In the second use the old tuple's finite pin. In the third include m, the tuple's finite
old pin and its locally tagged finite new pin. Exact coordinate order makes each an
ordinary root atom, supplying the current decision clause. Its future images are,
respectively, zero; images of w_E∧H_alpha; or images of w_O∧H_beta, killed by every exit.
The preceding argument supplies every successor decision clause. They are therefore
native strong atoms. Every nonzero root entity has a nonempty free coordinate and
contains one of them. Strong Atomicity follows at every relational type.

For necessary Atomicity, it remains to check the unchanged old domains. Their finite-pin
proof can be stated as follows. For a pin M, the symmetric profiles pinned by M form a
complete atomic Boolean algebra. Its classes consist of pairs (g alpha,h') with h'
agreeing with gh on M. Let P pin the tuple alpha. Enlarge M so h(M) contains the part
of P reachable by arrows of h's kind and, when the source is O, M includes a new point.
Then this class is stable under every finite enlargement of M: the extra finite image
matching extends to a sort-preserving target symmetry fixing P and h(M). Thus the
class is an atom in the entire admitted domain. Given a nonzero entity, move an arrow
on finitely many fresh source points to cover that reachable part of P without changing
its existing pin; its class then supplies an atom below the entity. This works at every
relational type at both E and O. Together with root Strong Atomicity, and since these
are all target objects, it proves necessary all-type Atomicity at R.

## 6. Propositional completeness and current Barcan

An E-proposition has two bits (a,b), for the E-target and O-target arrow classes. An
O-proposition has three bits (a,c,b), for Hom(O,E), G_O and K. These describe the whole
four- and eight-element proposition domains. Hence BC_t holds at both old objects;
root BC includes t, yielding necessary BC_t.

A root proposition has a current bit r, an E bit a, and replica bits c_n eventually equal
to b. Every such eventually constant sequence is admitted. Its transports are
\[
 y_u:(a,b),\qquad x_u:(a,b,b),\qquad z_{n,g}:(a,c_n,b).
\]
Thus every y_u and every fixed z_(n,g) is onto the entire target proposition domain.
For z, prescribe its exceptional bit at n and b elsewhere. The x_u arrows are not onto.

Fix any admitted root F^(tt) and suppose every root proposition p necessarily has F.
Reflexivity makes F universal currently. Surjectivity makes it universal over the full
old proposition domains at every y and z arrow. In particular, every replica-current
table C_n^F is all D_t(O). Choose n outside the finite exceptional set of this one F.
Then its eventual table B_F is also all D_t(O). The old pair criterion says each x_u row
is a symmetry image of B_F, so is universal too. All root successors therefore satisfy
forall p F(p), proving current BF_t. The exceptional set belongs to F alone; this does
not choose a common exception bound for the infinitely many possible bound propositions.

## 7. Failures inherited from the unchanged tail

**Necessary Inextensible Comprehension fails at et.** At E suppose an inextensible Y
were currently coextensive with the universal individual property. If S pins Y, extend
any E→E injection restricted to S to a permutation. Symmetry and pinning make Y universal
at every E-target row. The admitted property D with rows all individuals at E and old
individuals at O necessarily holds of each E individual. Inextensibility forces Y≤D,
so Y_i has no new member v. At O each current Y_i-member is necessarily different from
v because all individual arrows are injective. The predicate lambda x.x≠v is therefore
a weak-inextensibility test, but after any m:O→E the universal row Y_(mi) contains m(v),
which the test omits. This contradicts hereditary inextensibility. The accessible E
world has no such coextension; necessary IC fails at R.

**Necessary Boolean Completeness fails at et.** At O, the admitted family of haecceities
H_n of old individuals is defined using D. Suppose L with finite pin S were its least
upper bound. Choose old n and new v outside S and an injection h:O→E. Choose h' agreeing
with h on S and with h'(n)=h(v). Since H_n≤L, the row L_(h') contains h(v); pinning makes
L_h contain it too. Yet lambda x.x≠v is an admitted upper bound for every old H_n and
its h-row omits h(v). This contradicts leastness. O is accessible from R, so necessary
all-type BC fails. The family used here is internal and admitted.

**Necessary propositional Barcan fails.** At E let q=G_O=(0,1,0), an O-proposition
outside every E→O image (a,b,b). The E-pair consisting of all D_t(E) and D_t(O) minus
{q} is admitted with empty pin, since target symmetries fix all proposition blocks.
Every E-proposition necessarily has this property, but the full O quantifier includes
q and falsifies its boxed universal. Thus BF_t fails at accessible E. The record need
not add this redundant negative input: it is also derived from its other verdicts.

## 8. Relational Barcan fails already at et

For each new q∈O let H_q be its whole individual haecceity. The set
NewHaec={H_q:q new} is invariant under every sort-preserving symmetry. Its complement
is therefore an admitted empty-old-pin section table at type (et)t.

No root et-entity X can transport to H_q. At x_u its current extension is invariant
under all permutations of new individuals and cannot equal {q}. At z_(n,g), the image
is g_*b_n. Choose another new r and any h:O→E, and put h'=h composed with the transposition
of q,r. Since gi has old range, h'gi=hgi. The exit rule gives equal rows for g_*b_n at
h and h'. But H_q has rows {h(q)} and {h(r)}, which differ by injectivity. Thus even a
good replica with current extension {q} cannot be the whole haecceity H_q.

Define F^( (et)t ) at R with universal current extension, old E-pair
\[
 A=D_{et}(E),\qquad B=D_{et}(O)\setminus\mathrm{NewHaec},
\]
and every replica table equal to B. The data have empty support under the actual full
wreath action; B is fixed by all old/new symmetries. Its E-target rows are universal
and its O-target rows exclude exactly NewHaec. Every root et-entity necessarily satisfies
F by the no-image argument, while at x_i a new H_q belongs to the full target domain and
fails F. This is BF_et failure, hence failure of the relational Barcan schema.

Separately, BF_e fails using the root individual property with universal current row,
E-pair (all E, old O), and constant old-O replica tables. Every root individual transports
to an old individual at O, whereas the full O quantifier includes new ones. No inference
from relational BF to the individual instance is used.

## 9. Necessary Rigid Power

For a set D of tuples at an object V, write H_V(D) for the profile with row h[D] at
each arrow h from V. This notation does not assert admission. If that profile is
admitted, it is rigid: at any successor its later rows are the exact images of its
current extension. Persistence follows, and any admitted predicate necessarily
containing each current instance contains every later instance. This verifies weak
inextensibility at every successor against the full target domains.

The goal is the native all-type statement that, for each rigid F, the admitted property
\[
 P=\lambda X\, .\,\operatorname{Rigid}(X)\land X\le F
\]
is rigid. The quantifier over X includes every admitted relation of F's type at each
target, rather than only source images.

### 9.1. Exact tail facts

The `rigid-power` argument of [[symmetric-old-new-individuals]], parts (a)–(c), proves:

* At E and O, a rigid relation with current extension D is H_V(D).
* At E, a rigid relation's current tuples share one finite pointwise pin S. Consequently
  H_E(D') is admitted for every subset D' of its current extension.
* Every E-originating arrow acts injectively on every type; in particular ri:E→E is
  injective on tuples for every exit r:O→E.
* Rigid Power holds at both E and O, for arbitrary admitted rigid relations there.

The pointwise pin assertion is specific to E. Its proof uses the E pair description
and hereditary inextensibility. A test whose E table is universal and whose O table
consists of tuples with an old-only finite pin first puts the rigid carrier's O image
inside that old-pinned part. If a current tuple's least permutation support contains
n outside the carrier's pin S, choose a new point b and an exit r with rb=n and ri
fixing S. At O test weak inextensibility by the profile whose h-row is the union of
h'[F_i] over same-target h' agreeing with h on a finite Q containing iS and b. This
profile is Q-pinned and symmetric. It expresses the tuple as r'beta with beta old-pinned
and r'b=n, so that tuple has a support omitting n, a contradiction. Finite partial-map
extension then makes S a whole-tuple pin. Exact images of subsets are S-pinned and
admitted; rigidity and current coextension identify the original relation with its
exact-image profile.

At O the corresponding fact is weaker. A bijective exit j:O→E gives a common pin for
the tuples in jF, so all exiting maps act on F's current tuples through a fixed finite
set, since every exit factors through j. Combine that finite exit-control set with F's
setwise symmetry support and a new marker separating good and exiting arrows. This
admits H_O(F_current), which equals F by rigidity and current coextension. It need not
make every original O tuple pointwise fixed by one common support. These are the precise
tail facts used below, including for the empty argument tuple.

### 9.2. Every rigid root carrier is an exact-image profile

Write y=y_(1_E) and z_n=z_(n,1_O). Let F be rigid at R with current tuple set K and a
finite wreath support (P,J,Q). Equivariance gives finite setwise supports for its images:
yK is invariant under Fix_E(P), and z_nK under Fix_O(iP union Q_n), taking Q_n empty
outside J. For the latter use global old permutations fixing P and an independent
new permutation at n, with replica permutation identity. These are setwise assertions,
not common pointwise pins for the tuples.

Fix n. The test with current row K, universal E component, and universal replica tables
except the single table z_nK at n is admitted by the modification lemma. It necessarily
contains every current K-member. Weak inextensibility gives F_(z_n)⊆z_nK; persistence
gives the reverse inclusion. Covariance then gives equality at every z_(n,g).

For y use the test with current row K, E pair (yK, universal O table), and universal
replica tables. The E pair is admitted with old pin P. This test necessarily contains
K, including at arbitrary E-target injections u: for alpha∈yK, extend u on P together
with a finite whole pin of alpha to one E permutation s. The test's u-row is s[yK],
and u(alpha)=s(alpha), so it contains u(alpha). This extends only a finite restriction
of u. All O-target rows are universal; E-target exits from good replicas reduce to the
same check. Inextensibility and persistence now give F_y=yK.

The whole old E component a=y_*F is rigid by heredity, so §9.1 makes it H_E(yK).
Consequently every cone row is the corresponding image of K. Together with the good
rows and the identity row already proved, this establishes F=H_R(K).

### 9.3. One cofinite bound works pointwise on the entire carrier

Admission of this one F supplies a finite set N_F outside which b_n=i_*a as whole
entities. Since F is now an exact-image profile, their current rows give
\[
 z_nK=i(yK)\qquad(n\notin N_F).
\]
Fix such n and q∈K. Choose q'∈K with z_nq=i(yq'). For any old exit r:O→E, the category
law gives
\[
 (ri)(yq)=r(z_nq)=(ri)(yq').
\]
Injectivity of the E→E transport ri on tuples gives yq=yq'. Therefore
\[
 z_nq=i(yq)\quad\hbox{for every }q\in K\hbox{ and every }n\notin N_F.
\]
The exception set was chosen before q. There is no intersection of infinitely many
exception sets and no assumption that r is injective on arbitrary O higher-type entities.

### 9.4. Supported subsets have admitted exact-image profiles

Let K'⊆K be finitely supported under the full root wreath action. The common E pin of
yK admits a'=H_E(yK'). Each z_nK' has a finite O setwise support by §9.2 applied to K'.
Use it as a current modification table, with E component a', obtaining an admitted b'_n.
For every exiting h the category identity yields
\[
 h[z_nK']=(hi)[yK'].
\]
These are exactly the prescribed exit rows of b'_n. Its good rows are the symmetry
images of z_nK', so b'_n=H_O(z_nK') as a whole entity. This proves admission without
assuming arbitrary subsets of an O carrier are admitted.

For n outside N_F, §9.3 gives z_nK'=i(yK') pointwise, so b'_n=i_*a' as whole entities.
Together with the supported current row K', these are allowed root data. They admit
H_R(K'), which is rigid and lies below F.

### 9.5. Every admitted target rigid subrelation lifts

Let h be any nonidentity root arrow and let Z be an arbitrary admitted target rigid
subrelation of h_*F. By the tail characterization, Z=H_V(D), where D is its current
extension and D⊆hK. Define
\[
 K'=\{q\in K:hq\in D\}.
\]
Then hK'=D. We prove support of K' without treating h as a finitely supported parameter.

For a cone arrow h=y_u or x_u, enlarge a support of K by the common pointwise E pin S
of yK. A stabilizer action gamma has global old part s fixing S; its local part leaves
y-images unchanged. Thus y(gamma q)=s(yq)=yq for every q∈K, so h(gamma q)=hq. This
supports K' for any such D and any allowed u, even an injection whose description or
moved set is infinite.

For a good arrow h=z_(n,g), put D_0=g^{-1}[D]. Admission of Z and the old symmetry action
give a finite old/new setwise pin Q for D_0. Enlarge a support of K by n, the old part
of Q globally and its new part locally at n. A stabilizer fixes n and acts on z_nq by
an O symmetry fixing Q. It therefore preserves membership in D_0 and supports K'.
This support may depend on the particular target relation, as full target quantification
permits; no common pointwise O support is claimed.

Section 9.4 now supplies X=H_R(K'), and naturality of exact images gives
\[
 h_*X=H_V(hK')=H_V(D)=Z.
\]
These cases exhaust the nonidentity root arrows, so every admitted target rigid
subrelation has a rigid root subrelation lift.

### 9.6. The power property and its necessary scope

The displayed P is an admitted C term. Let L be its current extension, the admitted
rigid root subrelations of F. At each target its extension consists of all admitted
rigid subrelations of h_*F. Transport of a member of L remains rigid and supported
below h_*F, giving hL⊆P_h. Section 9.5 gives the reverse inclusion for every target
member. Hence P_h=hL at every arrow, including the identity by definition. P is an
already admitted exact-image profile and is therefore rigid by the opening criterion.

This proves root Rigid Power at every relational type, including t. The unchanged tail
has Rigid Power at E and O for arbitrary relations there, not merely images of root
relations. These are all accessible objects. Thus R satisfies necessary all-type Rigid
Power; no necessitation of an optional current assumption has been used.

The support restrictions are essential. At R the current-only singleton predicates
indexed by all root individuals form a rigid carrier, but its even-indexed external
subfamily is not supported. At O, the good-block singleton predicates indexed by all
new individuals form a rigid carrier with no common pointwise pin for its members.
The proof uses supported inverse images of admitted target subrelations, and requires
neither of those stronger subset or support claims.

## Sources

The construction and arguments are from *Wreath-supported upgrade of the variable-frame
old/new entrance*, §§1–8; *Variable-frame orbit entrance into the old/new tail*, §§1–2,
4–7; and *Further verdicts on the same wreath-supported entrance*, §§1–5, all by GPT-6
Astra, prompted by Daniel Kodsi, 30 October 2026, unpaginated.

The unchanged tail, pair classification, atomicity and old counterexamples are in
[[symmetric-old-new-individuals]] and its writeup. The original model is by Claude Fable
5.1, prompted by Cian Dorr, 6 October 2026; the corrected completeness argument is by
GPT-6 Astra, prompted by Daniel Kodsi, 22 October 2026, recorded 24 October 2026. The
symmetric finitely pinned semantics is Cian Dorr's *Boolean Completeness does not imply
Rigid Comprehension*, draft of 30 July 2026, Definitions 15–18, p.8, and Proposition20.

The additional Rigid Power argument is *Rigid Power gate for the wreath-supported old/new
entrance*, §§1–7, by GPT-6 Astra, prompted by Daniel Kodsi, 30 October 2026, unpaginated.
The E uniform-pin and E/O exact-image lemmas and old-tail Rigid Power are the native
`rigid-power` argument of [[symmetric-old-new-individuals]], parts (a)–(c), dated
11 October 2026, by GPT-6 Astra at Cian Dorr's request, checked and recorded by Claude
Opus 5.5. The added entrance lifting proof uses these specific earlier lemmas.

## Paper references

- **Background: Boolean Completeness does not imply Rigid Comprehension.** Dorr, Cian. Boolean Completeness does not imply Rigid Comprehension. Unpublished draft in progress, 30 July 2026, 27 pages. All page, proposition and lemma locators for this source refer to that draft. Parts of the draft were drafted with AI assistance; its mathematical claims are attributed to the author. — Definitions 15–18, p. 8; Proposition 20
