# Double-retract obstruction to finite rectangular unary rows

GPT-6 Astra, prompted by Daniel Kodsi, 30 October 2026.

Assume a **C-valid** restricted typed profile hierarchy with root v and target u,
individual domains D_e(v)=N and D_e(u)=N×N, diagonal h(n)=(n,n), and returns
j0(a,b)=a and j1(a,b)=b. The complete arrow lists are id_v,h at v and
id_u,j0,j1,k0,k1 at u, where k_i=h j_i, j_i h=id_v, j_i k_l=j_l,
k_i k_l=k_l and k_i h=h. Transport respects the ordinary C interpretation,
including whole-entity identity and application naturality.

Suppose every admitted root unary individual predicate has an h-row which is
a union of finitely many rectangles A_i×B_i, for arbitrary subsets A_i,B_i of N.
The finite number may depend on the predicate. Then current Well-Ordering at e
and Plenitude at input e, output et cannot both hold. Consequently full current
Functional Choice is impossible in this semantic class.

No condition is imposed on binary or higher rows, no common rank bound is assumed,
and no external full-profile admission is required. C-validity is essential:
syntactic term closure alone does not supply the rigidity theorems used below.
This is a construction obstruction, not a theorem that FC implies BC over C.

## 1. Inductive finiteness and the admitted operation

For F,G:et write Coext(F,G):=forall x^e(Fx <-> Gx). This is CURRENT
coextension, not whole-entity equality. H_x:=lambda z^e.z=x is the
individual haecceity, and 0_et is bottom.

For Y:(et)t define the admitted formula Ind(Y) by the conjunction
  Y(0_et);
  forall F,G [Coext(F,G) -> (YF <-> YG)];
  forall F,x [YF -> Y(F OR H_x)].
Define
  FinExt(F):=forall Y^(et)t [Ind(Y) -> YF].

Call this INDUCTIVE FINITENESS. No equivalence with external finiteness
is required or asserted. In particular its quantifier ranges over the
admitted classes, not every external subclass of D_et(v).

Define the admitted class
  Q(F):=exists R^et [Rigid(R) AND Coext(F,R)].
C proves Ind(Q): bottom is rigid; the assertion depends only on actual
coextension; and a rigid representative R of F yields the rigid
representative R OR H_x of F OR H_x. Here haecceities are rigid and
finite unions of rigid relations are rigid, both C facts. Thus the Y=Q
instance immediately proves

  C |- FinExt(F) -> exists R[ Rigid(R) AND Coext(F,R) ].         (Finite)

Coextensive weakly rigid relations are identical; rigid relations are
weakly rigid. Hence the witness in (Finite) is UNIQUE AS A WHOLE ENTITY.

For each externally finite current extension {s1,...,sm}, FinExt(F)
holds: in any admitted inductive class Y, finitely adjoin those
haecceities starting from bottom, and use coextension invariance to reach
F. This is a separate finite metatheoretic induction for each m. It
neither introduces an internal natural-number sort nor assumes an
admitted sequence enumerating all finite sets.

### Finite initial segments of a current well-order

Let L:eet witness current Well-Ordering_e. Use its strict part <_L.
Its well-order property quantifies over admitted unary predicates only.
Define n0 to be its least individual. After n0,...,n_{m-1} have been
chosen, the complement of their finite haecceity union is an admitted
predicate and is nonempty, since D_e(v)=N is externally infinite.
Let n_m be its L-least member. Totality and leastness show that the
strict predecessors of n_m are exactly n0,...,n_{m-1}.

Thus for every external finite m there is n_m whose admitted predicate
  F_n:=lambda x^e. x <_L n
has exactly m current instances. This does not claim that L is externally
well-founded, order-isomorphic to omega, or represented by an admitted
sequence m |-> n_m. Current L need not remain a well-order at u.

### The graph and its Plenitude representative

Define a single relation U of type e(et)t by

 U(n,R) iff
   [FinExt(F_n) AND Rigid(R) AND Coext(F_n,R)]
   OR [NOT FinExt(F_n) AND R=0_et].

This is an ordinary finite formula with parameter L. All abstractions,
quantifiers, and the rigid predicate have legitimate types. By (Finite) and
rigid-representative uniqueness it is CURRENTLY total and single-valued.
Plenitude_(e,et) therefore supplies G:e(et) with forall n U(n,Gn).

For every external finite m, the finite-prefix construction gives FinExt(F_(n_m)). The finite
union R_m:=H_(n0) OR ... OR H_(n_{m-1}) is rigid and coextensive with
F_(n_m), so uniqueness gives the WHOLE root identity

                         G(n_m)=R_m.                         (Prefix)

We have not promoted the unboxed Plenitude law into a universal boxed
law. Equation (Prefix), at each selected actual argument, can be transported
by ordinary profile naturality. This is exactly the needed strength.

## 2. An admitted unary diagnostic

For an individual predicate Y define

 ND_on(Y):=forall x^e,y^e.
           (Yx AND Yy AND x!=y) -> Box(x!=y).

Define the single admitted unary predicate at root

             P(n):=Rigid(G(n)) AND ND_on(G(n)).          (1)

It is an ordinary finite lambda formula with parameter G. Rigidity and
ND_on have the permitted quantifiers and types. There is no object-
language reference to j0,j1 or to the external coordinate labels. Those
maps enter only the semantic analysis below. An additional nonbottom
conjunct is unnecessary.

At the target, for n=(a,b), set Y=(h*G)(a,b) and let C be Y's current
extension, a subset of N x N. Naturality and j_i h=id_v give WHOLE
entity equalities

                    j0*Y=G(a),    j1*Y=G(b).           (2)

These hold even for new target arguments (a,b) outside h[N], because
they are application/transport equations. The current root law defining
G is subsequently applied only at the root individuals a and b. It is
not boxed or assumed universally correct at new target arguments.

## 3. Fixing a positive finite first-return rank forces the whole relation finite

Fix m>0 and put a=n_m. Suppose the target P-row holds at (n_m,b).
Then Y is rigid and satisfies ND_on at the target.

Persistence of Y implies that j0 carries every element of C into the
current extension of j0*Y=G(n_m), namely {n_0,...,n_(m-1)}. ND_on implies
that j0 is injective on C: two distinct current Y-instances cannot be
identified along the outgoing arrow j0. Hence C is externally finite,
with cardinality at most m. This is the ONLY inference of external
finiteness in the proof, and it uses a finite bound plus an injection.

Choose a finite list of the elements of C and let R_C be their finite
haecceity union at the target (bottom if C is empty). It is admitted,
rigid and currently coextensive with Y. Since Y is rigid, the native
coextensive-weakly-rigid uniqueness theorem implies

                             Y=R_C                    (3)

as WHOLE entities, not merely current coextension. Transporting this
finite union yields

       extension(j0*Y)=j0[C],  extension(j1*Y)=j1[C].  (4)

By (2), the first set has exactly m elements. With j0 injective on C,
this proves |C|=m. ND_on also makes j1 injective on C, so the second
set has exactly m elements. In particular extension(G(b)) is nonempty.

The root graph for G says either G(b)=bottom or it is rigid and coextensive
with F_b. Since m>0, the bottom branch is impossible. Therefore b has
exactly m strict predecessors under the current L.

This forces b=n_m. If b<n_m, then b is one of n_0,...,n_(m-1), and has
fewer than m predecessors. If n_m<b, all n_0,...,n_m are predecessors
of b, giving at least m+1. Current totality/antisymmetry of L leaves only
b=n_m. No global external well-foundedness assumption entered this step.

We have proved

             (h*P)(n_m,b) -> b=n_m, for every m>0.    (5)

## 4. The matching diagonal points really satisfy P

At (n_m,n_m)=h(n_m), the finite-prefix whole-entity identity and transport naturality give

 (h*G)(h(n_m))=h*(G(n_m))
             =H_{h(n_0)} OR ... OR H_{h(n_(m-1))}.

Here each h(n_i)=(n_i,n_i) is ONE target individual, so these are unary
haecceities of type et, not binary tuple-haecceities.

This finite union is rigid. Its current extension consists of the m
distinct diagonal points. Each of the five outgoing target maps is
injective on that finite set: j0,j1 both take (n_i,n_i) to n_i, and
k0,k1 fix each diagonal point. Thus ND_on holds. Consequently

                    (h*P)(n_m,n_m)                    (6)

for every m>0. Combining (5)-(6), the first-coordinate row at n_m is
EXACTLY the singleton {n_m}. The m=0 row is not needed, so the default
bottom branch creates no exception to this argument.

## 5. Contradiction with finite unary rectangularity

The admitted unary predicate P is supposed to have a target h-row
that is a union of some finite number q of rectangles A_i x B_i.
Equations (5)-(6) give infinitely many distinct singleton rows. A union
of q rectangles has at most 2^q distinct rows, already a contradiction.

Equivalently, avoid even an infinite-family formulation: choose the
externally finite indices m=1,...,q+1 using the finite construction in
Section 1. On their coordinate set, the P-row is a (q+1)-point diagonal.
Each rectangle can contain at most one of these diagonal points, since
two would force a forbidden cross point. Hence at least q+1 rectangles
are needed. This contradicts the chosen q. No admitted infinite sequence
or external union is required; every stage of this contradiction is finite.


## 6. Scope and sources

Full current Functional Choice supplies the two stated hypotheses through the
existing implications: FC gives Plenitude and Relational Choice; Plenitude gives
Actuality and hence Transversal; Transversal together with Relational Choice gives
Transversal Choice, hence Zorn and Well-Ordering. This uses the conjunction route,
not an implication from Relational Choice alone to Transversal Choice.

The proof identifies the exact positive finite-prefix rows of one admitted unary
predicate. It does not claim that its entire target row is the infinite diagonal.
It requires neither an admitted infinite enumeration nor external well-foundedness
of the current order. The standard full double-retraction model is unaffected:
its unary rows have no finite-rectangle restriction. No general double-retract
FC-to-BC theorem or alternative complete admission rule follows here.

- GPT-6 Astra, prompted by Daniel Kodsi, *Double retract: a unary finite-rectangle
  obstruction*, 30 October 2026, §§1–7 (unpaginated), for the unary diagnostic and
  finite first-return argument; *Double retract: an admitted uniform
  finite-rigidification rank obstruction*, same date, §§3–5, for the admitted
  FinExt graph and its Plenitude uniformization.
- OpenAI Codex, prompted by Daniel Kodsi, *Well-founded recursion and relational coding over Classicism*,
  22 October 2026, §§12.1 and 19.1 (unpaginated), for coextensive weak-rigidity
  uniqueness, finite rigid unions and unique finite rigidification. This prior
  finite-rigidification mechanism is used here with one current Plenitude witness.
- Background, Rigidity, for necessary weak rigidity, persistence and uniqueness;
  the double-retraction category has the same listed arrows as the existing full
  two-object double-retraction model, with the different individual action and
  restricted-row hypotheses explicitly stated above.
