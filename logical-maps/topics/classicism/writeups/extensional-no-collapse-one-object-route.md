# One-object nested-capacity construction for Extensional No Collapse

## 1. Exact claim, scope, and relationship to the companion proof

The model has one object and satisfies the native current Extensional No Collapse sentence

```text
exists F^((tt)t) [ F(Box) and forall X^tt
  ((FX -> F(hat X)) and
   (FX -> not forall p^t (Xp iff (hat X)p))) ].             (ENC)
```

Here `hat X = lambda p. exists q. q and Box(not X(not q) -> p)`, and `O_0=Box`, `O_(n+1)=hat O_n`. The quantifiers in ENC range over the full admitted global type domains. We construct one admitted F and, for each member O_n, a currently separating proposition at the SAME object. We do not infer ENC merely from different models at arbitrarily late depths or from whole-operator inequalities.

This presentation uses the nested-capacity mechanism of the finite-depth and product constructions. The general finite-depth capacity induction and the full finite-pin C-model theorem are used below.

The new model's higher domains are rebuilt globally. They are NOT asserted to be products of component higher domains, nor restrictions of the old two-object domains. Only the raw individual return game can be restricted to self-arrows without change; section 4 proves that statement.

## 2. The one-object category and its complete typed semantics

For each positive external integer d use the accepted countable leaf structure B_d. Its nested equivalences E_0,...,E_(d-1) have the following node types. A level-zero node U_0(m) has m leaves, where m is a positive integer or countable infinity. For j>=1, a node U_j(m), with m a nonnegative integer or infinity, has m infinite-parameter children of level j-1 and countably infinitely many children of each allowed finite-parameter type at that level. B_d has infinitely many top nodes of each finite parameter and infinitely many infinite-parameter top nodes. All nodes are nonempty. Write lambda(v) for the parameter of a node v.

Let

```text
Z = disjoint union_(d>=1) ({d} x B_d).
```

The category has just Z, with monoid

```text
M = product_(d>=1) End(B_d),
```

where each factor consists of ALL total leaf functions preserving all its nested equivalences. Thus every map preserves the external label d. Identities and composition are coordinatewise. This is a set-sized faithful concrete category in external ZFC. Its labels, equivalences, and node parameters constrain the allowed maps; none is being assumed to be an object-language constant or a rigid named predicate.

Use the full finite-subset pin ideal. At each relational type, admit all profiles whose row at h in M is an arbitrary subset of the appropriate product of the WHOLE global argument domains, subject only to having a finite individual pin S: rows agree whenever h and h' agree on S. There is no additional symmetry covariance or landing restriction. Transport is precomposition, `(hF)_k=F_(kh)`, and an individual z transports to h(z). Current truth is the row at the identity.

This is the same full finite-pin C construction used in the accepted depth theorem. Type recursion is well founded: a profile's row arguments have lower structural types. All domains are sets. Transport preserves admission, since h[S] pins hF if S pins F. Finite tuples of parameters have the union of their pins. When h and h' agree on that union, their transported parameters agree as WHOLE entities: every further k has kh and kh' agreeing on each original pin. Lambda rows therefore agree for every tuple in the full target argument domains. Quantifiers use these entire global domains, and modalities use all further maps; neither is restricted to a transport image or a single component. This gives the standard closure proof, beta/eta, and H-theorem-restricted Logical Equivalence.

Literal current identity is retained; for example an admitted constant-row singleton predicate distinguishes different whole current entities. No external-parameter test below replaces identity by current coextension. These observations check that the inherited C theorem applies to this monoid, not only to the original two-object categories.

## 3. Return recursion in the rebuilt global model

For finite S subset Z, let `U(S)={h in M: h fixes S pointwise}`. This is an admitted S-pinned true proposition. Every admitted true proposition q contains U(S) for some finite pin S, because q has the same truth row as the identity at maps fixing S.

Define raw subsets of M by

```text
R_0(S) = M;
h in R_(n+1)(S) iff
  for every finite T subset Z there exists k in M such that
  kh fixes S pointwise and k in R_n(T).                    (R)
```

The accepted hat/return calculation applies to the full global profile model and yields, for every admitted p,

```text
O_n(p) is currently true iff some finite S has R_n(S) subset p.   (H)
```

For completeness, the inductive hat step replaces a true q by its contained U(S), using monotonicity of the stage-n dual `D_n=not O_n not`. At h, `D_n(hU(S))` means every finite T has an R_n(T) map k on which hU(S) is true. That truth is exactly kh fixing S. This is (R). The stage-n monotonicity follows from (H). Thus the recurrence covers arbitrary admitted target propositions, not merely the special predicates constructed later.

Three elementary facts will be used:

1. The identity belongs to R_n(S) for all n and S: use identity as the return and induction for every challenge.
2. R_n(empty)=M for every n: any h has the identity return for every challenge; the fixing requirement is empty.
3. Enlarging the pin decreases R_n. This follows directly from (R).

The second fact is particular to this one-object situation. In the earlier two-object/product categories, an empty pin can still restrict cross-object directions; that restriction is not being discarded there.

## 4. Self-arrow restriction and exact component factorization

Let `R_n^d(S_d)` be the game in the ONE-object category End(B_d). For a self-arrow of B_d its membership agrees, at every n, with membership in the accepted two-object A_d/B_d return game. Proof: the claim is immediate at n=0. For h:B_d->B_d, every return appearing in (R) is again k:B_d->B_d, with challenges T subset B_d. Apply the induction hypothesis to k. No cross-arrow or other object can enter this membership test. This is a statement about raw games, not a blanket preservation claim about higher domains or formulas when deleting objects.

For a finite global pin S, let S_d be its intersection with coordinate d. Then for every n and h in M,

```text
h in R_n^Z(S) iff for every d, h_d in R_n^d(S_d).          (F)
```

At n=0 this is the definition of M. For the forward induction at n+1, fix d and challenge h with any finite T supported only in d. A global return k projects to a component return k_d in R_n^d(T_d), by the induction hypothesis, and k_d h_d fixes S_d. This holds for every component challenge.

For the reverse induction, let finite global T be given. Only finitely many coordinates meet S UNION T. In each of those coordinates the assumed component R_(n+1) membership supplies a return k_d fixing S_d after h_d and lying in R_n^d(T_d). In every other coordinate use the identity. There S_d=T_d=empty, so it meets both requirements. The tuple k is an allowed total global map; the induction hypothesis puts it in R_n^Z(T), and kh fixes S. This proves (F). Only finitely many nonidentity choices are required in this one-object proof.

In particular, with S wholly inside coordinate d, all other factors impose no restriction because R_n^e(empty)=End(B_e). This permits a component-supported game set to be a finite-pinned global proposition when its finite capacity table has that property.

## 5. The exact capacity table and predicate admission

For h in End(B_d) and finite S_d, let P(h,S_d) mean injection on S_d and reflection of all d equivalences there. The accepted exact table, now valid for this one-object game by section 4, is

```text
R_1:            P;
R_(2j+2):      P, parameter equality at anchored levels <j,
                   source parameter >= target parameter at level j;
R_(2j+3):      P, parameter equality at anchored levels <=j,
```

for 0<=j<d. A node is anchored when it meets the pin. Target nodes are determined by the images of their pinned leaves. The inequalities have the displayed orientation; the return's inequality is reversed relative to the original anchored pair.

For each n choose a finite S_0 in a single coordinate as specified below and set

```text
p_n(h) iff h in R_(n+1)^Z(S_0).                           (P_n)
```

This raw game set is admitted, for the following specific reason—not because arbitrary game sets are automatically admitted. At n=0 choose S_0={a,b} within one level-zero block. R_1 tests only their images and their finite equivalence pattern. At every later n choose S_0={a}. Then P is automatic and the table's remaining conditions depend only on the ancestor parameters of h(a), together with the fixed parameters of a. By (F), other coordinates impose no condition. Therefore p_n is pinned by S_0. These external capacity tests are legitimate semantic profiles; they need not be named in the language or encoded as internal cardinal arithmetic.

By (H) and definition (P_n), `O_(n+1)(p_n)` is currently true, witnessed by S_0. It remains to defeat every finite candidate pin for O_n.

## 6. Adjacent CURRENT separation at every finite n

### Initial step n=0

Take distinct a,b in a size-two level-zero block of B_1. Because their source equivalence pattern agrees at all levels, p_0 is just the test h(a)!=h(b). Collapse the B_1 coordinate constantly to one point and use identity on all other coordinates. This is an allowed total map and falsifies p_0. Since R_0(S)=M for every S, O_0(p_0) is false, whereas O_1(p_0) is true.

### Odd step n=2j+1

Take d=j+1 and choose a in a top node V=U_j(m) of B_d with fixed finite m>=1. Let S_0={a}. At this depth the active level j is the top. The predicate p_n requires preservation of all lower ancestor parameters of a and `lambda(hV)<=m`.

Let T be ANY finite global pin. Enlarge its d-coordinate to `T'=T_d union {a}`. Assign V to a fresh top node V'=U_j(m+1). We construct a finite prescription on T' that is injective, reflects every equivalence, and preserves all node parameters below j.

If j=0, there are at most m leaves of T' in V, so they inject into the m+1 leaves of V'. If j>0, at most m infinite-parameter children of V meet T'. Assign those to distinct infinite-parameter children of V'; it has m+1 of them. Every touched finite-parameter child goes to a distinct child of its exact finite type; V' has infinitely many of each. Below these matched child types, recursively match each finite trace with its exact node types, then inject its leaves. Equal finite child capacities and the infinite finite-type reservoirs make these allocations possible.

For every other top node meeting T', choose a distinct fresh top node of the SAME parameter and embed its finite trace with all lower types matched. B_d has infinitely many copies of every needed finite or infinite top type, so choices avoid V' and one another. This makes the combined finite prescription reflect all equivalences on T'. Extend it to a total preserving endomorphism: for each partially assigned source node, send its remaining children constantly into a child of its assigned target; proceed downwards, and send unassigned top nodes arbitrarily. No reflection outside T' is required.

The resulting h_d belongs to R_(2j+1)^d(T'), hence to R_(2j+1)^d(T_d). But it sends V to parameter m+1, so it fails R_(2j+2)^d({a}). Use identities at all other coordinates. By (F), the global h is in R_n^Z(T) and falsifies p_n. Since T was arbitrary, O_n(p_n) is false.

### Even step n=2j+2

Again take d=j+1, but choose a in an infinite-parameter top node V=U_j(infinity). The predicate p_n requires equality of all ancestor parameters through j, in particular an infinite-parameter image of V.

For arbitrary finite global T put `T'=T_d union {a}`. Choose a fresh top target V'=U_j(M) of finite parameter M. At j=0 choose positive M at least the number of leaves of T' in V. At j>0 choose M at least the number of infinite-parameter children of V touched by T'; zero is allowed when that number is zero. Such U_j(0) is nonempty when j>0. Assign touched infinite children injectively to the M infinite-child slots and touched finite children to distinct children of their exact type. Recursively match all lower parameters and inject the finite leaves, exactly as in the odd construction.

Send every other top node touched by T' into a distinct fresh copy of its own parameter type. Extend the finite prescription to a TOTAL endomorphism by the same node-by-node constant completion. On T' it is P, matches all parameters below j, and satisfies source>=target at j: the special pair has infinity>=M and the other pairs have equality. Thus h_d belongs to R_(2j+2)^d(T'). Its special top parameter changes from infinity to finite, so it fails R_(2j+3)^d({a}). Identities in all other coordinates give a global h in R_n^Z(T) falsifying p_n.

The approximation M is chosen after the arbitrary finite pin T. No injection of the entire infinite-parameter node into a finite-parameter node is asserted; the allowed total map may collapse outside the finite trace. This is exactly the flexibility used in the accepted capacity induction.

Together the cases establish, at Z, for EVERY external n>=0,

```text
not O_n(p_n),             O_(n+1)(p_n),                   (S)
```

with p_n an admitted global proposition. No common p for all n is claimed or needed.

## 7. One admitted family and the native full quantifiers

Let Q be the external countable set of WHOLE global operator entities `{O_n^Z : n in N}`. These entities are already in D_tt(Z), as denotations of closed logical terms. Their transport under any endomorphism fixes them: closed-term naturality has the same source and target object. Equivalently, the empty-environment closure proof gives each O_n an empty pin.

Define F of type (tt)t to have the SAME row Q at every h in M. This is a legitimate subset of D_tt(Z) at every row and is empty-pinned. Thus F is admitted at the next type stage; no recursive domain definition, internal enumeration, or internal natural-number object is being postulated. Its transported profile is again F.

At the identity, F contains Box. Every current X satisfying FX is literally some O_n, and by congruence and the definition of the iterates its hat is O_(n+1), again a member. For that X, the actual admitted input p_n from (S) witnesses failure of `forall p (Xp iff (hat X)p)`. This checks the universal X-clause over the full global D_tt and the universal p-clause over the full global D_t. There are no unintended additional members of F and no limitation to transported component inputs.

Therefore F witnesses the exact ENC sentence at Z, subject to the pending independent review of this working proof. In fact there is only one target object, the closed iterates transport to themselves, and the same family clauses are verified there. The argument also supports necessary ENC in this model by direct semantic evaluation, without necessitating an optional assumption. Ordinary No Collapse follows from the stronger current noncoextension.

## 8. Sources

The semantic framework is Bacon and Dorr, *Classicism* (2024; draft of 16 May 2023), Appendix D, D.1–D.4. The capacity induction is the finite-depth construction in the [finite-depth and fanout note](no-collapse-finite-depth-and-fanout.md). The one-object presentation retains that mechanism while rebuilding the entire typed hierarchy; it does not rely on preservation of formulas under arbitrary restriction to a subcategory.
