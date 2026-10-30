# Nominal cofinite entrance: double-retraction tail

GPT-6 Astra, prompted by Daniel Kodsi, 30 October 2026. ZFC metatheory;
the fixed logic C and its relational types.

This model separates **Self-Atomicity from necessary Strong Actuality**,
even in the presence of necessary all-type Boolean Completeness,
Atomicity and Inextensible Comprehension:

\[
\mathrm{SelfAtomicity}_{\rm all}
+\Box\mathrm{BC}_{\rm all}
+\Box\mathrm{Atomicity}_{\rm all}
+\Box\mathrm{IC}_{\rm all}
+\neg\Box\mathrm{StrongActuality}.
\]

The mechanism is a self-atom that becomes divisible at a future point
where it has no instances. Its self-atom condition survives, while its
strongness fails. Cofinite replicas ensure that every nonzero relation
still contains a self-atom. Supported families have joins, so the root
retains internal completeness.

The construction combines the double-retraction tail with a nominal
cofinite entrance to obtain these simultaneous verdicts.

## 1. Unchanged finite full tail

Use the category of the existing [[full-two-object-double-retraction]] model: objects A,B; arrows h:A->B and j_1,j_2:B->A; and e_i=h j_i:B->B. Its equations are

    j_i h=1_A,     e_i h=h,
    e_k e_i=e_i,   j_k e_i=j_i.

The arrows out of A are 1_A,h; those out of B are 1_B,j_1,j_2,e_1,e_2. In particular j_1 and j_2 remain DISTINCT arrows, even though the constant singleton individual functor sends them to the same individual function. General intensional action semantics is intended; faithfulness on individual maps is not claimed.

Keep the full typed domains at both old objects and the constant singleton individual functor. At a relational type tau=bar-sigma t, an old entity is an arbitrary table of argument tuples at each outgoing arrow. Transport is profile reindexing by postcomposition. These are exactly the source's full action domains. Every fixed old typed domain is finite: there are finitely many arrows and, recursively, finitely many argument tuples at each fixed type. Neither old quantifiers nor old domains are restricted later.

Write the two rows of a in D_A^tau as

    A_0 = a_(1_A),       A_1 = a_h.

For any arbitrary B-current table C, define b(a,C) in D_B^tau by

    b_(1_B)=C,
    b_(j_1)=b_(j_2)=A_0,
    b_(e_1)=b_(e_2)=A_1.

Fullness admits this entity. Direct calculation at ALL its outgoing coordinates gives the whole-entity identities

    j_i b(a,C)=a,          e_i b(a,C)=h a.

For example the two rows of j_i b are b_(j_i)=A_0 and b_(h j_i)=b_(e_i)=A_1. The rows of e_i b are A_1 at identity and each e_k, and A_0 at each j_k, which are precisely the rows of h a. If C=A_1, then b(a,C)=h a as a WHOLE entity. These calculations apply at every relational type, not just t.

## 2. The entrance category and composition

Add a root R with no incoming arrows except 1_R. Its nonidentity outgoing arrows are

    y:R->A,        x:R->B,        z_n:R->B  (n in N).

Set

    h y=x,
    j_i x=y,       e_i x=x,
    j_i z_n=y,     e_i z_n=x.

All z_n are distinct from one another and from x. In particular, z_n is NOT defined as h y_n for some new y_n. It is a fresh arrow whose composites after a return are x. Therefore j_i h=1_A is respected: j_i(hy)=j_i x=y.

Associativity is checked by the displayed tail relations. For example

    h(j_i z_n)=hy=x=(h j_i)z_n,
    j_k(e_i z_n)=j_k x=y=(j_k e_i)z_n,
    e_k(e_i z_n)=e_k x=x=(e_k e_i)z_n.

The cases beginning with x or y use the same equations. The replica index appears only at a fresh z_n before its first nonidentity old postcomposition; that postcomposition always lands in the y/x cone, where all subsequent composites use the tail action. This proves the category equations for arbitrary n.

Use one individual at R as well. Every individual action is the unique singleton map, so it respects all compositions.

## 3. Root domains and the nominal action

Let G=Sym(N) permute replica indices, fixing the tail, y, x, and root individuals. It sends z_n to z_(pi(n)). Define root domains recursively on argument types.

A root relation X of type tau has:

1. A current extension K_X contained in the full product of the already constructed root argument domains, supported by a finite set of replica indices under their recursive G-action.
2. An arbitrary old entity a_X in D_A^tau, with rows A_0^X,A_1^X.
3. Arbitrary B-current tables C_n^X, subject only to C_n^X=A_1^X for all but finitely many n.

Set b_n^X=b(a_X,C_n^X), and define whole transports by

    yX=a_X,       xX=h a_X,       z_nX=b_n^X.

The whole identities of section 1 prove compatibility with every old postcomposition. A root intension is determined by this data. The action of pi sends K_X to its image under the lower-type tuple action, fixes a_X, and replaces C_n by C_(pi^-1(n)). It is a domain automorphism.

Every whole root entity has finite support: combine a support of K_X with its finite exceptional set {n:C_n^X!=A_1^X}. The old a_X is fixed by G. Root individuals have empty support. By recursion every root argument tuple has finite support, so its singleton current extension is admitted.

There is no fixed support bound for an entire quantified domain. Every root variable ranges over its whole recursively defined domain, and every target variable ranges over the unchanged full target domain.

## 4. Closure and C soundness

For a term with finitely many free root parameters, evaluate its y-environment in the old A model to obtain a_t. At z_n, outside the finite union of the parameters' exception sets, the complete B environment is h applied to the A environment. Hence the whole term value is h a_t there.

At an exceptional n, its old B evaluation gives a full B entity b_(t,n). Naturality of the old interpretation and the equalities j_i z_n=y, e_i z_n=x give

    j_i b_(t,n)=a_t,        e_i b_(t,n)=h a_t.

In the full B profile these equations mean exactly that the j_i rows are the identity row of a_t, and the e_i rows are its h row. Its current row is arbitrary. Thus b_(t,n)=b(a_t,C_(t,n)) for an allowed table, and the whole cofinite condition holds.

This argument covers lambda abstraction: outside the finite exception union the FREE environments agree as whole B entities; the bound variables still range independently over all B arguments. It does not take a union of exception sets over bound-variable values or pull a target quantifier back to R.

At R, interpretation is equivariant under replica permutations. They reindex the full root domains, fix the full old domains, and relabel the z_n arrows. The finite union of supports of the free parameters consequently supports the current row of every term, including terms with root quantifiers and modal operators. This proves admission of the lambda and logical operations at every permitted type.

The usual restricted-profile soundness proof for C now applies. For clarity: actual Boolean and quantified clauses use these entire domains; singleton predicates distinguish different raw current entities; lambda beta/eta hold at every profile coordinate; H-theorem-equivalent formulas agree at every coordinate and assignment, so their abstractions are equal profiles. Logical Equivalence is used only with its theoremhood condition, not with optional assumptions. S4 follows from category composition and identity, and persistence of equality follows from transport being a function on entities.

## 5. Exact entailment order

The free coordinates are K_X, A_0^X, and C_n^X for every n. If X<=Y these coordinates are included. Conversely suppose inclusion at every free coordinate. Choose n outside the two finite exception sets. Then C_n^X=A_1^X and C_n^Y=A_1^Y, giving A_1^X contained in A_1^Y. Thus all A rows are included, and the table formula for b_n includes all its rows as well. The x row is determined by h a. This proves necessary inclusion at every root and old profile coordinate.

Hence root entailment is exactly componentwise inclusion of the displayed free rows. At t the Boolean algebra is 2 x 2 x FinCof(N), with the x truth bit recomputed as the eventual C_n bit. It is atomic, although its x coordinate does not give an additional singleton atom.

## 6. Self-atoms at every type and their density

There are three kinds of singleton free-coordinate relation.

**Current-root tuple atom.** Put one current root tuple into K, and put a=bottom and every C_n empty. It is admitted by finite support of the tuple. It is an ordinary atom by the free order, and all its nonidentity transports vanish. Therefore it is strong and self-atomic.

**The y-identity tuple atom.** For any old A argument tuple alpha, take K empty, A_0={alpha}, A_1 empty, and all C_n empty. It is admitted and is an ordinary atom by the free order. Its y transport is the full A singleton profile delta_(1_A,alpha). Its x and every z_n transport have one tuple alpha at each of the j_1,j_2 rows and empty current/e_i rows.

This root relation is a SELF-ATOM. Its only nonempty current row at a world accessible directly from R is the row at y, where its whole transport is the atom delta_(1_A,alpha). At the B worlds x and z_n its current extension is empty, so the self-atom conditional is vacuous there; at either later j_i it again becomes delta_(1_A,alpha). Further e_i transports keep the false-current two-j-row profile. Thus whenever it is instantiated its transported whole entity is an ordinary atom in the FULL target algebra.

It is not strong: after x or z_n, the nonzero profile with two j rows splits into the two admitted singleton-row profiles. Self-atoms are allowed precisely this kind of split at a world where they are not instantiated.

**Replica tuple atom.** For any n and any old B tuple beta, put K empty, a=bottom, C_n={beta}, and every other C_m empty. Its only nonzero old value is at z_n, namely delta_(1_B,beta). That old singleton becomes bottom after every nonidentity old arrow, because no such postcomposition can produce 1_B. This gives a strong atom and hence a self-atom. Support at the root is the single index n.

Every nonzero root relation has a nonempty free coordinate, and contains the corresponding atom just described. If every free coordinate is empty, eventuality makes A_1 empty too, so the whole relation is bottom. Equivalently, a nonzero composite x row is reflected at cofinitely many C_n rows and cannot form an uncovered remainder. Consequently every possible root relation contains a self-atom: **Self-Atomicity_all holds**. The same density proves ordinary Atomicity_all.

The cofinite restriction is essential. A singleton supported only at x would fail self-atomicity because e_i x=x; our cofinite domain does not admit that singleton. Any nonzero x row comes with fresh replica rows, and one of their self-atoms lies below it. The y atoms may be nonstrong, which is permitted by Self-Atomicity and is essential to the construction.

## 7. Internal Boolean completeness, with necessary scope

Let F be any admitted root property of tau-relations, and let L be its CURRENT extension, supported by a finite index set J. Form the external unions of the current rows K_X, the A-identity rows A_0^X, and the C_n^X tables over X in L.

The union K_* is J-supported: each permutation fixing J permutes L and carries the current rows accordingly. The union A_* is an arbitrary permitted A-current table. For n,m outside J, their transposition permutes L while fixing all old tuples, so the union table D_n equals D_m. Let B_* be this common table. There is no restriction on old tables beyond being subsets of their full finite tuple domains.

Choose a_* with rows (A_*,B_*), and use C_n^*=D_n. This sequence is eventually B_*, and K_* has finite support, so the resulting root relation is admitted. The free-coordinate order proves it is exactly the LUB of the current F-members. Complements give GLBs, including empty families. This proves native internal BC at every relational type.

It does not assert external completeness of arbitrary unrepresented root families. For example the externally chosen even replica singletons do not form an admitted current family, since that family has no finite index support.

Both old objects have full finite profile algebras at every fixed type and therefore BC and ordinary Atomicity at every type. Together with root BC and Atomicity, this proves **necessary BC_all and necessary Atomicity_all** at R.

## 8. Failure of necessary Strong Actuality

The world y reaches unchanged A. At A every true proposition p contains 1_A. Its h transport therefore contains both j_1 and j_2, since j_i h=1_A. The admitted B proposition {j_1} separates these two rows. Thus h p neither entails {j_1} nor entails its negation. No true proposition at A is strong, so Strong Actuality fails there and its necessitation fails at R.

At R itself the root-only true proposition is strong. The y propositional atom from section 6 is a self-atom that is not strong; since it is an ordinary atom, it has no nonzero proper strong subrelation. Therefore Strong Atomicity_t fails at R.

## 9. Necessary IC is compatible with the separation

For any root relation with current extension K, retain K and set all old data to bottom. This current-only coextension is admitted, because K already has finite support. It is inextensible: at the root any tester necessarily containing its current members bounds it, and at every strict successor its transport is bottom. No arrows return to R. The full old objects admit exact-image profiles of every current tuple set, and these are rigid and inextensible. Thus necessary IC_all holds at R.


## 10. Sources

GPT-6 Astra, prompted by Daniel Kodsi, *Self-atomic nominal entrance over
the full double-retraction tail*, 30 October 2026, §§1–9
(unpaginated), supplies this construction and its simultaneous profile.
The double-retraction category and its Strong Actuality failure are
Cian Dorr's construction of 6 October 2026, recorded in
[[full-two-object-double-retraction]]. Full action semantics is given
in Bacon and Dorr, *Classicism*, draft of 16 May 2023, §3.5, pp. 58–61,
and Appendix D, pp. 73–74.

The nominal supported-family method has antecedents in OpenAI Codex, prompted by Daniel Kodsi,
*Structural algebraic research: boxed Plenitude and stronger world
principles*, 22 October 2026, §2 (unpaginated). See also *Old/new model:
Boolean Completeness and the rigidity separation*, 22 October 2026,
the all-type completeness argument (unpaginated). The cofinite entrance
method is also used in [[nominal-cofinite-sections-entrance]].
