# Weak inextensibility obstructions for interpretation covers

GPT-6 Astra, prompted by Daniel Kodsi, 30 October 2026.

These are conditional theorems about explicitly specified interpretation-cover
semantics. They do not establish a general implication over unrestricted C.
Maximalism is not used. In each case, a weakly inextensible coextension of one
admitted family would produce a true proposition entailing every current truth,
and a nonzero propositional atom. Thus Atomlessness excludes that coextension
within the stated class, even when its finite-pin requirement is removed.

At relation type tt the native predicate is

    WeaklyInextensible(Y) :=
      forall X ((forall p (Y(p) -> Box X(p))) -> Y <= X).

The necessary inclusion Y<=X ranges over the complete future proposition domains.
All enlargements considered below must remain C-valid, with faithful whole
proposition profiles, C closure, and the explicitly retained category, family,
transport and test facts. Enlarging domains alone does not establish those facts.

## 1. Progressive-name cylinders

There is a single root object r, a monoid of root loops that are progressive maps on each auxiliary name set C_sigma, and old interpretation arrows whose targets never return to r. Each typed name set is indexed by an infinite initial ordinal with no greatest element. Higher-type names are semantic indices, not automatically root entities of that type.

Let C be the disjoint union of ALL auxiliary typed name sets. This is a set: the fixed relational type system has a set of finite types, and each C_sigma is a set. For each c in C, let p_c be the existing proposition Fix_{c}, true exactly at root loops fixing c and false at all old targets. The existing cylinder calculation gives, as WHOLE propositions,

    rho_h(p_c)=p_c if h fixes c, and bottom otherwise;
    rho_I(p_c)=bottom at every old interpretation I.

Every p_c is true and nonbottom at r. They are pairwise distinct, including across types: move one chosen name upwards and fix the other. Any nonidentity root loop moves at least one name in C.

Retain the following properties:

* E^(tt) has extension {p_c:c in C} at EVERY root loop and empty extension at every old arrow. It is empty-pinned and lands as the whole bottom property at each old target. There is no restriction to a countable subfamily of individual names.
* For each c, X_c^(tt) has universal current extension at root loops fixing c, and the extension D_t(r) minus {p_c} at root loops moving c. Its old section is the admitted closed old operation lambda q.(q=bottom). This is {c}-pinned and satisfies the original old-landing condition.

These are literal allowed profiles in the existing full finite-pin/old-landing hierarchy. If considering a domain extension, the theorem below assumes the same evaluation facts for E, p_c and X_c are preserved, and the root/old category still has the stated kinds of arrows. No pinning condition is imposed on the proposed new witness Y.

### Every current family member passes each test

Fix c and any d in C. At a root loop h fixing c, X_c is universal. At a root loop moving c:

* if d=c, rho_h(p_d)=bottom, different from the nonbottom p_c;
* if d differs from c, rho_h(p_d) is either bottom or p_d, both different from p_c.

Thus X_c accepts rho_h(p_d). At an old interpretation the transported p_d is bottom, accepted by the whole old section of X_c, including after any further old arrow. Hence Box X_c(p_d) holds at r for every c,d.

### The coextension isolates identity

Suppose Y is currently coextensive with E and weakly inextensible. Its current members are exactly the p_d. The preceding calculation verifies the native antecedent

    forall p (Y(p) -> Box X_c(p))

for each c. Weak inextensibility of Y therefore gives Y<=X_c for EVERY c.

Let h be a nonidentity root loop. Choose a typed name c moved by h. In the full target proposition domain, p_c remains a permitted argument, although the transport of the original p_c along h is bottom. Since X_c at h excludes the ARGUMENT p_c, the necessary entailment Y<=X_c implies Y_h(p_c) is false. But E_h(p_c) is true by the constant root-loop extension of E. Thus E and Y are not currently coextensive at h.

Define the admitted proposition

    w := (exists p E(p)) AND (forall p (E(p) iff Y(p))).

At id_r it is true: E is inhabited and Y was chosen coextensive. At every nonidentity root loop the second conjunct is false by the preceding argument. At every old arrow the first conjunct is false because E is empty there. Thus w is true at EXACTLY id_r among all outgoing root arrows.

Consequently w is an actual-world proposition: for every currently true proposition q, every arrow satisfying w is id_r and satisfies q, so w<=q. It is also a nonbottom atom of the root proposition algebra: any nonbottom subproposition must contain the identity and hence equal w. This directly contradicts global propositional Atomlessness.

No step selected a finite pin for Y. The argument uses full target arguments, in particular p_c at h, not just transported root arguments. Nor does it choose a uniform operation assigning witnesses to every current family: one weakly inextensible coextension of this ONE admitted E already suffices.


No pin of Y was used. The conclusion requires that every nonidentity root loop
move a detected auxiliary name, that no old arrow return to the root, and that
the listed families and tests retain their stated interpretations. Extra loops
invisible to every name, or changes to these admission facts, are outside this
theorem. No infinite conjunction of the tests is formed: the single coextension
formula uses the full proposition quantifier.

## 2. Surjective chain names

The surjective chain-name cover has typed names c=(sigma,j,n), chain-preserving nondecreasing surjections of N on every chain, trivial designated root symmetry, and the same arbitrary old interpretations/landing requirement. Such maps are deflationary. Therefore its fixed-name cylinders obey the same whole transport erasure: if h fixes c then rho_h p_c=p_c, and if h lowers c, no subsequent root loop can restore it, so rho_h p_c=bottom. Old transports are bottom as before.

An exact family choice matters. Every level-0 name is fixed by all root loops; its cylinder is the same root-only mask across chains and types. Accordingly use **all typed positive-level names**, rather than asserting that all names give pairwise distinct cylinders. These positive-level cylinders are nonbottom and pairwise distinct. On one chain, the map

    delta_m(k) = k       for k<m,
                 k-1    for k>=m,       m>=1

is a nondecreasing surjection fixing every smaller positive level and moving level m. It distinguishes different levels on that chain. Applying it on one chain and identity elsewhere distinguishes different chains or types. Every nonidentity loop lowers a positive-level name, so this family detects every nonidentity loop.

Its constant-root E and the X_c tests are admitted with the same empty/{c} pins and whole old bottom/equality sections as above. Hence the entire no-pin proof applies to this exact cover. It rules out enlarging only the admissible supports while retaining this family/test geometry and Atomlessness.

This obstruction is compatible with current full BF in the chain cover. BF can supply a root preimage of the excluded future p_c, but that preimage need not be one of E's actual members. The test antecedent concerns those members, so BF does not undo it.

## 3. Chain-permutation covariance

Keep the set-sized old C-complete family, all typed interpretation arrows, unchanged old domains and futures, and no old-to-root arrows. For each auxiliary type sigma use names `(sigma,j,n)`, with infinitely many chain indices j and n in N. Enlarge the root monoid to the full chain wreath monoid:

    h(sigma,j,n) = (sigma, pi_sigma(j), h_(sigma,j)(n)),

where each pi_sigma is a permutation of chains and each h_(sigma,j) is a nondecreasing surjection N to N. Let Gamma be all pure typed chain permutations, with every level map the identity. Use Gamma as the designated root symmetry group.

At all relational types retain finite arrow pins, whole old landing, and the usual root covariance

    R_(gamma g) = rho_gamma[R_g]

on the FULL target tuple domains. Admit every profile satisfying these conditions. An additional nominal finite-support requirement under the corresponding chain-relabeling automorphisms is allowed; all profiles used below satisfy that stronger requirement as well.

The wreath maps and designated symmetry form the following coherent category. The wreath maps form a monoid, Gamma consists of genuine invertible arrows, precomposition preserves all old interpretations, and postcomposition by old arrows is unchanged. Root transport preserves covariance and finite pins. The ordinary whole-transported-environment closure proof remains valid. Covariance of terms follows by bijective reindexing under Gamma; full root and old quantifiers are not restricted to fixed-support subsets.

Named lifts with zero root rows are covariant and retain their whole old interpretation values. Thus the old witnesses for pure and fixed free-signature Max are retained. Global Atomlessness also survives the attempted repair: at a root witness choose an individual chain absent from the pin, change its level-1 image by replacing that chain's level map, and split by the level of that image. The level test is Gamma-invariant, unlike the old exact-name fixing test. At an old witness the fresh propositional-name top/bottom split is unchanged. The obstruction below therefore concerns these same domains and transports.


### Current identity under covariance

For an existing root entity a, let H_a have singleton root row {rho_g a} at g
and whole old section equal to the old haecceity of rho_I a at I. A pin of a
pins H_a by equality of whole transported parameters; for an individual name
use its singleton pin. These rows satisfy covariance, and the old sections are
admitted old haecceities. At identity H_a separates a from every other entity,
so native current equality is literal equality. An arbitrary constant singleton
root row would generally fail covariance and is not used here.

The optional nominal support requirement preserves the displayed profiles:
chain relabelling conjugates loops and precomposes interpretations, and on
covariant profiles agrees with root Gamma transport. A finite arrow pin gives
support on its finitely many chains. The level predicates and full orbit
families are invariant under all such relabellings.

### Two low-type relations force the family

Define A of type et by the same root row at every loop: all individual names of level 1. Give A empty old rows. Define B of type eet by the same root relation at every loop:

    B((e,j,0),(e,j,1)) holds for every individual chain j,

with no other pairs and with empty old rows. Both profiles are empty-pinned and have whole bottom old sections. Chain permutations preserve their rows, so they satisfy covariance and have empty nominal support. Neither requires an e-valued operation.

For c_j=(e,j,1), put p_j=A c_j. As a WHOLE proposition, its root truth row at g says that the image g(c_j) still has level 1; all its old rows are false. The p_j are nonzero and pairwise distinct. Their transports are

    rho_h p_j = p_(pi_e(j))  if h_(e,j)(1)=1;
    rho_h p_j = bottom      if h_(e,j)(1)=0.

These are whole-profile identities, including all old futures. The second holds because a subsequent deflationary level map cannot raise level 0. Every old transport is bottom.

Now use the ordinary C term

    E := lambda p^t. exists a^e (A a AND p=(A a)).

At every root loop its extension is exactly P={p_j : j is an individual chain}. Here p=(A a) is identity of WHOLE propositions. The guard A a selects exactly the current level-1 names. At every old arrow the guard is false, so E has empty extension. Thus E is exactly the constant-root family used in the obstruction. It is lambda-forced once A is admitted, not an arbitrarily imported external family. It is also Gamma-invariant and empty-supported since Gamma permutes the p_j.

Let chi := exists a^e A a. It is true at every root loop and false at every old arrow. For a fixed c_k define the ordinary tt term

    X_k := lambda p^t.
       (chi AND (A c_k OR NOT exists b^e (((B c_k)b) AND p=(A b))))
       OR (NOT chi AND p=bottom).

At a root loop g, X_k is universal if g preserves the level of c_k. If it lowers that level to 0, X_k excludes exactly p_(pi_e(k)), the level-1 cylinder for the destination chain. At every old object its WHOLE section is lambda p.(p=bottom), including all subsequent futures. These are the required rows, now obtained from C closure itself.

The tester has the pin {c_k}, beyond the empty pins of A and B. Under a chain permutation its excluded proposition relabels together with its destination chain, so it is covariant. Its nominal support is just the chain of c_k. Consequently neither the family nor its tester is discarded by this symmetry or by the additional natural nominal finite-support requirement.

### Finitely pinned coextensions fail

Suppose Y is currently coextensive with E and weakly inextensible. Let S be a finite arrow pin of Y. Choose k whose entire individual chain is disjoint from S, and let h have identity chain permutation, collapse that chain's first step by n -> max(n-1,0), and act identically elsewhere. Then h agrees with identity on S, so Y_h has the same full row as Y_id and contains the target argument p_k.

For every j, Box X_k(p_j) holds. At a root g preserving c_k's level X_k is universal. Otherwise, the image of p_k is bottom. Every other p_j either becomes bottom or becomes p_(pi_e(j)), distinct from the excluded p_(pi_e(k)) because pi_e is injective. At every old arrow all these images are bottom, which X_k accepts.

Thus the exact weak-inextensibility antecedent `forall p(Yp -> Box X_k p)` holds. But at h the full target argument p_k belongs to Y_h and is excluded by X_k,h. Hence Y<=X_k fails, contradicting weak inextensibility.

This proves failure of WIC at tt in the specified finite-pin cover class. It remains valid with any smaller designated chain-permutation subgroup, provided A and B remain admitted. No full current powerset principle, all-type family encoding, or quantification over external arrows is needed. Future arguments are taken from the entire target D_t, including p_k, irrespective of which actual family member transports to them.

### All positive levels and types remove the pin of Y

For the full designated Gamma, there is a further retained-profile obstruction. Index c by ALL positive-level auxiliary names `(sigma,j,n)`, n>=1, and let p_c have root truth condition

    level(g(sigma,j,n)) = n,

with false old rows. The set of all such indices is a set. Each p_c is pinned by {c}, satisfies Gamma covariance, and has bottom old landing. They are pairwise distinct: different chains/types can be altered independently, and at two levels in one chain the first deletion at the larger level separates them. They are all currently true.

For h=(pi,h_j), whole transport is p_(sigma,pi_sigma(j),n) if h_j(n)=n, and bottom otherwise. Any fall in level makes future return impossible. Let E_all have the set of ALL these p_c as its constant root extension and empty old rows. The whole family is Gamma-invariant, so E_all is symmetric, empty-pinned and empty-supported.

For c=(sigma,j,n), define T_c at a root loop g to be universal if g preserves c's level, and otherwise to exclude exactly p_(sigma,pi_sigma(j),n). Its whole old section is lambda p.(p=bottom). It is {c}-pinned and covariant: postcomposition by gamma relabels the excluded chain by the same permutation as the proposition argument. It has finite nominal support. Thus both E_all and every T_c meet the stated full admission rule.

Every current E_all-member necessarily satisfies T_c, for every c: a surviving image can equal the excluded label only if it came from that same type, chain and level, which is precisely the member extinguished in the exclusion case. Other images are either differently labelled cylinders or bottom. Old images are bottom.

Suppose an arbitrary admitted Y, with NO pin assumption, is a weakly inextensible coextension of E_all. Then Y<=T_c for every c. Every nonunit loop lowers some positive-level name, so its T_c excludes a cylinder that E_all still contains. Hence E_all and Y are not coextensive at any nonunit loop.

By C closure form

    w := (exists p E_all(p)) AND forall p(E_all(p) iff Y(p)).

It is true at identity and false at every nonunit loop and every old arrow. It is true at EVERY gamma in Gamma: every proposition satisfies designated symmetry covariance, so its truth at gamma equals its truth at identity. Thus w has precisely Gamma as its root truth set and no old truth coordinates.

This is an actual atom. Every current true proposition is true at all Gamma arrows by covariance, so w entails every current truth. Equivalently, a nonzero subproposition of w is true at some gamma, hence at identity and all Gamma, and must equal w. Atomlessness therefore contradicts even one such Y.

This coextension-proposition argument isolates the entire designated symmetry group. Fixed-name cylinders cease to be symmetric once names can permute; the level-survival cylinders, relabelled exclusion tests and their full orbit family remain admissible. The argument persists under domain enlargement if these stated profiles, transports, covariance and full-target semantics are preserved. It does not claim they survive arbitrary changes of category or admission rules.

## 4. The exact name-permutation normalizer

Let K be the original product of chain-preserving monotone-surjection monoids, before adjoining chain permutations. Its normalizer among typed permutations of auxiliary names is exactly the chain-permutation group Gamma.

Indeed the K-orbit of (sigma,j,n) is the finite initial segment `{(sigma,j,m):0<=m<=n}`, of size n+1. A typed name permutation nu with nu K nu^-1=K maps these orbits to the corresponding orbits and therefore preserves levels. The image of (sigma,j,0) determines the destination chain; preservation of every larger initial-segment orbit forces all (sigma,j,n) into that same chain at the same levels. Conversely a permutation of chains plainly normalizes K.

Thus an independent permutation of levels inside an individual chain is absent from this ordered-chain geometry. A nontrivial local permutation inside a chain would not preserve the level-map monoid. Full chain permutations already provide the natural maximal name-induced normalizer, and the bad all-chain family is invariant under them. This is a statement about name-induced diagram automorphisms preserving this monoid, not a classification of arbitrary action-model automorphisms or all possible repair constructions.


## Sources and scope

- GPT-6 Astra, prompted by Daniel Kodsi, *A weak-IC witness forces Actuality in
  the progressive-cover geometry*, 30 October 2026, retained data and no-pin
  argument (unpaginated); *The fixed-cylinder obstruction without a pin for the
  witness*, same date, §§1–5, including the positive-level chain extension.
- GPT-6 Astra, prompted by Daniel Kodsi, *Max/WIC symmetry repair: a bounded
  architecture obstruction*, 30 October 2026, §§1–5; *The chain-symmetry WIC
  repair gate*, same date, §§1–4, for the transported-singleton identity detail.
- The finite-support permutation model's fixed-point-family WIC argument,
  Claude Fable 5.1, prompted by Cian Dorr, September 2026, supplies the earlier
  finite-pin family/test method. Christopher Sun's Vicinity/WIC-to-Actuality
  witness, 27 September 2026, supplies the earlier coextension-proposition
  mechanism, under different hypotheses.
- The progressive and surjective chain-name interpretation covers, 30 October
  2026, supply the original name-cylinder and whole-old-landing constructions.
  The chain-surjection infrastructure also comes from Bacon and Dorr,
  *Classicism*, draft of 16 May 2023, Appendix D, Proposition D.5(2), pp. 74–77.

The conclusions are restricted to the listed admission, transport and symmetry
hypotheses. They neither establish a general Maximalism/WIC incompatibility nor
classify arbitrary action-model automorphisms or other possible constructions.
The normalizer statement concerns typed name permutations conjugating the exact
chain-preserving monoid onto itself.
