# Symmetric ideally-full model: Base 1 with least-support representatives

**Status: conjectured; bronze star.** Recorded at Zachary Goodsell's request,
30 September 2026. The proposed verification below is by GPT-6 (OpenAI
Codex), following the question whether Transversal holds in Base 1. It has
not been independently checked and is not recorded as proved.

The underlying model is Cian Dorr's Base 1 from *Boolean Completeness does
not imply Rigid Comprehension*, draft of 30 July 2026, §3.1, p. 9. Its
established properties and their verification history remain in
`symmetric-all-surjections`. This record proposes two additional verdicts
for that same model: Transversal and necessary Transversal at every
admitted type. It does not propose a new underlying construction.

## The proposed witness

There is one object, $\mathbb N$. Arrows are all surjections
$h:\mathbb N\to\mathbb N$, and the symmetry group $G$ is the full
permutation group. Relational domains contain exactly the symmetric,
finitely pinned intensions of the relevant type. Evaluation is at the
identity arrow $1$.

Fix a type $\sigma$. Write $D_\sigma$ for its domain and $A_h$ for a
property's extension at the arrow $h$. Transport satisfies
$(k\cdot A)_h=A_{hk}$, with composition read as $hk=h\circ k$.
Symmetry gives $A_{gh}=g\cdot A_h$ for $g\in G$, where the action on a
set is the pointwise action on its members.

Let $E\subseteq D_\sigma$ be an actual extension $X_1$. If $X$ is pinned
by a finite set $S$, then every permutation fixing $S$ pointwise fixes
$E$: pinning gives $X_g=X_1$, while symmetry gives $X_g=g\cdot E$.

### Least supports of extensions

Use the least finite **permutation support** $S_E$ of $E$, not a pinning
set of an arbitrary property with extension $E$.

The relevant support lemma says that finite permutation supports are
closed under intersection. Here is the proposed elementary justification
for this setting. If finite $A,B$ support $E$, every transposition of two
points outside $A\cap B$ fixes $E$: choose a fresh point outside $A\cup B$
and the two points, and express that transposition as three transpositions
through the fresh point. Each of those fixes $A$ or fixes $B$ pointwise.
Thus every finite permutation fixing $A\cap B$ fixes $E$. For an arbitrary
permutation fixing $A\cap B$, choose a finite permutation fixing that
intersection and agreeing with it on $A$; the two have the same action on
$E$ because $A$ supports $E$. Hence the intersection is a support.

Starting with any finite support and intersecting supports that omit each
dispensable member gives a least support. Its characterization yields
$S_{g\cdot E}=g[S_E]$ for every permutation $g$.

### Canonical representatives

Propose the property $\widehat E$ with extensions

$$
(\widehat E)_h=
\begin{cases}
g\cdot E,&\text{if }h|_{S_E}\text{ is injective and }g|_{S_E}=h|_{S_E}
             \text{ for a permutation }g,\\
\varnothing,&\text{if }h|_{S_E}\text{ is not injective}.
\end{cases}
$$

The proposed checks are:

1. **Well-definedness.** An injection on a finite set extends to a
   permutation. If $g,g'$ both agree with $h$ on $S_E$, then
   $g^{-1}g'$ fixes $S_E$ and hence $E$, so $g\cdot E=g'\cdot E$.
2. **Pinning.** The extension depends only on $h|_{S_E}$. If arrows $k,k'$
   agree on $S_E$, then $hk,hk'$ also agree there for every arrow $h$.
   Thus $(k\cdot\widehat E)_h=(k'\cdot\widehat E)_h$ for every $h$,
   so the whole intension is pinned by $S_E$.
3. **Symmetry.** Postcomposing $h$ with a permutation $g$ preserves
   whether $h$ is injective on $S_E$, and carries the chosen image of $E$
   to its $g$-image. Hence $(\widehat E)_{gh}=g\cdot(\widehat E)_h$.
4. **Actual extension.** $(\widehat E)_1=E$.

If these checks apply to the full ideally-full domain at every type,
$\widehat E$ is an admissible property with the required actual extension.

### A classifier in the domain

The construction should also satisfy

$$
g\cdot\widehat E=\widehat{g\cdot E}\qquad(g\in G).
$$

To check this at an arrow $h$, compare $(\widehat E)_{hg}$ with
$(\widehat{g\cdot E})_h$. The injectivity tests agree because
$S_{g\cdot E}=g[S_E]$; in the injective case, compose a permutation
agreeing with $h$ on $g[S_E]$ with $g$ to obtain one agreeing with $hg$
on $S_E$.

Consequently the proposed collection

$$
\mathcal C_\sigma=\{\widehat E:E\text{ is an actual extension of a }
\sigma\text{-property}\}
$$

is permutation-invariant. Define $F^{(\sigma t)t}$ to have extension
$\mathcal C_\sigma$ at every arrow. It is then pinned by the empty set,
and permutation-invariance of its extension gives symmetry. Ideal fullness
should therefore put this classifier in the domain.

At $1$, every extension $E$ has its representative $\widehat E$ in
$\mathcal C_\sigma$. If another member $\widehat{E'}$ has extension $E$,
then $E'=E$, and the canonical construction gives the same intension.
Thus the proposed $F$ selects exactly one property in each coextension
class, as Transversal requires.

## Scope and remaining verification

The argument is intended for every admitted $\sigma$, including $e$ and
higher types. If verified, it establishes the full Transversal schema.
The model's already established No Pure Contingency would then give its
boxed form, instance by instance. Together with the established failures
of Actuality and Relational Choice, this would witness that Transversal
implies neither of them.

The conjecture remains the Base 1 satisfaction claim, not merely the
existence of a model with the displayed package. Check the domain and
transport claims at arbitrary types, the use of permutation supports of
extensions, and the admissibility of the single classifier. A defect in
this witness construction would leave the satisfaction claim open; a
negative resolution would require showing that no admissible classifier
works at some type. No new verdict has been added to the proved Base 1
record, and no independent or Lean verification is claimed.

## Paper references

- **Background: Boolean Completeness does not imply Rigid Comprehension.** Dorr, Cian. Boolean Completeness does not imply Rigid Comprehension. Unpublished draft in progress, 30 July 2026, 27 pages. All page, proposition and lemma locators for this source refer to that draft. Parts of the draft were drafted with AI assistance; its mathematical claims are attributed to the author. — §3.1, p. 9; symmetric ideally-full domains and transport in §3. Source of Base 1 and its semantics, not of the proposed Transversal verification.
