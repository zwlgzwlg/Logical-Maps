# Relational Choice in symmetric models with one individual

Proof by OpenAI Codex, prompted by Daniel Kodsi, 22 October 2026.
These are additional verdicts for existing constructions, not new models.

## The support obstruction

Use the symmetric ideally-full construction's actual profile semantics.
An intension at an object \(V\) is pinned by a permitted subset of its
pinning carrier \(I_V\); the carrier is distinct from the individual domain
in the singleton variant. Profiles at parallel arrows agreeing on that
subset coincide. For \(w:V\to W\) and a designated symmetry \(g\in G_W\),
the profile at \(gw\) is the image under \(g\) of the profile at \(w\).
Transport is precomposition. All symmetric pinned profiles are admitted.
Only the evaluation object's supports need be finite in the argument below.
In particular, the second object of the unpinned construction may retain
its improper ideal.

Suppose a graph \(S\) witnesses Relational Choice at input type \(tt\)
and output type \(t\) for the serial relation
\[
 U(A,p):=Ap\lor\neg\exists q\,Aq.
\]
Let the finite pinning set \(N\subseteq I_V\) support \(S\). At each
outgoing arrow define the **whole** property intension
\[
 A_w=D_t(W)\setminus\operatorname{Fix}((G_W)_{w[N]}),
 \qquad w:V\to W,
\]
where the stabilizer fixes \(w[N]\) pointwise and acts on propositions as
entities. The definition is a set-sized profile family. If parallel arrows
agree on \(N\), their images of \(N\) coincide, so \(A\) is \(N\)-pinned.
For a target symmetry \(g\),
\[
 (G_W)_{g[w[N]]}=g(G_W)_{w[N]}g^{-1}.
\]
Thus the fixed subsets, their complements and the profiles transform
equivariantly. Full admission gives \(A\) in the property domain.
This does not assume arrows \(w\) are injective or invertible.

For each \(g\in(G_V)_N\), pinning makes \(gS=S\) and \(gA=A\) as
whole intensions: at every further arrow \(k\), the arrows \(kg\) and
\(k\) agree on \(N\). Assume now that, for every finite \(N\), some
symmetry in \((G_V)_N\) moves a proposition. Then \(A_{1_V}\) is nonempty.
The selector chooses a proposition \(p\) in it. Equivariance shows that
\(S\) also chooses \(gp\) from the same \(A\), for every
\(g\in(G_V)_N\). Actual functionality implies \(gp=p\) for all such
\(g\), contradicting \(p\in A_{1_V}\).

Consequently the single membership-selector instance \(RC_{tt,t}\), and
hence full Relational Choice, fails. The proof uses no external Choice,
well-ordering, uniform choice of witnesses for different supports, or
general implication from RC to TC. It does require full admission of
symmetric pinned profiles; it does not apply to a sparse Henkin hierarchy.

## Construction witnesses

The six constructions below have finite supports at the evaluation object
and the full profile admission just used. Replacing the individual domain
by a singleton leaves their proposition domains, pinning carriers and
symmetry actions on propositions unchanged. The witnesses therefore apply
to both existing signature interpretations whenever those variants exist.

For the first five, put \(p_{ab}(w)\) iff \(w(a)=w(b)\). This proposition
is pinned by \(\{a,b\}\) and symmetric because target symmetries are
injective. For a transposition \(g=(a\ c)\) fixing \(b\),
\(gp_{ab}=p_{cb}\). An allowed arrow with
\(w(a)=w(b)\ne w(c)\) distinguishes them. All points in this paragraph
are pinning points, not required inhabitants of type \(e\).

* In **symmetric-class-reflecting-surjections**, take \(a,b,c\) outside
  the given finite support in one infinite qualitative class. The
  transposition is a qualitative automorphism. A surjection of that class
  onto itself with the required collision, extended identically on other
  classes, reflects the equivalence relation and is an allowed arrow.
* In **symmetric-collapse-pair**, choose the three points outside the
  support and the distinguished pair. Collapse that pair and \(a,b\),
  keep \(c\) distinct, and extend to a surjection. This is an allowed
  collapser; the transposition preserves the distinguished pair.
* In **symmetric-range-gap**, choose them also away from the distinguished
  point \(d\). A function omitting \(d\) can realize the collision.
* In **symmetric-two-object-unpinned**, choose them at the first object.
  The collision proposition is false on its permutation endoarrows. An
  arrow to the second object is any function and can realize the collision.
  This defines the proposition on every outgoing arrow; it is not merely
  a profile at the second object.
* In **symmetric-qualitative-links**, take distinct point endpoints
  \(u,v\) away from the distinguished pair. Choose \(a,b,c\) outside
  the support in the link fibre over \((u,v)\). Their transposition fixes
  all points and preserves the qualitative relation. The required arrow
  is checked explicitly next.

For qualitative links, take a surjection on the countable point carrier
collapsing the distinguished pair and fixing \(u,v\). Extend on each
companion pair by a bijection onto the companion pair of its point image.
Extend on a link fibre over \((x,y)\) by a surjection onto the link fibre
over \((f(x),f(y))\), when these images differ, and onto their companion
pair when they coincide. Use the recorded concrete presentation of links
\(\langle x,y,n\rangle\) to choose these fibre maps explicitly; this
requires no choice of a family of arbitrary enumerations. On the unchanged
fibre over \((u,v)\), choose a surjection identifying \(a,b\) but keeping
\(c\) distinct. This preserves the defining ternary relation. It is onto
points; every target companion pair has a source companion pair; and every
target link fibre has a source fibre above preimages of its distinct
endpoints. Hence the complete map is surjective and belongs to the
construction's collapser class. The native source's finite-extension
argument provides the same small collision instance.

The sixth construction, **symmetric-qualitative-contrast**, has only
injective arrows, so uses a different proposition. At the root \(W_0\)
the symmetry group is the full permutation group; at \(W_1\) it is
trivial. Fix a pinning point \(k\) at \(W_1\), and set
\[
 p_a(w)\quad\text{iff}\quad
 \operatorname{target}(w)=W_1\ \text{and}\ w(a)=k.
\]
It is symmetric and pinned by \(\{a\}\); profiles ending at \(W_0\)
are empty. Given finite \(N\), choose distinct \(a,c\notin N\).
The root symmetry \((a\ c)\) sends \(p_a\) to \(p_c\), and any
permutation \(w:W_0\to W_1\) with \(w(a)=k\) distinguishes them.

These conditions are attached only to the six specified constructions.
No conclusion about other members of the group follows without their own
condition witness. The three additional negative families in the original
application note already have the relevant derived failure and receive
no duplicate argument here.

## Old and new individuals: necessary Transversal Choice

The singleton variant of **symmetric-old-new-individuals** is different.
At \(E\) there are two outgoing arrow kinds, to \(E\) and to \(O\).
At \(O\) there are three: to \(E\), the old/new-preserving permutation
group \(G_O\), and the injections \(K\) into the old part. Composition
depends only on kinds. The individual domains are singletons and their
symmetry actions are trivial.

Induct simultaneously on types to show that every type domain at both
objects is finite and every designated symmetry acts trivially. Suppose
this holds for all argument types of a relation, and let \(X\) be pinned
by finite \(N\). Two arrows \(h,h'\) of the same kind have restrictions
on \(N\) matched by a target symmetry \(g\). At target \(E\), extend
the finite partial bijection to a permutation. For \(E\to O\) and
\(K\), all images are old and the matching extends within the old part.
For \(G_O\), extend separately on the old and new parts. Thus
\(gh|N=h'|N\). Symmetry and pinning give
\[
 X_{h'}=X_{gh}=g[X_h]=X_h,
\]
the last equality using the induction hypothesis on all argument entities.
Hence a whole intension is determined by one subset of a finite tuple
domain for each of finitely many arrow kinds. There are finitely many such
assignments. Precomposition by a source symmetry preserves kinds, so fixes
each intension. This completes the induction on whole entities, not just
their current extensions.

At either object, an equivalence relation on any actual type domain has
finitely many cells. Finite choice selects one point from each, and a
finite disjunction of equalities is an admitted property with exactly that
transversal as its current extension. This proves Transversal Choice at
every type at both objects, therefore its boxed schema at the root.
Only finite choice, available in ZF, is used. The same finite-domain
argument directly proves Relational Choice; the record retains only boxed
TC because boxed RC follows by the existing boxed TC-to-RC implication.
No assertion about the distinct principle `transversal-r` is added.

## Sources and verification scope

Direct source of the new arguments: OpenAI Codex, prompted by Daniel Kodsi,
*Singleton-individual variants: direct choice verdicts from the stabilizer
theorem*, 22 October 2026, §§1–4, unpaginated
(`rc-symmetric-singleton-applications.md`, unpaginated), and
*Relational Choice forces Transversal Choice in symmetric ideally-full map
categories*, same date, §§1–2, unpaginated
(`rc-symmetric-ideal-full-categories.md`, unpaginated).

Construction attribution is unchanged: Cian Dorr, *Boolean Completeness
does not imply Rigid Comprehension*, draft of 30 July 2026, Definitions
15–18, p.8, and the construction-specific sections in the model records;
the qualitative-contrast precursor is Bacon–Dorr, *Classicism*, draft of
16 May 2023, Appendix D, p.79. The old/new finite-domain argument was already
recorded by Claude Opus 5.5, prompted by Cian Dorr, 7 October 2026; the new
conclusion here uses it for choice.
