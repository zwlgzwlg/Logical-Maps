# Transversals from intersections of supports

Transversal holds necessarily in the [symmetric integer stages](symmetric-integer-paired-stages.html)
and in all four [symmetric surjection products](symmetric-surjection-products.html).
The same construction selects a representative at every relation type. It works with
infinite pins because it uses only intersections of two supports at a time.

Fix a stage $n$ and write $G$ for its automorphism group. For the paired
stages a pin is a countable union of complete blocks, enlarged to contain
all distinguished singleton blocks. For the surjection products it is
any subset of the auxiliary base of size at most $\kappa$. Each coordinate
has more interchangeable ordinary blocks than fit in a pin. Write $G_P$
for the pointwise stabilizer of a pin $P$. For a current extension $E$
of a relation, call $P$ a support if $G_P$ preserves $E$ as a set of
typed tuples. A pin for any relation with that extension is a support,
after closing under partners in the paired case.

**Intersection.** If $P,S$ support $E$, so does $R=P\cap S$. Let $g$
fix $R$ pointwise. Choose $\theta\in G_P$ moving all blocks of $g[P]$
outside $P$ to fresh blocks outside $P\cup S$, in their respective
coordinates. Then $\theta g[P\setminus R]$ misses $S$: a block of $P$
that stays in $P$ cannot land in $R$, which $g$ fixes. The map equal to
$\theta g$ on $P$ and the identity on $S$ therefore extends to an
automorphism $\beta\in G_S$. Indeed it is an injective block map on the
specified sets, preserves coordinates and the indicated orientations,
and leaves enough unused blocks for a bijective extension. The same
argument with one-point blocks works for the full symmetric group of
the surjection product. Since $\beta^{-1}\theta g$ fixes $P$, the two
stabilizers $G_P,G_S$ generate $G_R$. Both preserve $E$.

**Representative.** At an empty-word arrow with target $n$ and
coefficient $f$, give $Y_E$ the row
$$
 \bigcup\{\,\pi[E]:\pi\in G,\quad
         f|_S=\pi|_S\text{ for some support }S\text{ of }E\,\}.
$$
Use empty rows at all other targets or words. For the product with an
idempotent use only the identity monoid coordinate. If $P$ is any
support of $E$, two coefficients agreeing on $P$ yield the same row.
For every witness $\pi,S$ for the first coefficient, the support
$P\cap S$ gives the same witness for the second. The reverse inclusion
is identical. Thus $P$ pins $Y_E$. Target equivariance follows by
postcomposing the witnessing permutations. At the identity every
witness fixes a support of $E$ pointwise, so the row is exactly $E$.

For $h\in G$ the transported entity $hY_E$ is $Y_{h[E]}$. A witness
$\pi$ for $fh$ on $S$ corresponds to the witness $\pi h^{-1}$ for $f$
on $h[S]$, and these witnesses contribute the same tuple set. Consequently
the family of all $Y_E$ is invariant under $G$. Use that family as the
row of a higher-type predicate on every identity-monoid-coordinate
arrow to the current stage, and use empty rows elsewhere. This predicate
is equivariant and has empty pin. It selects precisely one entity for
each current extension: every extension occurs and different ones give
different identity rows. The construction applies at every stage.
