# Integer stages with blocks of new markers

Logical Necessity and necessary Rigid Power can hold while Tame Rigidity fails. In this model a rigid relation has a single set of coordinates that pins every tuple in its actual extension. The resulting uniformity gives exact rigid representatives for arbitrary subsets of a rigid bound. A weakly rigid relation need not have that uniformity.

## The stages

Let $\kappa$ be infinite and $O$ a set of $\kappa^+$ ordinary individuals. At stage $n\in\mathbb Z$ the individuals are
$$
 O\sqcup M_n,\qquad M_n=\{i\in\mathbb Z:i\le n\}\times\kappa.
$$
An arrow $f:n\to m$ is an injection together with a free word on a countable alphabet. Ordinary individuals must map to ordinary individuals. Each source marker may map to itself if present at the target, or to an ordinary individual. All images are jointly distinct. Compose injections and concatenate words. Target symmetries are arbitrary permutations of $O$, with empty word, fixing all markers. Ordinary pins at any source stage have size at most $\kappa$.

As in [the injective integer stages](injective-integer-stages.html), a relation assigns rows at all arrows. Postcomposition with a target symmetry acts equivariantly on each tuple row. At a fixed word and target, two arrows agreeing on a pin have equal rows. Precompose profiles for transport. Agreement on a pin survives postcomposition, so two arrows agreeing there give the same whole transported entity. Transported pins are given by their images. For individuals themselves one point pins the individual. The union of the pins of the finitely many parameters controls the open term at a target, including all bound arguments in an abstraction. These facts give a separated typed action model of C. Evaluate at stage zero.

## Two facts about pins

Include all $M_n$ in designated pins at $n$, which adds at most $\kappa$ points. An arrow kind is specified by target, word and the set of source markers retained as themselves. For each kind take a representative $d$ that maps the whole source bijectively onto $O$ together with just the retained markers. Allocate distinct ordinary images to the discarded source markers and map the ordinary source bijectively onto the remaining pool. Any arrow of this kind agrees on a prescribed pin with some $gd$ for a target symmetry $g$. Extend the resulting partial bijection on the ordinary pool; only $\kappa$ ordinary positions have been prescribed.

A group support for an entity $x$ is a set whose pointwise stabilizer fixes $x$. An arrow pin is a group support by equivariance. Group supports are closed under binary intersections on $O$. Given supports $P,Q$ and a permutation $g$ fixing their intersection, first move $Q\setminus P$ off $P\cup gP$ using a permutation fixing $P$. The moved $Q$ still supports $x$. Extend $g|P$ to a permutation fixing that moved support; this permutation fixes $x$ and has the same action on $x$ as $g$. There are $\kappa^+$ ordinary points and each mentioned set has size at most $\kappa$.

Conversely, suppose $x$ is fixed by the pointwise stabilizer of $N\supseteq M_n$. Then $N$ is an arrow pin for $x$. To see this at a relation type, let $S$ be any existing arrow pin. For arrows $f,f'$ agreeing on $N$ with the same target and word, use their common kind representative $d$. Choose target symmetries $g,g'$ matching $gd,g'd$ to $f,f'$ on $N\cup S$. Then $g^{-1}g'$ fixes $dN$. The image of $d$ consists of the whole ordinary pool and some fixed markers, so it is invariant under every target symmetry. Conjugating $g^{-1}g'$ along $d$ on this image yields a source symmetry fixing $N$, in particular fixing every source marker. Thus $(g^{-1}g')x_d=x_d$ by equivariance, pinning and the assumed fixity of $x$. It follows that $x_f=x_{f'}$. This establishes the row pin and hence equality of whole transports. At individual type the same assertion is immediate: an ordinary individual fixed by the stabilizer of $N$ belongs to $N$, while all markers already belong to $N$. The result applies componentwise to tuples.

## A common pin for every member of a rigid relation

Let $F$ be rigid at $n$, let $E$ be its actual tuple set and let $N$ be an arrow pin for $F$ containing $M_n$. Write $B=M_{n+1}\setminus M_n$ and let $b:n\to n+1$ be the inclusion with empty word.

At each arrow $n\to n+1$, the image of every current tuple has an arrow pin avoiding all of $B$: its transported pin lies in the image of the source, and none of the fresh markers can be in that image. Use the tester that at every arrow ending in $n+1$ accepts just those tuples admitting a pin disjoint from $B$, and is full at other targets. This is empty-pinned and target-equivariant. Weak inextensibility of $F$ now shows that every tuple in the current extension of $bF$ has a pin disjoint from $B$.

At $n+1$ use a second tester whose row at $k$ accepts tuples with a pin disjoint from $k[B]$. It is $B$-pinned and target-equivariant. It necessarily accepts each current member of $bF$ because $k$ is injective and transports a disjoint pin to a disjoint pin. Rigidity of $F$ supplies weak inextensibility at this second stage. The tester therefore holds on $F_{cb}$ for every return $c:n+1\to n$.

Fix $x\in E$ and one of its pins $S$. The set $S\setminus N$ consists entirely of ordinary points, at most $\kappa$ of them. Choose $c$ preserving every old marker and fixing the ordinary points of $N$. Use the $\kappa$ fresh markers to cover $S\setminus N$ by their ordinary images, filling any remaining such images with distinct points outside $N$. Map the remaining ordinary inputs injectively into the untouched ordinary reserve. Then $cb$ agrees with the identity on $N$, and hence $F_{cb}=E$. The second tester gives $x$ another pin $T$ disjoint from $S\setminus N$. The group-support intersection lemma shows that $x$ is fixed by the stabilizer of $N$, since $S\cap T\subseteq N$. The converse pin lemma makes $N$ an arrow pin for $x$. The same $N$ thus pins every tuple in $E$.

## Necessary Rigid Power

For any external $U\subseteq E$, take the rows
$$
 H_U(f)=f[U].
$$
They are equivariant, and the common pin $N$ pins them because it controls the whole transports of all members of $U$. This gives an admitted relation. Its rows are exact images both now and after every transport, so it is rigid. At $U=E$, rigid coextension yields $F=H_E$.

Given a future weakly rigid $Z\le hF$, let $U=E\cap h^{-1}[Z_1]$. By exactness $h[U]=Z_1$. The relation $hH_U$ is rigid and has that same current row, so $Z=hH_U$ by weak persistence and weak inextensibility in the two directions. Every target rigid subrelation of $hF$ is therefore exactly the transport of a rigid source subrelation. Conversely these transports are rigid subrelations, by persistence of both defining conditions. The rigid power predicate for $F$ consequently has exact images along all source arrows, and these identities are hereditary by composition. It is rigid. This proves Rigid Power at every stage, for all finite arities including the empty tuple.

## Failure of Tame Rigidity

At $n$ choose the unary individual predicate $D$ whose row at $h$ is $O\setminus h[M_n]$. It is pinned by $M_n$. Every current ordinary individual remains in that row under all arrows by injectivity, proving weak persistence. Suppose a tester necessarily accepts all current members, and at $h$ take $y\in O\setminus h[M_n]$. Keep $h$ on its original markers and on the tester's pin. If $y$ is already the image of a pinned ordinary point the tester accepts $y$. Otherwise assign it as the image of a fresh ordinary source point and extend to an allowed injection with the same target and word. The tester's row does not change and must contain $y$ there. Thus $D$ is weakly rigid.

At the inclusion $b:n\to n+1$, all current members of $bD$ are ordinary, so necessarily differ from any chosen new marker $z\in B$. Choose a return $c$ preserving the old markers. The ordinary $c(z)$ belongs to $D_{cb}$ and fails the distinctness test from $z$ there. Thus $bD$ fails weak inextensibility and $D$ fails rigidity. Tame Rigidity fails at each stage.

## Modal and Boolean properties

Integer translation acts simultaneously on stages and the first component of marker labels. All pure sentences therefore have the same truth at every stage. For one proposition name, assign each realized pure matrix with a proposition variable a different last letter. On the whole corresponding final-letter sector set the name equal to the chosen witnessing profile with that last letter stripped. Use bottom elsewhere. The countably many witness pins fit the common bound. Evaluation after each chosen letter recovers the entire witness. This gives Logical Necessity for a nonvacuous signature.

The representative-row proof of Boolean Completeness for [the injective stages](injective-integer-stages.html) also applies. At each kind representative $d$ take the union of the $d$-rows of the current members of a family pinned by $N\supseteq M_n$. Symmetries fixing $dN$ conjugate back to symmetries fixing $N$, which permute the current family. Therefore extend the union equivariantly to all arrows in this kind by matching restrictions to $N$. Comparing on the union with any member's or upper bound's pin gives precisely the least upper bound. This holds at every stage.

The empty-word endomorphisms keeping every current marker form one scalar atom containing the identity. After a word of positive length or an arrow losing a marker it is impossible. Otherwise the target is $m\ge n$, and an arrow back to $n$ must preserve exactly all the $M_n$ markers and carry the necessarily discarded $M_m\setminus M_n$ into the ordinary pool. With the empty word, this describes exactly one return kind. Thus the original atom is strong, giving necessary Strong Actuality.

These are ordinary mathematical proofs, with independent review of the two successive tests, uniform pin reduction, exact powers and modal separation.
