# ND, two-hat and 5-necessity at two symmetric paired sites

At \(W\), ND-necessity and two-hat necessity coincide. Every truth is 5-necessary, and one truth fails two-hat necessity. At \(V\), every truth is two-hat necessary, and some truth fails ND-necessity. Since the two objects reach each other, Truths are 5-necessary holds necessarily at both.

Use the block maps in [Dorr’s paired-individuals model](../index.html#model/paired-individuals-two-object) and impose full target block-permutation symmetry, as in the [symmetric integer-stage construction](symmetric-integer-paired-stages.html). There is just one coordinate. \(W\) has countably many two-element blocks. \(V\) adds one singleton \(\{\star\}\). All maps that send each block into a block are arrows, with ordinary composition. The symmetries at each object are the permutations of blocks and their elements that preserve block sizes. A relational entity is an equivariant table of tuple rows on the outgoing arrows, pinned by finitely many source sites. Transport is precomposition. These are symmetric ideally-full domains. Take the original sites as individuals or use a singleton individual at both stages. Purely relational names can be interpreted by the top elements. The modal calculations apply to both individual conventions.

Write \(\Box_d=\Box_{\ne}\) and \(\Box_h=\hat{\hat\Box}\). The two guards used below are
\[
 \Box_d p\ \leftrightarrow\ \exists q\,(q\land\Box(\Diamond q\to p)),
 \qquad
 \Box_h p\ \leftrightarrow\ \exists q\,(q\land\Box(\Diamond_d q\to p)).
\]
At an arrow \(h\), \(\Diamond_d q\) says that for each target truth \(t\) there is a continuation \(k\) with \(q\) true at \(kh\) and \(t\) possible after \(k\). Pins may be enlarged to unions of entire blocks, and may include \(\star\) at \(V\). A true proposition is true at every target symmetry of its own object by equivariance. [Modal definitions and comparisons](../index.html#background/varieties)

## At the object with ordinary doublets

For every true \(q\) at \(W\) we construct a true \(r\) there with \(\Box(\Diamond r\to\Diamond_d q)\). Take a finite block-closed pin \(N\) for \(q\), and let \(r\) pick out endomorphisms of \(W\) injective on \(N\). It is a true equivariant scalar. If \(\Diamond r\) at \(h:W\to B\), then \(h|_N\) is injective. Its source blocks therefore map bijectively onto distinct ordinary doublets at \(B\).

Given any true \(t\) at \(B\), take a finite block-closed pin \(T\), including \(\star\) if present. Choose \(k:B\to W\) inverse to \(h\) on \(h[N]\). Map the other ordinary blocks of \(T\) bijectively onto fresh disjoint doublets outside \(N\); send the target singleton, if present, to a member of a further fresh doublet. Extend to an arrow on the remaining sites. Then \(kh|_N=1|_N\), so \(q\) is true at \(kh\). There is also an arrow \(v:W\to B\) with \(vk|_T=1|_T\). Use the inverse on the chosen ordinary blocks and collapse the separate doublet onto \(\star\) when needed. Hence \(t\) is possible after \(k\). This gives \(\Diamond_d q\) at \(h\) and proves the guard assertion. Applied to a witness for \(\Box_h p\), it yields \(\Box_d p\). The converse is a theorem of C.

Let \(P\) hold at exactly the arrows ending at \(W\). It is true at \(W\). The inclusion \(u:W\to V\) has a retraction to \(W\), so it sees the true guard \(r\) just used, for **every** finite \(N\). The doublet argument therefore gives \(\Diamond_d q\) at \(u\) for every true \(q\) at \(W\). But \(P\) is false there. This proves \(\neg\Box_h P\).

To prove \(\Box_5P\), use the property \(Y\) of propositions accepting everything at \(W\)-targets and accepting at \(V\)-targets exactly those propositions with a pin omitting \(\star\). This condition is equivariant under the target symmetries. At \(V\) the proposition of endomorphisms that send \(\star\) to \(\star\) has no such pin: moving only \(\star\) changes its truth. Thus \(\forall z\,Yz=P\) as a whole proposition.

For \(z\) at \(W\) take its finite saturated pin \(N\) and the true guard \(r\) above. If \(\Diamond r\) at \(h\), then \(h\) is injective on \(N\). Each doublet in \(N\) maps to an ordinary doublet, so \(h[N]\) is a pin for the transport of \(z\) omitting \(\star\). Hence \(\Box_d(Yz)\) and therefore \(\Box_5(Yz)\) at \(W\). The general Barcan theorem for \(\Box_5\) gives \(\Box_5\forall z\,Yz\), or \(\Box_5P\). This adapts the single-coordinate pin test of the [paired model](../index.html#model/paired-individuals-two-object-surjective).

Now take any true \(p\) at \(W\) and use the same guard for a saturated pin of \(p\). An endomorphism seeing that guard agrees on the pin with a block permutation, since the two-element blocks there go bijectively onto distinct two-element blocks. Hence \(p\) is true at that endomorphism by equivariance. At every other target \(P\) is false. This gives \(\Box_d(P\to p)\), and thus \(\Box_5(P\to p)\). Normality of \(\Box_5\) and \(\Box_5P\) yield \(\Box_5p\).

## At the object with a singleton

For a true \(p\) at \(V\) choose a finite block-closed pin \(N\) containing \(\star\). Let \(q\) pick out endomorphisms of \(V\) that are injective on \(N\) and fix \(\star\). It is true, pinned, and target-equivariant. If \(\Diamond_d q\) at \(h\), then \(\Diamond q\) there, forcing \(h|_N\) to be injective. If \(h(\star)=b\) in an ordinary doublet \(\{b,b'\}\), use at the target the true test that the two images of \(b,b'\) are distinct. Any \(k\) making \(q\) true at \(kh\) would send \(b\) to \(\star\), collapsing the entire doublet. The distinctness test would then be impossible. Hence \(h\) lands at \(V\) and fixes \(\star\). Its restriction to \(N\) extends to a block symmetry. Thus \(p\) is true at \(h\), proving \(\Box_h p\). In particular every truth is 5-necessary at \(V\) also.

For the strict comparison let \(T\) hold exactly at the arrows ending at \(V\). Given any true guard at \(V\), take an ordinary doublet outside its pin and use \(h:V\to W\) that sends \(\star\) to one of its sites and fixes ordinary sites. A return collapsing that doublet onto \(\star\) fixes the pin in the composite, so the guard is possible at \(h\). Since \(T\) is false there, \(\Box_d T\) fails. Finally, the entrance \(V\to W\) reaches a point where the true \(P\) fails \(\Box_hP\). Hence the necessitation of Truths are two-hat necessary is false at either object.

The block maps and the modal tests originate in the paired-site work of 29 October 2026. OpenAI Codex (GPT-6), prompted by Daniel Kodsi, established the one-coordinate comparison on 27 November 2026.
