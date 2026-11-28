# Rigid relations in the multiset models

The [multiset word model](finite-multisets-free-words.html), its [involution variant](finite-multisets-free-words-involution.html) and the [two-colour variant](two-colour-multisets-with-a-word-guard.html) all satisfy necessary Tame Rigidity and necessary Inextensible Comprehension. Both rigid power principles fail in each model. The two uncoloured models satisfy necessary Rigid Rigidity and necessary Weakly Rigid Weak Rigidity. Both rigidity principles fail in the colour model.

## Testing a single arrow

Write $T_a$ for transport by the arrow $a$, and $F_a$ for the row of $F$ there. Each arrow is isolated by its word, total multiset size, and multiplicities on the finite support of the multiset. In the involution model also specify its bit. Thus the tester which omits a single tuple $b$ at $a$ and has full rows everywhere else is admitted.

Suppose $F$ is weakly rigid with current extension $E$. Weak persistence gives $T_a[E]\subseteq F_a$. If a tuple of $F_a$ lies outside $T_a[E]$, the tester which omits it necessarily holds of every original member of $E$ but misses this tuple, contrary to weak inextensibility. Therefore
$$
F_a=T_a[E]\qquad\hbox{at every arrow }a.
$$
Conversely these equalities imply rigidity. At any $a$, all subsequent rows are the exact images of $F_a$ by composition. Persistence follows directly, and a tester necessarily covering each current tuple covers every such image. There is just one object, so Tame Rigidity holds necessarily.

For Inextensible Comprehension take any current tuple set $E$. Use its exact images on the units and the empty row elsewhere. The units have multiset size zero and empty word, with either bit permitted in the involution variant. The profile is admitted. At a unit the single test for weak inextensibility follows from the exact images on the units, since the other rows are empty. A nonunit has only nonunit continuations and the relation becomes bottom. Thus it is inextensible.

## A power member without a rigid lift

Fix different one-letter words $d,k$. In the uncoloured model write $\kappa$ for the pin bound and partition the $\kappa^+$ multiset labels into $J$ and its complement of size $\kappa^+$ each. In the colour model choose $J$ of size $\aleph_1$ within one colour so that uncountably many labels of that colour lie outside $J$. Pins there are countable. For $i\in J$ choose pairwise distinct nonempty scalar profiles $q_i$ supported on degree-zero words. Use a further nonempty profile $q_*$ different from all those chosen, and write $q_i=q_*$ for $i\notin J$. Such profiles amount to arbitrary sets of words. There are $2^\kappa\ge\kappa^+$ of them in the uncoloured models, and at least continuum many in the colour model. Profiles in this construction ignore the optional bit.

For every multiset label $i$ define a proposition $x_i$ by the following table.

- At degree zero and word $vd$ it reads the truth value of $q_i$ at degree zero and word $v$.
- Its only other true address is degree one at the multiset $\delta_i$ and word $k$, with either bit if present.

This needs only the pin $\{i\}$. The $x_i$ are pairwise distinct by their degree-one marks. At the arrow $(0,d)$ their images are precisely $q_i$. Put $D=\{x_i:i\in I\}$ and prescribe $F_a=T_a[D]$. This profile has empty pin. Degree zero has just one multiset to test at any fixed word. At degree one, say $\delta_j$, all $x_i$ except $x_j$ become bottom. The residual of $x_j$ at $(\delta_j,w)$ is supported precisely at degree-zero words $v$ with $vw=k$, independently of $j$. At larger degrees every member becomes bottom. These equalities give admission and prove that $F$ is rigid by the first section.

Put $U=\{q_i:i\in J\}$. Its exact-image relation $H_U$ is admitted with empty pin, as all its members become bottom after any positive-degree arrow. It is a rigid subrelation of $T_{(0,d)}F$: on every further arrow its row is the image of $U$, a subset of the images of all the $q_i$.

Suppose a root weakly rigid $Y\le F$ had image $H_U$ at $(0,d)$. Exactness implies that the current row of $Y$ is precisely $\{x_i:i\in J\}$. Indeed, the $J$ labels are distinguished at $d$ and the remaining labels all have the excluded image $q_*$. At $(\delta_j,\epsilon)$ the row of $Y$ would then contain the particular nonzero degree-zero $k$-word proposition exactly for $j\in J$. For every candidate pin there are unpinned labels on both sides, in the same colour when applicable. Their degree, word, bit and pin observations coincide. Such a row profile is impossible. The tester omitting exactly $H_U$ at $(0,d)$ therefore necessarily accepts every current eligible subrelation and fails at that arrow. This refutes weak inextensibility of both power properties.

## The predicate of rigid relations

In the uncoloured models there is nevertheless a rigid preimage for every rigid relation $Z$ at every arrow $h$. On a relational input $x$ let $L_hx$ be its extension by empty rows off the right suffix of $h$: its row at $kh$ is $x_k$. Cancellation makes this well defined. The finite multiset support of $h$ together with the pin of $x$ pins this section. On the sole individual let $L_h$ be the identity. In describing the optional group bit one can either strip it in the section or use equivariance under the bit unit.

For a source arrow $a$, if its word and the word of $h$ are incomparable for the suffix relation, $T_aL_hx$ is bottom for every relational $x$. Otherwise cancel the common shorter suffix from their words and the coordinatewise minimum from their multisets. Denote the residuals on the $a$ side and the $h$ side by $A,H$, respectively. In the optional bit put the difference of the old bits into $A$ and use the unit bit in $H$. Directly comparing the row at each further arrow gives
$$
T_aL_hx=L_H(T_Ax).
$$
Indeed a future $k$ with $ka$ in the right suffix of $h$ has exactly the residual multiset and word required to lie in the right suffix of $H$. Writing $k=lH$ gives $ka= lAh$. The common suffix cancellation and coordinatewise subtraction give the converse and uniqueness. The identity holds for individuals as well.

With $V$ the current row of $Z$, take the source tuple set $E'=L_h[V]$, using the section at each input type. Its exact-image profile is admitted. For comparable words its row at $a$ is $L_H[Z_A]$, using the exactness of $Z$. At equal word and degree, agreement of the multiset coefficients on the pin of $Z$ and the finite support of $h$ gives the same $H$, the same degree and word for $A$, and agreement on the pin of $Z$. In the incomparable case the row is empty if $V$ is empty and otherwise contains only the tuple of relational bottoms and sole individual values. Thus this profile is rigid and its transport at $h$ has the same row as $Z$. Since both relations are rigid they are equal as entities. All proper transports of a rigid relation remain rigid, so the predicate of rigid relations itself has exact images and is rigid. Weak rigidity agrees with rigidity at every arrow, giving the weak predicate principle too.

In the colour model there is a proposition $p$ with no preimage at its distinguished letter $h$, as shown in the model's Barcan counterexample. Its haecceity is rigid at that object. If an old weakly rigid relation transported to that haecceity, its current members would project onto $\{p\}$ by exactness, furnishing a preimage of $p$. A tester omitting just that haecceity at the isolated address $h$ therefore defeats weak inextensibility for the predicate of rigid relations and for that of weakly rigid relations.

The exact-image and power arguments in the colour setting also have an independent proof using the missing scalar and its singleton-arrow atoms. The two-word argument above gives the same verdict in models with surjective transport. OpenAI Codex (GPT-6), prompted by Daniel Kodsi, 27 November 2026. Two further OpenAI Codex agents independently checked the tuple-deletion and two-word arguments.

A separate GPT-6 research group independently obtained necessary Tame Rigidity and the two power failures for the two-colour variant.
