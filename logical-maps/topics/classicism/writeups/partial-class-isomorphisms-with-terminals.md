# Partial class isomorphisms with terminal exits

A point satisfies Mathematical Possibilism and the necessary forms of BF, Tame Rigidity, Inextensible Comprehension and the collapse of ND-necessity to truth. Every atom at every type is strong. Nevertheless, at this point no property selects one representative of each coextension class of propositional properties.

## The action

Fix an infinite $\kappa\ge\aleph_0$. Partition an auxiliary set $A$ into $\kappa^+$ equivalence classes of size $\kappa^+$. Write $G$ for its class-preserving automorphism group, permitting permutations of the set of classes. A coefficient $h$ is a partial injection on $A$. There must be a permutation of classes under which the live elements of every source class are mapped bijectively onto its entire assigned target class. In particular every target point has a unique live preimage. Compose partial maps, with lost inputs staying lost. The composite still maps a live subset bijectively onto each assigned class. Every partial prescription on at most $\kappa$ inputs, including any specified deaths, extends to a coefficient provided its live part is injective and preserves and reflects equivalence. First extend the matching of classes to a permutation, then fill out the live partial bijections using the $\kappa^+$ unrestricted points per class. When there are no prescribed deaths the extension can be taken in $G$.

Use these maps as loops on $r$. In addition, for each natural number include one exit from $r$ to its own terminal object. Each exit absorbs all loops, and each terminal has only its identity. The actual individual sort is a singleton everywhere. Terminal types form the ordinary full extensional hierarchy over one individual; all are finite. At a relational type, a source entity consists of an ordinary loop profile together with an arbitrary whole value at each terminal. The ordinary rows are left-equivariant under $G$. They have one pin $N\subseteq A$ with $|N|\le\kappa$: coefficients having the same partial values on $N$ have equal entire rows. Transport along a loop precomposes ordinary coordinates and preserves every terminal coordinate. Agreement on a pin persists under postcomposition, and the image of its live part pins a transported profile. Therefore ordinary abstraction on the recursive tuple domains has the union of the parameter pins as a pin and is equivariant. Its terminal coordinates are the ordinary terminal interpretations on their parameters. These facts give the action law for typed terms, including quantification and abstraction, and a differing row is observable by application at the corresponding arrow.

## BF and the local modal test

All actual maps are onto at every type. For a target relation $Y$ at a loop $h$ choose an ordinary pin $T$. Give a source relation the same terminal components as $Y$. At a coefficient $f$, use the row of $Y$ at any permitted $k$ such that
$$
 k(y)=f(h^{-1}(y)) \quad(y\in T),
$$
allowing both sides to be undefined. The prescribed live values form a partial class isomorphism on $T$, because the unique live inverse of $h$ preserves and reflects classes. Thus a $k$ exists, and all choices give the same row. This rule is equivariant and pinned by $h^{-1}[T]$. At $f=lh$ it gives the row for $lY$, so the source relation transports along $h$ to $Y$. The individual sort is immediate and the independent terminal projections are onto. This proves necessary BF.

For a truth $p$ at $r$ with pin $N$ let $q$ say that every point of $N$ is live, and give it bottom at the terminals. This is true. If $q$ remains possible after a loop, every member of $N$ is still live. That loop agrees on $N$ with a group automorphism, so $p$ holds there by equivariance. At the terminal exits $q$ is impossible. Thus $q$ witnesses the ND-necessity of $p$. Each terminal is classical, so the schema holds necessarily.

## Exact images of weakly rigid relations

Let $F$ be weakly rigid at $r$ with current tuple set $E$ and pin $N$. For any enlarged pin $N'\supseteq N$, form a profile whose ordinary row at $h$ is
$$
 B_h=\bigcup_{t|_{N'}=h|_{N'}}t[E].
$$
Its terminal rows are the images of $E$ at each terminal. This is an admissible equivariant $N'$-pinned profile, and the terminal types admit all of the displayed images. It necessarily accepts every current member of $F$, so weak inextensibility gives $F\le B$. Conversely weak persistence gives $t[E]\subseteq F_t=F_h$ for every displayed $t$, including the direct terminal images in their own rows. Hence $F=B$.

For one fixed $h$, add to $N'$ one live $h$-input in every class meeting $N$. Take a tuple $tz\in B_h$ with $z\in E$ and let $L$ be a support of $z$. On $N$ prescribe $u$ to be the identity. For $l\in L\setminus N$ put $u(l)=h^{-1}(t(l))$ if $t(l)$ is live, otherwise leave it undefined. The class permutation of $h^{-1}t$ fixes each class meeting $N$ because of the extra live representatives. No prescribed live value from outside $N$ can equal $n\in N$: if $h(n)$ is dead it has no live inverse there, and if it is live then $t(n)=h(n)$ and injectivity of $t$ rules out this collision. The prescriptions therefore extend to a permitted $u$. The arrow $hu$ agrees with $t$ on $L$. Since $u$ fixes $N$, weak persistence puts $uz$ in $F_u=E$. Thus $tz=h(uz)\in h[E]$.

It follows that $F_h=h[E]$ at every loop, with exact images also at the terminals by the saturation equality. Composition makes these equalities hereditary; exact images give weak inextensibility and persistence at all successors. All weakly rigid relations at $r$ are rigid. The terminal claim is immediate, giving necessary Tame Rigidity.

## An inextensible coextension

Let $E$ be the current row of any source relation and $N$ one of its pins. Every group element fixing $N$ preserves $E$. Give $Y$ empty terminal rows. At $h$ use the row $gE$ if all of $N$ survives and $g\in G$ agrees with $h$ there; otherwise use the empty row. The result is independent of $g$, equivariant, $N$-pinned and coextensive with $E$.

For a loop live on $N$, let $j=h^{-1}$ on all of $A$, mapping into the live domain of $h$. The injection $j$ permutes classes and need not be a permitted surjection. For a target tuple $y\in gE$, choose a group automorphism $v$ agreeing with $j$ on a support of $y$ together with $hN$. Then $vg$ fixes $N$, so $vy\in E$; moreover $hv$ agrees with the identity on the chosen support of $y$, so $h(vy)=y$. Thus every loop member of $Y$ is the image along that same loop of a current member of $E$. Its terminal rows are empty. This proves weak inextensibility. When $h$ stays live on $N$, the whole $hY$ equals $gY$ by pinning and so is weakly inextensible by group transport. When $h$ kills a point of $N$, every continuation has empty row. This gives inextensibility, at $r$ and necessarily. It uses only actual automorphisms $v$ on the specified supports.

## Failure of Transversal and source atoms

For each site $a$ let $p_a$ be the scalar reporting that $a$ is live, with all terminal coordinates bottom. These are distinct and $g p_a=p_{ga}$. For any class $C$ and $c\in C$, the property of propositions having at $h$ the codes $p_z$ with $z$ in the class of $h(c)$, and empty when $c$ dies or at the terminals, is pinned by $c$. Its current row is $\{p_z:z\in C\}$.

A proposed Transversal has a pin $P$. Pick a class $C$ disjoint from $P$. Its unique selected representative $Y$ must be fixed by group elements fixing $P$ and preserving $C$ setwise. Enlarge a pin $S$ of $Y$ to contain $P$. Within each class move $S\setminus P$ off $S$ using such a group element. The moved set $S'$ is another pin of $Y$. Take a permitted partial surjection fixing $S$ and undefined on $S'\setminus P$. Such a prescription extends even when $S$ is infinite, since each ordinary pool has cardinal $\kappa^+$. Its row for $Y$ is therefore the class of codes of $C$. Postcompose by a permutation fixing $P$ and swapping $C$ with a fresh class. The two coefficients agree on $S'$, while target equivariance requires different rows. This refutes Transversal. The proof adapts the [bounded partial-injection argument](bounded-partial-injections.html). Relational Choice fails as well: the serial invariant relation on codes asks each to select another member of its class, acting as equality on noncodes. A fresh transposition fixing the input and the selector pin moves any chosen classmate.

Every occupied ordinary row splits by testing whether one fresh site is live. Both possibilities extend its prescribed values on a pin and retain the whole tuple at issue. Thus every source atom is supported on a single terminal and a single terminal tuple. It transports to an atom or bottom along all arrows, so every atom is strong. There is no actual propositional atom at $r$, since an actual truth has a nonempty ordinary row.

## Revised Mathematical Possibilism

All individual domains are singletons. The uniform individual order/field threshold tables thus give a finite inexact-ordinal bound. A rigid family whose current members belong to that finite list has at every arrow exactly their images by the preceding rigidity result. Its limit again has a uniform finite threshold table. This is the singleton case of the map's [bounded individual threshold argument](../index.html#arg-forcing-possibilism-countably-many-arrows).

Any countable collection of current entities has a common pin fixing all of them pointwise. All external relations on those points then occur as current rows: extend a set invariant under the stabilizer of $N$ by the $gE$ table used for inextensible coextensions. An infinite current carrier therefore has a countably infinite subset larger than the finite ordinal benchmark. Each strictly smaller subset is finite, since all comparison graphs on this countable subset are admitted. Its powerset can be coded on a finite, strictly smaller set inside the countable subset. Thus an infinite carrier fails revised smallness. Every finite Boolean algebra is isomorphic to the interval below a union of finitely many terminal bits, and the finite isomorphism graph is admitted by the same common-pin argument. Mathematical Possibilism holds at $r$.

The model combines the truth-collapse method of [class-reflecting surjections](symmetric-class-reflecting-surjections.html) and the coextension obstruction of bounded partial injections. The surjective partial maps, the exact-image and inextensibility proofs, and their combination with terminal Possibilism have ordinary proof certificates.
