# An atomless Maximalist point with both rigid powers

Work in ZFC. The model combines the finite-orbit loop action from [[cantor-copies-of-a-signature-root]] with the [[reduced-power-retraction]]. It gives signature Possibility+, Atomlessness and Weakly Rigid Power at the same point. Every weakly rigid bound there has externally finite current extension.

## Profiles and histories

Let $G=2^\omega$ be the Cantor group, and $X$ a second copy of Cantor space. Fix a pointed signature Possibility+ model $K$. For the stated finite-individual verdict choose the signature-definable root with a single propositional constant and its one auxiliary individual marker. The individuals at the initial kind $r$ are those of $K$, fixed by the $G$-action. At $s$ include these and one new individual. Let $j$ retract that inclusion and send the new individual to the marker. At relational type $\tau$ let $A_r,A_s$ denote the target tuple spaces in the two base kinds, determined at the lower argument types. Set
$$
 \begin{aligned}
 R_\tau={}&\operatorname{LC}(G,\mathcal P(A_r))\times
  \operatorname{LC}(G,\mathcal P(A_s)^\omega/{=^*})\times
  \operatorname{LC}(X,K_\tau),\\
 S_\tau={}&\mathcal P(A_s)\times R_\tau.
 \end{aligned}
$$
The value spaces are discrete. Equality in a reduced sequence factor means cofinite equality of its whole rows. At $r$ a loop $g$ right-translates the first two functions and fixes the old section. Each entity has a finite orbit, since its two locally constant functions on compact $G$ are constant on cosets of an open subgroup of finite index. Every current row is admitted using a constant first function.

For $x$ at $r$ choose representative rows $U^x_i$ of the value of its second function at the identity loop. Put $h_i x=(U^x_i,x)$ at $s$, with $j$ selecting the return coordinate. At the individual type use the inclusion and its stated retraction. An ordinary exit $p_v$ for $v\in X$ evaluates the third function and takes individuals identically to $K$. Interpret the public name with a constant old section having its given $K$ interpretation; its values elsewhere follow transport along the history. The original signature Possibility+ witnesses are accessible after an ordinary exit and the individual side condition is preserved there.

Use the finite histories of the reduced-power retraction. At an $r$-stage $R^I/D$ allow every $G^I/D$ loop, entrances to the Fubini product obtained by choosing a free ultrafilter on $\omega$ separately at each index, and an exit to $K^I/D$ for every indexwise choice $v_l\in X$. Each entry acts pointwise by $h_i$, and each $s$-return by $j$. In the old ultraproduct retain all arrows of the entire typed action structure, also varying by index. Distinct new entities separate by a loop row, by one of the reduced coordinates after an appropriate loop and entry, or by an old section and its continuation. At an iterated stage make the witnessing choices indexwise.

For an abstract at $r$, evaluate its current extension on the parameters after each loop $g$. For its $g$-indexed germ evaluate the entire $s$ row on $h_i$ of the loop-translated parameters. Their joint loop orbit is finite and the tuple of translated parameters is locally constant, so both functions just constructed are locally constant into their displayed discrete ranges. At $v$ apply the old evaluation on the projected parameters; that whole value is locally constant. At $s$ use the current row of the abstract and its $r$-denotation on the returned parameters. The $r$ case needs only current evaluations of proper subterms. The return coordinates agree by $jh_i=1$. Comparison of entire entrance rows is cofinite at each fixed loop and hence also along the varying products. This verifies term transport, arbitrary target arguments in a lambda and the pointwise Łoś computation of current truth throughout the histories.

## Finite weakly rigid bounds

If $F$ is weakly rigid at $r$ and its current extension is infinite, choose $x_0,x_1,\ldots$ from it in pairwise disjoint $G$-orbits, which is possible because each orbit is finite. For each $n$, weak persistence puts $h_i x_n$ in the $i$th row of the identity-loop germ of $F$ cofinitely often. An infinite exceptional set could be used for a free-ultrafilter entrance. Choose $k(i)\le i$ tending to infinity modulo finite sets such that $h_i x_{k(i)}$ belongs to that row cofinitely often: take the greatest $k\le i$ for which the first $k+1$ membership tests all succeed when there is one.

Use a tester with current loop rows full, constant old section top, and germ at every loop given by the same sequence omitting $h_i x_{k(i)}$ on the good indices only. Every current tuple $x$ necessarily passes the tester. At a first entry after any loop, $h_i(gx)=h_ix_{k(i)}$ would require $gx=x_{k(i)}$ by the return. The finite orbit of $x$ meets at most one of the chosen orbits, and the corresponding exceptional indices are finite. A return restores the loop-translated diagonal of $x$; all later loop choices, including varying choices in the iterated products, still lie in that same ground orbit. The excluded indices can therefore be bounded by the same finite set at every entry. At an old exit the tester is top. But at the first free-ultrafilter entrance the moving tuple belongs to $F$ and fails the tester. This contradicts weak inextensibility.

Thus each weakly rigid bound has a finite current extension, hence is the rigid finite union of its tuple-haecceities and has both rigid canonical powers by [[internally-finite-rigid-power]]. This uses current finiteness of the weakly rigid bound itself.

Local Weakly Inextensible Comprehension fails. For a weakly inextensible $Y$ with current extension $E$, take any $a\notin E$. The tester whose loop row at $g$ omits only $ga$, and whose germ and old sections are full, necessarily accepts all of $E$. Its loop table is locally constant by the finite orbit of $a$. Thus for all $g$, the row of $Y$ at $g$ lies in $g[E]$. Some open subgroup fixes the loop table of $Y$ at the identity, giving $E\subseteq g[E]$ there, and hence equality by inversion. Now take the actual truth extension on propositions. Its stabilizer is trivial: any nonidentity $g$ is distinguished from the identity by a clopen scalar loop table. The trivial subgroup is not open in $G$, excluding a weakly inextensible coextension.

The propositional Barcan counterexample uses the tester with all loop rows and old section top and with germ at every loop given by $h_i[R_t]$. It necessarily accepts each source proposition, including after any loop and return. At each first entry there is a new $s$ proposition with a fixed return value but the opposite current bit to the prescribed entrance row for that value. Its class fails the tester.

## Necessity operators

At $r$ the two-hat and 5 modalities agree with truth on every root loop. For the two-hat forward direction, each true guard $q$ at $r$ is ND-possible after any loop $g$: for any further true test, use the inverse loop to realize $q$ and the loop back to realize that test. Thus a two-hat necessity holds on every loop. Conversely let $w$ have full root loop table and both other coordinates bottom. Its image at an $s$ entry is ND-impossible, since a current-only truth there becomes bottom at the return, and at all old exits $w$ is bottom. At every intervening $r$-return the original parameters are diagonals up to indexwise loop translation. A proposition true on every original loop is true there. Hence $w$ is a two-hat guard for that proposition.

For 5-necessity take the operator testing truth on all loops at $r$. Give it the invariant loop table testing that the scalar input's loop table is full, and at every entrance row test the current truth of the $s$ input. Its old section is the identity operator of $K$. At an $r$-stage it has the all-loops interpretation on the group ultrapower. At an $s$-stage and in $K$ it acts at current truth as identity. It is necessarily N, K and B: the all-loops accessibility is a group and identity at the other kinds satisfies these laws directly. This S5 operator bounds 5-necessity above by all-loop truth, while the general two-hat bound gives the converse. The true $w$ is false at an entrance where every current truth is possible by the return, so $w$ is not ND-necessary. A proper clopen loop truth containing the identity witnesses failure of Truth implies 5-necessity.

## Boolean and current structure

At $t$ the order is componentwise in
$$
 \operatorname{Clop}(G)\times
 \operatorname{LC}(G,\mathcal P(\omega)/\mathrm{Fin})\times
 \operatorname{LC}(X,K_t).
$$
A nonzero clopen patch in any coordinate can be split in the Cantor parameter. This gives Atomlessness, including failure of Actuality. The scalar loop-coordinate clopens whose first one has even index have no supremum as a family: any clopen upper bound contains the all-zero point and therefore includes an entire unwanted odd-index cylinder that can be removed. The family and its injection into distinct Frege numerals at $t$ have admitted current rows. This refutes both countable and propositional Boolean Completeness.

Current rows give arbitrary graphs and hence well-orders and transversals by external choice. There is one individual and infinitely many scalars. The actual property of the standard Frege numeral values is an available inductive test, so every current number is a standard iterate. It follows that the scalar domain has no Frege finite cardinality.
