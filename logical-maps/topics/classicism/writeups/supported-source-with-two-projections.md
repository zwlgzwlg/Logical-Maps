# Distinctness can persist while Rigid Power fails at a successor

At one point, things of every type that are distinct remain distinct, Actuality holds, and there is a transversal of coextension at every type. At a successor neither Rigid Power nor Weakly Rigid Power holds. The obstruction is a rigid binary-coordinate graph whose two projections cannot both be represented at the earlier point.

## The two-object model

There are objects $w,v$, an arrow $f:w\to v$, two arrows $j_0,j_1:v\to w$, and the equations $j_i f=1_w$. The other endomorphisms at $v$ are $fj_0,fj_1$ and there are no other arrows. The individuals at $w$ form $A=\mathbb N\times\{0,1\}$. The individuals at $v$ form $A^2$, with $f$ the diagonal and $j_i$ the two projections. Let $G$ independently exchange the two members of each pair in $A$; it acts diagonally on $A^2$. A set or entity is supported if fixing finitely many pair indices pointwise suffices to preserve it.

For a relational type with input tuple domains $D^w,D^v$, define

$$
D_\tau(w)=\{(S,U): S\subseteq D^w,\ U\subseteq D^v,\text{ and one finite pin supports both}\},
\qquad
D_\tau(v)=\mathcal P(D^v)\times D_\tau(w)\times D_\tau(w).
$$

The group acts on each coordinate by its action on lower types. At $v$ the first coordinate is an unrestricted subset. Application reads the first coordinate at either object. On these carriers set

$$f(S,U)=(U,(S,U),(S,U)),\qquad j_i(B,y_0,y_1)=y_i.$$

The maps are equivariant and satisfy the category equations. A root pair gives its current row at $1_w$ and the row $U$ at $f$. A triple at $v$ supplies its current row and the rows of each of its two $w$-coordinates, giving its values at all five arrows out of $v$. Thus distinct relational entities are distinguished at some continuation and tuple.

For a lambda at $w$ take the current extension of its body at $w$ and the extension at $v$ on the $f$-images of the parameters. The ordinary group action commutes with evaluation: it preserves the arrow maps, equality, application, and permutes the entire domains of bound variables at each object. Hence the finite union of the parameters’ pins supports both complete rows. For a lambda at $v$ take the actual extension of its body, and take the two whole $w$-lambdas on the parameter lists transported by $j_0,j_1$. The $f$-image of a $w$-lambda agrees with the corresponding $v$-lambda even in its two return coordinates because $j_i f=1_w$. These clauses give the term-and-transport induction at all types. No finite pin is imposed on the first row at $v$. All original relational names may denote top and any individual names may use a fixed individual at $w$ and its diagonal at $v$.

Every map out of $w$ is either the identity or $f$, and $f$ has a left inverse at every type. This proves unboxed ND there. Its propositional algebra is $2\times2$, so the identity-only proposition is a true atom. At each relation type the pair $(S,\varnothing)$ represents the current extension $S$. The current class of precisely those pairs is $G$-invariant, so using it as a first row with empty $v$-row gives an admitted predicate selecting exactly one representative of each actual coextension class. This is Transversal as defined on the map.

## A rigid bound and its two projections

Let $E\subset A$ consist of both members of each even-indexed pair. It is $G$-invariant. Choose a bijection $b:A\to A$ sending $E$ onto $\mathbb N\times\{0\}$, which has no finite support. Write $\Delta S=\{(a,a):a\in S\}$. The individual property $U=(A,\Delta A)$ at $w$ has exactly the transported images of its current members at every arrow. The same holds of $Y=(E,\Delta E)$. A relation with this exact image property at every continuation is rigid: current members persist, and any tester holding necessarily of them must hold of all those images. The exact image property is hereditary by composition.

At $v$ take $F=(\mathrm{graph}(b),U,U)$. Its current row can be arbitrary. Its $j_i$-rows are the entire $A$, the projections of that graph, and its $fj_i$-rows are $\Delta A$. These are exactly the images under all the respective arrows. Hence $F$ is rigid. At $j_0$ the relation $Y$ is a rigid subrelation of $j_0F=U$.

If $Z\le F$ is weakly rigid at $v$, write $B'$ for its current row. For either projection $j_i$ we claim

$$(j_iZ)_{1_w}=j_i[B'].$$

Persistence gives inclusion from right to left. If $a\notin j_i[B']$, use the $v$-tester with full current row, with top in its other $w$-coordinate, and with $(A\setminus\{a\},A^2)$ in its $i$th coordinate. This is an admitted tester, since one pair index supports the deletion. Among the five arrows out of $v$ it excludes $a$ only in the current observation at $j_i$. Every member of $B'$ necessarily passes. Weak inextensibility therefore excludes $a$ from $(j_iZ)_{1_w}$, proving the equality.

If $j_0Z=Y$, this equality forces the first projection of $B'\subseteq\mathrm{graph}(b)$ to be exactly $E$. Hence its second projection is $b[E]$, which by the same equality is the current row of $j_1 Z$. Such a row must be finitely supported at $w$, a contradiction. Thus no weakly rigid subrelation of $F$ transports to $Y$ along $j_0$.

Finally use a tester on individual properties which is full at $v$, top at $j_1$, and at $j_0$ excludes only $Y$ in the current $w$-row, with full $f$-row. This is admitted since $Y$ is itself invariant. It holds necessarily of every current rigid or weakly rigid subrelation of $F$. At $j_0$, however, $Y$ is a rigid subrelation of the transported bound and the tester excludes it. Thus both power properties of $F$ fail weak inextensibility at $v$, giving the announced failures of the necessary principles at $w$.

## Both powers hold at the source

Let $F=(S,U)$ be any weakly rigid relation at $w$, with arbitrary input types. The tester with full current row and successor row $f[S]$ is admitted: $f$ commutes with the flips and $S$ has finite support. Every current member of $F$ necessarily satisfies this tester. Weak inextensibility gives $U\subseteq f[S]$, and persistence gives the reverse inclusion. Thus $F$ has exact images and is fully rigid. This proves Tame Rigidity at $w$.

Consider a weakly rigid $Z=(B',y_0,y_1)\le fF$ at $v$. Every tuple in $B'$ belongs to $f[S]$. As in the single-projection test above, the current row of $y_i$ must be $j_i[B']$: each tuple at $w$ has finite support, so deleting one tuple on the selected return is admitted. The successor row of $y_i$ must likewise be $fj_i[B']$. To see the reverse inclusion to persistence, consider any extra tuple in that row. Since $Z\le fF$, the tuple belongs to $f[S]$ and has finite support, even though the whole domain at $v$ can contain unsupported tuples. Use a tester full at $v$ and on the other return, whose selected $w$-coordinate has full current row and deletes just that tuple from its successor row. It excludes the tuple at $fj_i$ alone, contradicting weak inextensibility.

Both $j_i$ agree on $f[S]$. Hence $j_0[B']=j_1[B']=S'$ and $f[S']=B'$. The set $S'$ is the current row of $y_0$, so it is supported. The source relation $Y=(S',f[S'])$ is rigid, lies below $F$, and satisfies $fY=Z$ on all three coordinates. Every eligible successor subrelation is therefore the image of an eligible source subrelation, and every eligible source subrelation is itself rigid and stays eligible at $f$. Both the rigid and the weakly rigid power of $F$ have exact images on all arrows out of $w$, so are rigid there. This gives the two unboxed power principles at the very point where both necessary versions fail.

Boolean Completeness also holds at $w$. For any admitted family of source relations, its current extension is invariant under the flips fixing a finite pin. Take the union of its members in each of their two rows. Those same flips preserve the resulting pair, which is therefore a source entity. The order is inclusion in each row, making this pair the least upper bound.
