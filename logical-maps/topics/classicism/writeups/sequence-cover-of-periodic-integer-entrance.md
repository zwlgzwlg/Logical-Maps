# Local Strong Atomicity with higher-type Atomicity failing at a later point

There is a point where every nonzero relation contains a strong atom and every type satisfies Barcan. Scalars are strongly atomic at every accessible point. At one accessible point, however, a property of individuals contains neither an atom nor a self-atom.

Take the [periodic integer entrance](periodic-integer-entrance.html), with old objects $s,t$ and entrance $h:s\to t$. Each old object has the integer translations as loops, with $gh=hg$. At $s$ there is one individual. At $t$ the individual domain is $\mathbb Z\sqcup\{*\}$, with translations fixing $*$, and the type hierarchy is classical and full. A relation at $s$ has a current row and a terminal row, each fixed by some finite-index subgroup of the translations. The entrance projects to the terminal row. In particular every whole entity at $s$, and every finite tuple of such entities, has finite orbit.

Adjoin $r$ with only its identity entering it. Freely add an arrow $a:r\to s$ and, for each natural number $n$, a separate arrow $b_n:r\to t$, together with their old postcomposites. In particular $ha$ and the $b_n$ are distinct. An individual at $r$ consists of the individual at $s$ and a sequence of individuals at $t$ equal to $*$ except at finitely many indices. Its projections are its values under $a$ and $b_n$. Each relational type at $r$ consists of triples

$$
    (R,X,(Y_n)_{n\in\mathbb N}),\qquad
    X\in D(s),\quad Y_n\in D(t),\quad Y_n=hX
    \text{ for all but finitely many }n .
$$

Here $R$ is an arbitrary set of current argument tuples of the appropriate types. The old components are whole entities. Transport along $a$ gives $X$, and transport along $b_n$ gives $Y_n$. Interpret individual names by the sequence constantly $*$ and relational names by top.

The root row of a lambda abstract is the set of current tuples satisfying its matrix. At each entrance use the old abstract on the transported parameters. Outside the union of the finite exception sets of its parameters, the assignments at $b_n$ and $ha$ agree as whole entities at the same old object. The old abstract therefore agrees there on every tuple, including newly quantified arguments, with one exception set for the whole abstract. Old term transport determines its other rows. This verifies closure and naturality. Distinct entities differ in their current row or an old projection and hence are distinguishable. The order on relations is inclusion in the current row and in every old coordinate.

## Strong atoms at the new root

Let $F=(R,X,(Y_n))$ be nonzero. There are three ways to find a strong atom below it.

* A tuple in $R$ gives the singleton current row with every old coordinate bottom. It is an atom at $r$ and disappears under every proper arrow.
* If $X$ has a tuple in its current row, let $C$ at $s$ have just that tuple in its current row and empty terminal row. Its tuple has finite orbit, so $C$ is admitted. Then $(\varnothing,C,(0)_n)$ lies below $F$. It is a root atom by coordinate order. Its translates at $s$ are singletons in the current coordinate, and it is bottom at $t$.
* If some $Y_n$ is inhabited, take a singleton subrow there and bottom elsewhere, including at $s$. This is a root atom, as well as a singleton or bottom after every proper arrow. If $X$ is nonzero solely in its terminal row, the eventual equality supplies an inhabited $Y_n$.

Thus every nonzero relation at $r$ contains a strong atom. The scalar algebra at $s$ is the algebra of two bits with both atoms strong, and the terminal scalar algebra is the two-element algebra. This proves necessary Strong Atomicity at propositional type. All atoms at $r$ are strong by the density just proved, and all old atoms are strong by the periodic model's orbit calculation.

At $s$ take the property with empty current row and terminal row $\mathbb Z$. Every nonzero relation below it has a nonempty periodic subset of $\mathbb Z$ as its terminal row. A residue class in this row splits under passage to a subgroup of twice the index, so the relation cannot be an atom at $s$. Its terminal row contains infinitely many integers and hence is instantiated without being an atom at $t$. This rules out a self-atom below the same property. Both higher-type density failures are therefore accessible from $r$.

## Barcan and scalar completeness

At every type each entity at $s$ lifts along $a$, by a sequence constantly equal to its terminal projection. Each entity at $t$ lifts along any specified $b_n$, by a one-entry modification. For a possible witness to a root predicate at $gha$, where $g$ is a translation, choose $n$ outside the exception set of the predicate. Its value at $gb_n$ is then its value at $gha$, and every witness lifts along $gb_n$. At $ga$ and $gb_n$ use surjectivity directly. The identity case is immediate. This proves the dual Barcan Formula at every type at $r$. Both old objects satisfy propositional Barcan. At $s$ the singleton terminal property $\{0\}$ has infinite translation orbit and escapes the source tester for periodic properties, giving the old failure of relational Barcan.

For each $n$ write $p_n$ for the isolated root scalar supported at $b_n$ and its translates. The family of the $p_{2n}$ and its injection into the standard Frege numerals at propositional type are admitted by full current rows. All these numerals exist and are distinct because the root scalar domain contains finite sets of every standard size. A join of this family would include every even coordinate and exclude every odd coordinate, since the complement of any odd singleton is an upper bound. That pattern fails eventual constancy. Thus Countable Boolean Completeness fails already for a family of propositions, as does propositional Boolean Completeness. Finally $p_0\lor p_1$ is a self-atom, since wherever it holds its transport is terminal top. It splits at the root into two nonzero atoms.
