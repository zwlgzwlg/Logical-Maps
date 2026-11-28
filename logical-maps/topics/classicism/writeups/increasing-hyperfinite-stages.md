# Necessary Potential Infinity without Possible Infinity at propositional type

At every stage the propositions have a Frege-finite cardinality. Nevertheless every number at every stage counts a property of propositions at the next stage. This settles the necessary form of the question left by the [four-proposition entrance](absorbing-entrance-hyperfinite-group.html). It uses a different construction because a terminal hyperfinite group fails Potential Infinity at its own point.

## Stages and types

Work in ZFC. Let $K$ be the positive integers and $U$ a nonprincipal ultrafilter on $K$. Start with the set structure $M_{-1}=(V_{\omega+\omega},\in,U)$. All sets used in each fixed type and formula construction below have rank bounded by $\omega+d$ for some standard finite $d$. The required powersets, indexed products, quotient sets and separation instances therefore exist in this structure.

Choose successive elementary extensions $M_{-1}\preccurlyeq M_0\preccurlyeq M_1\preccurlyeq\cdots$. In $M_i$ choose $k_i$ realizing $k_i\in A$ for every $A\in U$ in $M_{i-1}$. The elementary diagram gives such an extension by compactness, since every finite intersection in $U$ is nonempty. The extensions may be externally ill-founded. Statements about their sets, elements, finiteness and ultrafilters always use their own membership relation. Each $k_j$ for $j>i$ belongs to every $U$-large set from $M_i$. In particular it exceeds every integer of $M_i$. The objects of the action category are the stages $i\ge0$. Its loops at $i$ are the cyclic group $G_{k_i}$ on $k_i$ elements as computed in $M_i$. There is one arrow $i\to j$ for each $i<j$, with the unique possible composites involving these arrows.

The following set definitions are uniform in $k\in K$ and are made inside each $M_i$. Put $D_e(k)=\{*\}$. For a relational type $\tau=\sigma_1\cdots\sigma_m t$ let
$$
 R_\tau(k)=\mathcal P\!\left(\prod_{a=1}^m D_{\sigma_a}(k)\right),
 \qquad
 D_\tau(k)=R_\tau(k)^{G_k}\times
              \left(\prod_{y\in K}R_\tau(y)\big/U\right).
$$
The empty product has one member, so a nullary row is a bit. This is a recursion on type. The actual domain at $i$ consists of the internal members of $D_\tau(k_i)$. Write a relation as $(A,[f])$, with loop rows $A(g)$ and a germ represented by $f$. At the current point application reads $A(1)$. A loop $g$ sends the first table to $v\mapsto A(vg)$ and keeps the germ. The arrow to $j>i$ sends it to the constant loop table with row $f(k_j)$ and the germ of the same function interpreted in $M_j$. Both are independent of the representative, since $k_j$ belongs to every earlier $U$-large set. Later transport discards the current table and keeps the germ again. Thus absorption and all composition laws hold. Individuals have their unique transports.

Unequal loop rows differ on a tuple at their stage. Unequal germs differ on a $U$-large set of indices. At $k_{i+1}$ their rows therefore differ on an actual target tuple, including at nullary types. Induction on type now identifies each record faithfully with its rows on all outgoing arrows.

## Term closure

We give the uniform evaluation argument since merely attaching unrestricted new higher types at later stages would not justify quantification. For a chosen representative of a parameter $a=(A,[f])$ put
$$
 a[y]=(\text{constant loop table with row }f(y),[f])\in D_\tau(y).
$$
Write $*[y]=*$ for individuals. Two choices for any finite list of parameters agree for $U$-almost every $y$. The specialization at a fresh future stage is independent of all choices. The germ of $a[y]$ is the original one, so its subsequent specialization uses that same germ.

Use fully applied atomic formulas and expand relational terms at their remaining arguments. Induct on syntax to define evaluation by set-theoretic formulas uniform in $k$ and the parameters. For a relation abstracted from a matrix, its loop row at $g$ consists of the target tuples satisfying the matrix at $k$ with the parameters transported by $g$. Its second coordinate is the germ of the function sending $y$ to the row of that matrix evaluated at $y$ with parameters $a[y]$ and every tuple in the corresponding domains at $y$. A finite change of representatives in this definition leaves the rows equal on a $U$-large set. Equivalently one can quantify over representatives and take the unique resulting germ. Fully applied predicates read their identity rows, identity compares the records of the arguments, and the current quantifier ranges over the entire internal $D_\sigma(k)$. The Boolean clauses are the usual ones. Ordinary necessity can be read as identity to top. Equivalently it tests every current loop and requires the future truth set to belong to $U$.

These clauses commute with transport. On a loop this is composition of the loop shifts, with the germ unchanged. At a strict arrow to $j$, elementarity interprets the same set-defined row function on all the target tuples at $k_j$, including new tuples. When the transported abstract is recomputed there, its current loop rows are constant because every loop fixes each transported parameter. The recomputed future row function uses the same parameter germs as the old one, so its germ is exactly the transported one. This proves the induction step for abstraction. The same computation gives residual rows in a partially applied relational expression. Together with the faithful row representation this gives the action-model closure and extensionality required by C. Give individual names the unique individual and relational names top at all stages.

## Exact number codes

The germ of a function to the two bits is a single bit. Thus the scalar algebra at stage $i$ is internally $\mathcal P(G_{k_i})\times\mathbf 2$, of finite size $L(k_i)=2^{k_i+1}$. To determine the native natural numbers without an assumption about external standardness, define for every internal natural $n$
$$
 r_n(y)=\{X\in D_{tt}(y): |X(1)|=n\}.
$$
Here $X(1)$ denotes the identity row of the first table. At type $(tt)t$ let $C_n(k)$ have $r_n(k)$ on every loop and the germ of $y\mapsto r_n(y)$. This particular representative specializes at every $y$ to $C_n(y)$ itself. The current row of native zero tests for zero instances, and its future rows make the same test, so $\mathbf0=C_0$. If the input is $C_n$, the successor matrix removes one member of an internal set and asks whether the remainder has size $n$. At each loop its current result is exactly $r_{n+1}(k)$, and the same calculation for the displayed representative gives $r_{n+1}(y)$ in the future row function. Hence $S C_n=C_{n+1}$ as whole entities, for every internal $n$. This calculation uses the internal finite-set theorem and applies without restriction to nonstandard $n$.

The internal set of the $C_n(k)$ is an available current predicate, using its set as the identity row and empty germ. It contains zero and is closed under successor. Conversely every admitted inductive predicate has an internal current row, which contains all $C_n(k)$ by ordinary induction *inside the stage structure*. Thus the native $\mathbb N_t$ consists exactly of these numbers. They are distinct because, for given internal $n\ne m$, the rows $r_n(y)$ and $r_m(y)$ differ on the cofinite tail where $L(y)\ge\max(n,m)$. Transport to stage $j$ takes $C_n(k_i)$ to $C_n(k_j)$ with $n$ interpreted by the elementary inclusion, as follows directly from the same uniform definition.

In $M_i$ the number $C_{L(k_i)}(k_i)$ counts the universal property of propositions. The Axiom of Infinity at $t$ therefore fails at every stage and its possibility fails. Given any $C_n(k_i)$, the next $k_{i+1}$ exceeds $n$. There an internal subset of $D_t(k_{i+1})$ of size $n$ exists and can be used as the identity row of a property. It is counted by the transported $C_n$. This proves Potential Infinity at every stage, hence its ordinary necessity at the designated one.

## Further verdicts

No signature sentence is contingent. The uniform evaluation of a fixed closed sentence with the designated names defines a subset of the positive integers in $M_{-1}$. Every $k_i$ belongs to that subset if it lies in $U$, and to its complement otherwise. All loops preserve the interpretations of the names.

At each stage Boolean Completeness holds at $t$. Every admitted family has an internal current extension, whose join exists in the internally finite scalar algebra. At every relational type the full loop-table factor is atomic. A nonzero germ has nonempty rows on a $U$-large set. Choose one tuple in each of these rows there, using internal Choice, and use the resulting singleton-row germ with empty loop table. Any subgerm is either zero or this whole germ by the ultrafilter law. A singleton tuple at one loop, with empty germ, serves when a loop row is occupied. These arguments prove necessary Atomicity at all relational types.

The singleton identity-loop proposition with zero germ is true and entails every current truth. Its transports are loop singletons or bottom, so Strong Actuality holds necessarily. In contrast the atom having empty loop table and germ one becomes top at every later stage, where it is true and has a proper nonzero part. Thus even at $t$ an atom can fail to be a self-atom.
