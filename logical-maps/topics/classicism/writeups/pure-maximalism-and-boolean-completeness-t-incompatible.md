# Maximalism excludes a countable join of propositions

At every pure Maximalist point, one fixed, purely definable family of propositions indexed by the individual Frege numbers has no least upper bound. Consequently pure Maximalism is incompatible with local Boolean Completeness at type $t$. The same holds for signature Maximalism, which includes the pure possibility instances. The argument uses a single supremum at the point where Maximalism holds.

## A pure recurrent numerical label

Write $N=\mathbb N_e$, $S=\operatorname{Suc}_e$ and $I=I_e^*$. Call a property of individuals infinite when no member of $N$ counts it. Let $D(k)$ say that there are a property $U$ counted by $k$ and a binary relation $R$ on individuals such that the rows $R(x,-)$, for $Ux$, are infinite and pairwise disjoint for distinct current indices. Put

$$
 J(n)=D(Sn)\land\forall k\in N\,(D(k)\to k\le Sn),\qquad
 G=\Box\bigl(\mathrm{C5}\land I\land\forall n\in N\,\Diamond J(n)\bigr).
$$

Here $\mathrm{C5}$ may be taken as the single native sentence $\Box\mathrm{ND}_t$, which gives the map's C5 consequences. On $I$, if $J(n)$ and $J(m)$ then $Sn=Sm$ by the two greatestness conditions, hence $n=m$. This works for every local number. The guard $G$ persists by 4. At a $G$-point every $d_n=G\land J(n)$ for a local $n\in N$ is possible. Two further C5 consequences used below are that each scalar identity or its negation persists, and that $\Diamond\Box A\to\Box A$ there.

The pure sentence $G$ is consistent. Let $A$ be a countably infinite individual set. Take all ordered partitions of $A$ into finitely many nonempty infinite blocks as the worlds of a single S5 clique. Individuals and whole relations transport identically. The permutations of $A$ act on the worlds and recursively on the types. At a relation type with joint argument domain $L$, take all subsets of $W\times L$ fixed by the pointwise stabilizer of some finite subset of $A$. A term evaluated on parameters is equivariant under their common stabilizer. This includes quantification over each full admitted domain, so abstraction gives an admitted relation. Distinct relations are separated by a tuple at some accessible world. This is the finitely supported S5 semantics used in [the profinite Boolean model](profinite-s5-boolean-algebras.html).

The constant-world predicate whose members are exactly the whole standard numeral entities has empty support, since the numerals are closed pure terms. It is inductive. The definition of $N$ therefore gives exactly these numerals at every world. By induction on standard $m$, its numeral counts precisely the current $m$-element rows, using the Frege successor's removal of a single instance. Every finite subset of $A$ is admitted as a constant row with finite support. Thus the numerals are distinct, $I$ holds throughout, and an infinite unary row means an externally infinite set.

At a world $w=(B_1,\ldots,B_h)$, every current unary row is finite or cofinite on each block. Its finite support leaves all permutations of each block outside that support available. Consequently any infinite row is cofinite on at least one block, and two disjoint infinite rows cannot use the same block in this way. Conversely, for $k\le h$, choose $k$ distinct individual tags and match them to $k$ different blocks. Their tag set is an admitted index property. The binary row associating each tag to its block extends to a whole relation with those tags as finite support. On the orbit of $w$ under permutations fixing the tags, transport its row equivariantly, and use the empty row elsewhere. This is well defined since the ordered partition's stabilizer fixes each block setwise. Hence $D(\bar k)$ holds precisely for $k\le h$. The label $J(\bar n)$ holds exactly at the worlds with $n+1$ blocks. Every such world is accessible everywhere, proving $G$.

## What a least upper bound would imply

Suppose a pure Maximalist point $r$ has a least upper bound $s$ of the current family

$$
      \lambda p^t.\ \exists n\in N\;(p=d_n).
$$

This is a single closed pure family. Boolean Completeness, stated for greatest lower bounds, gives its least upper bound by complement. The term $n\mapsto d_n$ supplies the indexing graph. Maximalism gives $\Diamond G$, hence $I$ at $r$ by the native implication $\Diamond I\to I$. For every source $n\in N$, numberhood persists to a $G$-point, which can see $d_n$. Thus each source $d_n$ is nonzero. Distinct source numbers stay distinct at Peano successors. The uniqueness of the labels under $G$ therefore makes the corresponding cells disjoint as whole propositions. In particular the indexing graph is injective on the source numbers.

The upper-bound assertions $d_n\le s$ for the individual source numbers are identities, so each persists. Form the scalar

$$
      T=\exists k\in N\,\bigl(J(k)\land(d_{Sk}\le s)\bigr).
$$

For each source $n$, $d_n\le T$ since $d_{Sn}\le s$ persists and $n$ remains a number. Hence $s\le T$ by leastness. Consider any accessible $G$-point. At that point $d_0\le s$. For an arbitrary number $n$ there, assume $d_n\le s$. Visit a $d_n$-point, where both $s$ and $T$ are true. The witness $k$ for $T$ equals the transported $n$ by uniqueness of $J$. Thus $d_{Sn}\le s$ there. The $G$-point has C5, so this possible identity already holds at the $G$-point. Induction on the admitted property $\lambda n.(d_n\le s)$ inside that point proves

$$
            \Box\bigl(G\to\forall n\in N\;(d_n\le s)\bigr) \quad\text{at }r.
$$

This is the step covering numbers newly available at a successor. It uses leastness at $r$ and Peano induction at the successor.

Let $X(n)$ be any formula with source parameters, and assume at $r$ that $\forall n\in N\,\Box(G\to X(n))$. Form

$$
       T_X=\exists k\in N\,\bigl(J(k)\land\Box(G\to X(k))\bigr).
$$

Each source $d_n$ entails $T_X$ by persistence of the box, so $s\le T_X$. At any accessible $G$-point and for any number $n$ there, visit a $d_n$-point. There $d_n\le s$ gives $s$, hence $T_X$. Uniqueness gives $\Box(G\to X(n))$ there. The C5 implication $\Diamond\Box A\to\Box A$ at the starting $G$-point now gives $X(n)$ at that point. We have proved the guarded numerical Barcan inference at $r$,

$$
 (\forall n\in N\,\Box(G\to X(n)))\quad\Longrightarrow\quad
 \Box\bigl(G\to\forall n\in N\,X(n)\bigr).
$$

Lean verifies the native countability predicate for this family at its counting type and the numerical Barcan inference from its join. [Guarded Barcan derivation](../lean/Classicism/Results/Research/RecurrentCells.lean)

## Arithmetic gives the contradiction

For every fixed arithmetical formula $A$ and tuple $\bar n$ of source numbers, either $\Box(G\to A(\bar n))$ or $\Box(G\to\neg A(\bar n))$. For numerical identity and the arithmetic operation graphs this follows from the preserved numberhood, guarded distinctness and guarded arithmetic facts in [Goodsell's arithmetic lemmas](countable-boolean-completeness-implies-necessity-of-arithmetic.html). Boolean connectives preserve the assertion. For a universal quantifier, if every source number takes the positive disjunct in the induction hypothesis, use the guarded Barcan inference. Otherwise a source number takes the negative disjunct. Its numberhood persists, so it refutes the universal at every $G$-point. This is Goodsell's induction for the Necessity of Arithmetic with $G$ as its guard. The Lean theorem `one_join_decides_arithmetic` composes the join argument with induction on the map’s native arithmetic syntax. It covers every closed arithmetic sentence and derives the needed atomic facts for the native addition and multiplication graphs. [Guarded arithmetic induction](../lean/Classicism/Results/Research/GuardedArithmetic.lean) · [Proof from one join](../lean/Classicism/Results/Research/RecurrentArithmetic.lean)

The arithmetical sentences $A$ for which pure C proves $G\to A$ form a consistent recursively enumerable extension of Peano arithmetic. Consistency follows from the partition clique and inclusion of PA from $G\to I$. By Rosser's incompleteness theorem choose a closed arithmetical $A$ independent of this theory. Both $G\land A$ and $G\land\neg A$ are C-consistent pure sentences. Maximalism makes both possible at $r$, contradicting the uniform arithmetic verdict just proved. Given C-consistency of these two sentences at the specified guard, Lean verifies the inconsistency of the native pure Maximalism and local propositional Boolean Completeness schemas. The existence of the partition model and the production of the two consistent arithmetic signs by Rosser’s theorem are the ordinary mathematical inputs. [Native inconsistency from the two consistent possibilities](../lean/Classicism/Results/Research/RecurrentPossibility.lean)

This uses the same effective-arithmetic argument as the map's [Maximalism incompatibility with Necessity of Arithmetic](../index.html#result/possibility-and-necessity-of-arithmetic-incompatible).

## A single sentence without a complete predecessor

Take the independent arithmetic sentence $A$ from the proof and put
$$
P=\Diamond(G\land A)\land\Diamond(G\land\neg A).
$$
This is a single C-consistent pure sentence, since any ordinary Maximalist point sees each of the two consistent conjuncts' witnesses. At every point that can see $P$, both possibilities hold by transitivity. These two possibilities alone give $\Diamond G$, hence the source Peano guard. The argument with the proposed supremum and the two upper bounds then makes $A$ agree at all accessible $G$-points. Thus $P$ cannot be possible from any point with local propositional Boolean Completeness.

There are arbitrarily many disjoint principal intervals exhibiting the obstruction at each pure Maximalist point. Start with $H=G$, or with $H=G\land\Diamond q$ for any closed pure $q$ with $H$ consistent. Such an $H$ persists, since possibility is itself necessary in the C5 cone. All the numerical labels still recur there. The proof with $H$ in place of $G$ shows that the countably indexed family $H\land J(n)$ has no upper bound that is least in the principal interval below $H$. Indeed any upper bound $u$ in the whole algebra restricts to the upper bound $u\land H$ in the interval, so a relative supremum would also be a global supremum.

Apply Rosser's theorem to C under this single guard $H$. Both arithmetic refinements $H\land B$ and $H\land\neg B$ are consistent for a suitable closed arithmetic $B$. Each refinement persists, by the Necessity of Arithmetic throughout a C5 cone with the Peano guard, and inherits the recurrence of every $J(n)$. At a pure Maximalist point the two refinements are disjoint nonzero propositions whose principal intervals both lack their respective countable joins. Repeating the construction externally at each finite node gives a binary tree of such incomplete intervals under $G$.

## Every infinite subfamily of the standard cells lacks a supremum

For every infinite external subset $A\subseteq\mathbb N$, the subset
$$
                 \{d_{\bar k}:k\in A\}
$$
of the actual propositional algebra has no supremum in that algebra. Here $\bar k$ denotes the standard $k$th numeral at $r$. The upper bounds range over **all** scalar entities admitted at $r$, ordered by the source's necessary implication. The chosen subset need not itself be the current extension of any admitted predicate.

Suppose $s$ were its supremum. The standard cells are nonzero and pairwise disjoint. For each $k\in A$ we have $d_{\bar k}\le s$, and for each standard $k\notin A$ the complement of $d_{\bar k}$ is an upper bound, giving $d_{\bar k}\le\neg s$. These identities persist. At any accessible $G$-point, each $d_{\bar k}$ is still possible. Consequently the local numerical predicate $Q(k):=(d_k\le s)$ has exactly $A$ as its standard trace.

Inside a $G$-cone, every arithmetic formula on current numbers with $Q$ as an additional predicate has a settled truth value. On numerical inputs $Q(k)$ is an identity of propositions. Both its signs persist in C5, and the ordinary arithmetic induction proving settled truth extends to $Q$, using BF on the numerical sort for quantifiers. This applies, in particular, to the order and the counting predicates used below.

The scalar
$$
           T=\exists k\in N\bigl(J(k)\land\exists l\in N\,(k<l\land Q(l))\bigr)
$$
is an upper bound of the selected standard cells. For each $k\in A$ separately, choose a larger standard $l\in A$. At every $d_{\bar k}$-point the inequality $\bar k<\bar l$ holds in its Peano arithmetic and $d_{\bar l}\le s$ persists. Hence $s\le T$. At an accessible $G$-point let $Q(k)$ hold. Visit a $d_k$-point, where $s$ gives $T$. The unique $J$-index there is the image of $k$, so it has a larger $Q$-index there. Settled truth brings this existence assertion back to the $G$-point.

Thus $Q$ is nonempty and has no largest member at every such point. In Peano arithmetic with induction for the admitted predicate $Q$, for every internal $n$ there is exactly one $n$th $Q$-member in increasing order, starting at rank zero. One explicit rank predicate counts $Q$ on the bounded interval below $k$ using coded finite bit sequences. Induction with $Q$ as a parameter supplies a binary membership code on each such interval. Least-number induction gives the first $Q$-index and the least $Q$-index above any already chosen one, giving existence of every rank by induction. Write $L(k,n)$ for “$k$ is the $n$th $Q$-member”. This arithmetic formula with parameter $Q$ is settled within the cone. For a standard $k\in A$, its rank is the ordinary standard number of members of $A$ below $k$, by the finitely many fixed membership verdicts there.

Let $X(n)$ be any formula with parameters at the source. Assume for every standard $i$, separately, that $\Box(G\to X(\bar i))$ holds at the source. The scalar
$$
 T_X=\exists k,n\in N\,\bigl(J(k)\land L(k,n)\land\Box(G\to X(n))\bigr)
$$
is another upper bound of all the selected cells. On $d_{\bar k}$ take its standard rank and use the corresponding boxed premise. Therefore $s\le T_X$. At any accessible $G$-point and any internal $n$, take its $Q$-member $k$ of rank $n$ and visit a $d_k$-point. There $s$ and hence $T_X$ hold. Uniqueness of the $J$-index and the transported rank give $\Box(G\to X(n))$ there. The C5 law $\Diamond\Box P\to\Box P$ gives $X(n)$ back at the initial $G$-point. We have proved an external guarded $\omega$-rule for every $X$.

Induct externally on arithmetic formulas evaluated at standard inputs. The atomic cases have their usual standard values at every $G$-point. For a universal that is true in standard arithmetic, its separate standard instances give the conclusion by the guarded $\omega$-rule. For a false universal a standard counterexample suffices. Thus every accessible $G$-point agrees with standard arithmetic on all sentences. The independent arithmetic sentence for the consistent effective $G$-theory has both signs realized at accessible $G$-points by Maximalism, a contradiction.

**Principal intervals.** If a proposition $p$ at $r$ lies above infinitely many of these standard cells, its principal interval $[\bot,p]$ fails external countable completeness. Indeed, for any infinite subfamily below $p$, a least upper bound inside the interval would also be its least upper bound in the full algebra. For every full-algebra upper bound $b$, the meet $b\land p$ is an upper bound in the interval. Thus each externally countably complete principal interval can contain only finitely many whole standard cells.

OpenAI Codex (GPT-6), prompted by Daniel Kodsi, 27 November 2026. One researcher found the least-upper-bound argument and its application to newly available numbers. A second constructed the pure finite-support partition model. Two researchers independently checked both parts, and three further researchers on the coordinating team reviewed the partition calculation, the passage between accessible Peano points, and the arithmetic contradiction. The incompleteness step follows Goodsell's Theorem 11. The argument for arbitrary infinite subfamilies was obtained independently by two further researchers.
