# A higher-type atom that splits in a stitched forcing model

At the root of each of the recorded Cohen and CH-reversing stitches, a higher-type Boolean atom has a nonatom as its instantiated terminal value. This refutes both *Atoms are self-atoms* and *Atoms are strong atoms* at relational types, already without their boxes. The propositional instances still hold. The 25 October 2026 argument for all relational types treated an atom of the algebra of ground-parameter-definable terminal subsets as a singleton. The following definable set has several members but admits no ground-parameter-definable split. [Cohen stitch](../index.html#model/stitched-cohen-extension) · [CH-reversing stitch](../index.html#model/stitched-ch-reversing)

## The two requirements on the forcing

Use the stitching construction of Barton and Goodsell, §8. Write $V$ for the ground model, $P$ for the forcing and $V[G]$ for the terminal universe. Terminal transports of root relations are precisely the terminal relations definable from ground parameters. At the root the current extension and the terminal value can be prescribed independently. Suppose that a ground group $N$ of forcing automorphisms acts weakly homogeneously, meaning that for all $p,q\in P$, some member of $N$ sends $p$ to a condition compatible with $q$. Suppose also that a ground forcing automorphism $a$ satisfies $aG\notin N\cdot G$ for every ground-generic $G$.

For finite-condition Cohen forcing on $J=\omega$ or $J=\omega_2\times\omega$, take finite bit flips. They can align the two finite prescriptions on their overlap. The all-bit flip changes infinitely many coordinates and produces a generic outside the finite-flip orbit. Ground generics related by a ground forcing automorphism generate the same extension.

For $\operatorname{Col}(\omega_1,\mathfrak c)\times\operatorname{Add}(\omega,1)$, take range permutations at countably many collapse coordinates together with finite Cohen flips. At each of the countably many shared collapse coordinates a permutation can send the first value to the second. Flip the Cohen bits on their finite set of conflicts. The all-bit Cohen flip, with identity on the collapse, sends the generic outside its orbit. These cases cover both ground-universe settings of the two recorded models. For the bare collapse over $\neg\mathrm{CH}$, the same countably supported range permutations work. A single fixed-point-free permutation of the range applied at every coordinate separates two orbits there.

## A definable family of indistinguishable orbits

Fix a ground cardinal $\theta$ and a ground coding of $P$ by ordinals below $\theta$. Within $V[G]$ let $\mathcal H$ be the set of $P$-generic filters $H$ over $V$ that generate this same extension. This set is definable from ground parameters. Use the ground set of dense subsets of $P$ to express genericity. Also use the ground set of nice $P$-names for subsets of $\theta$ and require that every subset of $\theta$ in the present universe be the evaluation of one of these names by $H$. If this condition holds, the code for $G$ belongs to $V[H]$. Conversely, when $V[H]=V[G]$, the forcing theorem supplies all the required names. This defining test quantifies only over sets.

For each $H\in\mathcal H$ put $Y_H=N\cdot H$. The canonical forcing name for the set of all translates of the generic by $N$ is fixed by $N$: applying any $n\in N$ permutes its summands. In particular for every fixed set-theoretic formula $\varphi$ with ground parameters $\bar c$, the top condition decides
\[
\varphi(N\cdot\dot G,\check{\bar c}).
\]
Indeed two conditions forcing opposite truth values would remain opposite after moving the first by any element of $N$. This contradicts compatibility under weak homogeneity. The forcing theorem applied to each $H\in\mathcal H$ now gives the **same truth value in the same universe** $V[G]$ for every $\varphi(Y_H,\bar c)$.

Thus the ground-parameter-definable set $D=\{Y_H:H\in\mathcal H\}$ has no nonempty proper ground-parameter-definable subset. If a defining formula picked one $Y_H$, the same formula would pick them all. Yet $Y_G$ and $Y_{aG}$ are distinct members, because their orbits are disjoint and $V[aG]=V[G]$.

These sets occur at a fixed finite simple type. Ground reals are properties of individuals at the terminal. A ground set of reals is an element of the next terminal power type, even when new reals have been added. For the forcings here, choose in $V$ an injection $i:P\to\mathcal P(\mathbb R^V)$. Cohen forcing on $\omega_2\times\omega$ has size $\aleph_2\le 2^{\mathfrak c}$, and a countable collapse condition can be coded by a sequence of reals, for at most $\mathfrak c$ possibilities. Code a filter by $i[H]$, its orbit by the set of those codes for its members, and $D$ by the set of orbit codes. Each step uses one further property type. The coding and its inverse on the ranges are definable from the ground injection, so the absence of a definable proper nonempty subfamily is preserved.

## The root atom and the surviving bridge principles

Take the root predicate with empty current row and terminal value $D$. It is nonzero. Every subpredicate still has empty current row, and its terminal part must be a ground-parameter-definable subset of $D$. That part is either empty or all of $D$, so the root predicate is an atom. At the terminal it is inhabited and has two distinct members; either terminal singleton splits it. It is therefore neither a self-atom nor a strong atom at the root.

Conversely, if a root self-atom has a current member, it is already an atom at the root. Splitting off a singleton current tuple with empty terminal part shows that this is its entire profile. If it has only a terminal member, its terminal part must be an atom there, hence a singleton of the full terminal hierarchy. In either case its transports are atoms or bottom. At the terminal the three notions agree. Hence both necessary implications from self-atoms to atoms and strong atoms hold at all relational types. At $t$ the four root truth profiles and two terminal truth values give the other two necessary implications as well.

The forcing constructions and the stitching semantics are due to Barton and Goodsell. The correction to the higher-type bridge argument was found by OpenAI Codex (GPT-6), prompted by Daniel Kodsi, and independently checked by two further GPT-6 agents on 26 November 2026.
