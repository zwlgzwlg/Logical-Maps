# Fixed CH with disagreement on arithmetic

Non-contingency of CH does not entail Necessity of Arithmetic. In one
countermodel it holds together with revised Mathematical Possibilism and
both necessary rigid powers. In another it holds with necessary Barcan at
all types, necessary propositional Boolean Completeness and Possibly
Witnessed Possibility. In each case two accessible classical structures
disagree about a single arithmetical consistency sentence.

## Choosing the terminal theories

Work in ZFC. Let $\varepsilon$ denote the truth value of CH in the ambient
set universe. Take $T$ to be Zermelo set theory with Choice, augmented by
CH if $\varepsilon$ is true and by its negation otherwise. Either choice
gives a recursively axiomatized theory interpreting elementary arithmetic.
The rank segment $V_{\omega+\omega}$ is a model of $T$. It contains the
reals, all their subsets, and the graphs of the functions that enter CH.
In particular the ordinary natural numbers satisfy $\operatorname{Con}(T)$.
By Gödel's second incompleteness theorem and first-order completeness
there is a countable $M\models T+\neg\operatorname{Con}(T)$.

Use the ordinary full classical type hierarchy on $\mathbb N$ as one
terminal. Use the full finite-type hierarchy on $\omega^M$, computed
inside $M$, as another. The latter is a Henkin hierarchy externally.
At individual type both satisfy the Peano guard, and their Frege
arithmetic agrees with their respective natural-number arithmetic.
Thus they disagree on $\operatorname{Con}(T)$. Reading that sentence
in real structures at individual-property type also separates Necessity
of Analysis. Such a structure exists in each hierarchy: encode natural
numbers by their singletons and reals by subsets of the naturals.

At any type where a real structure exists, the ambient full hierarchy
identifies its numbers with $\mathbb N$ by induction and its reals with
$\mathcal P(\mathbb N)$ by extensionality and fullness. All relations on
these carriers are present. Its structural CH therefore has sign
$\varepsilon$. The identical proof inside $M$, at each standard type,
gives the same sign because $M\models T$. This argument applies to
every real structure at that type, including structures with overlapping
number and real sorts.

## Checking the nonterminal points

In the [Boolean retraction](boolean-retraction-disagreeing-arithmetic.html)
use two copies of each terminal. The four projections and all the base
mode calculations are as in that construction. At either base mode $r,s$
every subset of a typed tuple carrier is the current row of a relation.
Consequently each real structure there also has the ordinary numbers,
all their subsets, and every relation needed to test its CH sentence.
For each fixed type $\sigma$, the universal sentence saying that every
$\operatorname{Real}_\sigma$ has sign $\varepsilon$ is a sentence of the
many-sorted language. Łoś's theorem gives it at all iterated stages and
all terminal ultrapowers. This verifies the required disjunct of
Non-contingency of CH at the initial root. The two uniterated terminal
exits already witness the arithmetical disagreement. The proofs of
necessary Rigid Power, necessary Weakly Rigid Power and revised
Mathematical Possibilism use the number of terminal coordinates, their
size bound, and their classical one-world semantics. All three
conditions hold with these choices.

For the [Stone terminals](stone-terminals-infinite-individuals.html)
keep the ordinary terminals and use three isolated copies of the
$M$-hierarchy. Each root word again admits all current subsets of every
tuple carrier. The same calculation verifies CH at every root word
and all terminals. The two terminal theories still refute Necessity of
Arithmetic. A tester omitting just one nonstandard Frege number at an
isolated $M$-terminal also refutes Arithmetic Necessitism, by the
original argument. Necessary Barcan and necessary propositional Boolean
Completeness use only the surjective projections and the completeness
of the propositional factors. In the word version the disjoint
last-letter assignments still witness Possibly Witnessed Possibility.
