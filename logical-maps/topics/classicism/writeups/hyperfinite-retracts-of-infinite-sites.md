# Hyperfinite retracts of infinite sites

At both individual and propositional type, the Infinity Schema and even the necessary possibility of the Axiom of Infinity can hold while the Axiom of Infinity itself fails. All four separations, with either Possible or Potential Infinity as the second premise, occur at the same Functional Choice point.

## The finite roots

Take a category with two objects $r,s$. There is an arrow $h:r\to s$, an arrow $j:s\to r$, and $jh=1_r$. The only endomorphism of $r$ is its identity. At $s$ take the infinite cyclic group and adjoin a zero $z=hj$. For every group element $g$ put $gh=h$ and $jg=j$. The same equations with $z$ follow from $jh=1_r$. These compositions are associative. For instance this category is realized by a singleton at $r$ and a copy of the integers with an added fixed point at $s$, with translations, the inclusion of the fixed point and the collapse onto it.

For each positive integer $k$, form the product of this category with the one-object cyclic group of order $k$. Denote its two objects again by $r,s$. Every arrow from $r$ has a left inverse. There are exactly $2k$ outgoing arrows from $r$ and countably infinitely many from $s$.

In the interpreting action model let $D_e(r)=\{1,\ldots,k\}$ and $D_e(s)=D_e(r)\times\mathbb N$. The arrow $h$ adds a zero second coordinate, $j$ projects to the first, and both groups act trivially on individuals. The zero endomorphism at $s$ resets the second coordinate to zero. At each relational type use the full action model. A value at an object specifies one arbitrary tuple row at each outgoing arrow. Transport along $u$ reads at $v$ the row indexed by $vu$. In particular a proposition is any subset of the outgoing arrows. Application at the identity reads the current row, and a lambda abstract takes at each arrow the row of its body on transported parameters and all target arguments.

Thus $r$ has $k$ individuals and $2^{2k}$ propositions. At $s$ both sorts are infinite, and the propositional sort has continuum cardinality. Give the individual names a common anchored value preserved in both directions, and the relational names the top values.

## The two sorts of infinity

Full current rows include the predicate picking out exactly the standard iterates of the native Frege successor on zero. These iterates form an inductive set and belong to every inductive set, so precisely they satisfy the native finite-cardinality predicate at each site. By ordinary external induction, the $m$th numeral holds of a property precisely when it has $m$ current members. This remains true even at a finite current carrier because the successor clause removes one member of the current extension.

It follows at $r$ that some finite cardinality counts all individuals and some finite cardinality counts all propositions. At $s$ no numeral counts the whole domain at either sort. Both objects can reach $s$. Thus necessarily it is possible that both Axioms of Infinity hold there, whereas both fail at $r$.

Take a nonprincipal ultraproduct over the positive integers, pointed at the sequence of roots. Use the many-sorted action presentations with paths, composition, typed transport and incidence. Each fixed formula of C has its ordinary first-order satisfaction translation on these presentations. The model conditions, including term closure for each fixed term, transfer as in the [finite-tree ultraproduct](witnessed-possibility-implies-infinity-schema-t.html). For each standard $n$, almost every root contains at least $n$ different individuals and at least $n$ different propositions. Hence both native Infinity Schemata hold. The two failures of actual infinity and the necessary possibility of actual infinity transfer as single sentences. Possible Infinity implies Potential Infinity at the corresponding type throughout the cone.

## Functional Choice and related signs

Fix a factor and a serial relation at $r$. Use Choice to pick an output $f(x)$ for each input $x$, the output being of type $\bar\tau t$. Each arrow $p$ from $r$ has a left inverse, so $x\mapsto p x$ is injective at every input type. At path $p$ prescribe the row of an operation $F$ by

$$
 F_p(px,\bar y)=(f(x))_p(\bar y)
$$

for every input $x$ and every target tuple $\bar y$. Extend the row arbitrarily elsewhere. The prescriptions are consistent by injectivity. At every path and every remaining argument, $Fx$ now agrees with $f(x)$, giving equality as whole entities. Thus $F$ selects at the root, and each Functional Choice instance transfers. A return via a left inverse also restores any root assignment exactly, giving the B instances with parameters. For the anchored interpretations of the names, every closed signature truth at either object recurs from the other.

* Full tuple rows give Boolean Completeness at all relational types at both sites. Every weakly rigid relation has exactly the transported images of its current members at every path, as witnessed by the tester that omits a single tuple at a single path. Conversely the exact-image property is hereditary by composition. Every current row generates such a profile. If a future subrow $V$ lies within the image of a rigid bound with source row $E$, then $E\cap p^{-1}(V)$ generates a rigid lift. This proves necessary Rigid Comprehension and both necessary rigid powers. Choosing a well-order of the target carrier for each path row gives Modal Well-Ordering.
* The singleton proposition at the identity is a true strong atom at each object. Its support after transport along $p$ consists of the left inverses of $p$. A path from $r$ has exactly one, and a path from $s$ has exactly one if it is a group arrow and none otherwise. Every composite is still an arrow of these forms. In contrast the scalar atom at $r$ supported only at $(1,h)$ is true after that entrance and splits there, because all the distinct endomorphisms $(1,g)$ satisfy $(1,g)(1,h)=(1,h)$. Hence Atoms are self-atoms fails at $t$.
* At a type with a necessary Peano guard, the numbers in every factor are precisely the distinct standard numerals, as above. They transport to the same numerals, giving both necessary distinctness and exactly the images of the old numbers at every arrow. Their property is therefore rigid. This proves Arithmetic Necessitism in the ultraproduct, one instance at a time.
* At $s$ a real number structure can be formed on its continuum-sized scalar carrier using distinct number labels, the usual subsets of the naturals and the usual membership relation. Full current rows admit all the required relations. At $r$ its finite scalar carrier cannot contain an injective successor on an inhabited subset omitting zero. This refutes Analytic Necessitism at $t$ in every factor and hence in the ultraproduct. For any real structure in a factor, full current tests make its numbers standard and its reals the full powerset of the numbers, by induction, extensionality and fullness. All second-order predicates on these objects are also available. Each guarded second-order analytical sentence thus has the same truth value wherever it is instantiated and transfers as a fixed sentence.

OpenAI Codex (GPT-6), prompted by Daniel Kodsi, 27 November 2026. Two other GPT-6 researchers independently checked the category, the model, Functional Choice and the infinity separations.
