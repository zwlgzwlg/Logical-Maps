# Integer stages with successively compressible coordinates

No Pure Contingency and revised Mathematical Possibilism hold together with necessary Weak Rigid Comprehension and necessary Inextensible Comprehension. Tame Rigidity and Intensional Choice fail at every stage. The construction uses the [two-object finite-image model](symmetric-finite-image-target.html) in successive coordinates.

## The stages

Fix a site set \(A\) of cardinality \(\aleph_1\). Stages and coordinate indices are integers. At stage \(n\) call \(i<n\) a past coordinate. An arrow \(h:n\to m\) requires \(n\le m\) and is a tuple of site maps \(h_i:A\to A\) with the following restrictions.

| Coordinate | Allowed map |
|---|---|
| \(i<n\) | A permutation or a countable-image function |
| \(n\le i<m\) | Any function |
| \(m\le i\) | A permutation |

Composition is coordinatewise. Within the past coordinates, maps of countable image form a two-sided ideal. A coordinate that changes kind at an intermediate step still admits its composite as an arbitrary function. Units are the stage-preserving arrows with a permutation in every coordinate. No nonunit can return to a unit.

Take one object-language individual, fixed by every arrow. At each relational type use tuple rows on arrows, equivariant under left composition by coordinatewise target permutations. The whole table has a source pin consisting of all past sites and at most countably many sites in the other coordinates. Arrows to the same target agreeing on this pin give identical rows. An entity transported by \(h\) has pin \(h[N]\) enlarged to include all past sites at the target. If arrows agree on the pin of an entity, they transport it to the same whole entity, by postcomposition. These conditions give typed closure: for an abstract, agreement on the union of the parameter pins gives identical transported parameters and hence the same row on **all** target arguments. Equivariance follows by transport under a target unit. They give Dorr’s usual symmetric action-model domains. Simultaneous translation of the two integer indices is a pure isomorphism, so every closed pure sentence has constant truth across the stages.

## Units and joins

The scalar \(G\) supported on the unit loops is admitted: at a loop only its fully pinned past coordinates can be singular. It is a true atom by left symmetry. After a nonunit it is bottom; after a unit it is again \(G\). Thus Strong Actuality holds everywhere. Every current truth contains \(G\), and \(\Diamond G\) fails after any nonunit. This proves Truths are ND-necessary at every stage.

Suppose a relation \(X\) has a tuple on a nonunit loop \(h\). On one singular coordinate choose a countable-image endomap fixing the whole image of \(h_i\); on the other coordinates take identities. The resulting nonunit \(k\) satisfies \(kh=h\). For a proper stage change \(h:n\to m\), choose \(n\le i<m\) and use a countable-image map fixing \(h_i[N_i]\), where \(N\) pins \(X\). Then \(X_{kh}=X_h\). In both cases \(hX\) is instantiated on the unit identity row and has a nonempty nonunit row. The scalar \(G\) splits it. A self-atom must therefore be supported only on units. It is an atom at any unit where it is instantiated and hence at the source by invertibility, and all nonunits kill it. This proves the necessary bridge at every relational type.

For Boolean Completeness let \(E\) be the actual members of an admitted family at \(n\) with pin \(N\). In particular every source unit fixing \(N\) stabilizes \(E\). For \(h:n\to m\) define \(J_h\) as the union of \(F_f\) for \(F\in E\) and arrows \(f:n\to m\) such that
\[
 f_i=h_i \quad(i<n\text{ or }i\ge m),\qquad
 f_i|_{N_i}=h_i|_{N_i}\quad(n\le i<m).
\]
Left equivariance is immediate. If \(h'\) agrees with \(h\) on \(N\), the past maps already agree. On \(i\ge m\) their differences are absorbed by a source unit with components \(h_i^{-1}h'_i\) there and identities elsewhere. This unit fixes \(N\) and permutes \(E\), so \(J_{h'}=J_h\). This proves admission and taking \(f=h\) proves the upper bound.

For leastness let \(Z\) bound every \(F\in E\), and take \(y\in F_f\) in the displayed union. On every changed coordinate, a source permutation fixing \(N_i\) moves the additional pin of \(F\) off the pin of \(Z\). There are \(\aleph_1\) sites and the sets to avoid are countable. Let \(u\) be the resulting source unit, identity elsewhere. Then \(uF\in E\). On changed coordinates splice \(f u^{-1}\) on the moved pin of \(F\) with \(h\) on the pin of \(Z\); they agree on the intersection, which is contained in \(N\). Use \(f=h\) on every other coordinate. The resulting arrow \(j\) has \((uF)_j=F_f\) and \(Z_j=Z_h\). Hence \(y\in Z_h\). This proves all-type Boolean Completeness at every stage. Together with Actuality it gives [Weak Rigid Comprehension](../index.html#result/completeness-and-actuality-imply-weak-rigid-comprehension).

For any current row \(D\) choose the profile with rows \(g[D]\) at units and empty rows elsewhere. Its pin is that of the original profile of \(D\), since \(D\) is invariant under units fixing that pin and the unit test uses only the past coordinates. Any tester necessarily accepting the present members contains each unit row. Transport to a nonunit is bottom, and transport along a unit gives the same argument with the moved row. This proves necessary Inextensible Comprehension.

## Mathematical Possibilism

With singleton individuals the inexact ordinal benchmark \(H\) is finite. To see the bound directly, use the finite class of ordinal entities given at **every** arrow by a single Boolean truth table on the two current bits of a binary order and its field. The order and field have just one possible tuple each. Zero and successor give such tables: well-ordering on the current field and restricting to the predecessor field depend only on those bits. A rigid family whose current members lie in this finite class equals the finite union of their haecceities, by weak inextensibility and persistence. At every arrow its current members are therefore exactly the images of that same finite list. Its limit again gives a common finite truth table. The finite class is inductive and is admitted as a tester since these uniform tables are fixed by every symmetry. Thus it bounds \(H\). [Finite-individual ordinal argument](../index.html#argument/forcing-possibilism-countably-many-arrows)

Any countable set of entities has a common pin, by taking the union of their countable nonpast parts. Every relation on such a set has an admitted present extension: use unit rows carrying the chosen graph equivariantly and empty rows elsewhere. The same applies to any finite list of ordinal entities in \(H\). Consequently an infinite Boolean carrier has a countably infinite subclass \(Y\) with \(H<Y\). All subsets and comparison graphs on \(Y\) are available. A strictly smaller subset of \(Y\) is finite, and all its subsets can be coded on a proper finite subset of \(Y\). Thus \(Y\) is power-closed in the precise revised sense, and the original infinite carrier is not small.

At a fixed stage look at loops with every coordinate a permutation except possibly \(n-1\). Choose a fixed finite-image map on \(n-1\). Its left orbit under target permutations determines an admitted scalar: the entire past is pinned, and all later coordinates of a loop are permutations. This scalar is an atom by transitivity on that orbit. Distinct ranks yield arbitrarily many disjoint atoms. Below a union of \(k\) such atoms lies exactly the Boolean algebra with \(k\) atoms. Every graph needed for a finite isomorphism can be realized on its present tuples as above, and bottom covers the trivial algebra when included. This proves revised Mathematical Possibilism at every stage.

## Tame Rigidity and Intensional Choice

Fix a source \(n\) and use coordinate \(i=n\). At any target let \(q_{ab}\) be the scalar that tests whether the two sites \(a,b\) in coordinate \(i\) have equal images at the arrow. It has a two-site pin and \(h q_{ab}=q_{h_i(a),h_i(b)}\). Fix \(a\) and let the row \(X_h\) consist of the \(q_{y,h_i(a)}\) for all sites \(y\). This is a left-equivariant profile pinned at \(a\). It is weakly persistent. If a test necessarily accepts the current \(q_{x,a}\), then it contains \(X_h\) whenever \(h_i\) is a permutation. At every changed coordinate arrow \(h_i\) is arbitrary. Change its value at a site outside the countable test pin and \(\{a\}\) to any desired \(y\), keeping all other coordinates unchanged. This proves weak inextensibility of \(X\) at \(n\).

Now enter \(n+1\) along \(h\) and take an endomap \(k\) constant with value \(c\) on \(i\), identity elsewhere. The set \(k[X_h]\) is \(\{\top\}\), whereas \(X_{kh}\) includes \(q_{y,c}\ne\top\) for \(y\ne c\). A legitimate tester at \(n+1\) has row \(\ell[X_h]\) at each loop \(\ell\) there and full rows at all proper stage changes. These loop rows depend only on \(\ell_i\), now a fully pinned past coordinate, and are left-equivariant. Every current member necessarily passes. The tester at \(k\) detects failure of weak inextensibility. Thus \(X\) is weakly rigid and not rigid. Uniqueness of weakly rigid coextensions also excludes Rigid Comprehension.

Finally, use a property of propositions whose row accepts everything at loops out of \(n\). At every later stage let it accept precisely the propositions \(q_{bc}\) for distinct sites \(b,c\) in coordinate \(i=n\). The property is admissible and necessarily inhabited. At an entrance constant on \(i\), all target permutations on \(i\) fixing that one image point fix the entrance. They would have to fix the uniquely selected proposition there. Distinct unordered pairs give distinct \(q_{bc}\), as a finite-image map can identify one pair while separating the other. The stabilizer of a single point of an uncountable set fixes no two-element subset. Hence Intensional Choice fails, at every stage.
