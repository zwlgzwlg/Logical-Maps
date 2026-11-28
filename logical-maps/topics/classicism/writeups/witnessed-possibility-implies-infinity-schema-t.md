# Witnessed Possibility and finite numbers of propositions

**Witnessed Possibility implies the Infinity Schema at type $t$.** Every fixed finite lower bound on the number of distinct propositions follows. Even Possibly Witnessed Possibility is consistent with an internal finite count of all propositions at every accessible point. In this countermodel one current finite number is too large to count a property of propositions anywhere. Thus the Axiom of Infinity, Possible Infinity and Potential Infinity at type $t$ all fail.

## Arbitrarily many propositions

Fix an ordinary nonnegative integer $j$. For a proposition $p$ write $p_1=p$, $p_0=\neg p$, and use the following finite modal formulas, recursively expanded $j$ times.

$$
 A_0^b=p_b,\qquad A_{j+1}^b=p_b\land\Diamond A_j^{1-b},\qquad
 L_j=A_j^0\lor A_j^1,\qquad E_j^b=A_j^b\land\neg L_{j+1},\qquad E_j=E_j^0\lor E_j^1.
$$

At a point of color $b$, $E_j^b$ says that $p$ allows exactly $j$ truth-value alternations. The sets $L_j$ descend, $\Diamond L_j=L_j$, and $E_{j+1}^b\le\Diamond E_j^{1-b}$. For the last inequality, $E_{j+1}^b$ sees an opposite-color point in $A_j^{1-b}$ but cannot see one in $A_{j+1}^{1-b}$. The predecessor closure of $L_j$ uses transitivity: a point seeing $j$ alternations can start that same length with its own color, either by retaining or by dropping the starting color of the witnessed sequence. These observations concern finite formulas in C. [Alternating layers and the capping lemma](witnessed-possibility-and-no-pure-contingency-imply-necessary-axiom-of-infinity-t.html)

Induct externally on $j$ to show that each color occurs as the starting color of a current proposition of exact rank $j$. The constant truth values supply rank zero. For the step, take a relational signature constant $C$ and put $c=\forall\bar x\,C(\bar x)$, with $c=C$ at propositional type. Every proposition is of the form $\forall\bar x\,X(\bar x)$ by taking $X=\lambda\bar x.p$. Applying Witnessed Possibility separately to the two formulas obtained from $E_j^0,E_j^1$ gives $\Diamond E_j^0(c)$ and $\Diamond E_j^1(c)$ for the same $c$. The witness opposite to the current color of $c$ shows that $q=L_{j+1}(c)$ holds here.

Choose a possible $E_j^d(c)$ and give $q$ the uniform color $1-d$, leaving $c$ unchanged outside $q$. Because $q$ is closed under predecessors, all later points of a point outside $q$ are also outside it. The new coloring there therefore has the old alternating ranks, all at most $j$. Within $q$ the color is constant. An alternating sequence starting here either stays in $q$ or leaves it once, so its length is at most $j+1$. The chosen $E_j^d(c)$ lies outside $q$, where it retains its exact rank and color $d$. It supplies $j+1$ alternations from here. Complementing this new proposition supplies the other starting color. This uses Witnessed Possibility only at the original point.

Now take a current proposition with exact rank $j$. The recurrence shows that $E_0,\ldots,E_j$ are all possible. They are pairwise disjoint, since $E_i=L_i\land\neg L_{i+1}$ for descending $L_i$. They give $j+1$ distinct propositions. Applying this proof separately at each ordinary $j$ proves every instance of the Infinity Schema. The proof with the additional premise of No Pure Contingency handles the map’s internally quantified finite numbers. [Witnessed Possibility with No Pure Contingency](witnessed-possibility-and-no-pure-contingency-imply-necessary-axiom-of-infinity-t.html)

## The countermodel

Take the full action model on a finite perfect binary tree. Arrows go from a vertex to each of its descendants, including itself. There is one individual everywhere. At a vertex a relation gives, independently at every descendant, a whole current row on the tuple domain at that descendant. Transport restricts this profile to the chosen subtree. Consequently each rooted subtree of height $h$ is isomorphic, at every type, to the original full tree of height $h$. Pure modal truth at a vertex depends only on its pointed subtree and the parameters there.

Fix any set-sized signature $\Sigma$ and a finite list of instances of Possibly Witnessed Possibility. Instance $i$ requires

$$\Diamond\exists\bar x\,\varphi_i(\bar x)\ \longrightarrow\ \Diamond\varphi_i(\bar c_i),$$

where the matrix is pure and the indicated constants are distinct and match the variable types. For each listed matrix that has a witness at the root of **any** finite perfect binary tree, fix one such tree, of height $h_i$, and a whole witnessing tuple. If the matrix has no such witness, it cannot have one at any vertex of any tree in the family.

Choose a depth $d$ with at least as many vertices as the number of chosen witnesses. In a tree of height at least $d+\max_i h_i$, assign each witness to a different vertex at depth $d$. Descend within that vertex’s subtree until its remaining height is exactly $h_i$. The resulting subtrees are pairwise disjoint. On the entire $i$th subtree prescribe the indicated relational constants to agree, row for row, with its chosen witness. Extend their profiles arbitrarily outside the prescribed subtrees. An individual constant has only one possible assignment. Distinctness within each tuple prevents collisions there, and disjointness of subtrees permits repeated use of the same name across different instances. If no witnesses were chosen, every listed antecedent is false and any height works.

Whenever a selected antecedent holds, its witness occurs at the root of a finite perfect subtree. Its matrix is therefore among those with a chosen witness, and its instance holds at the designated subtree with the actual constants. This proves the finite list simultaneously. It places no upper bound on the height chosen for that list.

Index these pointed models by finite subsets of all the signature instances and take an ultrafilter containing each cone of finite subsets that include a given instance. Such an ultrafilter exists in ZFC by the finite intersection property. Form the many-sorted Henkin ultraproduct of pointed action models, with worlds, the individual and relation sorts, transport and application included. The translation of every fixed typed formula, including its modal and quantifier clauses, is first order in this presentation. The axioms for typed lambda terms hold instance by instance in every factor. Łoś’s theorem therefore gives a model of C satisfying the full Possibly Witnessed Possibility scheme. It also transfers any fixed sentence common to the finite trees. One may require the factor for a fragment of size $s$ to have height at least $s$. [Related finite-model ultraproduct on S5 frames](ultraproduct-finite-full-s5.html)

Every type has a finite carrier at every vertex of each factor. The standard Frege numeral for its actual size thus counts the universal property there. Moreover a numeral larger than **all** the propositional carriers of that finite tree counts no property at any vertex. This gives the same closed assertion in every factor: at every point some finite numeral will never count a property of propositions. The numerical witness may depend on the factor. The transferred assertion refutes Potential Infinity at $t$; the finite counts of the universal property at all successors refute Possible Infinity and the Axiom of Infinity. The individual domain stays a singleton. The root still has arbitrarily many externally distinct propositions, as the positive implication requires, while its internal count is nonstandard.

## Other principles in the countermodel

* At all types every transport is onto. Extend any relation on a subtree by arbitrary rows elsewhere. At individual type the map is the identity. This yields necessary Barcan.
* In each finite tree entailment of relations is rowwise inclusion. Every admitted family has its rowwise union, giving necessary Boolean Completeness. A singleton tuple at one descendant is an atom whose transport is a singleton of the same form or bottom. Every nonzero relation contains one, and the identity-only true proposition is such an atom. This gives necessary Strong Atomicity and necessary Strong Actuality.
* For a current set of tuples $U$, take its direct image at each descendant. This relation is rigid, since at every later vertex its rows are precisely the further images of its current members. Conversely, a weakly rigid relation with current row $U$ has exactly these rows. Persistence gives one inclusion; for the other, use a tester true everywhere except at one target tuple outside the indicated image. If $Z$ is a rigid subrelation at a descendant $h$, with current row $V\subseteq h[U]$, its direct-image lift on $U\cap h^{-1}[V]$ lies below the original bound and transports to $Z$. Thus the power predicates themselves have the direct-image property, giving necessary Rigid Comprehension and both necessary Rigid Power principles.
* A necessarily inhabited property admits a profile choosing one singleton row at each vertex. An independently chosen finite well-order of each vertex’s domain gives a single relation which necessarily well-orders the type. Thus Intensional Choice holds necessarily and Modal Well-Ordering holds.

These claims transfer one fixed type and one sentence at a time. The proofs of strong atomicity and completeness in the ultraproduct use the map’s quantification over admitted relations.

Mathematical Possibilism also fails at one fixed carrier type, $tt$. At any
vertex $v$ of a finite tree put $D=D_t(v)$ and represent each $S\subseteq D$
by the property with current row $S$ and empty rows at proper descendants.
Full current rows put the Boolean algebra $\mathcal P(D)$, ordered by inclusion,
on these entities. Every finite carrier is small under the revised definition.
Indeed, if $|Y|=k>0$, a subcollection of size $k-1$ has $2^{k-1}\ge k$ subsets,
which cannot all receive different codes in a strictly smaller subcollection of
$Y$. The empty collection cannot be larger than the ordinal benchmark. The proposed
algebra has $2^{|D|}>|D|$ elements, more than the entire propositional domain, so
no propositional interval is order-isomorphic to it. The same fixed assertion
holds at every vertex in each factor and transfers to the ultraproduct.

### The remaining modal and analytic verdicts

At each vertex the singleton proposition true only there is impossible after every proper arrow. For every current truth $p$, this gives a current $q$ with $\Box(\Diamond q\to p)$, as required for distinctness necessity. This argument applies at all vertices. In any tree of positive height, choose two leaves. Their union is an atom everywhere it is instantiated, since an individual leaf has no proper descendants, yet the two singletons split that union at the root. This disproves Self-Atoms Are Atoms at $t$. Pure B fails there as well. The pure sentence “some true proposition could be false” is true at the root and impossible at either leaf. Trees of positive height form an ultrafilter-large set. For example, in the construction require a fragment's tree to have height at least the fragment's size. Equivalently, any fragment containing a matrix that can only be witnessed in a nontrivial tree already requires positive height.

Every simple type is finite at every vertex in a factor. An injective successor of an inhabited finite set cannot omit its zero. This rules out a real structure at each type at each vertex. The same argument applied to the Frege cardinalities rules out the Peano condition $I^*_\sigma$. For each fixed $\sigma$, the boxed assertions of these exclusions are single sentences and transfer to the ultraproduct. In particular Second-Order Analytic Necessitism holds, as do Arithmetic Necessitism and the guarded sentence schemata for arithmetic and analysis.

OpenAI Codex (GPT-6), prompted by Daniel Kodsi, obtained these additional verdicts on 27 November 2026. Two other GPT-6 research agents independently checked the finite-factor arguments and their transfer.
