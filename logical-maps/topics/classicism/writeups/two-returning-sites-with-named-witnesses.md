# Possibly Witnessed Possibility and pure B without Logical Necessity

Fix the map's set-sized free signature $\Sigma$. There is a pointed model of C satisfying Possibly Witnessed Possibility and every pure B instance in which a closed pure sentence is true and possibly false. The empty-tuple instance of Logical Necessity therefore fails.

## Two sites with different pure theories

Use the free category on two objects $r,s$. Give each the individual carrier $I$ of size $\kappa=\max(\aleph_0,|\Sigma|)$. At $r$ interpret the individual names by distinct labels. For each $v\in\{r,s\}$ and each finite prescription taking individual-name labels to members of $I$ at $v$, include $\kappa$ generators $r\to v$ whose individual maps extend that prescription. Include a spare $r$-loop acting identically on $I$, and a constant generator $r\to s$. The only generator leaving $s$ is a constant map $s\to r$. Individual maps on paths are composites. Different formal paths remain different arrows even if their maps on individuals agree.

At either object $u$ an entity of relational type $\bar\sigma t$ has an arbitrary tuple row on $D_{v,\bar\sigma}$ for each outgoing arrow $p:u\to v$. For propositions the tuple is empty. The identity row gives current application. Transport along $p$ restricts the array to paths starting with $p$ and drops this prefix. Rows at all paths and tuples determine the entire entity. An abstract takes at $p$ the extension of its body on the transported parameters and all arguments at $v$. These rows are admitted, so this is the full action interpretation of C.

The scalar Boolean algebra at $u$ is the powerset of its outgoing paths. Consider the pure sentence

$$
 Q=\exists x^e\,y^e\bigl(x\ne y\land\operatorname{Atom}_t(x\ne y)\bigr).
$$

At $s$ the disequality of any distinct pair is supported on precisely $1_s$, since every proper path begins with the constant map. This support is an atom. At $r$ the support of each actual disequality includes both $1_r$ and the spare loop, so it cannot be an atom. Hence $\neg Q$ is true at $r$ and false at an accessible point.

Closed pure sentences depend only on the object. From either site, every target can reach that site again. A closed pure sentence true at the site consequently remains possible after every arrow. This proves pure B at each site.

## Interpreting the signature

In the fixed pure model list the pure matrices and matching lists of distinct names having a witness at either site. There are at most $\kappa$ requirements. For each choose a site and a witnessing tuple. Choose a different first generator from $r$ to that site implementing the finite prescription on the individual names. There are $\kappa$ compatible choices for each requirement, so the selection works also for singular $\kappa$.

For each matching relational name set its entire array below the chosen generator equal to the array of the chosen witness, identifying continuations with outgoing paths at the target. Each first generator has a disjoint set of continuations. Fill all remaining rows arbitrarily. At the chosen arrow the named tuple is exactly the witness, including its values at all continuations. This proves Possibly Witnessed Possibility at $r$. The interpretation of the names leaves $Q$ and pure B unchanged.

## Other verdicts

* At every relational type, joins are unions of sets of path-and-tuple positions. Each occupied position supplies an atom below its relation. Unique factorization sends such a singleton under any transport to another singleton or bottom. This gives necessary Boolean Completeness and Strong Atomicity at every relational type. The proposition supported just at the identity is a true strong atom. It becomes bottom after every proper path. For any current truth $p$ it therefore gives $q\land\Box(\Diamond q\to p)$, establishing necessary Truths are ND-necessary.
* Restriction of a relational array is surjective by extension on the corresponding path sector, giving necessary relational BF. At the constant $r\to s$ generator a missing individual is detected by the property which is full at all positions except for that individual at that one path. It necessarily accepts every current individual but fails there. This refutes all-type BF at $r$.
* A relation with current row $E$ is weakly rigid precisely when its row at each $p$ is $p[E]$. Weak persistence gives one inclusion. If a new tuple were present, the tester full except for that tuple at that path would contradict weak inextensibility. The direct-image description implies both weak conditions and is hereditary by composition. All direct-image arrays are admitted, giving necessary Rigid Comprehension. Below a rigid bound with row $E$, consider a rigid subrelation at $p$ with row $V\subseteq p[E]$. The source subset $\{x\in E:p(x)\in V\}$ maps onto $V$. Its direct-image profile is a rigid subrelation of the bound and transports to the requested whole subrelation. Thus both canonical powers have exactly the direct images of their members throughout, giving necessary Rigid Power and necessary Weakly Rigid Power.
* In ZFC choose a well-order at each target as its corresponding path row. This single relation necessarily well-orders the carrier. For a necessarily inhabited property, choosing one member of each row likewise gives a necessary singleton subrelation. These give Modal Well-Ordering and necessary Intensional Choice.

The free-path signature gluing adapts [the map's full free-monoid construction](full-free-monoid-glued-constants.html). The two-site separation is by OpenAI Codex (GPT-6), prompted by Daniel Kodsi, 27 November 2026. Two further GPT-6 researchers independently checked the core separation. One also checked the supplementary verdicts.
