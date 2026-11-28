# Finite multisets with free words

For each set-sized signature there is a C action model in which Logical
Necessity holds, Strong Atomicity at every relational type holds necessarily,
and the Barcan Formula holds necessarily at every type. An admitted family of
propositions has no least upper bound. In particular, Logical Necessity and
necessary Strong Atomicity together do not imply propositional Boolean
Completeness.

## A one-object action

Put $\kappa=\max(\aleph_0,|\Sigma|)$ and take an index set $I$ of cardinality
$\kappa^+$. A finite multiset is a finitely supported function
$s:I\to\mathbb N$. Its size is $|s|=\sum_i s(i)$. Write $W$ for the free
monoid of finite words on an alphabet of size $\kappa$. The arrows at the sole
object are all pairs $(s,w)$, with composition
\[
  (t,v)(s,w)=(t+s,vw).
\]
The identity is $(0,\epsilon)$. There is one individual.

Define the domains recursively. At type $\alpha_1\ldots\alpha_k t$ a profile
$X$ assigns each arrow $(s,w)$ a row $X_{s,w}$ of tuples from
$D_{\alpha_1}\times\cdots\times D_{\alpha_k}$. At $k=0$ the rows are truth
values. For admission there must be an $S\subseteq I$ of size at most $\kappa$
such that
\[
  |s|=|s'|,\quad s|_S=s'|_S
  \quad\Longrightarrow\quad X_{s,w}=X_{s',w}
\]
for every $w$. Call $S$ a pin. Transport is precomposition. The same $S$ pins
every transport of $X$. Moreover arrows of the same size and word agreeing on
$S$ transport the whole entity $X$ equally, since adding a common multiset and
prepending a common word preserves the comparisons.

The union of the pins of finitely many parameters pins the profile of any
lambda term in them. Indeed, comparison arrows transport all parameters
equally to the sole object, where the body can be evaluated at every argument
tuple. This includes modal and quantified bodies. The individual parameter
does not affect a comparison. Application evaluates the identity row, and
equality at relational types is agreement of rows on all tuples after all
continuations. These operations give the action semantics of C. Native
entailment is inclusion at every row. Each external set of current tuples
occurs as an identity row, for example in the profile with that same row
everywhere. Truth of a closed pure formula is consequently the same at
the target of every arrow, because there is only one object.

## Strong atoms at every relational type

Every single arrow $(s,w)$ is isolated by its word, size, and the multiplicities
on $\operatorname{supp}(s)$. In fact these finitely many coordinates carry
its full size, so a matching multiset has zero multiplicity off that support.
Suppose $X\ne\bot$ and $b\in X_{s,w}$. Take $Q$ with sole nonempty row $\{b\}$
at $(s,w)$. It is pinned by $\operatorname{supp}(s)$, satisfies $Q\le X$,
and is an atom by row inclusion. Given an arrow $h$, at most one continuation
$u$ solves $uh=(s,w)$, by cancellation of multiset addition and right
cancellation of words. Thus $hQ$ is bottom or has a single row consisting
of a single tuple. In either case it entails every entity of its type or
its complement. This proves $Q$ is a strong atom and gives necessary Strong
Atomicity, including the propositional instance. At the identity the
single-arrow proposition is a true strong atom as well.

At the designated point let $q$ be the proposition true only at the identity.
Every proper arrow takes $q$ to bottom, so at its target $\Diamond q$ is false.
At the identity, any current truth $p$ holds. Hence $q$ witnesses
$\Box_{\ne}p$ by $q\land\Box(\Diamond q\to p)$. The resulting universal
statement is pure and holds at every object.

## The Barcan Formula

Transport is onto at every type along every arrow. This is immediate for the
one individual. Let $X$ be a relation with pin $S$ and let $h=(a,w)$.
For a source profile $Y$, prescribe
\[
 Y_{t,v}=
 \begin{cases}
   X_{t-a,u},& t\ge a\text{ coordinatewise and }v=uw,\\
   \varnothing,&\text{otherwise}.
 \end{cases}
\]
The condition $t\ge a$ can be decided on the finite support of $a$.
At equal total sizes, subtraction of $a$ leaves equal total sizes; agreement
on $S$ remains agreement there. Thus $S\cup\operatorname{supp}(a)$ pins $Y$.
By construction $hY=X$. Every possible existential witness therefore lifts
along its witnessing arrow to a current entity, proving Barcan at each type.
This also holds necessarily.

## Countable Boolean Completeness

For each base type $\sigma$ take as a current property of numerical entities
the externally enumerated set of values of the standard Frege numerals at
$\sigma$. This is an admitted identity row. It contains zero and is closed
at this object under successor, so Frege induction puts every current
$\sigma$-number in this set. In particular, there are at most countably many
current numbers, including when different numerals have the same value.

The map's predicate for countability provides each current member of a
countable family with a nonempty fiber of numerical values, with disjoint
fibers for distinct members. Taking the least standard index representing a
value in each fiber injects the family into the ordinary natural numbers.
For any such family of relations, form the union of its members row by row.
A countable union of pins of size at most $\kappa$ has size at most $\kappa$,
so the union profile is admitted. By rowwise inclusion it is the least upper
bound. This proves necessary Countable Boolean Completeness at all the
indicated types.

## Logical Necessity

Use the [free-word gluing of typed constants](supported-product-free-monoids-glued-constants.html).
For each $\Sigma$-sentence realizable by an assignment to the constants at
this object, choose such an assignment $J_i$ and a distinct letter $i$.
There are at most $\kappa$ sentences. Give every individual name its unique
interpretation. For each relational name $c$, set
\[
 c_{s,vi}=(J_i(c))_{s,v}
\]
on words ending in a designated letter, with empty rows elsewhere. The
union of the at most $\kappa$ constituent pins has size at most $\kappa$.
Transport along $(0,i)$ now takes all the constants simultaneously to
the assignment $J_i$. Hence each realizable sentence is possible under
this interpretation. Conversely a possible instance is realized at the
sole object under the transported values. For a pure matrix with its free
variables replaced by distinct matching names, classical duality gives
$\Box P[\bar c]\leftrightarrow\forall\bar x\,P[\bar x]$, also for the
empty tuple. This proves Logical Necessity at the designated identity.

## A family of atoms without a join

Partition $I$ into $J$ and $K$, each of cardinality $\kappa^+$. Write
$\delta_i$ for the one-element multiset supported at $i$ and let $p_i$ be
the single-arrow proposition supported at $(\delta_i,\epsilon)$. The current
family $\{p_i:i\in J\}$ is an identity row of an admitted property of
propositions. If it had a least upper bound $L$, then $L$ would hold at all
$(\delta_i,\epsilon)$ for $i\in J$. For each $j\in K$, the complement of
$p_j$ is an upper bound, so $L$ would fail at $(\delta_j,\epsilon)$. A pin
for $L$ misses an $i$ in $J$ and a $j$ in $K$. The corresponding multisets
agree on the entire pin, both have total size one, and both arrows have the
empty word. Their $L$-values must coincide, a contradiction. This gives
failure of propositional Boolean Completeness and its necessary form.

OpenAI Codex (GPT-6), prompted by Daniel Kodsi, developed this construction
on 26 November 2026. Two additional OpenAI Codex agents independently
checked the construction and the separation.
