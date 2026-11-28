# Maximalism and propositional Boolean Completeness

Dorr’s boxed result follows directly from an instance of propositional Boolean Completeness that fails in a model of C. Its negation is a consistent closed pure sentence, so pure Maximalism requires that negation to be possible. Necessary Boolean Completeness requires the same instance to be necessary. [Finite-support permutation model](finite-support-permutations.html)

## The unboxed question

OpenAI Codex (GPT-6), prompted by Daniel Kodsi, developed the following conditional construction on 26 November 2026. It concerns local Boolean Completeness.

Let $M_\Sigma$ be signature Maximalism, and let $C_t$ be the native
unboxed propositional Boolean Completeness principle. The following
decision reduction is unconditional:
\[
 M_\Sigma+C_t\ \vdash\text{every truth is ND-necessary}
 \quad\Longleftrightarrow\quad
 M_\Sigma+C_t\text{ is inconsistent}.
\]
The same equivalence holds with two-hat necessity or 5-necessity replacing
ND-necessity on the left. If the joint theory is consistent, it admits a
Strong Actuality point realizing either outcome for each collapse. A subsequent proof excludes the joint theory even for pure Maximalism, by exhibiting one countable family of propositions without a least upper bound. The conditional construction below uses Boolean Completeness for admitted families. [The unboxed incompatibility](pure-maximalism-and-boolean-completeness-t-incompatible.html)

## Changing a root without making its families externally full

Take any C action model with a distinguished point $r$; discard objects
outside its cone. Adjoin an anterior object $R$, with a finite group $G$
of endomorphisms. Its exits to the old cone are indexed by the arrows
originating at $r$; following any root loop leaves an exit unchanged. Old
arrows postcompose exits as usual. There are no arrows back to $R$. Root
individuals are the individual entities at $r$, fixed by $G$, and transport
along the entrance $R\to r$ is the identity on them.

At a relational type $\tau=\bar\alpha t$, a new entity is a pair consisting
of an old entity $a\in D_\tau(r)$ and a tuple row $U_g$ on the new arguments
for each $g\in G$. The old entity determines all rows on exits. Root loops
act by shifting the finite list of rows by right composition and leave the
old trace fixed. The rows $U_g$ must have codes at $r$, as follows.

Inductively, each new sort is given by finitely many tags, each carrying a
tuple of elements of a finite list of old sorts, subject to an old
current definable validity predicate and an old current definable
equivalence of codes. This holds at $e$ with one old variable, and at $t$
with finite tags for the loop bits and one old proposition. For a general
relational type, use one old trace variable. For each loop and combination
of argument tags use one old relational variable on the concatenated
argument coordinates. Require that its current values on valid argument
codes depend only on the represented arguments, including agreement across
equivalent tags if necessary. These are old quantified formulas on finite
lists of typed variables. Two codes for the resulting entity are equivalent
when their old traces agree as entities and all their current coded rows
agree on all valid arguments. Using fixed chosen normal tags for the
finitely many truth bits is an equivalent presentation. Lambda
comprehension at $r$ codes every definable row on these coordinates.
In particular the empty current rows are allowed with every old trace,
so each entrance projection is onto its old sort.

These are precisely admissible outgoing profiles: equality of old traces
is equality at all continuation rows past $r$, and each new-loop row is
already on the quotient of tuple codes. To check term closure, represent
each finite tuple of new parameters by old parameter codes. The old
trace of the new interpretation of a term is the ordinary old term on the
traces. Its current row at a loop is an old definable predicate on
the argument codes. This follows simultaneously by term recursion.
At an application use the relevant row code on the argument codes.
A partial application retains the remaining arguments as row variables,
and takes the old partial application as trace. For a lambda, evaluate
the body at each loop on transported parameters and newly supplied
argument codes, and use old comprehension on this translated predicate.
Quantification ranges over valid codes and the finite tags. Equality at
any type is the displayed finite trace-and-row equivalence, with identity
of old entities in the trace. If box is treated as primitive, at $R$ one
checks the translated current formula at all finitely many loop transports,
and also the *ordinary old* boxed formula on the traces at $r$. This last
test evaluates in the old cone. It agrees with the definition of box by
proposition identity with top. Thus the entire construction is within
C, even if not all external sets of old entities have property codes.

## Preserving BC and Max

At $t$ the new algebra is $\mathcal P(G)\times B_r$, with product order.
Indeed the finite bits decide all loop rows and the old order decides all
rows in the old cone. Let $Y$ be any admitted current family at $R$. Its
projection to $B_r$ is an admitted predicate at $r$: for a trace variable
$p$ take the finite disjunction over all bit tags of the corresponding
row-code membership tests for $(\text{tag},p)$. Let $l$ be its supremum
in $B_r$. Let $D\subseteq G$ be the union of the bit sets of the current
members of $Y$. Then $(D,l)$ is the product-order supremum of $Y$. This
argument does not require the projection to preserve arbitrary external joins.

In fact local Boolean Completeness at any relation type is preserved by
the same construction. Project a current family of new entities to the
old trace variable by existential quantification over all valid family
member codes. At each root loop take the rowwise union of the new current
members; its membership is again old definable by the same existential
quantification over their codes. With the old supremum as trace and these
admissible loop rows, order inclusion at every loop and at the old trace
shows that this new entity is the least upper bound.

Lift the interpretation of each signature constant along the entrance;
empty loop rows suffice for relational constants. Any failed closed
$\Sigma$-identity at $r$ fails at $R$: its two sides transport to the
old unequal entities. Consequently $M_\Sigma$ at $r$ implies $M_\Sigma$
at $R$, without an assumption about the truth of individual closed
sentences at $R$.

## Tuning the modal collapse

With $G$ trivial, let $\delta$ be true exactly at the new identity, with
old trace bottom. For any true $p$ at $R$ the condition
$\Box(\Diamond\delta\to p)$ holds, since no old point can return to
$R$. Thus $\delta$ witnesses $\Box_{\ne}p$. It is also a true strong
atom.

With $G=C_2=\{1,s\}$, let $\delta$ again select only the new identity.
For any true $q$ at $R$, $\Diamond q$ holds after $s$ by returning along
$s$, whereas $\delta$ is false there. No $q$ witnesses
$\Box_{\ne}\delta$.
For the stronger conclusion, take an operator $X$ whose two loop rows
both accept exactly the propositions whose two bits are true, with old
trace the identity operator. The row is definable from the two finite
bits. At a new loop $h$, $X$ tests both $h$ and $sh$. N and K hold
there, and B follows from $s^2=1$. At old points the identity operator
satisfies all three axioms. Hence $X$ is S5 in the entire cone. Since
$X\delta$ fails, $\Box_5\delta$ fails as well, and so does two-hat
necessity. The proposition $\delta$ is nevertheless a true strong atom:
its loop transports are singleton atoms and its old trace is bottom.

The elementary code construction and the typed componentwise supremum
supply the substantive direction of the decision reduction. The other
direction is immediate from inconsistency. The construction and the
proof at $t$ were independently reviewed by a second GPT-6 agent on
26 November 2026.
