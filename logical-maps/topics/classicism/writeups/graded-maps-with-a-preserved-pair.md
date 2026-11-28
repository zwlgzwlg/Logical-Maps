# Graded maps preserving an individual pair

Logical Necessity and necessary Countable Boolean Completeness can hold
at a point where a weakly rigid individual property ceases to be
weakly inextensible after one arrow. The same model admits a modal
well-order at every type.

## The model and the signature

Fix $\kappa\ge\max(2^{\aleph_0},|\Sigma|)$ and a set $A$ of size
$\kappa^+$ with a distinguished pair $B=\{b_0,b_1\}$. There is one
object, with individuals $A$. Its arrows $(f,n,w)$ have natural-number
grade $n$ and a word $w$ on a $\kappa$-letter alphabet. At grade zero
allow all maps $f:A\to A$ with $f[B]\subseteq B$. At positive grades
allow all maps $f:A\to B$. Composition sends a pair of arrows to the
composed map, the sum of their grades and the concatenation of their
words, with a later word prepended. The identity is
$(\mathrm{id}_A,0,\varepsilon)$. The specified maps are closed under
composition.

As in the [graded-maps model](graded-maps-free-words-glued-constants.html),
a relation profile assigns an arbitrary tuple row to each arrow. There
must be a pin $P\subset A$, $|P|\le\kappa$, such that at fixed grade
and word the row depends only on $f|_P$. For individuals use the
displayed map, and for relations use $(hX)_u=X_{uh}$. An $X$ pinned by
$P$ transports along $(f,n,w)$ to an entity pinned by $f[P]$. Arrows
agreeing on $P$ at fixed grade and word transport the entire relation
equally, by composing with every continuation. The union of parameter
pins pins the lambda profile, since its body depends on the transported
parameters. The resulting action interpretation is a model of C. Any
external set of tuples is an actual row, by using that row constantly.
Pure sentences have the same truth at every arrow.

To glue the signature, assign distinct individuals outside $B$ to
the individual names. For each signature sentence realizable at the
object under some assignment, choose such an assignment $J_i$ and a
different last letter $i$. Choose a surjection $f_i:A\to A$ fixing $B$
and giving the required values to the finitely many named individuals
of the sentence. The remaining $\kappa^+$ points allow surjectivity.
Choose a right inverse $s_i$ of $f_i$ fixing $B$. For each relational
name $c$, prescribe at $(l,n,vi)$ the $(l s_i,n,v)$-row of $J_i(c)$.
The composite is allowed at both kinds of grade since $s_i$ fixes
$B$. Use empty rows at every remaining address. If $P_{i,c}$ pins
$J_i(c)$, then $\bigcup_i s_i[P_{i,c}]$ pins the glued entity and
has size at most $\kappa$. At $(f_i,0,i)$ each named entity takes its
prescribed value, since $f_i s_i=\mathrm{id}_A$. Conversely truth
at an arrow yields a realizing assignment at the same object. This
establishes Logical Necessity for all distinct matching names.

## A weakly rigid property that ceases to be weakly inextensible

Let $F$ have row $A$ at grade zero and row $B$ at every positive
grade. It has empty pin. Every actual individual belongs to $F$
necessarily, since a positive arrow sends it into $B$.

Suppose a tester $Z$ necessarily contains every actual member of $F$,
and let $P$ be a pin for $Z$. For $h=(f,n,w)$ and $y\in F_h$ choose
$x\in A\setminus(P\cup B)$. Change $f$ only at $x$ to send $x$ to
$y$. At grade zero this preserves $B$ and at positive grades $y\in B$,
so the changed arrow is allowed. The tester has the same row as at
$h$, and must contain the transported $x$, hence $y$. Thus $F\le Z$
and $F$ is weakly inextensible at the designated point. Together with
weak persistence this gives weak rigidity.

After any positive arrow, the whole transport of $F$ has row $B$ at
every continuation. The tester $K_{(g,m,v)}=g[B]$ is pinned by $B$
and necessarily contains every one of the two current members.
A continuation can collapse $B$ onto $b_0$, at which point $K$ misses
$b_1$ although the transported $F$ still contains it. Thus the transport
fails weak inextensibility, refuting Tame Rigidity at type $e$.

## Other verdicts

- **Countable Boolean Completeness.** In every counting sort the
  standard Frege numeral values form an admitted inductive current row.
  They exhaust the numbers by Frege induction. The map's relation
  witnessing countability assigns disjoint nonempty fibers in this
  at-most-countable set to distinct family members. Choosing the least
  standard numeral index in each fiber shows that the family is
  externally countable. Its rowwise union is admitted on the union
  of its pins and is its least upper bound. This holds at every
  point.
- **Modal Well-Ordering.** At each type use the constant rows of an
  external well-order of the admitted local sort. It remains the
  same well-order at every arrow and has a least element in every
  nonempty admitted current subset there.
- **BF.** At type $e$, $F$ necessarily contains every current
  individual but fails on individuals outside $B$ at positive arrows.
  At type $t$, a positive arrow transports every current proposition
  to one pinned by $B$, since $f[P]\subseteq B$ for every $P$.
  Use a tester with full row at grade zero and row consisting of the
  $B$-pinned propositions at positive grades. It necessarily contains
  every current proposition. For $d\notin B$, the proposition testing
  $g(d)=b_0$ is admitted with pin $\{d\}$ and is not $B$-pinned:
  two grade-zero maps agreeing on $B$ can differ at $d$.
- **Atomlessness.** Given a nonempty proposition pinned by $P$, fix
  a witnessing arrow. At an input outside $P\cup B$ change its value
  to $b_0$ or $b_1$, preserving the grade and word. Both modified
  maps are allowed. The test for the value $b_0$ at that input splits
  the original proposition into two nonzero parts.
- **Infinity and the analytic principles.** The individual domain is
  infinite and there are infinitely many distinct last-letter
  propositions. With the above numeral cut, neither entire domain
  has a finite Frege count. At type $e$ choose disjoint subsets of
  $A$ representing the ordinary numbers and all their subsets, and
  admit their standard successor and membership graphs as current
  rows. They give a current real number structure. A constant
  positive-grade map collapses every two distinct individuals, so
  the numbers of no such structure can be necessarily distinct.
  This refutes both forms of Analytic Necessitism at $e$.

The propositional Boolean algebra does not even have all joins of
admitted families. Pick $d\notin B$, pairwise distinct
$x_i\notin B\cup\{d\}$ for $i<\kappa^+$ and pairwise distinct
$u_i\in A$. Let $p_i$ hold only on grade-zero empty-word maps with
$f(d)=u_i$ and $f(x_i)=b_0$. This family is an admitted current row.
For each $i$, the complement of the cylinder defined by grade zero,
empty word, $f(d)=u_i$ and $f(x_i)\ne b_0$ is an upper bound for
the family. A least upper bound must therefore, on grade-zero empty-
word maps with $f(d)=u_i$, hold exactly when $f(x_i)=b_0$. For any
proposed pin $P$ choose $x_i\notin P$. Two grade-zero maps can agree
on $P$, have $f(d)=u_i$, fix $B$, and differ on this test at $x_i$.
This contradicts pinning.

## A current set without a weakly inextensible coextension

Choose distinct sites $a_i$ outside the preserved pair and distinct subsets $S_i$ of the nonempty words, for $i<\kappa^+$. There are $2^\kappa$ subsets to choose from. On any nonempty word $w$, the proposition $p_i$ reads $w\in S_i$. At grade zero and the empty word it reads $f(a_i)=a_i$. Put its remaining rows false. The set $E=\{p_i:i<\kappa^+\}$ is an admitted current row.

Suppose $Y$ is a weakly inextensible coextension with pin $P$. Choose $a_i$ outside $P$ and an empty-word grade-zero arrow $h$ fixing $P$ while moving $a_i$. Its map may fix the preserved pair. Then $Y_h=Y_1=E$. Use a tester that omits the single entity $p_i$ on precisely the empty-word grade-zero arrows $g$ which move $a_i$, with full rows elsewhere. This is pinned by $a_i$. It necessarily accepts every member of $E$. On a tested arrow $g$, the proposition $gp_i$ is false at the identity while $p_i$ is true. For $j\ne i$, evaluating $gp_j$ after a nonempty-word continuation reads the distinct label $S_j$, so $gp_j\ne p_i$. But $Y_h$ contains $p_i$ at this tested arrow. This refutes Weakly Inextensible Comprehension at the unary proposition-input type and hence also Inextensible Comprehension.

Since every countable union of pins is a pin, evaluation at a point induces a countably complete ultrafilter in each nonzero scalar interval. The small Cantor regular-open algebra present over the infinite individual domain has no such ultrafilter, refuting revised Mathematical Possibilism. [Smallness and the interval test](partitioned-graded-maps-with-free-words.html)
