# Full present: Rosser-selected C5 component

Daniel Kodsi, with ChatGPT assistance. 30 October 2026.

There is a classical Henkin model of $C$ satisfying **necessary Weakly Rigid
Power**, and therefore necessary Rigid Power and necessary Tame Rigidity, while
failing both **Necessity of Arithmetic** and **Arithmetic Necessitism**.
The arithmetic failures occur at counting type $e$, with $\Box I^*_e$ true.
The power assertions hold at every finite argument tuple, including the
empty tuple and tuples containing individuals.

The construction uses the arithmetically disagreeing component from
[the Rosser-selected Cohen model, §§1–2](symmetric-cohen-arithmetic-contingency.md),
but attaches a different present to it. The contribution is an exact
description of rigid relations in a full present over a C5 component, followed
by the power lift and the arithmetic separation in that same model.

## 1. The component and its arithmetic

We first specify the component whose existence the cited proof supplies.
Its effective many-sorted first-order theory $T_H$ has a sort for every
admitted type, the original application and quantifier operations, a
classical truth predicate, and all finite parameterized lambda-template
operations. Its axioms include the Boolean and quantifier truth clauses,
actual equality, the H axioms, the lambda conversion laws, C5, $\Box I^*_e$
and the boxed absence of real structures at each type. Instances of Logical
Equivalence are admitted only with certificates of **H-theoremhood**.
Equivalence from the additional premises of $T_H$ does not license them.

The standard-arithmetic component of
[the Cohen arithmetic-growth proof, §§2–5](symmetric-cohen-arithmetic-growth.md)
is a model of $T_H$. Its canonical number field and its native Sum and Prod
graphs are standard. Consequently the arithmetic theory

$$
U=\{\varphi:T_H\vdash
  \operatorname{True}(\operatorname{val}(\varphi^e))\}
$$

is a sound computably enumerable extension of PA. Here $\varphi^e$ is the
map's individual-counting translation, with number variables of type
$\nu=(et)t$ and addition and multiplication expressed by their native
graphs. Numerical induction and total unique recursion graphs give the
effective PA interpretation; no operation is selected from a graph.
Finite certificates for enumerated axioms make finite proofs effectively
recognizable.

Rosser incompleteness gives a standard-true arithmetic sentence $G$
unprovable in $U$. First-order completeness and countable
Löwenheim–Skolem give a countable pointed classical Henkin model $A$ of

$$T_H+\neg\operatorname{True}(\operatorname{val}(G^e)).$$

Retain this particular $A$ and $G$. In particular,

$$
(I^*_e)_A=\top_A,\qquad
g:=(G^e)_A\ne\top_A.
\tag{1}
$$

The second assertion does not say $g=\bot_A$. Current falsity is sufficient.
C5 makes equality crisp as a proposition: an identity has value $\top_A$
and an inequality has value $\bot_A$. The component retains its original
quantifiers, ranging over every admitted object of the corresponding sort.
These facts, with its classical truth clauses and lambda operations, are
the hypotheses used below. We do not transfer its absence of real
structures to the model being constructed.

This is a construction in ZFC using the stated Henkin existence argument.
It requires neither a countable transitive model of ZFC nor a generic over
the entire universe.

## 2. A full present over the component

The following construction works first for any pointed classical Henkin C5
component $K$ with crisp equality. Choose a nonempty set $R_e$ and a map
$q_e:R_e\to K_e$. For every flattened relational type
$\tau=\alpha_1\cdots\alpha_k t$, define recursively

$$
R_\tau=
\mathcal P\!\left(\prod_{i=1}^{k}R_{\alpha_i}\right)\times K_\tau,
\qquad
q_\tau(S,f)=f.
\tag{2}
$$

The product for the empty tuple is a singleton; in particular,
$R_t=2\times K_t$. Every current row is admitted, independently of its
component entity. For a tuple write $\bar q$ for the componentwise
projection.

Application uses the current row and the component application. Partial
application takes the corresponding slice of the row and applies the
component entity to the projected argument. A lambda abstraction has the
extension of its body at the new present as its first coordinate and the
original $K$ abstraction with projected parameters as its second coordinate.
A quantified formula has its ordinary classical truth value over the full
$R$ domain in the first coordinate and its original $K$ quantifier value
over the full $K$ domain in the second coordinate. In particular, the second
quantifier is not restricted to the image of $q_e$.

Induction on terms gives

$$q(T^R(\bar a))=T^K(\bar q(\bar a)).\tag{3}$$

Current singleton rows make equality at the new present literal identity
of entities. The H axioms hold at that present and in the component.
For an H-theorem equivalence of two bodies, their current lambda rows agree,
and C in $K$ identifies their component abstractions. Thus the lambda
entities themselves agree. This validates precisely C's Logical Equivalence
schema, without admitting equivalences from optional premises. The
construction therefore gives a model of $C$. It does not require an action
representation of $K$.

For a proposition $B$ with fixed root parameters, equality-defined
necessity has the exact truth condition

$$
R\models\Box B
\quad\Longleftrightarrow\quad
R\models B\ \text{ and }\ B^K=\top_K.
\tag{4}
$$

Since equality in $K$ is crisp, $\Box_K p$ is $\top_K$ exactly when
$p=\top_K$, and is $\bot_K$ otherwise. For $F=(S,f)$ and $Z=(T,z)$,
(3)–(4) give

$$
R\models F\le Z
\quad\Longleftrightarrow\quad
S\subseteq T\ \text{ and }\ K\models f\le z.
\tag{5}
$$

The second condition is the old **necessary** universal inclusion.
It is stronger than inclusion between two current component extensions.
All later uses of an outer box use (4); they are not applications of
necessitation to an argument from optional assumptions.

## 3. Exactly which pairs are rigid

Write

$$
\operatorname{ext}_K(f)=
\{\bar b:K\models f[\bar b]\}.
$$

First observe that a persistent component relation has only top or bottom
membership values. For each tuple $\bar b$, necessary universal elimination
from persistence gives the Boolean inequality
$p\le\Box_Kp$, where $p=f[\bar b]$. If $p\ne\top_K$, crisp equality makes
$\Box_Kp=\bot_K$, hence $p=\bot_K$. In particular, membership in a rigid
component relation is currently true exactly when its whole value is top.
This observation does not assert that all component propositions are
bivalent.

The key criterion is

$$
R\models\operatorname{Rigid}(S,f)
\quad\Longleftrightarrow\quad
K\models\operatorname{Rigid}(f)
\ \text{ and }\
\operatorname{ext}_K(f)=\bar q[S].
\tag{6}
$$

For necessity, write rigidity as necessary weak rigidity. By (4), rigidity
of $(S,f)$ makes the whole $K$ value of weak rigidity of $f$ top; hence $f$
is rigid in $K$. Root weak persistence makes $f[\bar q(\bar a)]$ top for
every $\bar a\in S$, giving one image inclusion.

For the reverse image inclusion, fix any $\bar b\notin\bar q[S]$. The
component predicate

$$z_{\bar b}:=\lambda\bar x\,.\,\neg(\bar x=\bar b)$$

is admitted. Its value is top on every tuple other than $\bar b$, by crisp
equality. Pair it with the full current row to obtain a root test
$Z_{\bar b}$. This test is necessarily true of every tuple in $S$.
Root weak inextensibility gives $(S,f)\le Z_{\bar b}$, so (5) gives
$f\le z_{\bar b}$ in $K$. If $\bar b$ belonged to $\operatorname{ext}_K(f)$,
T and current universal elimination would contradict
$z_{\bar b}[\bar b]=\bot_K$. Each missing tuple is tested separately;
no component predicate for the set of all missing tuples is assumed.

For sufficiency, suppose $f$ is rigid and its current extension is
$\bar q[S]$. The membership observation gives root weak persistence.
Let $Z=(T,z)$ be any root test necessarily true at every tuple in $S$.
Then $S\subseteq T$ and $z$ has whole value top on $\bar q[S]$.
Consequently the following **current** premise is true in $K$:

$$\forall\bar b\,.\,f[\bar b]\to\Box z[\bar b].$$

Apply $f$'s component weak inextensibility to obtain $f\le z$.
Equation (5) yields $(S,f)\le Z$, establishing root weak inextensibility.
Component rigidity makes the whole old weak-rigidity value top;
(4), with the root weak rigidity just proved, gives full root rigidity.

This argument uses the component's current quantifier truth clause and its
weak-inextensibility clause. It does not infer that a universal has whole
value top merely because all its separately evaluated instances do.

## 4. The canonical rigid power and its box

Fix a root rigid $F=(S,f)$. If an admitted component relation $h$ is rigid
and $h\le f$, put

$$
S_h=\{\bar a\in S:\bar q(\bar a)\in\operatorname{ext}_K(h)\},
\qquad X_h=(S_h,h).
$$

Every component member of $h$ belongs to $\operatorname{ext}_K(f)$ and
therefore has a preimage in $S$ by (6). Thus
$\bar q[S_h]=\operatorname{ext}_K(h)$. Equations (5)–(6) show that $X_h$
is rigid and below $F$. This lifts every **admitted rigid component
subrelation**; it does not claim that every current subset of $S$ has a
rigid lift.

Now consider the literal native lambda entity

$$
\mathcal P_R(F):=
\lambda X\,.\,\operatorname{Rigid}(X)\land X\le F.
$$

Its component is exactly $\mathcal P_K(f)$, by term projection. Its current
row $C_F$ consists of all root rigid subrelations of $F$. Projection sends
each such member to a component rigid subrelation of $f$, and the preceding
construction supplies a preimage for every such component subrelation.
Hence

$$q_\tau[C_F]=\operatorname{ext}_K(\mathcal P_K(f)).\tag{7}$$

The recorded C5 power theorem makes $\mathcal P_K(f)$ rigid. Its proof uses
S5 stability of the boxed conjuncts defining the family and component
Barcan to obtain persistence and inextensibility. Apply (6) at the next
type to (7): the **canonical** $\mathcal P_R(F)$ is rigid. No replacement
by a merely coextensive family occurs.

This proves Rigid Power at the new present. C5 also gives the whole
component value of the entire Rigid Power instance as top. Equation (4)
therefore proves its outer box at the root.

Nothing requires $q_e$ to be onto. Mixed tuples of individuals and
relations are handled by the same complement tests. For the empty tuple,
the argument product is a singleton and the missing-tuple complement is
bottom; the same proof gives the nullary instance.

## 5. Tame Rigidity and Weakly Rigid Power

Suppose only that $F=(S,f)$ is weakly rigid at the root. Both image
inclusions in §3 used only weak persistence and weak inextensibility, so
$\operatorname{ext}_K(f)=\bar q[S]$ still follows.
Root weak persistence makes $f[\bar b]$ top for every current component
member $\bar b$ of $f$. Thus $f$ is weakly persistent in $K$.

For any admitted component test $z$ satisfying
$\forall\bar b(f[\bar b]\to\Box z[\bar b])$ currently in $K$, pair $z$
with the full root row. This root test is necessarily true on $S$.
Root weak inextensibility and (5) give $f\le z$ in $K$.
Therefore $f$ is weakly inextensible, hence weakly rigid, in $K$.

C5 implies Tame Rigidity, so $f$ is fully rigid in $K$. Its whole
weak-rigidity value is consequently top. Together with the given root
weak rigidity, (4) proves full rigidity of $F$. This establishes root
Tame Rigidity. The component's necessary Tame Rigidity makes the entire
old schema value top; (4) supplies the required outer box.

The recorded implication

$$
\Box\text{Tame Rigidity}+\Box\text{Rigid Power}
\ \Longrightarrow\ \Box\text{Weakly Rigid Power}
$$

now gives the stated strongest power verdict. The proof of that implication
uses necessary Tame Rigidity to identify the weak and full canonical power
predicates at the required modal scope. The argument includes all the
arities covered in §4.

## 6. Standard arithmetic at the new present

Specialize to the component $A$ from §1, and take

$$R_e=\omega\times A_e,\qquad q_e(n,a)=a.$$

Use the map's own $\mathbf0_e$, successor, $\mathbb N_e$, Sum and Prod.
Let $\bar n^R$ be the $n$-fold application of its closed successor term to
its closed zero, and let $O=\{\bar n^R:n\in\omega\}$.
The row $O$, paired with any component predicate, is an admitted
induction test. It contains zero and is closed under the actual root
successor. The least-inductive definition of $\mathbb N_e$ therefore
excludes every entity outside $O$. Conversely every admitted inductive
predicate contains each standard iterate by finite induction. Thus

$$\operatorname{ext}_R(\mathbb N_e)=O.\tag{8}$$

Term projection sends $\bar n^R$ to $\bar n^A$. The component's $I^*_e$
makes its standard numerals pairwise distinct; root numerals are therefore
pairwise distinct as well. Equation (8) gives current $I^*_e$ directly,
and its component is top by (1). Hence

$$(I^*_e)_R=(1,\top_A)=\top_R,\qquad R\models\Box I^*_e.\tag{9}$$

Standard number objects alone do not settle the arithmetic graphs.
For fixed standard $m$, the admitted current row

$$\{(\bar i^R,\overline{m+i}^R):i\in\omega\}$$

satisfies the native Sum initial and closure conditions and rejects every
incorrect standard output. Conversely any current relation satisfying
those conditions contains each correct pair by finite induction. The
universal definition of Sum consequently gives

$$R\models\operatorname{Sum}(\bar m,\bar n,\bar o)
\quad\Longleftrightarrow\quad o=m+n.$$

For Prod use
$\{(\bar i^R,\overline{mi}^R):i\in\omega\}$. The just-established Sum
calculation proves its closure condition. Finite induction puts each
correct product in every test satisfying the recursion premises; the
displayed graph excludes incorrect products. Thus Prod is standard too.
These are relational tests admitted by full current rows, paired with
arbitrary component entities. No arithmetic operation is selected from
its graph.

Induction on the native first-order arithmetic grammar now gives standard
arithmetic at the root. Its restricted current quantifiers range over
$O$, while its component quantifiers retain the whole number field of
$A$. For the **same** sentence $G^e$ as in §1,

$$(G^e)_R=(1,g),\qquad g\ne\top_A.\tag{10}$$

## 7. Both arithmetic failures with the guard true

By (9), $I_e=\Diamond I^*_e$ is also the whole top entity. In the exact
Necessity of Arithmetic instance

$$\Box(I_e\to G^e)\ \lor\ \Box(I_e\to\neg G^e),$$

the first alternative fails by (4) and (10), because $g\ne\top_A$.
The second fails because $\neg G^e$ is currently false.
This refutes the native guarded disjunction, with $\Box I^*_e$ true.

For the entity-level failure, $A$ has a current canonical number $c$
which is not a standard numeral. Otherwise its PA structure, including
the total unique Sum and Prod graphs, would be standard and could not
falsify the standard-true $G$. The admitted component predicate

$$z:=\lambda n^\nu\,.\,n\ne c$$

has whole value top on each standard component numeral, by crisp equality.
Pair $z$ with the full current $R_\nu$ row to obtain $Z$.
Every current root number is a standard numeral by (8), so each necessarily
satisfies $Z$. But the whole component quantifier sees the current
counterexample $c$ to $\mathbb N_A\subseteq z$. Hence its inclusion
formula is not top, and (5) gives

$$R\not\models\mathbb N_e\le Z.$$

This is a direct weak-inextensibility countertest for the canonical
$\mathbb N_e$. It is not rigid. Together with (9), it refutes the
type-$e$ instance of Arithmetic Necessitism with its antecedent true.

The two arithmetic failures and all the power verdicts concern this one
model. No verdict about Analytic Necessitism, SOAN, Boolean
Completeness or C5 at the root is asserted. In particular, the component's
absence of real structures does not pass to a root with this different
admission rule. Neither arithmetic failure is claimed necessary or at
every counting type.

## Sources and attribution

The general pair construction is OpenAI Codex, prompted by Daniel Kodsi,
*Classical present over an arbitrary model*, 25 October 2026, §§1–2.
The explicit C interpretation is retained in §2 above. The
Rosser-selected component is from GPT-6 Astra, prompted by Daniel Kodsi,
[Symmetric Cohen model: Rosser-selected component](symmetric-cohen-arithmetic-contingency.md),
30 October 2026, §§1–2.

The component power theorem is the recorded *C5 implies necessary Rigid
Power*, Claude Opus 5.5 (Anthropic), answering Cian Dorr, 3 October 2026.
The component Tame Rigidity theorem is due to Christopher Sun,
*Possible Worlds Without Atomicity*, September 2026; its necessitation and
the necessary-power composition are recorded separately in the map.
The exact-image criterion and its lift to the canonical family are the
additional arguments here.

The numeral-orbit and recursion-test methods have a prior instance in
Cian Dorr's coalesced-root constructions, especially
*coalesced-pinned-substitutions-nonstandard-root*, Claude Opus 5.5
(Anthropic), prompted by Cian Dorr, 29 October 2026, extending the
19 October construction. They are checked above for this particular
pair model and the same $A,G$.

The proof is mathematical, with no claimed independent human check or
new Lean verification.
