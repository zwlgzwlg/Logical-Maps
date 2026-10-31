# Symmetric Cohen model: Rosser-selected component

GPT-6 Astra, prompted by Daniel Kodsi. 30 October 2026.

There is a countable classical Henkin model of $C$ satisfying
**Second-Order Analytic Necessitism but failing Necessity of Arithmetic**.
The arithmetic guard $\Box I^*_e$ holds. All analytic possible-real antecedents
are false.

This changes the ground component of the
[arithmetic-growth Cohen construction](symmetric-cohen-arithmetic-growth.md).
An elementary extension of its standard-arithmetic component preserves every
first-order arithmetic truth. Here an effective theory preserving NoReal lets
Rosser incompleteness select a component that disagrees with standard arithmetic.
The root still has standard current arithmetic. The new combination is this
arithmetic **truth** disagreement with the all-host NoReal construction.
The old named-number-above-all-numerals package is not imposed on the new
component.

## 1. The effective component theory

The base construction in
[Symmetric Cohen model: arithmetic growth, §§2–5](symmetric-cohen-arithmetic-growth.md)
gives a countable ground classical Henkin model $A_0$ of

$$C5+\Box I^*_e+
\{\Box\neg\exists\mathfrak R\,\operatorname{Real}_\tau(\mathfrak R):
\tau\text{ an admitted type}\}.$$

Its current canonical numbers and arithmetic graphs are standard. It also
supplies the exact whole-object equations $I^*_e=\top$ and
$\exists\mathfrak R\operatorname{Real}_\tau(\mathfrak R)=\bot$.
The NoReal theorem and Boolean-Henkin reduction in that proof are essential
inputs. Compactness or incompleteness alone would not establish them.

Fix a countable many-sorted first-order language containing a sort for each
admitted type; application, Boolean proposition operations, typed equality and
quantifier operations; a current-truth predicate $T$; and an operation for
every finite lambda template with its finite typed parameter list. The effective
value translation of a typed term $a$ is written $\operatorname{val}(a)$.
Let $T_H$ contain the following effective schemes, universally closed over their
finite parameter contexts:

* The proposition Boolean-algebra equations, $T(\top)$, $\neg T(\bot)$,
  $\top\ne\bot$, and the Boolean truth clauses.
* $T(\operatorname{Eq}_\sigma(x,y))\leftrightarrow x=y$ and
  $T(Q_\sigma F)\leftrightarrow\forall x^\sigma\,T(Fx)$.
* The original H axioms and the beta, eta, substitution, renaming and
  logical-constant compatibility equations for all parameterized templates.
* The literal equality of the two abstraction values for every **certified
  H-proof** of the equivalence of their bodies. The proof certificate selects
  precisely an instance of C's Logical Equivalence; equivalence under $T_H$
  or under any optional hypothesis is not an admissible substitute.
* The truth translations of C5, $\Box I^*_e$, and each boxed NoReal instance.

Finite syntax, conversion certificates and H-proof certificates can be
enumerated. Include finite enumeration-stage certificates when checking an
axiom occurrence, so ordinary finite proofs are effectively recognizable.
Thus $T_H$ is computably enumerable. It contains neither $A_0$'s elementary
diagram nor its full true arithmetic theory.

Expanding $A_0$ by its actual term operations and truth predicate gives a model
of $T_H$. Conversely the displayed truth, equality, quantifier and lambda
clauses make every first-order model of $T_H$ an eligible classical C5 Henkin
component with the required boxed infinity and NoReal statements. This uses
all parameterized lambda operations, not just an application reduct. No
current-extensionality quotient is taken. These two semantic facts suffice;
no equivalence between two different proof calculi is required.

## 2. Selecting an arithmetically disagreeing component

For an ordinary arithmetic sentence $\varphi$, let $\varphi^e$ be its canonical
individual-counting translation. Variables range over $\mathbb N_e$ at
$\nu=(et)t$; identity, zero and successor are the native terms; eliminate
function symbols for addition and multiplication through the native
$\operatorname{Sum}$ and $\operatorname{Prod}$ graphs.

Under $I^*_e$ this is a recursive interpretation of PA. Zero is not a successor
and successor is injective by the guard. The impredicative least-inductive
property of canonical numbers gives every first-order induction instance by
applying it to the lambda predicate of the translated formula, with parameters.
The native recursion definitions give total unique Sum and Prod graphs, so
function-term elimination and first-order logical proof translation are valid.
These are the current relational arithmetic arguments; they require no choice
of an operation from its graph. Consequently $T_H$ proves
$T(\operatorname{val}(\varphi^e))$ for every PA theorem $\varphi$, and translation
commutes with Boolean operations and negation.

Let $U$ be the arithmetic theory with axioms

$$\{\varphi:T_H\vdash T(\operatorname{val}(\varphi^e))\}.$$

Dovetail over arithmetic sentences and finite $T_H$ proofs to enumerate it.
A finite arithmetic proof from these axioms translates back into $T_H$, using
the interpretation and truth clauses. Hence

$$U\vdash\varphi\quad\Longleftrightarrow\quad
T_H\vdash T(\operatorname{val}(\varphi^e)).$$

The standard arithmetic of $A_0$ makes every $U$ axiom true in $\mathbb N$.
In particular $U$ is a consistent computably enumerable extension of PA.
Rosser's first incompleteness theorem gives an ordinary sentence $G$ neither
proved nor refuted by $U$. Its usual proof-comparison fixed point is
standard-true: there is no actual proof of $G$, so the antecedent of each
standard comparison is false. Finite axiom-enumeration certificates permit
this use of Rosser for the computably enumerable theory. No internal
consistency statement, omega-consistency assumption or second-incompleteness
argument is needed.

Thus $T_H+\neg T(\operatorname{val}(G^e))$ is consistent. First-order
completeness and countable downward Löwenheim–Skolem yield a countable ground
model $A$ of it. Construct its domains and operations before any auxiliary
Cohen evaluation and give them the trivial symmetry action.

The boxed hypotheses give the whole-object equations

$$ (I^*_e)_A=\top_A,\qquad
(\exists\mathfrak R\operatorname{Real}_\tau(\mathfrak R))_A=\bot_A.$$

C5 makes equality propositions crisp: identity gives necessary identity, and
inequality gives necessary inequality. If $g=\operatorname{val}_A(G^e)$,
current falsity gives $g\ne\top_A$. We do not need or infer $g=\bot_A$.
The NoReal bottom equations come from their separate boxed hypotheses.

## 3. The hybrid and its C interpretation

Use the same Boolean hierarchy and symmetry group as the original construction:

$$B=\operatorname{RO}((2^\omega)^\omega),\qquad
B_{\rm fs}=\bigcup_{J\subseteq\omega\text{ finite}}B_J,$$

with finite products of finite-prefix permutations, and trivial action on $A$.
The hybrid has

$$D_e^r=\omega\times D_e^A,\qquad D_t^r=B_{\rm fs}\times B_A.$$

At a relational type, an entity is a finitely supported current Boolean
profile paired with an admitted $A$-component. Application, equality,
quantifiers and lambda use exactly
[the hybrid clauses in §7](symmetric-cohen-arithmetic-growth.md).
Projection $\pi_\tau$ to $A$ is onto and commutes with all term operations.
The component's admitted quantifiers and lambda operations are kept intact;
its nonstandard domains are not replaced by external full function spaces.

For propositions, native necessity has the whole value

$$\Box(b,a)=
\bigl(\delta_{b=1\land a=\top_A},\ \delta_{a=\top_A}\bigr),$$

where the second delta is $\top_A$ or $\bot_A$. In particular its current
Boolean coordinate tests whether both coordinates of the original proposition
are top. The original closure, support and C proofs require ground component
data and the component's C operations. They do not require that the component
be elementary over $A_0$, so they apply to this $A$.

## 4. NoReal survives the component change

For a field supported on finitely many Cohen coordinates $J$, the original
moving-object lemma supplies a generic-truth-filter-fixing prefix-transposition
involution whenever an element has essential support outside $J$. At the
classical evaluation this is an actual order automorphism of order two. An
order automorphism of finite order must fix every element: otherwise repeated
application to a strict inequality contradicts its finite order. Thus all
field elements descend to the intermediate universe using only the coordinates
$J$. Every subproperty in that universe is represented by an admitted
$J$-supported predicate. A fresh Cohen coordinate supplies an admitted bounded
rational cut whose supremum cannot belong to that intermediate field. This
refutes completeness.

Sections 3–4 and 7.2 of the original construction prove the required
moving-object and finite-coordinate descent statements for the whole typed
hierarchy. Their component assumptions are only groundness, trivial symmetry
action and the unchanged admitted operations. The new $A$ satisfies these
assumptions. Hence the current Boolean value of existential Real is zero at
every host. Its component is bottom by §2, so the **entire** proposition is

$$(\exists\mathfrak R\operatorname{Real}_\tau(\mathfrak R))_r
=(0,\bot_A).$$

Therefore necessarily no real structure exists at any admitted type. Every
SOAN and AN possible-real antecedent is false.
This is analytic vacuity at all hosts, not a nonvacuous real-field witness.

## 5. Current arithmetic, including its recursion graphs

Let $K=\{\bar n^r:n\in\mathbb N\}$ be the set of whole standard root numeral
objects. Its support-empty characteristic predicate is admitted with the
appropriate arbitrary component. Boolean finite induction through each
admitted inductive predicate, and this characteristic test in the opposite
direction, give the exact identity

$$\mathbb N_r=(\chi_K,\mathbb N_A).$$

Crisp finite individual subsets distinguish all standard numerals. Successor
is injective on them and omits zero. Together with the component equation,
this gives $I^*_e=(1,\top_A)$ and hence current $\Box I^*_e$.

Standard number objects alone do not prove standard arithmetic truth; verify
Sum and Prod. Fix standard $m$. The support-empty current graph

$$\{(\bar i^r,\overline{m+i}^r):i\in\mathbb N\}$$

is admitted, paired with any $A$-component. It satisfies the initial and
successor-closure premises of native Sum with Boolean value 1, and makes each
incorrect standard output have value 0. Conversely take any admitted,
possibly noncrisp recursion test $R$. Let $b$ be the conjunction of the
Boolean values of its initial and closure premises. Then
$b\le R(\bar0,\bar m)$; finite induction gives
$b\le R(\bar i,\overline{m+i})$ for every standard $i$. Thus every correct
Sum instance has defining implication value 1 for every test; their meet is
1. Incorrect outputs have value 0 by the displayed characteristic graph.

The same argument for
$\{(\bar i^r,\overline{mi}^r):i\in\mathbb N\}$, using the verified Sum
graph, proves standard Prod. The recursion quantifiers are guarded by the
crisp $\mathbb N$ predicate. These definitions are nonmodal in their current
coordinate, so arbitrary component coordinates do not change the calculation.
The identical argument works in the source base $A_0$ and supplies the standard
arithmetic graphs used in §2's soundness argument.

Induction on the native first-order arithmetic grammar now yields current
value 1 exactly for the standard-true sentences, and 0 for the standard-false
ones. Projection to $A$ preserves the component value of every formula.
In particular

$$(G^e)_r=(1,g),\qquad g\ne\top_A.$$

## 6. Failure of the exact guarded necessity schema

Since $I^*_e$ is the entire top object, $I_e=\Diamond I^*_e$ is also the entire
top object. The native instance is

$$\Box(I_e\to G^e)\ \lor\ \Box(I_e\to\neg G^e).$$

The first alternative has current value 0 because the component $g$ differs
from $\top_A$. The second has current value 0 because the first coordinate of
$\neg G^e$ is 0. Both alternatives therefore fail while $\Box I^*_e$ holds.
This is the exact Necessity of Arithmetic failure. It uses equality-defined
necessity on whole objects; it does not infer modal disagreement from mere
nonstandardness or append an unverified accessible point.

## 7. A classical ground model

Apply the Boolean-Henkin reduction of
[the original proof, §5](symmetric-cohen-arithmetic-growth.md) to this hybrid.
Choose a countable elementary substructure of the semantic algebra retaining
the value map and all syntactic lambda operations. Meet the countably many
dense witness requirements for its retained predicates. The resulting ground
ultrafilter defines classical current truth with literal identity and the full
Henkin quantifier truth lemma at every retained type. Whole propositions are
not quotiented by present agreement.

The C axioms, boxed NoReal, analytic schemas and $\Box I^*_e$ have Boolean
value 1, whereas the displayed necessity instance has value 0. These endpoint
values survive both restriction and the witness-filter evaluation. The final
model is an actual countable classical Henkin model in ZFC, without assuming
a countable transitive model of ZFC or an actual generic over the universe.

## Sources and attribution

The component-selection extension is GPT-6 Astra, prompted by Daniel Kodsi,
*Symmetric Cohen hybrid with first-order arithmetic contingency*, 30 October
2026, §§1–8 (unpaginated). Its finite-support hierarchy, NoReal theorem and
hybrid reduction are the same author's *Symmetric Cohen model: arithmetic
growth*, 29 October 2026, §§2–5 and 7.1–7.2, linked above.

The prior arithmetic-disagreement method is credited to Cian Dorr's
`coalesced-two-extensional-arithmetics-root`, 19 October 2026, with verification
by Claude Opus 5.5 (Anthropic), prompted by Cian Dorr, and to that model's
`coalesced-pinned-substitutions-nonstandard-root` development by Claude Opus 5.5,
prompted by Cian Dorr, 29 October 2026. The present extension preserves the
additional all-host NoReal requirements while selecting its disagreeing
component. It does not replace the proof of the original arithmetic-growth
model or pool that model's separately chosen component constraints.
