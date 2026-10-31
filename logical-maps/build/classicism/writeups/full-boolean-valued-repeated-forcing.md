# Full Boolean-valued models after repeated forcing

Daniel Kodsi, with ChatGPT assistance. Arguments dated 29 October 2026;
recorded here on 30 October 2026. The Boolean hierarchy, its forcing
interpretation and the earlier real-field obstruction are credited in
Section 7. No independent human check or Lean proof is recorded.

## 1. Two models and their scope

Relative to the consistency of ZFC, the following joint packages have
models of C:

| Forcing used twice | Common positive package | Additional verdicts |
| --- | --- | --- |
| Cohen forcing on $\omega$ | C5, necessary BF, necessary Relational Choice, Necessity of Second-Order Analysis | Analytic Necessitism fails |
| Countable partial binary functions on $\omega_1$ | The same common package | Analytic Necessitism holds; Second-Order Analytic Necessitism fails |

All positive analytical schemata have their full native carrier scope.
The failures occur at actual schema instances: AN at carrier $et$ in
the first model, and SOAN at carrier $et$ and arity one in the second.
Necessary BF is proved below but is a derived consequence of the C5
seed. The model records use only the existing unboxed AN and SOAN nodes.

In each case first force over a countable model $N$ of ZFC, obtaining
$M=N[G]$. Then construct a Boolean-valued hierarchy **inside $M$** using
a second application of the same forcing $Q$. Its Boolean algebra is

\[
A=\operatorname{RO}^{M}(Q^M),\qquad B=\mathbf2\times A.
\tag{1}
\]

The completion is formed anew in $M$. A completion computed in $N$
need not remain complete after the first forcing.

For the second example take $N\models\mathrm{ZFC}+\mathrm{CH}$.
The usual relative consistency of CH and first-order completeness
provide a countable such model from $\operatorname{Con}(\mathrm{ZFC})$.
The first example needs no CH assumption. Neither ground is required
to be transitive or externally well founded.

For an arbitrary countable model, choose a filter meeting every dense
set that the model regards as a dense subset of its forcing. Construct
the extension from its internal names modulo generic forcing equality,
using its internal forcing relation for membership. The forcing theorem
for each fixed standard finite formula gives the truth lemma and ZFC
in the extension. This uses no external recursion through ill-founded
ordinals. Every forcing calculation below is a fixed internal ZFC
theorem, interpreted in the relevant ground.

## 2. Why the second forcing preserves parameter-free theory

Suppose $Q$ is parameter-free definable and $N$ verifies these three
conditions:

1. $Q$ is weakly homogeneous.
2. $Q$ forces that the recomputed $Q$ has exactly its old set and order.
3. $Q\times Q$ is isomorphic to $Q$.

For every fixed standard parameter-free set-theoretic sentence $\theta$,

\[
M\models\theta
\quad\Longleftrightarrow\quad
M\models 1_Q\Vdash_Q\theta.
\tag{2}
\]

Here is the full argument. If conditions $p,q$ forced opposite signs of
$\theta$, weak homogeneity would give an automorphism taking $p$ to a
condition compatible with $q$. It fixes the sentence, producing a
contradiction. Since deciding conditions are dense, the top condition
decides one sign. Write $\varepsilon\theta$ for that sign, either
$\theta$ or $\neg\theta$.

The isomorphism in condition 3 shows
$1_{Q\times Q}\Vdash\varepsilon\theta$. The product is forcing
equivalent to the two-step iteration $Q*\check Q$. Condition 2 identifies
its second factor with the forcing defined in the intermediate model.
The iteration theorem therefore gives

\[
N\models 1_Q\Vdash
       (1_Q\Vdash\varepsilon\theta).
\]

The first generic extension satisfies both $\varepsilon\theta$ and
the assertion that its second forcing forces $\varepsilon\theta$.
This proves (2), including the case where the decided sign is negative.

Equation (2) is an external schema over standard finite formulas. It
does not provide a truth predicate inside $N$ or $M$, and it does not
assert that $M$ is elementary in its next forcing extension with
parameters from $M$. Those stronger statements are not used.

### The two forcing checks

For Cohen forcing, $Q=\operatorname{Fn}(\omega,2,{<}\omega)$.
Given $p,q$, flip the finitely many bits on their overlap at which they
disagree. This automorphism makes the image of $p$ compatible with $q$.
Forcing adds no finite sequences of ground ordinals, so the finite
binary conditions and their order are unchanged after a first Cohen
extension. Splitting $\omega$ into two infinite sets identifies the
product of two copies of $Q$ with $Q$. Thus all three conditions hold.

For the other example,

\[
Q=\operatorname{Fn}(\omega_1,2,{<}\omega_1),
\]

where conditions are **countable** partial functions. The union of a
descending countable sequence of conditions is a condition. To decide
a name for an ordinal sequence of length $\omega$, recursively decide
one coordinate at a time and then take such a lower bound. This gives
dense conditions deciding the whole sequence, so the forcing adds no
countable sequences of ordinals. It adds no reals and preserves
$\omega_1$.

Every countable condition in the extension can be coded by a countable
sequence of ordinals. That sequence is old; $\omega_1$ is unchanged.
Consequently the recomputed $Q$ is exactly the original forcing,
including its order. This verifies condition 2, rather than merely
asserting equivalence of two potentially different forcings.

Bit flips on the countable overlap of any two conditions make them
compatible, proving weak homogeneity. A ground bijection
$\omega_1\times\{0,1\}\to\omega_1$ merges the two countable domains
and gives $Q\times Q\cong Q$. All three conditions again hold. These
proofs, including the countable-sequence argument, are interpreted
internally when the ground is nonstandard.

## 3. The Boolean hierarchy and its common positive package

Inside $M$, set $D_e=\omega^M$, $D_t=B$, and

\[
D_{\sigma\to\tau}=(D_\tau^{D_\sigma})^M
\qquad(\tau\ne e).
\]

Use internal function application, Boolean connectives, and internal
meets and joins for quantification. Externalize each standard finite
type and evaluate a proposition by its first coordinate. First-coordinate
projection preserves these internal meets and joins, so satisfaction
has the ordinary classical quantifier clauses on the externalized
domains. Fullness here always means **internal** fullness.

The Boolean soundness induction validates each fixed finite H proof.
H-equivalent bodies have equal values at every assignment; internal
function extensionality therefore identifies their abstractions. This
validates C's theoremhood-restricted Logical Equivalence. No optional
root premise is used in that rule or necessitation.

Singleton characteristic predicates make defined identity crisp at
every type. The defined necessity operator is the global top test

\[
\delta(b)=
\begin{cases}1_B&b=1_B,\\0_B&b\ne1_B.\end{cases}
\]

Thus necessary distinctness is itself necessary, giving C5. Moreover
$\forall x\,\Box F x$ and $\Box\forall x\,F x$ both have value top
exactly when every $F(x)$ has value top, and otherwise bottom. BF and
its box hold at every admitted quantified type.

For Relational Choice, well-order the output domain internally and,
for any admitted binary relation $U$, define

\[
S(x,y)=U(x,y)\wedge
       \neg\bigvee_{z<y}U(x,z).
\tag{3}
\]

Internal Replacement and fullness admit this graph. Its row values
are pairwise disjoint, lie below the original row values, and have
the same join as those values. Crisp identity therefore makes the
value of its functional-totality assertion equal to the value of
the original row's totality. Inclusion has value top. The existential
choice conclusion has value at least the seriality antecedent, so
every instance of Relational Choice has value top. Its universal
closure and box do as well. The construction uses a relational graph
even for individual outputs, with no forbidden function type ending
in $e$.

### Extensional forcing transfer

We use transfer only for the native analytical fragment: relations
are applied to carrier elements, and identity compares carrier
labels. It does not replace intensional identity between relation
entities by equality of their forcing extensions.

For any internal set $T$, a name for a subset of $\check T$ can be
normalized to the coefficient function

\[
t\longmapsto\|\check t\in\dot Y\|_A.
\]

Conversely every internal map $T\to A$ supplies such a name. For
$T=D_\sigma^k$, the full relation domain supplies all these
coefficient maps, with independently chosen first coordinates.
Quantification over $\check T$ reduces to meets and joins over the
ground labels; Boolean substitution handles mixed element names.
Induction on a fixed finite extensional formula now identifies its
first coordinate with ground truth and its $A$ coordinate with its
forcing value. The same calculation works below any positive Boolean
support on which its field hypotheses hold.

### Necessity of Second-Order Analysis

Fix a native second-order analytical sentence $\varphi$. Translate it
to the parameter-free set-theoretic sentence $\theta_\varphi$ asserting
its truth in the canonical real field with its natural-number predicate.
An arity-$k$ relation quantifier becomes a quantifier over subsets of
$\mathbb R^k$. This is a finite first-order formula of set theory,
with powersets as sets; it uses no truth predicate.

By (2), $M$ and its second forcing give $\theta_\varphi$ the same
sign. Suppose the sign is positive. At any admitted carrier $\sigma$,
complete ordered fields with their least inductive natural-number
predicate are internally categorical. Thus every first-coordinate
real structure satisfies $\varphi$. In the forcing coordinate the
same categoricity and extensional transfer apply below the support
of each candidate real structure. It follows that

\[
\left\|\forall\mathfrak R\,
  (\operatorname{Real}_\sigma(\mathfrak R)
      \to\varphi(\mathfrak R))\right\|_B=1_B.
\tag{4}
\]

Its box is top. If the sign is negative, the same proof gives the
boxed assertion with $\neg\varphi$. This is exactly the native
Necessity of Second-Order Analysis schema, for every carrier and
every standard finite analytical sentence. Types without real
structures are handled by the implication in (4); no capacity
assumption is suppressed. This argument asserts no No Pure
Contingency principle for the full intensional language.

## 4. Rigidity, complete fields and represented powers

Three calculations will distinguish the two models.

**Endpoint rigidity.** A relation $Y:T\to B$ is rigid precisely when
every value is $0_B$ or $1_B$. Persistence requires
$Y(u)\le\delta(Y(u))$, forcing those endpoint values. Conversely,
write an endpoint-valued relation as $\chi_E$. For any admitted test
$Z$, both

\[
\forall u\,(Y(u)\to\Box Z(u))
\quad\text{and}\quad Y\le Z
\]

have the same endpoint value: top exactly when $Z(u)=1_B$ for all
$u\in E$. The implication in weak inextensibility is therefore
top for every test; its universal closure and leading box are top.
Persistence is immediate. This verifies full rigidity, not merely
fixed membership. Rigidity itself has endpoint value because its
defining conjuncts are boxed.

**Preserving a complete field.** If the forcing adds no reals, every
new bounded nonempty subset of the old real field has an old supremum.
Its rational lower cut is coded by a subset of $\omega$, hence is
old; the corresponding old real is its supremum. The least inductive
natural-number predicate also remains the same, since forcing
preserves $\omega$. The transfer just proved includes all the new
subproperties quantified over in the completeness and induction
clauses. Thus an endpoint copy of the old field is necessarily real.

Conversely, a genuinely new real supplies a new rational cut with no
old supremum. Any internally complete ground field is ground-isomorphic
to the ground reals, so its check fails completeness wherever that
new cut appears. An AN witness cannot evade this by varying its
operations: endpoint rigidity makes all five field relations ground
relations. Further, each candidate's
$\operatorname{RigidStr}\land\Box\operatorname{Real}$ has endpoint
value. A join of bottom candidate values remains bottom.

**Represented-power obstruction.** Let $X$ be a rigid carrier with
ground support $S$. All rigid unary relations supported on $X$ are
the endpoint characteristic functions $\chi_T$, for ground subsets
$T\subseteq S$. The full hierarchy admits the maximal endpoint
family containing all of them. For an arbitrary subset-name
coefficient map $f:S\to A$, the forcing coordinate of its existential
agreement with that family is

\[
\bigvee_{T\in\mathcal P(S)^M}
 \left(\bigwedge_{s\in T}f(s)
       \wedge\bigwedge_{s\in S\setminus T}\neg f(s)\right)
=\bigvee_{T\in\mathcal P(S)^M}
       \|\dot Y=\check T\|_A.
\tag{5}
\]

Any candidate represented family that satisfies its rigidity and
qualification clauses can select only a subcollection of these
ground subsets. Its agreement value cannot exceed (5). If (5) is
zero for one subset name, the boxed universal representation clause
fails for every such family. Families failing rigidity or qualification
already contribute bottom. The qualification clauses have endpoint
values for rigid carriers and families, as do the rigidity and boxed
representation clauses. Consequently Boolean mixing of different
families cannot repair the failed existential.

The join in (5) is essential: a mixture of old subsets can have no
single globally correct old representative while still being locally
represented with total Boolean value top. We use names unequal to
**every** old subset with equality value zero.

## 5. The second Cohen forcing: failure of AN

The second Cohen forcing adds a subset of $\omega$ unequal to every
old subset: for any old binary sequence and any condition, assign
the opposite bit at a fresh coordinate. The corresponding disagreement
sets are dense, so the new-real obstruction applies over $M$.

The $et$ domain contains all endpoint sequences indexed by $\omega^M$
and hence a ground copy of the real field. Give its field relations
endpoint values. Its first-coordinate realhood is true, regardless
of whether it stays complete after forcing. Thus
$\exists\mathfrak R\,\operatorname{Real}_{et}(\mathfrak R)$ has
nonzero Boolean value, and its possibility has value top.

Any prospective rigid necessarily-real tuple must, by Section 4, be
a ground complete ordered field with endpoint relations. The new
rational cut prevents its check from being complete. Every tuple
therefore contributes bottom to the AN consequent. The antecedent
is top and the consequent bottom: the native AN instance at $et$
fails. The map derives SOAN failure from this negative, so it is
not a separate seed.

Together with (4), this gives full Necessity of Second-Order Analysis
while AN fails. It does not claim that an arbitrary first Cohen
forcing preserves all parameter-free truth over every ground; the
first extension in the definition is what makes (2) available.

## 6. The second countably closed forcing: AN without SOAN

Both applications add no reals and preserve $\omega_1$, so CH holds
in $M$ and remains true after its second forcing. The no-new-reals
field argument supplies necessary completeness, but full AN requires
a separate check at every carrier.

For each ground real $r\in2^\omega$, the condition with domain
$\omega$ and values $r$ belongs to $Q$. Distinct such conditions are
incompatible, giving a ground-continuum antichain in $A$. Hence the
ground reals inject into $B$. Constant functions recursively inject
$B$ into every admitted nonindividual type, including purely
propositional types. Every such carrier therefore admits an endpoint
copy of the old complete field, with all its operations and its
natural-number predicate. Internal fullness admits these relations;
Section 4 gives rigidity and necessary realhood.

At $e$ the labels form $\omega^M$. In the ground and in the forcing
universe, no subset of $\omega$ carries a complete ordered field.
Extensional transfer makes every possible $\operatorname{Real}_e$
tuple have value zero, including on any proposed positive Boolean
support. Thus the possible-real antecedent at $e$ is bottom.
This is an internal ZFC impossibility argument, not an inference
from the external countability of the model. All carrier cases are
now covered, so full current AN holds.

Let $\dot H\subseteq\omega_1^M$ be the second generic subset. It is
total because the conditions deciding each coordinate are dense.
For every old $T\subseteq\omega_1$ and condition $p$, choose
$\alpha\notin\operatorname{dom}(p)$ and assign the bit opposite
to $T(\alpha)$. Hence

\[
\|\dot H=\check T\|_A=0
\quad\text{for every old }T\subseteq\omega_1.
\tag{6}
\]

Now consider **any** proposed rigid necessarily-real tuple, at any
carrier. If it fails either conjunct it contributes bottom to SOAN.
Otherwise its endpoint field relations give an internally complete
ground field on a support $S$. Ground categoricity and CH provide
an internal bijection $j:\omega_1\to S$. Transfer $\dot H$ along
$j$, using its normalized coefficients and extending by zero outside
$S$. If this subset name equalled any old subset of $S$ on a positive
condition, its inverse image would contradict (6). Thus every term
in (5) is zero for this name.

Section 4 defeats every unary represented family for this particular
field; the argument works for every prospective field. Consequently
the full SOAN existential consequent has value bottom. At $et$ the
explicit rigid necessary field above makes the possible-real
antecedent top. This refutes the native unary $et$ instance of SOAN.

The resulting joint package preserves every parameter-free
second-order analytical truth, preserves the real-field objects
required by AN, and still fails the native demand for represented
relation powers. No finite-type necessitism extension is asserted.

## 7. Attribution and boundaries

Andrew Bacon's *Could the truths of mathematics have been different?*,
draft of 9 October 2025, online Appendix B.2, pp. 7–9 (PDF pp. 41–43),
supplies the Boolean-valued construction and its basic soundness
lemmas. The internally full presentation, exact extensional transfer,
endpoint rigidity, and necessary choice arguments were developed in
the 25 October 2026 Boolean-model work of OpenAI Codex, prompted by
Daniel Kodsi. Their detailed one-stage application is also given in
the map's [countably closed subset model](full-boolean-valued-countably-closed-subset.html).

The rigid-ground-field obstruction from a new rational cut is prior
work recorded in
[full-boolean-valued-atom-and-atomless](full-boolean-valued-atom-and-atomless.html):
Claude Fable 5.1 (Anthropic), prompted by Zachary Goodsell,
23 October 2026, revised 24 October at Cian Dorr's direction.
The full-carrier no-new-reals argument and represented-power
calculation were developed with ChatGPT assistance for Daniel Kodsi
on 29 October 2026. They are reproduced above, including their
quantifier and carrier restrictions.

The additional step here is to prepare the ground by a first
application of the same forcing and prove (2) from homogeneity,
preservation of the forcing, and its product isomorphism. That step
supplies full analytical truth stability in the two stated joint
profiles. This is a proof of those relative examples, without a
claim of historical novelty for homogeneous forcing or absorption.
