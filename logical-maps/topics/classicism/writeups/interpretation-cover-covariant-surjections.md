# Interpretation cover: covariant surjections

Daniel Kodsi, with ChatGPT assistance, 30 October 2026. The construction
combines Cian Dorr's interpretation roots and symmetric-surjection argument
for Inextensible Comprehension with the typed-name interpretation covers
developed by OpenAI Codex, prompted by Daniel Kodsi. The prior arguments are
identified in Section 7. No independent human check or Lean proof is recorded.

## 1. Result and assumptions

There is one relative model of C with the joint root properties

\[
\text{Maximalism for }\Sigma,
\qquad\text{Atomlessness},
\qquad\text{Inextensible Comprehension},
\qquad\text{BF}.
\]

Inextensible Comprehension ranges over every relational type, including
$t$; BF ranges over every admitted quantified type, including $e$.
These are assertions at the root. In particular, the box in
$\operatorname{Inextensible}(Y)=\Box\operatorname{WeaklyInextensible}(Y)$
is proved, but no box is placed in front of the outer comprehension schema.
Pure Maximalism follows from the signature result.

Work in ZFC and use the following existence input from the interpretation-root
construction: a set-sized family of faithful pointed C action models contains
a witness for every closed pure C-consistent sentence. Each component retains
all of its original objects, arrows, domains, application and quantifier
operations. This proof does not establish that representation/completeness
input anew. Optional root properties are not added to the reference theory
$C$ or $C(\Sigma)$ used in Maximalism.

Fix a prescribed set-sized signature $\Sigma$ of free constants of admitted
types, under the conventions in the map's Background. It contains a
relational constant. Choose infinite auxiliary sets $C_\sigma$, one at each
admitted type, large enough to assign distinct names to the signature's
constants. Relational names are indices; they are not required to enumerate
the relational entities constructed below.

## 2. Domains and transports

Add a root $o$ to the disjoint union of the old components. Its individual
domain is $C_e$. Its loops are all tuples

\[
h=(h_\sigma)_\sigma,
\qquad h_\sigma:C_\sigma\twoheadrightarrow C_\sigma.
\]

The designated root symmetry group consists of all typewise permutations.
For every old object $V$, include every typed interpretation
$I_\sigma:C_\sigma\to D_\sigma(V)$ as an arrow $o\to V$.
Composition is $Ih$ and $kI$, using the old transport for $kI$.
All interpretations are included, so a non-surjective old transport still
gives an allowed composite. There are no arrows back to the root.

Proceed recursively through the finite types. At a relational type
$\tau=\sigma_1\cdots\sigma_n t$, an entity $X$ assigns to every arrow
$a:o\to V$ a row

\[
X_a\subseteq D_{\sigma_1}(V)\times\cdots\times D_{\sigma_n}(V).
\]

For $n=0$ a row is a truth value. Admit precisely the profiles satisfying:

1. **Finite pinning.** A finite set $S$ of typed names controls the rows:
   arrows to the same target that agree on $S$ have identical rows.
2. **Permutation covariance.** For each root permutation $\gamma$ and
   root loop $h$,
   \[
   X_{\gamma h}=\rho_\gamma[X_h],
   \]
   where $\rho_\gamma$ acts componentwise on the argument tuple.
3. **Old landing.** At each interpretation $I:o\to V$, the entire section
   $k\mapsto X_{kI}$ is an admitted old entity of type $\tau$ at $V$.

The argument types have lower complexity than $\tau$, so their domains and
transports have already been defined. The recursion uses full target
argument domains, even when an entrance misses some target entities.
Define transport by precomposition:

\[
(\rho_hX)_a=X_{ah}.
\]

If $S$ pins $X$, then $hS$ pins $\rho_hX$. Covariance follows from
$X_{\gamma ah}=\rho_\gamma[X_{ah}]$, and its old section at $I$ is
the already admitted section of $X$ at $Ih$. Thus transport lands in the
specified domains and is functorial. A root permutation acts bijectively.

We will repeatedly use the stronger consequence of pinning:

\[
a|S=b|S\quad\Longrightarrow\quad\rho_aX=\rho_bX.
\tag{1}
\]

Indeed, every further pair of composites $ka,kb$ still agrees on $S$,
so the transported entities agree on every future row and tuple.
Individual parameters have singleton-name pins.

### Closure under C

Literal identity at the root has admitted separators. For an entity $q$,
take the profile whose row at $h$ is $\{\rho_hq\}$ and whose old section
at $I$ is the old haecceity of $\rho_Iq$. Equation (1), covariance and
old term closure prove admission. Its identity row distinguishes $q$
from every different entity. A constant singleton row is not being
assumed covariant.

For a term with finitely many parameters, combine their pins. Arrows
agreeing on that union transport the complete parameter environment
identically. Evaluating the body on every tuple in the target proves
finite pinning for abstractions. Bound variables range over the whole
target domain; no common pin for that domain is required. At an old
interpretation the full section is its old term denotation, by induction
on terms, and hence satisfies old landing.

Every root permutation is an automorphism of the typed application
structure: covariance preserves application and its actions on all
domains are bijective. Thus quantified truth is preserved by reindexing.
The same holds for modal formulas, since the map $a\mapsto a\gamma$
bijectively reindexes all continuations, including old interpretations.
This proves covariance of all term denotations. Application, Boolean
operations, quantifiers and abstraction therefore stay in the admitted
domains. Beta and eta hold on profiles. Necessary coextension identifies
every row at every continuation, and hence identifies the entities.
H-theorem-equivalent bodies agree at all target assignments, validating
C's theoremhood-restricted Logical Equivalence. No optional premise
enters that rule or necessitation.

For a relational name $c$, its named lift $\widehat c$ has empty rows at
root loops and whole old section $I(c)$ at each old interpretation.
It is pinned by $\{c\}$ and admitted. For individuals use $c$ itself.
The identities

\[
\rho_I\widehat c=I(c),
\qquad\rho_h\widehat c=\widehat{h(c)}
\tag{2}
\]

concern the whole entities, not just their extensions at the targets.

## 3. Inextensible coextensions

Fix any $X$ of relational type and a finite typed pin $S$ for it. Let
$\delta_S$ be true at a root loop exactly when that loop is injective
on $S$ within each type, and false at every old interpretation.
This proposition is pinned by $S$, covariant under postcomposition by
permutations, and has whole Bottom sections in the old components.
It is therefore admitted, including when $S$ is empty.
Put

\[
Y=\lambda\bar x\,.\,\delta_S\land X[\bar x].
\]

It coextends $X$ at the root identity. The point of covariance is that
preimages can be chosen inside this particular extension.

**Tuple-preimage lemma.** If a root loop $f$ fixes $S$, and $r$ is any
root tuple with a finite combined pin $T$, there is a typed permutation
$\tau$ fixing $S$ such that

\[
\rho_f(\rho_\tau r)=r.
\tag{3}
\]

For each $t\in T_\sigma\setminus S_\sigma$, choose an $f_\sigma$-preimage
outside $S_\sigma$. This is possible because $f$ fixes $S$ and is onto;
different target names have different chosen preimages. Extend the finite
assignments, together with identity on $S$, to permutations. Then
$f\tau$ fixes $T$, and (1) gives (3). If $r\in X_1$, pinning and
covariance additionally give

\[
X_\tau=X_1=\rho_\tau[X_1],
\]

so $\rho_\tau r\in X_1$.

Now suppose an arbitrary admitted $Z$ is necessary of every current
$Y$-tuple. Consider any tuple $z\in Y_h$ at a root loop $h$.
Necessarily $h$ is injective on $S$. Extend $h|S$ to a typed permutation
$\pi$ and put $f=\pi^{-1}h$, which fixes $S$.
Pinning and covariance give

\[
X_h=X_\pi=\rho_\pi[X_1].
\]

Write $z=\rho_\pi r$ with $r\in X_1$. Lemma (3) supplies
$r'\in X_1=Y_1$ with $\rho_fr'=r$, hence $\rho_hr'=z$.
The assumed necessity of $Z[r']$ gives $Z_h[z]$.
At old entrances and at loops collapsing $S$, the row of $Y$ is empty.
This proves $Y\le Z$ for every admitted test $Z$, and therefore weak
inextensibility of $Y$.

The leading box requires a further check. A collapsing loop sends $Y$
to whole Bottom: every later root composite still collapses $S$, and
every old row is false. Old entrances also send $Y$ to whole Bottom.
If $h$ is injective on $S$, then

\[
\rho_h\delta_S=\delta_{hS},
\qquad
\rho_hY=\delta_{hS}\land\rho_hX,
\]

and $hS$ pins $\rho_hX$. The same full-domain argument proves weak
inextensibility of this transported relation. Bottom is weakly
inextensible in every component. Consequently $Y$ is necessarily
weakly inextensible, as required. The proof treats arbitrary finite
argument tuples, including the empty tuple.

## 4. Atomlessness

Let $p\ne\bot$ have finite pin $S$. Some row of $p$ is true.
If it is a root-loop row $p_h$, choose two fresh individual names
$u,v$ outside $S$. Extend finite prescriptions to surjections $h_=$
and $h_\ne$ that agree with $h$ on $S$, with respectively equal and
unequal images of $u,v$. The admitted scalar whose root-loop row at
$g$ says $g_e(u)=g_e(v)$, and whose old sections are Bottom, splits
$p$: both its intersection with $p$ and its complement's intersection
with $p$ have true rows.

If the true row is at an old interpretation $I$, choose a fresh
propositional name $c$ outside $S$. Change only $I(c)$, once to old
Top and once to old Bottom. Both interpretations are allowed, and
pinning keeps $p$ true. Equation (2) shows that $\widehat c$ splits
$p$. This second case includes propositions with no true root-loop
row. Thus every nonbottom proposition has a proper nonbottom part,
even if an old component has atoms.

## 5. Maximalism for the fixed signature

Every pure C-consistent sentence retains a witness in an unchanged old
component and is therefore possible at the root. For $\Sigma$, interpret
its individual constants by designated names and its relational
constants by the corresponding named lifts.

Take any closed $C(\Sigma)$-consistent sentence. Replace its finitely
many constants by variables and existentially close. This pure sentence
is C-consistent: otherwise instantiating the refutation at the constants
would refute the original sentence. Choose its old witness and assign
the witnessed values to the finitely many names. Extend the assignment
to an arbitrary typed interpretation. Equation (2) then recovers the
entire original sentence at the old witness. This proves the signature
possibility form of Maximalism, equivalent in C to the recorded
Distinctness form. Constants may denote equal values after an entrance;
no unique-name assumption is made.

## 6. BF

Use the dual form
$\Diamond\exists x^\sigma F x\to\exists x^\sigma\Diamond F x$.
If $b$ is a witness at a root loop $h$, apply the tuple-preimage lemma
with $S$ empty to its finite pin. It supplies $a$ with $\rho_ha=b$,
so the same loop witnesses $F a$.

If the witness $b$ is at an old interpretation $I$, choose a fresh
$\sigma$-name $c$ outside $F$'s pin. Change its interpretation to $b$,
leaving the pinned names unchanged. The new entrance $I'$ has exactly
the same full predicate row as $I$. Its current named lift reaches
$b$, by (2); for $\sigma=e$ use the name itself. Hence that current
entity possibly satisfies $F$. There is no assumption that an arbitrary
fixed old entrance is onto, or that an old component satisfies BF.

## 7. Sources and scope

The interpretation-root and whole-landing methods come from Cian Dorr's
19 October 2026 construction, with the landing correction supplied by
Claude Opus 5.5 (Anthropic), prompted by Cian Dorr; see the map's
[interpretation-root write-up](coalesced-pinned-interpretations-root.html).
The auxiliary typed names, named lifts and arbitrary-component version
of the cover occur in *Observer covers and Boolean completeness*,
Sections 2–3 and 8, by OpenAI Codex, prompted by Daniel Kodsi,
26 October 2026, and the
[named-permutation cover](interpretation-cover-named-permutations.html).

The injectivity-mask and within-extension tuple-preimage proof is the
all-type Inextensible Comprehension argument in
[symmetric-all-surjections](symmetric-all-surjections.html), supplied by
Claude Opus 5.5 (Anthropic), prompted and checked by Cian Dorr,
27 September 2026. Here full typed permutation covariance and all
root surjections preserve that argument while arbitrary old
interpretations preserve the complete family of witnesses. The
contribution is their simultaneous combination in this cover.

The construction supplies no boxed comprehension or BF assertion.
It also supplies no Boolean Completeness, Forcing Possibilism,
Strong Possibility or choice verdict. Its proofs should not be combined
with those of a different cover to assign a stronger joint profile.
