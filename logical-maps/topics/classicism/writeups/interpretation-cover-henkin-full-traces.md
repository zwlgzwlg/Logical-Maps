# Interpretation cover: Henkin and full subset traces

Daniel Kodsi, with ChatGPT assistance, 30 October 2026, using the named
interpretation cover and earlier component constructions credited in
Section 6. No independent human check or Lean proof is recorded.

## 1. Result and construction

A specified enlargement of the
[named-permutation interpretation cover](interpretation-cover-named-permutations.html)
has the joint root properties

\[
\text{Possibility+ for }\Sigma,
\quad\text{BF},
\quad\text{Relational Choice},
\quad\text{Vicinity},
\quad\text{Atomlessness},
\quad\neg\text{Rigid Power}.
\]

BF and Relational Choice range over all their admitted types. The
positive schemata are unboxed. Possibility+ has exactly the native
free-individual-variable and constant-exclusion conditions; its
consequences include pure and signature Maximalism. Rigid Power fails
at bound type $(et)t$, whose power property has type $((et)t)t$.

Work in ZFC with the interpretation-root existence input: a set-sized
family of faithful pointed C action models supplies every closed pure
C-consistent sentence with a witness. Retain these components unchanged
and add two disjoint isolated terminal components $H$ and $K$,
defined below. Their substructure relation is used in their construction
only; it is not an arrow between them.

Choose infinite typed auxiliary name sets large enough to dominate all
old domains and to accommodate the prescribed set-sized free signature.
At the root take all typed name permutations as loops, and all typed
interpretations as arrows to the old objects. There are no arrows back
to the root. The designated root symmetry group is trivial.
Relational entities are precisely profiles with a finite typed-name pin
and an admitted whole section at every old interpretation. Rows use
the full argument domains at their targets, and transport is
precomposition. Constants denote designated names and named lifts.

This is a fresh instance of the cover construction. Its root is not
asserted to be elementary over a previously chosen root, so the
positive verdicts are checked again in Section 5.

## 2. Two terminal components

Let $K$ be the full finite-type hierarchy on $\mathbb N$, with two
truth values and extensional equality. Present its semantics in a
countable many-sorted first-order language containing application,
the logical and quantifier operations, a denotation constructor for
every finite-parameter typed lambda template, and a name for every
individual $n\in\mathbb N$.

Countable closure under these functions and existential witnesses
gives an elementary substructure $H$ containing every individual.
Its whole collection of sorts is countable and $H_e=\mathbb N$.
Elementarity of the quantifier clauses makes its inherited quantifiers
range over the full displayed $H$ domains. All parameterized lambda
denotations and singleton predicates remain admitted.

Relations of $H$ can be regarded as relations on its own recursively
restricted argument domains. This loses no identities: if two $H$
relations differ, elementarity of extensionality supplies a
distinguishing tuple from $H$. Thus both components are terminal
extensional Henkin models of C. Their modal operator is identity;
every admitted relation is rigid, and each component individually
satisfies Rigid Power.

Write $s_n$ for the property of the individual $n$, and
$\operatorname{Sing}$ for the closed relation whose instances are
exactly these singleton properties. Both components admit them.
There are only countably many sets

\[
\{n\in\mathbb N:Ys_n\},\qquad Y\in D_{(et)t}(H).
\tag{1}
\]

Choose $A\subseteq\mathbb N$ outside this collection of traces.
Full $K$ admits the relation $Y_A$ with extension
$\{s_n:n\in A\}$. No $H$ relation has even the same trace on
the singletons. This formulation does not identify an unreified
$K$ representative with its restriction to $H$.

### Admission and C closure at the enlarged root

An empty pin means that a row may depend on its target object but
not on the interpretation into that fixed object. This allows the
component-specific profiles used below. A profile at relational type
$\sigma_1\cdots\sigma_n t$ has rows on the already defined lower
argument domains, so domain formation is a recursion on finite types.

If two arrows to the same target agree on the finite pin of an
entity, then all their continuations still agree there; its complete
transported sections coincide. Combining the pins of finitely many
parameters therefore fixes their whole transported environment.
Evaluating a term over all target tuples proves pinning, and its
entire old section is exactly the old admitted term denotation.
Quantification keeps the full old domain, even at a non-surjective
entrance. This establishes closure under abstraction, application,
quantification and the modal terms.

Literal root identity is separated by an admitted predicate with
the same singleton row at every root loop and Bottom at all old
targets. Beta and eta are whole profile identities. H-theorem
equivalence holds at every target assignment, validating C's
Logical Equivalence without using optional root premises.
The named lifts satisfy $\rho_I\widehat c=I(c)$ as whole old
entities, and individual names transport by $I_e$.

## 3. A rigid bound with incompatible subsets

For each $n$, define a root entity $a_n:et$ with empty rows at every
root loop, section $s_n$ at each $H$ and $K$ entrance, and whole
Bottom sections at every other old component. It is admitted with
an empty pin. Every root loop fixes it as a whole entity, and the
$a_n$ are pairwise distinct because their $H$ and $K$ sections differ.

Put $E=\{a_n:n\in\mathbb N\}$. Define $F:(et)t$ by the following
sections: row $E$ at every root loop, the admitted $\operatorname{Sing}$
at $H$ and $K$, and the haecceity of $\bot_{et}$ throughout every
other component. The latter sections transport naturally as the old
equality terms. Thus $F$ is admitted with an empty pin.

At every arrow $h$ out of the root,

\[
F_h=\rho_h[E].
\tag{2}
\]

The same identity persists after further arrows. It proves full
rigidity of $F$: membership persists, and any future member is
the transport of a member at the starting target. Every test necessary
on the latter members therefore covers the former, proving weak
inextensibility at every target.

Now let $R:(et)t$ be any current rigid relation with $R\le F$, and set

\[
B=\{n:R a_n\}.
\]

Persistence places $s_n$ in its image at every $H$ and $K$ entrance
whenever $n\in B$. To obtain the reverse inclusion, take $n\notin B$
and choose $V$ separately as $H$ or $K$. Admit the test $Z_n^V$ with
row $D_{et}(o)\setminus\{a_n\}$ at every root loop, section
$D_{et}(V)\setminus\{s_n\}$ at $V$, and whole Top at all other
old components. It has an empty pin and lands as an admitted
singleton complement at the terminal object $V$. Isolation of the
two added components makes these assignments compatible with every
continuation.

The test is necessary on every current $R$-member $a_m$: root
loops fix $a_m$, its $V$ image is $s_m\ne s_n$, and elsewhere
the test is Top. Weak inextensibility of $R$ gives $R\le Z_n^V$.
Applying the separately admitted test for each omitted $n$ shows that
every $H$ image and every $K$ image of $R$ has exactly the singleton
trace $B$. No external intersection of all these tests is required.

Consequently no such $R$ can have image $Y_A$ at any $K$ entrance.
If it did, its trace would be $A$, and any $H$ entrance would produce
an admitted $H$ relation with the forbidden trace (1).

## 4. Failure of the actual canonical power

Take the native lambda entity

\[
P_F=\lambda R^{(et)t}\,.\,
  \operatorname{Rigid}(R)\land R\le F.
\]

Term transport sends it at each $K$ entrance to the canonical power
of $\operatorname{Sing}_K$. That power contains $Y_A$: every
relation in terminal $K$ is rigid and $Y_A\le\operatorname{Sing}_K$.

Admit a higher test $Z$ which is Top at every root loop and every
old component except $K$, where it excludes exactly $Y_A$.
Its $K$ section is the complement of $Y_A$'s haecceity, and it
is pinned by the empty set. Every current member of $P_F$
necessarily satisfies $Z$, because Section 3 excludes $Y_A$
as its image at every $K$ entrance. Nevertheless, at a $K$
entrance the new member $Y_A$ belongs to the transported $P_F$
and fails $Z$. Hence

\[
\forall R\,(P_FR\to\Box ZR)
\quad\text{holds, but}\quad P_F\nleq Z.
\]

The canonical power $P_F$ is not weakly inextensible and therefore
not rigid, although $F$ is rigid. This refutes Rigid Power at the
stated bound type. The proof concerns the actual lambda entity,
not a replacement with the same extension.

Within this particular isolated-terminal architecture, the same
argument shows that weak inextensibility of the canonical power
forces agreement of the two admitted singleton-trace families:
intersect a representative with $\operatorname{Sing}$ and repeat
the missing-trace test. This is a necessary condition only, not a
sufficient condition or a general characterization of Rigid Power.

## 5. The positive package on the enlarged domains

**BF.** Root-loop witnesses lift by inverse permutations. For a
witness at an old interpretation $I$, let $S$ pin its predicate.
Choose a typed interpretation having infinite fibres and mapping
onto every target domain, and modify it on $S$ to agree with $I$.
The name sets were chosen large enough to permit this; finite
modification leaves every fibre nonempty. Named lifts make the
resulting entrance onto on every actual relational domain, as well
as on individuals. The full predicate row is unchanged by pinning,
so the target witness has a current preimage at that entrance.
This proves current BF at all admitted types.

**Relational Choice.** Every external current relation table is
admitted: use that table at all root loops and whole Bottom in
all old components. External ZFC choice supplies a selecting
relational graph for every current serial relation. This includes
graphs with individual outputs and does not assert Functional Choice.

**Vicinity.** The proposition true at all root loops and false at
all old entrances is admitted with an empty pin. Each loop has an
inverse returning to identity, so this proposition entails the
possibility of every current truth. It is a true Vicinity witness.

**Atomlessness.** If a nonbottom scalar has a true root-loop row,
vary a fresh individual name by a permutation while preserving its
finite pin. An admitted root-only scalar testing that name's
image splits it. If its truth occurs at an old interpretation,
vary a fresh propositional name between old Top and Bottom and
use the corresponding named lift. Both cases apply to all newly
admitted scalar profiles as well.

**Possibility+ for the prescribed signature.** Replace the finitely
many constants in a $C(\Sigma)$-consistent formula by variables and
existentially close these and its displayed individual variables.
A retained pure witness supplies the required values. The native
antecedent says the root individuals are pairwise distinct and
distinct from the individual constants occurring in the formula.
It therefore makes their name prescriptions compatible with those
for the constants. Assign the witnessed values and extend to a
typed interpretation. Named lifts recover the whole denotations,
making the original formula possible. Target values may coincide.
No free relational-parameter strengthening is used.

## 6. Attribution and limits

The underlying named cover and its positive properties are prior
work: Cian Dorr's interpretation-root machinery and *Observer
covers and Boolean completeness*, Sections 8.2–8.3, by OpenAI Codex,
prompted by Daniel Kodsi, 26 October 2026, followed by the explicit
named expansion and additional verdicts by GPT-6 Astra, prompted
by Daniel Kodsi, 29–30 October 2026. Coalesced-sum arguments already
use component-specific profiles and haecceities of Bottom.
Elementary Henkin closure and singleton-complement tests are also
prior methods.

The added argument uses two individually Rigid-Power-positive
terminal components whose admitted subset traces differ. One root
subrelation must land in both, and this prevents a lift of the
missing trace. The negative belongs to this specified augmented
model; it is not assigned to every possible witness family in the
original named-cover record. The relative existence input remains
explicit, and no boxed positive, Boolean Completeness or Strong
Possibility verdict is inferred.
