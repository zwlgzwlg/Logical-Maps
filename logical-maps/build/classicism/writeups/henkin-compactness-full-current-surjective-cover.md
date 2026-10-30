# Henkin compactness: full-current surjective cover

GPT-6 Astra, prompted by Daniel Kodsi. 30 October 2026.

For every set-sized free fixed signature $\Sigma$, one general Henkin model of
$C(\Sigma)$ satisfies **Maximalism for $\Sigma$, strict Forcing Possibilism,
and current Barcan at every type**. The same model satisfies the exact
signature Possibility+ schema, current Actuality, Truths are ND-necessary,
Transversal Choice and the quantified Axiom of Infinity at $e$.

The connection is joint compatibility of these principles. The construction
combines the [surjective-chain-name interpretation cover](interpretation-cover-surjective-chain-names.md)
with a full-current product, then uses Henkin compactness for larger signatures.
The finite-pin cardinal bound and the whole-target Barcan transfer are the
steps that make the combination work. All modal qualifications are current.
The final compactness model is not asserted to have full external powersets
or continuum-sized domains.

## 1. A countable complete family of whole action presentations

Work in external ZFC. Use the set-sized action-model completeness theorem for
$C$ (Bacon and Dorr, Theorem 3.23). The pure language has countably many finite
expressions. For each consistent pure closed sentence choose a pointed action
model realizing it. We need to reduce the entire semantic presentation, not
merely the domain at its evaluation point.

Encode such a model as a countable many-sorted first-order structure. Include
objects and arrows with source, target, identities and partial composition;
for each admitted type $\sigma$, a sort $E_\sigma$ of tagged local entities
with its location map; transport, application, current truth, and the sections
for logical constants. Include the graph of local denotation for every finite
pure term template with every finite typed parameter context. In particular,
all parameterized lambda abstractions are retained. Partial operations can be
graph relations with their guarded existence and uniqueness clauses.

The following first-order clauses hold, with location guards understood:

$$
\begin{aligned}
T(Q_\sigma(V)F)&\leftrightarrow
  \forall x\in E_\sigma(V)\,T(Fx),\\
T(\Box p)&\leftrightarrow
  \forall h\ (\operatorname{source}(h)=V\to T(\rho_h p)),\\
T(\operatorname{Eq}_\sigma(x,y))&\leftrightarrow x=y.
\end{aligned}
$$

Retain category laws, transport and term naturality, beta/eta and the
term-template composition clauses. Also retain a profile-separation clause for
every fixed relational type $\tau=\sigma_1\cdots\sigma_k t$: if $a\ne b$ at $V$,
some $h:V\to W$ and target tuple $\bar x$ distinguish the truth of
$(\rho_h a)[\bar x]$ and $(\rho_h b)[\bar x]$. Include $k=0$ for propositions.
This clause is first-order for each fixed finite type. It prevents distinct
whole entities from becoming identical when arrows or argument domains shrink.

Take a countable elementary substructure containing the designated object and
one witness in each sort. The usual iterative existential-witness closure
constructs it: at each stage close under the countably many operations and
choose witnesses for all existential formulas with parameters already chosen.
The union is countable and elementary. If a presentation includes designated
symmetry groups, include their action, inverse and composition relations too.

The retained objects and arrows form a category; every retained typed fiber is
nonempty and countable. Represent retained relations by their rows on all
retained future arrows and all retained argument tuples. Profile separation
makes this representation injective. Type recursion identifies application with
slicing and transport with reindexing. The quantifier clause now ranges over
**the entire retained fiber**, and the modal clause over all retained arrows.
Elementarity supplies a retained counterexample whenever a retained universal
clause is false. The term-template clauses prove preservation of interpretation
by structural induction. Thus this is again a $C$ action model, with literal
identity and the original H-theoremhood restriction on Logical Equivalence.
No closure under every externally supported relation is required of its old
Henkin domains.

The distinguished sentence remains true. Performing this reduction separately
for each consistent pure sentence gives a countable complete family with
countably many total semantic objects and arrows and countable typed fibers.

## 2. The cover and its proposition cardinality

Apply the construction in
[Interpretation cover: surjective chain names, §§1–8](interpretation-cover-surjective-chain-names.md)
to this family. At each type use $C_\sigma=\{\sigma\}\times\mathbb N\times\mathbb N$.
The root loops preserve chains and act on each chain by nondecreasing
surjections; retain all typed interpretations into every old object. The root
domains are the finite-pin profiles whose whole sections at old targets land
in the unchanged old domains. Its construction proves term closure, $C$,
current all-type BF, and the named-lift property. Denote this root by $K$.

Let $\mathfrak c=2^{\aleph_0}$. For a finite typed pin $S$, a whole proposition
is determined at a root loop by the tuple of name values on $S$, and at an old
interpretation by its target object and its assignment on $S$. There are only
countably many such patterns: $S$ is finite, all relevant names and old fibers
are countable, and the old objects form a countable set. An $S$-pinned
proposition is therefore a bit table on a countable set, giving at most
$\mathfrak c$ possibilities. Whole-old-domain landing only restricts these
tables. There are countably many finite pins, so

$$|D_t(K)|\le\mathfrak c.$$

This counts whole propositions, including their future rows. It neither bounds
all higher-type domains nor assumes the interpretation arrows themselves form
a countable set. Their finite-pin patterns are what have been counted.

## 3. The full-current root and its signature

Take $K$ as one component and terminal full singleton-individual models $T_n$
for $n\in\mathbb N$ as the others. Add a root $R$ with no return from a component,
with $D_e(R)=C_e$, identity individual entrance into $K$, and the unique
individual entrance into each $T_n$. At a flattened relational type admit

$$D_{\sigma_1\cdots\sigma_k t}(R)=
\mathcal P\!\left(\prod_j D_{\sigma_j}(R)\right)
\times D_{\sigma_1\cdots\sigma_k t}(K)
\times\prod_nD_{\sigma_1\cdots\sigma_k t}(T_n).$$

The first coordinate is the unrestricted current extension; the remaining
coordinates are entire admitted old entities. Application uses current
membership and component application. Transport is projection followed by old
transport. Quantification uses ordinary current quantification and the original
component quantifiers. A lambda abstraction has the current extension defined
by its formula and its component denotations in the old domains. Induction on
terms therefore gives closure, naturality and the original $C$ equations,
including Logical Equivalence with its H-theoremhood side condition. Equality
is literal identity at the current root. This is the full-current coalesced
construction; every old future and old typed domain remains unchanged.

For countable $\Sigma$, inject its constants typewise into the auxiliary names
of $K$. Their named lifts are the denotations at $K$. Interpret individual
constants at $R$ by the same names; give a relational constant its $K$ denotation
as its $K$ coordinate, any current row and arbitrary terminal coordinates.
Every constant projects correctly.

To realize a consistent closed signature sentence, replace its finitely many
constants by variables and existentially close. Free constants have no
nonlogical or unique-name axioms, so the resulting pure sentence is consistent.
A complete old component supplies its witnesses. An interpretation assigns
these whole typed witnesses to the designated names, proving signature Max at
$K$ and hence at $R$.

For signature Possibility+, fix a current individual tuple satisfying the
native distinctness and freshness guard for $P$. Its names are distinct and
disjoint from the individual constant names occurring in $P$. A pure old
realization of the existential closure of $P$ supplies values for its constant
slots and its displayed variable slots. Assign them to those names and extend
to a total typed interpretation. Relational constant names receive their entire
old values; no free relational variables are allowed by this schema. This
realizes $P$ in the full old target domains. The identity individual entrance
$R\to K$ preserves the freshness guard, so the same proof holds at $R$.
Distinct old values are not required for distinct names.

## 4. Current BF survives the product

Each entrance object satisfies current all-type BF: this is the cover theorem
for $K$ and immediate at a terminal model. Each individual entrance is onto.
Each relational entrance projection is onto as well, since a prescribed whole
component entity can be paired with any current row and arbitrary other
coordinates.

Use dual BF. If $\Diamond\exists x^\sigma Fx$ holds at $R$, a current witness
already gives $\exists x\,\Diamond Fx$. Otherwise some component $K_i$ satisfies
$\Diamond\exists x\,F_i x$. Its current BF supplies a current whole entity $b$
and a future witnessing $F_i$ of its transport. Onto projection supplies a root
$a$ mapping to $b$. The composite future witnesses $Fa$. This covers every
admitted type, including $e$, and every future quantified entity. It does not
assume later transports or their composites are onto; the component's BF
handles that part.

## 5. Strict Forcing Possibilism

The whole root proposition algebra is

$$B_R=2\times B_K\times2^{\mathbb N}.$$

It has cardinality exactly $\mathfrak c$: the upper bound follows from §2 and
the last factor supplies the lower bound. Each isolated terminal coordinate
is a Boolean atom, so there are infinitely many distinct atoms.

Full current rows externalize all the native tests at every carrier: every
external subset of a proposed Boolean algebra is admitted, and all graphs
needed for injections, Dedekind finiteness and mixed-type isomorphisms are
admitted. In ZFC every infinite complete Boolean algebra has at least
$\mathfrak c$ elements. Indeed choose a countable disjoint sequence of nonzero
elements (infinitely many atoms, or successive splittings in an atomless part);
the joins indexed by all subsets of that sequence are distinct. Hence no
infinite complete Boolean algebra is strictly smaller than $B_R$.

An eligible algebra in strict FP is consequently finite. If it has $m$ atoms,
choose $m$ of the displayed atoms of $B_R$ and let $p$ be their join. A further
displayed atom ensures $p\ne\top$, and the interval below $p$ is isomorphic to
the given finite Boolean algebra. Its isomorphism graph is admitted by full
current rows. The degenerate one-element algebra uses $p=\bot$. This proves
the exact finite-or-strictly-smaller version of FP, also at individual carriers.
It makes no completeness assertion about $B_R$ itself.

## 6. Further current properties of the same root

Let $w$ be true only at $R$, with bottom in every component coordinate. It is
below every current truth, so witnesses Actuality. There is no return to $R$;
therefore $\Diamond w=w$ as a whole proposition. For every current truth $p$,
$q=w$ witnesses $\exists q(q\land\Box(\Diamond q\to p))$, giving Truths are
ND-necessary. This checks all futures inside $K$, not just its entrance.

For Transversal Choice, apply external choice to the equivalence classes of
any current admitted equivalence relation on whole root entities. The selected
set is an admitted current row with bottom old coordinates. It selects exactly
one literal entity from each class, at every carrier.

For quantified Infinity at $e$, write $Z_n$ for the whole root denotation of
$\operatorname{Suc}_e^n(\mathbf0_e)$. The set $\{Z_n:n\in\mathbb N\}$ is the
current extension of an admitted predicate $W$ with bottom old coordinates.
It is inductive, so the impredicative finite-cardinality predicate holds only
of these standard numeral objects. Finite induction proves it holds of all
of them. A second induction using arbitrary current properties and the
admitted deleted-member term shows $Z_n(X)$ exactly when $X$ has $n$ current
members. The universal individual property has infinitely many members, so no
finite cardinality applies to it. This is the quantified Infinity axiom. The
map also derives it from signature Max and current BF; no duplicate argument
flag is needed.

## 7. Arbitrary set-sized free signatures

Use a many-sorted first-order Henkin presentation with one nonempty sort per
admitted type, application, logical operations, current truth $T$, and an
operation for every finite parameterized pure lambda template. Terms containing
signature constants are represented by substituting them as parameters into
these templates. Include conversion and interpretation clauses, current
quantifier truth, and $T(\operatorname{Eq}_\sigma(x,y))\leftrightarrow x=y$.
Propositions remain whole entities, distinct from their current truth values.
Do not impose extensionality from current coextension.

Include the translations of all $C(\Sigma)$ instances. Logical Equivalence
instances are selected externally by **H theoremhood**, never equivalence under
optional packages. Add every instance of the eight principles stated above.
Each is a finite first-order sentence at each fixed type or syntax instance.
FP's completeness, cardinality and isomorphism tests quantify over the admitted
sorts; they are not external powerset quantifiers in this presentation.

A finite fragment mentions only finitely many signature constants. Put them
in a countable free signature, adding fresh individual names as needed. Free
signature extension is conservative: models expand by arbitrary choices in
nonempty sorts, and a finite proof's extra constants can be replaced by fresh
variables after avoiding capture. The parameterized-template axioms already
hold under all assignments. Thus the H-theoremhood, C-theoremhood and
consistency side conditions selecting the fragment's Max and Possibility+
instances stay the same. For an open $P$, consistency is that of an assignment,
equivalently its existential closure, not its universal closure.

Sections 1–6 give a model of the entire countable-signature package and hence
of the fragment. Unused constants can be interpreted arbitrarily. Many-sorted
first-order compactness gives a model for the entire set-sized signature.
The Max reference theory remains $C(\Sigma)$, without the optional current
packages. The final model satisfies those packages because their native
formulas were expressly included. Its cardinality, current fullness and
standard arithmetic need not match the finite-fragment witnesses.

## Sources

The construction and scope extension are from GPT-6 Astra, prompted by Daniel
Kodsi, *Bounded composition gate: pure Max, strict FP, and current BF*, §§2–5,
and *Fixed-signature Max/FP: compactness scope gate and BF supplement*, §§2–5,
30 October 2026 (unpaginated). The strict-FP cardinal/atom criterion and the
qualified full-current product are from OpenAI Codex, prompted by Daniel Kodsi,
*Pure Maximalism and Forcing Possibilism*, 25 October 2026, §§5–6 (unpaginated).

The interpretation-root and named-witness methods are Cian Dorr's constructions
of 19 October 2026, with whole-domain verification by Claude Opus 5.5
(Anthropic), prompted by Cian Dorr. The surjective-chain-name version and its
proof are linked above. Action completeness and coalesced sums use Bacon and
Dorr, *Classicism*, Theorem 3.23, p. 57, and Appendix E, Definition E.2,
pp. 80–83, in the draft of 16 May 2023.

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — Theorem 3.23, p. 57; Appendix E, Definition E.2, pp. 80–83. Action-model completeness and coalesced sums; the joint composition is the direct source result.
