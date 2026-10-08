# Models

The particular models the results cite, as opposed to the semantics they are built in
(`Semantics/`). Today these are the ideally full models of the paper's Appendix D; the
M-set models on the two-element monoids are in `Semantics/IntensionalExamples.lean`.

| module | what |
| --- | --- |
| `Permutations.lean` | Part 1: the ideally full model over the permutations of `ℕ`. |
| `MonoidModel.lean` | The model over any monoid acting on `ℕ`, and the verdict lemmas, each parametrized by the one fact about the monoid that decides it. |
| `Monoids.lean` | Parts 2 to 8: the seven submonoids of the functions on `ℕ`, and the verdicts as instances. |
| `PairInjCollapse.lean` | Dorr's monoid of 7 October 2026, the pair-preserving injections and the collapses of `0` with `1`: Vicinity, BF (by approximation by surjections), Atomlessness, and the failure of **Rigid Power** at `e → t` with `F := ⊤`, through `SRig`, the quoted rigidity unfolded. |
| `Functions.lean` | A category of sets and some functions between them (`FunCat`), the ideally full model on it, and `BF` from approximation by surjections. |
| `ContingentBarcan.lean` | The two-object model after Part 8 with `BF` but not `□BF`: `ℕ` and a point, all functions as arrows. |
| `Pointed.lean` | Any monoid model with a point adjoined (one arrow in, none back): the verdicts at the point and at `ℕ`, each from the same fact about the monoid as in `MonoidModel`, and `□P`, `◇P` from the two. |
| `PointedParts.lean` | Parts 1 to 8 with a point adjoined. |

The verdicts, each a theorem about the quoted principle (`P.Actuality.quoted`,
`P.AtomicityT.quoted`, `Sentence.bf σ`, …):

| part | monoid | `ND` | `BF` | Actuality | Atomlessness | Atomicity (`t`) | BC (`e → t`) | namespace |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 1 | permutations | `□ND_σ` | `□BF_σ` | fails | holds | fails | fails | `Perms` |
| 2 | monotone surjections | fails (`e`) | `BF_σ` | fails | holds | fails | fails | `Monoids.MonoSurj` |
| 3 | monotone functions | fails | fails (`e`) | fails | holds | fails | fails | `Monoids.Mono` |
| 4 | monotone, collapsing `0, 1` unless the identity | fails | fails | holds | (fails) | fails | fails | `Monoids.Mono01` |
| 5 | as 4, surjective | fails | `BF_σ` | holds | (fails) | fails | fails | `Monoids.MonoSurj01` |
| 6 | the identity and the truncations `gₙ m = min m n` | fails | fails | fails | (fails) | holds | fails | `Monoids.Truncs` |
| 7 | the roundings `f_{2^j} m = 2^j ⌊m / 2^j⌋` | fails | fails | holds | (fails) | holds | fails | `Monoids.Pow2` |
| 8 | the shifts `kₙ m = m ∸ n` | fails | `BF_σ` | holds | (fails) | holds | fails | `Monoids.Shifts` |

Parenthesized entries are not theorems here: Atomlessness fails wherever Actuality or
Atomicity holds, which is the map's business. No Pure Contingency holds in every model
on a monoid (`Premodel.holdsAx_npc`), so each verdict is also a verdict on the
principle's necessitation; `Results/Consistency/Consistency.lean` states the packages, one
section per part. The Boolean Completeness column of the paper's Proposition D.5 is
one lemma, `MonoidModel.not_bc_of` (the haecceities of a set `S` of numbers have no least
upper bound, when properties including them can always be strengthened by pinning them
down by more), with the paper's witnesses: the even numbers in Parts 2 to 5 and 8, all
numbers in Parts 6 and 7. Part 1's failure, which the paper gets through Proposition 2.5,
is direct by the same lemma, the permutation model being definitionally the monoid model
on the permutation group; the maximalist incompatibility with `□`Boolean Completeness
follows (`Results/SentenceSchemas/Incompatibilities.lean`).

## The eight parts with a point adjoined (formalized)

The paper's construction after Part 8, `Pointed.lean` and `PointedParts.lean` (28
September): each part's monoid with a point adjoined, one arrow into it, none back. The
statuses at `ℕ`, each from a verdict at `ℕ` and one at the point (where everything
holds):

| part | `ND` | `BF` | Actuality | Atomicity (`t`) | BC (`e → t`) | Atomlessness |
| --- | --- | --- | --- | --- | --- | --- |
| 1⁺, 2⁺ | c. false | `□BF_σ` | c. false | c. false | c. false | false |
| 3⁺ | c. false | c. false (`e`) | c. false | c. false | c. false | false |
| 4⁺ | c. false | c. false | necessary | c. false | c. false | false |
| 5⁺ | c. false | `□BF_σ` | necessary | c. false | c. false | false |
| 6⁺ | c. false | c. false | c. false | necessary | c. false | false |
| 7⁺ | c. false | c. false | necessary | necessary | c. false | false |
| 8⁺ | c. false | `□BF_σ` | necessary | necessary | c. false | false |

and in every part the paper's `◇(□ND ∧ Atomicity)`. The packages are consistent
(`Results/Consistency/ConsistencyPointed.lean`, `part1_consistent` to `part8_consistent`).
This confirms the survey below on the paper's construction, including its two
corrections to "all the same principles hold as in the original model": `ND` fails at
`ℕ` in every part, and Atomlessness fails there (`{c}` is an atom). Part 1⁺ is on the
bijections as a submonoid of the functions on `ℕ`. The "impossible" of the survey's
Atomlessness column is proved only at `ℕ` (false there), not at the point.

## Survey: two-object variants, and what they would add to the map

Written 26 September 2026 at Cian's request. The paper's own construction, the first
subsection below, is now formalized (above); the other choices of arrows are not. The question: the
paper remarks that any of these models can be modified, by adjoining a second object
with no arrows back, so that principles hold only contingently; how many new
consistency facts would such variants add to the Logical Map, if the map's model list
stayed a flat list?

### The construction, and what it does at the base

The paper's version (Appendix D, after Part 8): to a one-object model on a monoid `M`
with domain `ℕ`, adjoin `W₁ = {0}`, the single arrow `c : ℕ → {0}` from `W₀`, and no
arrows back. The category has `Hom(W₀, W₀) = M`, `Hom(W₀, W₁) = {c}`,
`Hom(W₁, W₁) = {1}`, and `c ∘ g = c`. Two things are true of every such variant, and
settle its verdicts almost mechanically.

- *The domains at `W₀` are the old ones with one extra bit.* Arrows agree on a set of
  individuals only when they have the same target, so `c` agrees with nothing but
  itself, and a set of arrows out of `W₀` is pinned down by a finite `X` iff its
  `M`-part is. So a proposition at `W₀` is a pair `(P, b)`: an old proposition and
  whether `c` is in; `□(P, b) = (□P, b)` if `b`, `(∅, b)` if not; the connectives are
  componentwise. Higher types are the same with more bookkeeping.
- *`W₁` is the one-world model on one individual.* Its only arrow is the identity,
  everything is pinned, and its domains are the full Henkin hierarchy on `{0}`. There
  `ND`, `BF`, Actuality, Atomicity, Boolean Completeness, the Fregean Axiom, and No
  Contingency all hold, and Atomlessness fails (the one true proposition is an atom).

A pure sentence's truth at an object does not depend on the arrow (`sem_pure`), so
`□P` holds at `W₀` iff `P` holds at `W₀` and at `W₁`, and `◇P` iff at one of them. So
each principle has one of four statuses at the base, given by its truth values
(at `W₀`, at `W₁`): **necessary** (T, T), **contingently true** (T, F), **contingently
false** (F, T), **impossible** (F, F).

The verdicts at `W₀`, with two corrections to the paper's "all the same principles
hold as in the original model":

- **`ND` fails at `W₀` in every variant**, at every type: `c` identifies `0` and `1`,
  and at `t` sends `(P, b)` to `b`. For Parts 2 to 8 this is no change; for Part 1 it
  is (the paper's remark is right about `◇(□ND ∧ Atomicity)`, wrong about `ND`).
- **Atomlessness fails at `W₀` in every variant.** The proposition `(∅, c)`, true
  exactly along `c`, is possible, and nothing possible is strictly below it. So this
  construction cannot make Atomlessness contingent; it makes it impossible.
- **`BF` is as in the base model.** Where every arrow of `M` is surjective on
  individuals, so is `c`, and Proposition D.6 (`ideal_bf_of_surjective`, already
  stated for any category) gives `BF_σ` at every type; where `BF_e` failed, the same
  property, extended to hold of everything along `c`, still refutes it.
- **Actuality and Atomicity (`t`) are as in the base model.** The strongest true
  proposition of the variant is `({1}, no c)`, pinned iff `{1}` was; an atom below
  `(P, b)` with `P ≠ ∅` is an old atom below `P` with `c` left out, `(∅, c)` is an
  atom itself, and conversely an atom below `(P, no c)` is an old atom.
- **Boolean Completeness** fails at `W₀` as in the base model, on the same witnesses
  (`Pointed.not_bc_of`, checked 28 September).
- **No Pure Contingency fails** at `W₀` (`¬ND_e` is true and not necessary) and holds
  at `W₁`.

So the status table for the variant `X⁺` of each base model `X`, over the principles
the map tracks, is read off:

| base `X` | `ND` | `BF` | Actuality | Atomicity | Atomlessness | `BC` | `NPC` |
| --- | --- | --- | --- | --- | --- | --- | --- |
| Part 1⁺ | c. false | necessary | c. false | c. false | impossible | c. false | c. false |
| Part 2⁺ | c. false | necessary | c. false | c. false | impossible | c. false | c. false |
| Part 3⁺ | c. false | c. false | c. false | c. false | impossible | c. false | c. false |
| Part 4⁺ | c. false | c. false | necessary | c. false | impossible | c. false | c. false |
| Part 5⁺ | c. false | necessary | necessary | c. false | impossible | c. false | c. false |
| Part 6⁺ | c. false | c. false | c. false | necessary | impossible | c. false | c. false |
| Part 7⁺ | c. false | c. false | necessary | necessary | impossible | c. false | c. false |
| Part 8⁺ | c. false | necessary | necessary | necessary | impossible | c. false | c. false |
| Henkin⁺ | c. false | necessary | necessary | necessary | impossible | necessary | c. false |

The last row is the full one-world model on a domain with at least two individuals
(`M = {1}`), with `{0}` adjoined: the smallest model in which a principle is
contingently false. Part 1⁺ and Part 2⁺ have the same row, so the paper's construction
yields **eight** distinct new packages. Each is new: every one-object model satisfies
No Pure Contingency, so every fact the map has from a model today has each principle
necessary or impossible, and none of these packages, with its contingently false
entries, is derivable from them. (The two M-set models on the two-element monoids also
have variants, `Idem⁺` and `Invol⁺`, whose interest is the Fregean Axiom becoming
contingently false; they add two more rows on a different set of columns.)

What the paper's construction does *not* give is a contingently true principle:
everything true at `W₀` is true at `{0}`, except Atomlessness and No Pure
Contingency, which it makes fail at `W₀`. For that the second object must be a world
where the principle fails, one of the Parts, and then the choice of arrows
`W₀ → W₁` matters.

### The general form: a base model over a second one

Adjoin to `X` (monoid `M` on `ℕ`) a second one-object model `Y` (monoid `M_Y` on `N`)
with `Hom(W₀, W₁)` some set `H` of functions `ℕ → N` closed under precomposition by
`M` and postcomposition by `M_Y`, no arrows back. `W₁`'s domains are `Y`'s; the
statuses are (truth in `X`-part at `W₀`, truth in `Y`). Three choices of `H`:

- **All constants** `c_n`, `n ∈ N`. Always closed. At `W₀`: a constant is never
  injective, so `ND` fails; never surjective unless `|N| = 1`, so `BF_e` fails (the
  property "`y = m` along `c_m`, anything along `M`", pinned by `{0}`, is necessarily
  true of every actual individual and not of all of `N`); every `{c_n}` is pinned by
  `{0}`, so Atomlessness fails; Actuality and Atomicity are as in `X`, by the argument
  above with `𝒫(N)` for the extra bit. Statuses: `ND`, `BF`, Atomlessness are
  (F, as in `Y`); Actuality, Atomicity, `BC` are (as in `X`, as in `Y`); `NPC`
  contingently false. Over the nine base models, the `X`-side contributes five
  distinct triples (Actuality, Atomicity, `BC`) — Parts 1 to 3, Parts 4 and 5, Part 6,
  Parts 7 and 8, Henkin — and the `Y`-side nine distinct rows, so **up to 45 distinct
  packages**, which with the eight above makes about **53**. This is the construction
  that gives, for instance, Actuality and Atomicity contingently true (Part 8 over
  Part 1) or Atomicity necessary with Actuality contingently true (Part 7 over
  Part 6).
- **All functions** `ℕ → N`. Closed. No new atoms (a set of arrows to `W₁` is never
  pinned down to a singleton), so Atomlessness at `W₀` is as in `X` and Atomicity at
  `W₀` fails (a nonempty proposition of arrows to `W₁` has no atom below it, by the cut
  of Part 3); `ND` fails; `BF_e` at `W₀` is expected to hold when it holds in `X`, by
  the paper's remark in Part 3 that every function agrees with a surjection off any
  finite set. This is the construction for **Atomlessness contingently true** (Part 1
  over Part 8), the one status the constants cannot produce; it needs its `W₀`
  verdicts checked rather than read off, since the pinned sets at `W₀` change.
- **Injections** `ℕ → N`, when `M_Y` preserves them (Part 1 as `Y`). The one option
  that could keep `ND` at `W₀`; whether `BF` survives is not obvious (an injection
  that is not a surjection does not refute `BF_e` by any finitely pinned property I
  can see), so its statuses are open.

None of this reaches `C5`: `B` (`P → □◇P`) fails at `W₀` as soon as there is an arrow
to `W₁` (take the `M`-part's `⊤` with `c` left out). For `C5` the models must be
symmetric, which is the deferred symmetric ideally full model. Among the eight base
models Part 1, a group, is a `C5` model; Parts 4 to 8 are not (`B` fails at the actual
world), nor is Part 3 (`B` fails at "`h 0 = 0`", against a constant function).

### What this says about the model list

- **Counted flatly**: the paper's own construction adds 8 models to the 4 the project
  has (the Henkin one-world model, the two M-set models, Part 1) and the 7 of Parts 2
  to 8; the constants construction adds about 45 more; the all-functions construction
  a further batch of the same order, once its verdicts are checked. Each entry, done as
  the entries are done today, is a module with six or seven verdict theorems and a
  section of package facts in `Consistency.lean`: 50-odd modules of near-identical
  shape.
- **Counted by what has to be proved**: nothing per variant. Every verdict of a
  variant is a fixed function of the verdicts of its components — the tables above are
  those functions — and the proof of each function is one theorem per construction and
  principle ("Actuality at `W₀` of `X` over `Y` iff Actuality in `X`", "`ND` fails at
  `W₀` of any variant", D.6 for `BF`). The general lemmas already have this shape:
  `ideal_bf_of_surjective` is stated for any category, `holdsAx_npc` for any one-object
  model, the `MonoidModel` verdicts for any monoid. A variant is then a record
  `(construction, base, second, arrows)` whose status vector is computed, and the flat
  list is a view of the database, not its contents.
- **What the map's flat list would need per entry if it stayed flat**: the status of
  each of seven principles, hence a consistency fact for the package and, for each
  contingently false principle, the non-theoremhood of the principle and of its
  necessitation. The rows above are the data; the count of records is roughly seven
  times the count of models.
