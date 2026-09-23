# Verification report — 21 September 2026

**29/77 principles defined; 27/208 records proved in Lean; 0 records carry a Lean
certificate. 122 of the library's 124 theorems are theorems of `C⁻`. The strict layer uses
no Logical Equivalence at all: it derives Boolean algebras at every relational type from the
six Boolean Identities, and from all eleven the necessitations of the primitive proof
constants. The transformer, which is Appendix A as an induction on Lean proof terms, turns
every one of the 125 gated theorems into a proof from the eleven axioms, `e`, `e_exists`
and `em`, with no `propext` or `funext`; the 222 theorems it declares all pass the strict
and type audits. No statement quantifies over types: principles are families of formulas
indexed by types, and records are implications between instances.**

## Revision, 21 September 2026

Existence was moved out of the class `Ty`, which previously carried an `exists_self`
field. That field made `classicism-implies-existence-r` report no axiom dependency at
all, because declaring `e` an `R`-type discharged `e_exists` silently, and it made the
paper's `C⁻` inexpressible, since in `C⁻` the type `e` is an `R`-type whose inhabitation
is unprovable. `Ty` is now a marker class, Existence is the two theorems `existence_rel`
and `existence_e`, and `P.Existence σ` is a family with those two as its instances. The
checker now also reports, per theorem and per module, whether the axioms stay inside
`C⁻`, and `Tests.lean` asserts that split.

Later the same day, seven comprehension and choice records were added (see *What the
second batch tested*), and then the **term-level type-system check** was written, closing
the one hole the earlier report admitted. All 124 theorems pass it. Writing it found two
real laxities in what had already been accepted, both now fixed:

1. **Unguarded type binders.** Several prelude lemmas, and all five type-schematic
   Classicist Identities, were stated as `{σ : Type}` with no `Ty` guard, so they claimed
   instances at every Lean type rather than at the types of `R`. The Identity Identity, for
   example, was being asserted at `σ := Nat`. Sixteen declarations across six files gained
   a `[Ty σ]` binder.
2. **The choice definitions.** `Serial` and `Functional` were likewise unguarded.

Neither affected a proof, but both made statements stronger and wider than the map's
schemata, which is exactly the sort of drift the check is for. The original 20 September
report follows.

**Gate bypass, found and closed the same evening.** The gate recognised `propext`,
`funext` and `Quot.sound` only as the head of an application. Bound to a local name, as in
`have pe := @propext; pe ⟨fun _ => trivial, fun _ => h⟩`, the constant is an argument and
the body applies the variable `pe`, so no gated head is ever seen, and the walk did not
descend into `opaque` bodies at all. Both routes certified the Fregean Axiom `p → p = True`
as a theorem of `C⁻`, and the `funext` alias certified Functionality; the type check caught
the `funext` and `Quot.sound` aliases only by accident of their binder types. The walk now
rejects any bare occurrence of a gated primitive and descends into `opaque`s, which makes
every occurrence in the reachable term graph either checked or rejected. Five negative
controls in `Tests.lean` pin it. The library is unaffected: all 124 theorems still pass.

This is the first stage of the Lean layer. It establishes the setting and the
discipline, and ports a connected fragment of the map to test both. It does not yet
certify anything in the database: every classicism record still reads `lean: none`, and
the map displays no Lean badge. The reason is given under *Certificates* below.

## What was checked

`lake build` elaborates the library and runs `#classicism_audit` over every theorem in
it. The build fails if any theorem depends on an axiom outside
`{propext, Quot.sound, e, e_exists, em}` or applies `propext` or `funext` to a
hypothesis. On this run:

| Module | Theorems | Pass | In `C⁻` |
| --- | --- | --- | --- |
| `Booleanism` | 47 | 47 | 47 |
| `Identities` | 13 | 13 | 13 |
| `Modal` | 18 | 18 | 17 |
| `Order` | 5 | 5 | 5 |
| `Comprehension` | 10 | 10 | 10 |
| `Proofs` | 31 | 31 | 30 |

`Classicism/Tests.lean` additionally asserts that the checker **rejects** nine
deliberately bad proofs: `propext` on a hypothesis (the Fregean Axiom), `funext` on a
hypothesis (Functionality), both together (Extensionality), `Classical.em` (which
reaches `Classical.choice`), `nec%` on a hypothesis (the Fregean Axiom again), the identity
`(p = True) = p`, a `simp` call that rewrites under a binder, `sorry`, and a clean proof
that appeals to a rejected lemma. It asserts that four good shapes are **accepted**:
ζ-Equivalence, ξ, necessitation of a closed theorem, and Leibniz's Law on a hypothesis.

## The strict layer, 21 September

*Since this section was written the derivation has moved to `Classicism/Algebra.lean`, where
it is done for an arbitrary algebra presented by the six identities; `Classicism/Strict.lean`
now restates it at `Prop`. See stage four.*

Stage one of the Appendix A transformer is done. `Classicism/Strict.lean` derives the
Boolean algebra of propositions from the six Boolean Identities alone, under a policy that
bans `propext` and `funext` outright: bounds, complements, idempotence, annihilation,
absorption, a cancellation lemma, associativity of both operations, uniqueness of
complements, double negation and both De Morgan laws. `#classicism_strict_audit` reports
**36/36 strict**, and every theorem's axiom report names only Boolean identities. Not one
uses `em`, because excluded middle is already carried by the two Dissolution identities.
`Tests.lean` proves the same proposition, commutativity of `∧`, twice: once under the gate
and once strictly, and asserts that the strict policy rejects the first.

Three things about this stage are worth recording.

**Associativity is not an axiom.** The six identities are Huntington's postulates, two
commutative operations each distributing over the other with bounds and complements, and
associativity has to be derived. It goes through the cancellation lemma `eq_of_meet_eq`:
two propositions that agree under `p` and under `¬p` are identical, because the cases
recombine by distributivity over `p ∨ ¬p = ⊤`. Associativity of `∧` needs the dual
cancellation lemma, not the same one; the first attempt at deriving it from the `∧` version
was circular.

**The strict layer must keep its own `⊤` and `⊥`.** No axiom mentions Lean's `True`, and an
identity can enter a proof only from an axiom, from `rfl`, from congruence on identities
already held, or from `propext`. So `(q ∨ ¬q) = True` is not derivable strictly and the
library's `□p := (p = True)` cannot be reconstructed. The strict layer therefore uses the
paper's Figure 1 pair, `⊤ := (∀p. p) ∨ ¬(∀p. p)` and its dual. The shape is what pays:
since `⊤` is *some* `q ∨ ¬q` with `q` closed, Dissolution-∧∨ gives `p ∧ ⊤ = p` immediately.
Under the gate this whole issue is invisible, because `True = ⊤` is one unremarkable
Equivalence instance.

**All the tops are identical**, in three lines from Dissolution-∧∨ and Commutativity-∧:
`t_r = t_r ∧ t_s = t_s ∧ t_r = t_s`. That was the first result attempted and the sign that
the stage was tractable.

## Stage two: the `boolean_eq` tactic

`Classicism/Tautology.lean` makes the algebra decide things. `boolean_eq` proves any
tautologous identity between formulas built from atoms by `∧`, `∨`, `¬`, `⊤`, `⊥` and the
paper's defined `imp` and `iff`, emitting only the six Boolean Identities; on a
non-equivalence it names a falsifying assignment. It settles Peirce's law, the `PC`
self-distribution axiom, and four-atom absorption identities, none of which were proved by
hand, and it reproves commutativity, associativity and De Morgan.

The method is Shannon expansion on the atom list, driven by the same cancellation lemma
that gave associativity: to prove `P = Q`, prove it under `a` and under `¬a`, in each case
substituting a bound for `a` so that an atom disappears. The substitution is a second
proof-generating recursion, and its one delicate case is negation, since `l ∧ Q = l ∧ Q'`
does not yield `l ∧ ¬Q = l ∧ ¬Q'` by congruence; `relative_compl`, `l ∧ ¬q = l ∧ ¬(l ∧ q)`,
is the bridge. Cost is exponential in the atom count, which is correct for a complete
method and irrelevant at these sizes.

Two things this stage settled. The strict layer needs the paper's `imp` and `iff` rather
than Lean's `→` and `Iff`: the arrow is primitive and `Iff` is an inductive, and no axiom
connects either to the Boolean structure, exactly as with `True`. And `eq_of_iff_eq_top`,
which turns `(P ↔ Q) = ⊤` into `P = Q`, is four lines once the tactic exists. With it,
Appendix A's `PC` case is closed: any propositional `H`-theorem yields its identity from the
six axioms.

The tactic is untrusted. It hands the kernel a term, so a bug in it produces a rejected
proof rather than a false theorem.

## Stage three: the quantifier cases

`Classicism/Quantifier.lean`, eleven theorems, all strict and all inside `R`: Proposition
A.1 (`∀x.⊤ = ⊤`) and its dual, `UI`, `EG`, `Ref`, and the identities behind `Gen` and
`Inst`. With stage two this covers every base case of the paper's `hardlemma` except `LL`,
`β` and `η`.

**`UI` and `EG` are order facts.** Absorption-∨∀ says `Fy ∨ ∀F = Fy`, which is `∀F ≤ Fy`;
Absorption-∧∃ says `Fy ∧ ∃F = Fy`, which is `Fy ≤ ∃F`. Two lemmas convert an absorption
into an implication identical to `⊤`, each one `boolean_eq` and one rewrite. Neither needs
anything under a binder, since the instances come from the closed axiom by `congrFun`.

**`Gen` and `Inst` come out as identities, not rules.** Distribution-∨∀ *is*
`P → ∀u.Qu = ∀u.(P → Qu)` and Distribution-∧∃ is its dual, so the rules are one-line
corollaries.

**How the paper avoids ξ, and why it matters.** ξ, from `⊢ A = B` to
`⊢ (λv.A) = (λv.B)`, is `funext`, which the strict policy bans. The paper's `hardlemma` is
stated already λ-abstracted, and every step rewrites the target so that one of the eleven
*closed* identities appears applied to arguments, substitutes it by Ref and Leibniz's Law,
and β-reduces. Leibniz's Law is indifferent to depth and to intervening binders, so in Lean
the step is `congrArg (fun G => …G…) closedIdentity`. `Ref` is where this bites: the
Identity Identity gives `(a = a) = ∀X.(Xa ↔ Xa)`, whose body mentions `X`, so reaching
`∀X.⊤` takes six such substitutions under the binder. That is `lam_iff_self_top`, written
out, and it is the pattern stage four automates, as `liftClosed`. Lifting a *function* identity under a
quantifier needs nothing new, as `congrArg (fun F => ∀ x, F x)` does it; what is
unavailable is manufacturing the function identity from a pointwise one.

**Two encoding leaks found and fixed.** The Identity Identity had been stated with Lean's
`Iff`, which the strict layer cannot use for the same reason it cannot use `True`; it now
uses the paper's Figure 1 `iff`, defined in `Classicism/Core.lean` along with `imp`. And
`ref_top` at first reported `propext`, because reaching `Ty (σ → Prop)` ran through the
`Rel` instance, whose identity fields are gated. The type system is now carried by two pure
marker classes, `Ty` and the new `RelTy`, with `Rel` layered on top, so type-system
evidence is free of the gate. The term-level checker flagged the change the moment it was
made, which is what it is for.

## Stage four: the transformer, redesigned 21 September

The first version of the transformer **discarded** the gated argument of each `propext` and
tried to re-prove the identity with decision procedures. That cannot work in general, since
the quantifier and identity fragment has no decision procedure, and it led an earlier
revision of this report to call part of the gap permanent. That diagnosis was an artefact
of the design. Appendix A does not re-prove anything: it is an induction on the given
derivation, one fixed calculation per axiom scheme and per rule. The transformer now does
the same, and the old core is deleted.

What was built and checked:

* `Classicism/Algebra.lean`: the class `BA τ` whose six fields are the Boolean Identities in
  closed form, its instance at `Prop` (the axioms verbatim) and at `σ → τ` (one `congrArg`
  per field), and Huntington's development for an arbitrary such algebra. 42 theorems,
  42 strict. `Classicism/Strict.lean` is now 36 restatements of these at `Prop`.
* `boolean_eq` ported to any `BA τ`, reading Boolean structure under λ-binders. All its
  earlier uses pass unchanged.
* `Classicism/Rules.lean`: the rule lemmas for hypotheses, weakening, implication
  introduction and elimination, negation elimination, `UI`'s Boolean part, and Proposition
  A.3, each for any `BA τ`.
* `Classicism/Primitives.lean`: necessitations of the core proof constants. The
  propositional ones are `boolean_eq` between λ-terms closed by Proposition A.1. `Ref` and
  `LL` are derived λ-closed from the Identity Identity; `∃`-elimination from
  Distribution-∧∃ and `UI`; Existence at `e` from `Ref`, `EG` and the axiom `e_exists`.
* `Classicism/Transform.lean`: the induction. It declares `foo.nec : S' = ⊤` and
  `foo.strict : S'`, with kernel checking forced synchronous so that a rejected proof is an
  error on the spot.

All of these modules pass `#classicism_strict_audit` and `#classicism_types_audit` at build
time. The type check needed one change: `BA` is registered as type-system evidence, and its
arrow instance carries `[Ty σ]`, so that a `BA τ` exists exactly when `τ` is `v̄ → Prop` for
`R`-types `v̄`.

**Coverage after the mirrors, measured at build time by `Classicism/Transformed.lean`: 105 of 125.**
`Booleanism` 47/47, `Identities` 13/13, `Modal` 18/18, `Order` 6/6, `Comprehension` 10/10,
`Proofs` 11/31. The library count rose by one net, because the two `Order` instance laws
were given names (`le_iff_prop`, `le_iff_arrow`) and the class projection `Order.le_iff` is
no longer listed as a theorem to transform. Everything the transformer declares, 182
theorems, passes `#classicism_strict_audit` and `#classicism_types_audit` at build time.

**The class mirrors, 21 September.** `Classicism/Mirror.lean` defines `SRel` and `SOrder`.
`SRel`'s three laws are closed λ-identities. Its instance at `Prop` is three uses of
`boolean_eq` between λ-terms. Its instance at `σ → τ` lifts each law from `τ` by
`congrArg`; the third uses Absorption-∨∀ under the binders and a Boolean lemma, and contains
no `funext`, where the shallow instance has two. `SOrder`'s law at each instance is the
`.nec` the transformer produces from the shallow proof, so nothing about `Order` was proved
by hand. The type check caught two helper lemmas of mine with unguarded type variables, now
guarded. The transformer gained a registry (`#classicism_mirror`, `#classicism_nec`) and
translation of a theorem's parameters, so that `[Rel τ]` becomes `[SRel τ]`.

A structural fix came with this. The transformer declares its outputs in the module that
runs it, and the audit and the tests both ran it, so generated *definitions* clashed on
import. The outputs now have one home, `Classicism/Transformed.lean`, which both import.

**Principles as families, 22 September.** The outer mode was built and then removed.
Cian's ruling: `□S` for a schema `S` is the family of boxed instances, and "schema A
implies schema B" is a metalogical statement; what belongs in either layer is the
instance-level statement, with type variables as parameters, and the shallow layer must
certify nothing the strict layer cannot reach. So every principle is now a family
`P.Name σ τ … : Prop` with explicit type parameters, every record is an implication between
instances naming the types the argument uses, and the type-system check rejects a binder
over a type, guarded or not, anywhere but in the leading telescope of a declaration
(three negative controls pin this in `Tests.lean`). With no schema left, every theorem has
a necessitation, and the boxed records follow by `K`; one is checked in the tests.

The outer mode as built had copied a schema hypothesis as a schema hypothesis, so its
output still quantified over types; the version that would have matched the instance-level
reading, extracting the instances a proof uses, was never built. Its removal deletes the
`Copy` lemmas, `isSchematic`, `copy`, `cfeed`, `ccoerce` and `ensureCopy`, and the
transformer has one mode again. **Coverage is 125 of 125**, and the 222 theorems the
transformer declares all pass the strict and type audits.

Two changes were forced by this. `Exists.elim` is restated through `Prim.exists_rec`,
which the choice record needs. And the type audit now walks a whole module in one pass,
descending into each library constant once, with the heartbeat cap lifted for that pass;
before, each declaration re-walked the library, and the audit of the generated theorems
took longer than a build step is allowed.

**Known limits of the induction itself.** A motive that depends on the identity proof, a
recursor eliminating into data, and a type or instance abstraction inside a formula are
reported and not transformed. The bridge between two readings of one Lean formula handles
agreement up to unfolding, Boolean equivalence, and congruence under a shared connective or
quantifier, and reports anything else. A bare gated `funext` at a relational type other
than `Prop` that does not end in `propext` is not handled. Axiom reports are now coarser:
the six Boolean Identities are bundled in the `BA Prop` instance, so a transformed theorem
reports all six even if it uses one.

## The metalogical layer, 22 September

Begun after the shallow and strict layers were complete. Four modules under
`Classicism/Meta/`, all ordinary Lean (this layer is a theory *of* Classicism's proofs, so
`funext` and the other axioms are available and no audit runs over it): types as the mutual
inductive of *Elimination* Appendix A with decidable equality; intrinsically typed de
Bruijn terms over a signature, with the paper's six logical constants and Figure 1's
abbreviations; renaming and substitution with the identity laws and all four composition
laws proved; β and η as immediate, one-step and equivalence-closed relations, with
conversion `≡` proved a congruence. The examples file checks a β-step by `rfl`.

Then `Derivable Ax Δ p` (`Meta/Derivation.lean`), an inductive relation over an axiom set
with the rules of `H` in natural-deduction form and no special rule; weakening,
monotonicity in the axioms, and the `→`/`↔` rules are proved. `Meta/Axioms.lean` writes the
eleven identities as sentences and defines `C.axiomsMinus` and `C.axioms`. The examples
derive `⊤`, each axiom, `∃F` from `∀F` in a context, `∧`-symmetry from a hypothesis, and
Existence at a relational type from `λx. ⊤`. The definition of `Derivable` is the trusted
base of this layer: what it means for a sentence to be a theorem of Classicism is that
inductive, and nothing else.

Then `Meta/Denotation.lean`: the denotation of types, environments (an inductive family,
after nested pairs proved not reducibly equal to the context's reading and broke every
rewrite), interpretations, and terms; renaming and substitution commute with the
denotation, conversion preserves it, and `Derivable.sound` is proved by induction on the
derivation. The eleven identities are verified in `Prop` one by one, each by `propext` and
`funext`, so `C.Theorem.holds` and `C.consistent` follow. The examples check by `rfl` that
sentences read back are the strict layer's propositions: `⊤` is `Strict.Top`, `→` is
`imp`, and the axioms are the statements of the Lean axioms.

Then the quoter (`Meta/Quote.lean`), the first half of the translator. It builds the
sentence as syntax and elaborates it, so well-typedness is Lean's; and the reflection
theorem is checked by the kernel by `rfl`, so a wrong quotation cannot pass. It caught one
during development: `Term.dia` had been written as `¬□¬`, where the strict layer's `Dia`
is `¬(· = ⊥)`, and seven statements failed to reflect until the definition matched. The
reflection interpretation has domain the Lean type `e` itself, since statements mention
it. Run over the library at build time (`Meta/Quoted.lean`): 90 of 111 strict statements
in `Transformed`, and 16 of 22 in `Mirror`, quote and reflect; every failure is a
parameter of class `SRel` or `SOrder`. Two primitives, `Prim.congr_arg` and
`Prim.congr_fun`, had their codomain guarded by `Ty` rather than `RelTy`, which the type
check had accepted because the arrow's own `Ty` instance was assumed; the quoter refused
them, and they now say `RelTy`.

Then `Meta/Relational.lean`: the relational operations by recursion on the type, the
instances `instSRelDenote` and `instSOrderDenote` on the readings of relational types by
the same recursion, and seven lemmas by induction on the type that reading each operation
back gives the strict layer's. The quoter now sends a class parameter to a variable of
type `RTy` and a class operation to the recursive one, and proves reflection by
`reflect_by_rewriting`, a `simp only` with those lemmas followed by `rfl` for the
unfolding of `⟦t⟧` to `Prop`. A tactic failure is fatal: an earlier version had let an
elaboration error become `sorry` and reported success, which was caught when a residual
goal was printed; `Term.withoutErrToSorry` and a `hasSorry` check now guard it. With this,
**every strict statement quotes and reflects**: 111 of 111 in `Transformed`, 22 of 22 in
`Mirror`.

Then the translator (`Meta/Translate.lean`, with `Meta/Normalize.lean`). A survey of the
strict layer's proof terms found them almost entirely equational, the eleven axioms
entering through the fields of the Boolean-algebra instances, and the natural-deduction
constructors a handful of times; so the translation is Leibniz's Law at a predicate for
each of Lean's identity lemmas, with derived rules `eqCongr`, `eqTrans`, `eqMp` and
β-contracted variants `allEβ`, `substβ`, `eqCongrβ` whose conclusions are stated with
`Term.instantiate`, as Lean's typing of an application substitutes. A cited library
theorem is translated at its instantiation and declared as `c.derivable_n`, weakened
into the context by `Derivable.ofTheorem`, which needed `Derivable.rename`, proved. The
verified normalizer `Term.nf` (β by parallel passes, η by a strengthening that is proved
a section of weakening) gives conversion by reflection, `Conv.of_nf n a b rfl`; an untyped
shadow of the syntax decides where a conversion is needed and with what fuel.

The first derivations checked were `Strict.meet_comm`, `meet_top`, `join_idem`,
`compl_join` and `and_comm_eq.strict`, the last going through the whole strict machinery,
176 specializations of library lemmas among them. Getting there found: a memoization
keyed by context depth rather than context, which reused a quotation under the wrong
binder; the untyped shadow carrying each constant's context, so the same constant under
two binders compared unequal; η-reduction at the quoter, which made the hand-written
axioms mismatch, since `(λpq. p ∧ q)` became `∧`; and the kernel's cost of evaluating the
normalizer, which was the whole cost and was cut ten-fold by giving it exact fuel,
quoting faithfully so that most conversions vanish, using the β-contracted rules, and
evaluating on one side only where the other is normal. What remained cost about a minute
for that theorem, most of it the kernel evaluating substitutions.

Then the library-wide run, which taught three things. A run that printed nothing for an
hour was taken for a runaway and killed, twice; it was only slow, and its progress
lines had gone nowhere, since Lean captures what elaboration prints into the message
log. The audit now appends a line per theorem to a file named by an option, and runs
under a finite `maxHeartbeats`, with `checkSystem` calls in the translator's own loops so
that the limit is felt. Second, the elaborator's own normalization cost, 17 seconds of
that minute, was Meta-level `whnf` evaluating the same substitutions the kernel would;
the shadow now performs `instantiate`, `weaken` and `close` on itself, and that phase
is a second. Third, a micro-benchmark of the kernel found a 40-node substitution costing
17 ms, and the same function written through `Term.rec` directly 1.5 ms: `brecOn` is
what the kernel is slow at. `rename`, `subst`, `prename` and `step` are now defined by
the recursor, with `rfl` equations as their simp set and the structural definitions
kept for the compiler by `implemented_by`; the proofs that unfolded them needed only
the equation names. `absorption_and_exists.strict` went from 120 s to 44 s, the kernel's
share from 109 s to 33 s, with 407 specializations of library lemmas.

The library-wide run on the faster build found, in its first sixty theorems, twelve
failures with one cause: a law of a mirror class — `SRel.and_constP_true`, `coext_refl`,
`SOrder.le_iff`, held as fields and proved once at `Prop` and once at an arrow from the
law at the smaller type — cited at a type *variable*, which is neither an axiom nor a
theorem. There is no single derivation of such a law; there is one for every object
type, by induction on the type, and the translator now builds it through `RTy.rec`,
the `Prop` instance's proof translated as the base case and the arrow instance's as the
step, with the law at the smaller type as induction hypothesis and any lemma cited
under it taking the hypothesis as a parameter. A first version translated such lemmas in
place instead and thrashed for forty minutes.

The first derivation by induction then failed in the kernel, and the failure was a
design fault: the relational operations were functions on terms by recursion on the
type, and a function stuck at a type variable is not a node of the syntax, so `close`,
`weaken` and `instantiate` could not pass through it and the kernel could not see
`close S ≡ S`. With Cian's agreement (23 September) `∧_τ` and the other six are now
constructors of `Term`, their recursion the δ-rule of conversion (`Term.unfoldR`,
`Conv.delta`), their reading a recursion on the Lean side, and the bridge to the strict
layer's `SRel` a lemma per operation as before. Every proof over the syntax gained seven
trivial cases. A first attempt put δ into the kernel-evaluated normalizer, where it is
stuck at a type variable and so useless — a stuck term on one side of `nf n a = b`
matches nothing — so δ stays out of the normalizer: the translator unfolds an operation
at a constructor type itself, by `Conv.delta rfl` under congruences, and the quoters
emit an operation constant only at a type variable, reading it through the unfolded
instance at a constructor type. After that `SRel.coext_refl_nec.derivable : ∀ τ',
Theorem C⁻ (∀X. coext_τ' X X = ⊤)` checked in two seconds, the first theorem of this
project proved by induction on the structure of a relational type. Reflection over the
library still holds, 111 of 111 and 22 of 22.

The rest of that day went to the cost, and found the architecture. Each derivation was
specializing every cited lemma at the types it was used at, re-deriving the Boolean
identities through the arrow instances' congruence proofs at each type; `ll_lam`, whose
tautology sits three arrows deep, spent hours in the kernel. With the operations now
constants at a type variable, every class-parametric lemma is translated **once, at
object-type variables**, `BA` joins `SRel` and `SOrder` in the induction on the type, and a
citation applies the one derivation to the object types it needs. The proof term is
walked as a DAG (memoized): `ll_lam`'s is 4,407 nodes shared and 1,516,016 as a tree.
Then three measurements about the kernel: a two-sided `Conv.of_nf n a b` makes it
unfold both sides in step and compare the recursor's minor premises at every level, so
the certificate is always one-sided; comparing a substitution form with another lazily
is its slowest path, so each side of a coercion is bridged to its canonical tree first;
and the normalizer is evaluated only on the subterms that differ, reached by
congruence. Explicit β-certificates for every pass were tried in between and cost more
than any of these, in the elaborator and the kernel both. Results: `and_comm_eq.strict`
17 s (from 73), `absorption_and_exists.strict` 10 s of kernel (from 109), `ll_lam` 17 s
(from hours), the four class laws and the audit's first failures all deriving. Then the
library-wide run on this build: **111 of 111 strict theorems derived**, in eleven
minutes, the slowest 85 seconds. Every theorem of the library now has, kernel-checked,
a shallow proof, a strict proof from the eleven identities, and a derivation in the
metalogical layer's `H` plus the eleven identities as an axiom set, each link produced
by an untrusted program and checked by the kernel.

One Lean point worth recording: a rewrite whose motive's codomain is `Ty.denote D t` fails, since that is
`Prop` only after unfolding, so the formula-level lemmas are stated at `Prop` or applied
through `Eq.mp`.

## Records proved

Twenty results, each stated as the conjunction of its recorded premises implying its
recorded conclusion, with the premises taken as hypotheses rather than as axioms.

Theorems of Classicism (no premises): `classicism-implies-modal-k`,
`-modal-t`, `-modal-four`, `-modalized-fregean`, `-intensionality-r`,
`-modalized-functionality-r`, `-identity-necessary-r`, `-converse-barcan-r`,
`-existence-r`.

Implications: `distinctness-necessary-t-implies-modal-five`, `modal-five-implies-modal-b`,
`modal-b-implies-distinctness-necessary-r`, `barcan-r-implies-barcan-t`,
`necessary-barcan-t-implies-barcan-t`,
`necessary-distinctness-necessary-t-implies-distinctness-necessary-t`,
`extensionality-r-implies-fregean-axiom`, `fregean-axiom-implies-extensionality-r`,
`tractarianism-r-implies-barcan-r`, `functionality-r-implies-tractarianism-r`,
`barcan-r-implies-functionality-r`.

Comprehension and choice, added 21 September:
`rigid-comprehension-r-implies-persistent-comprehension-r`,
`rigid-comprehension-r-implies-inextensible-comprehension-r`,
`rigid-comprehension-r-implies-weak-rigid-comprehension-r`,
`weak-rigid-comprehension-r-implies-persistent-comprehension-r`,
`weak-rigid-comprehension-r-implies-very-weak-rigid-comprehension-r`,
`gallin-comprehension-implies-nd`, `functional-choice-r-implies-relational-choice-r`.

## What the second batch tested

The seven records above were chosen to put the setting under load rather than to raise
the count, and three things came out of it.

**The algebraic order is not a triviality at higher types.** The Background defines
`X ≤ Y` as `Y = X ∨_τ Y` and records that it is equivalent to the necessitated,
universally closed pointwise implication. Proving that equivalence, in
`Classicism/Order.lean`, is where the modal prelude earned its keep. Left to right, the
pointwise identities come from the relational identity by Leibniz's Law but then have to
be boxed, which is `NI` and `K`. Right to left, the boxed pointwise implication has to
become an identity again, which is Modalized Functionality, and feeding that needs the
step from `□∀z̄. X[z̄] → Y[z̄]` to `□∀z. □(…)`, which is axiom `4` followed by the
Converse Barcan Formula inside the outer box. The naive route fails exactly where it
should: an *unboxed* pointwise identity gives the relational identity only by
Functionality, which is the principle C lacks.

**There is no induction on the structure of a relational type.** `Rel` is a class, not an
inductive code, so any law whose proof recurses on type structure must be a class field
discharged once per shape. That is how `boxAt`, `boxImp` and `Order.le_iff` are supplied.
`Order` also had to become a class separate from `Rel`: its arrow instance needs
Modalized Functionality at `σ → τ`, which is proved from the `Rel (σ → τ)` fields, so as
a field of `Rel` it would be circular. This is the main structural cost of the shallow
approach and is what the metalogical layer's inductive types remove.

**Defining the comprehension predicates in unpacked form was the right call.** They are
written with `boxImp` and `boxAt`, so they need only `Rel τ`, and `persistent_iff_le`,
`weaklyInextensible_iff_le` and `inextensible_iff_le` then *prove* that they agree with
the Background's algebraic wording. Had they been defined algebraically, every
comprehension principle would have had to carry an `[Order τ]` binder, which would be
noise and would formally narrow each schema. `rigid_iff_box_veryWeaklyRigid` confirms the
Background's remark that rigidity is necessary very weak rigidity.

Otherwise the ergonomics held up. The three definitional-projection records are one line
each, and `gallin-comprehension-implies-nd` is six lines that read like the record's own
prose. No proof in this batch needed a workaround for the Equivalence gate. The only
friction was that `rw` cannot see through a class field's definitional unfolding, so a
hypothesis occasionally needs re-ascribing with `have h' : … := h` first.

**One place the formalisation improved on the record.** The recorded argument for
`functional-choice-r-implies-relational-choice-r` case-splits, saying that *if* the output
type is `e` one should first replace each output individual by its haecceity. The
haecceity detour is in fact uniform: it works at every output type, so no case split is
needed, and the Lean proof takes that route throughout. This was lucky as well as tidier,
because a case split on whether a type is `e` is **not expressible** with marker classes;
had the argument really needed one, this record could not have been done at all.

Each Lean proof follows the argument written in the record. Where the record cites the
paper, the Lean proof is that paper argument; `modal-b-implies-distinctness-necessary-r`
is Prior's, as the record says.

## Scope decisions

- **Existence is kept out of the type system**, so that `C⁻` is the base and the axiom
  shows up only where it is used. `Ty` is a marker class with no inhabitation field;
  `existence_rel` proves Existence at every relational type from the closed term `⊤_τ`
  with no axiom, and `existence_e` is the axiom. An earlier version put the witness in
  `Ty`, which made `classicism-implies-existence-r` report no axioms at all, hid the cost
  in the `Ty e` instance, and left `C⁻` inexpressible, since there `e` is a type whose
  inhabitation is unprovable. Because the schema's proof is not uniform across the two
  shapes of `R`-type, `P.Existence` is written as the conjunction of its two cases rather
  than as `∀ {σ} [Ty σ]`. An instance argument `[Ty σ]` is a parameter and propagates no
  axiom by itself; only instantiation at `e` does.
- **99 of the library's 101 theorems are theorems of `C⁻`.** The audit reports the split
  per module, and `Tests.lean` asserts it for a representative set. The two exceptions
  are `existence_e` and `classicism-implies-existence-r`. All thirteen identity theorems
  are `C⁻`, matching the paper's remark (n. 21) that the biconditionals generating them
  belong to `H⁻`.
- **Excluded middle is an axiom** (`em`), separate from `Classical.em`, whose proof goes
  through `Classical.choice` and so through Functional Choice.
- **`(p = True) = p` and `(p = False) = ¬p` are deliberately absent** from the Boolean
  prelude. Lean proves both, but only by applying `propext` to a hypothesis: they say
  that every truth is necessary, which with a propositional variable is another form of
  the Fregean Axiom, not a theorem of C, and not the map's No Pure Contingency, which is
  the weaker schema restricted to closed pure sentences. Their
  admissible replacements are `Modal.box_not_eq` and `Modal.box_and_eq`, proved by
  Leibniz's Law over closed identities.
- **The eleven identities appear twice.** `Classicism/Identities.lean` proves each by one
  gated use of Equivalence; `Classicism/Axiomatization.lean` states the same eleven as
  axioms, for the strict policy in which `propext` and `funext` are banned outright. The
  `example`s there certify by `type_of%` that each axiom is word for word the statement
  the gated file proves. Nothing in the library proves from the axioms, and the checker
  rejects a proof that does, so the two policies are at present two ways of reading one
  file rather than two developments.

## Remaining barriers

- **The term-level type-system check now exists** and all 124 theorems pass it. It
  enforces that every type is a type of `R`, that every bound type variable is guarded by
  a `Ty`, `Rel` or `Order` instance, and that every constant comes from a three-part
  whitelist. Writing it found two real laxities, recorded under the 21 September revision.
  Its one weakening: inside an elaboration auxiliary only the constant whitelist runs,
  because Lean drops instance arguments such an auxiliary does not literally use, so its
  statement can fall outside `R` while every use of it is inside.
- **The metalogical layer translates statements but not yet proofs.** Its syntax,
  `Derivable`, the standard model and the quoter exist, every strict statement quotes and
  reflects, and `C` is proved consistent, but nothing yet connects a strict proof to a
  derivation. The map's other models remain hand-verified, and the Maximalist
  principles are not yet stated.
- **57 principles have no definition**, including every comprehension, choice,
  completeness, infinity, signature and fundamentality principle. Those need the lattice
  apparatus, Frege cardinalities, and the purity side conditions.

## Certificates

No record's `lean` field was changed; all 208 remain `none`. Two things have to happen
first, and both are outside this topic's directory:

1. `pmap lean` generates `<lib>/Statements.lean` from the records, so that a proof
   inhabits a machine-written statement and cannot drift from the recorded claim. Its
   generator is specific to the unbounded-utility framework: it emits
   `∀ {O} [MeasurableSpace O] [LinearOrder O] (P : Pref O) [P.Regular]` for every
   statement. Generalising it to a per-topic statement shape is a change to
   `scripts/pmap.py`, shared tooling.
2. `pmap lean-check` is what may set `lean: verified`, and it is reached only through
   `lean_lib` in `topic.yaml`, which this topic deliberately does not yet set, precisely
   so that the broken generator is not run.

So the twenty-seven record theorems here are proved and audited, but they are not yet
certificates in the database's sense, because the statements they prove are hand-written
rather than generated from the records. The statements were checked against the records by hand and
by name; that is the current level of assurance, and the report says so rather than
claiming more.
