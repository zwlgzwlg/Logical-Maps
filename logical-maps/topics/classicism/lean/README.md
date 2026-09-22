# Classicism in Lean

> This directory is a self-contained Lake project, separate from the one in `Zach/`:
> run `lake build` from here. It was developed inside the Logical Maps repository at
> `logical-maps/topics/classicism/lean/` and moved here on 21 September 2026. Paths of the
> form `topics/classicism/…`, and the record and principle ids named in docstrings, refer to
> the *Classicism* topic of that repository.

A formalisation of Bacon and Dorr's **Classicism** inside base Lean 4, with no Mathlib
and none of Lean's own classical axioms taken for granted. The point is that the fit is
exact rather than approximate: Lean's three axioms are three principles of this map, and
removing them leaves a system in which Classicism can be stated and its theorems proved.

| Lean axiom | Principle on the map |
| --- | --- |
| `propext` | Fregean Axiom |
| `funext` (via `Quot.sound`) | Functionality |
| `Classical.choice` | Functional Choice, and more |

None of the three is a theorem of Classicism, so none may be used freely. Lean's
remaining rules for `→`, `∀`, `∧`, `∨`, `¬`, `↔`, `∃`, `=`, `True` and `False` are the
rules of the paper's `H`, short of two things, which this library adds as axioms:
excluded middle (`em`), and `∃ x : e, x = x` (`e_exists`), since Lean allows empty types
and `H` proves Existence at every type.

## C and C⁻

Dropping `e_exists` leaves the paper's `C⁻`, that is `H⁻` plus Classicism, which proves
the great majority of the paper's theorems. The library is arranged so that this line is
visible per theorem rather than global: **Existence is not built into the type system.**
The class `Ty` is a marker with no inhabitation field, so declaring `e` an `R`-type costs
nothing, and Existence is instead two theorems. `Modal.existence_rel` covers every
relational type, witnessed by the closed term `⊤_τ`, and needs no axiom.
`Modal.existence_e` is the axiom. Consequently a theorem's `#print axioms` report names
`e_exists` exactly when the theorem really uses it.

Were inhabitation folded back into `Ty`, `C⁻` could not be expressed at all, since there
`e` is a type whose inhabitation is unprovable, and `existence-r` would come out as a
triviality rather than a theorem with a stated cost. Note that an instance argument
`[Ty σ]` is a parameter, so it never propagates an axiom by itself; only instantiating at
`e` can do that.

`#classicism_audit` reports the split, and `Classicism/Tests.lean` asserts it with
`#classicism_expect_c_minus` and `#classicism_expect_needs_e`. At present 122 of the
library's 124 theorems are theorems of `C⁻`; the two exceptions are the Existence
theorem at `e` and the record that depends on it. The eleven identities are all `C⁻`,
which is what the paper says of the biconditionals generating them (n. 21).

## Logical Equivalence

Classicism is `H` closed under the rule

> **Equivalence.** If ⊢ P ↔ Q then ⊢ (λv̄.P) = (λv̄.Q).

A rule cannot be a Lean axiom. The rendering used here is a restriction on how
`propext` and `funext` may appear:

> `propext h` and `funext h` are admissible **only when `h` is closed**: the proof term
> `h` may mention object variables and global theorems, but no hypothesis, that is, no
> local variable whose type is a proposition.

Under that restriction `funext (fun v̄ => propext h)` is exactly ζ-Equivalence and
`funext (fun v => h)` with `h` a closed identity is the rule ξ, both of which
Classicism is closed under. Applied to a hypothesis instead, `propext` is the Fregean
Axiom and `funext` is Functionality. The restriction is a fact about the shape of the
proof term, and nothing in the term records it, so it is enforced mechanically by the
checker described below.

Because Classicism is already closed under Equivalence (§1.4), the closed proof `h` may
itself be a theorem of Classicism, not only of `H`. No separate `H`/`C` bookkeeping is
needed.

## The relational type system

The paper's type system `R` admits `e`, `t`, and `σ → τ` only when `τ ≠ e`. The class
`Ty σ` certifies that `σ` is an `R`-type and `Rel τ` that it is a relational one; the
only instances are `e`, `Prop` and arrows into relational types. So the map's `∀ᵀʸ σ` is
a parameter `(σ : Type) [Ty σ]` of a declaration, and a schema over relational types
takes a parameter `(τ : Type) [Rel τ]`.

**No formula quantifies over types.** A principle of the map is a schema, a family of
formulas indexed by types, and it is stated as exactly that: `Functionality σ τ` is a
formula once `σ` and `τ` are fixed, and there is no proposition `∀ {σ τ}, Functionality σ τ`.
A record about principles is an implication between *instances*, with the types the
argument needs as parameters, which the paper reads as a metatheorem. The type check
enforces this: a binder over a type, guarded or not, may be a parameter of a declaration
and nothing else. It is what keeps everything the shallow layer certifies within reach of
the strict layer, since a formula with type parameters is what Appendix A's induction
handles, whereas a quantifier over types has no algebra to live in. `Ty` carries no
inhabitation claim, for the reason given above; Existence at `e` and Existence at a
relational type are two instances of one family, with different proofs.

Because `Rel` is a class and not an inductive code, **there is no induction on the
structure of a relational type.** Anything whose proof recurses on that structure has to
be a class field, discharged once per shape. That is how `boxAt`, `boxImp` and the order
law `Order.le_iff` are supplied. `Order` has to be a class of its own rather than another
`Rel` field, because its arrow instance needs Modalized Functionality at `σ → τ`, which
is proved *from* the `Rel (σ → τ)` fields; as a field it would be circular. This is the
main structural constraint the shallow layer imposes, and a deep embedding is what would
lift it.
`Rel` also carries the pointwise Boolean structure that the paper writes with type
subscripts, and two closed identities that let Intensionality be proved uniformly at
every relational type. `Ty` is declared in `Type` rather than `Prop` so that an instance
argument is type-system evidence rather than a hypothesis, which matters to the gate.

## The strict policy

Under the gate, `propext` and `funext` are permitted in the ζ-Equivalence shape. Under the
**strict policy** they are banned outright and the eleven closed identities stand in their
place. `#classicism_strict` enforces it: the admitted axioms are the eleven, `e`, `e_exists`
and `em`, and nothing else. The strict modules do not even use `em`, since excluded middle
is already carried by the two Dissolution identities.

Appendix A of the paper is the metatheorem that the two policies prove the same theorems.
The strict layer is that appendix carried out on Lean proof terms: a **transformer** that
takes any gated proof and returns a strict one, by induction on the proof.

## Boolean algebras from the six identities

Appendix A reasons, at every step, about identities between **λ-terms**: its induction
hypothesis is `(λv̄. P) = (λv̄. ⊤)`, and "Booleanism" is invoked under the `λv̄`. Lean's
`funext` would turn a pointwise law into such an identity, but it is banned, and rightly,
since that is the rule ξ the paper avoids. `Classicism/Algebra.lean` gets the λ-level laws
another way. The six Boolean Identities are *closed*, so they transfer to every relational
type by Leibniz's Law alone:

* `BA τ` is a type with `and`, `or`, `neg` and the six identities in closed form;
* `BA Prop` is the six axioms, verbatim;
* `BA (σ → τ)` takes each field from the field at `τ` by **one** `congrArg`.

Huntington's derivation of a Boolean algebra from those six is then done once, about
elements `X Y Z : τ` of an arbitrary such algebra: bounds, complements, idempotence,
annihilation, absorption, a cancellation lemma, associativity of both operations,
uniqueness of complements, double negation, both De Morgan laws. At `τ := v̄ → Prop` the
operations unfold by β to the pointwise ones, so a law proved there *is* the λ-level
identity Appendix A needs. `Classicism/Strict.lean` restates the laws at `Prop` with Lean's
`∧`, `∨`, `¬`, for `rw`.

Two points of substance. The six identities are Huntington's axioms, so **associativity is
not among them and has to be derived**, through the cancellation lemma `eq_of_meet_eq`: two
elements agreeing under `p` and under `¬p` are identical. And the strict layer keeps **its
own `⊤` and `⊥`**, the paper's Figure 1 pair, because no axiom mentions Lean's `True`: an
identity can only enter from an axiom, from `rfl`, from congruence, or from `propext`, so
`(q ∨ ¬q) = True` is not reachable strictly. The same goes for Lean's `→` and `Iff`, in
place of which the strict layer has the paper's abbreviations `imp` and `iff`.

## `boolean_eq`

`Classicism/Tautology.lean` turns the algebra into a decision procedure. `boolean_eq`
proves any goal `P = Q` in any `BA τ`, where both sides are built from atoms by the Boolean
operations, the bounds, `imp` and `iff`, provided they are tautologically equivalent, and
it emits only the six Boolean Identities. It looks under λ-binders, so it proves identities
between propositions and identities between λ-terms alike:

    example (F G : σ → ρ → Prop) :
        (fun x u => F x u ∧ (G x u ∨ ¬ G x u)) = (fun x u => ¬ ¬ F x u) := by boolean_eq

The method is Shannon expansion, driven by the same cancellation lemma that gave
associativity. To prove `P = Q`, pick an atom `a` and prove `a ∧ P = a ∧ Q` and
`¬a ∧ P = ¬a ∧ Q`; each is settled by substituting `⊤` or `⊥` for `a`, which removes an
atom, so the recursion bottoms out at formulas of bounds only. Substitution is itself a
proof-generating recursion: conjunction and disjunction go through the distribution laws,
and negation through `relative_compl`, since `l ∧ Q = l ∧ Q'` does not give
`l ∧ ¬Q = l ∧ ¬Q'` by congruence alone.

This is the only decision procedure in the strict layer, and the transformer never calls it
on a theorem's content. It proves the fixed rule lemmas below, once, and bridges `¬A` to
`A → ⊥` where Lean identifies them.

## The transformer

`#classicism_transform foo` takes `foo : S`, proved under the gate, and declares

* `foo.nec : S' = ⊤`, the **necessitation** of `foo`, and
* `foo.strict : S'`,

from the eleven identities and no `propext` or `funext`, where `S'` is `S` read in the
paper's vocabulary (`True ↦ ⊤`, `False ↦ ⊥`, `→ ↦ imp`, `↔ ↦ iff`). The kernel checks both,
so a bug in the transformer yields a rejected declaration, never a false theorem. The
outputs pass `#classicism_strict` and `#classicism_types` like anything written by hand.

### It is an induction on the proof, and decides nothing

This is Appendix A's `hardlemma` done as the paper does it. Each constructor of a proof term
has **one fixed lemma**, and the transform of a proof is those lemmas composed in the shape
of the proof. Nothing is searched for or re-proved, so a new shallow theorem needs no new
strict work.

`H` is a Hilbert system and a Lean term is a natural deduction, in which `fun h => …` puts
hypotheses in scope. So the induction hypothesis is carried in sequent form: for `t : A` in
a context with object variables `v̄` and hypotheses `H₁ … Hₙ`, the transform of `t` proves

    (λv̄. Γ → A') = (λv̄. ⊤)          Γ := ⊤ ∧ H₁' ∧ … ∧ Hₙ'

which is an identity in the algebra `v̄ → Prop`. The paper's own `Gen` already has this
relativised shape, `P' → ∀u.Q` from `P' → Q`.

| proof term | what carries the induction |
| --- | --- |
| a hypothesis | `rule_hyp`, then `rule_weaken` past later hypotheses |
| `fun h : H => b` | `rule_imp_intro` |
| application to a proof | `rule_imp_elim`: Appendix A step (i) |
| `fun u : σ => b` | Distribution-∨∀, the hypothesis under `∀u`, Proposition A.1: step (ii) |
| application to a term | Absorption-∨∀, then `rule_absorb`: case (ii) |
| a constant `c : S` | its necessitation `S' = ⊤`, then `rule_const` |
| gated `propext s` | `s` transformed with `Γ` empty, then Proposition A.3 |
| gated `funext (fun x => s)` | `s` transformed with `x` added to `v̄`; η does the rest |

The propositional rule lemmas are in `Classicism/Rules.lean`, proved once for any `BA τ`.
A **library theorem is a constant like any other**, its necessitation being its own
transform, made on demand. The core constants (`And.intro`, `Or.elim`, `Eq.refl`,
`Exists.intro`, …, about thirty in all) have theirs in `Classicism/Primitives.lean`, where
`Ref` and `LL` come from the Identity Identity and `∃`-elimination from Distribution-∧∃.
Lean's recursors take a motive, which is not an object of any `R`-type, so they are first
restated with the motive instantiated (`Prim.ll`, `Prim.and_rec`, `Prim.exists_rec`). The
identity lemmas of core Lean (`Eq.symm`, `congrArg`, `Eq.mpr`, which is what `rw` emits)
are each Leibniz's Law at some property, and their necessitations are not proved by hand:
the transformer makes them.

Every step is `congrArg` on a closed identity with β for free, which is Ref and Leibniz's
Law. **There is no ξ**: nothing is ever proved pointwise and then abstracted.

### Why the gate is exactly the right condition

The `propext` case transforms its argument with `Γ` *empty*, because Equivalence needs
`(λv̄. A ↔ B) = (λv̄. ⊤)` outright and not under hypotheses. That is sound only if the
argument mentions no hypothesis in scope, which is what the gate checks. The
natural-deduction presentation of `C` says the same from the other side: its special rule
has premises `P ⊢ Q` and `Q ⊢ P` with no side premises. And since the hypothesis is already
abstracted over `v̄`, the result of that case is the rule of Equivalence in the paper's
**bundled** form `λv̄.A = λv̄.B`; a `funext` wrapped around a `propext` needs no treatment of
its own.

### `¬A` and `A → False`

Lean identifies these; their readings `¬A'` and `¬A' ∨ ⊥` are Boolean-equivalent but not
identical. So the induction tracks the formula it has actually proved, and where a proof is
used at another reading of the same Lean formula, a bridge identity is supplied: `rfl` if
they agree up to unfolding, `boolean_eq` between λ-terms if they are Boolean-equivalent,
and congruence under a shared connective or quantifier otherwise.

### Mirrors of the classes

`Rel τ` carries three laws, stated with Lean's `True` and proved in its instances by gated
Equivalence: `propext` at `Prop`, and at `σ → τ` a `funext` of a closed identity, which is
ζ. A proof that cites one of those laws has nothing to transform into until the class has
a strict counterpart. `Classicism/Mirror.lean` supplies it, built the way `BA` is: `SRel`
holds the three laws as **closed identities between λ-terms**, so that at `Prop` each is a
tautology for `boolean_eq`, and at `σ → τ` each follows from the law at `τ` by one
`congrArg`, the operations there being pointwise and β free. The third law, the identity
behind Intensionality, needs one further step, that `∀u.Cu` is identical to `(∀u.Cu) ∧ Cz`,
which is Absorption-∨∀. There is no `funext` anywhere in it.

`Order τ` needs no new proof at all. Its one law is proved in the shallow instances from
`K`, `4`, `NI`, `CBF` and Modalized Functionality, all of which transform, so the law of
each instance of the mirror `SOrder` is **the transformer's own output** on the shallow
proof.

The transformer learns which constant mirrors which from two commands,
`#classicism_mirror` for a class, its data projections and its instances, and
`#classicism_nec` for the necessitation of a law field. So a new class costs a mirror, but
no change to the transformer, and a new theorem about an existing class costs nothing.

### Records, between instances

A record "Schema A implies Schema B" is a metatheorem in the paper: from the instances of
A one derives each instance of B. The theorem stated here is the object-level content of
that, an implication between instances with the types as parameters,

    theorem functionality_r_implies_tractarianism_r {σ : Type} [Ty σ] :
        Functionality σ Prop → Tractarianism σ

which names the instance of the premise the argument consumes. Since it is a formula once
`σ` is fixed, the induction reaches it, and its strict form is the record's statement
between the instances read in the paper's vocabulary,

    Classicism.imp (P.Functionality.strict σ Prop) (P.Tractarianism.strict σ)

and its necessitation gives the boxed record by `K`: `□Functionality σ t → □Tractarianism σ`.
That is how the map's necessitated records are read, and the tests check one.

### Coverage

`Classicism/Transformed.lean` runs the transformer over the whole library, once, and is the
one home of what it declares. `Classicism/Audit.lean` then holds all of it to the strict
check and the type check: 222 generated theorems, 222 strict, 222 inside `R`.

| module | transformed |
| --- | --- |
| `Booleanism` | 47 of 47 |
| `Identities` | 13 of 13 |
| `Modal` | 18 of 18 |
| `Order` | 6 of 6 |
| `Comprehension` | 10 of 10 |
| `Proofs` | 31 of 31 |

**Every theorem of the shallow layer has a strict form**, from the eleven identities, `e`,
`e_exists` and `em`, with no `propext` and no `funext`. Nothing was proved by hand for any
particular theorem; the transformer is a fixed program, and a new theorem whose proof is
built from the constructors it knows costs nothing.

What the transformer does not handle, none of it needed by the library: a motive that
depends on the identity proof, a recursor eliminating into data, and a bare gated `funext`
whose body is an identity at a relational type other than `Prop` not ending in `propext`.
Each is reported, never guessed at.

## The metalogical layer

The third layer, begun 22 September 2026, makes the terms of the object language, their
derivations and their models into objects of Lean, so that statements *about* the language
can be made: that a schema implies a schema, that a closed pure sentence is a theorem, that
a sentence holds in a model. (Earlier notes called this the "deep" layer.) It lives under
`Classicism/Meta/` and is ordinary Lean, with `funext` and the rest available, since it is
not itself a proof in Classicism but a theory of Classicism's proofs. It is related to the
other two layers by a denotation, to come, reading its terms as Lean propositions.

Four decisions fixed its shape.

* **The syntax is its own datatype**, not a subtype of Lean's `Expr`. Substitution and
  conversion are things this layer proves theorems about, and `Expr`'s are implemented
  behind `extern` with no equations; a typing relation for `Expr` would be the Lean4Lean
  project; and the metalogical statements need a small closed grammar with decidable
  notions of "closed" and "pure". The bridge to the shallow layer will be the standard
  reflection pattern, a denotation checked by `rfl` per theorem.
* **Terms are intrinsically typed**, `Term Σ Γ σ`, so an ill-typed term cannot be written.
* **Variables are de Bruijn indices**, so α-equivalence is identity and only β and η remain.
  No higher-order abstract syntax.
* **The type system is fixed**, `e` and `t` the only base types, with nonlogical vocabulary
  entering through a signature `Σ` of constants; the pure language is the empty signature.

What exists so far:

* `Meta/Types.lean`: types and relational types as the mutual inductive of *Elimination*,
  Appendix A, with decidable equality and the case split every type is `e` or
  `σ₁ → … → σₙ → t`, which the shallow layer's classes could not perform.
* `Meta/Term.lean`: signatures, contexts, variables and terms, with the paper's logical
  constants `∧`, `∨`, `¬`, `∀σ`, `∃σ`, `=σ` as constants and its abbreviations `→`, `↔`,
  `⊤`, `⊥`, `□`, `◇` as definitions; purity; renaming and substitution as maps on variables
  lifted through binders, with the identity laws and the four composition laws
  (`rename_rename`, `subst_rename`, `rename_subst`, `subst_subst`).
* `Meta/Conversion.lean`: β and η in three grades, the immediate conversion of a redex,
  the one-step closure `Step` that applies it anywhere in a term, and the equivalence
  closure; `Conv` is βη-conversion, written `≡`, and is proved a congruence.
* `Meta/Examples.lean`: a β-step computing by `rfl`, an η-step, and purity decided.

Next: derivations, natural-deduction style with Equivalence as a constructor whose premise
is a closed derivation; then the denotation and the translator.

## Files

```
Classicism/Core.lean            e, em, e_exists, □ and ◇, the classes Ty and Rel
Classicism/Equivalence.lean     the gate, the nec% macro, tactic conventions
Classicism/Booleanism.lean      the propositional and quantifier identities, pointwise
Classicism/Identities.lean      the eleven closed identities in the paper's λ-form
Classicism/Axiomatization.lean  the same eleven as axioms, for the strict policy
Classicism/Algebra.lean         Boolean algebras from the six identities, at every relational type
Classicism/Strict.lean          the same laws restated at Prop, for rw
Classicism/Tautology.lean       the boolean_eq tactic, between propositions or λ-terms
Classicism/Quantifier.lean      Proposition A.1, UI, EG, Ref, Gen, Inst at Prop
Classicism/Rules.lean           one lemma per proof rule, in any such algebra
Classicism/Primitives.lean      necessitations of the core proof constants; Ref, LL, ∃-elim
Classicism/Transform.lean       #classicism_transform: Appendix A as an induction on proof terms
Classicism/Mirror.lean          SRel and SOrder, the strict mirrors of the classes Rel and Order
Classicism/Transformed.lean     the transformer run over the library; home of foo.nec and foo.strict
Classicism/Meta/Types.lean      metalogical layer: the types of R as an inductive
Classicism/Meta/Term.lean       intrinsically typed de Bruijn terms; renaming, substitution
Classicism/Meta/Conversion.lean β, η, one-step and equivalence closures; ≡
Classicism/Meta/Examples.lean   small computed checks
Classicism/Modal.lean           K, T, 4, NI, CBF, Intensionality and its corollaries
Classicism/Order.lean           the algebraic order and its pointwise characterisation
Classicism/Comprehension.lean   persistence, inextensibility and the rigidity variants
Classicism/Principles.lean      one Prop per principle of the map
Classicism/Proofs.lean          one theorem per record of the map
Classicism/Check.lean           #classicism_check and #classicism_audit
Classicism/TypeSystem.lean      #classicism_types: the relational type system
Classicism/Audit.lean           runs the audit over the library at build time
Classicism/Tests.lean           negative and positive controls for the checker
```

## The checker

`#classicism_check foo` walks the proof term of `foo` and of every constant it reaches,
and reports an error unless both hold:

1. **Axioms.** Everything `foo` depends on is one of `propext`, `Quot.sound`, `e`,
   `e_exists`, `em`. So `Classical.choice`, `sorryAx` and the alternative axioms of
   `Classicism.Axiomatization` are all rejected.
2. **The gate.** Every `propext` and `funext` occurrence reached has a closed argument,
   in the sense above. A `have`-bound proof is looked through to its value. A gated
   primitive that occurs other than as the head of an application, say bound to a local
   name by `have`, is rejected outright, since its argument is never seen; and `opaque`
   bodies are walked like theorem bodies.

`#classicism_audit Mod₁ Mod₂ …` runs it over every theorem declared in those modules.
`Classicism/Audit.lean` runs the audit over the whole library, so `lake build` fails if
a proof strays. The walk reaches core lemmas too, which is why `simp` is unusable here:
it rewrites under binders through `forall_congr`, which applies `funext` to a
hypothesis. `Classicism/Tests.lean` asserts that each of these is rejected, and that the
shapes the library relies on are accepted.

## The type-system check

The gate says nothing about type theory, so it is not by itself enough: a proof that
quantifies over `Type`, forms `e → e`, or recurses over `Nat` passes it. `Tests.lean`
contains three such proofs, and they do pass. `#classicism_types foo`, in
`Classicism/TypeSystem.lean`, is the second check, and `#classicism_types_audit` runs it
over a module. It enforces four things.

* **Types are types of `R`.** An `R`-type as a Lean expression is `e`, `Prop`, or a
  *non-dependent* arrow whose domain is an `R`-type and whose codomain is a relational
  one. Dependency is what excludes the rest of Lean's type theory.
* **Type variables are guarded parameters.** A type parameter `{σ : Type} [Ty σ]` counts
  as an `R`-type exactly when the telescope guards it with a `Ty`, `Rel` or `Order`
  instance; an unguarded one is a real quantifier over Lean types and is rejected. And a
  binder over a type may occur only in the leading telescope of a declaration, never inside
  a formula: a principle is a family of formulas indexed by types, not one formula
  quantifying over them.
* **Constants come from a whitelist**, in three named groups: the logical inductives with
  their constructors and recursors, which are the constants of `L` and the rules of `H`;
  the `Eq` plumbing that `rw`, `calc` and `▸` emit, which is all Leibniz's Law; and the
  formalisation's own metalanguage, `Trans` from `calc` and `PUnit` from the marker field
  of `Ty`. The three are listed separately so the distinction stays visible. A whitelisted
  core constant is treated as an accepted primitive and not descended into, since its
  definition is generic Lean; what is checked is that it is *applied at* `R`-types.

The library reaches only 59 core constants in total, which is why a whitelist is the
right instrument here. Nothing from arithmetic appears.

One weakening is worth stating plainly. Lean lifts an instance's proof fields into
`_proof_N` declarations and compiles `match` into `match_N` auxiliaries, dropping instance
arguments they do not literally use, so an auxiliary's *statement* can fall outside `R`
even when every use of it is inside. An eliminator's `motive` is the clearest case. Inside
such an auxiliary the binder and type checks are skipped and only the constant whitelist
runs, which is still what catches a forbidden recursor.

## Writing a proof

Use `rw`, `calc`, `▸`, `Eq.subst`, `congrArg` and `congrFun` freely: they are Leibniz's
Law. `rfl` proves only `βηδ`-conversions, which `H` proves. Case on a proposition with
`em_cases`, which uses this theory's `em`. Necessitate a closed theorem with
`nec% (theorem_name args)`, never `nec% h` for a hypothesis `h`: that yields `p → □p`
with `p` a variable, which is a form of the Fregean Axiom, not the map's No Pure
Contingency, whose instances are closed pure sentences. Avoid `simp`, `by_cases`,
`by_contra`, `decide` and `tauto`.

## Building

```sh
lake build
```

The toolchain is pinned in `lean-toolchain` and there are no dependencies, so the build
is self-contained and takes about a minute from cold.
