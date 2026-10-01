# The strict layer

A sideline of the project, kept for what it was built for: the exploration of how the
paper's simple type system and its eleven closed identities sit inside Lean's type theory.
It **re-proves every theorem of the shallow layer from the eleven identities alone**, by a
transformer that carries out Appendix A of *Classicism* on Lean proof terms, and it holds
those re-proofs to a stricter policy than the gate: no `propext`, no `funext`, the eleven
identities as the only axioms beyond `em` and `e_exists`.

It reads its proofs from the main project (`Classicism/*.lean`) and nothing in the main
project reads from it: since the evening of 24 September 2026 the route from a shallow
proof to a certificate in the object language runs through `Classicism/Tools/Translate.lean`
directly, and the metalogical layer's derivability is `H` closed under Subst rather than
the eleven identities (`Classicism/README.md`). The layer still builds and is audited
(`Strict/Audit.lean`, `Strict/Tests.lean`), and Appendix A itself — that the eleven
identities axiomatize the theory — remains a theorem to be proved *about* the metalogical
layer's `Derivable`, for which this layer's transformer is the constructive evidence,
one theorem at a time.

```
Strict/Axiomatization.lean  the eleven identities as Lean axioms, for the strict policy
Strict/Algebra.lean         Boolean algebras from the six identities, at every relational type
Strict/Vocabulary.lean      the same laws restated at Prop, for rw; Top, Bot, Box, imp, iff
Strict/Tautology.lean       the boolean_eq tactic, between propositions or λ-terms
Strict/Quantifier.lean      Proposition A.1, UI, EG, Ref, Gen, Inst at Prop
Strict/Rules.lean           one lemma per proof rule, in any such algebra
Strict/Primitives.lean      necessitations of the core proof constants; Ref, LL, ∃-elim
Strict/Transform.lean       #classicism_transform: Appendix A as an induction on proof terms
Strict/Mirror.lean          SRel, SOrder and SPointwise, the strict mirrors of the classes
Strict/Transformed.lean     the transformer run over the library; home of foo.nec and foo.strict
Strict/Audit.lean           the strict policy and type-system audits of all of the above
Strict/Tests.lean           controls for the policy, the tactic, the quantifier cases, the transformer
```

The sections below are the account written while this was the route to certification;
the file paths in them are the current ones.

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
since that is the rule ξ the paper avoids. `Strict/Algebra.lean` gets the λ-level laws
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
identity Appendix A needs. `Strict/Vocabulary.lean` restates the laws at `Prop` with Lean's
`∧`, `∨`, `¬`, for `rw`.

Two points of substance. The six identities are Huntington's axioms, so **associativity is
not among them and has to be derived**, through the cancellation lemma `eq_of_meet_eq`: two
elements agreeing under `p` and under `¬p` are identical. And the strict layer keeps **its
own `⊤` and `⊥`**, the paper's Figure 1 pair, because no axiom mentions Lean's `True`: an
identity can only enter from an axiom, from `rfl`, from congruence, or from `propext`, so
`(q ∨ ¬q) = True` is not reachable strictly. The same goes for Lean's `→` and `Iff`, in
place of which the strict layer has the paper's abbreviations `imp` and `iff`.

## `boolean_eq`

`Strict/Tautology.lean` turns the algebra into a decision procedure. `boolean_eq`
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

The propositional rule lemmas are in `Strict/Rules.lean`, proved once for any `BA τ`.
A **library theorem is a constant like any other**, its necessitation being its own
transform, made on demand. The core constants (`And.intro`, `Or.elim`, `Eq.refl`,
`Exists.intro`, …, about thirty in all) have theirs in `Strict/Primitives.lean`, where
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
a strict counterpart. `Strict/Mirror.lean` supplies it, built the way `BA` is: `SRel`
holds the three laws as **closed identities between λ-terms**, so that at `Prop` each is a
tautology for `boolean_eq`, and at `σ → τ` each follows from the law at `τ` by one
`congrArg`, the operations there being pointwise and β free. The third law, the identity
behind Intensionality, needs one further step, that `∀u.Cu` is identical to `(∀u.Cu) ∧ Cz`,
which is Absorption-∨∀. There is no `funext` anywhere in it.

`Order τ` needs no new proof at all. Its one law is proved in the shallow instances from
`K`, `4`, `NI`, `CBF` and Modalized Functionality, all of which transform, so the law of
each instance of the mirror `SOrder` is **the transformer's own output** on the shallow
proof.

`Pointwise τ` (`Classicism/Pointwise.lean`, 24 September) is a third class of the same
kind: the pointwise laws of the implication `⊑` at a relational type — a preorder under
which `∧_τ` is a meet, with `const_τ` and coextension — which `Rel` does not supply and
without which nothing can be proved pointwise at a type parameter. Its instances are
tautologies at `Prop` and the law at `τ` under a `∀` at `σ → τ`; its mirror `SPointwise`
is set up exactly as `SOrder`, each law a necessitation that is the transformer's output
on the shallow instance's proof.

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

`Strict/Transformed.lean` runs the transformer over the whole library, once, and is the
one home of what it declares. `Strict/Audit.lean` then holds all of it to the strict
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

