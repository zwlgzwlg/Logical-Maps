# Notes from reading the checker — Zach with Claude, 21 September 2026

Zach read this formalisation with Claude (Fable 5.1) and probed the three checks with
deliberately bad proofs. One real hole was found and closed in this commit; two soft spots
and two observations are recorded here for discussion. Every claim below was reproduced by
running `lake env lean` on a probe file against the built library; the probes that matter
are now negative controls in `Classicism/Tests.lean`.

## 1. Fixed: the gate could be bypassed by aliasing the primitive

The gate in `Classicism/Check.lean` recognised `propext`, `funext` and `Quot.sound` only as
the head of an application. Bound to a local name, the constant is an argument and the body
applies a variable, so no gated head is ever seen:

```lean
theorem fregeanHave (p : Prop) (h : p) : p = True :=
  have pe := @propext; pe ⟨fun _ => trivial, fun _ => h⟩
```

`have` elaborates to `letFun (@propext) (fun pe => pe ⟨…⟩)`. The walk saw `letFun` at the
head, a bare `.const propext` as an argument (which `visitConst` ignored, since it is an
axiom), and an application headed by the free variable `pe`. `#classicism_check` reported
"Classicism ✓ [C⁻] (axioms: [propext])" and `#classicism_types` reported "type system ✓",
because the alias binder's type `∀ {a b : Prop}, (a ↔ b) → a = b` lies entirely inside R.
That is the Fregean Axiom certified as a theorem of C⁻. The `@` matters: without it the
elaborator eta-expands `propext` into a partial application, which was caught.

The same trick evaded the gate with `let`, with `funext` (Functionality, axioms
`[Quot.sound]`) and with `Quot.sound`; those two were caught by the type check only by
accident, because their binder types mention `Sort u`, a dependent Π, or `Quot`.

A second route: the walk did not descend into `opaque` bodies at all, though `collectAxioms`
does. An `opaque hidden : ∀ p : Prop, p → p = True := fun _ h => propext ⟨…⟩` passed both
checks when used.

**The fix**, in `visit` and `visitConst`:

1. the `.const` branch rejects a bare occurrence of any of the three gated constants;
2. the `.app` branch no longer recurses into a gated head it has already handled, so the
   applied case does not trip rule 1;
3. `visitConst` descends into `opaqueInfo` values. The same line was added to
   `tvisitConst` in `Classicism/TypeSystem.lean`.

With rule 1 the walk maintains a clean invariant: every node is visited, so every occurrence
of a gated constant is either the head of an application, where its argument is checked, or
bare, where it is rejected; and every constant carrying a proof term (theorem, definition,
opaque) is descended into. The kinds not descended into carry no proof terms. An
`.mdata`-wrapped head would be rejected with a slightly misleading message, which is the safe
direction.

Five negative controls were added to `Tests.lean` (`fregeanViaHave`, `fregeanViaLet`,
`functionalityViaHave`, `fregeanViaAliasLemma`, `fregeanViaOpaque`). The full build passes:
all 124 library theorems still pass the gate with the same C⁻ split, and the type, strict
and transformer audits are unchanged.

The general point, for the design: policing the *shape* of a proof term has to be argued
for by an invariant like the one above. Banning the axiom outright, as the ICIC project does
with its attribute-tagged axiom list, needs no such argument, since no aliasing can alter
`#print axioms`. The strict layer already gives this here: a transformed theorem's trust base
is the eleven axioms and the kernel, and the gate could be deleted afterwards.

## 2. Not fixed: namespace-based trust in the other two checks

Both are caught today by the gate's closed axiom list `allowedAxioms`, so they matter only
if one check is run in isolation. Recorded for discussion rather than changed.

- `#classicism_strict` (`strictAllowedAxiom`) trusts any constant under the namespace
  `Classicism.Axiomatic`. An `axiom Classicism.Axiomatic.rogue2 : ∀ p, p = Strict.Top` is
  reported as "strict ✓ (axioms: [Classicism.Axiomatic.rogue2])". A closed list of the
  eleven names would remove this.
- `#classicism_types` (`allowedConstant`) trusts any constant with prefix `Classicism`, and
  `tvisitConst` descends into theorems and definitions but not axioms. An `axiom
  Classicism.rogue : ∀ p, p → □p` with an R-statement passes the type check. The gate check
  rejects it ("depends on the axiom `Classicism.rogue`, which is not part of Classicism").

## 3. Observation: `Ty` is a marker, so anyone can declare `Ty Nat`

`Ty` has no proof content, so `instance : Ty Nat := ⟨()⟩` is accepted, and
`necessity_of_identity m n` at `Nat` then passes the gate check as a theorem of C⁻ with
axioms `[propext]`. The type check rejects it (the binder `m : Nat` is not an R-type), and
flags the instance itself. Fine as long as both checks always run together, which
`Audit.lean` ensures; worth keeping in mind for anyone running a single command by hand.

## 4. Observation: why the type check is not optional

The gate alone is not a sound extension of the open rule to dependent types, and the failure
is two lines:

```lean
theorem boxProperty (P : e → Prop) (s : {y : e // P y}) : □ (P s.val) :=
  nec% (Subtype.property s)                       -- gate ✓: `s` is an object variable
theorem fregeanViaSubtype (P : e → Prop) (x : e) (hx : P x) : □ (P x) :=
  boxProperty P ⟨x, hx⟩                           -- gate ✓: no propext, no hypothesis in a gated argument
```

Both are reported "Classicism ✓ [C⁻]". Only `#classicism_types` stops it, by rejecting the
subtype binder. This is exactly the derivation that forced the persistence discipline in the
ICIC project (necessitating `Subtype.property` and instantiating at `⟨x, hx⟩`): the open rule
at a contingent-domain type is what goes wrong. The two projects answer it differently, the
ICIC one by restricting the rule to persistent types, this one by removing the types.

## 5. Points for discussion

- **R versus F.** Recovering the paper's theory inside a CIC-based system with a `Ty`-style
  marker only works with an R-shaped marker. Modalized Functionality holds at every type
  there (from the modal quotient axiom), and the paper's note 23 says its instances at types
  ending in `e` are not theorems of F-Classicism.
- **A guarded transformer for ICIC.** The strict layer's certificate is the thing the ICIC
  project lacks. Its analogue there would need existence guards `E x := ∃ b, b = x` in the
  induction hypothesis, Absorption in guarded form at every type, the domain axioms as
  identities `(λ y. E y) = (λ y. ⊤)`, and a per-inductive-type bundle (necessitated
  induction principle, constructor existence). Not started.
- **A model for ICIC** is the prior task. A presheaf model of CIC validates `p → □p`, since
  proofs persist upward, so the model has to allow the type of proofs of a contingent
  proposition to lose inhabitants and read `p → q` materially. Not a presheaf topos.
