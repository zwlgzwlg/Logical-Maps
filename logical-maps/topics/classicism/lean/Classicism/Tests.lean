import Classicism.Check
import Classicism.TypeSystem
import Classicism.Modal
import Classicism.Identities
import Classicism.Proofs
import Classicism.Strict
import Classicism.Tautology
import Classicism.Quantifier
import Classicism.Transformed

/-!
# Controls for the checker

Every declaration here is deliberately outside Classicism, except the positive controls
at the end. `#classicism_expect_rejection` fails the build if the checker *accepts* one
of them, so these are the regression tests for the gate itself. None of this file is
imported by the library proper.
-/

namespace Classicism.Tests

/-! ### The three axioms Classicism rejects -/

/-- `propext` applied to a hypothesis is the Fregean Axiom, which C does not prove. -/
theorem fregeanAxiom (p q : Prop) (h : p ↔ q) : p = q := propext h

/-- `funext` applied to a hypothesis is Functionality, which C does not prove. -/
theorem functionality {σ : Type} [Ty σ] (X Y : σ → Prop) (h : ∀ z, X z = Y z) : X = Y := funext h

/-- Full Extensionality, the two together. -/
theorem extensionality {σ : Type} [Ty σ] (X Y : σ → Prop) (h : ∀ z, X z ↔ Y z) : X = Y :=
  funext fun z => propext (h z)

/-- `Classical.em` reaches `Classical.choice`, which gives Functional Choice at every
type. The theory's own `em` axiom must be used instead. -/
theorem viaChoice (p : Prop) : p ∨ ¬ p := Classical.em p

/-! ### Two more routes to the Fregean Axiom

Both of the next two say that a true proposition is necessary, with `p` a propositional
*variable*. Generalised, `∀p. p → □p` is interderivable with the Fregean Axiom in
Booleanism: one direction applies the axiom to `p ↔ ⊤`, the other splits on `p` and
identifies it with `⊤` or with `⊥`. So neither is No Pure Contingency, which is the much
weaker *sentence schema* `P → □P` for `P` a closed pure sentence, and which the map
records as an optional principle in its own right. Nothing here can express that schema,
since it quantifies over syntax rather than over propositions.

They are kept apart because each exercises a different path in the checker: the first
reaches `propext` through the `nec%` macro with a free hypothesis, the second nests
`propext` inside the argument of another `propext`, so catching it needs the walk to
descend under a binder and pick the hypothesis up there. -/

/-- `nec%` applied to a hypothesis. The macro is the rule of Necessitation only when its
argument is closed; applied to `h : p` it is the Fregean Axiom. The macro cannot tell the
difference; the checker can. -/
theorem fregeanAxiomViaNec (p : Prop) (h : p) : □ p := nec% h

/-- `(p = True) = p`, that is `□p = p`, another form of the same axiom: it follows from
the Fregean Axiom, and returns `p → □p` by Leibniz's Law. Lean proves it only by applying
`propext` to the hypothesis, under a binder. This is why `Classicism/Booleanism.lean`
omits it. -/
theorem fregeanAxiomViaBoxIdentity (p : Prop) : (p = True) = p :=
  propext ⟨fun h => h ▸ trivial, fun h => propext ⟨fun _ => trivial, fun _ => h⟩⟩

/-- `simp` rewrites under binders with `forall_congr`, which applies `funext` to a
hypothesis. Any `simp` call that does so is rejected, which is why the prelude avoids
the tactic. -/
theorem viaSimp {σ : Type} [Ty σ] (X : σ → Prop) (h : ∀ z, X z = True) : (∀ z, X z) = True := by
  simp [h]

/-- An unfinished proof. -/
theorem viaSorry (p : Prop) : p := sorry

/-- The walk is transitive: a proof that is itself impeccable is still rejected when it
appeals to a rejected lemma. -/
theorem viaSmuggledLemma (p q : Prop) (h : p ↔ q) : □ (p = q) :=
  nec% (fregeanAxiom p q h)

#classicism_expect_rejection fregeanAxiom functionality extensionality viaChoice
#classicism_expect_rejection fregeanAxiomViaNec fregeanAxiomViaBoxIdentity
#classicism_expect_rejection viaSimp viaSorry viaSmuggledLemma

/-! ### The gated primitive reached other than by name

The gate recognises `propext`, `funext` and `Quot.sound` as the head of an application.
Bound to a local name, or hidden in an `opaque`, the constant never stands at a head, and
the application in the body has a variable as its head. Each proof below was certified as
a theorem of `C⁻` before the walk rejected a bare occurrence of a gated primitive and
descended into `opaque` bodies. They are the Fregean Axiom and Functionality again. -/

/-- `propext` under a `have`-bound alias. `have` is `letFun`, so `@propext` is an argument
and the body applies the local `pe`. -/
theorem fregeanViaHave (p : Prop) (h : p) : p = True :=
  have pe := @propext; pe ⟨fun _ => trivial, fun _ => h⟩

/-- The same through `let`, which is a separate node of the walk. -/
theorem fregeanViaLet (p : Prop) (h : p) : p = True :=
  let pe := @propext; pe ⟨fun _ => trivial, fun _ => h⟩

/-- `funext` under an alias: Functionality. -/
theorem functionalityViaHave {σ : Type} [Ty σ] (X Y : σ → Prop) (h : ∀ z, X z = Y z) :
    X = Y :=
  have fe := @funext; fe h

/-- The alias inside a global lemma, reached transitively. -/
theorem fregeanViaAliasLemma (p : Prop) (h : p) : □ p := fregeanViaHave p h

/-- An `opaque` body is a proof term like any other. `#print axioms` sees through it, so
the walk must too. -/
opaque hiddenFregean : ∀ p : Prop, p → p = True :=
  fun _ h => propext ⟨fun _ => trivial, fun _ => h⟩
theorem fregeanViaOpaque (p : Prop) (h : p) : p = True := hiddenFregean p h

#classicism_expect_rejection fregeanViaHave fregeanViaLet functionalityViaHave
#classicism_expect_rejection fregeanViaAliasLemma fregeanViaOpaque

/-! ### Positive controls

These must pass: the gate has to admit the shapes the library actually relies on. -/

/-- ζ-Equivalence: `funext` of `propext` of a closed biconditional. -/
theorem zetaEquivalence {σ : Type} [Ty σ] : (fun x : σ => x = x) = (fun _ : σ => True) :=
  funext fun x => propext ⟨fun _ => trivial, fun _ => rfl⟩

/-- ξ: `funext` of a closed identity. -/
theorem xiRule {σ : Type} [Ty σ] (p q : Prop) (h : p = q) :
    (fun _ : σ => p ∧ True) = (fun _ : σ => p) :=
  funext fun _ => and_true_eq p

/-- Necessitation of a closed theorem, the intended use of `nec%`. -/
theorem necessitation (p : Prop) : □ (p ∨ ¬ p) := nec% (em p)

/-- Leibniz's Law on a hypothesis is unrestricted. -/
theorem leibniz (p q : Prop) (h : p = q) (hp : □ p) : □ q := h ▸ hp

#classicism_check zetaEquivalence xiRule necessitation leibniz

/-! ### Where `e_exists` is and is not needed

`C⁻` is `H⁻` plus Classicism, and it proves nearly everything the paper proves: the only
Existence instance `H⁻` misses is the one at `e`. The library is built so that a
theorem's axiom report says which side of that line it falls on. These assertions pin
the line down. The eleven identities come out `C⁻`, which is what the paper says of the
biconditionals that generate them (n. 21). -/

#classicism_expect_c_minus intensionality modalized_functionality modal_K modal_four
#classicism_expect_c_minus necessity_of_identity converse_barcan existence_rel
#classicism_expect_c_minus Classicism.Identities.identity_identity
#classicism_expect_c_minus Classicism.Identities.distribution_or_forall
#classicism_expect_c_minus Classicism.Identities.dissolution_and_or
#classicism_expect_c_minus Classicism.Proofs.barcan_r_implies_functionality_r
#classicism_expect_c_minus Classicism.Proofs.classicism_implies_existence_rel

#classicism_expect_needs_e existence_e Classicism.Proofs.classicism_implies_existence_e

/-! ### Controls for the type-system check

The gate says nothing about type theory, so these all pass it and must be caught by
`#classicism_types` instead. That is the point of having both. -/

/-- Quantification over Lean types with no `Ty` guard. This is a genuine type quantifier,
not the map's metalinguistic `∀ᵀʸ`. -/
theorem unguardedTypeQuantifier : ∀ (σ : Type) (x : σ), x = x := fun _ _ => rfl

/-- A type outside `R`: `e → e` is not admitted, since a function type must end in `t`. -/
theorem nonRelationalArrow (f : e → e) (x : e) : f x = f x := rfl

/-- A dependent function type is outside `R` however its parts behave: `R` admits only
non-dependent `σ → τ`. -/
theorem dependentType (F : (σ : Type) → σ → Prop) (x : e) : F e x = F e x := rfl

/-- An inductive type that is not a logical constant, with its recursor. -/
theorem usesNat (n : Nat) : n = n := rfl

/-- Recursion over `Nat`: the clearest case of leaving the type theory, even though the
statement is about propositions only. -/
theorem usesNatRec (p : Prop) (h : p) : ∀ n : Nat, p := fun n => Nat.rec h (fun _ ih => ih) n

#classicism_types_expect_rejection unguardedTypeQuantifier nonRelationalArrow
#classicism_types_expect_rejection dependentType usesNat usesNatRec

-- All three pass the *gate*, which is exactly why the type check has to exist: the
-- axiom and Equivalence checks say nothing about type theory.
#classicism_check unguardedTypeQuantifier nonRelationalArrow usesNat

/-! Positive controls: the shapes the library relies on must survive the type check. -/

#classicism_types zetaEquivalence xiRule necessitation leibniz

/-! ### Controls for the strict policy

`Classicism/Strict.lean` uses no Logical Equivalence at all. Its theorems therefore pass
`#classicism_strict`, while the gate-policy library does not: every `_eq` lemma in
`Classicism/Booleanism.lean` proves the same thing by one `propext`, which the strict
policy bans. The two below are the same proposition proved under the two policies. -/

#classicism_strict Classicism.Strict.meet_assoc Classicism.Strict.compl_join
#classicism_strict Classicism.Strict.compl_compl Classicism.Strict.join_assoc

/-- Commutativity of `∧` under the gate, via `propext`: banned by the strict policy. -/
theorem gatedCommutativity (p q : Prop) : (p ∧ q) = (q ∧ p) := and_comm_eq p q

/-- The same proposition under the strict policy, via Commutativity-∧ and `congrFun`. -/
theorem strictCommutativity (p q : Prop) : (p ∧ q) = (q ∧ p) := Strict.meet_comm p q

#classicism_strict_expect_rejection gatedCommutativity
#classicism_strict strictCommutativity

/-! ### The tautology tactic

`boolean_eq` decides identities between `∧`/`∨`/`¬` formulas from the six Boolean
Identities. These are all checked strictly, so each reports only Boolean axioms. -/

namespace Taut
open Classicism.Strict

/-- A law proved by hand in `Strict.lean`, now by tactic. -/
theorem byTactic_comm (p q : Prop) : (p ∧ q) = (q ∧ p) := by boolean_eq
/-- Associativity, which by hand needed the dual cancellation lemma. -/
theorem byTactic_assoc (p q r : Prop) : (p ∨ (q ∨ r)) = ((p ∨ q) ∨ r) := by boolean_eq
/-- De Morgan. -/
theorem byTactic_deMorgan (p q : Prop) : (¬ (p ∧ q)) = ((¬ p) ∨ (¬ q)) := by boolean_eq
/-- A tautology is identical to `⊤`. -/
theorem byTactic_taut (p q : Prop) : ((p ∧ q) ∨ ((¬ p) ∨ (¬ q))) = Top := by boolean_eq
/-- Four atoms, beyond anything proved by hand. -/
theorem byTactic_four (p q r s : Prop) :
    ((p ∨ q) ∧ ((¬ p) ∨ r) ∧ (q ∨ r ∨ s)) = ((p ∨ q) ∧ ((¬ p) ∨ r)) := by boolean_eq
/-- Peirce's law, through the paper's defined implication. -/
theorem byTactic_peirce (p q : Prop) : imp (imp (imp p q) p) p = Top := by boolean_eq
/-- The self-distribution axiom of `PC`. -/
theorem byTactic_selfDistrib (p q r : Prop) :
    imp (imp p (imp q r)) (imp (imp p q) (imp p r)) = Top := by boolean_eq

#classicism_strict byTactic_comm byTactic_assoc byTactic_deMorgan byTactic_taut
#classicism_strict byTactic_four byTactic_peirce byTactic_selfDistrib
#classicism_strict Classicism.Strict.eq_of_iff_eq_top Classicism.Strict.iff_eq_top_of_eq

end Taut

/-! ### The quantifier cases of Appendix A

Every axiom of `H` that governs a quantifier or identity, shown identical to `⊤` from the
Classicist Identities, plus the two identities behind `Gen` and `Inst`. All strict. -/

namespace Quant
open Classicism.Strict

#classicism_strict Classicism.Strict.forall_const_top Classicism.Strict.exists_const_bot
#classicism_strict Classicism.Strict.ui_top Classicism.Strict.eg_top
#classicism_strict Classicism.Strict.imp_forall Classicism.Strict.meet_exists
#classicism_strict Classicism.Strict.lam_iff_self_top Classicism.Strict.ref_top
#classicism_strict Classicism.Strict.gen_top

end Quant

/-! ### The transformer

`#classicism_transform foo` runs Appendix A's induction over the proof term of `foo` and
declares `foo.nec : S' = ⊤` and `foo.strict : S'`, where `S'` is the statement read in the
paper's vocabulary. Each line below exercises it and, by the reported axioms, demonstrates
that the shallow theory is Classicism. The whole library is run in `Classicism/Audit.lean`;
these are the cases worth naming.

Boolean lemmas, and the eleven identities themselves. -/

#classicism_transform Classicism.and_comm_eq Classicism.and_assoc_eq Classicism.not_and_eq
#classicism_transform Classicism.Identities.commutativity_and
#classicism_transform Classicism.Identities.absorption_or_forall
#classicism_transform Classicism.Identities.identity_identity

/-! Statements mentioning `True`, `False`, `→` and `↔`, which no axiom mentions. -/

#classicism_transform Classicism.and_true_eq Classicism.not_true_eq Classicism.true_imp_eq
#classicism_transform Classicism.imp_eq_not_or Classicism.contrapos_eq Classicism.iff_eq_and_imp

/-! Quantifiers: proofs that pass under a binder, and `∃`-elimination. An earlier design,
which re-proved each identity instead of transforming its proof, could do none of these. -/

#classicism_transform Classicism.and_forall_absorb_eq Classicism.forall_and_distrib_eq
#classicism_transform Classicism.not_forall_eq Classicism.not_exists_eq
#classicism_transform Classicism.Identities.forall_duality

/-! Implications, with hypotheses in scope and Leibniz's Law on them: the modal logic. -/

#classicism_transform Classicism.modal_T Classicism.modal_K Classicism.modal_four
#classicism_transform Classicism.necessity_of_identity Classicism.converse_barcan
#classicism_transform Classicism.box_and_eq Classicism.dia_intro Classicism.existence_e

/-! The outputs are ordinary theorems. They pass the strict check and the type check like
anything written by hand. -/

#classicism_strict Classicism.modal_K.nec Classicism.modal_K.strict
#classicism_strict Classicism.converse_barcan.nec Classicism.forall_and_distrib_eq.strict
#classicism_types Classicism.modal_K.nec Classicism.converse_barcan.nec

/-! ### Through the class mirrors

Proofs that cite the laws of `Rel` and `Order` transform once those classes have strict
mirrors (`Classicism/Mirror.lean`). Intensionality and Modalized Functionality are the
paper's §1.5; the last line is the order law at function types, whose transform *is* the
law of the mirror instance. -/

#classicism_transform Classicism.intensionality Classicism.modalized_fregean
#classicism_transform Classicism.modalized_functionality Classicism.le_iff_arrow
#classicism_transform Classicism.persistent_iff_le Classicism.rigid_iff_box_veryWeaklyRigid

#classicism_strict Classicism.intensionality.nec Classicism.modalized_functionality.nec
#classicism_strict Classicism.le_iff_arrow.nec Classicism.persistent_iff_le.nec
#classicism_types Classicism.intensionality.nec Classicism.le_iff_arrow.nec

/-- The mirror instances themselves rest on the eleven identities alone. -/
theorem mirrorArrowLaw {σ τ : Type} [Ty σ] [Strict.SRel τ] :
    (∀ (X Y : σ → τ) (p : Prop),
      Strict.SRel.and X (Strict.SRel.constP (p ∧ Strict.SRel.coext X Y))
        = Strict.SRel.and Y (Strict.SRel.constP (p ∧ Strict.SRel.coext X Y))) = Strict.Top :=
  Strict.SRel.and_constP_coext_nec (σ → τ)

#classicism_strict mirrorArrowLaw

/-! ### Records, between instances

A record is an implication between instances of principles, with the types as parameters,
so it is a formula and the induction reaches it: each gets a necessitation, from which the
boxed record follows by `K`. -/

#classicism_transform Classicism.Proofs.functionality_r_implies_tractarianism_r
#classicism_transform Classicism.Proofs.barcan_r_implies_functionality_r
#classicism_transform Classicism.Proofs.gallin_comprehension_implies_nd
#classicism_transform Classicism.Proofs.functional_choice_r_implies_relational_choice_r
#classicism_transform Classicism.Proofs.classicism_implies_existence_e

#classicism_strict Classicism.Proofs.functionality_r_implies_tractarianism_r.nec
#classicism_strict Classicism.Proofs.functional_choice_r_implies_relational_choice_r.nec
#classicism_types Classicism.Proofs.functionality_r_implies_tractarianism_r.nec
#classicism_types Classicism.Proofs.gallin_comprehension_implies_nd.nec

/-- The strict statement of a record is the paper's, between instances read in the
paper's vocabulary: Functionality at `σ → t` with `imp` and `SRel`. -/
example {σ : Type} [Ty σ] :
    type_of% (Classicism.Proofs.functionality_r_implies_tractarianism_r.strict (σ := σ))
    = Classicism.imp (P.Functionality.strict σ Prop) (P.Tractarianism.strict σ) := rfl

/-- The boxed record, `□Functionality at σ → t` implies `□Tractarianism at σ`, from the
necessitation and `K`; this is how the map's necessitated records are read. -/
example {σ : Type} [Ty σ] :
    □ (P.Functionality σ Prop) → □ (P.Tractarianism σ) :=
  modal_K _ _ (nec% (Classicism.Proofs.functionality_r_implies_tractarianism_r (σ := σ)))

/-! ### No quantifier over types inside a formula

A principle is a family of formulas indexed by types, and the type-system check rejects a
proposition that quantifies over types, guarded or not, anywhere but in the leading
telescope of a declaration. These would otherwise pass every other check. -/

/-- A schema written as one proposition. -/
def schemaAsProposition : Prop := ∀ {σ : Type} [Ty σ] (x : σ), x = x
#classicism_types_expect_rejection schemaAsProposition

/-- A hypothesis that is a schema. -/
theorem schemaAsHypothesis (h : ∀ {σ : Type} [Ty σ] (x : σ), x = x) : ∀ p : Prop, p = p :=
  fun p => h p
#classicism_types_expect_rejection schemaAsHypothesis

/-- Even a schema as the conclusion, with parameters in front. -/
theorem schemaAsConclusion (p : Prop) : p → ∀ {σ : Type} [Ty σ] (x : σ), x = x :=
  fun _ {_} [Ty _] x => rfl
#classicism_types_expect_rejection schemaAsConclusion

end Classicism.Tests
