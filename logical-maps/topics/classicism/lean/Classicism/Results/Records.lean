import Classicism.Principles

/-!
# Proofs of map records

One theorem per record of `topics/classicism/results/`, named after the record id with
hyphens replaced by underscores. Records with no premises are theorems of C. Each
docstring names the record and the source of the argument.

## Records are stated between instances

A record "Schema A implies Schema B" is, in the paper, a metatheorem: from the instances
of A one derives each instance of B. What is stated here is the object-level content of
that, an implication between **instances** with the types as parameters:

    theorem functionality_r_implies_tractarianism_r {σ : Type} [Ty σ] :
        Functionality σ Prop → Tractarianism σ

says which instance of the premise the argument consumes, Functionality at `σ → t`, for
the conclusion at `σ`. Where an argument uses a premise at several types, each is a
separate hypothesis. This is the form the type-system check requires, since no formula
quantifies over types, and it is what puts every record within the strict layer's reach:
each theorem here has a necessitation, from which the boxed record follows by `K`.
-/

namespace Classicism.Proofs
open Classicism.P

/-! ### Theorems of Classicism (records with no premises) -/

/-- `classicism-implies-modal-k`. -/
theorem classicism_implies_modal_k : ModalK := modal_K
/-- `classicism-implies-modal-t`. -/
theorem classicism_implies_modal_t : ModalT := modal_T
/-- `classicism-implies-modal-four`. -/
theorem classicism_implies_modal_four : ModalFour := modal_four
/-- `classicism-implies-modalized-fregean`. -/
theorem classicism_implies_modalized_fregean : ModalizedFregean := modalized_fregean
/-- `classicism-implies-intensionality-r`. -/
theorem classicism_implies_intensionality_r {τ : Type} [Rel τ] : Intensionality τ :=
  fun X Y => intensionality X Y
/-- `classicism-implies-modalized-functionality-r`. -/
theorem classicism_implies_modalized_functionality_r {σ τ : Type} [Ty σ] [Rel τ] :
    ModalizedFunctionality σ τ := fun X Y => modalized_functionality X Y
/-- `classicism-implies-identity-necessary-r`. -/
theorem classicism_implies_identity_necessary_r {σ : Type} [Ty σ] : NecessityOfIdentity σ :=
  fun x y => necessity_of_identity x y
/-- `classicism-implies-converse-barcan-r`. -/
theorem classicism_implies_converse_barcan_r {σ : Type} [Ty σ] : ConverseBarcan σ :=
  fun X => converse_barcan X
/-- `classicism-implies-existence-r`, the instance at `e`: the axiom `e_exists`. This is
the one record proof whose axiom report names that axiom. -/
theorem classicism_implies_existence_e : Existence e := existence_e

/-- `classicism-implies-existence-r`, the instances at relational types: a theorem of
`C⁻`, whose axiom report shows Existence there costing nothing. Together with the instance
at `e` this covers every type of `R`, which is the record. -/
theorem classicism_implies_existence_rel {τ : Type} [Rel τ] : Existence τ := existence_rel

/-! ### Modal principles (Classicism, Proposition 2.2) -/

/-- `distinctness-necessary-t-implies-modal-five`: `◇p` is `p ≠ False`, so `ND` at
type `t` applied to `p` and `False` is `5` word for word. -/
theorem distinctness_necessary_t_implies_modal_five : NecessityOfDistinctnessT → ModalFive :=
  fun nd p => nd p False

/-- `modal-five-implies-modal-b`: compose `p → ◇p` with `5`. -/
theorem modal_five_implies_modal_b : ModalFive → ModalB :=
  fun five p hp => five p (dia_intro p hp)

/-- Closed lemma for Prior's argument: `◇(x ≠ y) → x ≠ y`, since `x = y` gives
`□(x = y)` by NI and then `(x ≠ y) = False`. -/
theorem ne_of_dia_ne {σ : Type} [Ty σ] (x y : σ) : ◇ (x ≠ y) → x ≠ y := fun hd hxy =>
  hd (calc (x ≠ y) = ¬ (x = y) := rfl
        _ = ¬ True := by rw [necessity_of_identity x y hxy]
        _ = False := not_true_eq)

/-- `modal-b-implies-distinctness-necessary-r` (Prior): `B` gives `□◇(x ≠ y)`; the
necessitation of the closed lemma and `K` give `□(x ≠ y)`. -/
theorem modal_b_implies_distinctness_necessary_r {σ : Type} [Ty σ] :
    ModalB → NecessityOfDistinctness σ := by
  intro b x y hne
  exact modal_K _ _ (nec% (ne_of_dia_ne x y)) (b (x ≠ y) hne)

/-- `necessary-barcan-t-implies-barcan-t`: `T`. -/
theorem necessary_barcan_t_implies_barcan_t : NecBarcanT → BarcanT := box_elim

/-- `necessary-distinctness-necessary-t-implies-distinctness-necessary-t`: `T`. -/
theorem necessary_distinctness_necessary_t_implies_distinctness_necessary_t :
    NecNecessityOfDistinctnessT → NecessityOfDistinctnessT := box_elim

/-- `barcan-r-implies-barcan-t`: BF at type `t` is the instance of the schema at `t`. -/
theorem barcan_r_implies_barcan_t : Barcan Prop → BarcanT := fun bf => bf

/-! ### Extensionality (Classicism, §1.4) -/

/-- `extensionality-r-implies-fregean-axiom`: the nullary instance. -/
theorem extensionality_r_implies_fregean_axiom : Extensionality Prop → FregeanAxiom :=
  fun ext p q h => ext p q h

/-- `fregean-axiom-implies-extensionality-r`: the Fregean Axiom makes the true
coextension sentence identical to `True`, and Intensionality finishes. -/
theorem fregean_axiom_implies_extensionality_r {τ : Type} [Rel τ] :
    FregeanAxiom → Extensionality τ := by
  intro fa X Y h
  exact intensionality X Y (fa (coext X Y) True ⟨fun _ => trivial, fun _ => h⟩)

/-! ### Tractarianism, Functionality and BF (Classicism, Proposition 2.1, n. 27) -/

/-- `True ≤ q` is `□q`: `q = (True ∨ q)` iff `q = True`. -/
theorem true_entails_eq_box (q : Prop) : (True ≤ q) = □ q := by
  show (q = (True ∨ q)) = (q = True)
  rw [true_or_eq]

/-- `tractarianism-r-implies-barcan-r`: take `p := True`. -/
theorem tractarianism_r_implies_barcan_r {σ : Type} [Ty σ] : Tractarianism σ → Barcan σ := by
  intro tr X h
  rw [← true_entails_eq_box]
  exact tr True X (fun x => by rw [true_entails_eq_box]; exact h x)

/-- `functionality-r-implies-tractarianism-r`: Functionality at `σ → t` identifies `X`
with `λx. p ∨ Xx`; then `∀x. Xx = ∀x. p ∨ Xx = p ∨ ∀x. Xx` by Distribution-∨∀. -/
theorem functionality_r_implies_tractarianism_r {σ : Type} [Ty σ] :
    Functionality σ Prop → Tractarianism σ := by
  intro fn p X h
  have hX : X = fun x => p ∨ X x := fn X (fun x => p ∨ X x) h
  show (∀ x, X x) = (p ∨ ∀ x, X x)
  calc (∀ x, X x) = (∀ x, p ∨ X x) := by conv => lhs; rw [hX]
    _ = (p ∨ ∀ x, X x) := (or_forall_distrib_eq X p).symm

/-- `barcan-r-implies-functionality-r`: NI pointwise, BF at `σ` to box the quantifier,
then Modalized Functionality. -/
theorem barcan_r_implies_functionality_r {σ τ : Type} [Ty σ] [Rel τ] :
    Barcan σ → Functionality σ τ := by
  intro bf X Y h
  exact modalized_functionality X Y
    (bf (fun z => X z = Y z) (fun z => necessity_of_identity _ _ (h z)))


/-! ### Comprehension (Classicism, §2.3; Dorr, *BC does not imply RC*) -/

/-- `rigid-comprehension-r-implies-persistent-comprehension-r`: the first conjunct. -/
theorem rigid_comprehension_r_implies_persistent_comprehension_r {τ : Type} [Rel τ] :
    RigidComprehension τ → PersistentComprehension τ := by
  intro rc X
  obtain ⟨Y, hY, hco⟩ := rc X
  exact ⟨Y, hY.1, hco⟩

/-- `rigid-comprehension-r-implies-inextensible-comprehension-r`: the second conjunct. -/
theorem rigid_comprehension_r_implies_inextensible_comprehension_r {τ : Type} [Rel τ] :
    RigidComprehension τ → InextensibleComprehension τ := by
  intro rc X
  obtain ⟨Y, hY, hco⟩ := rc X
  exact ⟨Y, hY.2, hco⟩

/-- `rigid-comprehension-r-implies-weak-rigid-comprehension-r`: a rigid relation is
persistent by definition, and `T` strips the leading box from its inextensibility
conjunct. So the rigid coextension already witnesses the weaker principle. -/
theorem rigid_comprehension_r_implies_weak_rigid_comprehension_r {τ : Type} [Rel τ] :
    RigidComprehension τ → WeakRigidComprehension τ := by
  intro rc X
  obtain ⟨Y, hY, hco⟩ := rc X
  exact ⟨Y, weaklyRigid_of_rigid hY, hco⟩

/-- `weak-rigid-comprehension-r-implies-very-weak-rigid-comprehension-r`: `Persistent(Y)`
unpacks as `□∀x̄. Y[x̄] → □Y[x̄]`, and `T` gives weak persistence. The inextensibility
conjunct is the same in both conditions. -/
theorem weak_rigid_comprehension_r_implies_very_weak_rigid_comprehension_r {τ : Type} [Rel τ] :
    WeakRigidComprehension τ → VeryWeakRigidComprehension τ := by
  intro wrc X
  obtain ⟨Y, hY, hco⟩ := wrc X
  exact ⟨Y, veryWeaklyRigid_of_weaklyRigid hY, hco⟩

/-- `weak-rigid-comprehension-r-implies-persistent-comprehension-r`: the first conjunct
of weak rigidity is persistence itself. -/
theorem weak_rigid_comprehension_r_implies_persistent_comprehension_r {τ : Type} [Rel τ] :
    WeakRigidComprehension τ → PersistentComprehension τ := by
  intro wrc X
  obtain ⟨Y, hY, hco⟩ := wrc X
  exact ⟨Y, hY.1, hco⟩

/-- Closed lemma for the Gallin argument: a relation holding of `a` and failing of `b`
distinguishes them, by Leibniz's Law. Being closed, it may be necessitated. -/
theorem ne_of_holds_and_not_holds {σ : Type} [Ty σ] (Y : σ → Prop) (a b : σ) :
    (Y a ∧ ¬ Y b) → a ≠ b := fun ⟨hYa, hnYb⟩ hab => hnYb (hab ▸ hYa)

/-- `gallin-comprehension-implies-nd`. Apply Gallin Extensional Comprehension to
`λx^σ. x = a`, of the admitted type `σt`, and let `Y` be the coextension supplied.
Coextensiveness gives `Ya` from `a = a` and `¬Yb` from `b ≠ a`; persistence of `Y` and of
`¬Y` boxes each. The box distributes over the conjunction, and the closed lemma above
necessitates, so `K` yields `□(a ≠ b)`. The instance of the premise used is the one at
`σ → t`, for ND at `σ`. -/
theorem gallin_comprehension_implies_nd {σ : Type} [Ty σ] :
    GallinExtensionalComprehension (σ → Prop) → NecessityOfDistinctness σ := by
  intro gec a b hne
  obtain ⟨Y, hY, hnY, hco⟩ := gec (fun x : σ => x = a)
  have hYa : Y a := (hco a).1 rfl
  have hnYb : ¬ Y b := fun hb => hne ((hco b).2 hb).symm
  have hbox : □ (Y a) ∧ □ (¬ Y b) :=
    ⟨weaklyPersistent_apply (weaklyPersistent_of_persistent hY) a hYa,
     weaklyPersistent_neg_apply (weaklyPersistent_of_persistent hnY) b hnYb⟩
  have hconj : □ (Y a ∧ ¬ Y b) := by rw [box_and_eq]; exact hbox
  exact modal_K _ _ (nec% (ne_of_holds_and_not_holds Y a b)) hconj

/-! ### Choice (Classicism, §2.4) -/

/-- `functional-choice-r-implies-relational-choice-r`. Functional Choice cannot be
applied directly, because the output type may be `e` while an operation's output type may
not. Replace each output `y` by its haecceity `λw. w = y`, of the admitted type `τt`, and
choose among haecceities instead: the relation `λx H. ∃y. H = (λw. w = y) ∧ (Ux)y` is
serial because `U` is, so Functional Choice supplies `X : σ → τ → Prop` with `X x` a
haecceity of some `U`-successor of `x`. That `X` is itself the required subrelation, since
haecceities are injective by identity elimination. The record's argument treats the `e`
case separately; the haecceity detour is uniform, so no case split is needed. The instance
of Functional Choice used is the one at `σ`, `τ → t`, for Relational Choice at `σ`, `τ`. -/
theorem functional_choice_r_implies_relational_choice_r {σ τ : Type} [Ty σ] [Ty τ] :
    FunctionalChoice σ (τ → Prop) → RelationalChoice σ τ := by
  intro fc U hser
  -- The relation between an argument and the haecceities of its `U`-successors.
  have hser' : Serial (fun (x : σ) (H : τ → Prop) => ∃ y, H = (fun w => w = y) ∧ U x y) := by
    intro x
    obtain ⟨y, hy⟩ := hser x
    exact ⟨fun w => w = y, y, rfl, hy⟩
  obtain ⟨X, hX⟩ := fc _ hser'
  refine ⟨X, ?_, ?_⟩
  · -- `X x` is the haecceity of one `U`-successor, so it holds of exactly that one.
    intro x
    obtain ⟨y, hXy, hUy⟩ := hX x
    refine ⟨y, ?_, ?_⟩
    · show X x y
      rw [hXy]
    · intro z hz
      rw [hXy] at hz
      exact hz.symm
  · -- And everything it holds of is that successor, so it is a subrelation of `U`.
    intro x y hxy
    obtain ⟨w, hXw, hUw⟩ := hX x
    rw [hXw] at hxy
    rw [hxy]
    exact hUw

/-! ### Actuality and Boolean Completeness (Classicism, §2.2; Propositions 2.5–2.9, 2.15)

The records among Actuality, Boolean Completeness, Atomicity, the comprehension principles
and Plenitude that a shallow proof reaches. The constructions of a greatest lower bound
and of a comprehension witness are written at type `t` (or `σ → t`), where they are
propositions (or properties); the map's records range over every relational type, and
the paper says "parallel arguments establish the proposition at other relational
types". At a type variable the shallow layer cannot write `λz̄. ∀Y. X*Y → Y z̄`, so the
uniform statement is one for the metalogical layer, by induction on the arity. -/

/-- `necessary-actuality-implies-actuality`: `T`. -/
theorem necessary_actuality_implies_actuality : NecActuality → Actuality := box_elim

/-- `necessary-boolean-completeness-r-implies-boolean-completeness-r`: `T`. -/
theorem necessary_boolean_completeness_r_implies_boolean_completeness_r {τ : Type} [Rel τ] :
    NecBooleanCompleteness τ → BooleanCompleteness τ := box_elim

/-- `boolean-completeness-r-implies-boolean-completeness-t`: the instance at `t`. -/
theorem boolean_completeness_r_implies_boolean_completeness_t :
    BooleanCompleteness Prop → BooleanCompletenessT := fun h => h

/-- `extensionality-r-implies-actuality`: `⊤` is the witness. By the Fregean Axiom every
truth `q` is `⊤ ∨ q`, which is `⊤ ≤ q`. -/
theorem extensionality_r_implies_actuality : Extensionality Prop → Actuality :=
  fun ext => ⟨True, trivial, fun q hq => ext q (True ∨ q) ⟨fun _ => Or.inl trivial, fun _ => hq⟩⟩

/-- `∀p. Tp → p` and `Tq` give `q`. -/
theorem all_of_T_imp (T : Prop → Prop) (q : Prop) : T q → (∀ p, T p → p) → q := fun h hw => hw q h

/-- `persistent-comprehension-r-implies-actuality` (Classicism, n. 38): take a persistent
`T` coextensive with truth and `w := ∀p. Tp → p`. Then `w` is true; and if `q` is true,
`Tq`, hence `□Tq` by persistence, and `w` entails `q` by `K`. Persistence is all that
is used, not inextensibility. -/
theorem persistent_comprehension_r_implies_actuality :
    PersistentComprehension (Prop → Prop) → Actuality := fun pc =>
  (pc (fun p => p)).elim fun T hT =>
    ⟨∀ p, T p → p, fun p hTp => (hT.2 p).2 hTp, fun q hq =>
      le_of_box_boxImp (modal_K _ _ (nec% (all_of_T_imp T q))
        (weaklyPersistent_apply (weaklyPersistent_of_persistent hT.1) q ((hT.2 q).1 hq)))⟩

/-- `rigid-comprehension-r-implies-actuality` (Proposition 2.9): through Persistent
Comprehension. -/
theorem rigid_comprehension_r_implies_actuality : RigidComprehension (Prop → Prop) → Actuality :=
  fun rc => persistent_comprehension_r_implies_actuality
    (rigid_comprehension_r_implies_persistent_comprehension_r rc)

/-- `w ≤ Xy` is an identity, so it is necessary when true: `λy. w ≤ Xy` is persistent. -/
theorem le_apply_box {σ : Type} [Ty σ] (w : Prop) (X : σ → Prop) :
    ∀ y, Rel.le w (X y) → □ (Rel.le w (X y)) := fun y h => necessity_of_identity _ _ h

/-- `actuality-implies-persistent-comprehension-r` at `σ → t` (Classicism, n. 38): with
`w` the actual world, `λy. w ≤ Xy` is persistent, since entailments are necessary when
true, and coextensive with `X`, since `w` entails exactly the truths. -/
theorem actuality_implies_persistent_comprehension_r {σ : Type} [Ty σ] :
    Actuality → PersistentComprehension (σ → Prop) := fun act X =>
  act.elim fun w hw =>
    ⟨fun y => Rel.le w (X y), nec% (le_apply_box w X),
      fun y => ⟨fun hX => hw.2 (X y) hX, fun h => imp_of_le_prop w (X y) h hw.1⟩⟩

/-- `w → ∀y. w ∧ Xy → Zy` gives `∀y. w ∧ Xy → Zy`. -/
theorem imp_of_w_imp {σ : Type} [Ty σ] (w : Prop) (X Z : σ → Prop) :
    (w → ∀ y, w ∧ X y → Z y) → ∀ y, w ∧ X y → Z y := fun h y hy => h hy.1 y hy

/-- With `w` the actual world, `λy. w ∧ Xy` is coextensive with `X` and *weakly*
inextensible: if `∀y. w ∧ Xy → □Zy`, then `∀y. w ∧ Xy → Zy` is a truth, so `w` entails
it, which is `□∀y. w ∧ Xy → Zy`. This is the argument of Classicism, n. 38, for
`actuality-implies-inextensible-comprehension-r`; it gives the unboxed inextensibility,
and the box the map's `Inextensible` carries would need `w` to entail the truths at every
world, which Actuality does not say. So the record is not stated here. -/
theorem actuality_implies_weakly_inextensible_comprehension {σ : Type} [Ty σ] :
    Actuality → ∀ X : σ → Prop, ∃ Y : σ → Prop, WeaklyInextensible Y ∧ coext X Y := fun act X =>
  act.elim fun w hw =>
    ⟨fun y => w ∧ X y,
      fun Z hZ => modal_K _ _ (nec% (imp_of_w_imp w X Z))
        ((le_iff_prop _ _).1 (hw.2 _ (fun y hy => box_elim (hZ y hy)))),
      fun y => ⟨fun hX => ⟨hw.1, hX⟩, fun h => h.2⟩⟩

/-- `w → Zx` gives `∀y. w ∧ y = x → Zy`. -/
theorem profile_of_w_imp {σ : Type} [Ty σ] (w : Prop) (Z : σ → Prop) (x : σ) :
    (w → Z x) → ∀ y, w ∧ y = x → Z y := fun h y hy => hy.2 ▸ h hy.1

/-- `actuality-implies-actual-profile-r` at `σ` (Classicism, n. 36): `λy. w ∧ y = x` is
the true profile of `x`, and it entails every `Z` with `Zx`, since `w` entails `Zx`. -/
theorem actuality_implies_actual_profile_r {σ : Type} [Ty σ] : Actuality → ActualProfile σ :=
  fun act x => act.elim fun w hw =>
    ⟨fun y => w ∧ y = x, ⟨hw.1, rfl⟩, fun Z hZ =>
      (le_iff _ _).2 (modal_K _ _ (nec% (profile_of_w_imp w Z x))
        ((le_iff_prop _ _).1 (hw.2 (Z x) hZ)))⟩

/-! The greatest lower bound of a property `X` of propositions, from a very weakly rigid
`X*` coextensive with it: `U := ∀p. X*p → p` (Classicism, n. 40, at type `t`). -/

/-- `V → ∀q. X*q → q` and `X*p` give `V → p`. -/
theorem meet_imp (T : Prop → Prop) (V p : Prop) : (V → ∀ q, T q → q) → T p → V → p :=
  fun h hT hV => h hV p hT

/-- `∀q. X*q → V → q` gives `V → ∀q. X*q → q`. -/
theorem meet_of_forall_imp (T : Prop → Prop) (V : Prop) : (∀ q, T q → V → q) → V → ∀ q, T q → q :=
  fun h hV q hT => h q hT hV

/-- `∀p. X*p → p` is a greatest lower bound of `X`, for `X*` very weakly rigid and
coextensive with `X`. A lower bound `V` of `X` is one of `X*`, so `∀q. X*q → □(V → q)`;
weak inextensibility boxes the universal, `□∀q. X*q → V → q`, which is `V ≤ U`.
Conversely from `V ≤ U` and `X*p`, `□X*p` by weak persistence, and `K` gives `V ≤ p`. -/
theorem glb_of_veryWeaklyRigid (X T : Prop → Prop) (hT : VeryWeaklyRigid T) (hco : coext X T) :
    GLB (∀ p, T p → p) X := fun V =>
  ⟨fun hlb => (le_iff_prop _ _).2 (modal_K _ _ (nec% (meet_of_forall_imp T V))
      (hT.2 (fun q => V → q) (fun q hTq => (le_iff_prop _ _).1 (hlb q ((hco q).2 hTq))))),
   fun hle p hXp => (le_iff_prop _ _).2 (modal_K _ _ (modal_K _ _ (nec% (meet_imp T V p))
      ((le_iff_prop _ _).1 hle)) (weaklyPersistent_apply hT.1 p ((hco p).1 hXp)))⟩

/-- Very Weak Rigid Comprehension at `t → t` already gives Boolean Completeness at `t`:
the proof of `glb_of_veryWeaklyRigid` uses only weak persistence and weak
inextensibility. Not a record of the map. -/
theorem very_weak_rigid_comprehension_implies_boolean_completeness_t :
    VeryWeakRigidComprehension (Prop → Prop) → BooleanCompleteness Prop := fun vrc X =>
  (vrc X).elim fun T hT => ⟨∀ p, T p → p, glb_of_veryWeaklyRigid X T hT.1 hT.2⟩

/-- `weak-rigid-comprehension-r-implies-boolean-completeness-r`, at `t`. -/
theorem weak_rigid_comprehension_r_implies_boolean_completeness_r :
    WeakRigidComprehension (Prop → Prop) → BooleanCompleteness Prop := fun wrc =>
  very_weak_rigid_comprehension_implies_boolean_completeness_t
    (weak_rigid_comprehension_r_implies_very_weak_rigid_comprehension_r wrc)

/-- `rigid-comprehension-r-implies-boolean-completeness-r` (Proposition 2.8), at `t`. -/
theorem rigid_comprehension_r_implies_boolean_completeness_r :
    RigidComprehension (Prop → Prop) → BooleanCompleteness Prop := fun rc =>
  weak_rigid_comprehension_r_implies_boolean_completeness_r
    (rigid_comprehension_r_implies_weak_rigid_comprehension_r rc)

/-- Under the Fregean Axiom, `V ≤ p` is `V → p`. -/
theorem le_iff_imp_of_fregean (fa : FregeanAxiom) (V p : Prop) : Rel.le V p ↔ (V → p) :=
  ⟨imp_of_le_prop V p, fun h => fa p (V ∨ p) ⟨fun hp => Or.inr hp, fun hvp => hvp.elim h id⟩⟩

/-- `extensionality-r-implies-boolean-completeness-r`, at `t` (Classicism, n. 33): under
the Fregean Axiom the order is material implication, and `∀p. Xp → p` is a greatest
lower bound of `X` outright. -/
theorem extensionality_r_implies_boolean_completeness_r :
    Extensionality Prop → BooleanCompleteness Prop := fun ext X =>
  ⟨∀ p, X p → p, fun V =>
    ⟨fun hlb => (le_iff_imp_of_fregean ext V _).2
        (fun hV p hXp => (le_iff_imp_of_fregean ext V p).1 (hlb p hXp) hV),
     fun hle p hXp => (le_iff_imp_of_fregean ext V p).2
        (fun hV => (le_iff_imp_of_fregean ext V _).1 hle hV p hXp)⟩⟩

/-- `necessary-rigid-comprehension-r-implies-necessary-actuality`: the unboxed record
necessitated, and `K`. -/
theorem necessary_rigid_comprehension_r_implies_necessary_actuality :
    NecRigidComprehension (Prop → Prop) → NecActuality :=
  modal_K _ _ (nec% rigid_comprehension_r_implies_actuality)

/-- `necessary-rigid-comprehension-r-implies-necessary-boolean-completeness-r`, at `t`. -/
theorem necessary_rigid_comprehension_r_implies_necessary_boolean_completeness_r :
    NecRigidComprehension (Prop → Prop) → NecBooleanCompleteness Prop :=
  modal_K _ _ (nec% rigid_comprehension_r_implies_boolean_completeness_r)

/-- `actuality-incompatible-with-atomlessness`: a strongest truth `a` is an atom. It is
possible, so Atomlessness gives a possible `q` strictly below it; `q` is not true, else
`a ≤ q` and antisymmetry make `q = a`; so `a ∧ ¬q` is true, `a ≤ a ∧ ¬q ≤ ¬q`, and with
`q ≤ a`, `q ≤ ¬q`, which makes `q = ⊥`, against its possibility. -/
theorem actuality_incompatible_with_atomlessness : Actuality → Atomlessness → False :=
  fun act atl => act.elim fun a ha => (atl a (dia_intro a ha.1)).elim fun q hq =>
    (em q).elim
      (fun hqt => hq.2.2 (le_antisymm_prop q a hq.2.1 (ha.2 q hqt)))
      (fun hqf => hq.1 (eq_false_of_le_neg q (le_trans_prop q a (¬ q) hq.2.1
        (le_trans_prop a (a ∧ ¬ q) (¬ q) (ha.2 (a ∧ ¬ q) ⟨ha.1, hqf⟩) (and_le_right_prop a (¬ q))))))

/-! Plenitude (Classicism, §2.4, Propositions 2.13 and 2.15) -/

/-- The relation mapping each truth to itself and each falsehood to `⊤` is functional
(stated unfolded, so that the audits do not read it as a record). -/
theorem actual_rel_functional :
    ∀ p : Prop, ∃ q : Prop, ((p ∧ p = q) ∨ (¬ p ∧ q = True)) ∧
      ∀ z : Prop, ((p ∧ p = z) ∨ (¬ p ∧ z = True)) → q = z :=
  fun p => (em p).elim
    (fun hp => ⟨p, Or.inl ⟨hp, rfl⟩, fun z hz => hz.elim (fun h => h.2) (fun h => absurd hp h.1)⟩)
    (fun hp => ⟨True, Or.inr ⟨hp, rfl⟩, fun z hz => hz.elim (fun h => absurd h.1 hp) (fun h => h.2.symm)⟩)

/-- `∀p. Zp` gives `Zq`. -/
theorem all_imp (Z : Prop → Prop) (q : Prop) : (∀ p, Z p) → Z q := fun h => h q

/-- `plenitude-r-implies-actuality` (Proposition 2.15): Plenitude represents that relation
by an operation `Z`, with `Zp = p` for true `p` and `Zp = ⊤` for false `p`. Then `∀p. Zp`
is true, and it entails each `Zq`, hence each truth `q`. -/
theorem plenitude_r_implies_actuality : Plenitude Prop Prop → Actuality := fun pl =>
  (pl _ actual_rel_functional).elim fun Z hZ =>
    ⟨∀ p, Z p,
     fun p => (hZ p).elim (fun h => h.2 ▸ h.1) (fun h => h.2 ▸ trivial),
     fun q hq => (hZ q).elim
       (fun h => h.2 ▸ le_of_box_boxImp (nec% (all_imp Z q)))
       (fun h => absurd hq h.1)⟩

/-- The relation mapping `x` to `⊤` and everything else to `⊥` is functional. -/
theorem haec_rel_functional {σ : Type} [Ty σ] (x : σ) :
    Functional (fun z (w : Prop) => (x = z ∧ w = True) ∨ (x ≠ z ∧ w = False)) := fun z =>
  (em (x = z)).elim
    (fun h => ⟨True, Or.inl ⟨h, rfl⟩, fun w hw => hw.elim (fun h' => h'.2.symm) (fun h' => absurd h h'.1)⟩)
    (fun h => ⟨False, Or.inr ⟨h, rfl⟩, fun w hw => hw.elim (fun h' => absurd h'.1 h) (fun h' => h'.2.symm)⟩)

/-- `Zx = ⊤` and `Zy = ⊥` make `x ≠ y`. -/
theorem ne_of_values {σ : Type} [Ty σ] (Z : σ → Prop) (x y : σ) : Z x = True → Z y = False → x ≠ y := by
  intro hx hy hxy
  rw [hxy] at hx
  rw [hx] at hy
  exact hy ▸ trivial

/-- `plenitude-r-implies-distinctness-necessary-r` (Proposition 2.13): for `x ≠ y`, the
operation representing "`⊤` at `x`, `⊥` elsewhere" has `Zx = ⊤` and `Zy = ⊥`, both
necessarily, so necessarily `x ≠ y`. -/
theorem plenitude_r_implies_distinctness_necessary_r {σ : Type} [Ty σ] :
    Plenitude σ Prop → NecessityOfDistinctness σ := fun pl x y hxy =>
  (pl _ (haec_rel_functional x)).elim fun Z hZ =>
    have hx : Z x = True := (hZ x).elim (fun h => h.2) (fun h => absurd rfl h.1)
    have hy : Z y = False := (hZ y).elim (fun h => absurd h.1 hxy) (fun h => h.2)
    modal_K _ _ (modal_K _ _ (nec% (ne_of_values Z x y)) (necessity_of_identity _ _ hx))
      (necessity_of_identity _ _ hy)

/-- `functional-choice-r-implies-plenitude-r`: a functional relation is serial. -/
theorem functional_choice_r_implies_plenitude_r {σ τ : Type} [Ty σ] [Rel τ] :
    FunctionalChoice σ τ → Plenitude σ τ :=
  fun fc U hU => fc U (fun x => (hU x).elim fun y hy => ⟨y, hy.1⟩)

/-! Atomicity and BF imply `□`Actuality (Classicism, Proposition 2.7). -/

/-- An atom `w` entails `q → w ≤ q`, for every `q`: if `w ≤ q`, then `w ≤ q` is
necessary, so `q → w ≤ q` is `⊤`; if `w ≤ ¬q`, then `w ≤ ¬q ∨ r` for any `r`. -/
theorem atom_le_imp_le (w q : Prop) (hw : Atom w) : Rel.le w (q → Rel.le w q) :=
  (atom_le_or_le_neg w q hw).elim
    (fun h => by
      rw [show Rel.le w q = True from box_le_prop w q h, imp_true_eq]
      exact le_top_prop w)
    (fun h => by
      rw [imp_eq_not_or q (Rel.le w q)]
      exact le_or_of_le_left_prop w (¬ q) _ h)

/-- `(p → q) → (q → r) → p → r`. -/
theorem imp_trans_aux (p q r : Prop) : (p → q) → (q → r) → p → r := fun h₁ h₂ hp => h₂ (h₁ hp)

/-- `p ≤ q` and `□(q → r)` give `p ≤ r`. -/
theorem le_of_le_of_box_imp (p q r : Prop) (h : Rel.le p q) (hb : □ (q → r)) : Rel.le p r :=
  (le_iff_prop _ _).2 (modal_K _ _ (modal_K _ _ (nec% (imp_trans_aux p q r)) ((le_iff_prop _ _).1 h)) hb)

/-- `w ∧ ∀q. q → w ≤ q` gives Actuality, with `w` as witness. -/
theorem actuality_of_witness (w : Prop) : (w ∧ ∀ q, q → Rel.le w q) → Actuality := fun h => ⟨w, h.1, h.2⟩

/-- Given Tractarianism at `t`, an atom entails Actuality: it entails `q → w ≤ q` for
each `q`, so by Tractarianism it entails `∀q. q → w ≤ q`, and it entails itself. -/
theorem atom_le_actuality (w : Prop) (hw : Atom w) (tr : Tractarianism Prop) : Rel.le w Actuality :=
  le_of_le_of_box_imp w _ _
    (le_and_prop w w _ (le_refl_prop w) (tr w (fun q => q → Rel.le w q) (fun q => atom_le_imp_le w q hw)))
    (nec% (actuality_of_witness w))

/-- `¬A ≤ ¬¬A` says `¬A = ⊥`, that is `□A`. -/
theorem box_of_neg_le_neg_neg (A : Prop) (h : Rel.le (¬ A) (¬ ¬ A)) : □ A := by
  have h' : (¬ A) = False := eq_false_of_le_neg (¬ A) h
  show A = True
  calc A = ¬ ¬ A := (not_not_eq A).symm
    _ = ¬ False := by rw [h']
    _ = True := not_false_eq

/-- `atomicity-t-and-bf-imply-necessary-actuality` (Proposition 2.7): if Actuality is not
necessary, `¬Actuality` is not `⊥`, so by Atomicity at `t` some atom `w` lies below it;
but by BF (through Tractarianism) every atom entails Actuality; so `w ≤ ⊥`, and `w` is
not an atom. -/
theorem atomicity_t_and_bf_imply_necessary_actuality : AtomicityT → Barcan Prop → NecActuality :=
  fun at_ bf =>
    have tr : Tractarianism Prop :=
      functionality_r_implies_tractarianism_r (barcan_r_implies_functionality_r bf)
    (em (□ Actuality)).elim id fun hn =>
      (at_ (¬ Actuality)).elim
        (fun h => absurd (box_of_neg_le_neg_neg Actuality h) hn)
        (fun h => h.elim fun w hw => by
          have h1 : Rel.le w (Actuality ∧ ¬ Actuality) :=
            le_and_prop w Actuality (¬ Actuality) (atom_le_actuality w hw.1 tr) hw.2
          rw [and_not_self_eq Actuality] at h1
          exact (not_le_neg_of_atom hw.1 (le_trans_prop w False (¬ w) h1 (bot_le_prop (¬ w)))).elim)

/-- `atomicity-and-bf-imply-necessary-actuality`: only the `t` instance of Atomicity is
used. -/
theorem atomicity_and_bf_imply_necessary_actuality : Atomicity Prop → Barcan Prop → NecActuality :=
  atomicity_t_and_bf_imply_necessary_actuality

end Classicism.Proofs
