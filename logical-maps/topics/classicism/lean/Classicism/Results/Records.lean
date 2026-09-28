import Classicism.Paper
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
open Classicism.P Classicism.Paper

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
theorem classicism_implies_existence_r_at_e : Existence e := existence_e

/-- `classicism-implies-existence-r`, the instances at relational types: a theorem of
`C⁻`, whose axiom report shows Existence there costing nothing. Together with the instance
at `e` this covers every type of `R`, which is the record. -/
theorem classicism_implies_existence_r_relational {τ : Type} [Rel τ] : Existence τ := existence_rel

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
  exact intensionality X Y (fa (X ≡ Y) True ⟨fun _ => trivial, fun _ => h⟩)

/-! ### Tractarianism, Functionality and BF (Classicism, Proposition 2.1, n. 27) -/

/-- `True ≤ q` is `□q`: `q = (True ∨ q)` iff `q = True`. -/
theorem true_entails_eq_box (q : Prop) : entails True q = □ q := by
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
  have hX : X = λ x ↦ p ∨ X x := fn X (λ x ↦ p ∨ X x) h
  show (∀ x, X x) = (p ∨ ∀ x, X x)
  calc (∀ x, X x) = (∀ x, p ∨ X x) := congrArg (λ Y : σ → Prop ↦ ∀ x, Y x) hX
    _ = (p ∨ ∀ x, X x) := (or_forall_distrib_eq X p).symm

/-- `barcan-r-implies-functionality-r`: NI pointwise, BF at `σ` to box the quantifier,
then Modalized Functionality. -/
theorem barcan_r_implies_functionality_r {σ τ : Type} [Ty σ] [Rel τ] :
    Barcan σ → Functionality σ τ := by
  intro bf X Y h
  exact modalized_functionality X Y
    (bf (λ z ↦ X z = Y z) (fun z => necessity_of_identity _ _ (h z)))


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
  obtain ⟨Y, hY, hnY, hco⟩ := gec (λ x : σ ↦ x = a)
  have hYa : Y a := (hco a).1 rfl
  have hnYb : ¬ Y b := fun hb => hne ((hco b).2 hb).symm
  have hbox : □ (Y a) ∧ □ (¬ Y b) :=
    ⟨weaklyPersistent_apply (weaklyPersistent_of_persistent hY) a hYa,
     weaklyPersistent_neg_apply (weaklyPersistent_of_persistent hnY) b hnYb⟩
  have hconj : □ (Y a ∧ ¬ Y b) := by rw [box_and_eq]; exact hbox
  exact modal_K _ _ (nec% (ne_of_holds_and_not_holds Y a b)) hconj

/-- `necessary-gallin-comprehension-implies-gallin-comprehension`: `T`. -/
theorem necessary_gallin_comprehension_implies_gallin_comprehension {τ : Type} [Rel τ] :
    NecGallinExtensionalComprehension τ → GallinExtensionalComprehension τ := box_elim

/-- `necessary-gallin-comprehension-implies-necessary-nd`: the last record necessitated. -/
theorem necessary_gallin_comprehension_implies_necessary_nd {σ : Type} [Ty σ] :
    NecGallinExtensionalComprehension (σ → Prop) → NecNecessityOfDistinctness σ :=
  modal_K _ _ (nec% (gallin_comprehension_implies_nd (σ := σ)))

/-- `fregean-axiom-implies-necessary-distinctness-necessary-r`: under the Fregean Axiom
what is true is `⊤`, so necessary; apply that to each distinctness and then to ND. -/
theorem fregean_axiom_implies_necessary_distinctness_necessary_r {σ : Type} [Ty σ] :
    FregeanAxiom → NecNecessityOfDistinctness σ := fun fa =>
  have box : ∀ p : Prop, p → □ p := fun p hp => fa p True ⟨fun _ => trivial, fun _ => hp⟩
  box _ (fun x y hne => box _ hne)

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
  have hser' : Serial (λ (x : σ) (H : τ → Prop) ↦ ∃ y, H = (λ w ↦ w = y) ∧ U x y) := by
    intro x
    obtain ⟨y, hy⟩ := hser x
    exact ⟨λ w ↦ w = y, y, rfl, hy⟩
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
  (pc (λ p ↦ p)).elim fun T hT =>
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
    ∀ y, w ≤ X y → □ (w ≤ X y) := fun y h => necessity_of_identity _ _ h

/-- `actuality-implies-persistent-comprehension-r` at `σ → t` (Classicism, n. 38): with
`w` the actual world, `λy. w ≤ Xy` is persistent, since entailments are necessary when
true, and coextensive with `X`, since `w` entails exactly the truths. -/
theorem actuality_implies_persistent_comprehension_r_unary {σ : Type} [Ty σ] :
    Actuality → PersistentComprehension (σ → Prop) := fun act X =>
  act.elim fun w (hw : ActualWorld w) =>
    ⟨λ y ↦ w ≤ X y, nec% (le_apply_box w X),
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
    Actuality → ∀ X : σ → Prop, ∃ Y : σ → Prop, WeaklyInextensible Y ∧ X ≡ Y := fun act X =>
  act.elim fun w (hw : ActualWorld w) =>
    ⟨λ y ↦ w ∧ X y,
      fun Z hZ => modal_K _ _ (nec% (imp_of_w_imp w X Z))
        ((le_iff_prop _ _).1 (hw.2 _ (fun y hy => box_elim (hZ y hy)))),
      fun y => ⟨fun hX => ⟨hw.1, hX⟩, fun h => h.2⟩⟩

/-- `w → Zx` gives `∀y. w ∧ y = x → Zy`. -/
theorem profile_of_w_imp {σ : Type} [Ty σ] (w : Prop) (Z : σ → Prop) (x : σ) :
    (w → Z x) → ∀ y, w ∧ y = x → Z y := fun h y hy => hy.2 ▸ h hy.1

/-- `actuality-implies-actual-profile-r` at `σ` (Classicism, n. 36): `λy. w ∧ y = x` is
the true profile of `x`, and it entails every `Z` with `Zx`, since `w` entails `Zx`. -/
theorem actuality_implies_actual_profile_r_unary {σ : Type} [Ty σ] : Actuality → ActualProfile σ :=
  fun act x => act.elim fun w (hw : ActualWorld w) =>
    ⟨λ y ↦ w ∧ y = x, ⟨hw.1, rfl⟩, fun Z hZ =>
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
theorem glb_of_veryWeaklyRigid (X T : Prop → Prop) (hT : VeryWeaklyRigid T) (hco : X ≡ T) :
    GLB (∀ p, T p → p) X := fun V =>
  ⟨fun hlb => (le_iff_prop _ _).2 (modal_K _ _ (nec% (meet_of_forall_imp T V))
      (hT.2 (λ q ↦ V → q) (fun q hTq => (le_iff_prop _ _).1 (hlb q ((hco q).2 hTq))))),
   fun hle p hXp => (le_iff_prop _ _).2 (modal_K _ _ (modal_K _ _ (nec% (meet_imp T V p))
      ((le_iff_prop _ _).1 hle)) (weaklyPersistent_apply hT.1 p ((hco p).1 hXp)))⟩

/-- Very Weak Rigid Comprehension at `t → t` already gives Boolean Completeness at `t`:
the proof of `glb_of_veryWeaklyRigid` uses only weak persistence and weak
inextensibility. Not a record of the map. -/
theorem very_weak_rigid_comprehension_implies_boolean_completeness_t :
    VeryWeakRigidComprehension (Prop → Prop) → BooleanCompleteness Prop := fun vrc X =>
  (vrc X).elim fun T hT => ⟨∀ p, T p → p, glb_of_veryWeaklyRigid X T hT.1 hT.2⟩

/-- `weak-rigid-comprehension-r-implies-boolean-completeness-r`, at `t`. -/
theorem weak_rigid_comprehension_r_implies_boolean_completeness_r_at_t :
    WeakRigidComprehension (Prop → Prop) → BooleanCompleteness Prop := fun wrc =>
  very_weak_rigid_comprehension_implies_boolean_completeness_t
    (weak_rigid_comprehension_r_implies_very_weak_rigid_comprehension_r wrc)

/-- `rigid-comprehension-r-implies-boolean-completeness-r` (Proposition 2.8), at `t`. -/
theorem rigid_comprehension_r_implies_boolean_completeness_r_at_t :
    RigidComprehension (Prop → Prop) → BooleanCompleteness Prop := fun rc =>
  weak_rigid_comprehension_r_implies_boolean_completeness_r_at_t
    (rigid_comprehension_r_implies_weak_rigid_comprehension_r rc)

/-- Under the Fregean Axiom, `V ≤ p` is `V → p`. -/
theorem le_iff_imp_of_fregean (fa : FregeanAxiom) (V p : Prop) : V ≤ p ↔ (V → p) :=
  ⟨imp_of_le_prop V p, fun h => fa p (V ∨ p) ⟨fun hp => Or.inr hp, fun hvp => hvp.elim h id⟩⟩

/-- `extensionality-r-implies-boolean-completeness-r`, at `t` (Classicism, n. 33): under
the Fregean Axiom the order is material implication, and `∀p. Xp → p` is a greatest
lower bound of `X` outright. -/
theorem extensionality_r_implies_boolean_completeness_r_at_t :
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
theorem necessary_rigid_comprehension_r_implies_necessary_boolean_completeness_r_at_t :
    NecRigidComprehension (Prop → Prop) → NecBooleanCompleteness Prop :=
  modal_K _ _ (nec% rigid_comprehension_r_implies_boolean_completeness_r_at_t)

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
    Functional (λ z (w : Prop) ↦ (x = z ∧ w = True) ∨ (x ≠ z ∧ w = False)) := fun z =>
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

/-- `necessary-plenitude-r-implies-plenitude-r`: `T`. -/
theorem necessary_plenitude_r_implies_plenitude_r {σ τ : Type} [Ty σ] [Rel τ] :
    NecPlenitude σ τ → Plenitude σ τ := box_elim

/-- `necessary-plenitude-r-implies-necessary-distinctness-necessary-r`: Proposition 2.13
necessitated. -/
theorem necessary_plenitude_r_implies_necessary_distinctness_necessary_r {σ : Type} [Ty σ] :
    NecPlenitude σ Prop → NecNecessityOfDistinctness σ :=
  modal_K _ _ (nec% (plenitude_r_implies_distinctness_necessary_r (σ := σ)))

/-- `necessary-plenitude-r-implies-necessary-actuality`: Proposition 2.15 necessitated. -/
theorem necessary_plenitude_r_implies_necessary_actuality :
    NecPlenitude Prop Prop → NecActuality :=
  modal_K _ _ (nec% plenitude_r_implies_actuality)

/-- `functional-choice-r-implies-plenitude-r`: a functional relation is serial. -/
theorem functional_choice_r_implies_plenitude_r {σ τ : Type} [Ty σ] [Rel τ] :
    FunctionalChoice σ τ → Plenitude σ τ :=
  fun fc U hU => fc U (fun x => (hU x).elim fun y hy => ⟨y, hy.1⟩)

/-! Atomicity and BF imply `□`Actuality (Classicism, Proposition 2.7). -/

/-- An atom `w` entails `q → w ≤ q`, for every `q`: if `w ≤ q`, then `w ≤ q` is
necessary, so `q → w ≤ q` is `⊤`; if `w ≤ ¬q`, then `w ≤ ¬q ∨ r` for any `r`. -/
theorem atom_le_imp_le (w q : Prop) (hw : Atom w) : w ≤ (q → w ≤ q) :=
  (atom_le_or_le_neg w q hw).elim
    (fun h => by
      rw [show (w ≤ q) = True from box_le_prop w q h, imp_true_eq]
      exact le_top_prop w)
    (fun h => by
      rw [imp_eq_not_or q (w ≤ q)]
      exact le_or_of_le_left_prop w (¬ q) _ h)

/-- `(p → q) → (q → r) → p → r`. -/
theorem imp_trans_aux (p q r : Prop) : (p → q) → (q → r) → p → r := fun h₁ h₂ hp => h₂ (h₁ hp)

/-- `p ≤ q` and `□(q → r)` give `p ≤ r`. -/
theorem le_of_le_of_box_imp (p q r : Prop) (h : p ≤ q) (hb : □ (q → r)) : p ≤ r :=
  (le_iff_prop _ _).2 (modal_K _ _ (modal_K _ _ (nec% (imp_trans_aux p q r)) ((le_iff_prop _ _).1 h)) hb)

/-- `w ∧ ∀q. q → w ≤ q` gives Actuality, with `w` as witness. -/
theorem actuality_of_witness (w : Prop) : ActualWorld w → Actuality := fun h => ⟨w, h.1, h.2⟩

/-- Given Tractarianism at `t`, an atom entails Actuality: it entails `q → w ≤ q` for
each `q`, so by Tractarianism it entails `∀q. q → w ≤ q`, and it entails itself. -/
theorem atom_le_actuality (w : Prop) (hw : Atom w) (tr : Tractarianism Prop) : w ≤ Actuality :=
  le_of_le_of_box_imp w _ _
    (le_and_prop w w _ (le_refl_prop w) (tr w (λ q ↦ q → w ≤ q) (fun q => atom_le_imp_le w q hw)))
    (nec% (actuality_of_witness w))

/-- `¬A ≤ ¬¬A` says `¬A = ⊥`, that is `□A`. -/
theorem box_of_neg_le_neg_neg (A : Prop) (h : (¬ A) ≤ (¬ ¬ A)) : □ A := by
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
          have h1 : w ≤ (Actuality ∧ ¬ Actuality) :=
            le_and_prop w Actuality (¬ Actuality) (atom_le_actuality w hw.1 tr) hw.2
          rw [and_not_self_eq Actuality] at h1
          exact (not_le_neg_of_atom hw.1 (le_trans_prop w False (¬ w) h1 (bot_le_prop (¬ w)))).elim)

/-- `atomicity-and-bf-imply-necessary-actuality`: only the `t` instance of Atomicity is
used. -/
theorem atomicity_and_bf_imply_necessary_actuality : Atomicity Prop → Barcan Prop → NecActuality :=
  atomicity_t_and_bf_imply_necessary_actuality

/-! ### `C5`: `□ND` at `t` (Classicism, §§2.1–2.3)

`C5` is `C` with `□ND`, equivalently `□5` or `□B` (Proposition 2.2). The records below take
`□ND_t` (`NecNecessityOfDistinctnessT`) as the `C5` premise: from `ND_t`, `B` follows
(`modal_five_implies_modal_b`), and from `B`, `ND` at every type (Prior); so `□ND_t`
gives `B`, `□B`, and `ND`, `□ND` at every type. Helper lemmas are stated unfolded, so
that the audits do not read them as records. -/

/-- `ND_t` gives `B`. -/
theorem b_of_nd_t : (∀ x y : Prop, x ≠ y → □ (x ≠ y)) → ∀ p : Prop, p → □ ◇ p :=
  fun nd => modal_five_implies_modal_b (distinctness_necessary_t_implies_modal_five nd)

/-- `□ND_t` gives `□B`. -/
theorem box_b_of_box_nd_t :
    □ (∀ x y : Prop, x ≠ y → □ (x ≠ y)) → □ (∀ p : Prop, p → □ ◇ p) :=
  modal_K _ _ (nec% b_of_nd_t)

/-- `◇∀x. Xx → ∀x. ◇Xx`: were some `Xx` identical to `⊥`, so would `∀x. Xx` be. -/
theorem dia_forall_imp {σ : Type} [Ty σ] (X : σ → Prop) : ◇ (∀ x, X x) → ∀ x, ◇ (X x) :=
  fun hd x hx => hd (calc (∀ u, X u) = (X x ∧ ∀ u, X u) := (and_forall_absorb_eq X x).symm
      _ = (False ∧ ∀ u, X u) := by rw [hx]
      _ = False := false_and_eq _)

/-- `◇¬p` is `¬□p`. -/
theorem dia_not_eq (p : Prop) : (◇ (¬ p)) = ¬ □ p := by
  rw [dia_eq_not_box_not, not_not_eq]

/-- With `B`, `◇□p → p`: otherwise `¬p`, so `□◇¬p` by `B`, which is `□¬□p`, and `□p` is
`⊥`, against `◇□p`. -/
theorem b_dia_box_imp : (∀ p : Prop, p → □ ◇ p) → ∀ p : Prop, ◇ □ p → p := fun b p hd =>
  (em p).elim id fun hn => by
    have h1 : (◇ (¬ p)) = True := b (¬ p) hn
    have h3 : (□ p) = False :=
      calc (□ p) = ¬ ¬ □ p := (not_not_eq _).symm
        _ = ¬ True := by rw [← dia_not_eq, h1]
        _ = False := not_true_eq
    exact (hd h3).elim

/-- `∀x. ◇□Fx → Fx`, from `B`. -/
theorem b_forall_dia_box_imp {σ : Type} [Ty σ] (F : σ → Prop) :
    (∀ p : Prop, p → □ ◇ p) → ∀ x, ◇ □ (F x) → F x := fun b x => b_dia_box_imp b (F x)

/-- `G ⊆ F` and `∀x. Gx` give `∀x. Fx`. -/
theorem forall_imp_forall {σ : Type} [Ty σ] (G F : σ → Prop) :
    G ⊆ F → (∀ x, G x) → ∀ x, F x := fun h g x => h x (g x)

/-- `necessary-nd-implies-bf` (Proposition 2.3; Prior, and the
proof Prior attributes to Lemmon): from `∀x. □Fx`, `B` gives `□◇∀x. □Fx`; inside the box
`◇∀ → ∀◇` gives `∀x. ◇□Fx`, and the necessitation of `B` in the form `◇□p → p` gives
`∀x. Fx`. -/
theorem necessary_nd_implies_bf {σ : Type} [Ty σ] :
    NecNecessityOfDistinctness Prop → Barcan σ := fun hnd F hF =>
  have hb : ∀ p : Prop, p → □ ◇ p := b_of_nd_t (box_elim hnd)
  have h1 : □ (∀ x, ◇ □ (F x)) :=
    modal_K _ _ (nec% (dia_forall_imp (λ x ↦ □ (F x)))) (hb _ hF)
  have h2 : □ (∀ x, ◇ □ (F x) → F x) :=
    modal_K _ _ (nec% (b_forall_dia_box_imp F)) (box_b_of_box_nd_t hnd)
  modal_K _ _ (modal_K _ _ (nec% (forall_imp_forall (λ x ↦ ◇ □ (F x)) F)) h2) h1

/-- `necessary-distinctness-necessary-t-implies-distinctness-necessary-r`: `B`, then
Prior's argument. -/
theorem necessary_distinctness_necessary_t_implies_distinctness_necessary_r {σ : Type} [Ty σ] :
    NecNecessityOfDistinctnessT → NecessityOfDistinctness σ := fun hnd =>
  modal_b_implies_distinctness_necessary_r (b_of_nd_t (box_elim hnd))

/-- `ND_t` gives `ND` at `σ`, unfolded, for necessitation. -/
theorem nd_of_nd_t {σ : Type} [Ty σ] :
    (∀ x y : Prop, x ≠ y → □ (x ≠ y)) → ∀ x y : σ, x ≠ y → □ (x ≠ y) := fun nd =>
  modal_b_implies_distinctness_necessary_r (b_of_nd_t nd)

/-- `necessary-distinctness-necessary-t-implies-necessary-distinctness-necessary-r`: the
last record necessitated. -/
theorem necessary_distinctness_necessary_t_implies_necessary_distinctness_necessary_r
    {σ : Type} [Ty σ] : NecNecessityOfDistinctnessT → NecNecessityOfDistinctness σ :=
  modal_K _ _ (nec% (nd_of_nd_t (σ := σ)))

/-- `□ND_t` gives `BF` at `σ`, unfolded, for necessitation. -/
theorem bf_of_box_nd_t {σ : Type} [Ty σ] :
    □ (∀ x y : Prop, x ≠ y → □ (x ≠ y)) → ∀ X : σ → Prop, (∀ x, □ (X x)) → □ (∀ x, X x) :=
  necessary_nd_implies_bf

/-- `necessary-distinctness-necessary-r-implies-necessary-barcan-r`: Proposition 2.3
necessitated, with `4`. -/
theorem necessary_distinctness_necessary_r_implies_necessary_barcan_r {σ : Type} [Ty σ] :
    NecNecessityOfDistinctness Prop → NecBarcan σ := fun hnd =>
  modal_K _ _ (nec% (bf_of_box_nd_t (σ := σ))) (modal_four _ hnd)

/-- `x = y` makes anything follow from `x ≠ y`. -/
theorem eq_imp_ne_imp {σ : Type} [Ty σ] (x y : σ) (q : Prop) : x = y → x ≠ y → q :=
  fun h hne => (hne h).elim

/-- `q` gives `p → q`. -/
theorem imp_intro' (p q : Prop) : q → p → q := fun hq _ => hq

/-- With `ND` at `σ`, each instance of `ND` is necessary: if `x = y`, `NI` makes the
antecedent necessarily false; if not, `ND` and `4` make the consequent necessary. -/
theorem box_nd_instance {σ : Type} [Ty σ] (nd : ∀ x y : σ, x ≠ y → □ (x ≠ y)) (x y : σ) :
    □ (x ≠ y → □ (x ≠ y)) :=
  (em (x = y)).elim
    (fun h => modal_K _ _ (nec% (eq_imp_ne_imp x y (□ (x ≠ y)))) (necessity_of_identity x y h))
    (fun h => modal_K _ _ (nec% (imp_intro' (x ≠ y) (□ (x ≠ y)))) (modal_four _ (nd x y h)))

/-- `nd-and-bf-imply-necessary-nd`
(Proposition 2.4): each instance of `ND` is necessary, and `BF`, twice, boxes the two
quantifiers. -/
theorem nd_and_bf_imply_necessary_nd
    {σ : Type} [Ty σ] : NecessityOfDistinctness σ → Barcan σ → NecNecessityOfDistinctness σ :=
  fun nd bf => bf (λ x ↦ ∀ y, x ≠ y → □ (x ≠ y))
    (fun x => bf (λ y ↦ x ≠ y → □ (x ≠ y)) (fun y => box_nd_instance nd x y))

/-- `distinctness-necessary-t-and-barcan-t-imply-necessary-distinctness-necessary-t`
(Proposition 2.4 at `t`). -/
theorem distinctness_necessary_t_and_barcan_t_imply_necessary_distinctness_necessary_t :
    NecessityOfDistinctnessT → BarcanT → NecNecessityOfDistinctnessT :=
  nd_and_bf_imply_necessary_nd

/-! In `C5` persistence is inextensibility (Classicism, n. 41). -/

/-- `◇¬q` and `q → □q` give `¬q`. -/
theorem not_of_dia_not_of_persist (q : Prop) : ◇ (¬ q) → (q → □ q) → ¬ q := fun hd hp hq => by
  rw [dia_not_eq] at hd
  exact hd (hp hq)

/-- `□¬q` gives `□(q → r)`. -/
theorem box_imp_of_box_not (q r : Prop) : □ (¬ q) → □ (q → r) :=
  modal_K _ _ (nec% (fun (hn : ¬ q) (hq : q) => (hn hq).elim : ¬ q → q → r))

/-- `□r` gives `□(q → r)`. -/
theorem box_imp_of_box (q r : Prop) : □ r → □ (q → r) :=
  modal_K _ _ (nec% (imp_intro' q r))

/-- With `B` and `BF` at `σ`, a persistent property is weakly inextensible (n. 41): if
`∀z. Yz → □Zz`, then for each `z`, either `Yz`, and `□Zz`, or `¬Yz`, and `B` with
persistence make `□¬Yz`; either way `□(Yz → Zz)`, and `BF` boxes the quantifier. -/
theorem weaklyInextensible_of_persistent_b_bf {σ : Type} [Ty σ] (Y : σ → Prop) :
    (∀ p : Prop, p → □ ◇ p) → (∀ X : σ → Prop, (∀ x, □ (X x)) → □ (∀ x, X x)) →
      Persistent Y → WeaklyInextensible Y := fun b bf hP Z hZ =>
  bf (λ z ↦ Y z → Z z) fun z =>
    (em (Y z)).elim
      (fun hy => box_imp_of_box (Y z) (Z z) (hZ z hy))
      (fun hn => box_imp_of_box_not (Y z) (Z z)
        (modal_K _ _ (modal_K _ _ (nec% (not_of_dia_not_of_persist (Y z))) (b _ hn))
          (converse_barcan (λ z ↦ Y z → □ (Y z)) hP z)))

/-- In `C5` a persistent property is inextensible: the last lemma necessitated, with `□B`,
`□BF` and `4` for persistence. -/
theorem inextensible_of_persistent_c5 {σ : Type} [Ty σ]
    (hnd : □ (∀ x y : Prop, x ≠ y → □ (x ≠ y))) (Y : σ → Prop) (hP : Persistent Y) :
    Inextensible Y :=
  modal_K _ _ (modal_K _ _ (modal_K _ _ (nec% (weaklyInextensible_of_persistent_b_bf Y))
    (box_b_of_box_nd_t hnd)) (necessary_distinctness_necessary_r_implies_necessary_barcan_r hnd))
    (modal_four _ hP)

/-- `c5-and-actuality-imply-rigid-comprehension` (for relations of type `σ → t` only)
(Proposition 2.10), at `σ → t`: Actuality gives a persistent coextension,
`λy. w ≤ Xy` (n. 38), and in `C5` it is inextensible. -/
theorem c5_and_actuality_imply_rigid_comprehension_unary
    {σ : Type} [Ty σ] :
    Actuality → NecNecessityOfDistinctness Prop → RigidComprehension (σ → Prop) := fun act hnd X =>
  (actuality_implies_persistent_comprehension_r_unary act X).elim fun Y hY =>
    ⟨Y, ⟨hY.1, inextensible_of_persistent_c5 hnd Y hY.1⟩, hY.2⟩

/-- `c5-and-actuality-imply-completeness` (at type `t` only)
(Proposition 2.5, right to left), at `t`: Propositions 2.10 and 2.8. -/
theorem c5_and_actuality_imply_completeness_at_t :
    Actuality → NecNecessityOfDistinctness Prop → BooleanCompleteness Prop := fun act hnd =>
  rigid_comprehension_r_implies_boolean_completeness_r_at_t
    (c5_and_actuality_imply_rigid_comprehension_unary act hnd)

/-! Boolean Completeness gives Plenitude in `C5` (Proposition 2.14, n. 48). For `R`
functional, let `F_R X := ∀y p. Ryp → Xy ≤ p`, and `G` the greatest lower bound of the
upper bounds of `F_R`, which is its least upper bound. At each `a`, with `Ra pₐ`: the
property `λx. x = a ∧ pₐ` satisfies `F_R` (by `ND`), so it is below `G`, and `pₐ ≤ Ga`;
and `λx. x ≠ a ∨ pₐ` is an upper bound of `F_R` (by `ND` and `BF`), so `G` is below it,
and `Ga ≤ pₐ`. -/

/-- `X ≤ Y` at `σ → t` gives `Xa ≤ Ya`. -/
theorem le_apply_of_le {σ : Type} [Ty σ] (X Y : σ → Prop) (a : σ) (h : X ≤ Y) :
    X a ≤ Y a :=
  (le_iff_prop _ _).2 (converse_barcan (λ z ↦ X z → Y z) ((le_iff X Y).1 h) a)

/-- `G ≤ G` at `σ → t`. -/
theorem le_refl_arrow_prop {σ : Type} [Ty σ] (G : σ → Prop) : G ≤ G :=
  (le_iff G G).2 (nec% (fun (z : σ) (h : G z) => h))

/-- A greatest lower bound of the upper bounds of `F` is an upper bound of `F`. -/
theorem glb_ub_upper {σ : Type} [Ty σ] (F : (σ → Prop) → Prop) (G : σ → Prop)
    (hG : GLB G (λ w ↦ UB w F)) : UB G F :=
  fun X hX => (hG X).1 (fun _ hY => hY X hX)

/-- And below every upper bound. -/
theorem glb_ub_least {σ : Type} [Ty σ] (F : (σ → Prop) → Prop) (G : σ → Prop)
    (hG : GLB G (λ w ↦ UB w F)) : ∀ Y : σ → Prop, UB Y F → G ≤ Y :=
  fun Y hY => (hG G).2 (le_refl_arrow_prop G) Y hY

/-- `y ≠ a` refutes `y = a ∧ p`. -/
theorem ne_imp_and_imp {σ : Type} [Ty σ] (y a : σ) (p q : Prop) : y ≠ a → (y = a ∧ p) → q :=
  fun hne h => (hne h.1).elim

/-- `λx. x = a ∧ pₐ` satisfies `F_R`, given `ND`. -/
theorem haec_and_le {σ : Type} [Ty σ] (nd : ∀ x y : σ, x ≠ y → □ (x ≠ y))
    (R : σ → Prop → Prop) (a : σ) (pa : Prop) (huniq : ∀ z, R a z → pa = z) :
    ∀ y p, R y p → (y = a ∧ pa) ≤ p := fun y p hRy =>
  (em (y = a)).elim
    (fun h => by
      rw [h] at hRy ⊢
      rw [← huniq p hRy]
      exact and_le_right_prop (a = a) pa)
    (fun h => (le_iff_prop _ _).2 (modal_K _ _ (nec% (ne_imp_and_imp y a pa p)) (nd y a h)))

/-- So `pₐ ≤ Ga`. -/
theorem pa_le_of {σ : Type} [Ty σ] (a : σ) (pa : Prop) (G : σ → Prop)
    (h : (λ x ↦ x = a ∧ pa) ≤ G) : pa ≤ G a :=
  le_trans_prop pa (a = a ∧ pa) (G a)
    (le_and_prop pa (a = a) pa ((le_iff_prop _ _).2 (nec% (fun (_ : pa) => (rfl : a = a))))
      (le_refl_prop pa))
    (le_apply_of_le _ G a h)

/-- `(q → p) → q → r ∨ p`. -/
theorem imp_or_right' (q p r : Prop) : (q → p) → q → r ∨ p := fun h hq => Or.inr (h hq)

/-- `r → q → r ∨ p`. -/
theorem imp_or_left' (r q p : Prop) : r → q → r ∨ p := fun h _ => Or.inl h

/-- `λx. x ≠ a ∨ pₐ` is an upper bound of `F_R`, given `ND` and `BF`. -/
theorem ne_or_ub {σ : Type} [Ty σ] (nd : ∀ x y : σ, x ≠ y → □ (x ≠ y))
    (bf : ∀ X : σ → Prop, (∀ x, □ (X x)) → □ (∀ x, X x))
    (R : σ → Prop → Prop) (a : σ) (pa : Prop) (hRa : R a pa) :
    ∀ X : σ → Prop, (∀ y p, R y p → X y ≤ p) → X ≤ (λ x ↦ x ≠ a ∨ pa) :=
  fun X hX => (le_iff X _).2 (bf (λ x ↦ X x → x ≠ a ∨ pa) fun x =>
    (em (x = a)).elim
      (fun h => by
        rw [h]
        exact modal_K _ _ (nec% (imp_or_right' (X a) pa (a ≠ a))) ((le_iff_prop _ _).1 (hX a pa hRa)))
      (fun h => modal_K _ _ (nec% (imp_or_left' (x ≠ a) (X x) pa)) (nd x a h)))

/-- `a ≠ a ∨ p` gives `p`. -/
theorem ne_self_or_imp {σ : Type} [Ty σ] (a : σ) (p : Prop) : (a ≠ a ∨ p) → p :=
  fun h => h.elim (fun hne => (hne rfl).elim) id

/-- So `Ga ≤ pₐ`. -/
theorem ga_le_of {σ : Type} [Ty σ] (a : σ) (pa : Prop) (G : σ → Prop)
    (h : G ≤ (λ x ↦ x ≠ a ∨ pa)) : G a ≤ pa :=
  le_trans_prop (G a) (a ≠ a ∨ pa) pa (le_apply_of_le G _ a h)
    ((le_iff_prop _ _).2 (nec% (ne_self_or_imp a pa)))

/-- `c5-and-completeness-imply-plenitude` (for output type `t` only)
(Proposition 2.14), for relations of type `σ → t → t`: Boolean Completeness at `σ → t`
gives the least upper bound `G` of `F_R`, and `Ga = pₐ` at every `a`. -/
theorem c5_and_completeness_imply_plenitude_at_t
    {σ : Type} [Ty σ] :
    BooleanCompleteness (σ → Prop) → NecNecessityOfDistinctness Prop → Plenitude σ Prop :=
  fun bc hnd R hR =>
    have nd := nd_of_nd_t (σ := σ) (box_elim hnd)
    have bf := bf_of_box_nd_t (σ := σ) hnd
    (bc (λ Y ↦ UB Y (λ X ↦ ∀ y p, R y p → X y ≤ p))).elim fun G hG =>
      ⟨G, fun a => (hR a).elim fun pa hpa =>
        have e : pa = G a := le_antisymm_prop pa (G a)
          (pa_le_of a pa G (glb_ub_upper _ G hG _ (haec_and_le nd R a pa hpa.2)))
          (ga_le_of a pa G (glb_ub_least _ G hG _ (ne_or_ub nd bf R a pa hpa.1)))
        e ▸ hpa.1⟩

/-- `c5-and-completeness-imply-actuality`
(Proposition 2.5, left to right): Boolean Completeness at `t → t` gives Plenitude at
`t → t` (Proposition 2.14), and Plenitude gives Actuality (Proposition 2.15). -/
theorem c5_and_completeness_imply_actuality :
    BooleanCompleteness (Prop → Prop) → NecNecessityOfDistinctness Prop → Actuality := fun bc hnd =>
  plenitude_r_implies_actuality
    (c5_and_completeness_imply_plenitude_at_t bc hnd)

/-! Atomicity is `□`Actuality and `□`Boolean Completeness in `C5` (Proposition 2.6). -/

/-- `atomicity-t-and-necessary-distinctness-necessary-t-imply-necessary-actuality`
(Proposition 2.6, left to right): Proposition 2.7, with `BF_t` from Proposition 2.3. -/
theorem atomicity_t_and_necessary_distinctness_necessary_t_imply_necessary_actuality :
    AtomicityT → NecNecessityOfDistinctnessT → NecActuality := fun at_ hnd =>
  atomicity_t_and_bf_imply_necessary_actuality at_
    (necessary_nd_implies_bf hnd)

/-- Actuality and `□ND_t` give Boolean Completeness at `t`, unfolded, for necessitation. -/
theorem bc_of_actuality_box_nd_t :
    Actuality → □ (∀ x y : Prop, x ≠ y → □ (x ≠ y)) → BooleanCompleteness Prop :=
  c5_and_actuality_imply_completeness_at_t

/-- `necessary-actuality-and-necessary-distinctness-necessary-t-imply-necessary-boolean-completeness-r`,
at `t`: Proposition 2.5 necessitated, with `4`. -/
theorem necessary_actuality_and_necessary_distinctness_necessary_t_imply_necessary_boolean_completeness_r :
    NecActuality → NecNecessityOfDistinctnessT → NecBooleanCompleteness Prop := fun hna hnd =>
  modal_K _ _ (modal_K _ _ (nec% bc_of_actuality_box_nd_t) hna) (modal_four _ hnd)

/-- `c5-and-atomicity-imply-necessary-completeness` (at type `t` only)
(Proposition 2.6), at `t`. -/
theorem c5_and_atomicity_imply_necessary_completeness_at_t :
    Atomicity Prop → NecNecessityOfDistinctness Prop → NecBooleanCompleteness Prop := fun at_ hnd =>
  necessary_actuality_and_necessary_distinctness_necessary_t_imply_necessary_boolean_completeness_r
    (atomicity_t_and_necessary_distinctness_necessary_t_imply_necessary_actuality at_ hnd) hnd

/-- `◇p` and `□q` give `◇(p ∧ q)`. -/
theorem dia_and_of_dia_box (p q : Prop) : ◇ p → □ q → ◇ (p ∧ q) := fun hp hq h =>
  hp (calc p = (p ∧ True) := (and_true_eq p).symm
    _ = (p ∧ q) := by rw [hq]
    _ = False := h)

/-- `□(p → q)` and `◇p` give `◇q`. -/
theorem contra_imp (p q : Prop) : (p → q) → ¬ q → ¬ p := fun h hq hp => hq (h hp)

theorem dia_mono (p q : Prop) : □ (p → q) → ◇ p → ◇ q := fun h hp hq =>
  hp ((box_not_eq p).mp
    (modal_K _ _ (modal_K _ _ (nec% (contra_imp p q)) h) ((box_not_eq q).mpr hq)))

/-- `◇(p ∨ q)` gives `◇p ∨ ◇q`. -/
theorem dia_or (p q : Prop) : ◇ (p ∨ q) → ◇ p ∨ ◇ q := fun h =>
  (em (◇ p)).elim Or.inl fun hp => (em (◇ q)).elim Or.inr fun hq =>
    (h (by
      have hp' : p = False := (not_not_eq _).mp hp
      have hq' : q = False := (not_not_eq _).mp hq
      rw [hp', hq', or_self_eq])).elim

/-- With `BF`, `◇∃x. φx` gives `∃x. ◇φx`: otherwise `∀x. □¬φx`, so `□∀x. ¬φx`, which is
`□¬∃x. φx`. -/
theorem dia_exists_of_bf {σ : Type} [Ty σ] (bf : ∀ X : σ → Prop, (∀ x, □ (X x)) → □ (∀ x, X x))
    (φ : σ → Prop) : ◇ (∃ x, φ x) → ∃ x, ◇ (φ x) := fun hd =>
  (em (∃ x, ◇ (φ x))).elim id fun hn => by
    have h1 : ∀ x, □ (¬ φ x) := fun x => by
      rw [box_not_eq_not_dia]; exact fun h => hn ⟨x, h⟩
    have h2 : □ (¬ ∃ x, φ x) := by
      rw [not_exists_eq]; exact bf _ h1
    rw [box_not_eq_not_dia] at h2
    exact (h2 hd).elim

/-- With `ND`, an identity that is possible is true. -/
theorem eq_of_dia_eq {σ : Type} [Ty σ] (nd : ∀ x y : σ, x ≠ y → □ (x ≠ y)) (a b : σ) :
    ◇ (a = b) → a = b := fun hd =>
  (em (a = b)).elim id fun hne => by
    have h : □ (a ≠ b) := nd a b hne
    have h' : (a = b) = False := by
      rw [← box_not_eq]; exact h
    exact (hd h').elim

/-- The actual world, inside the diamond: `x ∧ w ∧ ∀q. q → w ≤ q` gives `w ≤ x`. -/
theorem le_of_actual_and (x w : Prop) : (x ∧ ActualWorld w) → w ≤ x :=
  fun h => h.2.2 x h.1

/-- A true proposition entailing every truth is non-bottom and decides every proposition. -/
theorem decides_of_actual (x w : Prop) :
    (x ∧ ActualWorld w) → (¬ (w = False) ∧ ∀ z, w ≤ z ∨ w ≤ ¬ z) :=
  fun h => ⟨fun e => e ▸ h.2.1, fun z => (em z).elim (fun hz => Or.inl (h.2.2 z hz))
    (fun hz => Or.inr (h.2.2 (¬ z) hz))⟩

/-- A non-bottom proposition deciding every proposition is an atom. -/
theorem atom_of_decides (w : Prop) (h : ¬ (w = False) ∧ ∀ z, w ≤ z ∨ w ≤ ¬ z) : Atom w :=
  fun z => ⟨fun hz => (h.2 z).elim
      (fun hwz => absurd (le_antisymm_prop z w hz.1 hwz) hz.2)
      (fun hwn => le_trans_prop z w (¬ z) hz.1 hwn),
    fun hz => by
      have hz0 : z = False := eq_false_of_le_neg z hz
      exact ⟨hz0 ▸ bot_le_prop w, fun e => h.1 (e ▸ hz0)⟩⟩

/-- With `ND_t`, a proposition possibly non-bottom and possibly deciding everything is so. -/
theorem decides_of_dia (nd : ∀ x y : Prop, x ≠ y → □ (x ≠ y)) (w : Prop) :
    ◇ (¬ (w = False) ∧ ∀ z, w ≤ z ∨ w ≤ ¬ z) →
      (¬ (w = False) ∧ ∀ z, w ≤ z ∨ w ≤ ¬ z) := fun hd =>
  ⟨ne_of_dia_ne w False (dia_mono _ _ (nec% (fun (h : ¬ (w = False) ∧ ∀ z, w ≤ z ∨ w ≤ ¬ z) => h.1)) hd),
   fun z => (dia_or _ _ (dia_forall_imp (λ z ↦ w ≤ z ∨ w ≤ ¬ z)
      (dia_mono _ _ (nec% (fun (h : ¬ (w = False) ∧ ∀ z, w ≤ z ∨ w ≤ ¬ z) => h.2)) hd) z)).elim
     (fun h => Or.inl (eq_of_dia_eq nd _ _ h)) (fun h => Or.inr (eq_of_dia_eq nd _ _ h))⟩

/-- `x ∧ Actuality` is `∃w. x ∧ (w ∧ ∀q. q → w ≤ q)`. -/
theorem and_actuality_eq (x : Prop) :
    (x ∧ ∃ w : Prop, w ∧ ∀ q, q → w ≤ q) = ∃ w : Prop, x ∧ (w ∧ ∀ q, q → w ≤ q) :=
  and_exists_distrib_eq _ x

/-- `c5-and-necessary-actuality-imply-atomicity` (at type `t` only)
(Proposition 2.6, right to left, through `□`Actuality): a non-bottom `x` is compatible
with Actuality; by `BF` some `w` is possibly true with `x` and an actual world; then
`w ≤ x` is possible, hence true by `ND`; and `w`, possibly non-bottom and deciding every
proposition, is so, by `ND`, hence an atom. -/
theorem c5_and_necessary_actuality_imply_atomicity_at_t :
    NecActuality → NecNecessityOfDistinctness Prop → Atomicity Prop := fun hna hnd x =>
  have nd : ∀ x y : Prop, x ≠ y → □ (x ≠ y) := box_elim hnd
  have bf := bf_of_box_nd_t (σ := Prop) hnd
  (em (x = False)).elim (fun h => Or.inl (le_neg_of_eq_false x h)) fun hx => Or.inr (by
    have h1 : ◇ (x ∧ Actuality) := dia_and_of_dia_box x Actuality hx hna
    have h2 : ◇ (∃ w : Prop, x ∧ (w ∧ ∀ q, q → w ≤ q)) := by
      rw [← and_actuality_eq]; exact h1
    obtain ⟨w, hw⟩ := dia_exists_of_bf bf _ h2
    exact ⟨w, atom_of_decides w (decides_of_dia nd w (dia_mono _ _ (nec% (decides_of_actual x w)) hw)),
      eq_of_dia_eq nd _ _ (dia_mono _ _ (nec% (le_of_actual_and x w)) hw)⟩)

/-- Boolean Completeness at `t → t` and `□ND_t` give Actuality, unfolded, for necessitation. -/
theorem actuality_of_bc_box_nd_t :
    BooleanCompleteness (Prop → Prop) → □ (∀ x y : Prop, x ≠ y → □ (x ≠ y)) → Actuality :=
  c5_and_completeness_imply_actuality

/-- `necessary-boolean-completeness-r-and-necessary-distinctness-necessary-t-imply-necessary-actuality`:
Proposition 2.5 necessitated. -/
theorem necessary_boolean_completeness_r_and_necessary_distinctness_necessary_t_imply_necessary_actuality :
    NecBooleanCompleteness (Prop → Prop) → NecNecessityOfDistinctnessT → NecActuality := fun hnb hnd =>
  modal_K _ _ (modal_K _ _ (nec% actuality_of_bc_box_nd_t) hnb) (modal_four _ hnd)

/-- `c5-and-necessary-completeness-imply-atomicity` (at type `t` only)
(Proposition 2.6, right to left). -/
theorem c5_and_necessary_completeness_imply_atomicity_at_t :
    NecBooleanCompleteness (Prop → Prop) → NecNecessityOfDistinctness Prop → Atomicity Prop := fun hnb hnd =>
  c5_and_necessary_actuality_imply_atomicity_at_t
    (necessary_boolean_completeness_r_and_necessary_distinctness_necessary_t_imply_necessary_actuality hnb hnd) hnd

/-- Actuality and `□ND_t` give Rigid Comprehension at `σ → t`, unfolded, for necessitation. -/
theorem rc_of_actuality_box_nd_t {σ : Type} [Ty σ] :
    Actuality → □ (∀ x y : Prop, x ≠ y → □ (x ≠ y)) → RigidComprehension (σ → Prop) :=
  c5_and_actuality_imply_rigid_comprehension_unary

/-- `c5-and-atomicity-imply-necessary-rigid-comprehension` (for relations of type `σ → t` only)
(Classicism, §2.3: `C5` + Atomicity = `C5` + `□`Rigid Comprehension), at `σ → t`:
`□`Actuality, and Proposition 2.10 necessitated. The converse is
`necessary_rigid_comprehension_r_implies_necessary_actuality` with the last record. -/
theorem c5_and_atomicity_imply_necessary_rigid_comprehension_unary
    {σ : Type} [Ty σ] :
    Atomicity Prop → NecNecessityOfDistinctness Prop → NecRigidComprehension (σ → Prop) := fun at_ hnd =>
  modal_K _ _ (modal_K _ _ (nec% (rc_of_actuality_box_nd_t (σ := σ)))
    (atomicity_t_and_necessary_distinctness_necessary_t_imply_necessary_actuality at_ hnd))
    (modal_four _ hnd)

/-- `necessary-rigid-comprehension-r-and-necessary-distinctness-necessary-t-imply-atomicity-t`:
`□`Rigid Comprehension at `t → t` gives `□`Actuality (Proposition 2.9 necessitated), and
`C5` then gives Atomicity. -/
theorem necessary_rigid_comprehension_r_and_necessary_distinctness_necessary_t_imply_atomicity_t :
    NecRigidComprehension (Prop → Prop) → NecNecessityOfDistinctnessT → AtomicityT := fun hrc hnd =>
  c5_and_necessary_actuality_imply_atomicity_at_t
    (necessary_rigid_comprehension_r_implies_necessary_actuality hrc) hnd

/-! Rigid Comprehension and `BF` give `□BF` (Proposition 2.12, n. 43); Rigid Comprehension
and `ND` give Plenitude (Proposition 2.16, n. 49). -/

/-- Inside the box: weak inextensibility of `F` and `□∀x. Fx` give `BF`. -/
theorem bf_of_weaklyInextensible {σ : Type} [Ty σ] (F : σ → Prop) :
    WeaklyInextensible F → □ (∀ x, F x) → ∀ Y : σ → Prop, (∀ x, □ (Y x)) → □ (∀ x, Y x) :=
  fun hI hall Y hY =>
    modal_K _ _ (modal_K _ _ (nec% (forall_imp_forall F Y)) (hI Y (fun z _ => hY z))) hall

/-- `rigid-comprehension-and-bf-imply-necessary-bf` (Proposition 2.12): a
rigid `F` coextensive with self-identity holds necessarily of everything, so by `BF`
`□∀x. Fx`; its inextensibility, necessitated, then gives `BF` in every world. -/
theorem rigid_comprehension_and_bf_imply_necessary_bf {σ : Type} [Ty σ] :
    RigidComprehension (σ → Prop) → Barcan σ → NecBarcan σ := fun rc bf =>
  (rc (λ x ↦ x = x)).elim fun F hF =>
    have hall : □ (∀ x, F x) :=
      bf F (fun x => weaklyPersistent_apply (weaklyPersistent_of_persistent hF.1.1) x ((hF.2 x).1 rfl))
    modal_K _ _ (modal_K _ _ (nec% (bf_of_weaklyInextensible F)) hF.1.2) (modal_four _ hall)

/-- `Rs x q → Z x → q`, for `Z := λy. ∀p. Rs y p → p`. -/
theorem z_imp_of_rs {σ : Type} [Ty σ] (Rs : σ → Prop → Prop) (x : σ) (q : Prop) :
    Rs x q → (∀ p, Rs x p → p) → q := fun h hz => hz q h

/-- `∀y p. Rs y p → y ≠ x ∨ p = q` and `q` give `Z x`. -/
theorem z_of_functional {σ : Type} [Ty σ] (Rs : σ → Prop → Prop) (x : σ) (q : Prop) :
    (∀ y p, Rs y p → y ≠ x ∨ p = q) → q → ∀ p, Rs x p → p := fun h hq p hp =>
  (h x p hp).elim (fun hne => (hne rfl).elim) (fun e => e ▸ hq)

/-- With `ND` and `NI`, `y ≠ x ∨ p = q` is necessary when true. -/
theorem box_ne_or_eq {σ : Type} [Ty σ] (nd : ∀ x y : σ, x ≠ y → □ (x ≠ y)) (y x : σ) (p q : Prop) :
    (y ≠ x ∨ p = q) → □ (y ≠ x ∨ p = q) := fun h => h.elim
  (fun hne => modal_K _ _ (nec% (fun (h : y ≠ x) => (Or.inl h : y ≠ x ∨ p = q))) (nd y x hne))
  (fun he => modal_K _ _ (nec% (fun (h : p = q) => (Or.inr h : y ≠ x ∨ p = q))) (necessity_of_identity p q he))

/-- `rigid-comprehension-and-nd-imply-plenitude` (for output type `t` only) (Proposition
2.16), for relations of type `σ → t → t`: with `Rs` rigid and coextensive with the
functional `R`, `Z := λy. ∀p. Rs y p → p` represents it. At `x` with `Rxq`: `Rs x q` is
necessary, so `Zx ≤ q`; and every `Rs y p` has `y ≠ x ∨ p = q`, necessarily so by `ND`
and `NI`, so by inextensibility necessarily, which gives `q ≤ Zx`. -/
theorem rigid_comprehension_and_nd_imply_plenitude_at_t {σ : Type} [Ty σ] :
    RigidComprehension (σ → Prop → Prop) → NecessityOfDistinctness σ → Plenitude σ Prop :=
  fun rc nd R hR => (rc R).elim fun Rs hRs =>
    ⟨λ y ↦ ∀ p, Rs y p → p, fun x => (hR x).elim fun q hq =>
      have hRsq : Rs x q := (hRs.2 x q).1 hq.1
      have hfun : ∀ y p, Rs y p → y ≠ x ∨ p = q := fun y p hp =>
        (em (y = x)).elim (fun e => Or.inr (by
            rw [e] at hp
            exact (hq.2 p ((hRs.2 x p).2 hp)).symm))
          Or.inl
      have hle1 : (∀ p, Rs x p → p) ≤ q := (le_iff_prop _ _).2
        (modal_K _ _ (nec% (z_imp_of_rs Rs x q))
          (weaklyPersistent_of_persistent hRs.1.1 x q hRsq))
      have hle2 : q ≤ (∀ p, Rs x p → p) := (le_iff_prop _ _).2
        (modal_K _ _ (nec% (z_of_functional Rs x q))
          (weaklyInextensible_of_inextensible hRs.1.2 (λ y p ↦ y ≠ x ∨ p = q)
            (fun y p hp => box_ne_or_eq nd y x p q (hfun y p hp))))
      show R x (∀ p, Rs x p → p) by
        rw [← le_antisymm_prop q _ hle2 hle1]; exact hq.1⟩

/-! Proposition 2.11 (n. 42), reduced to a restriction principle.

The paper derives Rigid Comprehension from `□`Atomicity, Boolean Completeness and `BF`
with `X*`, the least upper bound of the haecceities of the `X`s. Parts (i) to (iii) of
n. 42 (`X*` is coextensive with `X`, given Actuality, and persistent) go through as
written. Part (iv), inextensibility, has two steps that do not: it boxes a pointwise
claim with `BF` where `□BF` would be needed, and its "without loss of generality" step
assumes that, for `w` an atom and `w′` possibly an atom below `X*z ∧ ¬Yz`, the greatest
lower bound `w″` of the `p` with `w ≤ (p = w′)` is still identical to `w′` wherever `w`
is true, which nothing in the premises gives (see `HANDOFF.md`, §4).

What part (iv) needs from `w″` is only this: for a proposition `p` (here `∀x. X*x →
□Yx`) and a proposition `q` (here `∃z. X*z ∧ ¬Yz`), a proposition `r` that is identical
to `q` wherever `p` is true (`p ≤ (r = q)`) and that entails everything `p` makes `q`
entail (`p ≤ (q ≤ s)` gives `r ≤ s`): `q` restricted to what is accessible from the
`p`-worlds. Given that, for every `p` and `q`, inextensibility follows with `BF` at the
type of properties only, and without atoms. The restriction principle holds in `C5`,
with `r := q ∧ ◇p` (`restriction_of_box_b`); whether `□`Atomicity, Boolean Completeness
and `BF` or `□BF` give it is open. -/

/-- `Hu` gives `∀z. u = z → Hz`. -/
theorem haec_imp {σ : Type} [Ty σ] (u : σ) (H : σ → Prop) : H u → ∀ z, u = z → H z :=
  fun h z e => e ▸ h

/-- The haecceity `λx. u = x` is below `H` when `Hu` is necessary. -/
theorem haec_le_of_box {σ : Type} [Ty σ] (u : σ) (H : σ → Prop) (h : □ (H u)) :
    (λ x ↦ u = x) ≤ H :=
  (le_iff _ _).2 (modal_K _ _ (nec% (haec_imp u H)) h)

/-- `(u = u → p) → p`. -/
theorem imp_of_rfl_imp {σ : Type} [Ty σ] (u : σ) (p : Prop) : (u = u → p) → p := fun h => h rfl

/-- The least upper bound `G` of the haecceities of the `X`s, as the greatest lower
bound of their upper bounds, is below every `H` that is necessary of each `X`. -/
theorem lub_haec_le {σ : Type} [Ty σ] (X G : σ → Prop)
    (hG : GLB G (λ w ↦ UB w (λ Y ↦ ∃ u, X u ∧ Y = λ x ↦ u = x)))
    (H : σ → Prop) (hH : X ⊆ boxAt H) : G ≤ H :=
  glb_ub_least _ G hG H fun Y hY => hY.elim fun u hu => by
    rw [hu.2]
    exact haec_le_of_box u H (hH u hu.1)

/-- And `Gu` is necessary for each `X`, `u` (n. 42, (i) and (iii)). -/
theorem box_lub_haec_of {σ : Type} [Ty σ] (X G : σ → Prop)
    (hG : GLB G (λ w ↦ UB w (λ Y ↦ ∃ u, X u ∧ Y = λ x ↦ u = x)))
    (u : σ) (hu : X u) : □ (G u) :=
  modal_K _ _ (nec% (imp_of_rfl_imp u (G u)))
    ((le_iff_prop _ _).1 (le_apply_of_le _ G u (glb_ub_upper _ G hG _ ⟨u, hu, rfl⟩)))

/-- `Gu → Xu`, given the actual world `w` (n. 42, (ii)): `λy. w → Xy` is necessary of
each `X`, so above `G`. -/
theorem lub_haec_imp {σ : Type} [Ty σ] (act : Actuality) (X G : σ → Prop)
    (hG : GLB G (λ w ↦ UB w (λ Y ↦ ∃ u, X u ∧ Y = λ x ↦ u = x)))
    (u : σ) (hu : G u) : X u :=
  act.elim fun w (hw : ActualWorld w) =>
    imp_of_le_prop (G u) (w → X u)
      (le_apply_of_le G (λ y ↦ w → X y) u
        (lub_haec_le X G hG _ fun v hv => (le_iff_prop _ _).1 (hw.2 (X v) hv))) hu hw.1

/-- `Gu`, then `∀z. Gz → □Yz` makes `q ≤ Yu`. -/
theorem le_of_inext_premise {σ : Type} [Ty σ] (G Y : σ → Prop) (q : Prop) (u : σ) :
    G u → G ⊆ boxAt Y → q ≤ Y u :=
  fun hg hA => (le_iff_prop _ _).2 (box_imp_of_box q (Y u) (hA u hg))

/-- `r = ∃z. Gz ∧ ¬Yz` and `∀z. Gz → r → Yz` give `∀z. Gz → Yz`. -/
theorem forall_of_restricted {σ : Type} [Ty σ] (G Y : σ → Prop) (r : Prop) :
    r = (∃ z, G z ∧ ¬ Y z) → G ⊆ (λ z ↦ r → Y z) → G ⊆ Y :=
  fun e h z hg => (em (Y z)).elim id fun hn => h z hg (e ▸ ⟨z, hg, hn⟩)

/-- Inside the box: where `p` holds, `r = q`, so `□∀z. Gz → r → Yz` gives `□∀z. Gz → Yz`. -/
theorem box_forall_of_restricted {σ : Type} [Ty σ] (G Y : σ → Prop) (p r : Prop) :
    (p → r = (∃ z, G z ∧ ¬ Y z)) → □ (G ⊆ λ z ↦ r → Y z) → p → □ (G ⊆ Y) :=
  fun hrq hb hp => modal_K _ _ (modal_K _ _ (nec% (forall_of_restricted G Y r))
    (necessity_of_identity r _ (hrq hp))) hb

/-- **Proposition 2.11, reduced** (n. 42, with part (iv) repaired): Actuality, Boolean
Completeness at `σ → t`, `BF` at the type of properties, and the restriction principle
give Rigid Comprehension at `σ → t`. The witness is `X*`, the least upper bound of the
haecceities of the `X`s. For inextensibility, fix `Y`; with `p := ∀z. X*z → □Yz` and
`q := ∃z. X*z ∧ ¬Yz`, restriction gives `r`; each `X`-thing `u` has `□X*u`, so
`p ≤ (q ≤ Yu)`, so `r ≤ Yu`, so `λx. r → Yx` is above `X*`; and where `p` holds `r = q`,
so `X* ≤ Y` there. `BF` at `σ → t` boxes the quantifier over `Y`. -/
theorem rigid_comprehension_r_of_restriction {σ : Type} [Ty σ] (act : Actuality)
    (bc : BooleanCompleteness (σ → Prop)) (bf : Barcan (σ → Prop))
    (res : ∀ p q : Prop, ∃ r : Prop, p ≤ (r = q) ∧ ∀ s : Prop, p ≤ (q ≤ s) → r ≤ s) :
    RigidComprehension (σ → Prop) := fun X =>
  (bc (λ Y ↦ UB Y (λ Z ↦ ∃ u, X u ∧ Z = λ x ↦ u = x))).elim fun G hG =>
    have hbox : X ⊆ boxAt G := box_lub_haec_of X G hG
    have hpers : Persistent G :=
      (le_iff G (boxAt G)).1 (lub_haec_le X G hG _ fun u hu => modal_four _ (hbox u hu))
    have hinext : Inextensible G :=
      bf (λ Y ↦ G ⊆ boxAt Y → □ (G ⊆ Y)) fun Y =>
        (res (G ⊆ boxAt Y) (∃ z, G z ∧ ¬ Y z)).elim fun r hr =>
          have hGr : G ≤ (λ x ↦ r → Y x) := lub_haec_le X G hG _ fun u hu =>
            (le_iff_prop _ _).1 (hr.2 (Y u) ((le_iff_prop _ _).2
              (modal_K _ _ (nec% (le_of_inext_premise G Y (∃ z, G z ∧ ¬ Y z) u)) (hbox u hu))))
          modal_K _ _ (modal_K _ _ (nec% (box_forall_of_restricted G Y (G ⊆ boxAt Y) r))
            ((le_iff_prop _ _).1 hr.1)) (modal_four _ ((le_iff G _).1 hGr))
    ⟨G, ⟨hpers, hinext⟩, fun u =>
      ⟨fun hu => box_elim (hbox u hu), lub_haec_imp act X G hG u⟩⟩

/-- `(∀p. p → □◇p) → p → (q ∧ ◇p) = q`. -/
theorem and_dia_eq_of_b (p q : Prop) : (∀ p : Prop, p → □ ◇ p) → p → (q ∧ ◇ p) = q :=
  fun b hp => by rw [b p hp]; exact and_true_eq q

/-- `q ≤ s` gives `□(q → s)`, unfolded. -/
theorem box_imp_of_le' (q s : Prop) : q ≤ s → □ (q → s) := fun h => (le_iff_prop q s).1 h

/-- With `B`: `□(p → q ≤ s)`, `q` and `◇p` give `s`. -/
theorem le_of_and_dia_of_b (p q s : Prop) :
    (∀ p : Prop, p → □ ◇ p) → □ (p → q ≤ s) → q ∧ ◇ p → s := fun b h hq =>
  b_dia_box_imp b (q → s) (dia_mono _ _ (nec% (box_imp_of_le' q s)) (dia_mono _ _ h hq.2)) hq.1

/-- The restriction principle holds in `C5`, with `r := q ∧ ◇p`. -/
theorem restriction_of_box_b (hb : □ (∀ p : Prop, p → □ ◇ p)) :
    ∀ p q : Prop, ∃ r : Prop, p ≤ (r = q) ∧ ∀ s : Prop, p ≤ (q ≤ s) → r ≤ s :=
  fun p q => ⟨q ∧ ◇ p,
    (le_iff_prop _ _).2 (modal_K _ _ (nec% (and_dia_eq_of_b p q)) hb),
    fun s h => (le_iff_prop _ _).2 (modal_K _ _ (modal_K _ _ (nec% (le_of_and_dia_of_b p q s)) hb)
      (modal_four _ ((le_iff_prop _ _).1 h)))⟩

/-! ### Routine records (28 September, night)

Specializations to `t`, `T` stripping a box, necessitations of records already proved
(`K` with the box of the premise), and a few short arguments at `t`. -/

/-- `atomicity-r-implies-atomicity-t`: the `t`-instance. -/
theorem atomicity_r_implies_atomicity_t : Atomicity Prop → AtomicityT := fun h => h
/-- `distinctness-necessary-r-implies-distinctness-necessary-t`: the `t`-instance. -/
theorem distinctness_necessary_r_implies_distinctness_necessary_t :
    NecessityOfDistinctness Prop → NecessityOfDistinctnessT := fun h => h
/-- `necessary-barcan-r-implies-necessary-barcan-t`: the `t`-instance. -/
theorem necessary_barcan_r_implies_necessary_barcan_t : NecBarcan Prop → NecBarcanT := fun h => h
/-- `necessary-distinctness-necessary-r-implies-necessary-distinctness-necessary-t`. -/
theorem necessary_distinctness_necessary_r_implies_necessary_distinctness_necessary_t :
    NecNecessityOfDistinctness Prop → NecNecessityOfDistinctnessT := fun h => h
/-- `strong-leibniz-r-implies-strong-leibniz-t`: the `t`-instance. -/
theorem strong_leibniz_r_implies_strong_leibniz_t : StrongLeibniz Prop → StrongLeibnizT :=
  fun h => h
/-- `necessary-strong-leibniz-r-implies-necessary-strong-leibniz-t`. -/
theorem necessary_strong_leibniz_r_implies_necessary_strong_leibniz_t :
    NecStrongLeibniz Prop → NecStrongLeibnizT := fun h => h

/-- `necessary-atomicity-r-implies-atomicity-r`: `T`. -/
theorem necessary_atomicity_r_implies_atomicity_r {τ : Type} [Rel τ] :
    NecAtomicity τ → Atomicity τ := box_elim
/-- `necessary-barcan-r-implies-barcan-r`: `T`. -/
theorem necessary_barcan_r_implies_barcan_r {σ : Type} [Ty σ] : NecBarcan σ → Barcan σ := box_elim
/-- `necessary-distinctness-necessary-r-implies-distinctness-necessary-r`: `T`. -/
theorem necessary_distinctness_necessary_r_implies_distinctness_necessary_r {σ : Type} [Ty σ] :
    NecNecessityOfDistinctness σ → NecessityOfDistinctness σ := box_elim
/-- `necessary-rigid-comprehension-r-implies-rigid-comprehension-r`: `T`. -/
theorem necessary_rigid_comprehension_r_implies_rigid_comprehension_r {τ : Type} [Rel τ] :
    NecRigidComprehension τ → RigidComprehension τ := box_elim
/-- `necessary-extensionality-r-implies-extensionality-r`: `T`. -/
theorem necessary_extensionality_r_implies_extensionality_r {τ : Type} [Rel τ] :
    NecExtensionality τ → Extensionality τ := box_elim
/-- `necessary-fregean-axiom-implies-fregean-axiom`: `T`. -/
theorem necessary_fregean_axiom_implies_fregean_axiom : NecFregeanAxiom → FregeanAxiom := box_elim
/-- `necessary-functional-choice-r-implies-functional-choice-r`: `T`. -/
theorem necessary_functional_choice_r_implies_functional_choice_r {σ τ : Type} [Ty σ] [Rel τ] :
    NecFunctionalChoice σ τ → FunctionalChoice σ τ := box_elim
/-- `necessary-functionality-r-implies-functionality-r`: `T`. -/
theorem necessary_functionality_r_implies_functionality_r {σ τ : Type} [Ty σ] [Rel τ] :
    NecFunctionality σ τ → Functionality σ τ := box_elim
/-- `necessary-modal-b-implies-modal-b`: `T`. -/
theorem necessary_modal_b_implies_modal_b : NecModalB → ModalB := box_elim
/-- `necessary-modal-five-implies-modal-five`: `T`. -/
theorem necessary_modal_five_implies_modal_five : NecModalFive → ModalFive := box_elim
/-- `necessary-relational-choice-r-implies-relational-choice-r`: `T`. -/
theorem necessary_relational_choice_r_implies_relational_choice_r {σ τ : Type} [Ty σ] [Ty τ] :
    NecRelationalChoice σ τ → RelationalChoice σ τ := box_elim
/-- `necessary-tractarianism-r-implies-tractarianism-r`: `T`. -/
theorem necessary_tractarianism_r_implies_tractarianism_r {σ : Type} [Ty σ] :
    NecTractarianism σ → Tractarianism σ := box_elim
/-- `necessary-strong-leibniz-t-implies-strong-leibniz-t`: `T`. -/
theorem necessary_strong_leibniz_t_implies_strong_leibniz_t : NecStrongLeibnizT → StrongLeibnizT :=
  box_elim

/-- `necessary-barcan-r-implies-necessary-functionality-r`: Proposition 2.1 necessitated. -/
theorem necessary_barcan_r_implies_necessary_functionality_r {σ τ : Type} [Ty σ] [Rel τ] :
    NecBarcan σ → NecFunctionality σ τ :=
  modal_K _ _ (nec% (barcan_r_implies_functionality_r (σ := σ) (τ := τ)))
/-- `necessary-distinctness-necessary-r-implies-necessary-modal-five`. -/
theorem necessary_distinctness_necessary_r_implies_necessary_modal_five :
    NecNecessityOfDistinctness Prop → NecModalFive :=
  modal_K _ _ (nec% distinctness_necessary_t_implies_modal_five)
/-- `necessary-modal-five-implies-necessary-modal-b`. -/
theorem necessary_modal_five_implies_necessary_modal_b : NecModalFive → NecModalB :=
  modal_K _ _ (nec% modal_five_implies_modal_b)
/-- `necessary-modal-b-implies-necessary-distinctness-necessary-r`. -/
theorem necessary_modal_b_implies_necessary_distinctness_necessary_r {σ : Type} [Ty σ] :
    NecModalB → NecNecessityOfDistinctness σ :=
  modal_K _ _ (nec% (modal_b_implies_distinctness_necessary_r (σ := σ)))
/-- `necessary-functional-choice-r-implies-necessary-plenitude-r`. -/
theorem necessary_functional_choice_r_implies_necessary_plenitude_r {σ τ : Type} [Ty σ] [Rel τ] :
    NecFunctionalChoice σ τ → NecPlenitude σ τ :=
  modal_K _ _ (nec% (functional_choice_r_implies_plenitude_r (σ := σ) (τ := τ)))
/-- `necessary-functional-choice-r-implies-necessary-relational-choice-r`. -/
theorem necessary_functional_choice_r_implies_necessary_relational_choice_r {σ τ : Type} [Ty σ]
    [Ty τ] : NecFunctionalChoice σ (τ → Prop) → NecRelationalChoice σ τ :=
  modal_K _ _ (nec% (functional_choice_r_implies_relational_choice_r (σ := σ) (τ := τ)))
/-- `necessary-functionality-r-implies-necessary-tractarianism-r`. -/
theorem necessary_functionality_r_implies_necessary_tractarianism_r {σ : Type} [Ty σ] :
    NecFunctionality σ Prop → NecTractarianism σ :=
  modal_K _ _ (nec% (functionality_r_implies_tractarianism_r (σ := σ)))
/-- `necessary-tractarianism-r-implies-necessary-barcan-r`. -/
theorem necessary_tractarianism_r_implies_necessary_barcan_r {σ : Type} [Ty σ] :
    NecTractarianism σ → NecBarcan σ :=
  modal_K _ _ (nec% (tractarianism_r_implies_barcan_r (σ := σ)))

/-- `relational-choice-and-plenitude-imply-functional-choice-r`: Relational Choice selects
a functional subrelation, and Plenitude represents it by an operation. -/
theorem relational_choice_and_plenitude_imply_functional_choice_r {σ τ : Type} [Ty σ] [Rel τ] :
    RelationalChoice σ τ → Plenitude σ τ → FunctionalChoice σ τ := fun rc pl U hser =>
  (rc U hser).elim fun S hS => (pl S hS.1).elim fun X hX => ⟨X, fun x => hS.2 x (X x) (hX x)⟩
/-- `necessary-relational-choice-and-necessary-plenitude-imply-necessary-functional-choice`. -/
theorem necessary_relational_choice_and_necessary_plenitude_imply_necessary_functional_choice
    {σ τ : Type} [Ty σ] [Rel τ] :
    NecRelationalChoice σ τ → NecPlenitude σ τ → NecFunctionalChoice σ τ := fun h₁ h₂ =>
  modal_K _ _ (modal_K _ _
    (nec% (relational_choice_and_plenitude_imply_functional_choice_r (σ := σ) (τ := τ))) h₁) h₂

/-- `classicism-implies-broad-necessitism-r`: necessitate `∀x. ∃y. y = x`, then `CBF`. -/
theorem classicism_implies_broad_necessitism_r {σ : Type} [Ty σ] : BroadNecessitism σ := fun x =>
  converse_barcan (λ x ↦ ∃ y : σ, y = x) (nec% (fun (x : σ) => (⟨x, rfl⟩ : ∃ y, y = x))) x

/-- `extensionality-r-implies-functionality-r`: pointwise identity is coextension. -/
theorem extensionality_r_implies_functionality_r {σ τ : Type} [Ty σ] [Rel τ] :
    Extensionality (σ → τ) → Functionality σ τ := fun ext X Y h =>
  ext X Y (fun z => by show Rel.coext (X z) (Y z); rw [h z]; exact Rel.coext_refl (Y z))

/-- A truth is `⊤` under the Fregean Axiom, so necessary. -/
theorem box_of_fregean (fa : FregeanAxiom) (p : Prop) (hp : p) : □ p :=
  fa p True ⟨fun _ => trivial, fun _ => hp⟩

/-- `fregean-axiom-implies-necessary-fregean-axiom`. -/
theorem fregean_axiom_implies_necessary_fregean_axiom : FregeanAxiom → NecFregeanAxiom :=
  fun fa => box_of_fregean fa _ fa

/-- `extensionality-r-implies-necessary-extensionality-r`: the nullary instance is the
Fregean Axiom, which makes every truth necessary. -/
theorem extensionality_r_implies_necessary_extensionality_r {τ : Type} [Rel τ] :
    Extensionality τ → Extensionality Prop → NecExtensionality τ := fun ext extP =>
  box_of_fregean (extensionality_r_implies_fregean_axiom extP) _ ext

/-- `fregean-axiom-implies-distinctness-preserving-collapse`: `⊤` is a true `q` with
`□(◇⊤ → p)`, since `p` is necessary. -/
theorem fregean_axiom_implies_distinctness_preserving_collapse :
    FregeanAxiom → DistinctnessPreservingCollapse := fun fa p hp =>
  ⟨True, trivial, box_of_fregean fa _ (fun _ => hp)⟩

/-- `distinctness-preserving-collapse-and-nd-imply-fregean-axiom`: under `ND_t` the two
necessities coincide, so every truth is `⊤` and every falsehood `⊥`. -/
theorem distinctness_preserving_collapse_and_nd_imply_fregean_axiom :
    DistinctnessPreservingCollapse → NecessityOfDistinctness Prop → FregeanAxiom :=
  fun col nd p q hpq =>
    have box : ∀ r : Prop, r → □ r := fun r hr => (col r hr).elim fun s hs =>
      modal_K _ _ hs.2 (nd s False (fun e => (e ▸ hs.1 : False)))
    (em p).elim
      (fun hp => (box p hp).trans (box q (hpq.1 hp)).symm)
      (fun hnp =>
        have hp0 : p = False := by rw [← box_not_eq]; exact box _ hnp
        have hq0 : q = False := by rw [← box_not_eq]; exact box _ (fun hq => hnp (hpq.2 hq))
        hp0.trans hq0.symm)

/-- `atomicity-t-incompatible-with-atomlessness`: an atom below `⊤` has nothing possible
strictly below it. -/
theorem atomicity_t_incompatible_with_atomlessness : AtomicityT → Atomlessness → False :=
  fun at_ atl => ((at_ True).elim
    (fun h => absurd (eq_false_of_le_neg True h) (fun e => e ▸ trivial))
    (fun h => h.elim fun q hq =>
      have hdq : ◇ q := fun e => not_le_neg_of_atom hq.1 (le_neg_of_eq_false q e)
      (atl q hdq).elim fun r hr =>
        hr.1 (eq_false_of_le_neg r ((hq.1 r).1 ⟨hr.2.1, hr.2.2⟩))))

/-- A non-bottom proposition is not below its negation. -/
theorem not_le_neg_of_ne_false (p : Prop) (h : p ≠ False) : ¬ p ≤ ¬ p :=
  fun hle => h (eq_false_of_le_neg p hle)

/-- `strong-leibniz-t-implies-atomicity-t`: a strong world is a weak one, `T`, hence an
atom. -/
theorem strong_leibniz_t_implies_atomicity_t : StrongLeibnizT → AtomicityT := fun sl x =>
  (em (x ≤ ¬ x)).elim Or.inl fun hx =>
    have hne : x ≠ False := fun e => hx (le_neg_of_eq_false x e)
    (sl x hne).elim fun w hw => Or.inr ⟨w, atom_of_decides w ⟨hw.1.1, box_elim hw.1.2⟩, hw.2⟩

/-- `w ≤ q ∨ w ≤ ¬q` is necessary once true: each disjunct is. -/
theorem box_le_or_le (w q : Prop) (h : w ≤ q ∨ w ≤ ¬ q) : □ (w ≤ q ∨ w ≤ ¬ q) :=
  h.elim (fun h => modal_K _ _ (nec% (fun (h' : w ≤ q) => (Or.inl h' : w ≤ q ∨ w ≤ ¬ q)))
      (box_le_prop w q h))
    (fun h => modal_K _ _ (nec% (fun (h' : w ≤ ¬ q) => (Or.inr h' : w ≤ q ∨ w ≤ ¬ q)))
      (box_le_prop w (¬ q) h))

/-- `atomicity-t-and-bf-t-imply-strong-leibniz-t`: an atom below `p` decides every `q`,
each decision is necessary, and BF at `t` boxes the quantifier. -/
theorem atomicity_t_and_bf_t_imply_strong_leibniz_t : AtomicityT → BarcanT → StrongLeibnizT :=
  fun at_ bf p hp => ((at_ p).elim (fun h => absurd h (not_le_neg_of_ne_false p hp))
    (fun h => h.elim fun w hw =>
      ⟨w, ⟨fun e => not_le_neg_of_atom hw.1 (le_neg_of_eq_false w e),
        bf (λ q ↦ w ≤ q ∨ w ≤ ¬ q) fun q => box_le_or_le w q (atom_le_or_le_neg w q hw.1)⟩, hw.2⟩))

/-- `necessary-atomicity-and-necessary-bf-t-imply-necessary-strong-leibniz-t`. -/
theorem necessary_atomicity_and_necessary_bf_t_imply_necessary_strong_leibniz_t :
    NecAtomicity Prop → NecBarcanT → NecStrongLeibnizT := fun h₁ h₂ =>
  modal_K _ _ (modal_K _ _ (nec% atomicity_t_and_bf_t_imply_strong_leibniz_t) h₁) h₂

end Classicism.Proofs
