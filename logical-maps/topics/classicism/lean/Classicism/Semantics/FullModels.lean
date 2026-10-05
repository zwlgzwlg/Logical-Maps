import Classicism.Semantics.IntensionalTheory
import Classicism.Semantics.IntensionalProperties
import Classicism.Certified.Schemas

/-!
# What holds in every full model

The map's general arguments about full and extensionally full models (`arguments/` in the
topic), as theorems about intensional action models:

- **Relational Choice** holds in every extensionally full model (`holds_rc`), the map's
  `relational-choice-full`; and at every arrow of a full one, so `□`Relational Choice
  (`holds_box_rc`), `relational-choice-full-boxed`.

Lean's metatheory has choice, so the map's condition `metatheory-choice` is met by every
model here; the choice is `Classical.choose`.
-/

namespace Classicism.Meta.Intensional

open CategoryTheory

namespace Premodel

variable {Sig : Signature} {C : Type} [SmallCategory C] (A : Premodel Sig C)

/-- **Extensionally full** at every object: every set of tuples from the domains at an object
is the extension, at the identity arrow, of an element of the domain of the matching
relational type there. -/
def ExtFull : Prop :=
  ∀ (ρ : RTy) (W : C) (E : Set (Args A.inner ρ W)),
    ∃ x : A.Dom W (.rel ρ), (A.incl ρ W x).ext' A.inner = E

/-- A full model is extensionally full. -/
theorem Full.extFull (h : A.Full) : A.ExtFull := by
  intro ρ W E
  obtain ⟨x, hx⟩ := h ρ W {p | ∃ a ∈ E, p = ⟨W, a, 𝟙 W⟩}
  refine ⟨x, ?_⟩
  ext a
  simp only [Intension.ext', hx, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨a', ha', e⟩
    cases e
    exact ha'
  · intro ha
    exact ⟨a, ha, rfl⟩

variable {A}

/-- A relation variable applied to two variables holds iff its extension contains them. -/
theorem holds_app_var2 {Γ : Ctx} {W : C} (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ) {σ τ : Ty}
    (R : Var Γ (.rel (.arr σ (.arr τ .t)))) (x : Var Γ σ) (y : Var Γ τ) :
    A.Holds h (.app (.app (.var R) (.var x)) (.var y)) g ↔
      (g.get x, (g.get y, PUnit.unit)) ∈ (A.incl _ W (g.get R)).ext' A.inner := by
  rw [A.holds_app h g (.app (.var R) (.var x)) (.var y) (a' := g.get y) rfl]
  show _ ∈ A.apply (A.sem h (.var R) g) (A.Incl σ W (g.get x)) ↔ _
  rw [A.apply_Incl]
  simp [Intension.ext']
  rfl

/-- A relation variable applied to one variable. -/
theorem holds_app_var1 {Γ : Ctx} {W : C} (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ) {σ : Ty}
    (F : Var Γ (.rel (.arr σ .t))) (x : Var Γ σ) :
    A.Holds h (.app (.var F) (.var x)) g ↔
      (g.get x, PUnit.unit) ∈ (A.incl _ W (g.get F)).ext' A.inner := by
  rw [A.holds_app h g (.var F) (.var x) (a' := g.get x) rfl]
  rfl

/-- Two variables are equal iff their values are. -/
theorem holds_eq_var (M : A.IsModel) {Γ : Ctx} {W : C} (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ)
    {σ : Ty} (x y : Var Γ σ) : A.Holds h (Term.eq' (.var x) (.var y)) g ↔ g.get x = g.get y := by
  rw [A.holds_eq M]
  exact ⟨fun e => A.Incl_injective σ W e, fun e => congrArg (A.Incl σ W) e⟩

/-! ### Relational Choice -/

/-- Relational Choice at `σ`, `τ`, at any arrow of an extensionally full model: a serial
relation's extension has a functional subset by choice, and that subset is the extension of an
element of the domain. -/
theorem holds_rc {B : Premodel Signature.pure C} (M : B.IsModel) (hE : B.ExtFull) {W : C}
    (h : B.W₀ ⟶ W) (σ τ : Ty) : B.Holds h (P.RelationalChoice.quoted σ τ) .nil := by
  simp only [P.RelationalChoice.quoted, B.holds_forall M, B.holds_imp M, B.holds_exists M,
    B.holds_conj M, holds_app_var2, holds_eq_var M, IEnv.get]
  intro U hU
  choose f hf using hU
  obtain ⟨S, hS⟩ := hE (.arr σ (.arr τ .t)) W {a | a.2.1 = f a.1}
  refine ⟨S, fun x => ⟨f x, ?_, fun z hz => ?_⟩, fun x y hxy => ?_⟩
  · rw [hS]; rfl
  · rw [hS] at hz; exact hz.symm
  · rw [hS] at hxy
    have hy : y = f x := hxy
    exact hy ▸ hf x

/-- `□`Relational Choice: Relational Choice at every arrow, every object being extensionally
full. -/
theorem holds_box_rc {B : Premodel Signature.pure C} (M : B.IsModel) (hE : B.ExtFull) {W : C}
    (h : B.W₀ ⟶ W) (σ τ : Ty) : B.Holds h (P.NecRelationalChoice.quoted σ τ) .nil := by
  show B.Holds h (Term.box (P.RelationalChoice.quoted σ τ)) .nil
  rw [B.holds_box M]
  intro V k
  exact holds_rc M hE (h ≫ k) σ τ

/-! ### Transversal Choice -/

/-- Transversal Choice at `σ`, at any arrow of an extensionally full model: the
representatives of the cells of an equivalence relation's extension, chosen by
`Quotient.out`, are the extension of an element of the domain. -/
theorem holds_tc {B : Premodel Signature.pure C} (M : B.IsModel) (hE : B.ExtFull) {W : C}
    (h : B.W₀ ⟶ W) (σ : Ty) : B.Holds h (P.TransversalChoice.quoted σ) .nil := by
  simp only [P.TransversalChoice.quoted, B.holds_forall M, B.holds_imp M, B.holds_exists M,
    B.holds_conj M, holds_app_var2, holds_app_var1, holds_eq_var M, IEnv.get]
  rintro R ⟨hrefl, hsymm, htrans⟩
  let r : Setoid (B.Dom W σ) :=
    ⟨fun x y => (x, (y, PUnit.unit)) ∈ (B.incl _ W R).ext' B.inner, ⟨hrefl, hsymm _ _, htrans _ _ _⟩⟩
  obtain ⟨F, hF⟩ := hE (.arr σ .t) W {a | a.1 = (Quotient.mk r a.1).out}
  refine ⟨F, fun x => ⟨(Quotient.mk r x).out, ?_, ?_, fun z ⟨hxz, hz⟩ => ?_⟩⟩
  · exact hsymm _ _ (Quotient.mk_out (s := r) x)
  · rw [hF]
    show _ = (Quotient.mk r (Quotient.mk r x).out).out
    rw [Quotient.out_eq]
  · rw [hF] at hz
    have hz : z = (Quotient.mk r z).out := hz
    rw [hz, Quotient.sound (s := r) (hsymm _ _ hxz)]

/-! ### Distinctness-Preserving Collapse -/

variable (A) in
/-- **The actual world is isolated**: the actual-world proposition `a`, true and entailing
every truth, is in the domain at the evaluation object, and no world outside `a` sees a world
in `a`. -/
def ActualWorldIsolated : Prop :=
  ∃ a : A.Dom A.W₀ (.rel .t), (A.incl .t A.W₀ a).True A.inner ∧
    (∀ p : A.Dom A.W₀ (.rel .t), (A.incl .t A.W₀ p).True A.inner → A.incl .t A.W₀ a ⊆ A.incl .t A.W₀ p) ∧
    ∀ {V U : C} (i : A.W₀ ⟶ V) (j : V ⟶ U), (⟨V, PUnit.unit, i⟩ : Tuple A.inner .t A.W₀) ∉ A.incl .t A.W₀ a →
      (⟨U, PUnit.unit, i ≫ j⟩ : Tuple A.inner .t A.W₀) ∉ A.incl .t A.W₀ a

/-- Distinctness-Preserving Collapse where the actual world is isolated: for a true `p`, take
`q := a`; at a world in `a`, `p` holds, and at a world outside it `◇a` fails. -/
theorem holds_dpc {B : Premodel Signature.pure C} (M : B.IsModel) (hI : B.ActualWorldIsolated) :
    B.HoldsSentence P.DistinctnessPreservingCollapse.quoted := by
  obtain ⟨a, ha, hle, hiso⟩ := hI
  simp only [Premodel.HoldsSentence, P.DistinctnessPreservingCollapse.quoted, B.holds_forall M,
    B.holds_imp M, B.holds_exists M, B.holds_conj M, B.holds_box M, B.holds_dia M, holds_var,
    IEnv.get, IEnv.get_map, B.incl_map, Intension.mem_map, Category.comp_id, Category.id_comp]
  intro p hp
  refine ⟨a, ha, fun {V} k ⟨U, j, hj⟩ => ?_⟩
  by_contra hk
  exact hiso k j (fun h => hk (hle p hp h)) hj

end Premodel

end Classicism.Meta.Intensional
