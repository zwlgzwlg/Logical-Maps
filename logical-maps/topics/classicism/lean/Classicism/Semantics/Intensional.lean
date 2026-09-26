import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Set.Basic
import Classicism.Syntax.Entailment
import Classicism.Semantics.Env

/-!
# Intensional action premodels and models

The intensional form of the paper's action models (Dorr, *Boolean Completeness without
Rigid Comprehension*, §"Intensional action models"; the paper *Classicism* sketches it and
its Appendix E uses the passage to and from it, `Int` and `App`). This module has the
definitions; `IntensionalSoundness.lean` has the soundness theorem.

An **action** of a category `C` is a functor `C ⥤ Type`. On a category with a base object
`W₀`, a premodel supplies an inner action `-^σ` for each type, with `W^e` nonempty, and at
each relational type `τ = σ₁ → ⋯ → σₙ → t` the inner action is a *subaction* of the outer
one `-^[τ]`: at `W`, the sets of tuples `⟨x₁, …, xₙ, h⟩` with `h : W → V` an arrow and each
`xₖ` an *inner* element of `V^{σₖ}`, an arrow `h : W → V` acting by precomposition,
`h^[τ] A = {⟨x̄, i⟩ | ⟨x̄, i ∘ h⟩ ∈ A}`. So a relation is an **intension**: which tuples it
holds of, at which possibilities. Where the action models of *Classicism* take an element
of `W^{σ→τ}` to be a well-behaved function on pairs `⟨h, x⟩`, here it is the set of the
tuples the function accepts; the two are in bijection (`Int` and `App`), and what the
intensional form buys is that the Boolean operations at every relational type are the set
operations, and entailment is inclusion.

The interpretation function is total here where the paper's is partial: an application
whose argument's value is not inner reads as the empty set of tuples with an inner
witness, which is the paper's `A @ x` when the argument is inner. An intensional action
premodel is a **model** when the value of every term is inner, the paper's definition.

Everything is classical (Mathlib is imported), as the paper's model theory is.
-/

namespace Classicism.Meta.Intensional

open CategoryTheory

/-! ### Tuples and intensions over a family of inner actions -/

section Outer

variable {C : Type} [SmallCategory C] (inner : Ty → C ⥤ Type)

/-- The arguments of a relational type at an object: `()` at `t`, and at `σ → ρ` an inner
element of `V^σ` and the arguments of `ρ`. Written through the recursor of the mutual
inductive, as a reducible definition, so that it reduces by iota at a constructor. -/
abbrev Args (ρ : RTy) (V : C) : Type :=
  @RTy.rec (fun _ => PUnit.{2}) (fun _ => C → Type)
    PUnit.unit (fun _ _ => PUnit.unit)
    (fun _ => PUnit)
    (fun σ _ _ ih => fun V => (inner σ).obj V × ih V)
    ρ V

example (V : C) : Args inner .t V = PUnit := rfl
example (σ : Ty) (ρ : RTy) (V : C) : Args inner (.arr σ ρ) V = ((inner σ).obj V × Args inner ρ V) := rfl

/-- A tuple of a relational type from `W`: a target `V`, arguments at `V`, and an arrow
`W → V`, in the paper's order with the arrow last. -/
abbrev Tuple (ρ : RTy) (W : C) : Type := Σ V : C, Args inner ρ V × (W ⟶ V)

/-- The outer domain at a relational type: the intensions, sets of tuples. -/
abbrev Intension (ρ : RTy) (W : C) : Type := Set (Tuple inner ρ W)

/-- The outer domain at a type: at `e` the inner domain itself. -/
abbrev Outer (σ : Ty) (W : C) : Type :=
  match σ with
  | .e => (inner .e).obj W
  | .rel ρ => Intension inner ρ W

/-- The action of an arrow on arguments, componentwise. -/
def Args.map : ∀ (ρ : RTy) {V V' : C}, (V ⟶ V') → Args inner ρ V → Args inner ρ V'
  | .t, _, _, _, _ => PUnit.unit
  | .arr σ ρ, _, _, j, a => ((inner σ).map j a.1, Args.map ρ j a.2)

theorem Args.map_id : ∀ (ρ : RTy) (V : C) (a : Args inner ρ V), Args.map inner ρ (𝟙 V) a = a
  | .t, _, _ => rfl
  | .arr σ ρ, V, a => by
    show ((inner σ).map (𝟙 V) a.1, Args.map inner ρ (𝟙 V) a.2) = a
    rw [Functor.map_id, Args.map_id ρ]; rfl

theorem Args.map_comp : ∀ (ρ : RTy) {V V' V'' : C} (j : V ⟶ V') (k : V' ⟶ V'') (a : Args inner ρ V),
    Args.map inner ρ (j ≫ k) a = Args.map inner ρ k (Args.map inner ρ j a)
  | .t, _, _, _, _, _, _ => rfl
  | .arr σ ρ, _, _, _, j, k, a => by
    show ((inner σ).map (j ≫ k) a.1, Args.map inner ρ (j ≫ k) a.2) = _
    rw [Functor.map_comp, Args.map_comp ρ]; rfl

/-- The action of an arrow on an intension, by precomposition:
`h^[τ] A = {⟨x̄, i⟩ | ⟨x̄, i ∘ h⟩ ∈ A}`. -/
def Intension.map {ρ : RTy} {W V : C} (h : W ⟶ V) (A : Intension inner ρ W) : Intension inner ρ V :=
  {p | (⟨p.1, p.2.1, h ≫ p.2.2⟩ : Tuple inner ρ W) ∈ A}

@[simp] theorem Intension.mem_map {ρ : RTy} {W V : C} (h : W ⟶ V) (A : Intension inner ρ W)
    (p : Tuple inner ρ V) :
    p ∈ Intension.map inner h A ↔ (⟨p.1, p.2.1, h ≫ p.2.2⟩ : Tuple inner ρ W) ∈ A :=
  Iff.rfl

theorem Intension.map_id {ρ : RTy} {W : C} (A : Intension inner ρ W) : Intension.map inner (𝟙 W) A = A := by
  ext ⟨V, a, i⟩; simp [Intension.map]

theorem Intension.map_comp {ρ : RTy} {W V U : C} (h : W ⟶ V) (i : V ⟶ U) (A : Intension inner ρ W) :
    Intension.map inner (h ≫ i) A = Intension.map inner i (Intension.map inner h A) := by
  ext ⟨T, a, j⟩; simp [Intension.map, Category.assoc]

/-- The same at a type: the inner action at `e`. -/
def Outer.map : ∀ (σ : Ty) {W V : C}, (W ⟶ V) → Outer inner σ W → Outer inner σ V
  | .e, _, _, h, x => (inner .e).map h x
  | .rel _, _, _, h, A => Intension.map inner h A

@[simp] theorem Outer.map_rel {ρ : RTy} {W V : C} (h : W ⟶ V) (A : Intension inner ρ W) :
    Outer.map inner (.rel ρ) h A = Intension.map inner h A := rfl

theorem Outer.map_id : ∀ (σ : Ty) (W : C) (x : Outer inner σ W), Outer.map inner σ (𝟙 W) x = x
  | .e, _, x => by
    show (inner .e).map (𝟙 _) x = x
    rw [Functor.map_id]; rfl
  | .rel ρ, W, A => Intension.map_id inner A

theorem Outer.map_comp : ∀ (σ : Ty) {W V U : C} (h : W ⟶ V) (i : V ⟶ U) (x : Outer inner σ W),
    Outer.map inner σ (h ≫ i) x = Outer.map inner σ i (Outer.map inner σ h x)
  | .e, _, _, _, h, i, x => by
    show (inner .e).map (h ≫ i) x = (inner .e).map i ((inner .e).map h x)
    rw [Functor.map_comp]; rfl
  | .rel ρ, _, _, _, h, i, A => Intension.map_comp inner h i A

/-- The application of an intension of type `σ → ρ` to an inner element of `W^σ`:
`A @ x = {⟨ȳ, h⟩ | ⟨h^σ x, ȳ, h⟩ ∈ A}`. -/
def Intension.app {σ : Ty} {ρ : RTy} {W : C} (F : Intension inner (.arr σ ρ) W) (x : (inner σ).obj W) :
    Intension inner ρ W :=
  {p | (⟨p.1, ((inner σ).map p.2.2 x, p.2.1), p.2.2⟩ : Tuple inner (.arr σ ρ) W) ∈ F}

@[simp] theorem Intension.mem_app {σ : Ty} {ρ : RTy} {W : C} (F : Intension inner (.arr σ ρ) W)
    (x : (inner σ).obj W) (p : Tuple inner ρ W) :
    p ∈ F.app inner x ↔ (⟨p.1, ((inner σ).map p.2.2 x, p.2.1), p.2.2⟩ : Tuple inner (.arr σ ρ) W) ∈ F :=
  Iff.rfl

/-- Application commutes with the action of arrows: `h^ρ (F @ x) = (h^{σ→ρ} F) @ (h^σ x)`. -/
theorem Intension.app_map {σ : Ty} {ρ : RTy} {W V : C} (h : W ⟶ V) (F : Intension inner (.arr σ ρ) W)
    (x : (inner σ).obj W) :
    Intension.map inner h (F.app inner x) = (Intension.map inner h F).app inner ((inner σ).map h x) := by
  ext ⟨U, a, j⟩
  simp [Intension.app, Intension.map, Functor.map_comp]

/-- The extension of an intension at its object: the arguments it holds of under the
identity arrow. -/
def Intension.ext' {ρ : RTy} {W : C} (A : Intension inner ρ W) : Set (Args inner ρ W) :=
  {a | (⟨W, a, 𝟙 W⟩ : Tuple inner ρ W) ∈ A}

/-- A proposition at `W` is **true** when it contains the identity arrow of `W`. -/
def Intension.True {W : C} (p : Intension inner .t W) : Prop :=
  (⟨W, PUnit.unit, 𝟙 W⟩ : Tuple inner .t W) ∈ p

end Outer

/-! ### Intensional action premodels -/

/-- An intensional action premodel for `Sig` on the category `C`: a base object `W₀`; an
inner action for each type, nonempty at `e`; the inclusion of each inner relational domain
into the intensions, natural and injective, which makes it a subaction; and a value at the
base for each constant.

The paper asks the category to be *rooted*, every object having an arrow from `W₀`; as
for the action models, nothing here uses it, so it is not asked. -/
structure Premodel (Sig : Signature) (C : Type) [SmallCategory C] where
  /-- The base object. -/
  W₀ : C
  /-- The inner action at each type. -/
  inner : Ty → C ⥤ Type
  /-- `W^e` is nonempty. -/
  nonempty_e : ∀ W : C, Nonempty ((inner .e).obj W)
  /-- The subaction: each inner relational domain sits inside the intensions. -/
  incl : ∀ (ρ : RTy) (W : C), (inner (Ty.rel ρ)).obj W → Intension inner ρ W
  /-- The inclusion commutes with the actions. -/
  incl_map : ∀ (ρ : RTy) {W V : C} (h : W ⟶ V) (x : (inner (Ty.rel ρ)).obj W),
    incl ρ V ((inner (Ty.rel ρ)).map h x) = Intension.map inner h (incl ρ W x)
  /-- The inclusion is injective. -/
  incl_injective : ∀ (ρ : RTy) (W : C), Function.Injective (incl ρ W)
  /-- The value of each constant, at the base. -/
  I : ∀ c : Sig.Const, (inner (Sig.typeOf c)).obj W₀

namespace Premodel

variable {Sig : Signature} {C : Type} [SmallCategory C] (A : Premodel Sig C)

/-- The inner domain at `W` and `σ`. -/
abbrev Dom (W : C) (σ : Ty) : Type := (A.inner σ).obj W

/-- The inclusion at a type: the identity at `e`. -/
def Incl : ∀ (σ : Ty) (W : C), A.Dom W σ → Outer A.inner σ W
  | .e, _, x => x
  | .rel ρ, W, x => A.incl ρ W x

theorem Incl_map : ∀ (σ : Ty) {W V : C} (h : W ⟶ V) (x : A.Dom W σ),
    A.Incl σ V ((A.inner σ).map h x) = Outer.map A.inner σ h (A.Incl σ W x)
  | .e, _, _, _, _ => rfl
  | .rel ρ, _, _, h, x => A.incl_map ρ h x

theorem Incl_injective : ∀ (σ : Ty) (W : C), Function.Injective (A.Incl σ W)
  | .e, _ => fun _ _ h => h
  | .rel ρ, W => A.incl_injective ρ W

theorem Incl_rel (ρ : RTy) (W : C) (x : A.Dom W (.rel ρ)) : A.Incl (.rel ρ) W x = A.incl ρ W x := rfl

/-- The application of an intension to an outer argument: the tuples `⟨ȳ, h⟩` such that
`⟨x', ȳ, h⟩ ∈ F` for the inner `x'` that is `h^σ x`, when there is one. When the argument is
inner this is the paper's `F @ x` (`apply_Incl`); in a model every argument is. -/
def apply {σ : Ty} {ρ : RTy} {W : C} (F : Intension A.inner (.arr σ ρ) W) (x : Outer A.inner σ W) :
    Intension A.inner ρ W :=
  {p | ∃ x' : A.Dom p.1 σ, A.Incl σ p.1 x' = Outer.map A.inner σ p.2.2 x ∧
    (⟨p.1, (x', p.2.1), p.2.2⟩ : Tuple A.inner (.arr σ ρ) W) ∈ F}

theorem apply_Incl {σ : Ty} {ρ : RTy} {W : C} (F : Intension A.inner (.arr σ ρ) W) (x : A.Dom W σ) :
    A.apply F (A.Incl σ W x) = F.app A.inner x := by
  ext ⟨U, a, j⟩
  simp only [apply, Intension.app, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨x', hx', hF⟩
    rw [← A.Incl_map] at hx'
    rw [← A.Incl_injective σ U hx']
    exact hF
  · intro hF
    exact ⟨_, A.Incl_map σ j x, hF⟩

theorem apply_eq {σ : Ty} {ρ : RTy} {W : C} (F : Intension A.inner (.arr σ ρ) W) {x : Outer A.inner σ W}
    {b : A.Dom W σ} (hb : A.Incl σ W b = x) : A.apply F x = F.app A.inner b := by
  subst hb; exact A.apply_Incl F b

/-- Application commutes with the action of arrows, for any intension and any outer
argument: the transport lemma's application case. -/
theorem apply_map {σ : Ty} {ρ : RTy} {W V : C} (i : W ⟶ V) (F : Intension A.inner (.arr σ ρ) W)
    (x : Outer A.inner σ W) :
    A.apply (Intension.map A.inner i F) (Outer.map A.inner σ i x)
      = Intension.map A.inner i (A.apply F x) := by
  ext ⟨U, a, j⟩
  simp only [apply, Intension.mem_map, Set.mem_ofPred_eq]
  rw [Outer.map_comp]

/-- Move an assignment along an arrow: `i ∘ g`. -/
abbrev push {W V : C} (i : W ⟶ V) {Γ : Ctx} (g : IEnv (A.Dom W) Γ) : IEnv (A.Dom V) Γ :=
  g.map fun σ => (A.inner σ).map i

/-! ### The readings of the logical constants

Each is a set of tuples whose membership does not depend on the arrow: the constants "do
not care about the first co-ordinate of their argument". The type-subscripted operations
read uniformly at every relational type `ρ`, since a relation of type `ρ` is a set of
tuples: `¬_ρ` is complement, `∧_ρ` intersection, `⊑_ρ` inclusion, and so on. That their
readings agree with the readings of their unfoldings is the δ-clause of the soundness
proof, a lemma rather than a definition. -/

/-- The constant relation `const_ρ : t → ρ`: `⟨p, ȳ, i⟩` when `p` is true. -/
def constRead (ρ : RTy) (W : C) : Intension A.inner (.arr (.rel .t) ρ) W :=
  {p | (A.incl .t p.1 p.2.1.1).True A.inner}

/-- `¬_ρ`: `⟨X, ȳ, i⟩` when `X` does not hold of `ȳ`. At `t`, `¬`. -/
def negRead (ρ : RTy) (W : C) : Intension A.inner (.arr (.rel ρ) ρ) W :=
  {p | (⟨p.1, p.2.1.2, 𝟙 p.1⟩ : Tuple A.inner ρ p.1) ∉ A.incl ρ p.1 p.2.1.1}

/-- `∧_ρ`: `⟨X, Y, ȳ, i⟩` when both hold of `ȳ`. At `t`, `∧`. -/
def andRead (ρ : RTy) (W : C) : Intension A.inner (.arr (.rel ρ) (.arr (.rel ρ) ρ)) W :=
  {p | (⟨p.1, p.2.1.2.2, 𝟙 p.1⟩ : Tuple A.inner ρ p.1) ∈ A.incl ρ p.1 p.2.1.1 ∧
    (⟨p.1, p.2.1.2.2, 𝟙 p.1⟩ : Tuple A.inner ρ p.1) ∈ A.incl ρ p.1 p.2.1.2.1}

/-- `∨_ρ`. At `t`, `∨`. -/
def orRead (ρ : RTy) (W : C) : Intension A.inner (.arr (.rel ρ) (.arr (.rel ρ) ρ)) W :=
  {p | (⟨p.1, p.2.1.2.2, 𝟙 p.1⟩ : Tuple A.inner ρ p.1) ∈ A.incl ρ p.1 p.2.1.1 ∨
    (⟨p.1, p.2.1.2.2, 𝟙 p.1⟩ : Tuple A.inner ρ p.1) ∈ A.incl ρ p.1 p.2.1.2.1}

/-- `∀σ`: `⟨B, i⟩` when the extension of `B` is everything. -/
def allRead (σ : Ty) (W : C) : Intension A.inner (.arr (.rel (.arr σ .t)) .t) W :=
  {p | ∀ a : A.Dom p.1 σ, (⟨p.1, (a, PUnit.unit), 𝟙 p.1⟩ : Tuple A.inner (.arr σ .t) p.1) ∈ A.incl _ p.1 p.2.1.1}

/-- `∃σ`: `⟨B, i⟩` when the extension of `B` is nonempty. -/
def exRead (σ : Ty) (W : C) : Intension A.inner (.arr (.rel (.arr σ .t)) .t) W :=
  {p | ∃ a : A.Dom p.1 σ, (⟨p.1, (a, PUnit.unit), 𝟙 p.1⟩ : Tuple A.inner (.arr σ .t) p.1) ∈ A.incl _ p.1 p.2.1.1}

/-- `=σ`: `⟨x, y, i⟩` when `x = y`. -/
def eqRead (σ : Ty) (W : C) : Intension A.inner (.arr σ (.arr σ .t)) W :=
  {p | p.2.1.1 = p.2.1.2.1}

/-- Coextensiveness `≡_ρ`: `⟨X, Y, i⟩` when the extensions of `X` and `Y` agree. -/
def coextRead (ρ : RTy) (W : C) : Intension A.inner (.arr (.rel ρ) (.arr (.rel ρ) .t)) W :=
  {p | ∀ a : Args A.inner ρ p.1, (⟨p.1, a, 𝟙 p.1⟩ : Tuple A.inner ρ p.1) ∈ A.incl ρ p.1 p.2.1.1 ↔
    (⟨p.1, a, 𝟙 p.1⟩ : Tuple A.inner ρ p.1) ∈ A.incl ρ p.1 p.2.1.2.1}

/-- The pointwise box `□_ρ`: `⟨X, ȳ, i⟩` when `X` holds of `ȳ` under every arrow. -/
def boxRead (ρ : RTy) (W : C) : Intension A.inner (.arr (.rel ρ) ρ) W :=
  {p | ∀ (U : C) (j : p.1 ⟶ U), (⟨U, Args.map A.inner ρ j p.2.1.2, j⟩ : Tuple A.inner ρ p.1) ∈ A.incl ρ p.1 p.2.1.1}

/-- Pointwise implication `⊑_ρ`, `λX Y. ∀z̄. X z̄ → Y z̄`: `⟨X, Y, i⟩` when the extension of
`X` is included in that of `Y`. -/
def boxImpRead (ρ : RTy) (W : C) : Intension A.inner (.arr (.rel ρ) (.arr (.rel ρ) .t)) W :=
  {p | ∀ a : Args A.inner ρ p.1, (⟨p.1, a, 𝟙 p.1⟩ : Tuple A.inner ρ p.1) ∈ A.incl ρ p.1 p.2.1.1 →
    (⟨p.1, a, 𝟙 p.1⟩ : Tuple A.inner ρ p.1) ∈ A.incl ρ p.1 p.2.1.2.1}

/-! ### The interpretation function -/

/-- The paper's `⟦A⟧^g_h`: the value of a term relative to an arrow `h : W₀ → W` and an
assignment `g` of inner elements at `W`, an outer element at `W`. The clause for an
abstraction: `⟨x, ȳ, i⟩` is in the value of `λv. B` when `ȳ` is in the extension of the value
of `B` relative to `i ∘ h` and `(i ∘ g)[v ↦ x]`. -/
def sem : ∀ {Γ : Ctx} {σ : Ty} {W : C},
    (A.W₀ ⟶ W) → Term Sig Γ σ → IEnv (A.Dom W) Γ → Outer A.inner σ W
  | _, _, W, _, .var v, g => A.Incl _ W (g.get v)
  | _, _, W, h, .const c, _ => A.Incl _ W ((A.inner _).map h (A.I c))
  | _, _, _, h, .app f a, g => A.apply (sem h f g) (sem h a g)
  | _, _, W, h, .lam (σ := σ) (ρ := ρ) b, g =>
    {p : Tuple A.inner (.arr σ ρ) W |
      (⟨p.1, p.2.1.2, 𝟙 p.1⟩ : Tuple A.inner ρ p.1) ∈ sem (h ≫ p.2.2) b (.cons p.2.1.1 (A.push p.2.2 g))}
  | _, _, W, _, .and, _ => A.andRead .t W
  | _, _, W, _, .or, _ => A.orRead .t W
  | _, _, W, _, .not, _ => A.negRead .t W
  | _, _, W, _, .all σ, _ => A.allRead σ W
  | _, _, W, _, .ex σ, _ => A.exRead σ W
  | _, _, W, _, .eq σ, _ => A.eqRead σ W
  | _, _, W, _, .constR ρ, _ => A.constRead ρ W
  | _, _, W, _, .negR ρ, _ => A.negRead ρ W
  | _, _, W, _, .andR ρ, _ => A.andRead ρ W
  | _, _, W, _, .orR ρ, _ => A.orRead ρ W
  | _, _, W, _, .coextR ρ, _ => A.coextRead ρ W
  | _, _, W, _, .boxR ρ, _ => A.boxRead ρ W
  | _, _, W, _, .boxImpR ρ, _ => A.boxImpRead ρ W

/-- `A, h, g ⊩ P`: the value of `P` is true, containing the identity arrow of `W`. -/
def Holds {Γ : Ctx} {W : C} (h : A.W₀ ⟶ W) (p : Formula Sig Γ) (g : IEnv (A.Dom W) Γ) : Prop :=
  (⟨W, PUnit.unit, 𝟙 W⟩ : Tuple A.inner .t W) ∈ A.sem h p g

/-- A sentence holds in the premodel: at the base, under the identity. -/
def HoldsSentence (p : Sentence Sig) : Prop := A.Holds (𝟙 A.W₀) p .nil

/-- An axiom set holds in the premodel. -/
def HoldsAx (Ax : AxiomSet Sig) : Prop := ∀ a, Ax a → A.HoldsSentence a

/-- **Intensional action model**: the value of every term, relative to every arrow from
the base and every assignment of inner elements, is inner. -/
def IsModel : Prop :=
  ∀ {Γ : Ctx} {σ : Ty} {W : C} (h : A.W₀ ⟶ W) (t : Term Sig Γ σ) (g : IEnv (A.Dom W) Γ),
    A.sem h t g ∈ Set.range (A.Incl σ W)

end Premodel

end Classicism.Meta.Intensional
