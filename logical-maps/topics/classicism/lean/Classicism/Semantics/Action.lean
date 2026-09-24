import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Data.Set.Basic
import Classicism.Syntax.Entailment

/-!
# Action premodels and action models

The paper's models of Classicism (Classicism, §"Action models"; soundness in the appendix
"Soundness and completeness of action models for Classicism"), formalized directly. This
module has the definitions; `ActionSoundness.lean` has the theorem.

An **action** of a category `C` is a functor `C ⥤ Type`. An **action premodel** on a
rooted category `⟨C, W₀⟩` supplies an *inner* action `-^σ` for every type `σ`, with
`W^e` nonempty; the paper asks that `-^t` be a subaction of the powerset action (at `W`,
the sets of arrows out of `W`, with `h` acting by division) and `-^{σ→τ}` a subaction of
the exponential action of `-^σ` and `-^τ` (well-behaved functions on pairs `⟨h, x⟩`).
Here, following Cian's reformulation, each type also has an **outer** action `-^[σ]`,
defined by recursion on the type from the inner actions: `-^[e] = -^e`, `-^[t]` the
powerset action, and `-^[σ→ρ]` the functions on pairs `⟨h : W → V, x ∈ V^σ⟩` (an *inner*
argument) into `V^[ρ]` (an *outer* value), with no well-behavedness required. The
premodel then supplies an injective, natural map `-^σ → -^[σ]` — the subaction — and the
paper's conditions on it: the elements of `W^{σ→ρ}` are well-behaved and take their
values in the inner `-^ρ`.

The point of the outer actions is that the **interpretation function** is total: the
value of a term, relative to an arrow `h : W₀ → W` and an assignment of *inner* elements
at `W` to its free variables, is an element of the outer domain, by the paper's nine
clauses. The paper's interpretation is partial at exactly one place, an application whose
argument's value is not in the inner domain; there the outer reading takes a default
value. An action premodel is an **action model** when no value is ever outside the inner
domain, which is the paper's definition; in a model the two interpretations agree
everywhere.

Everything is classical here (Mathlib is imported), as the paper's model theory is.
-/

namespace Classicism.Meta

open CategoryTheory

/-! ### The outer actions -/

section Outer

variable {C : Type} [SmallCategory C] (inner : Ty → C ⥤ Type)

/-- The outer domain at a relational type: at `t`, the sets of arrows out of `W` (to any
object); at `σ → ρ`, the functions taking an arrow `h : W → V` and an inner element of
`V^σ` to an outer element of `V^[ρ]`. Written through the recursor, as a reducible
definition, so that `RawR inner .t W` *is* a `Set` to instance search: the `∈`, `∩`,
`ᶜ` and `ext` of sets then apply to it directly. -/
abbrev RawR (ρ : RTy) (W : C) : Type :=
  @RTy.rec (fun _ => PUnit.{2}) (fun _ => C → Type)
    PUnit.unit (fun _ _ => PUnit.unit)
    (fun W => Set (Σ V : C, W ⟶ V))
    (fun σ _ _ ih => fun W => ∀ V : C, (W ⟶ V) → (inner σ).obj V → ih V)
    ρ W

/-- The outer domain at a type: at `e` the inner domain itself. -/
abbrev RawT (σ : Ty) (W : C) : Type :=
  match σ with
  | .e => (inner .e).obj W
  | .rel ρ => RawR inner ρ W

example (W : C) : RawR inner .t W = Set (Σ V : C, W ⟶ V) := rfl
example (σ : Ty) (ρ : RTy) (W : C) :
    RawR inner (.arr σ ρ) W = ∀ V : C, (W ⟶ V) → (inner σ).obj V → RawR inner ρ V := rfl

/-- The action of an arrow on an outer element: at `t` by division, at `σ → ρ` by
precomposition. -/
def RawR.map : ∀ (ρ : RTy) {W V : C}, (W ⟶ V) → RawR inner ρ W → RawR inner ρ V
  | .t, _, _, h, X => {p : Σ V, _ ⟶ V | (⟨p.1, h ≫ p.2⟩ : Σ V, _ ⟶ V) ∈ X}
  | .arr _ _, _, _, h, α => fun U i x => α U (h ≫ i) x

/-- The same at a type. -/
def RawT.map : ∀ (σ : Ty) {W V : C}, (W ⟶ V) → RawT inner σ W → RawT inner σ V
  | .e, _, _, h, x => (inner .e).map h x
  | .rel ρ, _, _, h, x => RawR.map inner ρ h x

theorem RawR.map_id : ∀ (ρ : RTy) (W : C) (x : RawR inner ρ W), RawR.map inner ρ (𝟙 W) x = x
  | .t, _, X => by
    show {p : Σ V, _ ⟶ V | (⟨p.1, 𝟙 _ ≫ p.2⟩ : Σ V, _ ⟶ V) ∈ X} = X
    ext ⟨V, i⟩
    simp
  | .arr _ ρ, _, α => by
    show (fun U i x => α U (𝟙 _ ≫ i) x) = α
    funext U i x
    simp

theorem RawR.map_comp : ∀ (ρ : RTy) {W V U : C} (h : W ⟶ V) (i : V ⟶ U) (x : RawR inner ρ W),
    RawR.map inner ρ (h ≫ i) x = RawR.map inner ρ i (RawR.map inner ρ h x)
  | .t, _, _, _, h, i, X => by
    show {p : Σ V, _ ⟶ V | (⟨p.1, (h ≫ i) ≫ p.2⟩ : Σ V, _ ⟶ V) ∈ X}
      = {p : Σ V, _ ⟶ V | (⟨p.1, h ≫ (i ≫ p.2)⟩ : Σ V, _ ⟶ V) ∈ X}
    ext ⟨V, j⟩
    simp [Category.assoc]
  | .arr _ ρ, _, _, _, h, i, α => by
    show (fun T j x => α T ((h ≫ i) ≫ j) x) = (fun T j x => α T (h ≫ (i ≫ j)) x)
    funext T j x
    simp [Category.assoc]

theorem RawT.map_id : ∀ (σ : Ty) (W : C) (x : RawT inner σ W), RawT.map inner σ (𝟙 W) x = x
  | .e, _, x => by
    show (inner .e).map (𝟙 _) x = x
    rw [Functor.map_id]; rfl
  | .rel ρ, W, x => RawR.map_id inner ρ W x

theorem RawT.map_comp : ∀ (σ : Ty) {W V U : C} (h : W ⟶ V) (i : V ⟶ U) (x : RawT inner σ W),
    RawT.map inner σ (h ≫ i) x = RawT.map inner σ i (RawT.map inner σ h x)
  | .e, _, _, _, h, i, x => by
    show (inner .e).map (h ≫ i) x = (inner .e).map i ((inner .e).map h x)
    rw [Functor.map_comp]; rfl
  | .rel ρ, _, _, _, h, i, x => RawR.map_comp inner ρ h i x

end Outer

/-! ### Environments over a family of domains -/

/-- An assignment: an element of `Dom σ` for each variable of type `σ` in the context,
innermost first. -/
inductive IEnv (Dom : Ty → Type) : Ctx → Type
  /-- The empty assignment. -/
  | nil : IEnv Dom []
  /-- A value for the innermost variable, and the rest. -/
  | cons {Γ : Ctx} {σ : Ty} : Dom σ → IEnv Dom Γ → IEnv Dom (σ :: Γ)

namespace IEnv

variable {Dom Dom' : Ty → Type}

/-- The value of a variable. -/
def get : ∀ {Γ : Ctx} {σ : Ty}, Var Γ σ → IEnv Dom Γ → Dom σ
  | _, _, .zero, .cons x _ => x
  | _, _, .succ v, .cons _ g => get v g

/-- Apply a family of functions to every value. -/
def map (f : ∀ σ, Dom σ → Dom' σ) : ∀ {Γ : Ctx}, IEnv Dom Γ → IEnv Dom' Γ
  | _, .nil => .nil
  | _, .cons x g => .cons (f _ x) (map f g)

@[simp] theorem get_map (f : ∀ σ, Dom σ → Dom' σ) :
    ∀ {Γ : Ctx} {σ : Ty} (v : Var Γ σ) (g : IEnv Dom Γ), (g.map f).get v = f σ (g.get v)
  | _, _, .zero, .cons _ _ => rfl
  | _, _, .succ v, .cons _ g => get_map f v g

end IEnv

/-! ### Action premodels -/

/-- An action premodel for `Sig` on the category `C`: a base object `W₀`; an inner action
for each type, nonempty at `e`; the inclusion of each inner relational domain into the
outer one, natural and injective; the paper's conditions on the inner elements of arrow
type, well-behavedness and values in the inner domain; and a value at the base for each
constant.

The paper asks the category to be *rooted*, every object having an arrow from `W₀`, and
says in a footnote that this "is just a convenience, since [other objects] would make no
difference if they were present". Nothing here uses it, so it is not asked: what holds at
the base is determined by the objects reachable from it, and the *truncation* of a
premodel by an arrow (`ActionFacts.lean`) is then simply the same premodel with a new
base. -/
structure Premodel (Sig : Signature) (C : Type) [SmallCategory C] where
  /-- The base object. -/
  W₀ : C
  /-- The inner action at each type. -/
  inner : Ty → C ⥤ Type
  /-- `W^e` is nonempty. -/
  nonempty_e : ∀ W : C, Nonempty ((inner .e).obj W)
  /-- The subaction: each inner relational domain sits inside the outer one. -/
  incl : ∀ (ρ : RTy) (W : C), (inner (Ty.rel ρ)).obj W → RawR inner ρ W
  /-- The inclusion commutes with the actions. -/
  incl_map : ∀ (ρ : RTy) {W V : C} (h : W ⟶ V) (x : (inner (Ty.rel ρ)).obj W),
    incl ρ V ((inner (Ty.rel ρ)).map h x) = RawR.map inner ρ h (incl ρ W x)
  /-- The inclusion is injective. -/
  incl_injective : ∀ (ρ : RTy) (W : C), Function.Injective (incl ρ W)
  /-- An inner element of arrow type is well-behaved:
  `i^ρ (α ⟨h, x⟩) = α ⟨h ≫ i, i^σ x⟩`. -/
  wellBehaved : ∀ (σ : Ty) (ρ : RTy) {W V U : C} (α : (inner (Ty.rel (.arr σ ρ))).obj W)
    (h : W ⟶ V) (i : V ⟶ U) (x : (inner σ).obj V),
    RawR.map inner ρ i (incl (.arr σ ρ) W α V h x)
      = incl (.arr σ ρ) W α U (h ≫ i) ((inner σ).map i x)
  /-- An inner element of arrow type takes inner values. -/
  app_inner : ∀ (σ : Ty) (ρ : RTy) {W V : C} (α : (inner (Ty.rel (.arr σ ρ))).obj W)
    (h : W ⟶ V) (x : (inner σ).obj V),
    incl (.arr σ ρ) W α V h x ∈ Set.range (incl ρ V)
  /-- The value of each constant, at the root. -/
  I : ∀ c : Sig.Const, (inner (Sig.typeOf c)).obj W₀

namespace Premodel

variable {Sig : Signature} {C : Type} [SmallCategory C] (A : Premodel Sig C)

/-- The inner domain at `W` and `σ`. -/
abbrev Dom (W : C) (σ : Ty) : Type := (A.inner σ).obj W

/-- The inclusion at a type: the identity at `e`. -/
def Incl : ∀ (σ : Ty) (W : C), A.Dom W σ → RawT A.inner σ W
  | .e, _, x => x
  | .rel ρ, W, x => A.incl ρ W x

theorem Incl_map : ∀ (σ : Ty) {W V : C} (h : W ⟶ V) (x : A.Dom W σ),
    A.Incl σ V ((A.inner σ).map h x) = RawT.map A.inner σ h (A.Incl σ W x)
  | .e, _, _, _, _ => rfl
  | .rel ρ, _, _, h, x => A.incl_map ρ h x

theorem Incl_injective : ∀ (σ : Ty) (W : C), Function.Injective (A.Incl σ W)
  | .e, _ => fun _ _ h => h
  | .rel ρ, W => A.incl_injective ρ W

/-- A default outer element, for the one clause where the paper's interpretation is
undefined. -/
noncomputable def dflt : ∀ (σ : Ty) (W : C), RawT A.inner σ W
  | .e, W => Classical.choice (A.nonempty_e W)
  | .rel .t, _ => (∅ : Set _)
  | .rel (.arr _ ρ), _ => fun _ _ _ => dflt (.rel ρ) _

open Classical in
/-- The application of an outer function to an outer argument: the paper's
`⟦A⟧⟨id, ⟦B⟧⟩`, when the argument is inner; the default otherwise. -/
noncomputable def apply {σ : Ty} {ρ : RTy} {W : C}
    (F : RawR A.inner (.arr σ ρ) W) (x : RawT A.inner σ W) : RawR A.inner ρ W :=
  if hx : x ∈ Set.range (A.Incl σ W) then F W (𝟙 W) (Set.mem_range.mp hx).choose
  else A.dflt (.rel ρ) W

/-- Move an assignment along an arrow: `i ∘ g`. -/
abbrev push {W V : C} (i : W ⟶ V) {Γ : Ctx} (g : IEnv (A.Dom W) Γ) : IEnv (A.Dom V) Γ :=
  g.map fun σ => (A.inner σ).map i

/-! ### The readings of the type-subscripted operations

Each mirrors the unfolding `Term.unfoldR` of `Term.lean`, at `t` the clause of the
propositional operation, at `σ → ρ` the reading of the abstraction that unfolds it; so
that the δ-rule preserves the reading. -/

/-- The reading of `¬` at `t`. -/
def notRead (W : C) : RawR A.inner (.arr (.rel .t) .t) W :=
  fun V _ p => (A.incl .t V p)ᶜ

/-- The reading of `∧` at `t`. -/
def andRead (W : C) : RawR A.inner (.arr (.rel .t) (.arr (.rel .t) .t)) W :=
  fun _ _ p U j q => A.incl .t U ((A.inner (.rel .t)).map j p) ∩ A.incl .t U q

/-- The reading of `∨` at `t`. -/
def orRead (W : C) : RawR A.inner (.arr (.rel .t) (.arr (.rel .t) .t)) W :=
  fun _ _ p U j q => A.incl .t U ((A.inner (.rel .t)).map j p) ∪ A.incl .t U q

/-- The reading of `∀σ`: the arrows `j` under which the predicate holds of everything. -/
def allRead (σ : Ty) (W : C) : RawR A.inner (.arr (.rel (.arr σ .t)) .t) W :=
  fun V _ α => {p : Σ U, V ⟶ U | ∀ a : A.Dom p.1 σ, (⟨p.1, 𝟙 p.1⟩ : Σ U, p.1 ⟶ U) ∈ A.incl (.arr σ .t) V α p.1 p.2 a}

/-- The reading of `∃σ`. -/
def exRead (σ : Ty) (W : C) : RawR A.inner (.arr (.rel (.arr σ .t)) .t) W :=
  fun V _ α => {p : Σ U, V ⟶ U | ∃ a : A.Dom p.1 σ, (⟨p.1, 𝟙 p.1⟩ : Σ U, p.1 ⟶ U) ∈ A.incl (.arr σ .t) V α p.1 p.2 a}

/-- The reading of `=σ`: the arrows under which the two elements are identified. -/
def eqRead (σ : Ty) (W : C) : RawR A.inner (.arr σ (.arr σ .t)) W :=
  fun _ _ a U j b => {p : Σ T, U ⟶ T | (A.inner σ).map p.2 ((A.inner σ).map j a) = (A.inner σ).map p.2 b}

/-- The reading of `⊤ := ∀p.p ∨ ¬∀p.p` at `W`, written out. -/
noncomputable def topRead (W : C) : RawR A.inner .t W :=
  let T := A.apply (A.allRead (.rel .t) W) (fun U _ q => A.incl .t U q)
  A.apply (A.apply (A.orRead W) T) (A.apply (A.notRead W) T)

/-- `const_ρ`: at `t`, `λp. p`; at `σ → ρ`, `λp z. const_ρ p`. -/
noncomputable def constRead : ∀ (ρ : RTy) (W : C), RawR A.inner (.arr (.rel .t) ρ) W
  | .t, _ => fun V _ p => A.incl .t V p
  | .arr _ ρ, _ => fun _ _ p U j _ =>
    A.apply (constRead ρ U) (A.incl .t U ((A.inner (.rel .t)).map j p))

/-- `¬_ρ`: at `t`, `¬`; at `σ → ρ`, `λX z. ¬_ρ (X z)`. -/
noncomputable def negRead : ∀ (ρ : RTy) (W : C), RawR A.inner (.arr (.rel ρ) ρ) W
  | .t, W => A.notRead W
  | .arr σ ρ, _ => fun _ _ X U j z =>
    A.apply (negRead ρ U) (A.apply (A.incl (.arr σ ρ) U ((A.inner (.rel (.arr σ ρ))).map j X)) (A.Incl σ U z))

/-- `∧_ρ`: at `t`, `∧`; at `σ → ρ`, `λX Y z. X z ∧_ρ Y z`. -/
noncomputable def andRRead : ∀ (ρ : RTy) (W : C), RawR A.inner (.arr (.rel ρ) (.arr (.rel ρ) ρ)) W
  | .t, W => A.andRead W
  | .arr σ ρ, _ => fun _ _ X _ j Y T k z =>
    A.apply (A.apply (andRRead ρ T)
        (A.apply (A.incl (.arr σ ρ) T ((A.inner (.rel (.arr σ ρ))).map k ((A.inner (.rel (.arr σ ρ))).map j X))) (A.Incl σ T z)))
      (A.apply (A.incl (.arr σ ρ) T ((A.inner (.rel (.arr σ ρ))).map k Y)) (A.Incl σ T z))

/-- `∨_ρ`. -/
noncomputable def orRRead : ∀ (ρ : RTy) (W : C), RawR A.inner (.arr (.rel ρ) (.arr (.rel ρ) ρ)) W
  | .t, W => A.orRead W
  | .arr σ ρ, _ => fun _ _ X _ j Y T k z =>
    A.apply (A.apply (orRRead ρ T)
        (A.apply (A.incl (.arr σ ρ) T ((A.inner (.rel (.arr σ ρ))).map k ((A.inner (.rel (.arr σ ρ))).map j X))) (A.Incl σ T z)))
      (A.apply (A.incl (.arr σ ρ) T ((A.inner (.rel (.arr σ ρ))).map k Y)) (A.Incl σ T z))

/-- Coextensiveness at `ρ`: at `t`, `λp q. p ↔ q`; at `σ → ρ`, `λX Y. ∀z. X z ≡_ρ Y z`. -/
noncomputable def coextRead : ∀ (ρ : RTy) (W : C), RawR A.inner (.arr (.rel ρ) (.arr (.rel ρ) .t)) W
  | .t, _ => fun _ _ p U j q =>
    let P := A.incl .t U ((A.inner (.rel .t)).map j p)
    let Q := A.incl .t U q
    A.apply (A.apply (A.andRead U) (A.apply (A.apply (A.orRead U) (A.apply (A.notRead U) P)) Q))
      (A.apply (A.apply (A.orRead U) (A.apply (A.notRead U) Q)) P)
  | .arr σ ρ, _ => fun _ _ X U j Y =>
    A.apply (A.allRead σ U) fun T k z =>
      A.apply (A.apply (coextRead ρ T)
          (A.apply (A.incl (.arr σ ρ) T ((A.inner (.rel (.arr σ ρ))).map k ((A.inner (.rel (.arr σ ρ))).map j X))) (A.Incl σ T z)))
        (A.apply (A.incl (.arr σ ρ) T ((A.inner (.rel (.arr σ ρ))).map k Y)) (A.Incl σ T z))

/-- `□_ρ`: at `t`, `λp. p = ⊤`; at `σ → ρ`, `λX z. □_ρ (X z)`. -/
noncomputable def boxRead : ∀ (ρ : RTy) (W : C), RawR A.inner (.arr (.rel ρ) ρ) W
  | .t, _ => fun V _ p => A.apply (A.apply (A.eqRead (.rel .t) V) (A.incl .t V p)) (A.topRead V)
  | .arr σ ρ, _ => fun _ _ X U j z =>
    A.apply (boxRead ρ U) (A.apply (A.incl (.arr σ ρ) U ((A.inner (.rel (.arr σ ρ))).map j X)) (A.Incl σ U z))

/-- Pointwise implication at `ρ`: at `t`, `λp q. p → q`; at `σ → ρ`, `λX Y. ∀z. X z ⊑_ρ Y z`. -/
noncomputable def boxImpRead : ∀ (ρ : RTy) (W : C), RawR A.inner (.arr (.rel ρ) (.arr (.rel ρ) .t)) W
  | .t, _ => fun _ _ p U j q =>
    A.apply (A.apply (A.orRead U) (A.apply (A.notRead U) (A.incl .t U ((A.inner (.rel .t)).map j p)))) (A.incl .t U q)
  | .arr σ ρ, _ => fun _ _ X U j Y =>
    A.apply (A.allRead σ U) fun T k z =>
      A.apply (A.apply (boxImpRead ρ T)
          (A.apply (A.incl (.arr σ ρ) T ((A.inner (.rel (.arr σ ρ))).map k ((A.inner (.rel (.arr σ ρ))).map j X))) (A.Incl σ T z)))
        (A.apply (A.incl (.arr σ ρ) T ((A.inner (.rel (.arr σ ρ))).map k Y)) (A.Incl σ T z))

/-! ### The interpretation function -/

/-- The paper's `⟦A⟧^g_h`: the value of a term relative to an arrow `h : W₀ → W` and an
assignment `g` of inner elements at `W`, an outer element at `W`. The nine clauses are the
paper's; the application clause takes the default when the argument's value is not inner,
where the paper's is undefined. -/
noncomputable def sem : ∀ {Γ : Ctx} {σ : Ty} {W : C},
    (A.W₀ ⟶ W) → Term Sig Γ σ → IEnv (A.Dom W) Γ → RawT A.inner σ W
  | _, _, W, _, .var v, g => A.Incl _ W (g.get v)
  | _, _, W, h, .const c, _ => A.Incl _ W ((A.inner _).map h (A.I c))
  | _, _, _, h, .app f a, g => A.apply (sem h f g) (sem h a g)
  | _, _, _, h, .lam b, g => fun _ i x => sem (h ≫ i) b (.cons x (A.push i g))
  | _, _, W, _, .and, _ => A.andRead W
  | _, _, W, _, .or, _ => A.orRead W
  | _, _, W, _, .not, _ => A.notRead W
  | _, _, W, _, .all σ, _ => A.allRead σ W
  | _, _, W, _, .ex σ, _ => A.exRead σ W
  | _, _, W, _, .eq σ, _ => A.eqRead σ W
  | _, _, W, _, .constR ρ, _ => A.constRead ρ W
  | _, _, W, _, .negR ρ, _ => A.negRead ρ W
  | _, _, W, _, .andR ρ, _ => A.andRRead ρ W
  | _, _, W, _, .orR ρ, _ => A.orRRead ρ W
  | _, _, W, _, .coextR ρ, _ => A.coextRead ρ W
  | _, _, W, _, .boxR ρ, _ => A.boxRead ρ W
  | _, _, W, _, .boxImpR ρ, _ => A.boxImpRead ρ W

/-- `A, h, g ⊩ P`: the identity arrow of `W` is in the value of `P`. -/
def Holds {Γ : Ctx} {W : C} (h : A.W₀ ⟶ W) (p : Formula Sig Γ) (g : IEnv (A.Dom W) Γ) : Prop :=
  (⟨W, 𝟙 W⟩ : Σ V, W ⟶ V) ∈ A.sem h p g

/-- A sentence holds in the premodel: at the root, under the identity. -/
def HoldsSentence (p : Sentence Sig) : Prop := A.Holds (𝟙 A.W₀) p .nil

/-- An axiom set holds in the premodel. -/
def HoldsAx (Ax : AxiomSet Sig) : Prop := ∀ a, Ax a → A.HoldsSentence a

/-- **Action model**: the value of every term, relative to every arrow from the root and
every assignment of inner elements, is inner. -/
def IsModel : Prop :=
  ∀ {Γ : Ctx} {σ : Ty} {W : C} (h : A.W₀ ⟶ W) (t : Term Sig Γ σ) (g : IEnv (A.Dom W) Γ),
    A.sem h t g ∈ Set.range (A.Incl σ W)

end Premodel

end Classicism.Meta
