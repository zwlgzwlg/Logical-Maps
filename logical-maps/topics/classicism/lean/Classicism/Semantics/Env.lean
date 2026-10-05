import Classicism.Syntax.Term

/-!
# Assignments

An assignment gives each variable of a context a value in a family of domains indexed by
type. It is the environment of every semantics of this layer (the reading in `Prop`, the
action models, the intensional action models), and this module holds it and the facts
about it that renaming and substitution need: the assignment a renaming pulls back, and
its behaviour under `lift` and `shift`.
-/

namespace Classicism.Meta

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

theorem ext : ∀ {Γ : Ctx} {g g' : IEnv Dom Γ}, (∀ σ (v : Var Γ σ), g.get v = g'.get v) → g = g'
  | [], .nil, .nil, _ => rfl
  | _ :: _, .cons x g, .cons x' g', h => by
    have h0 := h _ .zero
    simp only [get] at h0
    rw [h0, ext (fun _ v => h _ (.succ v))]

theorem nil_eq (g : IEnv Dom []) : g = .nil := by cases g; rfl

/-- The assignment with the given values. -/
def ofFun : ∀ {Γ : Ctx}, (∀ σ, Var Γ σ → Dom σ) → IEnv Dom Γ
  | [], _ => .nil
  | _ :: _, f => .cons (f _ .zero) (ofFun fun _ v => f _ (.succ v))

@[simp] theorem get_ofFun : ∀ {Γ : Ctx} (f : ∀ σ, Var Γ σ → Dom σ) {σ : Ty} (v : Var Γ σ),
    (ofFun f).get v = f σ v
  | _, _, _, .zero => rfl
  | _, f, _, .succ v => get_ofFun (fun _ v => f _ (.succ v)) v

/-- The assignment a renaming pulls back. -/
def ren {Γ Δ : Ctx} (r : Ren Γ Δ) (g : IEnv Dom Δ) : IEnv Dom Γ :=
  ofFun fun _ v => g.get (r _ v)

@[simp] theorem get_ren {Γ Δ : Ctx} (r : Ren Γ Δ) (g : IEnv Dom Δ) {σ : Ty} (v : Var Γ σ) :
    (ren r g).get v = g.get (r _ v) :=
  get_ofFun _ v

theorem ren_lift {Γ Δ : Ctx} (r : Ren Γ Δ) {σ : Ty} (x : Dom σ) (g : IEnv Dom Δ) :
    ren (Ren.lift r (σ := σ)) (.cons x g) = .cons x (ren r g) :=
  ext fun _ v => by cases v <;> rfl

theorem ren_shift {Γ : Ctx} {σ : Ty} (x : Dom σ) (g : IEnv Dom Γ) :
    ren (Ren.shift (σ := σ)) (.cons x g) = g :=
  ext fun _ v => by simp [Ren.shift, get]

theorem map_ren {Dom' : Ty → Type} (f : ∀ σ, Dom σ → Dom' σ) {Γ Δ : Ctx} (r : Ren Γ Δ)
    (g : IEnv Dom Δ) : (ren r g).map f = ren r (g.map f) :=
  ext fun _ v => by simp

end IEnv

end Classicism.Meta
