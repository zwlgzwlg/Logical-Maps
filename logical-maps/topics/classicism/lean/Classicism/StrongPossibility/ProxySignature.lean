import Classicism.StrongPossibility.TypedSignature

/-! The private proxy uses six fresh individual names. This is the six-element
instance of adjoining a typed signature. -/

namespace Classicism.Meta.ProxySignature
open CategoryTheory Intensional

def ControlNames : Signature := ⟨Fin 6, fun _ => Ty.e⟩
abbrev Extended (Sig : Signature) := TypedSignature.sum Sig ControlNames

variable {Sig : Signature} {Γ : Ctx} {σ : Ty}

noncomputable abbrev lift (a : Term Sig Γ σ) : Term (Extended Sig) Γ σ :=
  TypedSignature.lift a

abbrev control (i : Fin 6) : Term (Extended Sig) Γ .e := TypedSignature.fresh (Extra := ControlNames) i

variable {C : Type} [SmallCategory C]

abbrev expand (A : Premodel Sig C) (v : Fin 6 → A.Dom A.W₀ .e) : Premodel (Extended Sig) C :=
  TypedSignature.expand (Extra := ControlNames) A v

abbrev restrict (B : Premodel (Extended Sig) C) : Premodel Sig C := TypedSignature.restrict B

theorem restrict_expand (A : Premodel Sig C) (v : Fin 6 → A.Dom A.W₀ .e) :
    restrict (expand A v) = A := rfl

theorem expand_isModel (A : Premodel Sig C) (M : A.IsModel) (v : Fin 6 → A.Dom A.W₀ .e) :
    (expand A v).IsModel := TypedSignature.expand_isModel (Extra := ControlNames) A M v

theorem restrict_isModel (B : Premodel (Extended Sig) C) (M : B.IsModel) :
    (restrict B).IsModel := TypedSignature.restrict_isModel B M

theorem sem_lift (B : Premodel (Extended Sig) C) {W : C} (h : B.W₀ ⟶ W)
    (t : Term Sig Γ σ) (g : IEnv (B.Dom W) Γ) :
    B.sem h (lift t) g = (restrict B).sem h t g := TypedSignature.sem_lift B h t g

theorem sem_expand_lift (A : Premodel Sig C) (v : Fin 6 → A.Dom A.W₀ .e) {W : C}
    (h : A.W₀ ⟶ W) (t : Term Sig Γ σ) (g : IEnv (A.Dom W) Γ) :
    (expand A v).sem h (lift t) g = A.sem h t g := TypedSignature.sem_expand_lift (Extra := ControlNames) A v h t g

theorem sem_control (A : Premodel Sig C) (v : Fin 6 → A.Dom A.W₀ .e)
    {W : C} (h : A.W₀ ⟶ W) (i : Fin 6) (g : IEnv (A.Dom W) Γ) :
    (expand A v).sem h (control i) g = (A.inner .e).map h (v i) := rfl

theorem holds_lift (B : Premodel (Extended Sig) C) {W : C} (h : B.W₀ ⟶ W)
    (p : Formula Sig Γ) (g : IEnv (B.Dom W) Γ) :
    B.Holds h (lift p) g ↔ (restrict B).Holds h p g := TypedSignature.holds_lift B h p g

theorem sem_expand_truncate (A : Premodel Sig C) {V W : C} (h : A.W₀ ⟶ V)
    (v : Fin 6 → A.Dom V .e) (k : V ⟶ W) (t : Term Sig Γ σ) (g : IEnv (A.Dom W) Γ) :
    (expand (A.truncate h) v).sem k (lift t) g = A.sem (h ≫ k) t g := by
  exact (sem_expand_lift (A.truncate h) v k t g).trans (A.sem_truncate h k t g)

end Classicism.Meta.ProxySignature
