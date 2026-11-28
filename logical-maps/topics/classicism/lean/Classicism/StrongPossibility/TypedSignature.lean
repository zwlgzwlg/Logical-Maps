import Classicism.Coalesced.Parameters

/-!
# Adjoining typed parameters to an intensional action model

A new name has a chosen inner value at the base. Its interpretation at an
arrow is the transport of that value. Old terms retain their whole denotation
under every assignment, including under binders.
-/

namespace Classicism.Meta.TypedSignature

open CategoryTheory Intensional

/-- Disjoint union of two free signatures. -/
def sum (Sig Extra : Signature) : Signature where
  Const := Sig.Const ⊕ Extra.Const
  typeOf := Sum.elim Sig.typeOf Extra.typeOf

variable {Sig Extra : Signature}

/-- Read an old term in the extended signature. -/
noncomputable def lift {Γ : Ctx} {σ : Ty} (t : Term Sig Γ σ) : Term (sum Sig Extra) Γ σ :=
  Term.rec (motive := fun Γ σ _ => Term (sum Sig Extra) Γ σ)
    (var := fun v => Term.var v)
    (const := fun c => Term.const (Sig := sum Sig Extra) (.inl c))
    (app := fun _ _ f a => Term.app f a) (lam := fun _ b => Term.lam b)
    (and := Term.and) (or := Term.or) (not := Term.not)
    (all := Term.all) (ex := Term.ex) (eq := Term.eq)
    (constR := Term.constR) (negR := Term.negR) (andR := Term.andR) (orR := Term.orR)
    (coextR := Term.coextR) (boxR := Term.boxR) (inclR := Term.inclR) t

/-- A fresh constant in any context. -/
abbrev fresh {Γ : Ctx} (c : Extra.Const) : Term (sum Sig Extra) Γ (Extra.typeOf c) :=
  Term.const (Sig := sum Sig Extra) (Sum.inr c)

variable {C : Type} [SmallCategory C]

/-- Interpret each new name by its supplied base value. -/
abbrev expand (A : Premodel Sig C) (v : ∀ c : Extra.Const, A.Dom A.W₀ (Extra.typeOf c)) :
    Premodel (sum Sig Extra) C where
  W₀ := A.W₀
  inner := A.inner
  nonempty_e := A.nonempty_e
  incl := A.incl
  incl_map := A.incl_map
  incl_injective := A.incl_injective
  I c := match c with
    | .inl old => A.I old
    | .inr i => v i

/-- Forget the added names in any expanded premodel. -/
abbrev restrict (B : Premodel (sum Sig Extra) C) : Premodel Sig C where
  W₀ := B.W₀
  inner := B.inner
  nonempty_e := B.nonempty_e
  incl := B.incl
  incl_map := B.incl_map
  incl_injective := B.incl_injective
  I c := B.I (.inl c)

theorem restrict_expand (A : Premodel Sig C) (v : ∀ c : Extra.Const, A.Dom A.W₀ (Extra.typeOf c)) :
    restrict (expand (Extra := Extra) A v) = A := rfl

theorem expand_isModel (A : Premodel Sig C) (M : A.IsModel) (v : ∀ c : Extra.Const, A.Dom A.W₀ (Extra.typeOf c)) :
    (expand (Extra := Extra) A v).IsModel :=
  (expand (Extra := Extra) A v).isModel_of_reductAt (Premodel.reductAt_isModel M)

theorem restrict_isModel (B : Premodel (sum Sig Extra) C) (M : B.IsModel) :
    (restrict B).IsModel :=
  (restrict B).isModel_of_reductAt (Premodel.reductAt_isModel M)

private theorem restrict_Incl (B : Premodel (sum Sig Extra) C) (σ : Ty) (W : C)
    (x : B.Dom W σ) : B.Incl σ W x = (restrict B).Incl σ W x := by
  cases σ <;> rfl

private theorem restrict_apply (B : Premodel (sum Sig Extra) C) {σ : Ty} {ρ : RTy} {W : C}
    (F : Intension B.inner (.arr σ ρ) W) (x : Outer B.inner σ W) :
    B.apply F x = (restrict B).apply F x := by
  cases σ <;> rfl

/-- Whole denotation commutes with restriction, also for open terms under arbitrary binders. -/
theorem sem_lift (B : Premodel (sum Sig Extra) C) :
    ∀ {Γ : Ctx} {σ : Ty} {W : C} (h : B.W₀ ⟶ W) (t : Term Sig Γ σ)
      (g : IEnv (B.Dom W) Γ), B.sem h (lift (Extra := Extra) t) g = (restrict B).sem h t g
  | _, _, _, _, .var _, _ => restrict_Incl B _ _ _
  | _, _, _, _, .const _, _ => restrict_Incl B _ _ _
  | _, _, _, h, .app f a, g => by
    change B.apply (B.sem h (lift (Extra := Extra) f) g) (B.sem h (lift (Extra := Extra) a) g) = _
    rw [sem_lift B h f g, sem_lift B h a g]
    exact restrict_apply B _ _
  | _, _, _, h, .lam b, g => by
    ext ⟨U, ⟨x, a⟩, k⟩
    change _ ∈ B.sem (h ≫ k) (lift (Extra := Extra) b) (.cons x (B.push k g)) ↔ _
    rw [sem_lift B (h ≫ k) b]
    rfl
  | _, _, _, _, .and, _ | _, _, _, _, .or, _ | _, _, _, _, .not, _
  | _, _, _, _, .all _, _ | _, _, _, _, .ex _, _ | _, _, _, _, .eq _, _
  | _, _, _, _, .constR _, _ | _, _, _, _, .negR _, _ | _, _, _, _, .andR _, _
  | _, _, _, _, .orR _, _ | _, _, _, _, .coextR _, _ | _, _, _, _, .boxR _, _
  | _, _, _, _, .inclR _, _ => rfl

theorem sem_expand_lift (A : Premodel Sig C) (v : ∀ c : Extra.Const, A.Dom A.W₀ (Extra.typeOf c))
    {Γ : Ctx} {σ : Ty} {W : C} (h : A.W₀ ⟶ W) (t : Term Sig Γ σ) (g : IEnv (A.Dom W) Γ) :
    (expand (Extra := Extra) A v).sem h (lift (Extra := Extra) t) g = A.sem h t g :=
  sem_lift (expand (Extra := Extra) A v) h t g

theorem sem_fresh (A : Premodel Sig C) (v : ∀ c : Extra.Const, A.Dom A.W₀ (Extra.typeOf c))
    {Γ : Ctx} {W : C} (h : A.W₀ ⟶ W) (c : Extra.Const) (g : IEnv (A.Dom W) Γ) :
    (expand (Extra := Extra) A v).sem h (fresh c) g =
      A.Incl _ W ((A.inner _).map h (v c)) := by
  change (expand (Extra := Extra) A v).Incl _ W ((A.inner _).map h (v c)) = _
  exact restrict_Incl (expand (Extra := Extra) A v) _ _ _

theorem holds_lift (B : Premodel (sum Sig Extra) C) {Γ : Ctx} {W : C}
    (h : B.W₀ ⟶ W) (p : Formula Sig Γ) (g : IEnv (B.Dom W) Γ) :
    B.Holds h (lift (Extra := Extra) p) g ↔ (restrict B).Holds h p g := by
  unfold Premodel.Holds
  rw [sem_lift]

theorem holdsSentence_lift (B : Premodel (sum Sig Extra) C) (p : Sentence Sig) :
    B.HoldsSentence (lift p) ↔ (restrict B).HoldsSentence p :=
  holds_lift B _ _ _

end Classicism.Meta.TypedSignature
