import Classicism.Meta.Action

/-!
# Soundness of action models

The appendix "Soundness and completeness of action models for Classicism", the soundness
half, for the derivation system `Derivable` and the eleven identities. The lemmas are the
paper's, in its order: **transport** (`⟦A⟧^{i∘g}_{i∘h} = i^σ ⟦A⟧^g_h`), that renaming and
**substitution** pull an assignment back, **β** and **η** (and δ, by `rfl`), so that
conversion preserves the value; then each rule of `Derivable` preserves holding; then the
eleven identities hold at every arrow and assignment of every action model.

All of it is for an action *model*: the transport lemma's application case is where the
paper uses that `⟦A⟧^g_h` is in the inner domain, and so is well-behaved.
-/

namespace Classicism.Meta

open CategoryTheory

namespace IEnv

variable {Dom : Ty → Type}

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

namespace Premodel

variable {Sig : Signature} {C : Type} [SmallCategory C] (A : Premodel Sig C)

/-! ### Assignments along arrows -/

theorem push_cons {W V : C} (i : W ⟶ V) {Γ : Ctx} {σ : Ty} (x : A.Dom W σ) (g : IEnv (A.Dom W) Γ) :
    A.push i (.cons x g) = .cons ((A.inner σ).map i x) (A.push i g) := rfl

theorem push_id {W : C} {Γ : Ctx} (g : IEnv (A.Dom W) Γ) : A.push (𝟙 W) g = g :=
  IEnv.ext fun _ v => by
    simp only [push, IEnv.get_map]
    rw [Functor.map_id]; rfl

theorem push_push {W V U : C} (i : W ⟶ V) (j : V ⟶ U) {Γ : Ctx} (g : IEnv (A.Dom W) Γ) :
    A.push j (A.push i g) = A.push (i ≫ j) g :=
  IEnv.ext fun _ v => by
    simp only [push, IEnv.get_map]
    rw [Functor.map_comp]; rfl

theorem push_ren {W V : C} (i : W ⟶ V) {Γ Δ : Ctx} (r : Ren Γ Δ) (g : IEnv (A.Dom W) Δ) :
    A.push i (IEnv.ren r g) = IEnv.ren r (A.push i g) :=
  IEnv.map_ren _ r g

/-! ### Application at an inner argument -/

theorem apply_Incl {σ : Ty} {ρ : RTy} {W : C} (F : RawR A.inner (.arr σ ρ) W) (x : A.Dom W σ) :
    A.apply F (A.Incl σ W x) = F W (𝟙 W) x := by
  have hx : A.Incl σ W x ∈ Set.range (A.Incl σ W) := ⟨x, rfl⟩
  rw [apply, dif_pos hx]
  congr 1
  exact A.Incl_injective σ W (Set.mem_range.mp hx).choose_spec

theorem apply_eq {σ : Ty} {ρ : RTy} {W : C} (F : RawR A.inner (.arr σ ρ) W) {x : RawT A.inner σ W}
    {b : A.Dom W σ} (hb : A.Incl σ W b = x) : A.apply F x = F W (𝟙 W) b := by
  subst hb; exact A.apply_Incl F b

/-- An outer function of the form `i^[σ→ρ] (incl α)`, applied to `i^σ b`, is `i^ρ` of the
application: well-behavedness, in the form the transport lemma's application case needs. -/
theorem apply_map {σ : Ty} {ρ : RTy} {W V : C} (i : W ⟶ V) (α : A.Dom W (.rel (.arr σ ρ)))
    (b : A.Dom W σ) :
    A.apply (RawR.map A.inner (.arr σ ρ) i (A.incl (.arr σ ρ) W α))
        (RawT.map A.inner σ i (A.Incl σ W b))
      = RawR.map A.inner ρ i (A.apply (A.incl (.arr σ ρ) W α) (A.Incl σ W b)) := by
  rw [← A.Incl_map, apply_Incl, apply_Incl, A.wellBehaved]
  show A.incl (.arr σ ρ) W α V (i ≫ 𝟙 V) _ = A.incl (.arr σ ρ) W α V (𝟙 W ≫ i) _
  rw [Category.comp_id, Category.id_comp]

/-! ### Transport: `⟦A⟧^{i∘g}_{i∘h} = i^σ ⟦A⟧^g_h` -/

theorem sem_push (M : A.IsModel) : ∀ {Γ : Ctx} {σ : Ty} {W : C} (h : A.W₀ ⟶ W) (t : Term Sig Γ σ)
    (g : IEnv (A.Dom W) Γ) {V : C} (i : W ⟶ V),
    A.sem (h ≫ i) t (A.push i g) = RawT.map A.inner σ i (A.sem h t g)
  | _, _, _, _, .var v, g, _, i => by
    simp only [sem, push, IEnv.get_map]
    rw [A.Incl_map]
  | _, _, _, h, .const c, _, _, i => by
    show A.Incl _ _ ((A.inner _).map (h ≫ i) (A.I c)) = RawT.map A.inner _ i (A.Incl _ _ ((A.inner _).map h (A.I c)))
    rw [Functor.map_comp, ← A.Incl_map]; rfl
  | _, _, W, h, .app f a, g, _, i => by
    show A.apply (A.sem (h ≫ i) f (A.push i g)) (A.sem (h ≫ i) a (A.push i g))
      = RawR.map A.inner _ i (A.apply (A.sem h f g) (A.sem h a g))
    rw [sem_push M h f g i, sem_push M h a g i]
    obtain ⟨α, hα⟩ := Set.mem_range.mp (M h f g)
    obtain ⟨b, hb⟩ := Set.mem_range.mp (M h a g)
    rw [← hα, ← hb]
    exact A.apply_map i α b
  | _, _, _, h, .lam b, g, _, i => by
    show (fun U j x => A.sem ((h ≫ i) ≫ j) b (.cons x (A.push j (A.push i g))))
      = (fun U j x => A.sem (h ≫ (i ≫ j)) b (.cons x (A.push (i ≫ j) g)))
    funext U j x
    rw [Category.assoc, A.push_push]
  | _, _, _, _, .and, _, _, _ | _, _, _, _, .or, _, _, _ | _, _, _, _, .not, _, _, _
  | _, _, _, _, .all _, _, _, _ | _, _, _, _, .ex _, _, _, _ | _, _, _, _, .eq _, _, _, _ => rfl
  | _, _, _, _, .constR ρ, _, _, _ => by cases ρ <;> rfl
  | _, _, _, _, .negR ρ, _, _, _ => by cases ρ <;> rfl
  | _, _, _, _, .andR ρ, _, _, _ => by cases ρ <;> rfl
  | _, _, _, _, .orR ρ, _, _, _ => by cases ρ <;> rfl
  | _, _, _, _, .coextR ρ, _, _, _ => by cases ρ <;> rfl
  | _, _, _, _, .boxR ρ, _, _, _ => by cases ρ <;> rfl
  | _, _, _, _, .boxImpR ρ, _, _, _ => by cases ρ <;> rfl

/-! ### Renaming and substitution pull an assignment back -/

theorem sem_rename : ∀ {Γ Δ : Ctx} (r : Ren Γ Δ) {σ : Ty} {W : C} (h : A.W₀ ⟶ W) (t : Term Sig Γ σ)
    (g : IEnv (A.Dom W) Δ), A.sem h (t.rename r) g = A.sem h t (IEnv.ren r g)
  | _, _, r, _, _, h, .var v, g => by
    show A.Incl _ _ (g.get (r _ v)) = A.Incl _ _ ((IEnv.ren r g).get v)
    rw [IEnv.get_ren]
  | _, _, _, _, _, _, .const _, _ | _, _, _, _, _, _, .and, _ | _, _, _, _, _, _, .or, _
  | _, _, _, _, _, _, .not, _ | _, _, _, _, _, _, .all _, _ | _, _, _, _, _, _, .ex _, _
  | _, _, _, _, _, _, .eq _, _ | _, _, _, _, _, _, .constR _, _ | _, _, _, _, _, _, .negR _, _
  | _, _, _, _, _, _, .andR _, _ | _, _, _, _, _, _, .orR _, _ | _, _, _, _, _, _, .coextR _, _
  | _, _, _, _, _, _, .boxR _, _ | _, _, _, _, _, _, .boxImpR _, _ => rfl
  | _, _, r, _, _, h, .app f a, g => by
    show A.apply (A.sem h (f.rename r) g) (A.sem h (a.rename r) g) = _
    rw [sem_rename r h f g, sem_rename r h a g]; rfl
  | _, _, r, _, _, h, .lam b, g => by
    show (fun U j x => A.sem (h ≫ j) (b.rename (Ren.lift r)) (.cons x (A.push j g)))
      = (fun U j x => A.sem (h ≫ j) b (.cons x (A.push j (IEnv.ren r g))))
    funext U j x
    rw [sem_rename (Ren.lift r) (h ≫ j) b, IEnv.ren_lift, A.push_ren]

theorem sem_weaken {Γ : Ctx} {σ τ : Ty} {W : C} (h : A.W₀ ⟶ W) (t : Term Sig Γ σ)
    (x : A.Dom W τ) (g : IEnv (A.Dom W) Γ) :
    A.sem h (t.weaken (τ := τ)) (.cons x g) = A.sem h t g := by
  rw [Term.weaken, A.sem_rename, IEnv.ren_shift]

theorem sem_close {Γ : Ctx} {σ : Ty} {W : C} (h : A.W₀ ⟶ W) (a : Term Sig [] σ)
    (g : IEnv (A.Dom W) Γ) : A.sem h a.close g = A.sem h a .nil := by
  rw [Term.close, A.sem_rename, IEnv.nil_eq (IEnv.ren _ g)]

/-- The assignment a substitution pulls back: the inner element each substituted term
denotes, which the model condition provides. -/
noncomputable def subEnv (M : A.IsModel) {Γ Δ : Ctx} {W : C} (h : A.W₀ ⟶ W) (s : Sub Sig Γ Δ)
    (g : IEnv (A.Dom W) Δ) : IEnv (A.Dom W) Γ :=
  IEnv.ofFun fun σ v => (Set.mem_range.mp (M h (s σ v) g)).choose

theorem Incl_subEnv_get (M : A.IsModel) {Γ Δ : Ctx} {W : C} (h : A.W₀ ⟶ W) (s : Sub Sig Γ Δ)
    (g : IEnv (A.Dom W) Δ) {σ : Ty} (v : Var Γ σ) :
    A.Incl σ W ((A.subEnv M h s g).get v) = A.sem h (s σ v) g := by
  unfold subEnv
  rw [IEnv.get_ofFun]
  exact (Set.mem_range.mp (M h (s σ v) g)).choose_spec

theorem subEnv_lift (M : A.IsModel) {Γ Δ : Ctx} {W : C} (h : A.W₀ ⟶ W) (s : Sub Sig Γ Δ)
    (g : IEnv (A.Dom W) Δ) {σ : Ty} {V : C} (j : W ⟶ V) (x : A.Dom V σ) :
    A.subEnv M (h ≫ j) (Sub.lift s (σ := σ)) (.cons x (A.push j g))
      = .cons x (A.push j (A.subEnv M h s g)) := by
  apply IEnv.ext
  intro τ v
  apply A.Incl_injective
  rw [A.Incl_subEnv_get]
  cases v with
  | zero => rfl
  | succ v =>
    show A.sem (h ≫ j) (s _ v).weaken (.cons x (A.push j g)) = A.Incl _ _ ((A.push j (A.subEnv M h s g)).get v)
    rw [A.sem_weaken, A.sem_push M, push, IEnv.get_map, A.Incl_map, A.Incl_subEnv_get]

theorem sem_subst (M : A.IsModel) : ∀ {Γ Δ : Ctx} (s : Sub Sig Γ Δ) {σ : Ty} {W : C} (h : A.W₀ ⟶ W)
    (t : Term Sig Γ σ) (g : IEnv (A.Dom W) Δ), A.sem h (t.subst s) g = A.sem h t (A.subEnv M h s g)
  | _, _, s, _, _, h, .var v, g => (A.Incl_subEnv_get M h s g v).symm
  | _, _, _, _, _, _, .const _, _ | _, _, _, _, _, _, .and, _ | _, _, _, _, _, _, .or, _
  | _, _, _, _, _, _, .not, _ | _, _, _, _, _, _, .all _, _ | _, _, _, _, _, _, .ex _, _
  | _, _, _, _, _, _, .eq _, _ | _, _, _, _, _, _, .constR _, _ | _, _, _, _, _, _, .negR _, _
  | _, _, _, _, _, _, .andR _, _ | _, _, _, _, _, _, .orR _, _ | _, _, _, _, _, _, .coextR _, _
  | _, _, _, _, _, _, .boxR _, _ | _, _, _, _, _, _, .boxImpR _, _ => rfl
  | _, _, s, _, _, h, .app f a, g => by
    show A.apply (A.sem h (f.subst s) g) (A.sem h (a.subst s) g) = _
    rw [sem_subst M s h f g, sem_subst M s h a g]; rfl
  | _, _, s, _, _, h, .lam b, g => by
    show (fun U j x => A.sem (h ≫ j) (b.subst (Sub.lift s)) (.cons x (A.push j g)))
      = (fun U j x => A.sem (h ≫ j) b (.cons x (A.push j (A.subEnv M h s g))))
    funext U j x
    rw [sem_subst M (Sub.lift s) (h ≫ j) b, A.subEnv_lift M]

theorem sem_instantiate (M : A.IsModel) {Γ : Ctx} {σ τ : Ty} {W : C} (h : A.W₀ ⟶ W)
    (b : Term Sig (σ :: Γ) τ) (a : Term Sig Γ σ) (g : IEnv (A.Dom W) Γ) {a' : A.Dom W σ}
    (ha : A.Incl σ W a' = A.sem h a g) :
    A.sem h (b.instantiate a) g = A.sem h b (.cons a' g) := by
  rw [Term.instantiate, A.sem_subst M]
  congr 1
  apply IEnv.ext
  intro τ v
  apply A.Incl_injective
  rw [A.Incl_subEnv_get]
  cases v with
  | zero => exact ha.symm
  | succ v => rfl

/-! ### Conversion preserves the value -/

theorem sem_beta (M : A.IsModel) {Γ : Ctx} {σ : Ty} {W : C} (h : A.W₀ ⟶ W) {a b : Term Sig Γ σ}
    (hab : Beta a b) (g : IEnv (A.Dom W) Γ) : A.sem h a g = A.sem h b g := by
  cases hab with
  | intro b a =>
    obtain ⟨a', ha⟩ := Set.mem_range.mp (M h a g)
    show A.apply (fun U j x => A.sem (h ≫ j) b (.cons x (A.push j g))) (A.sem h a g) = _
    rw [A.apply_eq _ ha, A.sem_instantiate M h b a g ha, Category.comp_id, A.push_id]

theorem sem_eta (M : A.IsModel) {Γ : Ctx} {σ : Ty} {W : C} (h : A.W₀ ⟶ W) {a b : Term Sig Γ σ}
    (hab : Eta a b) (g : IEnv (A.Dom W) Γ) : A.sem h a g = A.sem h b g := by
  cases hab with
  | intro f =>
    show (fun U j x => A.apply (A.sem (h ≫ j) f.weaken (.cons x (A.push j g))) (A.Incl _ _ x)) = A.sem h f g
    funext U j x
    rw [A.sem_weaken, A.sem_push M, A.apply_Incl]
    show A.sem h f g U (j ≫ 𝟙 U) x = A.sem h f g U j x
    rw [Category.comp_id]

theorem sem_delta : ∀ {Γ : Ctx} {σ : Ty} {a b : Term Sig Γ σ}, Delta a b →
    ∀ {W : C} (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ), A.sem h a g = A.sem h b g
  | _, _, .constR ρ, _, h, _, _, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .negR ρ, _, h, _, _, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .andR ρ, _, h, _, _, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .orR ρ, _, h, _, _, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .coextR ρ, _, h, _, _, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .boxR ρ, _, h, _, _, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .boxImpR ρ, _, h, _, _, _ => by cases ρ <;> cases h <;> rfl
  | _, _, .var _, _, h, _, _, _ | _, _, .const _, _, h, _, _, _ | _, _, .app _ _, _, h, _, _, _
  | _, _, .lam _, _, h, _, _, _ | _, _, .and, _, h, _, _, _ | _, _, .or, _, h, _, _, _
  | _, _, .not, _, h, _, _, _ | _, _, .all _, _, h, _, _, _ | _, _, .ex _, _, h, _, _, _
  | _, _, .eq _, _, h, _, _, _ => nomatch h

theorem sem_step (M : A.IsModel)
    {R : ∀ {Γ : Ctx} {σ : Ty}, Term Sig Γ σ → Term Sig Γ σ → Prop}
    (hR : ∀ {Γ : Ctx} {σ : Ty} {a b : Term Sig Γ σ}, R a b →
      ∀ {W : C} (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ), A.sem h a g = A.sem h b g) :
    ∀ {Γ : Ctx} {σ : Ty} {a b : Term Sig Γ σ}, Step R a b →
      ∀ {W : C} (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ), A.sem h a g = A.sem h b g
  | _, _, _, _, .here hab, _, h, g => hR hab h g
  | _, _, _, _, .appL (f := f) (f' := f') (a := a) hab, _, h, g => by
    show A.apply (A.sem h f g) (A.sem h a g) = A.apply (A.sem h f' g) (A.sem h a g)
    rw [sem_step M hR hab h g]
  | _, _, _, _, .appR (f := f) (a := a) (a' := a') hab, _, h, g => by
    show A.apply (A.sem h f g) (A.sem h a g) = A.apply (A.sem h f g) (A.sem h a' g)
    rw [sem_step M hR hab h g]
  | _, _, _, _, .lam (b := b) (b' := b') hab, _, h, g => by
    show (fun U j x => A.sem (h ≫ j) b (.cons x (A.push j g)))
      = (fun U j x => A.sem (h ≫ j) b' (.cons x (A.push j g)))
    funext U j x
    rw [sem_step M hR hab (h ≫ j) (.cons x (A.push j g))]

theorem sem_conv (M : A.IsModel) {Γ : Ctx} {σ : Ty} {a b : Term Sig Γ σ} (hab : a ≡ b)
    {W : C} (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ) : A.sem h a g = A.sem h b g := by
  induction hab with
  | rel hab => exact A.sem_step M (fun {_ _ _ _} hab {_} h g => hab.elim (fun hb => A.sem_beta M h hb g)
      (fun hab => hab.elim (fun he => A.sem_eta M h he g) (fun hd => A.sem_delta hd h g))) hab h g
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ### The paper's "more helpful form" of the clauses

`A, h, g ⊩ P ∧ Q` iff both, and so on: what each rule of `Derivable` needs. -/

section Holds

variable (M : A.IsModel) {Γ : Ctx} {W : C} (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ)

theorem holds_var (v : Var Γ (.rel .t)) :
    A.Holds h (.var v) g ↔ (⟨W, 𝟙 W⟩ : Σ V, W ⟶ V) ∈ A.incl .t W (g.get v) := Iff.rfl

/-- An application holds iff the function's value contains the identity at the argument's
inner element. -/
theorem holds_app {σ : Ty} (F : Term Sig Γ (σ ⇒ RTy.t)) (a : Term Sig Γ σ) {a' : A.Dom W σ}
    (ha : A.Incl σ W a' = A.sem h a g) :
    A.Holds h (.app F a) g ↔ (⟨W, 𝟙 W⟩ : Σ V, W ⟶ V) ∈ A.sem h F g W (𝟙 W) a' := by
  unfold Holds
  show (⟨W, 𝟙 W⟩ : Σ V, W ⟶ V) ∈ A.apply (σ := σ) (ρ := .t) (A.sem h F g) (A.sem h a g) ↔ _
  rw [A.apply_eq _ ha]

/-- The value of an abstraction at the identity arrow is the value of the body with the
argument. -/
theorem sem_lam_id {σ : Ty} {ρ : RTy} (b : Term Sig (σ :: Γ) ρ) (x : A.Dom W σ) :
    A.sem h (.lam b) g W (𝟙 W) x = A.sem h b (.cons x g) := by
  show A.sem (h ≫ 𝟙 W) b (.cons x (A.push (𝟙 W) g)) = _
  rw [Category.comp_id, A.push_id]

theorem holds_weaken {σ : Ty} (p : Formula Sig Γ) (x : A.Dom W σ) :
    A.Holds h (p.weaken (τ := σ)) (.cons x g) ↔ A.Holds h p g := by
  unfold Holds; rw [A.sem_weaken]

theorem holds_close (a : Sentence Sig) : A.Holds h a.close g ↔ A.Holds h a .nil := by
  unfold Holds; rw [A.sem_close]

include M

/-- Membership of an arbitrary arrow in the value of a formula is holding after transport
along it. -/
theorem mem_sem_iff (p : Formula Sig Γ) {V : C} (k : W ⟶ V) :
    (⟨V, k⟩ : Σ V, W ⟶ V) ∈ A.sem h p g ↔ A.Holds (h ≫ k) p (A.push k g) := by
  unfold Holds
  rw [A.sem_push M]
  show _ ↔ (⟨V, k ≫ 𝟙 V⟩ : Σ V, W ⟶ V) ∈ A.sem h p g
  rw [Category.comp_id]

theorem sem_conj (p q : Formula Sig Γ) : A.sem h (Term.conj p q) g = A.sem h p g ∩ A.sem h q g := by
  obtain ⟨p', hp⟩ := Set.mem_range.mp (M h p g)
  obtain ⟨q', hq⟩ := Set.mem_range.mp (M h q g)
  show A.apply (A.apply (A.andRead W) (A.sem h p g)) (A.sem h q g) = A.sem h p g ∩ A.sem h q g
  rw [← hp, ← hq, A.apply_Incl, A.apply_Incl]
  show A.incl .t W ((A.inner (.rel .t)).map (𝟙 W) p') ∩ A.incl .t W q' = A.incl .t W p' ∩ A.incl .t W q'
  rw [Functor.map_id]; rfl

theorem sem_disj (p q : Formula Sig Γ) : A.sem h (Term.disj p q) g = A.sem h p g ∪ A.sem h q g := by
  obtain ⟨p', hp⟩ := Set.mem_range.mp (M h p g)
  obtain ⟨q', hq⟩ := Set.mem_range.mp (M h q g)
  show A.apply (A.apply (A.orRead W) (A.sem h p g)) (A.sem h q g) = A.sem h p g ∪ A.sem h q g
  rw [← hp, ← hq, A.apply_Incl, A.apply_Incl]
  show A.incl .t W ((A.inner (.rel .t)).map (𝟙 W) p') ∪ A.incl .t W q' = A.incl .t W p' ∪ A.incl .t W q'
  rw [Functor.map_id]; rfl

theorem sem_neg (p : Formula Sig Γ) : A.sem h (Term.neg p) g = (A.sem h p g)ᶜ := by
  obtain ⟨p', hp⟩ := Set.mem_range.mp (M h p g)
  show A.apply (A.notRead W) (A.sem h p g) = (A.sem h p g)ᶜ
  rw [← hp, A.apply_Incl]; rfl

theorem holds_conj (p q : Formula Sig Γ) :
    A.Holds h (Term.conj p q) g ↔ A.Holds h p g ∧ A.Holds h q g := by
  unfold Holds; rw [A.sem_conj M]; exact Set.mem_inter_iff _ _ _

theorem holds_disj (p q : Formula Sig Γ) :
    A.Holds h (Term.disj p q) g ↔ A.Holds h p g ∨ A.Holds h q g := by
  unfold Holds; rw [A.sem_disj M]; exact Set.mem_union _ _ _

theorem holds_neg (p : Formula Sig Γ) : A.Holds h (Term.neg p) g ↔ ¬ A.Holds h p g := by
  unfold Holds; rw [A.sem_neg M]; exact Set.mem_compl_iff _ _

theorem holds_imp (p q : Formula Sig Γ) :
    A.Holds h (Term.imp p q) g ↔ (A.Holds h p g → A.Holds h q g) := by
  rw [Term.imp, A.holds_disj M, A.holds_neg M]; exact imp_iff_not_or.symm

theorem holds_iff (p q : Formula Sig Γ) :
    A.Holds h (Term.iff p q) g ↔ (A.Holds h p g ↔ A.Holds h q g) := by
  rw [Term.iff, A.holds_conj M, A.holds_imp M, A.holds_imp M]; exact iff_def.symm

theorem holds_all {σ : Ty} (F : Term Sig Γ (σ ⇒ RTy.t)) :
    A.Holds h (.app (.all σ) F) g ↔ ∀ a : A.Dom W σ, (⟨W, 𝟙 W⟩ : Σ V, W ⟶ V) ∈ A.sem h F g W (𝟙 W) a := by
  obtain ⟨F', hF⟩ := Set.mem_range.mp (M h F g)
  unfold Holds
  show (⟨W, 𝟙 W⟩ : Σ V, W ⟶ V) ∈ A.apply (A.allRead σ W) (A.sem h F g) ↔ _
  rw [← hF, A.apply_Incl]
  exact Iff.rfl

theorem holds_ex {σ : Ty} (F : Term Sig Γ (σ ⇒ RTy.t)) :
    A.Holds h (.app (.ex σ) F) g ↔ ∃ a : A.Dom W σ, (⟨W, 𝟙 W⟩ : Σ V, W ⟶ V) ∈ A.sem h F g W (𝟙 W) a := by
  obtain ⟨F', hF⟩ := Set.mem_range.mp (M h F g)
  unfold Holds
  show (⟨W, 𝟙 W⟩ : Σ V, W ⟶ V) ∈ A.apply (A.exRead σ W) (A.sem h F g) ↔ _
  rw [← hF, A.apply_Incl]
  exact Iff.rfl

theorem holds_forall {σ : Ty} (b : Formula Sig (σ :: Γ)) :
    A.Holds h (Term.forall' b) g ↔ ∀ a : A.Dom W σ, A.Holds h b (.cons a g) := by
  rw [Term.forall', A.holds_all M]
  simp only [A.sem_lam_id]
  exact Iff.rfl

theorem holds_exists {σ : Ty} (b : Formula Sig (σ :: Γ)) :
    A.Holds h (Term.exists' b) g ↔ ∃ a : A.Dom W σ, A.Holds h b (.cons a g) := by
  rw [Term.exists', A.holds_ex M]
  simp only [A.sem_lam_id]
  exact Iff.rfl

theorem holds_eq {σ : Ty} (a b : Term Sig Γ σ) :
    A.Holds h (Term.eq' a b) g ↔ A.sem h a g = A.sem h b g := by
  obtain ⟨a', ha⟩ := Set.mem_range.mp (M h a g)
  obtain ⟨b', hb⟩ := Set.mem_range.mp (M h b g)
  unfold Holds
  show (⟨W, 𝟙 W⟩ : Σ V, W ⟶ V) ∈ A.apply (A.apply (A.eqRead σ W) (A.sem h a g)) (A.sem h b g)
    ↔ A.sem h a g = A.sem h b g
  rw [← ha, ← hb, A.apply_Incl, A.apply_Incl]
  show (A.inner σ).map (𝟙 W) ((A.inner σ).map (𝟙 W) a') = (A.inner σ).map (𝟙 W) b' ↔ _
  simp only [Functor.map_id, types_id_apply]
  exact ⟨fun e => e ▸ rfl, fun e => A.Incl_injective σ W e⟩

/-- Two formulas that hold together at every arrow and assignment have the same value. -/
theorem sem_eq_of_holds_iff (p q : Formula Sig Γ)
    (hpq : ∀ {V : C} (h : A.W₀ ⟶ V) (g : IEnv (A.Dom V) Γ), A.Holds h p g ↔ A.Holds h q g) :
    A.sem h p g = A.sem h q g := by
  ext ⟨V, k⟩
  rw [A.mem_sem_iff M, A.mem_sem_iff M]
  exact hpq _ _

end Holds

/-! ### Soundness of the rules -/

/-- Every hypothesis holds. -/
def HoldsHyps {Γ : Ctx} {W : C} (h : A.W₀ ⟶ W) (Δ : List (Formula Sig Γ)) (g : IEnv (A.Dom W) Γ) :
    Prop :=
  ∀ q ∈ Δ, A.Holds h q g

theorem holdsHyps_weaken {Γ : Ctx} {W : C} (h : A.W₀ ⟶ W) (Δ : List (Formula Sig Γ)) {σ : Ty}
    (x : A.Dom W σ) (g : IEnv (A.Dom W) Γ) (hΔ : A.HoldsHyps h Δ g) :
    A.HoldsHyps h (Hyps.weaken (σ := σ) Δ) (.cons x g) := by
  intro q hq
  rw [Hyps.weaken, List.mem_map] at hq
  obtain ⟨q', hq', rfl⟩ := hq
  exact (A.holds_weaken h g q' x).2 (hΔ q' hq')

theorem holdsHyps_cons {Γ : Ctx} {W : C} (h : A.W₀ ⟶ W) {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ}
    {g : IEnv (A.Dom W) Γ} (hp : A.Holds h p g) (hΔ : A.HoldsHyps h Δ g) : A.HoldsHyps h (p :: Δ) g := by
  intro q hq
  rcases List.mem_cons.1 hq with rfl | hq
  · exact hp
  · exact hΔ q hq

/-- Filling a hole with terms of the same value at every arrow and assignment gives terms
of the same value. -/
theorem sem_plug_congr : ∀ {Γ Γ' : Ctx} {σ τ : Ty} (K : Hole Sig Γ σ Γ' τ) {a b : Term Sig Γ' τ},
    (∀ {V : C} (h' : A.W₀ ⟶ V) (g' : IEnv (A.Dom V) Γ'), A.sem h' a g' = A.sem h' b g') →
    ∀ {W : C} (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ), A.sem h (K.plug a) g = A.sem h (K.plug b) g
  | _, _, _, _, .hole, _, _, e, _, h, g => e h g
  | _, _, _, _, .appL K c, a, b, e, _, h, g => by
    show A.apply (A.sem h (K.plug a) g) (A.sem h c g) = A.apply (A.sem h (K.plug b) g) (A.sem h c g)
    rw [sem_plug_congr K e h g]
  | _, _, _, _, .appR f K, a, b, e, _, h, g => by
    show A.apply (A.sem h f g) (A.sem h (K.plug a) g) = A.apply (A.sem h f g) (A.sem h (K.plug b) g)
    rw [sem_plug_congr K e h g]
  | _, _, _, _, .lam K, a, b, e, _, h, g => by
    show (fun U i x => A.sem (h ≫ i) (K.plug a) (.cons x (A.push i g)))
      = (fun U i x => A.sem (h ≫ i) (K.plug b) (.cons x (A.push i g)))
    funext U i x
    exact sem_plug_congr K e (h ≫ i) _

/-- Existence at `e` holds at every arrow: the domain of individuals is nonempty. -/
theorem existence_e_holds (M : A.IsModel) {W : C} (h : A.W₀ ⟶ W) :
    A.Holds h (existence_e : Sentence Sig) .nil := by
  rw [existence_e, A.holds_exists M]
  exact ⟨Classical.choice (A.nonempty_e W), (A.holds_eq M h _ _ _).2 rfl⟩

/-- The logical part of any axiom set holds at every arrow. -/
theorem logical_holds (M : A.IsModel) (Ax : AxiomSet Sig) {W : C} (h : A.W₀ ⟶ W) :
    ∀ a, Ax.logical a → A.Holds h a .nil := fun _ ha => by
  rw [show _ = existence_e from ha.2]; exact A.existence_e_holds M h

/-- **Soundness.** In an action model, a derivation from hypotheses holding at an arrow and
assignment, in a theory whose axioms hold at that arrow, has a conclusion holding there. -/
theorem sound (M : A.IsModel) :
    ∀ {Ax : AxiomSet Sig} {W : C} (h : A.W₀ ⟶ W), (∀ a, Ax a → A.Holds h a .nil) →
    ∀ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ}, Derivable Ax Δ p →
      ∀ g : IEnv (A.Dom W) Γ, A.HoldsHyps h Δ g → A.Holds h p g
  | _, _, h, hAx, _, _, _, .hyp hp, _, hΔ => hΔ _ hp
  | _, _, h, hAx, _, _, _, .ax ha, g, _ => (A.holds_close h g _).2 (hAx _ ha)
  | _, _, h, hAx, _, _, _, .andI h₁ h₂, g, hΔ =>
    (A.holds_conj M h g _ _).2 ⟨sound M h hAx h₁ g hΔ, sound M h hAx h₂ g hΔ⟩
  | _, _, h, hAx, _, _, _, .andE₁ h₁, g, hΔ => ((A.holds_conj M h g _ _).1 (sound M h hAx h₁ g hΔ)).1
  | _, _, h, hAx, _, _, _, .andE₂ h₁, g, hΔ => ((A.holds_conj M h g _ _).1 (sound M h hAx h₁ g hΔ)).2
  | _, _, h, hAx, _, _, _, .orI₁ h₁, g, hΔ => (A.holds_disj M h g _ _).2 (Or.inl (sound M h hAx h₁ g hΔ))
  | _, _, h, hAx, _, _, _, .orI₂ h₁, g, hΔ => (A.holds_disj M h g _ _).2 (Or.inr (sound M h hAx h₁ g hΔ))
  | _, _, h, hAx, _, _, _, .orE h₁ h₂ h₃, g, hΔ =>
    ((A.holds_disj M h g _ _).1 (sound M h hAx h₁ g hΔ)).elim
      (fun hp => sound M h hAx h₂ g (A.holdsHyps_cons h hp hΔ))
      (fun hq => sound M h hAx h₃ g (A.holdsHyps_cons h hq hΔ))
  | _, _, h, hAx, _, _, _, .notI h₁ h₂, g, hΔ => (A.holds_neg M h g _).2 fun hp =>
    (A.holds_neg M h g _).1 (sound M h hAx h₂ g (A.holdsHyps_cons h hp hΔ))
      (sound M h hAx h₁ g (A.holdsHyps_cons h hp hΔ))
  | _, _, h, hAx, _, _, _, .notE h₁ h₂, g, hΔ =>
    absurd (sound M h hAx h₁ g hΔ) ((A.holds_neg M h g _).1 (sound M h hAx h₂ g hΔ))
  | _, _, h, hAx, _, _, _, .em p, g, _ =>
    (A.holds_disj M h g _ _).2 ((Classical.em (A.Holds h p g)).imp id (A.holds_neg M h g p).2)
  | _, _, h, hAx, _, _, _, .allE (F := F) h₁ a, g, hΔ => by
    obtain ⟨a', ha⟩ := Set.mem_range.mp (M h a g)
    exact (A.holds_app h g F a ha).2 ((A.holds_all M h g F).1 (sound M h hAx h₁ g hΔ) a')
  | _, _, h, hAx, _, _, _, .allI h₁, g, hΔ => (A.holds_forall M h g _).2 fun a =>
    sound M h hAx h₁ (.cons a g) (A.holdsHyps_weaken h _ a g hΔ)
  | _, _, h, hAx, _, _, _, .exI (F := F) a h₁, g, hΔ => by
    obtain ⟨a', ha⟩ := Set.mem_range.mp (M h a g)
    exact (A.holds_ex M h g F).2 ⟨a', (A.holds_app h g F a ha).1 (sound M h hAx h₁ g hΔ)⟩
  | _, _, h, hAx, _, _, _, .exE (F := F) (r := r) h₁ h₂, g, hΔ => by
    obtain ⟨a, ha⟩ := (A.holds_ex M h g F).1 (sound M h hAx h₁ g hΔ)
    have hF : A.Holds h (.app F.weaken (.var .zero)) (.cons a g) := by
      rw [A.holds_app h (.cons a g) F.weaken (.var .zero) (a' := a) rfl, A.sem_weaken]
      exact ha
    exact (A.holds_weaken h g r a).1
      (sound M h hAx h₂ (.cons a g) (A.holdsHyps_cons h hF (A.holdsHyps_weaken h _ a g hΔ)))
  | _, _, h, hAx, _, _, _, .refl a, g, _ => (A.holds_eq M h g a a).2 rfl
  | _, W, h, hAx, _, _, _, .ll (a := a) (b := b) F h₁ h₂, g, hΔ => by
    have e := (A.holds_eq M h g a b).1 (sound M h hAx h₁ g hΔ)
    have hFa := sound M h hAx h₂ g hΔ
    unfold Holds at hFa ⊢
    show (⟨W, 𝟙 W⟩ : Σ V, W ⟶ V) ∈ A.apply (ρ := .t) (A.sem h F g) (A.sem h b g)
    rw [← e]; exact hFa
  | _, _, h, hAx, _, _, _, .conv h₁ c, g, hΔ => by
    unfold Holds; rw [← A.sem_conv M c]; exact sound M h hAx h₁ g hΔ
  | Ax, _, h, hAx, _, _, _, .subst (P := P) (Q := Q) K h₁ h₂ h₃, g, hΔ => by
    have e : ∀ {V : C} (h' : A.W₀ ⟶ V) (g' : IEnv (A.Dom V) _), A.sem h' P g' = A.sem h' Q g' :=
      fun h' g' => A.sem_eq_of_holds_iff M h' g' P Q fun h'' g'' =>
        ⟨fun hp => sound M h'' (A.logical_holds M Ax h'') h₁ g''
            (fun q hq => by rw [List.mem_singleton.1 hq]; exact hp),
         fun hq => sound M h'' (A.logical_holds M Ax h'') h₂ g''
            (fun q hq' => by rw [List.mem_singleton.1 hq']; exact hq)⟩
    unfold Holds
    rw [← A.sem_plug_congr K e h g]
    exact sound M h hAx h₃ g hΔ

/-- A theorem of a theory holds in every action model of the theory. -/
theorem Theorem.holds (M : A.IsModel) {Ax : AxiomSet Sig} (hAx : A.HoldsAx Ax) {p : Sentence Sig}
    (hp : Theorem Ax p) : A.HoldsSentence p :=
  A.sound M (𝟙 A.W₀) hAx hp .nil (fun _ hq => nomatch hq)

/-! ### The eleven identities hold in every action model

Each is `λ… P = λ… Q` with `P` and `Q` holding together at every arrow and assignment, by
the clauses above; the abstractions then have the same value at every argument. Since
the identities are theorems of `C`, this is a corollary of soundness; it is kept as a
direct check, and as the semantic side of the paper's Appendix A. -/

section Axioms

variable (M : A.IsModel) {W : C} (h : A.W₀ ⟶ W)
include M

theorem holds_eq_lam2 {σ τ : Ty} (b₁ b₂ : Formula Sig [τ, σ])
    (hb : ∀ {V : C} (h : A.W₀ ⟶ V) (g : IEnv (A.Dom V) [τ, σ]), A.Holds h b₁ g ↔ A.Holds h b₂ g) :
    A.Holds h (Term.eq' (.lam (.lam b₁)) (.lam (.lam b₂))) .nil := by
  rw [A.holds_eq M]
  show (fun V i x U j y => A.sem ((h ≫ i) ≫ j) b₁ (.cons y (A.push j (.cons x (A.push i .nil)))))
    = (fun V i x U j y => A.sem ((h ≫ i) ≫ j) b₂ (.cons y (A.push j (.cons x (A.push i .nil)))))
  funext V i x U j y
  exact A.sem_eq_of_holds_iff M _ _ b₁ b₂ hb

theorem holds_eq_lam3 {σ τ υ : Ty} (b₁ b₂ : Formula Sig [υ, τ, σ])
    (hb : ∀ {V : C} (h : A.W₀ ⟶ V) (g : IEnv (A.Dom V) [υ, τ, σ]), A.Holds h b₁ g ↔ A.Holds h b₂ g) :
    A.Holds h (Term.eq' (.lam (.lam (.lam b₁))) (.lam (.lam (.lam b₂)))) .nil := by
  rw [A.holds_eq M]
  show (fun V i x U j y T k z => A.sem (((h ≫ i) ≫ j) ≫ k) b₁
      (.cons z (A.push k (.cons y (A.push j (.cons x (A.push i .nil)))))))
    = (fun V i x U j y T k z => A.sem (((h ≫ i) ≫ j) ≫ k) b₂
      (.cons z (A.push k (.cons y (A.push j (.cons x (A.push i .nil)))))))
  funext V i x U j y T k z
  exact A.sem_eq_of_holds_iff M _ _ b₁ b₂ hb

theorem identities_holds : ∀ a, Meta.C.identities a → A.Holds h a .nil := by
  intro a ha
  cases ha with
  | commutativity_and =>
    apply A.holds_eq_lam2 M h; intro V h g
    rw [A.holds_conj M, A.holds_conj M]; exact And.comm
  | commutativity_or =>
    apply A.holds_eq_lam2 M h; intro V h g
    rw [A.holds_disj M, A.holds_disj M]; exact Or.comm
  | distribution_and_or =>
    apply A.holds_eq_lam3 M h; intro V h g
    rw [A.holds_conj M, A.holds_disj M, A.holds_disj M, A.holds_conj M, A.holds_conj M]
    exact and_or_left
  | distribution_or_and =>
    apply A.holds_eq_lam3 M h; intro V h g
    rw [A.holds_disj M, A.holds_conj M, A.holds_conj M, A.holds_disj M, A.holds_disj M]
    exact or_and_left
  | dissolution_and_or =>
    apply A.holds_eq_lam2 M h; intro V h g
    rw [A.holds_conj M, A.holds_disj M, A.holds_neg M]
    exact and_iff_left (Classical.em _)
  | dissolution_or_and =>
    apply A.holds_eq_lam2 M h; intro V h g
    rw [A.holds_disj M, A.holds_conj M, A.holds_neg M]
    exact or_iff_left (fun ⟨h₁, h₂⟩ => h₂ h₁)
  | identity_identity σ =>
    apply A.holds_eq_lam2 M h; intro V h g
    rw [A.holds_eq M, A.holds_forall M]
    constructor
    · intro e X
      rw [A.holds_iff M, A.holds_app h _ _ _ (a' := g.get (.succ .zero)) rfl,
        A.holds_app h _ _ _ (a' := g.get .zero) rfl]
      have : g.get (.succ .zero) = g.get .zero := A.Incl_injective σ V e
      show _ ↔ (⟨V, 𝟙 V⟩ : Σ U, V ⟶ U) ∈ A.incl _ V X V (𝟙 V) (g.get .zero)
      rw [this]
      exact Iff.rfl
    · intro hX
      -- the predicate "is identical to y", the value of `λw. y = w`, an inner element
      obtain ⟨X, hX'⟩ := Set.mem_range.mp (M h (Term.lam (Term.eq' (Term.v2 : Term Sig [σ, σ, σ] σ) Term.v0)) g)
      have := (A.holds_iff M h _ _ _).1 (hX X)
      rw [A.holds_app h _ _ _ (a' := g.get (.succ .zero)) rfl,
        A.holds_app h _ _ _ (a' := g.get .zero) rfl] at this
      have key : ∀ w : A.Dom V σ, (⟨V, 𝟙 V⟩ : Σ U, V ⟶ U) ∈ A.sem h (.var .zero) (.cons X g) V (𝟙 V) w
          ↔ A.Incl σ V (g.get (.succ .zero)) = A.Incl σ V w := by
        intro w
        show (⟨V, 𝟙 V⟩ : Σ U, V ⟶ U) ∈ A.Incl (.rel (σ ⇒ .t)) V X V (𝟙 V) w ↔ _
        rw [hX', A.sem_lam_id]
        show A.Holds h (Term.eq' Term.v2 Term.v0) (.cons w g) ↔ _
        rw [A.holds_eq M h]
        exact Iff.rfl
      rw [key, key] at this
      exact (this.1 rfl)
  | absorption_or_forall σ =>
    apply A.holds_eq_lam2 M h; intro V h g
    rw [A.holds_disj M, A.holds_all M]
    constructor
    · intro hd
      rcases hd with hd | hd
      · exact hd
      · exact (A.holds_app h g _ _ (a' := g.get .zero) rfl).2 (hd _)
    · exact Or.inl
  | distribution_or_forall σ =>
    apply A.holds_eq_lam2 M h; intro V h g
    rw [A.holds_disj M, A.holds_all M, A.holds_forall M]
    constructor
    · intro hd a
      rw [A.holds_disj M, A.holds_app h _ _ _ (a' := a) rfl]
      rcases hd with hd | hd
      · exact Or.inl hd
      · exact Or.inr (hd a)
    · intro hd
      by_cases hp : A.Holds h (.var .zero) g
      · exact Or.inl hp
      · refine Or.inr fun a => ?_
        have := hd a
        rw [A.holds_disj M, A.holds_app h _ _ _ (a' := a) rfl] at this
        exact this.resolve_left hp
  | absorption_and_exists σ =>
    apply A.holds_eq_lam2 M h; intro V h g
    rw [A.holds_conj M, A.holds_ex M]
    constructor
    · exact And.left
    · intro hd
      exact ⟨hd, g.get .zero, (A.holds_app h g _ _ (a' := g.get .zero) rfl).1 hd⟩
  | distribution_and_exists σ =>
    apply A.holds_eq_lam2 M h; intro V h g
    rw [A.holds_conj M, A.holds_ex M, A.holds_exists M]
    constructor
    · rintro ⟨hp, a, ha⟩
      refine ⟨a, ?_⟩
      rw [A.holds_conj M, A.holds_app h _ _ _ (a' := a) rfl]
      exact ⟨hp, ha⟩
    · rintro ⟨a, ha⟩
      rw [A.holds_conj M, A.holds_app h _ _ _ (a' := a) rfl] at ha
      exact ⟨ha.1, a, ha.2⟩

theorem axioms_holds : ∀ a, Meta.C.axioms a → A.Holds h a .nil := fun _ ha => by
  rw [show _ = existence_e from ha]; exact A.existence_e_holds M h

end Axioms

/-- **Action models are sound for Classicism**: a theorem of `C` holds in every action
model; of `C⁻`, likewise. -/
theorem theorem_holds (M : A.IsModel) {p : Sentence Sig} (hp : Meta.C.Theorem p) : A.HoldsSentence p :=
  A.sound M (𝟙 A.W₀) (A.axioms_holds M _) hp .nil (fun _ hq => nomatch hq)

theorem theoremMinus_holds (M : A.IsModel) {p : Sentence Sig} (hp : Meta.C.TheoremMinus p) :
    A.HoldsSentence p :=
  A.sound M (𝟙 A.W₀) (fun _ h => h.elim) hp .nil (fun _ hq => nomatch hq)

/-- Soundness for `C` extended by an axiom set: what a non-implication on the map needs.
An axiom set holding at every arrow (as a necessitated one does) supports derivations at
every arrow; one holding at the root supports derivations at the root. -/
theorem theoremWith_holds (M : A.IsModel) {Ax : AxiomSet Sig} (hAx : A.HoldsAx Ax)
    {p : Sentence Sig} (hp : Theorem (Meta.C.axioms ∪ Ax) p) : A.HoldsSentence p :=
  A.sound M (𝟙 A.W₀) (fun a ha => ha.elim (A.axioms_holds M _ a) (hAx a)) hp .nil
    (fun _ hq => nomatch hq)

/-- **Entailment transfers holding**: in an action model of `Ax₁`, `Ax₂` holds. So a model
of `Ax₁` refuting a sentence of `Ax₂` shows that `Ax₁` does not entail `Ax₂` — the map's
non-implication records. -/
theorem entails_holds (M : A.IsModel) {Ax₁ Ax₂ : AxiomSet Sig} (e : Ax₁ ⟹ Ax₂)
    (h₁ : A.HoldsAx Ax₁) : A.HoldsAx Ax₂ :=
  fun a ha => A.theoremWith_holds M h₁ (e a ha)

theorem not_entails_of_model (M : A.IsModel) {Ax₁ Ax₂ : AxiomSet Sig} (h₁ : A.HoldsAx Ax₁)
    {a : Sentence Sig} (ha : Ax₂ a) (hn : ¬ A.HoldsSentence a) : ¬ (Ax₁ ⟹ Ax₂) :=
  fun e => hn (A.entails_holds M e h₁ a ha)

end Premodel

end Classicism.Meta
