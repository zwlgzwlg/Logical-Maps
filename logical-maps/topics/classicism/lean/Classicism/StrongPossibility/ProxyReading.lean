import Classicism.StrongPossibility.ProxyCounting

namespace Classicism.Meta.ProxyDiagonal

open CategoryTheory Intensional Term
variable {Sig : Signature} {C : Type} [SmallCategory C]
variable (A : Premodel Sig C) (M : A.IsModel)
variable {W : C} {Γ : Ctx}

abbrev read (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ) (c : Names Sig Γ) : Six (A.Dom W .e) :=
  c.map (fun x => A.sem h x g)

abbrev move {V : C} (k : W ⟶ V) (c : Six (A.Dom W .e)) : Six (A.Dom V .e) :=
  c.map ((A.inner Ty.e).map k)

def Six.isStart {α : Type} (c : Six α) := c.a0 ≠ c.a1
def Six.isOld {α : Type} (c : Six α) := c.b0 = c.b1
def Six.isTest {α : Type} (c : Six α) := ¬c.isStart ∧ ¬c.isOld ∧ c.c0 ≠ c.c1
def Six.isPriv {α : Type} (c : Six α) := ¬c.isStart ∧ ¬c.isOld ∧ c.c0 = c.c1

abbrev sixArgs {V : C} (u : Six (A.Dom V .e)) : Args A.inner S V :=
  (u.a0,u.a1,u.b0,u.b1,u.c0,u.c1,PUnit.unit)

abbrev row {V : C} (p : Intension A.inner S W) (k : W ⟶ V) (u : Six (A.Dom V .e)) : Prop :=
  (⟨V, sixArgs A u, k⟩ : Tuple A.inner S W) ∈ p

abbrev bindSix (g : IEnv (A.Dom W) Γ) (c : Six (A.Dom W .e)) : IEnv (A.Dom W) (Ctx.block roles Γ) :=
  .cons c.c1 (.cons c.c0 (.cons c.b1 (.cons c.b0 (.cons c.a1 (.cons c.a0 g)))))

theorem read_weaken {σ : Ty} (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ)
    (x : A.Dom W σ) (c : Names Sig Γ) :
    read A h (.cons x g) (c.map (fun z => z.weaken)) = read A h g c := by
  cases c; simp [read, Six.map, A.sem_weaken]

theorem read_push {V : C} (h : A.W₀ ⟶ W) (k : W ⟶ V) (g : IEnv (A.Dom W) Γ)
    (c : Names Sig Γ) : read A (h ≫ k) (A.push k g) c = move A k (read A h g c) := by
  cases c; simp only [read, move, Six.map, A.sem_push]; rfl

theorem read_controls (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ) (u : Six (A.Dom W .e)) :
    read A h (bindSix A g u) controls = u := by cases u; rfl

theorem sem_wkSix (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ) (u : Six (A.Dom W .e))
    {σ : Ty} (p : Term Sig Γ σ) :
    A.sem h (p.rename (Ren.wkBlock roles)) (bindSix A g u) = A.sem h p g := by
  rw [A.sem_rename]
  congr 1
  apply IEnv.ext
  intro τ v
  simp [IEnv.get_ren, Ren.wkBlock, roles, Ren.comp, Ren.shift, bindSix, IEnv.get, Ren.id]

theorem read_wkSix (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ) (u : Six (A.Dom W .e))
    (c : Names Sig Γ) :
    read A h (bindSix A g u) (c.map (fun x => x.rename (Ren.wkBlock roles))) = read A h g c := by
  cases c; simp [read, Six.map, sem_wkSix]

include M

theorem holds_start (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ) (c : Names Sig Γ) :
    A.Holds h (start c) g ↔ (read A h g c).isStart := by
  rw [start, A.holds_neg M, A.holds_eq M]; rfl

theorem holds_old (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ) (c : Names Sig Γ) :
    A.Holds h (old c) g ↔ (read A h g c).isOld := A.holds_eq M h g _ _

theorem holds_test (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ) (c : Names Sig Γ) :
    A.Holds h (test c) g ↔ (read A h g c).isTest := by
  simp only [test, A.holds_conj M, A.holds_neg M, holds_start A M, holds_old A M, A.holds_eq M]; rfl

theorem holds_priv (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ) (c : Names Sig Γ) :
    A.Holds h (priv c) g ↔ (read A h g c).isPriv := by
  simp only [priv, A.holds_conj M, A.holds_neg M, holds_start A M, holds_old A M, A.holds_eq M]; rfl

omit M in
theorem holds_atSix (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ) (p : Term Sig Γ S)
    (c : Names Sig Γ) : A.Holds h (atSix p c) g ↔ row A (A.sem h p g) (𝟙 W) (read A h g c) := by
  have he {ρ : RTy} (F : Intension A.inner (Ty.e ⇒ ρ) W) (x : A.Dom W .e) :
      A.apply F x = F.app A.inner x := A.apply_Incl F x
  unfold Premodel.Holds atSix
  simp only [Premodel.sem, he, Intension.mem_app]
  dsimp only [row, sixArgs, read, Six.map]
  rw [(A.inner Ty.e).map_id W]
  rfl

theorem holds_forallSix (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ)
    (b : Formula Sig (Ctx.block roles Γ)) :
    A.Holds h (forallBlock roles b) g ↔ ∀ u : Six (A.Dom W .e), A.Holds h b (bindSix A g u) := by
  simp only [roles, forallBlock, A.holds_forall M]
  exact ⟨fun f u => f u.a0 u.a1 u.b0 u.b1 u.c0 u.c1,
    fun f a b c d e s => f ⟨a,b,c,d,e,s⟩⟩

/-- Comparison of one tuple with another at all private successors. -/
def kernel (c : Six (A.Dom W .e)) (x y : A.Dom W .e) : Prop :=
  ∀ {V : C} (k : W ⟶ V), (move A k c).isPriv → (A.inner Ty.e).map k x = (A.inner Ty.e).map k y

theorem holds_tag (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ) (c : Names Sig Γ)
    (x : Term Sig Γ .e) (n : Nat) :
    A.Holds h (tag n c x) g ↔ Size n (kernel A (read A h g c) (A.sem h x g)) := by
  rw [tag, holds_exactly A M]
  apply iff_of_eq; apply congrArg (Size n); funext y; apply propext
  unfold Here
  rw [Premodel.mem_sem_lam, Category.comp_id, A.push_id]
  change A.Holds h (box _) (.cons y g) ↔ _
  rw [A.holds_box M]
  apply forall_congr'; intro V
  apply forall_congr'; intro k
  rw [A.holds_imp M, holds_priv A M, read_push, read_weaken, A.holds_eq M,
    A.sem_push, A.sem_push, A.sem_weaken]
  rfl

theorem holds_bit (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ) (c : Names Sig Γ) :
    A.Holds h (bit c) g ↔ ∃ x, Size 7 (kernel A (read A h g c) x) := by
  simp only [bit, A.holds_exists M, holds_tag A M, read_weaken]
  rfl

end Classicism.Meta.ProxyDiagonal
