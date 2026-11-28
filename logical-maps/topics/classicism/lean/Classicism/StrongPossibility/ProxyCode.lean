import Classicism.StrongPossibility.ProxyReading
import Classicism.StrongPossibility.ProxyFibres

namespace Classicism.Meta.ProxyDiagonal

open CategoryTheory Intensional Term
variable {Sig : Signature} {C : Type} [SmallCategory C]
variable (A : Premodel Sig C) (M : A.IsModel)
variable {W V : C} {Γ : Ctx}

theorem row_map {U : C} (p : Intension A.inner S W) (k : W ⟶ V) (l : V ⟶ U)
    (u : Six (A.Dom U .e)) :
    row A (Intension.map A.inner k p) l u ↔ row A p (k ≫ l) u := Iff.rfl

theorem mem_lamSix (h : A.W₀ ⟶ W) (k : W ⟶ V) (g : IEnv (A.Dom W) Γ)
    (b : Formula Sig (Ctx.block roles Γ)) (u : Six (A.Dom V .e)) :
    row A (A.sem h (lamBlock roles b) g) k u ↔
      A.Holds (h ≫ k) b (bindSix A (A.push k g) u) := by
  dsimp only [row, sixArgs, roles, lamBlock]
  rw [A.mem_sem_lam h g _ u.a0 _ k, A.mem_sem_lam _ _ _ u.a1 _ (𝟙 V),
    A.mem_sem_lam _ _ _ u.b0 _ (𝟙 V), A.mem_sem_lam _ _ _ u.b1 _ (𝟙 V),
    A.mem_sem_lam _ _ _ u.c0 _ (𝟙 V), A.mem_sem_lam _ _ _ u.c1 _ (𝟙 V)]
  simp only [Category.comp_id, A.push_id]
  rfl

theorem row_ext {p q : Intension A.inner S W}
    (H : ∀ {Z : C} (k : W ⟶ Z) (u : Six (A.Dom Z .e)), row A p k u ↔ row A q k u) : p = q := by
  ext ⟨Z,⟨a,b,c,d,e,f,⟨⟩⟩,k⟩
  exact H k ⟨a,b,c,d,e,f⟩

def possible (p : Intension A.inner S W) (k : W ⟶ V) (u : Six (A.Dom V .e)) : Prop :=
  ∃ (Z : C) (l : V ⟶ Z), row A p (k ≫ l) (move A l u)

def rowClosed (p : Intension A.inner S W) : Prop :=
  ∀ {V : C} (k : W ⟶ V) (u : Six (A.Dom V .e)), row A p k u ↔ possible A p k u

include M in
theorem row_diaRows (h : A.W₀ ⟶ W) (k : W ⟶ V) (g : IEnv (A.Dom W) Γ)
    (p : Term Sig Γ S) (u : Six (A.Dom V .e)) :
    row A (A.sem h (diaRows p) g) k u ↔ possible A (A.sem h p g) k u := by
  rw [diaRows, mem_lamSix, A.holds_dia M]
  unfold possible
  apply exists_congr; intro Z
  apply exists_congr; intro l
  rw [holds_atSix, read_push, read_controls, A.sem_push, sem_wkSix, A.sem_push]
  simp only [Outer.map_rel]
  rw [row_map A _ l (𝟙 _) _, Category.comp_id, row_map A _ k l _]

include M in
theorem holds_fixed (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ) (p : Term Sig Γ S) :
    A.Holds h (eq' p (diaRows p)) g ↔ rowClosed A (A.sem h p g) := by
  rw [A.holds_eq M]
  constructor
  · intro H V k u
    calc row A (A.sem h p g) k u ↔ row A (A.sem h (diaRows p) g) k u := by rw [H]
         _ ↔ possible A (A.sem h p g) k u := row_diaRows A M h k g p u
  · intro H
    exact row_ext A fun k u => (H k u).trans (row_diaRows A M h k g p u).symm

def tagged (c v : Six (A.Dom W .e)) : Prop :=
  Size 1 (kernel A c v.a0) ∧ Size 2 (kernel A c v.a1) ∧
  Size 3 (kernel A c v.b0) ∧ Size 4 (kernel A c v.b1) ∧
  Size 5 (kernel A c v.c0) ∧ Size 6 (kernel A c v.c1)

include M in
theorem holds_tags (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ) (c v : Names Sig Γ) :
    A.Holds h (allTags c v) g ↔ tagged A (read A h g c) (read A h g v) := by
  simp only [allTags, A.holds_conj M, holds_tag A M]; rfl

def oldPossible (p : Intension A.inner S W) (k : W ⟶ V) (c v : Six (A.Dom V .e)) : Prop :=
  ∃ (Z : C) (l : V ⟶ Z), (move A l c).isOld ∧ row A p (k ≫ l) (move A l v)

def isCode (p : Intension A.inner S W) (c : Six (A.Dom W .e)) : Prop :=
  rowClosed A p ∧ ∀ {V : C} (k : W ⟶ V), (move A k c).isTest →
    ∀ (v : Six (A.Dom V .e)), tagged A (move A k c) v →
      ((∃ x, Size 7 (kernel A (move A k c) x)) ↔ oldPossible A p k (move A k c) v)

include M in
theorem holds_code (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ) (p : Term Sig Γ S) (c : Names Sig Γ) :
    A.Holds h (code c p) g ↔ isCode A (A.sem h p g) (read A h g c) := by
  unfold code isCode
  rw [A.holds_conj M, holds_fixed A M, A.holds_box M]
  apply and_congr_right; intro _
  apply forall_congr'; intro Z
  apply forall_congr'; intro k
  rw [A.holds_imp M, holds_test A M, read_push, holds_forallSix A M]
  apply imp_congr_right; intro _
  apply forall_congr'; intro u
  rw [A.holds_imp M, holds_tags A M, read_controls, read_wkSix, read_push]
  apply imp_congr_right; intro _
  rw [A.holds_iff M, holds_bit A M, read_wkSix, read_push, A.holds_dia M]
  apply iff_congr Iff.rfl
  unfold oldPossible
  apply exists_congr; intro Z'
  apply exists_congr; intro l
  rw [A.holds_conj M, holds_old A M, read_push, read_wkSix, read_push,
    holds_atSix, read_push, read_controls, A.sem_push, sem_wkSix, A.sem_push]
  simp only [Outer.map_rel]
  rw [row_map A _ l (𝟙 _) _, Category.comp_id, row_map A _ k l _]

end Classicism.Meta.ProxyDiagonal
