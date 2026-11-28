import Classicism.StrongPossibility.DoubleCover
import Classicism.StrongPossibility.Unary
import Classicism.Semantics.IntensionalFacts
import Classicism.Syntax.Pure

/-! Native semantics of the actual quoted unary search, in an arbitrary action model. -/

namespace Classicism.Meta.StrongPossibility.UnaryReading

open CategoryTheory Intensional Term DoubleCover
variable {Sig : Signature} {Γ : Ctx}

abbrev S : RTy := Ty.e ⇒ RTy.t
abbrev Tester : RTy := (S : Ty) ⇒ RTy.t
abbrev Family : RTy := Ty.e ⇒ (Tester : Ty) ⇒ S
abbrev Ind (Sig : Signature) (Γ : Ctx) := Term Sig Γ Ty.e

def same (a b x y : Ind Sig Γ) : Formula Sig Γ := box (Term.imp (eq' a b) (eq' x y))

def hasTwin (a b x : Ind Sig Γ) : Formula Sig Γ :=
  exists' (conj (neg (eq' x.weaken v0)) (same a.weaken b.weaken x.weaken v0))

def diaRows (p : Term Sig Γ S) : Term Sig Γ S := .lam (dia (.app p.weaken v0))

def code (a b : Ind Sig Γ) (p : Term Sig Γ S) : Formula Sig Γ :=
  conj (eq' p (diaRows p)) (box (Term.imp (neg (eq' a b)) (forall' (Term.iff (neg (hasTwin a.weaken b.weaken v0))
    (dia (conj (eq' a.weaken b.weaken) (.app p.weaken v0)))))))

def search (b : Ind Sig Γ) (f : Term Sig Γ Tester) (a : Ind Sig Γ) : Formula Sig Γ :=
  dia (conj (neg (eq' a b)) (exists' (conj (code a.weaken b.weaken v0)
    (dia (conj (eq' a.weaken b.weaken) (neg (.app f.weaken v0)))))))

def op : Term Sig [] Family := .lam (.lam (.lam
  (search (.var (.succ (.succ .zero))) v1 v0)))

/-- This direct spelling is definitionally the quotation used in the unary contradiction. -/
theorem op_quoted : (op (Sig := Sig)) = ofPure Classicism.Proofs.UnarySP.operator.term := rfl

variable {C : Type} [SmallCategory C] (A : Premodel Sig C) (M : A.IsModel)
variable {W V : C}

abbrev mv {Y Z : C} (k : Y ⟶ Z) (x : A.Dom Y .e) := (A.inner .e).map k x

def Fibre (a b x y : A.Dom W .e) : Prop :=
  ∀ {Z : C} (k : W ⟶ Z), mv A k a = mv A k b → mv A k x = mv A k y

def HasTwin (a b x : A.Dom W .e) : Prop :=
  ∃ y : A.Dom W .e, x ≠ y ∧ Fibre A a b x y

def IsCode (a b : A.Dom W .e) (p : Unary A W) : Prop :=
  Fixed A p ∧ ∀ {Z : C} (k : W ⟶ Z), mv A k a ≠ mv A k b → ∀ x : A.Dom Z .e,
    ¬ HasTwin A (mv A k a) (mv A k b) x ↔ ∃ (Y : C) (l : Z ⟶ Y),
      mv A (k ≫ l) a = mv A (k ≫ l) b ∧ row A p (k ≫ l) (mv A l x)

def CanFind (f : Intension A.inner Tester W) (j : W ⟶ V) (b a : A.Dom V .e) : Prop :=
  ∃ (Z : C) (k : V ⟶ Z), mv A k a ≠ mv A k b ∧ ∃ p : A.Dom Z S,
    IsCode A (mv A k a) (mv A k b) (A.incl S Z p) ∧ ∃ (Y : C) (l : Z ⟶ Y),
      mv A (k ≫ l) a = mv A (k ≫ l) b ∧
      (⟨Y, ((A.inner S).map l p, PUnit.unit), j ≫ k ≫ l⟩ : Tuple A.inner Tester W) ∉ f

/-- A search cannot distinguish an individual from itself at any continuation. -/
theorem not_canFind_self (f : Intension A.inner Tester W) (j : W ⟶ V) (b : A.Dom V .e) :
    ¬ CanFind A f j b b := fun ⟨_, _, different, _⟩ => different rfl

include M in
theorem holds_same (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ) (a b x y : Ind Sig Γ) :
    A.Holds h (same a b x y) g ↔
      Fibre A (A.sem h a g) (A.sem h b g) (A.sem h x g) (A.sem h y g) := by
  simp only [same, A.holds_box M, A.holds_imp M, A.holds_eq M, A.sem_push, Fibre]
  rfl

include M in
theorem holds_hasTwin (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ) (a b x : Ind Sig Γ) :
    A.Holds h (hasTwin a b x) g ↔ HasTwin A (A.sem h a g) (A.sem h b g) (A.sem h x g) := by
  simp only [hasTwin, A.holds_exists M, A.holds_conj M, A.holds_neg M, A.holds_eq M,
    holds_same A M, A.sem_weaken]
  rfl

theorem holds_at (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ) (p : Term Sig Γ S) (x : Ind Sig Γ) :
    A.Holds h (.app p x) g ↔ row A (A.sem h p g) (𝟙 W) (A.sem h x g) :=
  A.holds_app h g p x (a' := A.sem h x g) rfl

include M in
theorem row_diaRows (h : A.W₀ ⟶ W) (k : W ⟶ V) (g : IEnv (A.Dom W) Γ)
    (p : Term Sig Γ S) (x : A.Dom V .e) :
    row A (A.sem h (diaRows p) g) k x ↔ possible A (A.sem h p g) k x := by
  unfold row diaRows
  rw [A.mem_sem_lam h g _ x _ k]
  change A.Holds (h ≫ k) (dia (.app p.weaken v0)) (.cons x (A.push k g)) ↔ _
  rw [A.holds_dia M]
  apply exists_congr; intro Z
  apply exists_congr; intro l
  rw [holds_at, A.sem_push, A.sem_weaken, A.sem_push, A.sem_push]
  simp only [Outer.map_rel, row_map, Category.comp_id]
  rfl

include M in
theorem holds_fixed (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ) (p : Term Sig Γ S) :
    A.Holds h (eq' p (diaRows p)) g ↔ Fixed A (A.sem h p g) := by
  rw [A.holds_eq M]
  constructor
  · intro e V k x
    calc row A (A.sem h p g) k x ↔ row A (A.sem h (diaRows p) g) k x := by rw [e]
         _ ↔ _ := row_diaRows A M h k g p x
  · intro H
    ext ⟨V,⟨x,⟨⟩⟩,k⟩
    exact (H k x).trans (row_diaRows A M h k g p x).symm

include M in
theorem holds_code (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ) (a b : Ind Sig Γ) (p : Term Sig Γ S) :
    A.Holds h (code a b p) g ↔ IsCode A (A.sem h a g) (A.sem h b g) (A.sem h p g) := by
  rw [code, A.holds_conj M, holds_fixed A M, A.holds_box M]
  unfold IsCode
  apply and_congr_right
  intro _
  apply forall_congr'; intro Z
  apply forall_congr'; intro k
  rw [A.holds_imp M, A.holds_neg M, A.holds_eq M, A.sem_push, A.sem_push, A.holds_forall M]
  apply imp_congr_right
  intro _
  apply forall_congr'; intro x
  rw [A.holds_iff M, A.holds_neg M, holds_hasTwin A M, A.sem_weaken, A.sem_weaken,
    A.sem_push, A.sem_push, A.holds_dia M]
  apply iff_congr Iff.rfl
  apply exists_congr; intro Y
  apply exists_congr; intro l
  rw [A.holds_conj M, A.holds_eq M, holds_at]
  simp only [A.sem_push, A.sem_weaken, Outer.map_rel, row_map, Category.comp_id]
  simp only [mv, Functor.map_comp, types_comp_apply]
  rfl

include M in
theorem holds_search (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ)
    (b : Ind Sig Γ) (f : Term Sig Γ Tester) (a : Ind Sig Γ) :
    A.Holds h (search b f a) g ↔
      CanFind A (A.sem h f g) (𝟙 W) (A.sem h b g) (A.sem h a g) := by
  rw [search, A.holds_dia M]
  unfold CanFind
  apply exists_congr; intro Z
  apply exists_congr; intro k
  rw [A.holds_conj M, A.holds_neg M, A.holds_eq M, A.sem_push, A.sem_push, A.holds_exists M]
  apply and_congr_right; intro _
  apply exists_congr; intro p
  rw [A.holds_conj M, holds_code A M, A.sem_weaken, A.sem_weaken, A.sem_push, A.sem_push,
    A.holds_dia M]
  apply and_congr_right; intro _
  apply exists_congr; intro Y
  apply exists_congr; intro l
  rw [A.holds_conj M, A.holds_eq M, A.holds_neg M,
    A.holds_app _ _ _ _ (a' := (A.inner S).map l p) (by
      rw [A.sem_push]; exact A.incl_map S l p)]
  simp only [A.sem_push, A.sem_weaken, Outer.map_rel, Intension.mem_map, Category.comp_id,
    Category.id_comp, mv, Functor.map_comp, types_comp_apply]
  rfl

/-- The concrete operator applied to two inner arguments. -/
abbrev value (h : A.W₀ ⟶ W) (b : A.Dom W .e) (f : A.Dom W Tester) : Unary A W :=
  ((A.sem h op .nil).app A.inner b).app A.inner f

theorem canFind_map (f : Intension A.inner Tester W) (k : W ⟶ V)
    (a b : A.Dom V .e) :
    CanFind A (Intension.map A.inner k f) (𝟙 V) b a ↔ CanFind A f k b a := by
  simp only [CanFind, Intension.mem_map, Category.id_comp]

include M in
theorem row_value (h : A.W₀ ⟶ W) (b : A.Dom W .e) (f : A.Dom W Tester)
    (k : W ⟶ V) (x : A.Dom V .e) :
    row A (value A h b f) k x ↔ CanFind A (A.incl Tester W f) k (mv A k b) x := by
  simp only [value, row, Intension.mem_app]
  unfold op
  rw [A.mem_sem_lam, A.mem_sem_lam, A.mem_sem_lam]
  simp only [Category.comp_id, A.push_id]
  change A.Holds (h ≫ k) _ (.cons x (.cons ((A.inner _).map k f)
    (.cons (mv A k b) (A.push k .nil)))) ↔ _
  rw [holds_search A M]
  change CanFind A (A.incl Tester _ ((A.inner _).map k f)) _ _ _ ↔ _
  rw [A.incl_map, canFind_map]
  rfl

end Classicism.Meta.StrongPossibility.UnaryReading
