import Classicism.StrongPossibility.ProxyRecovery
import Classicism.StrongPossibility.ProxyRussell

namespace Classicism.Meta.ProxyDiagonal
open CategoryTheory Intensional Term
variable {Sig : Signature} {C : Type} [SmallCategory C]
variable (A : Premodel Sig C) (M : A.IsModel)
variable {W V Z : C} {Γ : Ctx}

abbrev testerRow (f : Intension A.inner Tester W) (k : W ⟶ V) (p : A.Dom V S) : Prop :=
  (⟨V,(p,PUnit.unit),k⟩ : Tuple A.inner Tester W) ∈ f

/-- Interpretation of the search initiated by an arbitrary six-tuple. -/
def canFind (f : Intension A.inner Tester W) (j : W ⟶ V) (c : Six (A.Dom V .e)) : Prop :=
  ∃ (Z : C) (k : V ⟶ Z), (move A k c).isStart ∧
    ∃ p : A.Dom Z S, isCode A (A.incl S Z p) (move A k c) ∧
      ∃ (U : C) (l : Z ⟶ U), (move A l (move A k c)).isOld ∧
        ¬testerRow A f (j ≫ k ≫ l) ((A.inner S).map l p)

include M in
theorem holds_search (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ)
    (f : Term Sig Γ Tester) (c : Names Sig Γ) :
    A.Holds h (search f c) g ↔ canFind A (A.sem h f g) (𝟙 W) (read A h g c) := by
  rw [search, A.holds_dia M]
  unfold canFind
  apply exists_congr; intro Z
  apply exists_congr; intro k
  rw [A.holds_conj M, holds_start A M, read_push, A.holds_exists M]
  apply and_congr_right; intro _
  apply exists_congr; intro p
  rw [A.holds_conj M, holds_code A M, read_weaken, read_push]
  apply and_congr_right; intro _
  rw [A.holds_dia M]
  apply exists_congr; intro U
  apply exists_congr; intro l
  rw [A.holds_conj M, holds_old A M, read_push, read_weaken, read_push, A.holds_neg M]
  apply and_congr_right; intro _
  apply not_congr
  rw [A.holds_app _ _ _ _ (a' := (A.inner S).map l p) rfl, A.sem_push, A.sem_weaken, A.sem_push]
  change (⟨U,((A.inner S).map l p,PUnit.unit), k ≫ l ≫ 𝟙 U⟩ : Tuple A.inner Tester W) ∈ A.sem h f g ↔ _
  simp only [testerRow, Category.comp_id, Category.id_comp]

abbrev QValue (h : A.W₀ ⟶ W) (f : A.Dom W Tester) : Intension A.inner S W :=
  (A.sem h Q .nil).app A.inner f

theorem canFind_map (f : Intension A.inner Tester W) (k : W ⟶ V) (c : Six (A.Dom V .e)) :
    canFind A (Intension.map A.inner k f) (𝟙 V) c ↔ canFind A f k c := by
  unfold canFind testerRow
  simp only [Intension.mem_map, Category.id_comp]

set_option maxHeartbeats 600000 in
include M in
theorem row_Q (h : A.W₀ ⟶ W) (f : A.Dom W Tester) (k : W ⟶ V) (u : Six (A.Dom V .e)) :
    row A (QValue A h f) k u ↔ canFind A (A.incl Tester W f) k u := by
  unfold QValue row
  rw [Intension.mem_app]
  dsimp only [Q]
  rw [A.mem_sem_lam h .nil _ ((A.inner _).map k f) (sixArgs A u) k]
  change row A (A.sem (h ≫ k) (lamBlock roles _) (.cons ((A.inner _).map k f) (A.push k .nil))) (𝟙 V) u ↔ _
  rw [mem_lamSix, Category.comp_id, A.push_id, holds_search A M, read_controls, sem_wkSix]
  change canFind A (A.incl Tester V ((A.inner _).map k f)) (𝟙 V) u ↔ _
  rw [A.incl_map]
  exact canFind_map A _ k u

theorem canFind_moves (f : Intension A.inner Tester W) (k : W ⟶ V) (j : V ⟶ Z)
    (c : Six (A.Dom V .e)) (H : canFind A f (k ≫ j) (move A j c)) : canFind A f k c := by
  obtain ⟨U,l,hs,p,hp,Y,m,ho,hf⟩ := H
  refine ⟨U,j ≫ l,?_,p,?_,Y,m,?_,?_⟩
  · simpa only [move_comp] using hs
  · simpa only [move_comp] using hp
  · simpa only [move_comp] using ho
  · simpa only [Category.assoc] using hf

theorem possible_here (p : Intension A.inner S W) (k : W ⟶ V) (u : Six (A.Dom V .e)) (H : row A p k u) :
    possible A p k u := by
  refine ⟨V,𝟙 V,?_⟩
  rw [Category.comp_id, move_id A u]
  exact H

theorem closed_of_search (p : Intension A.inner S W) (f : Intension A.inner Tester W)
    (rows : ∀ {V : C} (k : W ⟶ V) (u : Six (A.Dom V .e)), row A p k u ↔ canFind A f k u) :
    rowClosed A p := by
  intro V k u
  constructor
  · exact possible_here A _ k u
  · rintro ⟨Z,l,H⟩
    exact (rows k u).2 (canFind_moves A _ k l u ((rows _ _).1 H))

include M in
theorem Q_closed (h : A.W₀ ⟶ W) (f : A.Dom W Tester) : rowClosed A (QValue A h f) :=
  closed_of_search A (QValue A h f) (A.incl Tester W f) (row_Q A M h f)

include M in
theorem d_closed (h : A.W₀ ⟶ W) : rowClosed A (A.sem h d .nil) := by
  obtain ⟨f,hf⟩ := Set.mem_range.mp (M h (rho (Sig := Sig)) .nil)
  change rowClosed A (A.apply (A.sem h Q .nil) (A.sem h rho .nil))
  rw [A.apply_eq _ hf]
  exact Q_closed A M h f

end Classicism.Meta.ProxyDiagonal
