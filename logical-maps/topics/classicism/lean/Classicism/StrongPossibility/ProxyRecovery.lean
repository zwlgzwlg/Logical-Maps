import Classicism.StrongPossibility.ProxyCode

namespace Classicism.Meta.ProxyDiagonal
open CategoryTheory Intensional Term
variable {Sig : Signature} {C : Type} [SmallCategory C]
variable (A : Premodel Sig C)
variable {W T Z L : C}

theorem move_comp {U V : C} (j : W ⟶ V) (k : V ⟶ U) (c : Six (A.Dom W .e)) :
    move A (j ≫ k) c = move A k (move A j c) := by
  cases c
  simp [move, Six.map, Functor.map_comp]

theorem move_id (c : Six (A.Dom W .e)) : move A (𝟙 W) c = c := by
  cases c
  simp [move, Six.map]

theorem old_moves {V : C} (c : Six (A.Dom W .e)) (hc : c.isOld) (j : W ⟶ V) :
    (move A j c).isOld := congrArg ((A.inner Ty.e).map j) hc

/-- A private exit whose composites contain every private successor computes the exact
kernel in the definition of every size tag. -/
theorem kernel_of_private (v : T ⟶ L) (c : Six (A.Dom T .e))
    (hv : (move A v c).isPriv)
    (factor : ∀ {V} (k : T ⟶ V), (move A k c).isPriv → ∃ l : L ⟶ V, k = v ≫ l)
    (x y : A.Dom T .e) : kernel A c x y ↔ (A.inner Ty.e).map v x = (A.inner Ty.e).map v y := by
  refine ⟨fun H => H v hv, ?_⟩
  intro H V k hk
  obtain ⟨l,rfl⟩ := factor k hk
  simp only [Functor.map_comp, types_comp_apply, H]

/-- The existential in Code sees precisely the possibility of the chosen old row.
Factorization is only needed for arrows satisfying the old guard. -/
theorem oldPossible_iff (p : Intension A.inner S W) (j : W ⟶ T) (v : T ⟶ Z)
    (c u : Six (A.Dom T .e)) (hold : (move A v c).isOld)
    (factor : ∀ {V} (k : T ⟶ V), (move A k c).isOld → ∃ l : Z ⟶ V, k = v ≫ l) :
    oldPossible A p j c u ↔ possible A p (j ≫ v) (move A v u) := by
  constructor
  · rintro ⟨V,k,hk,hr⟩
    obtain ⟨l,rfl⟩ := factor k hk
    exact ⟨V,l,by simpa only [move_comp, Category.assoc] using hr⟩
  · rintro ⟨V,l,hr⟩
    refine ⟨V,v ≫ l,?_,?_⟩
    · rw [move_comp]; exact old_moves A _ hold _
    · simpa only [move_comp, Category.assoc] using hr

/-- One physical test site recovers the source code's value on its selected old tuple.
It uses native Code's fixed-row conjunct to remove the last possibility. -/
theorem recover_row (p : Intension A.inner S W) (c : Six (A.Dom W .e))
    (j : W ⟶ T) (v : T ⟶ Z) (u : Six (A.Dom T .e)) (Hcode : isCode A p c)
    (ht : (move A j c).isTest) (htags : tagged A (move A j c) u)
    (hold : (move A v (move A j c)).isOld)
    (factor : ∀ {V} (k : T ⟶ V), (move A k (move A j c)).isOld → ∃ l : Z ⟶ V, k = v ≫ l) :
    (∃ x, Size 7 (kernel A (move A j c) x)) ↔ row A p (j ≫ v) (move A v u) :=
  (Hcode.2 j ht u htags).trans
    ((oldPossible_iff A p j v _ u hold factor).trans (Hcode.1 (j ≫ v) (move A v u)).symm)

/-- The readback is equality of the *whole* old relation when the chosen copies
provide a test for every old arrow and every target tuple. -/
theorem recover_old_profile (p : Intension A.inner S W) (c : Six (A.Dom W .e)) (w : W ⟶ Z)
    (d : Intension A.inner S Z) (hc : isCode A p c)
    (probe : ∀ {V : C} (k : Z ⟶ V) (u : Six (A.Dom V .e)),
      ∃ (T V' : C) (j : W ⟶ T) (v : T ⟶ V') (tup : Six (A.Dom T .e)),
        (move A j c).isTest ∧ tagged A (move A j c) tup ∧
        (move A v (move A j c)).isOld ∧
        (∀ {Y : C} (l : T ⟶ Y), (move A l (move A j c)).isOld → ∃ f : V' ⟶ Y, l = v ≫ f) ∧
        ((∃ x, Size 7 (kernel A (move A j c) x)) ↔ row A d k u) ∧
        (row A p (j ≫ v) (move A v tup) ↔ row A p (w ≫ k) u)) :
    Intension.map A.inner w p = d := by
  apply row_ext A
  intro V k u
  rcases probe k u with ⟨T,V',j,v,tup,ht,hTags,hold,hFactor,hBit,hCopy⟩
  rw [row_map A p w k u]
  exact hCopy.symm.trans ((recover_row A p c j v tup hc ht hTags hold hFactor).symm.trans hBit)

end Classicism.Meta.ProxyDiagonal
