import Classicism.StrongPossibility.ProxyOperator

namespace Classicism.Meta.ProxyDiagonal
open CategoryTheory Intensional Term

variable {Sig : Signature} {C : Type} [SmallCategory C] (A : Premodel Sig C)
variable {W Z : C}

abbrev hasBit (c : Six (A.Dom W .e)) := ∃ x, Size 7 (kernel A c x)

structure Tests (c : Six (A.Dom W .e)) (target : Intension A.inner S W) : Prop where
  start : c.isStart
  isolated : ∀ {V : C} (j : W ⟶ V), (move A j c).isStart →
    ∃ e : V = W, j ≫ eqToHom e = 𝟙 W
  /-- Every test and every admissible choice of its tag representatives returns the
  programmed target bit. -/
  sound : ∀ {T : C} (j : W ⟶ T), (move A j c).isTest →
    ∃ (V : C) (v : T ⟶ V), (move A v (move A j c)).isOld ∧
      (∀ {Y : C} (l : T ⟶ Y), (move A l (move A j c)).isOld → ∃ f : V ⟶ Y, l = v ≫ f) ∧
      ∀ u : Six (A.Dom T .e), tagged A (move A j c) u →
        (hasBit A (move A j c) ↔ row A target (j ≫ v) (move A v u))
  /-- Every tuple at every old address has a probe agreeing on the old rows of all
  admitted input relations. Duplicate old components may be used. -/
  cover : ∀ {Z : C} (w : W ⟶ Z), (move A w c).isOld →
    ∀ {Y : C} (k : Z ⟶ Y) (u : Six (A.Dom Y .e)),
    ∃ (T V : C) (j : W ⟶ T) (v : T ⟶ V) (t : Six (A.Dom T .e)),
      (move A j c).isTest ∧ tagged A (move A j c) t ∧ (move A v (move A j c)).isOld ∧
      (∀ {D : C} (l : T ⟶ D), (move A l (move A j c)).isOld → ∃ f : V ⟶ D, l = v ≫ f) ∧
      (hasBit A (move A j c) ↔ row A target (w ≫ k) u) ∧
      (∀ p : A.Dom W S, row A (A.incl S W p) (j ≫ v) (move A v t) ↔
                            row A (A.incl S W p) (w ≫ k) u)

theorem Tests.passes {c : Six (A.Dom W .e)} {target : Intension A.inner S W}
    (H : Tests A c target) (closed : rowClosed A target) : isCode A target c := by
  refine ⟨closed, ?_⟩
  intro T j hT t ht
  obtain ⟨V,v,hold,hfac,hb⟩ := H.sound j hT
  exact (hb t ht).trans ((closed _ _).trans (oldPossible_iff A target j v _ t hold hfac).symm)

theorem Tests.recovers {c : Six (A.Dom W .e)} {target : Intension A.inner S W}
    (H : Tests A c target) (w : W ⟶ Z) (hw : (move A w c).isOld)
    (p : A.Dom W S) (hp : isCode A (A.incl S W p) c) :
    Intension.map A.inner w (A.incl S W p) = Intension.map A.inner w target := by
  apply recover_old_profile A _ c w _ hp
  intro Y k u
  obtain ⟨T,V,j,v,t,ht,hTags,ho,hFac,hBit,hRows⟩ := H.cover w hw k u
  refine ⟨T,V,j,v,t,ht,hTags,ho,hFac,?_,hRows p⟩
  exact hBit.trans (row_map A target w k u).symm

variable (M : A.IsModel)
include M

theorem holds_rho_d (h : A.W₀ ⟶ W) : A.Holds h (.app rho d) .nil :=
  A.sound M (Ax := AxiomSet.empty) h (fun _ H => H.elim) (Δ := []) rho_d .nil (by
    intro p hp; cases hp)

omit M in
theorem tester_of_d (h : A.W₀ ⟶ W) (w : W ⟶ Z) (f : Term Sig [] Tester) (p : A.Dom W S)
    (hp : A.incl S W p = A.sem h d .nil) :
    A.Holds (h ≫ w) (.app f d) .nil ↔
      testerRow A (A.sem h f .nil) w ((A.inner S).map w p) := by
  have hd : A.Incl S Z ((A.inner S).map w p) = A.sem (h ≫ w) d .nil := by
    change A.incl S Z ((A.inner S).map w p) = A.sem (h ≫ w) d (A.push w .nil)
    rw [A.incl_map, hp, A.sem_push]; rfl
  rw [A.holds_app _ _ _ _ hd]
  change (⟨Z,((A.inner S).map w p,PUnit.unit),𝟙 Z⟩ : Tuple A.inner Tester Z) ∈
    A.sem (h ≫ w) f (A.push w .nil) ↔ _
  rw [A.sem_push]
  change (⟨Z,((A.inner S).map w p,PUnit.unit),w ≫ 𝟙 Z⟩ : Tuple A.inner Tester W) ∈
    A.sem h f .nil ↔ _
  rw [Category.comp_id]

theorem row_applied_Q (h : A.W₀ ⟶ W) (f : Term Sig [] Tester) (c : Six (A.Dom W .e)) :
    row A (A.sem h (.app Q f) .nil) (𝟙 W) c ↔ canFind A (A.sem h f .nil) (𝟙 W) c := by
  obtain ⟨F,hF⟩ := Set.mem_range.mp (M h f .nil)
  change row A (A.apply (A.sem h Q .nil) (A.sem h f .nil)) (𝟙 W) c ↔ _
  rw [A.apply_eq _ hF, ← hF]
  exact row_Q A M h F (𝟙 W) c

/-- The native Q applied to the marked term contains the distinguished tuple, while
the diagonal d omits the same tuple. -/
theorem separates_at (h : A.W₀ ⟶ W) (c : Six (A.Dom W .e))
    (G : Tests A c (A.sem h d .nil)) (f : Term Sig [] Tester) (w : W ⟶ Z)
    (hw : (move A w c).isOld) (hf : ¬A.Holds (h ≫ w) (.app f d) .nil) :
    row A (A.sem h (.app Q f) .nil) (𝟙 W) c ∧ ¬row A (A.sem h d .nil) (𝟙 W) c := by
  obtain ⟨D,hD⟩ := Set.mem_range.mp (M h (d (Sig := Sig)) .nil)
  have hDi : A.incl S W D = A.sem h d .nil := hD
  constructor
  · apply (row_applied_Q A M h f c).mpr
    refine ⟨W,𝟙 W,?_,D,?_,Z,w,?_,?_⟩
    · rw [move_id]; exact G.start
    · rw [move_id, hDi]; exact G.passes A (d_closed A M h)
    · rw [move_id]; exact hw
    · simp only [Category.id_comp]
      exact fun H => hf ((tester_of_d A h w f D hDi).mpr H)
  · change ¬ row A (A.sem h (.app Q rho) .nil) (𝟙 W) c
    rw [row_applied_Q A M]
    rintro ⟨V,k,hStart,P,hP,Y,l,hOld,hMiss⟩
    obtain ⟨e,he⟩ := G.isolated k hStart
    subst V
    simp only [eqToHom_refl, Category.comp_id] at he
    subst k
    rw [move_id] at hP hOld
    simp only [Category.id_comp] at hMiss
    have hmap := G.recovers A l hOld P hP
    have hPD : (A.inner S).map l P = (A.inner S).map l D := by
      apply A.incl_injective
      rw [A.incl_map, A.incl_map, hDi]
      exact hmap
    rw [hPD] at hMiss
    exact hMiss ((tester_of_d A h l rho D hDi).mp (holds_rho_d A M (h ≫ l)))

theorem marked_term_separation (h : A.W₀ ⟶ W) (c : Six (A.Dom W .e))
    (G : Tests A c (A.sem h d .nil)) (f : Term Sig [] Tester) (w : W ⟶ Z)
    (hw : (move A w c).isOld) (hf : ¬A.Holds (h ≫ w) (.app f d) .nil) :
    ¬A.Holds h (eq' (.app Q f) d) .nil := by
  obtain ⟨hp,hn⟩ := separates_at A M h c G f w hw hf
  intro H
  exact hn ((A.holds_eq M h .nil _ _).mp H ▸ hp)

end Classicism.Meta.ProxyDiagonal
