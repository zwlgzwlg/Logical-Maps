import Classicism.StrongPossibility.UnaryReading
import Classicism.StrongPossibility.Layers

/-! Exact native interpretation of the unary reader on the doubled category. -/

namespace Classicism.Meta.StrongPossibility.UnaryLayerReading

open CategoryTheory Intensional DoubleCover UnaryReading
open Layers (Site)

noncomputable section

variable {C : Type} [SmallCategory C] {Sig : Signature}
variable (O : Premodel Sig C) (d : Unary O O.W₀) (hd : Fixed O d)

abbrev π := Under.forget O.W₀
abbrev root : Under O.W₀ := Under.mk (𝟙 O.W₀)
abbrev individual : Layers.Domain (π O) O .e := ⟨upper O d hd, vertical O d hd⟩

abbrev first {z : Under O.W₀} (s : O.Dom z.right .e) : Upper O d z := ⟨s,.left⟩
abbrev second {z : Under O.W₀} (s : O.Dom z.right .e) (absent : ¬ bit O d z s) :
    Upper O d z := ⟨s,.right absent⟩

include hd in
private theorem staysFalse {z v : Under O.W₀} (j : z ⟶ v) {b : O.Dom z.right .e}
    (absent : ¬ bit O d z b) : ¬ bit O d v ((O.inner .e).map j.right b) :=
  fun present => absent (bit_back O d hd j b present)

theorem nonemptyUpper (z : Under O.W₀) : Nonempty (Upper O d z) :=
  (O.nonempty_e z.right).map (first O d)

abbrev Doubled := Layers.model (π O) O (individual O d hd) (root O) (𝟙 O.W₀)
  (nonemptyUpper O d) (first O d)

local notation "P" => Doubled O d hd

abbrev Up (z : Under O.W₀) := Site.upper (π := π O) z
abbrev Lo (z : C) := Site.lower (π := π O) z

theorem distinct {z : Under O.W₀} (s : O.Dom z.right .e) (hs : ¬ bit O d z s) :
    second O d s hs ≠ first O d s := by simp [first, second]

theorem mv_first {z v : Under O.W₀} (j : z ⟶ v) (s : O.Dom z.right .e) :
    mv P (Site.up (π O) j) (first O d s) = first O d (mv O j.right s) := rfl

theorem mv_second {z v : Under O.W₀} (j : z ⟶ v) (s : O.Dom z.right .e) (hs : ¬ bit O d z s) :
    mv P (Site.up (π O) j) (second O d s hs) = second O d (mv O j.right s) (staysFalse O d hd j hs) := rfl

theorem cross_mv {z : Under O.W₀} {Y : C} (k : z.right ⟶ Y) (u : Upper O d z) :
    mv P (Site.cross (π O) k) u = mv O k u.1 := rfl

theorem fibre_iff {z : Under O.W₀} (b : O.Dom z.right .e) (hb : ¬ bit O d z b) (x y : Upper O d z) :
    Fibre P (W := Up O z) (second O d b hb) (first O d b) x y ↔ x.1 = y.1 := by
  constructor
  · intro H
    calc
      x.1 = mv O (𝟙 z.right) x.1 := ((O.inner .e).map_id_apply _ _).symm
      _ = mv O (𝟙 z.right) y.1 := H (Site.cross (π O) (𝟙 z.right)) rfl
      _ = y.1 := (O.inner .e).map_id_apply _ _
  · intro H v k heq
    cases v with
    | lower Y => exact congrArg ((O.inner .e).map (show z.right ⟶ Y from k)) H
    | upper t =>
      exact False.elim (distinct O d (mv O (show z ⟶ t from k).right b) (staysFalse O d hd k hb) heq)

/-- A singleton fibre says yes. An individual with a twin says no. -/
theorem noTwin_iff {z : Under O.W₀} (b : O.Dom z.right .e) (hb : ¬ bit O d z b) (x : Upper O d z) :
    ¬ HasTwin P (W := Up O z) (second O d b hb) (first O d b) x ↔ bit O d z x.1 := by
  have twin : HasTwin P (W := Up O z) (second O d b hb) (first O d b) x ↔ ¬ bit O d z x.1 := by
    refine Iff.trans ?_ (twin_iff O d x)
    unfold HasTwin
    apply exists_congr; intro y
    exact and_congr Iff.rfl (fibre_iff O d hd b hb x y)
  exact (not_congr twin).trans Classical.not_not

theorem lower_row {z : Under O.W₀} (p : (P).Dom (Up O z) S) {Y : C}
    (k : z.right ⟶ Y) (x : O.Dom Y .e) :
    row P ((P).incl S _ p) (Site.cross (π O) k) x ↔ row O (O.incl S _ p.2) k x := Iff.rfl

theorem lower_fixed {z : Under O.W₀} (p : (P).Dom (Up O z) S)
    (hf : Fixed P ((P).incl S _ p)) : Fixed O (O.incl S _ p.2) := by
  intro Y k x
  have h := hf (Site.cross (π O) k) x
  constructor
  · intro H
    obtain ⟨t,j,Hj⟩ := h.1 ((lower_row O d hd p k x).2 H)
    cases t with
    | upper _ => exact PEmpty.elim j
    | lower Z => exact ⟨Z, j, Hj⟩
  · rintro ⟨Z,j,Hj⟩
    exact (lower_row O d hd p k x).1 (h.2 ⟨Lo O Z,Site.down (π O) j,Hj⟩)

private theorem read_iff_possible {z v : Under O.W₀} (j : z ⟶ v) (p : (P).Dom (Up O z) S)
    (b : O.Dom z.right .e) (hb : ¬ bit O d z b) (x : Upper O d v) :
    (∃ (t : Site (π O)) (k : Up O v ⟶ t),
      mv P (Site.up (π O) j ≫ k) (second O d b hb) = mv P (Site.up (π O) j ≫ k) (first O d b) ∧
        row P ((P).incl S _ p) (Site.up (π O) j ≫ k) (mv P k x)) ↔
        possible O (O.incl S _ p.2) j.right x.1 := by
  constructor
  · rintro ⟨t,k,heq,h⟩
    cases t with
    | upper t =>
      exact False.elim (distinct O d (mv O (j ≫ (show v ⟶ t from k)).right b)
        (staysFalse O d hd (j ≫ (show v ⟶ t from k)) hb) heq)
    | lower Z => exact ⟨Z,k,h⟩
  · rintro ⟨Z,k,h⟩
    exact ⟨Lo O Z,Site.cross (π O) k,rfl,h⟩

/-- At any upper start, a code is precisely a possibility-fixed upper predicate whose
entire lower projection equals the old predicate recorded by the cover. -/
theorem isCode_iff {z : Under O.W₀} (b : O.Dom z.right .e) (hb : ¬ bit O d z b) (p : (P).Dom (Up O z) S) :
    IsCode P (W := Up O z) (second O d b hb) (first O d b) ((P).incl S _ p) ↔
      Fixed P ((P).incl S _ p) ∧ O.incl S _ p.2 = Intension.map O.inner z.hom d := by
  constructor
  · rintro ⟨hf,H⟩
    refine ⟨hf, ?_⟩
    ext ⟨Y, ⟨s, ⟨⟩⟩, k⟩
    change row O (O.incl S _ p.2) k s ↔ row O d (z.hom ≫ k) s
    let v := Under.mk (z.hom ≫ k)
    let j : z ⟶ v := Under.homMk k rfl
    let x := first O d (z := v) s
    have test := H (Site.up (π O) j) (distinct O d (z := v) (mv O k b) (staysFalse O d hd j hb)) x
    exact (lower_fixed O d hd p hf k s).trans <|
      (read_iff_possible O d hd j p b hb x).symm.trans
        (test.symm.trans (noTwin_iff O d hd (z := v) (mv O k b) (staysFalse O d hd j hb) x))
  · rintro ⟨hf,heq⟩
    refine ⟨hf,?_⟩
    rintro (v|Z) k hn x
    · let j : z ⟶ v := k
      change ¬ HasTwin P (W := Up O v) (second O d (mv O j.right b) (staysFalse O d hd j hb)) (first O d (mv O j.right b)) x ↔ _
      refine (noTwin_iff O d hd _ (staysFalse O d hd j hb) x).trans (Iff.trans ?_ (read_iff_possible O d hd j p b hb x).symm)
      have e : row O (O.incl S z.right p.2) j.right x.1 = row O d (z.hom ≫ j.right) x.1 :=
        congrArg (fun q : Unary O z.right => row O q j.right x.1) heq
      have step := congrArg (fun h : O.W₀ ⟶ v.right => row O d h x.1) (Under.w j)
      exact Iff.trans (Iff.of_eq (e.trans step).symm) ((lower_fixed O d hd p hf) j.right x.1)
    · exact False.elim (hn rfl)

def OldReject {Z : C} (F : O.Dom Z Tester) (s : O.Dom Z S) : Prop :=
  ∃ (Y : C) (j : Z ⟶ Y), (⟨Y,((O.inner _).map j s,PUnit.unit),j⟩ :
    Tuple O.inner Tester Z) ∉ O.incl Tester _ F

/-- At a pair of distinct markers over one anchor, an arbitrary tester's value is
exactly possible rejection of the recorded lower predicate. -/
theorem canFind_iff {z : Under O.W₀} (b : O.Dom z.right .e) (hb : ¬ bit O d z b) (f : (P).Dom (Up O z) Tester)
    (witness : (P).Dom (Up O z) S)
    (code : IsCode P (W := Up O z) (second O d b hb) (first O d b) ((P).incl S _ witness))
    (hs : O.incl S _ witness.2 = Intension.map O.inner z.hom d) :
    CanFind P ((P).incl Tester _ f) (𝟙 (Up O z)) (first O d b) (second O d b hb)
      ↔ OldReject O f.2 witness.2 := by
  let s := witness.2
  constructor
  · rintro ⟨v,j,hn,p,hcode,t,k,heq,hbad⟩
    cases v with
    | lower Y => exact False.elim (hn rfl)
    | upper v =>
      let J : z ⟶ v := j
      have reads := (isCode_iff O d hd (z := v) (mv O J.right b) (staysFalse O d hd J hb) p).1 hcode
      have peq : p.2 = (O.inner _).map J.right s := by
        apply O.incl_injective S
        exact reads.2.trans <| calc
          Intension.map O.inner v.hom d = Intension.map O.inner (z.hom ≫ J.right) d :=
            congrArg (fun j => Intension.map O.inner j d) (Under.w J).symm
          _ = Intension.map O.inner J.right (Intension.map O.inner z.hom d) :=
            Intension.map_comp O.inner z.hom J.right d
          _ = Intension.map O.inner J.right (O.incl S z.right s) := congrArg _ hs.symm
          _ = O.incl S v.right ((O.inner _).map J.right s) := (O.incl_map S J.right s).symm
      cases t with
      | upper y =>
        exact False.elim (distinct O d (z := y) (mv O (J ≫ (show v ⟶ y from k)).right b)
          (staysFalse O d hd (J ≫ (show v ⟶ y from k)) hb) heq)
      | lower Y =>
        let K : v.right ⟶ Y := k
        refine ⟨Y,J.right ≫ K,?_⟩
        change (⟨Y,((O.inner _).map K p.2,PUnit.unit),
          (𝟙 z.right) ≫ J.right ≫ K⟩ : Tuple O.inner Tester z.right) ∉ O.incl Tester _ f.2 at hbad
        have image : (O.inner (Ty.rel S)).map (J.right ≫ K) s = (O.inner _).map K p.2 := by
          rw [peq,Functor.map_comp]; rfl
        let rejected (x : O.Dom Y S) (l : z.right ⟶ Y) : Prop :=
          (⟨Y,(x,PUnit.unit),l⟩ : Tuple O.inner Tester z.right) ∉ O.incl Tester z.right f.2
        exact (congrArg₂ rejected image (Category.id_comp (J.right ≫ K)).symm).mpr hbad
  · rintro ⟨Y,k,hbad⟩
    have id₁ : mv P (𝟙 (Up O z)) (first O d b) = first O d b :=
      ((P).inner .e).map_id_apply (Up O z) _
    have id₂ : mv P (𝟙 (Up O z)) (second O d b hb) = second O d b hb :=
      ((P).inner .e).map_id_apply (Up O z) _
    refine ⟨Up O z,𝟙 _,?_,witness,?_,Lo O Y,Site.cross (π O) k,?_,?_⟩
    · rw [id₁,id₂]; exact distinct O d (z := z) b hb
    · rw [id₁,id₂]; exact code
    · simp only [Category.id_comp]; rfl
    · simp only [Category.id_comp]
      exact hbad

/-- The concrete marker row in the doubled model evaluates the old tester at the
old predicate, under ordinary possibility. -/
theorem root_row (M : (P).IsModel) (b : O.Dom O.W₀ .e) (hb : ¬ bit O d (root O) b)
    (f : (P).Dom (P).W₀ Tester)
    (witness : (P).Dom (P).W₀ S)
    (code : IsCode P (W := Up O (root O)) (second O d (z := root O) b hb)
      (first O d (z := root O) b) ((P).incl S _ witness))
    (hs : O.incl S _ witness.2 = d) :
    row P (value P (𝟙 _) (first O d b) f) (𝟙 _) (second O d b hb) ↔ OldReject O f.2 witness.2 := by
  refine (row_value P M (𝟙 _) (first O d b) f (𝟙 _) (second O d b hb)).trans ?_
  have m : mv P (𝟙 (P).W₀) (first O d (z := root O) b) = first O d b :=
    ((P).inner .e).map_id_apply _ _
  refine (Iff.of_eq (congrArg (fun marker : (P).Dom (P).W₀ .e =>
    CanFind P ((P).incl Tester _ f) (𝟙 _) marker (second O d b hb)) m)).trans ?_
  exact canFind_iff O d hd (z := root O) b hb f witness code (hs.trans (Intension.map_id O.inner d).symm)

end
end Classicism.Meta.StrongPossibility.UnaryLayerReading
