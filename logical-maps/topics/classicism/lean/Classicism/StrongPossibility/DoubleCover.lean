import Classicism.Semantics.Intensional
import Mathlib.CategoryTheory.Comma.Over.Basic

/-! The individual action of the two-layer model, and reading its lower unary intensions.
An object of `Under W` remembers the whole path from the old base, including the
transport of any parameters. All future arrows in the underlying category remain
available at every such object. -/

namespace Classicism.Meta.StrongPossibility.DoubleCover

open CategoryTheory Intensional

variable {C : Type} [SmallCategory C] {Sig : Signature}
variable (A : Premodel Sig C) {W : C}

abbrev Unary (V : C) := Intension A.inner (Ty.e ⇒ RTy.t) V

def row {V Z : C} (p : Unary A V) (h : V ⟶ Z) (x : A.Dom Z .e) : Prop :=
  (⟨Z, (x, PUnit.unit), h⟩ : Tuple A.inner (Ty.e ⇒ RTy.t) V) ∈ p

def possible {V Z : C} (p : Unary A V) (h : V ⟶ Z) (x : A.Dom Z .e) : Prop :=
  ∃ (Y : C) (k : Z ⟶ Y), row A p (h ≫ k) ((A.inner .e).map k x)

def Fixed {V : C} (p : Unary A V) : Prop :=
  ∀ {Z : C} (h : V ⟶ Z) (x : A.Dom Z .e), row A p h x ↔ possible A p h x

@[simp] theorem row_map {V Y Z : C} (p : Unary A V) (h : V ⟶ Y)
    (k : Y ⟶ Z) (x : A.Dom Z .e) :
    row A (Intension.map A.inner h p) k x ↔ row A p (h ≫ k) x := Iff.rfl

theorem fixed_map {V Y : C} (p : Unary A V) (hp : Fixed A p) (h : V ⟶ Y) :
    Fixed A (Intension.map A.inner h p) := by
  intro Z k x
  simpa only [possible, row_map, Category.assoc] using hp (h ≫ k) x

/-- A twin is available exactly when the lower predicate is false. -/
inductive Copy (available : Prop) where
  | left
  | right (present : available)

private def Copy.tag {p : Prop} : Copy p → Bool
  | .left => false
  | .right _ => true

private def Copy.map {p q : Prop} (keep : p → q) : Copy p → Copy q
  | .left => .left
  | .right present => .right (keep present)

@[simp] private theorem Copy.tag_map {p q : Prop} (keep : p → q) (i : Copy p) :
    (i.map keep).tag = i.tag := by cases i <;> rfl

variable (d : Unary A W)

abbrev bit (z : Under W) (s : A.Dom z.right .e) : Prop := row A d z.hom s

abbrev Upper (z : Under W) := (s : A.Dom z.right .e) × Copy (¬ bit A d z s)

theorem bit_back (hd : Fixed A d) {z y : Under W} (k : z ⟶ y)
    (s : A.Dom z.right .e) :
    bit A d y ((A.inner .e).map k.right s) → bit A d z s := by
  intro h
  apply (hd z.hom s).2
  exact ⟨y.right, k.right, by simpa only [Under.w] using h⟩

/-- Transport keeps the tag. Falsity persists because the predicate is possibility-fixed. -/
def upperMap (hd : Fixed A d) {z y : Under W} (k : z ⟶ y) (u : Upper A d z) :
    Upper A d y := ⟨(A.inner .e).map k.right u.1, u.2.map (mt (bit_back A d hd k u.1))⟩

private theorem upperMap_tag (hd : Fixed A d) {z y : Under W} (k : z ⟶ y)
    (u : Upper A d z) : (upperMap A d hd k u).2.tag = u.2.tag :=
  Copy.tag_map _ _

private theorem upper_ext {z : Under W} {u v : Upper A d z}
    (base : u.1 = v.1) (tag : u.2.tag = v.2.tag) : u = v := by
  obtain ⟨s,i⟩ := u
  obtain ⟨t,j⟩ := v
  change s = t at base
  subst t
  cases i <;> cases j <;> simp_all [Copy.tag]

def upper (hd : Fixed A d) : Under W ⥤ Type where
  obj z := Upper A d z
  map k := ↾(upperMap A d hd k)
  map_id z := by
    apply ConcreteCategory.hom_ext; intro u
    apply upper_ext A d
    · exact (A.inner .e).map_id_apply z.right u.1
    · exact upperMap_tag A d hd (𝟙 z) u
  map_comp k l := by
    apply ConcreteCategory.hom_ext; intro u
    apply upper_ext A d
    · exact (A.inner .e).map_comp_apply k.right l.right u.1
    · exact (upperMap_tag A d hd (k ≫ l) u).trans
        ((upperMap_tag A d hd l (upperMap A d hd k u)).trans (upperMap_tag A d hd k u)).symm

abbrev lower : Under W ⥤ Type := Under.forget W ⋙ A.inner .e

/-- The two layers and their vertical arrows form a natural transformation. -/
noncomputable def vertical (hd : Fixed A d) : upper A d hd ⟶ lower A (W := W) where
  app _ := ↾Sigma.fst
  naturality _ _ _ := rfl

/-- The old predicate is false precisely when the given representative has a twin. -/
theorem twin_iff {z : Under W} (u : Upper A d z) :
    (∃ y : Upper A d z, u ≠ y ∧ u.1 = y.1) ↔ ¬ bit A d z u.1 := by
  obtain ⟨s,i⟩ := u
  constructor
  · rintro ⟨⟨t,j⟩, different, same⟩
    change s = t at same
    subst t
    cases i <;> cases j <;> simp_all
  · intro absent
    cases i with
    | left => exact ⟨⟨s,.right absent⟩, by simp, rfl⟩
    | right _ => exact ⟨⟨s,.left⟩, by simp, rfl⟩

end Classicism.Meta.StrongPossibility.DoubleCover
