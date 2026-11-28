import Classicism.Semantics.IntensionalFull

/-! A category of upper sites, each with a vertical arrow to its old site.
Lower sites keep exactly their old continuations. -/

namespace Classicism.Meta.StrongPossibility.Layers
open CategoryTheory Intensional
noncomputable section

variable {U C : Type} [SmallCategory U] [SmallCategory C] (π : U ⥤ C)

inductive Site (π : U ⥤ C)
  | upper (u : U)
  | lower (z : C)

namespace Site

abbrev Hom : Site π → Site π → Type
  | .upper u, .upper v => u ⟶ v
  | .upper u, .lower z => π.obj u ⟶ z
  | .lower _, .upper _ => PEmpty
  | .lower z, .lower w => z ⟶ w

def identity : (x : Site π) → Hom π x x
  | .upper u => 𝟙 u
  | .lower z => 𝟙 z

def comp : {x y z : Site π} → Hom π x y → Hom π y z → Hom π x z
  | .upper _, .upper _, .upper _, f, g => f ≫ g
  | .upper _, .upper _, .lower _, f, g => π.map f ≫ g
  | .upper _, .lower _, .lower _, f, g => f ≫ g
  | .lower _, .lower _, .lower _, f, g => f ≫ g
  | .lower _, .upper _, _, f, _ => nomatch f
  | _, .lower _, .upper _, _, g => nomatch g

instance : SmallCategory (Site π) where
  Hom := Hom π
  id := identity π
  comp := comp π
  id_comp := by rintro (_|_) (_|_) f <;> first | exact PEmpty.elim f | simp [identity, comp]
  comp_id := by rintro (_|_) (_|_) f <;> first | exact PEmpty.elim f | simp [identity, comp]
  assoc := by
    rintro (_|_) (_|_) (_|_) (_|_) f g h <;>
      first | exact PEmpty.elim f | exact PEmpty.elim g | exact PEmpty.elim h | simp [comp, Category.assoc]

abbrev up {u v : U} (j : u ⟶ v) : upper (π := π) u ⟶ upper v := j
abbrev down {x y : C} (j : x ⟶ y) : lower (π := π) x ⟶ lower y := j
abbrev cross {u : U} {x : C} (j : π.obj u ⟶ x) : upper (π := π) u ⟶ lower x := j

end Site

variable {Sig : Signature} (O : Premodel Sig C)

/-- The upper domain at a type, with its projection onto the old domain. -/
structure Domain (σ : Ty) where
  upper : U ⥤ Type
  project : upper ⟶ π ⋙ O.inner σ

namespace Domain
variable {π O σ}

private theorem natural_cross (D : Domain π O σ) {u v : U} {z : C} (f : u ⟶ v) (g : π.obj v ⟶ z) :
    D.project.app u ≫ (O.inner σ).map (π.map f ≫ g) = D.upper.map f ≫ D.project.app v ≫ (O.inner σ).map g := by
  rw [Functor.map_comp, ← Category.assoc, ← Functor.comp_map, ← D.project.naturality, Category.assoc]

private theorem cross_lower (D : Domain π O σ) {u : U} {v z : C} (f : π.obj u ⟶ v) (g : v ⟶ z) :
    D.project.app u ≫ (O.inner σ).map (f ≫ g) = (D.project.app u ≫ (O.inner σ).map f) ≫ (O.inner σ).map g := by
  rw [Functor.map_comp, Category.assoc]

def inner (D : Domain π O σ) : Site π ⥤ Type where
  obj
    | .upper u => D.upper.obj u
    | .lower z => O.Dom z σ
  map {x y} f := match x, y with
    | .upper _, .upper _ => D.upper.map f
    | .upper u, .lower _ => D.project.app u ≫ (O.inner σ).map f
    | .lower _, .lower _ => (O.inner σ).map f
    | .lower _, .upper _ => nomatch f
  map_id := by rintro (_|_) <;> apply Functor.map_id
  map_comp := by
    rintro (_|_) (_|_) (_|_) f g <;> first | exact PEmpty.elim f | exact PEmpty.elim g | apply Functor.map_comp | skip
    · exact natural_cross D f g
    · exact cross_lower D f g

end Domain

variable (E : Domain π O .e)
abbrev atom (σ : Ty) : Domain π O σ := ⟨π ⋙ O.inner σ, 𝟙 _⟩

/-- A relation upstairs consists of all its upper rows and one whole lower relation. -/
abbrev relation (ρ : RTy) (args : U ⥤ Type) : Domain π O (.rel ρ) where
  upper := prodAction (intensionAction args) (π ⋙ O.inner (.rel ρ))
  project := { app := fun _ => TypeCat.ofHom Prod.snd }

abbrev level (σ : Ty) : Domain π O σ :=
  @Ty.rec (fun σ => Domain π O σ) (fun _ => U ⥤ Type) E
    (relation π O) (fun i => atom π O (.var i)) pointAction
    (fun _ _ d rest => prodAction d.upper rest) σ

abbrev upperArgs (ρ : RTy) : U ⥤ Type :=
  @RTy.rec (fun σ => Domain π O σ) (fun _ => U ⥤ Type) E
    (relation π O) (fun i => atom π O (.var i)) pointAction
    (fun _ _ d rest => prodAction d.upper rest) ρ

abbrev inner (σ : Ty) := (level π O E σ).inner

def oldArgs : ∀ (ρ : RTy) {z : C}, Args (inner π O E) ρ (.lower z) ≃ Args O.inner ρ z
  | .t, _ => Equiv.refl _
  | .arr _ ρ, _ => Equiv.prodCongr (Equiv.refl _) (oldArgs ρ)

def newArgs : ∀ (ρ : RTy) {u : U}, Args (inner π O E) ρ (.upper u) ≃ (upperArgs π O E ρ).obj u
  | .t, _ => Equiv.refl _
  | .arr _ ρ, _ => Equiv.prodCongr (Equiv.refl _) (newArgs ρ)

def incl (ρ : RTy) : (s : Site π) → ((inner π O E (.rel ρ)).obj s) → Intension (inner π O E) ρ s
  | .lower z, p, ⟨.lower w, a, j⟩ => (⟨w,(oldArgs π O E ρ (z := w)) a,j⟩ : Tuple O.inner ρ z) ∈ O.incl ρ z p
  | .lower _, _, ⟨.upper _, _, j⟩ => nomatch j
  | .upper u, p, ⟨.upper v, a, j⟩ => (⟨v,(newArgs π O E ρ (u := v)) a,j⟩ : Σ v, (upperArgs π O E ρ).obj v × (u ⟶ v)) ∈ p.1
  | .upper u, p, ⟨.lower w, a, j⟩ => (⟨w,(oldArgs π O E ρ (z := w)) a,j⟩ : Tuple O.inner ρ (π.obj u)) ∈ O.incl ρ _ p.2

/-- Read the complete old intension below a site. -/
def lowerRows {ρ : RTy} {x : Site π} {z : C} (vert : x ⟶ .lower z)
    (X : Intension (inner π O E) ρ x) : Intension O.inner ρ z :=
  {p | (⟨.lower p.1, (oldArgs π O E ρ (z := p.1)).symm p.2.1, vert ≫ Site.down π p.2.2⟩ :
    Tuple (inner π O E) ρ x) ∈ X}

theorem lower_incl (ρ : RTy) (z : C) (y : O.Dom z (.rel ρ)) :
    lowerRows π O E (𝟙 (Site.lower (π := π) z)) (incl π O E ρ (.lower z) y) = O.incl ρ z y := by
  ext ⟨w,a,j⟩
  change (⟨w, (oldArgs π O E ρ (z := w)) ((oldArgs π O E ρ (z := w)).symm a), 𝟙 z ≫ j⟩ : Tuple O.inner ρ z) ∈ O.incl ρ z y ↔ _
  simp

theorem vertical_incl (ρ : RTy) (u : U) (y : (level π O E (.rel ρ)).upper.obj u) :
    lowerRows π O E (Site.cross π (𝟙 (π.obj u))) (incl π O E ρ _ y) = O.incl ρ _ y.2 := by
  ext ⟨w,a,j⟩
  change (⟨w, (oldArgs π O E ρ (z := w)) ((oldArgs π O E ρ (z := w)).symm a), 𝟙 _ ≫ j⟩ : Tuple O.inner ρ _) ∈ O.incl ρ (π.obj u) y.2 ↔ _
  simp

theorem incl_injective (ρ : RTy) : ∀ x, Function.Injective (incl π O E ρ x)
  | .lower z => by
    intro p q e
    apply O.incl_injective ρ z
    rw [← lower_incl π O E ρ z p, ← lower_incl π O E ρ z q, e]
  | .upper u => by
    intro p q e
    apply Prod.ext
    · ext ⟨v,a,j⟩
      have H := Set.ext_iff.mp e ⟨.upper v, (newArgs π O E ρ (u := v)).symm a, Site.up π j⟩
      change (⟨v, (newArgs π O E ρ (u := v)) ((newArgs π O E ρ (u := v)).symm a), j⟩ : Σ v, (upperArgs π O E ρ).obj v × (u ⟶ v)) ∈ p.1 ↔ (⟨v, (newArgs π O E ρ (u := v)) ((newArgs π O E ρ (u := v)).symm a), j⟩ : Σ v, (upperArgs π O E ρ).obj v × (u ⟶ v)) ∈ q.1 at H
      simpa only [Equiv.apply_symm_apply] using H
    · apply O.incl_injective ρ _
      rw [← vertical_incl π O E ρ u p, ← vertical_incl π O E ρ u q, e]

theorem incl_map (ρ : RTy) : ∀ {x y} (j : x ⟶ y) (p : (inner π O E (.rel ρ)).obj x),
    incl π O E ρ y ((inner π O E (.rel ρ)).map j p) = Intension.map (inner π O E) j (incl π O E ρ x p)
  | .lower _, .upper _, j, _ => nomatch j
  | .lower z, .lower w, j, p => by
    have m := O.incl_map ρ (show z ⟶ w from j) p
    ext ⟨v,a,k⟩; cases v with
    | upper => exact PEmpty.elim k
    | lower v => exact Set.ext_iff.mp m ⟨v, oldArgs π O E ρ (z := v) a, k⟩
  | .upper u, .lower z, j, p => by
    have m := O.incl_map ρ (show π.obj u ⟶ z from j) p.2
    ext ⟨v,a,k⟩; cases v with
    | upper => exact PEmpty.elim k
    | lower v => exact Set.ext_iff.mp m ⟨v, oldArgs π O E ρ (z := v) a, k⟩
  | .upper u, .upper v, j, p => by
    ext ⟨w,a,k⟩; cases w with
    | upper => rfl
    | lower w => exact Set.ext_iff.mp (O.incl_map ρ (π.map (show u ⟶ v from j)) p.2) ⟨w, oldArgs π O E ρ (z := w) a,k⟩

/-- Put old constants into the upper layer with any chosen lift of each individual name. -/
def liftValue (u : U) (lift : O.Dom (π.obj u) .e → E.upper.obj u) :
    ∀ σ, O.Dom (π.obj u) σ → (level π O E σ).upper.obj u
  | .e, a => lift a
  | .var _, a => a
  | .rel _, y => (∅,y)

def model (u : U) (base : O.W₀ ⟶ π.obj u) (ne : ∀ v, Nonempty (E.upper.obj v))
    (lift : O.Dom (π.obj u) .e → E.upper.obj u) : Premodel Sig (Site π) where
  W₀ := .upper u
  inner := inner π O E
  nonempty_e
    | .upper v => ne v
    | .lower z => O.nonempty_e z
  incl := incl π O E
  incl_map := incl_map π O E
  incl_injective := incl_injective π O E
  I c := liftValue π O E u lift _ ((O.inner _).map base (O.I c))

end
end Classicism.Meta.StrongPossibility.Layers
