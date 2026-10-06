import Classicism.Models.SymBase
import Classicism.Models.Functions
import Classicism.Models.Conditions
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Nat.Pairing

/-!
# Symmetric ideally full models

The map's group `symmetric-ideally-full`: Dorr's symmetric ideally full models
(*Boolean Completeness does not imply Rigid Comprehension*, draft of 30 July 2026,
Definitions 15–18), each a category of sets and functions, the identity action for `e`, the
ideal of finite sets, and a group of symmetries at each object; the premodel is
`Premodel.symIdeal`, a model by Proposition 20 (`symIdeal_isModel`).

The members here, each over `ℕ`:

- `allSurj`: all surjections, the symmetries all permutations (Base 1);
- `infClasses`: all surjections, the symmetries the permutations preserving an equivalence
  relation with infinitely many infinite classes (`cls n`, the first coordinate of
  `Nat.unpair n`);
- `collapsePair`: the permutations preserving the pair `{0, 1}`, which are the symmetries, and
  the surjections collapsing it (Base 2);
- `rangeGap`: the permutations fixing `0`, which are the symmetries, and the functions omitting
  `0` from their range;
- `rangeGapNoAct`: the surjections for which `0` is its own only preimage, and the functions
  omitting `0`; the symmetries the permutations fixing `0`;
- `contrast`: two objects, each `ℕ`, the permutations as all the arrows, the symmetries all
  permutations at the first and the identity at the second (Appendix D, p. 79).

Not here: the two-object model whose second object carries the improper ideal, and the
model on the qualitative link structure (Base 3).
-/

namespace Classicism.Meta.Intensional

open CategoryTheory

namespace SymIdeal

/-! ### One object, the natural numbers -/

/-- A monoid of maps on `ℕ` with a set of symmetries among them: one object. -/
structure Base where
  Arr : (ℕ → ℕ) → Prop
  arr_id : Arr id
  arr_comp : ∀ {f g : ℕ → ℕ}, Arr f → Arr g → Arr (g ∘ f)
  /-- The symmetries: permutations, each in the monoid with its inverse. -/
  Sym : (ℕ → ℕ) → Prop
  sym_arr : ∀ {f}, Sym f → Arr f
  sym_bij : ∀ {f}, Sym f → Function.Bijective f
  sym_inv : ∀ {f} (h : Sym f), Sym (Equiv.ofBijective f (sym_bij h)).symm
  sym_id : Sym id
  sym_comp : ∀ {f g}, Sym f → Sym g → Sym (g ∘ f)

/-- The category of a base. -/
def Base.cat (B : Base) : FunCat where
  Obj := Unit
  X _ := ℕ
  Arr f := B.Arr f
  arr_id _ := B.arr_id
  arr_comp hf hg := B.arr_comp hf hg

variable (B : Base)

/-- The object. -/
abbrev star : B.cat.Ob := ()

instance : Subsingleton B.cat.Ob := inferInstanceAs (Subsingleton Unit)

/-- The symmetries, as arrows. -/
def syms (V : B.cat.Ob) : Set (V ⟶ V) := {g | B.Sym (FunCat.fn g)}

theorem syms_symGroup : SymGroup (syms B) := by
  intro V g hg
  let e := Equiv.ofBijective _ (B.sym_bij hg)
  refine ⟨FunCat.arr (F := B.cat) (i := V) (j := V) e.symm (B.sym_arr (B.sym_inv hg)), B.sym_inv hg, ?_, ?_⟩
  · exact FunCat.hom_ext (funext fun x => e.symm_apply_apply x)
  · exact FunCat.hom_ext (funext fun x => e.apply_symm_apply x)

/-- The base, for the map's group. -/
abbrev Base.toSym : SymBase where
  F := B.cat
  G := syms B
  G_id _ := B.sym_id
  G_comp {_ g s} hg hs := B.sym_comp (f := FunCat.fn g) (g := FunCat.fn s) hg hs
  G_inv := syms_symGroup B
  W₀ := star B
  ne _ := ⟨(0 : ℕ)⟩

/-- **The symmetric ideally full model of a base.** -/
noncomputable abbrev model : Premodel Signature.pure B.cat.Ob := (B.toSym).model

theorem model_isModel : (model B).IsModel := (B.toSym).model_isModel

/-! ### The members on one object -/

/-- An inverse of a permutation fixing a point fixes it. -/
theorem symm_fix {f : ℕ → ℕ} (hf : Function.Bijective f) {a : ℕ} (h : f a = a) :
    (Equiv.ofBijective f hf).symm a = a :=
  (Equiv.ofBijective f hf).symm_apply_eq.2 h.symm

/-- All surjections; all permutations (Base 1). -/
def allSurj : Base where
  Arr f := Function.Surjective f
  arr_id := Function.surjective_id
  arr_comp hf hg := hg.comp hf
  Sym f := Function.Bijective f
  sym_arr h := h.2
  sym_bij h := h
  sym_inv h := (Equiv.ofBijective _ h).symm.bijective
  sym_id := Function.bijective_id
  sym_comp hf hg := hg.comp hf

/-- The class of a natural number: infinitely many classes, each infinite. -/
def cls (n : ℕ) : ℕ := (Nat.unpair n).1

/-- All surjections; the permutations preserving the classes. -/
def infClasses : Base where
  Arr f := Function.Surjective f
  arr_id := Function.surjective_id
  arr_comp hf hg := hg.comp hf
  Sym f := Function.Bijective f ∧ ∀ x y, cls (f x) = cls (f y) ↔ cls x = cls y
  sym_arr h := h.1.2
  sym_bij h := h.1
  sym_inv {f} h := by
    refine ⟨(Equiv.ofBijective f h.1).symm.bijective, fun x y => ?_⟩
    have := h.2 ((Equiv.ofBijective f h.1).symm x) ((Equiv.ofBijective f h.1).symm y)
    rw [Equiv.ofBijective_apply_symm_apply f h.1 x, Equiv.ofBijective_apply_symm_apply f h.1 y] at this
    exact this.symm
  sym_id := ⟨Function.bijective_id, fun _ _ => Iff.rfl⟩
  sym_comp hf hg := ⟨hg.1.comp hf.1, fun x y => (hg.2 _ _).trans (hf.2 x y)⟩

/-- `f` preserves the pair `{0, 1}`. -/
def PairPres (f : ℕ → ℕ) : Prop := (f 0 = 0 ∧ f 1 = 1) ∨ (f 0 = 1 ∧ f 1 = 0)

/-- The permutations preserving `{0, 1}`, and the surjections collapsing it (Base 2). -/
def collapsePair : Base where
  Arr f := (Function.Bijective f ∧ PairPres f) ∨ (Function.Surjective f ∧ f 0 = f 1)
  arr_id := Or.inl ⟨Function.bijective_id, Or.inl ⟨rfl, rfl⟩⟩
  arr_comp {f g} hf hg := by
    rcases hg with ⟨hgb, hgp⟩ | ⟨hgs, hgc⟩
    · rcases hf with ⟨hfb, hfp⟩ | ⟨hfs, hfc⟩
      · refine Or.inl ⟨hgb.comp hfb, ?_⟩
        rcases hfp with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rcases hgp with ⟨g0, g1⟩ | ⟨g0, g1⟩ <;>
          simp [PairPres, Function.comp, h0, h1, g0, g1]
      · exact Or.inr ⟨hgb.2.comp hfs, by simp [Function.comp, hfc]⟩
    · rcases hf with ⟨hfb, hfp⟩ | ⟨hfs, hfc⟩
      · refine Or.inr ⟨hgs.comp hfb.2, ?_⟩
        rcases hfp with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> simp [Function.comp, h0, h1, hgc]
      · exact Or.inr ⟨hgs.comp hfs, by simp [Function.comp, hfc]⟩
  Sym f := Function.Bijective f ∧ PairPres f
  sym_arr h := Or.inl h
  sym_bij h := h.1
  sym_inv {f} h := by
    refine ⟨(Equiv.ofBijective f h.1).symm.bijective, ?_⟩
    rcases h.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact Or.inl ⟨symm_fix h.1 h0, symm_fix h.1 h1⟩
    · refine Or.inr ⟨?_, ?_⟩
      · exact (Equiv.ofBijective f h.1).symm_apply_eq.2 h1.symm
      · exact (Equiv.ofBijective f h.1).symm_apply_eq.2 h0.symm
  sym_id := ⟨Function.bijective_id, Or.inl ⟨rfl, rfl⟩⟩
  sym_comp {f g} hf hg := by
    refine ⟨hg.1.comp hf.1, ?_⟩
    rcases hf.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;> rcases hg.2 with ⟨g0, g1⟩ | ⟨g0, g1⟩ <;>
      simp [PairPres, Function.comp, h0, h1, g0, g1]

/-- The permutations fixing `0`, which are the symmetries, and the functions omitting `0`. -/
def rangeGap : Base where
  Arr f := (Function.Bijective f ∧ f 0 = 0) ∨ ∀ x, f x ≠ 0
  arr_id := Or.inl ⟨Function.bijective_id, rfl⟩
  arr_comp {f g} hf hg := by
    rcases hg with ⟨hgb, hg0⟩ | hg
    · rcases hf with ⟨hfb, hf0⟩ | hf
      · exact Or.inl ⟨hgb.comp hfb, by simp [Function.comp, hf0, hg0]⟩
      · exact Or.inr fun x e => hf x (hgb.1 (by simpa [Function.comp, hg0] using e))
    · exact Or.inr fun x => hg _
  Sym f := Function.Bijective f ∧ f 0 = 0
  sym_arr h := Or.inl h
  sym_bij h := h.1
  sym_inv {f} h := ⟨(Equiv.ofBijective f h.1).symm.bijective, symm_fix h.1 h.2⟩
  sym_id := ⟨Function.bijective_id, rfl⟩
  sym_comp hf hg := ⟨hg.1.comp hf.1, by simp [Function.comp, hf.2, hg.2]⟩

/-- The surjections for which `0` is its own only preimage, and the functions omitting `0`;
the symmetries the permutations fixing `0`. -/
def rangeGapNoAct : Base where
  Arr f := (Function.Surjective f ∧ ∀ x, f x = 0 ↔ x = 0) ∨ ∀ x, f x ≠ 0
  arr_id := Or.inl ⟨Function.surjective_id, fun _ => Iff.rfl⟩
  arr_comp {f g} hf hg := by
    rcases hg with ⟨hgs, hg0⟩ | hg
    · rcases hf with ⟨hfs, hf0⟩ | hf
      · exact Or.inl ⟨hgs.comp hfs, fun x => (hg0 _).trans (hf0 x)⟩
      · exact Or.inr fun x e => hf x ((hg0 _).1 e)
    · exact Or.inr fun x => hg _
  Sym f := Function.Bijective f ∧ f 0 = 0
  sym_arr {f} h := Or.inl ⟨h.1.2, fun x => ⟨fun e => h.1.1 (e.trans h.2.symm), fun e => e ▸ h.2⟩⟩
  sym_bij h := h.1
  sym_inv {f} h := ⟨(Equiv.ofBijective f h.1).symm.bijective, symm_fix h.1 h.2⟩
  sym_id := ⟨Function.bijective_id, rfl⟩
  sym_comp hf hg := ⟨hg.1.comp hf.1, by simp [Function.comp, hf.2, hg.2]⟩

/-! ### Two objects: qualitative contrast (Appendix D, p. 79) -/

/-- Two copies of `ℕ`, the permutations as all the arrows between them. -/
def contrastCat : FunCat where
  Obj := Bool
  X _ := ℕ
  Arr f := Function.Bijective f
  arr_id _ := Function.bijective_id
  arr_comp hf hg := hg.comp hf

/-- `W₀`, where all individuals are qualitatively indiscernible, and `W₁`, where each plays a
unique role. -/
abbrev W₀ : contrastCat.Ob := (false : Bool)
abbrev W₁ : contrastCat.Ob := (true : Bool)

/-- The symmetries: all permutations at `W₀`, the identity at `W₁`. -/
def contrastSyms (V : contrastCat.Ob) : Set (V ⟶ V) :=
  match V with
  | false => Set.univ
  | true => {𝟙 _}

theorem contrastSyms_symGroup : SymGroup contrastSyms := by
  intro V g hg
  match V, hg with
  | false, _ =>
    let e := Equiv.ofBijective _ g.2
    refine ⟨FunCat.arr (F := contrastCat) (i := W₀) (j := W₀) e.symm e.symm.bijective, trivial, ?_, ?_⟩
    · exact FunCat.hom_ext (funext fun x => e.symm_apply_apply x)
    · exact FunCat.hom_ext (funext fun x => e.apply_symm_apply x)
  | true, hg =>
    rw [Set.mem_singleton_iff.1 hg]
    exact ⟨𝟙 _, rfl, Category.id_comp _, Category.id_comp _⟩

/-- The base. -/
def contrastBase : SymBase where
  F := contrastCat
  G := contrastSyms
  G_id V := match V with
    | false => trivial
    | true => rfl
  G_comp {V} {g s} hg hs := match V, hg, hs with
    | false, _, _ => trivial
    | true, hg, hs => by
      rw [Set.mem_singleton_iff.1 hg, Set.mem_singleton_iff.1 hs]
      exact Set.mem_singleton_iff.2 (Category.id_comp _)
  G_inv := contrastSyms_symGroup
  W₀ := W₀
  ne _ := ⟨(0 : ℕ)⟩

/-- **The qualitative-contrast model**, based at `W₀`. -/
noncomputable abbrev contrast : Premodel Signature.pure contrastCat.Ob := contrastBase.model

theorem contrast_isModel : contrast.IsModel := contrastBase.model_isModel

/-! ### The actual world: the symmetries -/

section actual

variable {B}

/-- The proposition true at exactly the symmetries. -/
def symProp : Intension (SymT B.cat.De (syms B)) .t (star B) := {p | B.Sym (FunCat.fn p.2.2)}

/-- **The actual world is the set of symmetries, and is isolated**, when the identity is a
symmetry, a composite of arrows is one exactly when both are, and whether an arrow is one is
settled by its values on a finite set. -/
theorem actualWorldIsolated_of (hid : B.Sym id)
    (hcomp : ∀ {h j : ℕ → ℕ}, B.Arr h → B.Arr j → (B.Sym (j ∘ h) ↔ B.Sym h ∧ B.Sym j))
    (N : Set ℕ) (hN : N.Finite)
    (hpin : ∀ {h i : ℕ → ℕ}, B.Arr h → B.Arr i → (∀ x ∈ N, h x = i x) → (B.Sym h ↔ B.Sym i)) :
    (model B).ActualWorldIsolated := by
  obtain ⟨a, ha⟩ := (mem_range_symIncl B.cat.De (syms B) .t (star B) symProp).2
    ⟨⟨N, hN, fun V h i hag => by
      ext ⟨U, ⟨⟩, k⟩
      exact (hcomp h.2 k.2).trans ((and_congr_left' (hpin h.2 i.2 fun x hx => hag x hx)).trans
        (hcomp i.2 k.2).symm)⟩,
    fun V a k s hs hk => (hcomp k.2 s.2).2 ⟨hk, hs⟩⟩
  have ha' : (model B).incl .t (star B) a = symProp := ha
  refine ⟨a, ?_, fun p hp => ?_, fun {V U} i j hi => ?_⟩
  · show (⟨star B, PUnit.unit, 𝟙 (star B)⟩ : Tuple (SymT B.cat.De (syms B)) .t (star B)) ∈
      (model B).incl .t (star B) a
    rw [ha']; exact hid
  · show (model B).incl .t (star B) a ⊆ (model B).incl .t (star B) p
    rw [ha']
    rintro ⟨V, ⟨⟩, k⟩ hk
    cases V
    exact Premodel.Sym.at_id (symIdeal_domSym .t (star B) p) PUnit.unit hk hp
  · change (⟨V, PUnit.unit, i⟩ : Tuple (SymT B.cat.De (syms B)) .t (star B)) ∉ (model B).incl .t (star B) a at hi
    show (⟨U, PUnit.unit, i ≫ j⟩ : Tuple (SymT B.cat.De (syms B)) .t (star B)) ∉ (model B).incl .t (star B) a
    rw [ha'] at hi ⊢
    exact fun h => hi ((hcomp i.2 j.2).1 h).1

end actual

/-! ### Collapse pair and range gap: the actual world is isolated -/

theorem collapsePair_comp {h j : ℕ → ℕ} (hh : collapsePair.Arr h) (hj : collapsePair.Arr j) :
    collapsePair.Sym (j ∘ h) ↔ collapsePair.Sym h ∧ collapsePair.Sym j := by
  constructor
  · intro hs
    have hinj : Function.Injective (j ∘ h) := hs.1.1
    have h01 : h 0 ≠ h 1 := fun e => absurd (hinj (a₁ := 0) (a₂ := 1) (by simp [Function.comp, e])) (by decide)
    have hS : collapsePair.Sym h := hh.resolve_right fun ⟨_, e⟩ => h01 e
    refine ⟨hS, hj.resolve_right fun ⟨_, e⟩ => ?_⟩
    rcases hS.2 with ⟨a, b⟩ | ⟨a, b⟩
    · exact absurd (hinj (a₁ := 0) (a₂ := 1) (by simp [Function.comp, a, b, e])) (by decide)
    · exact absurd (hinj (a₁ := 0) (a₂ := 1) (by simp [Function.comp, a, b, e])) (by decide)
  · rintro ⟨hh, hj⟩
    exact collapsePair.arr_comp (Or.inl hh) (Or.inl hj) |>.resolve_right fun ⟨_, e⟩ =>
      absurd ((hj.1.comp hh.1).1 e) (by decide)

theorem collapsePair_pin {h i : ℕ → ℕ} (hh : collapsePair.Arr h) (hi : collapsePair.Arr i)
    (e : ∀ x ∈ ({0, 1} : Set ℕ), h x = i x) : collapsePair.Sym h ↔ collapsePair.Sym i := by
  have e0 := e 0 (by simp); have e1 := e 1 (by simp)
  constructor
  · intro hS
    exact hi.resolve_right fun ⟨_, c⟩ => by
      rcases hS.2 with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [← e0, ← e1, a, b] at c <;> exact absurd c (by decide)
  · intro hS
    exact hh.resolve_right fun ⟨_, c⟩ => by
      rcases hS.2 with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [e0, e1, a, b] at c <;> exact absurd c (by decide)

theorem collapsePair_actualWorldIsolated : (model collapsePair).ActualWorldIsolated :=
  actualWorldIsolated_of ⟨Function.bijective_id, Or.inl ⟨rfl, rfl⟩⟩ collapsePair_comp
    {0, 1} (Set.toFinite _) collapsePair_pin

theorem rangeGap_comp {h j : ℕ → ℕ} (hh : rangeGap.Arr h) (hj : rangeGap.Arr j) :
    rangeGap.Sym (j ∘ h) ↔ rangeGap.Sym h ∧ rangeGap.Sym j := by
  constructor
  · rintro ⟨hb, h0⟩
    have hjS : rangeGap.Sym j := hj.resolve_right fun hj' => hj' _ h0
    refine ⟨hh.resolve_right fun hh' => hh' 0 (hjS.1.1 ?_), hjS⟩
    simpa [Function.comp, hjS.2] using h0
  · rintro ⟨hh, hj⟩
    exact ⟨hj.1.comp hh.1, by simp [Function.comp, hh.2, hj.2]⟩

theorem rangeGap_pin {h i : ℕ → ℕ} (hh : rangeGap.Arr h) (hi : rangeGap.Arr i)
    (e : ∀ x ∈ ({0} : Set ℕ), h x = i x) : rangeGap.Sym h ↔ rangeGap.Sym i := by
  have e0 := e 0 rfl
  constructor
  · intro hS
    exact hi.resolve_right fun hi' => hi' 0 (e0 ▸ hS.2)
  · intro hS
    exact hh.resolve_right fun hh' => hh' 0 (e0 ▸ hS.2)

theorem rangeGap_actualWorldIsolated : (model rangeGap).ActualWorldIsolated :=
  actualWorldIsolated_of ⟨Function.bijective_id, rfl⟩ rangeGap_comp {0} (Set.toFinite _) rangeGap_pin

/-! ### The group's conditions -/

section conditions

variable {B}

/-- Not being one of the members of `K`: `x ∉ k[K]` at the arrow `k`. -/
def avoid (K : Set ℕ) : Intension (SymT B.cat.De (syms B)) (.arr .e .t) (star B) :=
  {p | p.2.1.1 ∉ FunCat.fn p.2.2 '' K}

theorem sym_injective {g : star B ⟶ star B} (hg : g ∈ syms B (star B)) : Function.Injective (FunCat.fn g) :=
  (B.sym_bij hg).1

theorem avoid_mem (K : Set ℕ) (hK : K.Finite) : avoid K ∈ Set.range ((model B).incl (.arr .e .t) (star B)) := by
  refine (mem_range_symIncl B.cat.De (syms B) _ (star B) _).2 ⟨⟨K, hK, fun V h i ha => ?_⟩, ?_⟩
  · ext ⟨U, ⟨x, ⟨⟩⟩, j⟩
    have e : (FunCat.fn j ∘ FunCat.fn h) '' K = (FunCat.fn j ∘ FunCat.fn i) '' K :=
      Set.image_congr fun a ha' => by
        show FunCat.fn j (FunCat.fn h a) = FunCat.fn j (FunCat.fn i a)
        have e' : FunCat.fn h a = FunCat.fn i a := ha a ha'
        rw [e']
    show x ∉ (FunCat.fn j ∘ FunCat.fn h) '' K ↔ x ∉ (FunCat.fn j ∘ FunCat.fn i) '' K
    rw [e]
  · rintro V ⟨x, ⟨⟩⟩ k g hg (hx : x ∉ FunCat.fn k '' K)
    cases V
    rintro ⟨a, ha, e⟩
    exact hx ⟨a, ha, sym_injective hg e⟩

/-- **`transposable`**, for a base whose symmetries include, for every finite `K` containing
the base's special points `K₀` and every `y` outside `K`, the transposition of `y` with some
other point outside `K`: the property of not being in `K` has extension `ℕ ∖ K`, and the
transposition fixes `K`, so fixes the property, and moves `y`. -/
theorem transposable_of (K₀ : Set ℕ) (hK₀ : K₀.Finite)
    (hmove : ∀ K : Set ℕ, K.Finite → K₀ ⊆ K → ∀ y ∉ K, ∃ z ∉ K, z ≠ y ∧ B.Sym (Equiv.swap y z)) :
    (B.toSym).Transposable := by
  intro N hN
  have hK : (N ∪ K₀).Finite := hN.union hK₀
  obtain ⟨a, ha⟩ := avoid_mem (B := B) _ hK
  have ha' : (model B).incl (.arr .e .t) (star B) a = avoid (N ∪ K₀) := ha
  have hext : ∀ y : ℕ, (⟨star B, (y, PUnit.unit), 𝟙 (star B)⟩ : Tuple (model B).inner (.arr .e .t) (star B)) ∈
      (model B).incl _ (star B) a ↔ y ∉ N ∪ K₀ := fun y => by
    rw [ha']
    show y ∉ id '' (N ∪ K₀) ↔ _
    rw [Set.image_id]
  obtain ⟨y₀, hy₀⟩ := Set.Finite.exists_notMem (α := ℕ) hK
  refine ⟨a, ⟨y₀, (hext y₀).2 hy₀⟩, fun (y : ℕ) hy => ?_⟩
  have hy := (hext y).1 hy
  obtain ⟨z, hz, hzy, hs⟩ := hmove _ hK Set.subset_union_right y hy
  have hfix : ∀ x : ℕ, x ∈ N ∪ K₀ → Equiv.swap y z x = x := fun x hx =>
    Equiv.swap_apply_of_ne_of_ne (fun e => hy (by rw [← e]; exact hx)) (fun e => hz (by rw [← e]; exact hx))
  refine ⟨FunCat.arr (F := B.cat) (i := star B) (j := star B) (Equiv.swap y z) (B.sym_arr hs), hs,
    fun x hx => hfix x (Or.inl hx), ?_, ?_⟩
  · apply (model B).incl_injective
    erw [(model B).incl_map, ha']
    ext ⟨U, ⟨x, ⟨⟩⟩, j⟩
    show x ∉ (FunCat.fn j ∘ Equiv.swap y z) '' (N ∪ K₀) ↔ x ∉ FunCat.fn j '' (N ∪ K₀)
    refine not_congr ⟨fun ⟨b, hb, e⟩ => ⟨b, hb, ?_⟩, fun ⟨b, hb, e⟩ => ⟨b, hb, ?_⟩⟩
    · rw [← e]; show FunCat.fn j b = FunCat.fn j (Equiv.swap y z b); rw [hfix b hb]
    · rw [← e]; show FunCat.fn j (Equiv.swap y z b) = FunCat.fn j b; rw [hfix b hb]
  · show Equiv.swap y z y ≠ y
    rw [Equiv.swap_apply_left]; exact hzy

/-- A finite set of naturals has a point outside it and outside another given point. -/
theorem exists_fresh {K : Set ℕ} (hK : K.Finite) (y : ℕ) : ∃ z ∉ K, z ≠ y := by
  obtain ⟨z, hz⟩ := (hK.union (Set.finite_singleton y)).exists_notMem
  exact ⟨z, fun h => hz (Or.inl h), fun h => hz (Or.inr h)⟩

/-- When the symmetry group's members are told apart by a finite set and composites behave,
it is pinned down. -/
theorem symmetryGroupPinned_of
    (hcomp : ∀ {h j : ℕ → ℕ}, B.Arr h → B.Arr j → (B.Sym (j ∘ h) ↔ B.Sym h ∧ B.Sym j))
    (N : Set ℕ) (hN : N.Finite)
    (hpin : ∀ {h i : ℕ → ℕ}, B.Arr h → B.Arr i → (∀ x ∈ N, h x = i x) → (B.Sym h ↔ B.Sym i)) :
    (B.toSym).SymmetryGroupPinned := by
  have mem : ∀ k : star B ⟶ star B, (⟨star B, PUnit.unit, k⟩ : Tuple (SymT B.cat.De (syms B)) .t (star B)) ∈
      (B.toSym).groupProp ↔ B.Sym (FunCat.fn k) := fun k => by
    constructor
    · rintro ⟨g, hg, he⟩
      obtain ⟨-, he⟩ := Sigma.mk.inj_iff.1 he
      rw [(Prod.mk.inj (eq_of_heq he)).2]; exact hg
    · exact fun hk => ⟨k, hk, rfl⟩
  refine ⟨N, hN, fun V h i ha => ?_⟩
  cases V
  ext ⟨U, ⟨⟩, k⟩
  cases U
  show (⟨star B, PUnit.unit, h ≫ k⟩ : Tuple (SymT B.cat.De (syms B)) .t (star B)) ∈ (B.toSym).groupProp ↔
    (⟨star B, PUnit.unit, i ≫ k⟩ : Tuple (SymT B.cat.De (syms B)) .t (star B)) ∈ (B.toSym).groupProp
  rw [mem, mem]
  show B.Sym (FunCat.fn k ∘ FunCat.fn h) ↔ B.Sym (FunCat.fn k ∘ FunCat.fn i)
  exact (hcomp h.2 k.2).trans ((and_congr_left' (hpin h.2 i.2 fun x hx => ha x hx)).trans (hcomp i.2 k.2).symm)

end conditions

/-! ### The members' conditions -/

theorem swap_fix {y z a : ℕ} {K : Set ℕ} (hy : y ∉ K) (hz : z ∉ K) (ha : a ∈ K) : Equiv.swap y z a = a :=
  Equiv.swap_apply_of_ne_of_ne (fun e => hy (e ▸ ha)) (fun e => hz (e ▸ ha))

theorem allSurj_transposable : allSurj.toSym.Transposable :=
  transposable_of ∅ Set.finite_empty fun K hK _ y _ => by
    obtain ⟨z, hz, hzy⟩ := exists_fresh hK y
    exact ⟨z, hz, hzy, (Equiv.swap y z).bijective⟩

theorem collapsePair_transposable : collapsePair.toSym.Transposable :=
  transposable_of {0, 1} (Set.toFinite _) fun K hK hK₀ y hy => by
    obtain ⟨z, hz, hzy⟩ := exists_fresh hK y
    exact ⟨z, hz, hzy, (Equiv.swap y z).bijective,
      Or.inl ⟨swap_fix hy hz (hK₀ (by simp)), swap_fix hy hz (hK₀ (by simp))⟩⟩

theorem rangeGap_transposable : rangeGap.toSym.Transposable :=
  transposable_of {0} (Set.toFinite _) fun K hK hK₀ y hy => by
    obtain ⟨z, hz, hzy⟩ := exists_fresh hK y
    exact ⟨z, hz, hzy, (Equiv.swap y z).bijective, swap_fix hy hz (hK₀ rfl)⟩

theorem rangeGapNoAct_transposable : rangeGapNoAct.toSym.Transposable :=
  transposable_of {0} (Set.toFinite _) fun K hK hK₀ y hy => by
    obtain ⟨z, hz, hzy⟩ := exists_fresh hK y
    exact ⟨z, hz, hzy, (Equiv.swap y z).bijective, swap_fix hy hz (hK₀ rfl)⟩

/-- A transposition within a class preserves every number's class. -/
theorem cls_swap {y z : ℕ} (h : cls y = cls z) (x : ℕ) : cls (Equiv.swap y z x) = cls x := by
  rcases eq_or_ne x y with rfl | hxy
  · rw [Equiv.swap_apply_left, h]
  rcases eq_or_ne x z with rfl | hxz
  · rw [Equiv.swap_apply_right, h]
  rw [Equiv.swap_apply_of_ne_of_ne hxy hxz]

theorem infClasses_transposable : infClasses.toSym.Transposable :=
  transposable_of ∅ Set.finite_empty fun K hK _ y _ => by
    have hfin : {m | Nat.pair (cls y) m ∈ K ∪ {y}}.Finite :=
      (hK.union (Set.finite_singleton y)).preimage
        (fun a _ b _ e => (Nat.pair_eq_pair.1 e).2)
    obtain ⟨m, hm⟩ := hfin.exists_notMem
    have hc : cls y = cls (Nat.pair (cls y) m) := by simp [cls, Nat.unpair_pair]
    refine ⟨Nat.pair (cls y) m, fun h => hm (Or.inl h), fun h => hm (Or.inr h), (Equiv.swap _ _).bijective,
      fun a b => ?_⟩
    rw [cls_swap hc, cls_swap hc]

theorem collapsePair_symmetryGroupPinned : collapsePair.toSym.SymmetryGroupPinned :=
  symmetryGroupPinned_of collapsePair_comp {0, 1} (Set.toFinite _) collapsePair_pin

theorem rangeGap_symmetryGroupPinned : rangeGap.toSym.SymmetryGroupPinned :=
  symmetryGroupPinned_of rangeGap_comp {0} (Set.toFinite _) rangeGap_pin

/-- `fixes-or-omits`, with `0` the distinguished individual: the symmetries fix it, every
arrow fixes or omits it, and the successor function omits it. -/
theorem rangeGap_fixesOrOmits : rangeGap.toSym.FixesOrOmits :=
  ⟨fun _ => (0 : ℕ), fun _ _ hg => hg.2, fun _ k => k.2.imp (fun h => h.2) id,
    ⟨star rangeGap, FunCat.arr (F := rangeGap.cat) (i := star rangeGap) (j := star rangeGap) Nat.succ
      (Or.inr Nat.succ_ne_zero), Nat.succ_ne_zero 0⟩⟩

theorem rangeGapNoAct_fixesOrOmits : rangeGapNoAct.toSym.FixesOrOmits :=
  ⟨fun _ => (0 : ℕ), fun _ _ hg => hg.2, fun _ k => k.2.imp (fun h => (h.2 0).2 rfl) id,
    ⟨star rangeGapNoAct, FunCat.arr (F := rangeGapNoAct.cat) (i := star rangeGapNoAct) (j := star rangeGapNoAct)
      Nat.succ (Or.inr Nat.succ_ne_zero), Nat.succ_ne_zero 0⟩⟩

/-! ### Infinitely many individuals, and separable collapses -/

theorem infinitelyManyIndividuals (B : Base) : (B.toSym).model.InfinitelyManyIndividuals :=
  inferInstanceAs (Infinite ℕ)

theorem contrast_infinitelyManyIndividuals : contrastBase.model.InfinitelyManyIndividuals :=
  inferInstanceAs (Infinite ℕ)

/-- Halving up to `2i + 3`, then shifting down: a surjection collapsing `0` with `1` and each pair
`2j + 2, 2j + 3` with `j ≤ i`, and nothing beyond. -/
def halfThen (i : ℕ) (x : ℕ) : ℕ := if x ≤ 2 * i + 3 then x / 2 else x - (i + 2)

theorem halfThen_surjective (i : ℕ) : Function.Surjective (halfThen i) := fun y => by
  by_cases hy : y ≤ i + 1
  · exact ⟨2 * y, by simp only [halfThen]; rw [if_pos (by omega)]; omega⟩
  · exact ⟨y + (i + 2), by simp only [halfThen]; rw [if_neg (by omega)]; omega⟩

theorem halfThen_sep {i j : ℕ} (h : i < j) :
    halfThen i (2 * i + 2) = halfThen i (2 * i + 3) ∧ halfThen i (2 * j + 2) ≠ halfThen i (2 * j + 3) := by
  simp only [halfThen]
  refine ⟨by rw [if_pos (by omega), if_pos (by omega)]; omega, ?_⟩
  rw [if_neg (by omega), if_neg (by omega)]; omega

/-- Separation of the pairs `2i + 2, 2i + 3` by maps `f i` that collapse pair `i` but not later ones. -/
theorem separable_of (B : Base) (f : ℕ → ℕ → ℕ) (hf : ∀ i, B.Arr (f i))
    (hsep : ∀ {i j}, i < j → f i (2 * i + 2) = f i (2 * i + 3) ∧ f i (2 * j + 2) ≠ f i (2 * j + 3)) :
    (B.toSym).SeparableCollapses := by
  refine ⟨fun i => 2 * i + 2, fun i => 2 * i + 3, fun i j hij => ?_⟩
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · exact ⟨star B, FunCat.arr (F := B.cat) (i := star B) (j := star B) (f i) (hf i), Or.inl (hsep h)⟩
  · exact ⟨star B, FunCat.arr (F := B.cat) (i := star B) (j := star B) (f j) (hf j), Or.inr (hsep h)⟩

theorem collapsePair_separable : collapsePair.toSym.SeparableCollapses :=
  separable_of collapsePair halfThen
    (fun i => Or.inr ⟨halfThen_surjective i, by simp only [halfThen]; rw [if_pos (by omega), if_pos (by omega)]⟩)
    halfThen_sep

theorem rangeGap_separable : rangeGap.toSym.SeparableCollapses :=
  separable_of rangeGap (fun i x => halfThen i x + 1) (fun i => Or.inr fun x => Nat.succ_ne_zero _)
    fun h => ⟨by rw [(halfThen_sep h).1], fun e => (halfThen_sep h).2 (by omega)⟩

/-! ### Surjective arrows -/

theorem allSurj_surjectiveArrows : allSurj.toSym.SurjectiveArrows := fun _ k => k.2
theorem infClasses_surjectiveArrows : infClasses.toSym.SurjectiveArrows := fun _ k => k.2
theorem collapsePair_surjectiveArrows : collapsePair.toSym.SurjectiveArrows := fun _ k =>
  k.2.elim (fun h => h.1.2) (fun h => h.1)

end SymIdeal

end Classicism.Meta.Intensional
