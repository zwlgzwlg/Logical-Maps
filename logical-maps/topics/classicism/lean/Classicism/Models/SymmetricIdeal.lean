import Classicism.Semantics.Symmetric
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

/-- **The symmetric ideally full model of a base.** -/
noncomputable abbrev model : Premodel Signature.pure B.cat.Ob :=
  Premodel.symIdeal B.cat.De (syms B) (star B) (fun _ => ⟨(0 : ℕ)⟩) (fun c => nomatch c)

theorem model_isModel : (model B).IsModel := symIdeal_isModel (syms_symGroup B)

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

/-- **The qualitative-contrast model**, based at `W₀`. -/
noncomputable abbrev contrast : Premodel Signature.pure contrastCat.Ob :=
  Premodel.symIdeal contrastCat.De contrastSyms W₀ (fun _ => ⟨(0 : ℕ)⟩) (fun c => nomatch c)

theorem contrast_isModel : contrast.IsModel := symIdeal_isModel contrastSyms_symGroup

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

end SymIdeal

end Classicism.Meta.Intensional
