import Classicism.Semantics.Symmetric
import Classicism.Models.Functions
import Classicism.Models.Conditions
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Pi

/-!
# Symmetry-constrained full models

The map's group `symmetry-constrained-full`: one object, the three-element set `X`, a monoid
of maps on it as the arrows, and the permutations of `X` as the symmetries; an intension is
admitted when it is symmetric (Dorr's Definition 17). Every intension is pinned down by the
finite set `X` itself, so this is the symmetric ideally full premodel over the base
(`Premodel.symIdeal`), a model by Proposition 20 (`symIdeal_isModel`).

The construction is for any monoid of maps on `X` containing the permutations (`Maps3`),
the permutations then being arrows, so that the symmetry condition is Dorr's. The two
members: all `27` maps (`allMaps`, `symmetry-constrained-full-all-maps`), and the six
permutations with the three collapses (`permsCollapses`, `symmetry-constrained-full-collapse`).
-/

namespace Classicism.Meta.Intensional

open CategoryTheory

namespace SymFull

/-- A monoid of maps on a three-element set containing the permutations. -/
structure Maps3 where
  Arr : (Fin 3 → Fin 3) → Prop
  arr_id : Arr id
  arr_comp : ∀ {f g : Fin 3 → Fin 3}, Arr f → Arr g → Arr (g ∘ f)
  arr_perm : ∀ {f : Fin 3 → Fin 3}, Function.Bijective f → Arr f

/-- Its category: one object, the set, and the maps of the monoid. -/
def Maps3.cat (M : Maps3) : FunCat where
  Obj := Unit
  X _ := Fin 3
  Arr f := M.Arr f
  arr_id _ := M.arr_id
  arr_comp hf hg := M.arr_comp hf hg

variable (M : Maps3)

/-- The object. -/
abbrev star : M.cat.Ob := ()

/-- The symmetries: the arrows that are permutations. -/
def perms (V : M.cat.Ob) : Set (V ⟶ V) := {g | Function.Bijective (FunCat.fn g)}

/-- The permutations are closed under inverses. -/
theorem perms_symGroup : SymGroup (perms M) := by
  intro V g hg
  let e := Equiv.ofBijective _ hg
  refine ⟨FunCat.arr (F := M.cat) (i := V) (j := V) e.symm (M.arr_perm e.symm.bijective), e.symm.bijective, ?_, ?_⟩
  · exact FunCat.hom_ext (funext fun x => e.symm_apply_apply x)
  · exact FunCat.hom_ext (funext fun x => e.apply_symm_apply x)

/-- **The symmetry-constrained full model on the monoid.** -/
noncomputable abbrev model : Premodel Signature.pure M.cat.Ob :=
  Premodel.symIdeal M.cat.De (perms M) (PinIdeal.fin _) (star M) (fun _ => ⟨(0 : Fin 3)⟩) (fun c => nomatch c)

theorem model_isModel : (model M).IsModel := symIdeal_isModel (perms_symGroup M)

variable {M}

/-! ### The conditions it meets -/

instance : Subsingleton M.cat.Ob := inferInstanceAs (Subsingleton Unit)

theorem homs_finite (V U : M.cat.Ob) : Finite (V ⟶ U) := by
  have : Finite (M.cat.X V → M.cat.X U) := inferInstanceAs (Finite (Fin 3 → Fin 3))
  exact Subtype.finite

/-- `finitely-many-propositions`: a proposition is a set of tuples, and there are finitely
many tuples, one for each of the finitely many arrows. -/
theorem finitely_many_propositions : (model M).FinitelyManyPropositions := by
  have := homs_finite (M := M)
  have : Finite (Set (Σ V : M.cat.Ob, PUnit × ((star M) ⟶ V))) := by
    have : Finite M.cat.Ob := inferInstanceAs (Finite Unit)
    infer_instance
  show Finite {A : Set (Σ V : M.cat.Ob, PUnit × ((star M) ⟶ V)) // _}
  exact Subtype.finite

/-- `finitely-many-propositions-everywhere`: likewise at every object, there being one. -/
theorem finitely_many_propositions_everywhere : (model M).FinitelyManyPropositionsEverywhere :=
  fun {V} _ => by
    obtain rfl : V = (star M) := Subsingleton.elim _ _
    exact finitely_many_propositions

/-! ### Orbits: extensional fullness and the isolated actual world -/

instance (i : M.cat.Ob) : Finite (M.cat.X i) := inferInstanceAs (Finite (Fin 3))
instance (i : M.cat.Ob) : Finite (M.cat.De.obj i) := inferInstanceAs (Finite (Fin 3))

/-- Two arrows agreeing on every individual are equal, so everything is pinned down by the
finite set of all individuals. -/
theorem pinned_univ {ρ : RTy} (F : Intension (SymT M.cat.De (perms M) (PinIdeal.fin _)) ρ (star M)) :
    ∃ N : Set (M.cat.De.obj (star M)), N.Finite ∧
      ∀ (V : M.cat.Ob) (h i : (star M) ⟶ V), AgreeOn M.cat.De N h i →
        Intension.map (SymT M.cat.De (perms M) (PinIdeal.fin _)) h F = Intension.map (SymT M.cat.De (perms M) (PinIdeal.fin _)) i F :=
  ⟨Set.univ, Set.toFinite _, fun _ h i ha => by
    rw [(FunCat.hom_ext (funext fun x => (ha x (Set.mem_univ x) : FunCat.fn h x = FunCat.fn i x)) : h = i)]⟩

/-- The orbit of a set of argument tuples: `g ȳ` at each permutation `g`, for `ȳ` in the set. -/
def orbit {ρ : RTy} (E : Set (Args (SymT M.cat.De (perms M) (PinIdeal.fin _)) ρ (star M))) : Intension (SymT M.cat.De (perms M) (PinIdeal.fin _)) ρ (star M) :=
  {p | ∃ (g : (star M) ⟶ (star M)), g ∈ perms M (star M) ∧ ∃ b ∈ E,
    p = (⟨(star M), Args.map (SymT M.cat.De (perms M) (PinIdeal.fin _)) ρ g b, g⟩ : Tuple (SymT M.cat.De (perms M) (PinIdeal.fin _)) ρ (star M))}

theorem perms_comp {g s : (star M) ⟶ (star M)} (hg : g ∈ perms M (star M)) (hs : s ∈ perms M (star M)) :
    g ≫ s ∈ perms M (star M) := hs.comp hg

theorem orbit_sym {ρ : RTy} (E : Set (Args (SymT M.cat.De (perms M) (PinIdeal.fin _)) ρ (star M))) :
    SymCond M.cat.De (perms M) (PinIdeal.fin _) (orbit E) := by
  rintro V a k s hs ⟨g, hg, b, hb, he⟩
  cases he
  exact ⟨g ≫ s, perms_comp hg hs, b, hb, by rw [Args.map_comp]⟩

theorem orbit_mem {ρ : RTy} (E : Set (Args (SymT M.cat.De (perms M) (PinIdeal.fin _)) ρ (star M))) :
    orbit E ∈ Set.range ((model M).incl ρ (star M)) :=
  (mem_range_symIncl M.cat.De (perms M) (PinIdeal.fin _) ρ (star M) _).2 ⟨pinned_univ _, orbit_sym E⟩

/-- The identity is the only permutation that is the identity tuple's arrow. -/
theorem mem_orbit_id {ρ : RTy} (E : Set (Args (SymT M.cat.De (perms M) (PinIdeal.fin _)) ρ (star M))) (a : Args (SymT M.cat.De (perms M) (PinIdeal.fin _)) ρ (star M)) :
    (⟨(star M), a, 𝟙 (star M)⟩ : Tuple (SymT M.cat.De (perms M) (PinIdeal.fin _)) ρ (star M)) ∈ orbit E ↔ a ∈ E := by
  constructor
  · rintro ⟨g, -, b, hb, he⟩
    obtain ⟨-, he⟩ := Sigma.mk.inj_iff.1 he
    have he := eq_of_heq he
    obtain ⟨ha, hg⟩ := Prod.mk.inj he
    subst hg
    rw [ha, Args.map_id]; exact hb
  · intro ha
    exact ⟨𝟙 (star M), Function.bijective_id, a, ha, by rw [Args.map_id]⟩

/-- `extensionally-full`: any set of tuples at the identity is the extension there of its
orbit, which is symmetric. -/
theorem extFull : (model M).ExtFull := by
  intro ρ W E
  cases W
  obtain ⟨x, hx⟩ := orbit_mem E
  refine ⟨x, ?_⟩
  ext a
  show (⟨(star M), a, 𝟙 (star M)⟩ : Tuple (SymT M.cat.De (perms M) (PinIdeal.fin _)) ρ (star M)) ∈ (model M).incl ρ (star M) x ↔ a ∈ E
  rw [hx]
  exact mem_orbit_id E a

/-- An arrow whose composite with another is a permutation is one: it is injective, and
the set is finite. -/
theorem perm_of_comp_perm {i j : (star M) ⟶ (star M)} (h : i ≫ j ∈ perms M (star M)) : i ∈ perms M (star M) := by
  have hinj : Function.Injective (FunCat.fn i) := fun x y e => h.1 (by
    show FunCat.fn j (FunCat.fn i x) = FunCat.fn j (FunCat.fn i y); rw [e])
  exact (Finite.injective_iff_bijective).1 hinj

/-- `actual-world-isolated`: the actual-world proposition is the orbit of the identity, the
permutations; no arrow from a non-permutation leads back to one. -/
theorem actualWorldIsolated : (model M).ActualWorldIsolated := by
  obtain ⟨a, ha⟩ := orbit_mem (ρ := .t) Set.univ
  refine ⟨a, ?_, fun p hp => ?_, fun {V U} i j hi => ?_⟩
  · show (⟨(star M), PUnit.unit, 𝟙 (star M)⟩ : Tuple (SymT M.cat.De (perms M) (PinIdeal.fin _)) .t (star M)) ∈ (model M).incl .t (star M) a
    rw [ha, mem_orbit_id]; trivial
  · show (model M).incl .t (star M) a ⊆ (model M).incl .t (star M) p
    rw [ha]
    rintro _ ⟨g, hg, ⟨⟩, -, rfl⟩
    have := Premodel.Sym.at_id (symIdeal_domSym .t (star M) p) PUnit.unit hg hp
    exact this
  · cases V; cases U
    change (⟨(star M), PUnit.unit, i⟩ : Tuple (SymT M.cat.De (perms M) (PinIdeal.fin _)) .t (star M)) ∉ (model M).incl .t (star M) a at hi
    show (⟨(star M), PUnit.unit, i ≫ j⟩ : Tuple (SymT M.cat.De (perms M) (PinIdeal.fin _)) .t (star M)) ∉ (model M).incl .t (star M) a
    rw [ha] at hi ⊢
    rintro ⟨g, hg, ⟨⟩, -, he⟩
    obtain ⟨-, he⟩ := Sigma.mk.inj_iff.1 he
    have he := (Prod.mk.inj (eq_of_heq he)).2
    exact hi ⟨i, perm_of_comp_perm (he ▸ hg), PUnit.unit, trivial, rfl⟩

/-! ### The members -/

/-- All `27` maps: `symmetry-constrained-full-all-maps`. -/
def allMaps : Maps3 where
  Arr _ := True
  arr_id := trivial
  arr_comp _ _ := trivial
  arr_perm _ := trivial

/-- The six permutations and the three collapses: `symmetry-constrained-full-collapse`. -/
def permsCollapses : Maps3 where
  Arr f := Function.Bijective f ∨ ∃ i, ∀ x, f x = i
  arr_id := Or.inl Function.bijective_id
  arr_comp {f g} hf hg := by
    rcases hg with hg | ⟨i, hi⟩
    · rcases hf with hf | ⟨j, hj⟩
      · exact Or.inl (hg.comp hf)
      · exact Or.inr ⟨g j, fun x => by simp [Function.comp, hj]⟩
    · exact Or.inr ⟨i, fun x => hi _⟩
  arr_perm hf := Or.inl hf

end SymFull

end Classicism.Meta.Intensional
