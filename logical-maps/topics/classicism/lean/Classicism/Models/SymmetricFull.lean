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

Here the member whose arrows are all `27` maps, `symmetry-constrained-full-all-maps`: its
permutations are arrows, so the symmetry condition is Dorr's. (The member with the identity
and the collapses only, whose permutations are not arrows, relabels by conjugation instead,
and is not here.)
-/

namespace Classicism.Meta.Intensional

open CategoryTheory

namespace SymFull

/-- All maps on `Fin 3`, one object. -/
def allMaps : FunCat where
  Obj := Unit
  X _ := Fin 3
  Arr _ := True
  arr_id _ := trivial
  arr_comp _ _ := trivial

/-- The object. -/
abbrev star : allMaps.Ob := ()

/-- The symmetries: the arrows that are permutations. -/
def perms (V : allMaps.Ob) : Set (V ⟶ V) := {g | Function.Bijective (FunCat.fn g)}

/-- The permutations are closed under inverses. -/
theorem perms_symGroup : SymGroup perms := by
  intro V g hg
  let e := Equiv.ofBijective _ hg
  refine ⟨FunCat.arr (F := allMaps) (i := V) (j := V) e.symm trivial, e.symm.bijective, ?_, ?_⟩
  · exact FunCat.hom_ext (funext fun x => e.symm_apply_apply x)
  · exact FunCat.hom_ext (funext fun x => e.apply_symm_apply x)

/-- **The symmetry-constrained full model on all maps of a three-element set.** -/
noncomputable abbrev model : Premodel Signature.pure allMaps.Ob :=
  Premodel.symIdeal allMaps.De perms star (fun _ => ⟨(0 : Fin 3)⟩) (fun c => nomatch c)

theorem model_isModel : model.IsModel := symIdeal_isModel perms_symGroup

/-! ### The conditions it meets -/

instance : Subsingleton allMaps.Ob := inferInstanceAs (Subsingleton Unit)

theorem homs_finite (V U : allMaps.Ob) : Finite (V ⟶ U) := by
  have : Finite (allMaps.X V → allMaps.X U) := inferInstanceAs (Finite (Fin 3 → Fin 3))
  exact Subtype.finite

/-- `finitely-many-propositions`: a proposition is a set of tuples, and there are finitely
many tuples, one for each of the finitely many arrows. -/
theorem finitely_many_propositions : model.FinitelyManyPropositions := by
  have := homs_finite
  have : Finite (Set (Σ V : allMaps.Ob, PUnit × (star ⟶ V))) := by
    have : Finite allMaps.Ob := inferInstanceAs (Finite Unit)
    infer_instance
  show Finite {A : Set (Σ V : allMaps.Ob, PUnit × (star ⟶ V)) // _}
  exact Subtype.finite

/-- `finitely-many-propositions-everywhere`: likewise at every object, there being one. -/
theorem finitely_many_propositions_everywhere : model.FinitelyManyPropositionsEverywhere :=
  fun {V} _ => by
    obtain rfl : V = star := Subsingleton.elim _ _
    exact finitely_many_propositions

/-! ### Orbits: extensional fullness and the isolated actual world -/

instance (i : allMaps.Ob) : Finite (allMaps.X i) := inferInstanceAs (Finite (Fin 3))
instance (i : allMaps.Ob) : Finite (allMaps.De.obj i) := inferInstanceAs (Finite (Fin 3))

/-- Two arrows agreeing on every individual are equal, so everything is pinned down by the
finite set of all individuals. -/
theorem pinned_univ {ρ : RTy} (F : Intension (SymT allMaps.De perms) ρ star) :
    ∃ N : Set (allMaps.De.obj star), N.Finite ∧
      ∀ (V : allMaps.Ob) (h i : star ⟶ V), AgreeOn allMaps.De N h i →
        Intension.map (SymT allMaps.De perms) h F = Intension.map (SymT allMaps.De perms) i F :=
  ⟨Set.univ, Set.toFinite _, fun _ h i ha => by
    rw [(FunCat.hom_ext (funext fun x => (ha x (Set.mem_univ x) : FunCat.fn h x = FunCat.fn i x)) : h = i)]⟩

/-- The orbit of a set of argument tuples: `g ȳ` at each permutation `g`, for `ȳ` in the set. -/
def orbit {ρ : RTy} (E : Set (Args (SymT allMaps.De perms) ρ star)) : Intension (SymT allMaps.De perms) ρ star :=
  {p | ∃ (g : star ⟶ star), g ∈ perms star ∧ ∃ b ∈ E,
    p = (⟨star, Args.map (SymT allMaps.De perms) ρ g b, g⟩ : Tuple (SymT allMaps.De perms) ρ star)}

theorem perms_comp {g s : star ⟶ star} (hg : g ∈ perms star) (hs : s ∈ perms star) :
    g ≫ s ∈ perms star := hs.comp hg

theorem orbit_sym {ρ : RTy} (E : Set (Args (SymT allMaps.De perms) ρ star)) :
    SymCond allMaps.De perms (orbit E) := by
  rintro V a k s hs ⟨g, hg, b, hb, he⟩
  cases he
  exact ⟨g ≫ s, perms_comp hg hs, b, hb, by rw [Args.map_comp]⟩

theorem orbit_mem {ρ : RTy} (E : Set (Args (SymT allMaps.De perms) ρ star)) :
    orbit E ∈ Set.range ((model).incl ρ star) :=
  (mem_range_symIncl allMaps.De perms ρ star _).2 ⟨pinned_univ _, orbit_sym E⟩

/-- The identity is the only permutation that is the identity tuple's arrow. -/
theorem mem_orbit_id {ρ : RTy} (E : Set (Args (SymT allMaps.De perms) ρ star)) (a : Args (SymT allMaps.De perms) ρ star) :
    (⟨star, a, 𝟙 star⟩ : Tuple (SymT allMaps.De perms) ρ star) ∈ orbit E ↔ a ∈ E := by
  constructor
  · rintro ⟨g, -, b, hb, he⟩
    obtain ⟨-, he⟩ := Sigma.mk.inj_iff.1 he
    have he := eq_of_heq he
    obtain ⟨ha, hg⟩ := Prod.mk.inj he
    subst hg
    rw [ha, Args.map_id]; exact hb
  · intro ha
    exact ⟨𝟙 star, Function.bijective_id, a, ha, by rw [Args.map_id]⟩

/-- `extensionally-full`: any set of tuples at the identity is the extension there of its
orbit, which is symmetric. -/
theorem extFull : model.ExtFull := by
  intro ρ W E
  cases W
  obtain ⟨x, hx⟩ := orbit_mem E
  refine ⟨x, ?_⟩
  ext a
  show (⟨star, a, 𝟙 star⟩ : Tuple (SymT allMaps.De perms) ρ star) ∈ model.incl ρ star x ↔ a ∈ E
  rw [hx]
  exact mem_orbit_id E a

/-- An arrow whose composite with another is a permutation is one: it is injective, and
the set is finite. -/
theorem perm_of_comp_perm {i j : star ⟶ star} (h : i ≫ j ∈ perms star) : i ∈ perms star := by
  have hinj : Function.Injective (FunCat.fn i) := fun x y e => h.1 (by
    show FunCat.fn j (FunCat.fn i x) = FunCat.fn j (FunCat.fn i y); rw [e])
  exact (Finite.injective_iff_bijective).1 hinj

/-- `actual-world-isolated`: the actual-world proposition is the orbit of the identity, the
permutations; no arrow from a non-permutation leads back to one. -/
theorem actualWorldIsolated : model.ActualWorldIsolated := by
  obtain ⟨a, ha⟩ := orbit_mem (ρ := .t) Set.univ
  refine ⟨a, ?_, fun p hp => ?_, fun {V U} i j hi => ?_⟩
  · show (⟨star, PUnit.unit, 𝟙 star⟩ : Tuple (SymT allMaps.De perms) .t star) ∈ model.incl .t star a
    rw [ha, mem_orbit_id]; trivial
  · show model.incl .t star a ⊆ model.incl .t star p
    rw [ha]
    rintro _ ⟨g, hg, ⟨⟩, -, rfl⟩
    have := Premodel.Sym.at_id (symIdeal_domSym .t star p) PUnit.unit hg hp
    exact this
  · cases V; cases U
    change (⟨star, PUnit.unit, i⟩ : Tuple (SymT allMaps.De perms) .t star) ∉ model.incl .t star a at hi
    show (⟨star, PUnit.unit, i ≫ j⟩ : Tuple (SymT allMaps.De perms) .t star) ∉ model.incl .t star a
    rw [ha] at hi ⊢
    rintro ⟨g, hg, ⟨⟩, -, he⟩
    obtain ⟨-, he⟩ := Sigma.mk.inj_iff.1 he
    have he := (Prod.mk.inj (eq_of_heq he)).2
    exact hi ⟨i, perm_of_comp_perm (he ▸ hg), PUnit.unit, trivial, rfl⟩

end SymFull

end Classicism.Meta.Intensional
