import Classicism.Semantics.IntensionalExamples
import Classicism.Models.Functions
import Classicism.Models.Conditions
import Classicism.Semantics.Arrows
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finite.Sigma
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# The full action models of *Classicism* §3

The map's group `full-action-models`, each member with one individual (its records' setting):
the full intensional action model with the constant action `Unit` for `e`, on

- the monoid of surjections of `ℕ` (`full-surjection-monoid`),
- the group of permutations of `ℕ` (`full-permutation-group-infinite-set`),
- the two-object chain `W₀ → W₁` (`full-two-object-chain`), the category `Fin 2` ordered,
- the retract: `h : W₀ → W₁`, `j : W₁ → W₀` with `j ∘ h = 1`, and `k = h ∘ j`
  (`full-two-object-retract`), as a category of sets and functions;

besides the two M-set models on two-element monoids (`Semantics/IntensionalExamples.lean`).
Here are the models, the verdicts particular to them, and their proofs that they meet the
conditions of the map's general arguments.

General facts about full models used: `ND_t` fails when an arrow out of the base has no
retraction (`full_not_nd_t`), and `ND` holds at every type when every arrow out of the base
has one (`Premodel.holds_nd_of_retractions`, `Semantics/Arrows.lean`).
-/

namespace Classicism.Meta.Intensional

open CategoryTheory

/-! ### Full models with one individual, on any category -/


/-- In a full model, `ND_t` fails when some arrow out of the base has no retraction: its
transport identifies `∅` and `{1}`. -/
theorem full_not_nd_t {C : Type} [SmallCategory C] (De : C ⥤ Type) (W₀ : C)
    (ne : ∀ W : C, Nonempty (De.obj W)) {V : C} (k : W₀ ⟶ V) (hk : ∀ m : V ⟶ W₀, k ≫ m ≠ 𝟙 W₀) :
    ¬ (Premodel.full (Sig := Signature.pure) De W₀ ne (fun c => nomatch c)).HoldsSentence
      (Sentence.nd (.rel .t)) := by
  intro H
  rw [Premodel.HoldsSentence, Premodel.holds_nd_iff _ (Premodel.full_isModel De)] at H
  have hinj := @H V k
  have e : (FullT De (.rel .t)).map k (∅ : Set (Σ U : C, PUnit × (W₀ ⟶ U))) =
      (FullT De (.rel .t)).map k ({⟨W₀, PUnit.unit, 𝟙 W₀⟩} : Set (Σ U : C, PUnit × (W₀ ⟶ U))) := by
    apply Set.ext
    rintro ⟨U, ⟨⟩, m⟩
    show _ ∈ (∅ : Set _) ↔ (⟨U, PUnit.unit, k ≫ m⟩ : Σ U : C, PUnit × (W₀ ⟶ U)) ∈ ({⟨W₀, PUnit.unit, 𝟙 W₀⟩} : Set _)
    simp only [Set.mem_empty_iff_false, Set.mem_singleton_iff, false_iff]
    intro h
    obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp h
    exact hk m (Prod.mk.inj (eq_of_heq hh)).2
  have := hinj e
  exact Set.notMem_empty _ (this ▸ Set.mem_singleton (⟨W₀, PUnit.unit, 𝟙 W₀⟩ : Σ U : C, PUnit × (W₀ ⟶ U)))

namespace FullActionModels

variable {C : Type} [SmallCategory C]

/-- The constant action `Unit`: one individual at every object. -/
def unitDe (C : Type) [SmallCategory C] : C ⥤ Type := (Functor.const C).obj Unit

/-- The full model on a category with one individual, based at `W₀`, with no constants. -/
noncomputable def unitModel (W₀ : C) : Premodel Signature.pure C :=
  Premodel.full (unitDe C) W₀ (fun _ => ⟨()⟩) (fun c => nomatch c)

theorem unitModel_isModel (W₀ : C) : (unitModel W₀).IsModel := Premodel.full_isModel _

theorem unitModel_full (W₀ : C) : (unitModel W₀).Full := fun ρ W => fullIncl_surjective _ ρ W

theorem unitModel_one_individual (W₀ : C) : (unitModel W₀).OneIndividual :=
  fun _ => inferInstanceAs (Subsingleton Unit)

/-! ### The surjections of `ℕ` -/

/-- The monoid of surjections of `ℕ`. -/
def surj : Submonoid (Function.End ℕ) where
  carrier := {f | Function.Surjective f}
  one_mem' := Function.surjective_id
  mul_mem' hf hg := hf.comp hg

/-- Halving, a surjection that is not injective, so has no left inverse. -/
def half : surj := ⟨fun n => n / 2, fun y => ⟨2 * y, by show 2 * y / 2 = y; omega⟩⟩

theorem half_ne_one : half ≠ 1 := fun e => by
  have := congrArg (fun f : surj => (f : Function.End ℕ) 1) e
  exact absurd this (by decide)

/-- `ND_t` fails: transport along halving identifies `∅` and `{1}`, since no surjection
undoes it. -/
theorem surj_not_nd_t : ¬ (MSet.model surj).HoldsSentence (Sentence.nd (.rel .t)) :=
  full_not_nd_t (MSet.unitAction surj) (SingleObj.star surj) (fun _ => ⟨()⟩) (V := SingleObj.star surj)
    (half : SingleObj.star surj ⟶ SingleObj.star surj) fun m' e => by
    let m : surj := m'
    have e' : (m * half : surj) = 1 := e
    have e : ((m * half : surj) : Function.End ℕ) = 1 := congrArg Subtype.val e'
    have h0 : ((m * half : surj) : Function.End ℕ) 0 = 0 := by rw [e]; rfl
    have h1 : ((m * half : surj) : Function.End ℕ) 1 = 1 := by rw [e]; rfl
    have h01 : ((m * half : surj) : Function.End ℕ) 0 = ((m * half : surj) : Function.End ℕ) 1 := rfl
    exact absurd (h0.symm.trans (h01.trans h1)) (by decide)

theorem surj_not_fregean : ¬ (MSet.model surj).HoldsSentence Sentence.fregean :=
  MSet.not_fregean surj half half_ne_one

/-! ### The permutations of `ℕ` -/

theorem perm_box_nd (σ : Ty) : (MSet.model (Equiv.Perm ℕ)).HoldsSentence (Term.box (Sentence.nd σ)) :=
  Premodel.holds_box_nd_of_groupoid _ (MSet.model_isModel _) σ

theorem perm_box_bf (σ : Ty) : (MSet.model (Equiv.Perm ℕ)).HoldsSentence (Term.box (Sentence.bf σ)) :=
  Premodel.holds_box_bf_of_groupoid _ (MSet.model_isModel _) σ

theorem perm_not_fregean : ¬ (MSet.model (Equiv.Perm ℕ)).HoldsSentence Sentence.fregean :=
  MSet.not_fregean _ (Equiv.swap 0 1) fun e => by
    have := congrArg (fun f : Equiv.Perm ℕ => f 0) e
    simp at this

/-! ### The chain `W₀ → W₁` -/

/-- The chain, based at its first object. -/
noncomputable abbrev chain : Premodel Signature.pure (Fin 2) := unitModel 0

/-- The arrow `W₀ → W₁`. -/
def chainArrow : (0 : Fin 2) ⟶ 1 := homOfLE (by decide)

theorem chain_not_nd_t : ¬ chain.HoldsSentence (Sentence.nd (.rel .t)) :=
  full_not_nd_t (unitDe (Fin 2)) 0 (fun _ => ⟨()⟩) chainArrow fun m => absurd (leOfHom m) (by decide)

theorem chain_not_fregean : ¬ chain.HoldsSentence Sentence.fregean :=
  chain.not_fregean_of_propFull (unitModel_isModel _) (unitModel_full _).propFull chainArrow
    fun e => absurd (congrArg Sigma.fst e) (by decide)

/-- Finitely many propositions at the base: sets of the two arrows out of it. -/
theorem chain_finitely_many_propositions : chain.FinitelyManyPropositions := by
  have : ∀ V W : Fin 2, Finite (V ⟶ W) := fun _ _ => inferInstanceAs (Finite (ULift (PLift _)))
  change Finite (Set (Σ V : Fin 2, PUnit × ((0 : Fin 2) ⟶ V)))
  infer_instance

/-- The actual-world proposition `{1}` is isolated: the only other arrow goes to `W₁`, out of
which there is only the identity. -/
theorem chain_actual_world_isolated : chain.ActualWorldIsolated := by
  obtain ⟨a, ha⟩ := unitModel_full (0 : Fin 2) .t 0
    ({⟨0, PUnit.unit, 𝟙 0⟩} : Set (Σ V : Fin 2, PUnit × ((0 : Fin 2) ⟶ V)))
  refine ⟨a, ?_, fun p hp => ?_, fun {V U} i j hi => ?_⟩
  · change (⟨0, PUnit.unit, 𝟙 0⟩ : Σ V : Fin 2, PUnit × ((0 : Fin 2) ⟶ V)) ∈ chain.incl .t 0 a
    exact ha ▸ Set.mem_singleton _
  · change chain.incl .t 0 a ⊆ chain.incl .t 0 p
    rw [ha]
    intro t ht
    rw [Set.mem_singleton_iff.1 ht]
    exact hp
  · change (⟨V, PUnit.unit, i⟩ : Σ V : Fin 2, PUnit × ((0 : Fin 2) ⟶ V)) ∉ chain.incl .t 0 a at hi
    change (⟨U, PUnit.unit, i ≫ j⟩ : Σ V : Fin 2, PUnit × ((0 : Fin 2) ⟶ V)) ∉ chain.incl .t 0 a
    rw [ha] at hi ⊢
    intro h
    obtain ⟨rfl, _⟩ := Sigma.mk.inj_iff.mp h
    -- `U = 0`, so `V = 0` (`0 ≤ V ≤ 0`), and `i` is the identity
    have hV : V = 0 := le_antisymm (leOfHom j) (Fin.zero_le V)
    subst hV
    exact hi (Set.mem_singleton_iff.2 rfl)

/-! ### The retract -/

/-- The category of the retract, as sets and functions: `W₀ = Unit`, `W₁ = Bool`, with
`h = (· ↦ false) : W₀ → W₁`, `j : W₁ → W₀`, and on `W₁` the identity and `k = (· ↦ false)`. -/
def retractCat : FunCat where
  Obj := Bool
  X
    | true => Bool
    | false => Unit
  Arr {i j} f := match i, j, f with
    | true, true, f => f = id ∨ f = fun _ => false
    | false, true, f => f () = false
    | _, false, _ => True
  arr_id i := by cases i <;> simp
  arr_comp {i j k} {f g} hf hg := by
    cases i <;> cases j <;> cases k <;> simp only at hf hg ⊢
    · exact hg
    · show g (f ()) = false
      rcases hg with rfl | rfl <;> simp [hf]
    · exact Or.inr (funext fun _ => hg)
    · rcases hf with rfl | rfl <;> rcases hg with rfl | rfl
      · exact Or.inl rfl
      all_goals simp [Function.comp_def]

/-- The objects `W₀` and `W₁` of the retract. -/
abbrev W₀ : retractCat.Ob := (false : Bool)
abbrev W₁ : retractCat.Ob := (true : Bool)

/-- `h : W₀ → W₁`. -/
def rh : W₀ ⟶ W₁ := FunCat.arr (F := retractCat) (i := W₀) (j := W₁) (fun _ => false) rfl
/-- `j : W₁ → W₀`. -/
def rj : W₁ ⟶ W₀ := FunCat.arr (F := retractCat) (i := W₁) (j := W₀) (fun _ => ()) trivial
/-- `k = h ∘ j : W₁ → W₁`. -/
def rk : W₁ ⟶ W₁ := FunCat.arr (F := retractCat) (i := W₁) (j := W₁) (fun _ => false) (Or.inr rfl)

theorem rh_rk : rh ≫ rk = rh := FunCat.hom_ext (funext fun _ => rfl)

theorem rk_ne_id : rk ≠ 𝟙 W₁ := fun e => Bool.false_ne_true (congrFun (congrArg FunCat.fn e) true)

/-- The retract, based at `W₀`. -/
noncomputable abbrev retract : Premodel Signature.pure retractCat.Ob := unitModel W₀

/-- Every arrow out of `W₀` has a retraction: the identity, or `h`, undone by `j`. -/
theorem retract_retractions : ∀ {V : retractCat.Ob} (i : W₀ ⟶ V), ∃ r : V ⟶ W₀, i ≫ r = 𝟙 W₀
  | V, i => by
    refine ⟨FunCat.arr (F := retractCat) (i := V) (j := W₀) (fun _ => ()) (by cases V <;> trivial), ?_⟩
    exact FunCat.hom_ext (funext fun _ => rfl)

/-- `ND` holds at every type: every arrow out of the base has a retraction. -/
theorem retract_nd (σ : Ty) : retract.HoldsSentence (Sentence.nd σ) :=
  Premodel.holds_nd_of_retractions (unitModel_isModel _) retract_retractions σ

theorem retract_not_fregean : ¬ retract.HoldsSentence Sentence.fregean :=
  retract.not_fregean_of_propFull (unitModel_isModel _) (unitModel_full _).propFull rh
    fun e => Bool.false_ne_true (congrArg Sigma.fst e).symm

/-- `BF_t` fails: transport along `h` is not onto the propositions at `W₁`, since it puts the
identity and `k` in or out together (`h ∘ k = h`); `{1}` is the transport of nothing. -/
theorem retract_not_bf_t : ¬ retract.HoldsSentence (Sentence.bf (.rel .t)) := by
  intro H
  obtain ⟨X, hX⟩ := @Premodel.full_bf_surjective _ _ (unitDe _) _ W₀ _ _ (.rel .t) H W₁ rh
    ({⟨W₁, PUnit.unit, 𝟙 W₁⟩} : Set (Σ U : retractCat.Ob, PUnit × (W₁ ⟶ U)))
  have h1 : (⟨W₁, PUnit.unit, 𝟙 W₁⟩ : Σ U : retractCat.Ob, PUnit × (W₁ ⟶ U)) ∈
      (FullT (unitDe _) (.rel .t)).map rh X := hX ▸ Set.mem_singleton _
  have h2 : (⟨W₁, PUnit.unit, rk⟩ : Σ U : retractCat.Ob, PUnit × (W₁ ⟶ U)) ∈
      (FullT (unitDe _) (.rel .t)).map rh X := by
    show (⟨W₁, PUnit.unit, rh ≫ rk⟩ : Σ U : retractCat.Ob, PUnit × (W₀ ⟶ U)) ∈ X
    rw [rh_rk]
    have h1 : (⟨W₁, PUnit.unit, rh ≫ 𝟙 W₁⟩ : Σ U : retractCat.Ob, PUnit × (W₀ ⟶ U)) ∈ X := h1
    rwa [Category.comp_id] at h1
  rw [hX, Set.mem_singleton_iff] at h2
  obtain ⟨_, hh⟩ := Sigma.mk.inj_iff.mp h2
  exact rk_ne_id (Prod.mk.inj (eq_of_heq hh)).2

/-! ### The conditions on arrows each model meets -/

/-- In a monoid of surjections, every arrow is an epimorphism. -/
theorem surj_epi {V U : SingleObj surj} (k : V ⟶ U) : Epi k := ⟨fun {_} g g' e => by
  let k' : surj := k
  let g₁ : surj := g
  let g₂ : surj := g'
  have e' : g₁ * k' = g₂ * k' := e
  show g₁ = g₂
  apply Subtype.ext
  funext n
  obtain ⟨n', rfl⟩ := k'.2 n
  exact congrFun (congrArg Subtype.val e') n'⟩

theorem surj_epic : (MSet.model surj).EpicArrows :=
  fun _ k => ⟨surj_epi k, fun y => ⟨y, Subsingleton.elim (α := Unit) _ _⟩⟩

/-- Halving has no retraction among the surjections: `m ∘ half` identifies `0` and `1`. -/
theorem half_unretracted : ∀ m : SingleObj.star surj ⟶ SingleObj.star surj,
    (half : SingleObj.star surj ⟶ SingleObj.star surj) ≫ m ≠ 𝟙 _ := fun m' e => by
  let m : surj := m'
  have e' : (m * half : surj) = 1 := e
  have e : ((m * half : surj) : Function.End ℕ) = 1 := congrArg Subtype.val e'
  have h0 : ((m * half : surj) : Function.End ℕ) 0 = 0 := by rw [e]; rfl
  have h1 : ((m * half : surj) : Function.End ℕ) 1 = 1 := by rw [e]; rfl
  have h01 : ((m * half : surj) : Function.End ℕ) 0 = ((m * half : surj) : Function.End ℕ) 1 := rfl
  exact absurd (h0.symm.trans (h01.trans h1)) (by decide)

theorem surj_unretracted : (MSet.model surj).UnretractedArrow :=
  ⟨_, half, half_unretracted⟩

/-- An element other than `1` of a monoid is an arrow other than the identity. -/
theorem mset_nonidentity {M : Type} [Monoid M] (m : M) (hm : m ≠ 1) : (MSet.model M).NonidentityArrow :=
  ⟨_, (m : SingleObj.star M ⟶ SingleObj.star M), fun e =>
    hm (MSet.arrow_injective M (e.trans (MSet.arrow_id M)))⟩

theorem surj_nonidentity : (MSet.model surj).NonidentityArrow := mset_nonidentity half half_ne_one

/-- In a group, every arrow is invertible. -/
theorem group_invertible (G : Type) [Group G] : (MSet.model G).InvertibleArrows := fun _ k =>
  ⟨⟨(show G from k)⁻¹, by
    show (show G from k)⁻¹ * (show G from k) = 1
    exact inv_mul_cancel _, by
    show (show G from k) * (show G from k)⁻¹ = 1
    exact mul_inv_cancel _⟩⟩

theorem group_epic (G : Type) [Group G] : (MSet.model G).EpicArrows := fun h k =>
  ⟨have := group_invertible G h k; inferInstance, fun y => ⟨y, Subsingleton.elim (α := Unit) _ _⟩⟩

theorem perm_nonidentity : (MSet.model (Equiv.Perm ℕ)).NonidentityArrow :=
  mset_nonidentity (Equiv.swap 0 1) fun e => by
    have := congrArg (fun f : Equiv.Perm ℕ => f 0) e
    simp at this

theorem chain_epic : chain.EpicArrows :=
  fun _ _ => ⟨⟨fun _ _ _ => Subsingleton.elim _ _⟩, fun y => ⟨y, Subsingleton.elim (α := Unit) _ _⟩⟩

theorem chain_unretracted : chain.UnretractedArrow :=
  ⟨1, chainArrow, fun m => absurd (leOfHom m) (by decide)⟩

theorem chain_nonidentity : chain.NonidentityArrow :=
  ⟨1, chainArrow, fun e => absurd (congrArg Sigma.fst e) (by decide)⟩

theorem retract_nonidentity : retract.NonidentityArrow :=
  ⟨W₁, rh, fun e => Bool.false_ne_true (congrArg Sigma.fst e).symm⟩

/-! ### How many propositions -/

/-- A full M-set model on a finite monoid has finitely many propositions at its one object. -/
theorem mset_finitely_many_everywhere (M : Type) [Monoid M] [Finite M] :
    (MSet.model M).FinitelyManyPropositionsEverywhere := fun {V} _ => by
  have : Finite (SingleObj M) := inferInstanceAs (Finite Unit)
  have : ∀ V W : SingleObj M, Finite (V ⟶ W) := fun _ _ => inferInstanceAs (Finite M)
  change Finite (Set (Σ U : SingleObj M, PUnit × (V ⟶ U)))
  infer_instance

/-- A full M-set model on an infinite monoid has infinitely many propositions: the singletons of
the arrows. -/
theorem mset_infinitely_many_propositions (M : Type) [Monoid M] [Infinite M] :
    (MSet.model M).InfinitelyManyPropositions := by
  change Infinite (Set (Σ U : SingleObj M, PUnit × (SingleObj.star M ⟶ U)))
  have : Infinite (Σ U : SingleObj M, PUnit × (SingleObj.star M ⟶ U)) :=
    Infinite.of_injective (fun m : M => (⟨SingleObj.star M, PUnit.unit, m⟩ : Σ U : SingleObj M, PUnit × (SingleObj.star M ⟶ U)))
      fun m n e => by
        obtain ⟨_, hh⟩ := Sigma.mk.inj_iff.mp e
        exact (Prod.mk.inj (eq_of_heq hh)).2
  exact Infinite.of_injective (fun x => ({x} : Set _)) Set.singleton_injective

/-- The surjections `m ↦ m ∸ n` are infinitely many. -/
instance : Infinite surj :=
  Infinite.of_injective (fun n : ℕ => (⟨fun m => m - n, fun y => ⟨y + n, by show y + n - n = y; omega⟩⟩ : surj))
    fun a b e => by
      have := congrFun (congrArg Subtype.val e) (a + b + 1)
      change a + b + 1 - a = a + b + 1 - b at this
      omega

theorem chain_finitely_many_everywhere : chain.FinitelyManyPropositionsEverywhere := fun {V} _ => by
  have : ∀ V W : Fin 2, Finite (V ⟶ W) := fun _ _ => inferInstanceAs (Finite (ULift (PLift _)))
  change Finite (Set (Σ U : Fin 2, PUnit × (V ⟶ U)))
  infer_instance

theorem retract_homs_finite : ∀ V U : retractCat.Ob, Finite (V ⟶ U)
  | false, false => by
    have : Finite (retractCat.X false → retractCat.X false) := inferInstanceAs (Finite (Unit → Unit))
    exact Subtype.finite
  | false, true => by
    have : Finite (retractCat.X false → retractCat.X true) := inferInstanceAs (Finite (Unit → Bool))
    exact Subtype.finite
  | true, false => by
    have : Finite (retractCat.X true → retractCat.X false) := inferInstanceAs (Finite (Bool → Unit))
    exact Subtype.finite
  | true, true => by
    have : Finite (retractCat.X true → retractCat.X true) := inferInstanceAs (Finite (Bool → Bool))
    exact Subtype.finite

theorem retract_finitely_many_everywhere : retract.FinitelyManyPropositionsEverywhere := fun {V} _ => by
  have : Finite retractCat.Ob := inferInstanceAs (Finite Bool)
  have := retract_homs_finite
  change Finite (Set (Σ U : retractCat.Ob, PUnit × (V ⟶ U)))
  infer_instance

theorem retract_finitely_many_propositions : retract.FinitelyManyPropositions :=
  retract_finitely_many_everywhere (𝟙 _)

/-- `W₀` has four propositions, and `W₁`, out of which there is only the identity, two. -/
theorem chain_fewer_propositions_after : chain.FewerPropositionsAfter := by
  refine ⟨3, 1, chainArrow, ?_, fun U j f hf => ?_⟩
  · let t0 : Σ V : Fin 2, PUnit.{1} × ((0 : Fin 2) ⟶ V) := ⟨0, PUnit.unit, 𝟙 0⟩
    let t1 : Σ V : Fin 2, PUnit.{1} × ((0 : Fin 2) ⟶ V) := ⟨1, PUnit.unit, chainArrow⟩
    have h01 : t0 ≠ t1 := fun e => absurd (congrArg Sigma.fst e) (by decide : (0 : Fin 2) ≠ 1)
    let f : Fin 3 → Set (Σ V : Fin 2, PUnit.{1} × ((0 : Fin 2) ⟶ V)) := ![∅, {t0}, {t1}]
    refine ⟨f, fun i i' e => ?_⟩
    fin_cases i <;> fin_cases i' <;> simp only [f] at e <;>
      first
        | rfl
        | exact absurd e.symm (Set.singleton_ne_empty _)
        | exact absurd e (Set.singleton_ne_empty _)
        | exact absurd (Set.singleton_eq_singleton_iff.1 e) h01
        | exact absurd (Set.singleton_eq_singleton_iff.1 e).symm h01
  · have hU : U = 1 := le_antisymm (Fin.le_last U) (leOfHom j)
    subst hU
    have hs : Subsingleton (Σ W : Fin 2, PUnit.{1} × ((1 : Fin 2) ⟶ W)) := ⟨by
      rintro ⟨W, ⟨⟩, h⟩ ⟨W', ⟨⟩, h'⟩
      obtain rfl : W = 1 := le_antisymm (Fin.le_last W) (leOfHom h)
      obtain rfl : W' = 1 := le_antisymm (Fin.le_last W') (leOfHom h')
      obtain rfl : h = h' := Subsingleton.elim _ _
      rfl⟩
    have univ_of : ∀ S : Set (Σ W : Fin 2, PUnit.{1} × ((1 : Fin 2) ⟶ W)), S.Nonempty → S = Set.univ :=
      fun S ⟨y, hy⟩ => Set.eq_univ_of_forall fun x => Subsingleton.elim y x ▸ hy
    let g : Set (Σ W : Fin 2, PUnit.{1} × ((1 : Fin 2) ⟶ W)) → Bool :=
      fun S => @decide S.Nonempty (Classical.dec _)
    have hg : Function.Injective g := by
      intro S S' e
      by_cases hS : S.Nonempty <;> by_cases hS' : S'.Nonempty
      · rw [univ_of S hS, univ_of S' hS']
      · simp [g, hS, hS'] at e
      · simp [g, hS, hS'] at e
      · rw [Set.not_nonempty_iff_eq_empty.1 hS, Set.not_nonempty_iff_eq_empty.1 hS']
    let f' : Fin 3 → Set (Σ W : Fin 2, PUnit.{1} × ((1 : Fin 2) ⟶ W)) := f
    have := Fintype.card_le_of_injective (g ∘ f') (hg.comp hf)
    simp at this

/-! ### Non-epi arrows, returning arrows and coherent retractions -/

/-- An element other than `1` with a left inverse is an arrow other than the identity that
returns. -/
theorem mset_returning {M : Type} [Monoid M] (m r : M) (hm : m ≠ 1) (hr : r * m = 1) :
    (MSet.model M).ReturningArrow :=
  ⟨_, (m : SingleObj.star M ⟶ SingleObj.star M), (r : SingleObj.star M ⟶ SingleObj.star M), hr,
    fun e => hm (MSet.arrow_injective M (e.trans (MSet.arrow_id M)))⟩

theorem group_returning {G : Type} [Group G] (g : G) (hg : g ≠ 1) : (MSet.model G).ReturningArrow :=
  mset_returning g g⁻¹ hg (inv_mul_cancel g)

theorem perm_returning : (MSet.model (Equiv.Perm ℕ)).ReturningArrow :=
  group_returning (Equiv.swap 0 1) fun e => by
    have := congrArg (fun f : Equiv.Perm ℕ => f 0) e
    simp at this

/-- The swap of `0` and `1`, a surjection undone by itself. -/
def swap01 : surj := ⟨⇑(Equiv.swap (0 : ℕ) 1), (Equiv.swap (0 : ℕ) 1).surjective⟩

theorem surj_returning : (MSet.model surj).ReturningArrow :=
  mset_returning swap01 swap01 (fun e => by
      have : (Equiv.swap (0 : ℕ) 1) 0 = 0 := congrFun (congrArg Subtype.val e) 0
      simp at this)
    (Subtype.ext (funext fun n => show (Equiv.swap (0 : ℕ) 1) ((Equiv.swap (0 : ℕ) 1) n) = n from
      Equiv.swap_apply_self 0 1 n))

/-- In a group, `r_g := g⁻¹` are coherent retractions. -/
theorem group_coherent (G : Type) [Group G] : (MSet.model G).CoherentRetractions :=
  ⟨fun g => ((show G from g)⁻¹ : G), fun g => inv_mul_cancel (show G from g), fun g x => by
    show (show G from x * g)⁻¹ * (show G from x) = (show G from g)⁻¹
    rw [mul_inv_rev, inv_mul_cancel_right]⟩

/-- `1·k = k·k` with `1 ≠ k`. -/
theorem idem_nonepic : (MSet.model Idem).NonepicArrow :=
  ⟨SingleObj.star Idem, SingleObj.star Idem, (Idem.k : SingleObj.star Idem ⟶ SingleObj.star Idem),
    ((1 : Idem) : SingleObj.star Idem ⟶ SingleObj.star Idem),
    (Idem.k : SingleObj.star Idem ⟶ SingleObj.star Idem), Idem.k_ne_one.symm, rfl⟩

/-- `1 ∘ h = k ∘ h` with `1 ≠ k`. -/
theorem retract_nonepic : retract.NonepicArrow :=
  ⟨W₁, W₁, rh, 𝟙 W₁, rk, rk_ne_id.symm, rh_rk.symm⟩

/-- `h`, undone by `j`. -/
theorem retract_returning : retract.ReturningArrow :=
  ⟨W₁, rh, rj, FunCat.hom_ext (funext fun _ => rfl),
    fun e => Bool.false_ne_true (congrArg Sigma.fst e).symm⟩

/-- Every arrow into `W₀` is the one function to `Unit`, so any retractions are coherent. -/
theorem retract_coherent : retract.CoherentRetractions :=
  ⟨fun {V} _ => FunCat.arr (F := retractCat) (i := V) (j := W₀) (fun _ => ()) (by cases V <;> trivial),
    fun _ => FunCat.hom_ext (funext fun _ => rfl), fun _ _ => FunCat.hom_ext (funext fun _ => rfl)⟩

end FullActionModels

end Classicism.Meta.Intensional
