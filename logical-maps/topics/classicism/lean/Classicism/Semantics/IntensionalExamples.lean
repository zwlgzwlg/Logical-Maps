import Classicism.Semantics.IntensionalFull
import Classicism.Semantics.IntensionalProperties
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Groupoid.Basic

/-!
# Examples: full M-set models, in the intensional form

The paper's first examples (Classicism, §"Exploring action models"): full action models
on a category with one object, a monoid `M`, *M-set models*. Two monoids on `{1, k}`:
with `k·k = k`, in whose full model `ND_t` and the Fregean Axiom fail; and with `k·k = 1`,
the two-element group, in whose full model the Fregean Axiom fails but `ND_σ` holds at
every type, necessarily, since every arrow is an isomorphism. These are the map's
records `full-idempotent-monoid` and `full-involution-group`.

Also two general facts: at an object all of whose out-arrows are isomorphisms, `ND_σ`
and `BF_σ` hold at every type; so in a full model on a groupoid, `□ND_σ` and `□BF_σ`.

This is the port of `ActionExamples.lean` to intensional action models: the same
verdicts, with a proposition now a set of tuples `⟨(), m⟩` rather than of arrows `m`.
-/

namespace Classicism.Meta.Intensional

open CategoryTheory

/-! ### Isomorphisms give `ND` and `BF` -/

namespace Premodel

section
variable {Sig : Signature} {C : Type} [SmallCategory C] (A : Premodel Sig C) (M : A.IsModel)
include M

theorem holds_nd_of_iso (σ : Ty) {W : C} (h : A.W₀ ⟶ W) (hiso : ∀ {V : C} (k : W ⟶ V), IsIso k) :
    A.Holds h (Sentence.nd σ) .nil :=
  (A.holds_nd_iff M σ h).2 fun k => by
    have := hiso k
    exact ((isIso_iff_bijective _).1 inferInstance).1

theorem holds_bf_of_iso (σ : Ty) {W : C} (h : A.W₀ ⟶ W) (hiso : ∀ {V : C} (k : W ⟶ V), IsIso k) :
    A.Holds h (Sentence.bf σ) .nil :=
  A.holds_bf_of_surjective M σ h fun k => by
    have := hiso k
    exact ((isIso_iff_bijective _).1 inferInstance).2

end

section
variable {Sig : Signature} {C : Type} [Groupoid.{0} C] (A : Premodel Sig C) (M : A.IsModel)
include M

/-- In a model on a groupoid, `□ND_σ` at the base, for every `σ`. -/
theorem holds_box_nd_of_groupoid (σ : Ty) : A.HoldsSentence (Term.box (Sentence.nd σ)) :=
  (A.holds_box M _ _ _).2 fun k => by
    rw [IEnv.nil_eq (A.push k IEnv.nil)]
    exact A.holds_nd_of_iso M σ _ fun _ => inferInstance

theorem holds_box_bf_of_groupoid (σ : Ty) : A.HoldsSentence (Term.box (Sentence.bf σ)) :=
  (A.holds_box M _ _ _).2 fun k => by
    rw [IEnv.nil_eq (A.push k IEnv.nil)]
    exact A.holds_bf_of_iso M σ _ fun _ => inferInstance

end

end Premodel

/-! ### Full M-set models -/

namespace MSet

variable (M : Type) [Monoid M]

/-- The constant action `Unit`, for `e`. -/
def unitAction : SingleObj M ⥤ Type := (Functor.const (SingleObj M)).obj Unit

/-- The full intensional action model on the monoid `M`, with one individual and no
constants. -/
noncomputable def model : Premodel Signature.pure (SingleObj M) :=
  Premodel.full (unitAction M) (SingleObj.star M) (fun _ => ⟨()⟩) (fun c => nomatch c)

theorem model_isModel : (model M).IsModel := Premodel.full_isModel _

theorem model_full : (model M).Full := fun ρ W => fullIncl_surjective (unitAction M) ρ W

/-- The propositions at the object: sets of tuples `⟨(), m⟩`, one per arrow. -/
abbrev Prop' : Type := Set (Tuple (FullT (unitAction M)) .t (SingleObj.star M))

/-- An arrow out of the object, as a tuple of the propositional domain. -/
abbrev arrow (m : M) : Tuple (FullT (unitAction M)) .t (SingleObj.star M) :=
  ⟨SingleObj.star M, PUnit.unit, m⟩

/-- The identity arrow is `1`. -/
theorem arrow_id : (⟨SingleObj.star M, PUnit.unit, 𝟙 (SingleObj.star M)⟩ :
    Tuple (FullT (unitAction M)) .t (SingleObj.star M)) = arrow M 1 := by
  simp [arrow, SingleObj.id_as_one]

theorem arrow_injective : Function.Injective (arrow M) := by
  intro m n e
  obtain ⟨_, h⟩ := Sigma.mk.inj_iff.mp e
  exact (Prod.mk.inj (eq_of_heq h)).2

/-- **The Fregean Axiom fails** in the full model on any monoid with an element other
than `1`: the propositions `⊤` and `{1}` agree at the identity but differ. -/
theorem not_fregean (m : M) (hm : m ≠ 1) : ¬ (model M).HoldsSentence Sentence.fregean :=
  (model M).not_fregean_of_propFull (model_isModel M) (model_full M).propFull
    (m : SingleObj.star M ⟶ SingleObj.star M) fun e => hm (arrow_injective M (e.trans (arrow_id M)))

/-- The action of an arrow on a proposition: `⟨(), m⟩` is in `k^t X` iff `⟨(), k ≫ m⟩` is
in `X`. -/
theorem mem_map_t (k : SingleObj.star M ⟶ SingleObj.star M) (X : Prop' M)
    (p : Tuple (FullT (unitAction M)) .t (SingleObj.star M)) :
    p ∈ (FullT (unitAction M) (.rel .t)).map k X ↔
      (⟨p.1, p.2.1, k ≫ p.2.2⟩ : Tuple (FullT (unitAction M)) .t (SingleObj.star M)) ∈ X :=
  Iff.rfl

end MSet

/-! ### The idempotent monoid `{1, k}`, `k·k = k` -/

/-- The two-element monoid with `k·k = k`. -/
inductive Idem | one | k
  deriving DecidableEq

namespace Idem

instance : One Idem := ⟨.one⟩
instance : Mul Idem := ⟨fun a b => match a, b with
  | .one, x => x
  | x, .one => x
  | .k, .k => .k⟩

instance : Monoid Idem where
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl

theorem mul_k (m : Idem) : m * k = k := by cases m <;> rfl

theorem k_ne_one : (k : Idem) ≠ 1 := by decide

/-- `k^t` identifies `∅` and `{1}`, so `ND_t` fails (Classicism, §"Exploring action
models"): the map's `full-idempotent-monoid` violates `distinctness-necessary-t`. -/
theorem not_nd_t : ¬ (MSet.model Idem).HoldsSentence (Sentence.nd (.rel .t)) := by
  intro H
  rw [Premodel.HoldsSentence, (MSet.model Idem).holds_nd_iff (MSet.model_isModel Idem)] at H
  have hk : Function.Injective ((FullT (MSet.unitAction Idem) (.rel .t)).map
      (X := SingleObj.star Idem) (Y := SingleObj.star Idem) k) :=
    @H (SingleObj.star Idem) k
  have e : (FullT (MSet.unitAction Idem) (.rel .t)).map (X := SingleObj.star Idem) (Y := SingleObj.star Idem) k
        (∅ : MSet.Prop' Idem)
      = (FullT (MSet.unitAction Idem) (.rel .t)).map (X := SingleObj.star Idem) (Y := SingleObj.star Idem) k
        ({MSet.arrow Idem 1} : MSet.Prop' Idem) := by
    apply Set.ext
    rintro ⟨V, ⟨⟩, m⟩
    rw [MSet.mem_map_t, MSet.mem_map_t, Set.mem_singleton_iff]
    constructor
    · exact False.elim
    · intro h
      obtain ⟨_, hh⟩ := Sigma.mk.inj_iff.mp h
      have := (Prod.mk.inj (eq_of_heq hh)).2
      rw [SingleObj.comp_as_mul, mul_k] at this
      exact k_ne_one this
  have := hk e
  exact Set.notMem_empty _ (this ▸ Set.mem_singleton (MSet.arrow Idem 1))

/-- The Fregean Axiom fails: `fregean-axiom` is violated. -/
theorem not_fregean : ¬ (MSet.model Idem).HoldsSentence Sentence.fregean :=
  MSet.not_fregean Idem k k_ne_one

/-- `k^t` is not surjective, `{1}` being `k^t` of nothing, so by the paper's (iii) `BF_t`
fails: the record violates `barcan-t`. -/
theorem not_bf_t : ¬ (MSet.model Idem).HoldsSentence (Sentence.bf (.rel .t)) := by
  intro H
  have hs := @Premodel.full_bf_surjective _ _ (MSet.unitAction Idem) _ _ _ _ (.rel .t) H
    (SingleObj.star Idem) (k : SingleObj.star Idem ⟶ SingleObj.star Idem)
  obtain ⟨X, hX⟩ := hs ({MSet.arrow Idem 1} : MSet.Prop' Idem)
  have h1 : (⟨SingleObj.star Idem, PUnit.unit, (k : SingleObj.star Idem ⟶ SingleObj.star Idem) ≫
      (MSet.arrow Idem 1).2.2⟩ : Tuple (FullT (MSet.unitAction Idem)) .t (SingleObj.star Idem)) ∈ X := by
    have h := Set.mem_singleton (MSet.arrow Idem 1)
    rw [← hX] at h
    exact h
  have hk : MSet.arrow Idem k ∈ ({MSet.arrow Idem 1} : MSet.Prop' Idem) := by
    rw [← hX]
    exact h1
  exact k_ne_one (MSet.arrow_injective Idem (Set.mem_singleton_iff.mp hk))

end Idem

/-! ### The two-element group `{1, k}`, `k·k = 1` -/

/-- The two-element group. -/
inductive Invol | one | k
  deriving DecidableEq

namespace Invol

instance : One Invol := ⟨.one⟩
instance : Mul Invol := ⟨fun a b => match a, b with
  | .one, x => x
  | x, .one => x
  | .k, .k => .one⟩
instance : Inv Invol := ⟨id⟩

instance : Group Invol where
  mul_assoc a b c := by cases a <;> cases b <;> cases c <;> rfl
  one_mul a := by cases a <;> rfl
  mul_one a := by cases a <;> rfl
  inv_mul_cancel a := by cases a <;> rfl

theorem k_ne_one : (k : Invol) ≠ 1 := by decide

/-- `□ND_σ` holds at every type: every arrow is an isomorphism. The map's
`full-involution-group` satisfies `necessary-distinctness-necessary-r`. -/
theorem box_nd (σ : Ty) : (MSet.model Invol).HoldsSentence (Term.box (Sentence.nd σ)) :=
  (MSet.model Invol).holds_box_nd_of_groupoid (MSet.model_isModel Invol) σ

/-- `□BF_σ` likewise. -/
theorem box_bf (σ : Ty) : (MSet.model Invol).HoldsSentence (Term.box (Sentence.bf σ)) :=
  (MSet.model Invol).holds_box_bf_of_groupoid (MSet.model_isModel Invol) σ

/-- The Fregean Axiom fails: four propositions. -/
theorem not_fregean : ¬ (MSet.model Invol).HoldsSentence Sentence.fregean :=
  MSet.not_fregean Invol k k_ne_one

end Invol

end Classicism.Meta.Intensional
