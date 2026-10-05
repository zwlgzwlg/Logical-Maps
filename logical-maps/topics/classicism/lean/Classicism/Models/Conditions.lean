import Classicism.Models.MonoidModel
import Classicism.Semantics.IntensionalTheory
import Classicism.Semantics.FullModels
import Classicism.Semantics.Counting
import Classicism.Semantics.Arrows
import Classicism.Semantics.Numerals
import Mathlib.Algebra.Group.Action.Faithful
import Mathlib.Algebra.Group.Submonoid.MulAction
import Mathlib.Algebra.Group.Action.End

/-!
# The map's conditions on models, as predicates

A general argument on the map (`arguments/<id>.yaml`, or a group's shared argument) says that
every model meeting some conditions has a verdict: a principle holds in it, or fails. Its Lean
form quantifies over models and assumes the conditions; these are the conditions. Each is
the Lean reading of the condition's prose, named in the condition's `lean` field.

- **Conditions of the topic** (`conditions.yaml`) are predicates on intensional premodels.
- **Conditions of a group** are predicates on what the group's construction is built from:
  for the finite-support models on one object (`finite-support-one-object`), the monoid
  acting on `ℕ`, whose ideally full model is `MonoidModel.model M`.

A model meets a condition by a proof of the predicate for its Lean model, named in its
record's `lean.meets` (or its group's, for every member).
-/

namespace Classicism.Meta.Intensional

open CategoryTheory

namespace Premodel

variable {Sig : Signature} {C : Type} [SmallCategory C]

/-- `one-object-action-model`: the model has a single object. -/
abbrev OneObject (_A : Premodel Sig C) : Prop := Subsingleton C

theorem oneObject_of_subsingleton (A : Premodel Sig C) [Subsingleton C] : A.OneObject :=
  inferInstance

/-- `metatheory-choice`: the model is constructed in a metatheory with the axiom of choice.
Lean's is one, so every model meets it. -/
def MetatheoryChoice (_A : Premodel Sig C) : Prop := True

theorem metatheoryChoice (A : Premodel Sig C) : A.MetatheoryChoice := trivial

/-- `one-individual`: there is exactly one individual at every world. (There is at least one:
the domains at `e` are nonempty.) -/
def OneIndividual (A : Premodel Sig C) : Prop := ∀ W : C, Subsingleton (A.Dom W .e)

/-- `finitely-many-propositions`: there are finitely many propositions at the evaluation
world. -/
def FinitelyManyPropositions (A : Premodel Sig C) : Prop := Finite (A.Dom A.W₀ (.rel .t))

/-- `finitely-many-propositions-everywhere`: there are finitely many propositions at every object
reachable from the evaluation point. -/
def FinitelyManyPropositionsEverywhere (A : Premodel Sig C) : Prop :=
  ∀ {V : C} (_ : A.W₀ ⟶ V), Finite (A.Dom V (.rel .t))

/-- `infinitely-many-individuals`: there are infinitely many individuals at the evaluation world. -/
def InfinitelyManyIndividuals (A : Premodel Sig C) : Prop := Infinite (A.Dom A.W₀ .e)

/-- `infinitely-many-propositions`: there are infinitely many propositions at the evaluation
world. -/
def InfinitelyManyPropositions (A : Premodel Sig C) : Prop := Infinite (A.Dom A.W₀ (.rel .t))

/-! `full-model` and `full-action-model` are `Premodel.Full` (`IntensionalProperties.lean`): in
the intensional form a full action model is a full model, every intension present at every
object. `extensionally-full` is `Premodel.ExtFull` and `actual-world-isolated` is
`Premodel.ActualWorldIsolated` (`FullModels.lean`). -/

/-- `d6-surjective`: the model is ideally full, and every arrow out of the evaluation object
acts surjectively on the individuals (so on the finite sets of them, the pinning sets):
Proposition D.6's hypothesis. -/
def D6Surjective (A : Premodel Sig C) : Prop :=
  ∃ (W₀ : C) (De : C ⥤ Type) (ne : ∀ W : C, Nonempty (De.obj W))
    (I : ∀ c : Sig.Const, (IdealT De (Sig.typeOf c)).obj W₀),
    A = Premodel.ideal De W₀ ne I ∧ ∀ {V : C} (k : W₀ ⟶ V), Function.Surjective (De.map k)

/-- The pure reduct of an ideally full model is the ideally full model of the pure language. -/
theorem reduct_ideal (De : C ⥤ Type) (W₀ : C) (ne : ∀ W : C, Nonempty (De.obj W))
    (I : ∀ c : Sig.Const, (IdealT De (Sig.typeOf c)).obj W₀) :
    (Premodel.ideal De W₀ ne I).reduct =
      Premodel.ideal (Sig := Signature.pure) De W₀ ne (fun c => nomatch c) := by
  unfold reduct Premodel.ideal
  congr

end Premodel

namespace MonoidModel

/-- A monoid's one-object category has one object. -/
instance instSubsingletonSingleObj {M : Type} [Monoid M] : Subsingleton (SingleObj M) :=
  inferInstanceAs (Subsingleton Unit)

/-- A monoid of functions on `ℕ` acts on `ℕ` faithfully: Appendix D's monoids. -/
instance instFaithfulSMulSubmonoid (S : Submonoid (Function.End ℕ)) : FaithfulSMul S ℕ :=
  ⟨fun h => Subtype.ext (funext h)⟩

variable (M : Type) [Monoid M] [MulAction M ℕ]

/-- `actual-world-pinned`: the singleton of the identity arrow is pinned down by a finite set. -/
def ActualWorldPinned : Prop := FinPinned' ({tup (1 : M)} : Prop' M)

/-- `collapse-unpinned`: the arrows other than the identity form a nonempty proposition pinned
down by a finite set, and none of them has a singleton pinned down by a finite set. -/
def CollapseUnpinned : Prop :=
  FinPinned' (ofPred fun g : M => g ≠ 1) ∧ (∃ g : M, g ≠ 1) ∧
    ∀ g : M, g ≠ 1 → ¬ FinPinned' ({tup g} : Prop' M)

/-- `positive-preserving`: every arrow is monotone, and some arrow sends `0` to a positive
number. -/
def PositivePreserving : Prop :=
  (∀ g : M, Monotone fun n : ℕ => g • n) ∧ ∃ g : M, 0 < g • 0

/-! ### Meeting the conditions -/

theorem oneObject : (model M).OneObject := inferInstance

theorem actualWorldPinned_of_onePinned (h : OnePinned M) : ActualWorldPinned M := by
  obtain ⟨N, hN, h⟩ := h
  exact ⟨N, hN, singleton_pinned_of N 1 fun g hg => h g fun x hx => by rw [hg x hx, one_smul]⟩

theorem d6Surjective_of_surjective (hs : ∀ k : M, Function.Surjective fun n : ℕ => k • n) :
    (model M).D6Surjective :=
  ⟨_, _, _, _, rfl, fun k => hs (arrow k)⟩

/-- A free arrow has no singleton pinned down by a finite set. -/
theorem not_finPinned_of_free {k : M} (hk : Free k) : ¬ FinPinned' ({tup k} : Prop' M) := by
  rintro ⟨N, hN, hp⟩
  obtain ⟨k', hagree, n, hn⟩ := hk N hN
  have : tup k' ∈ ({tup k} : Prop' M) :=
    (mem_iff_of_pinned hp fun x hx => hagree x hx).2 rfl
  exact hn (by rw [tup_injective this])

/-- Conversely, when the monoid acts faithfully, an arrow without a finitely pinned singleton
is free. -/
theorem free_of_not_finPinned [FaithfulSMul M ℕ] {k : M} (hk : ¬ FinPinned' ({tup k} : Prop' M)) :
    Free k := by
  intro X hX
  by_contra hf
  push Not at hf
  exact hk ⟨X, hX, singleton_pinned_of X k fun g hg =>
    FaithfulSMul.eq_of_smul_eq_smul (hf g hg)⟩

/-- The arrows other than the identity are a nonempty proposition with no atom below it: each
of them is free, having no finitely pinned singleton (`not_atomicityT_of_free`). -/
theorem not_atomicityT_of_collapseUnpinned [FaithfulSMul M ℕ] (h : CollapseUnpinned M) :
    ¬ (model M).HoldsSentence P.AtomicityT.quoted := by
  obtain ⟨hp, ⟨g, hg⟩, hun⟩ := h
  exact not_atomicityT_of_free M hp (fun e => Set.notMem_empty (tup g) (e ▸ mem_ofPred.2 hg))
    fun k hk => free_of_not_finPinned M (hun k (mem_ofPred.1 hk))

end MonoidModel

end Classicism.Meta.Intensional
