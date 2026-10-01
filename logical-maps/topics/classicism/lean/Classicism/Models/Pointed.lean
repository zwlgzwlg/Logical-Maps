import Classicism.Models.Functions
import Classicism.Models.MonoidModel
import Mathlib.Algebra.Group.Submonoid.MulAction
import Mathlib.Algebra.Group.Action.End
import Classicism.Semantics.IntensionalProperties

/-!
# A monoid model with a point adjoined

Classicism, Appendix D, after Part 8: "for any of the above models, we can adjoin a second
object `W₁ = {0}`, with a single arrow from `W₀` to `W₁` (namely, the function from `ℕ`
to `{0}`) and no arrows from `W₁` to `W₀`. Then all the same principles (from among ND,
BF, Atomicity, Actuality, and Boolean Completeness) hold as in the original model, but we
also have `◇(□ND ∧ Atomicity)`."

This module is that construction for any monoid `S` of functions on `ℕ`: the category on
`Two` whose arrows `ℕ → ℕ` are the members of `S`, with the one arrow `c : ℕ → {0}`, the
identity of the point, and nothing back; the ideally full model on it, based at `ℕ`. The
verdicts, each from the fact about `S` that decides it in the one-object model:

- **At the point, everything holds** that holds in a one-world model on one individual:
  `□ND_σ`, `BF_σ`, Actuality, Atomicity at `t`, Boolean Completeness. The point's only
  arrow is its identity.
- **At `ℕ`, as in the one-object model**: Actuality holds when `{1}` is finitely pinned in
  `S` and fails when `1` is free; Atomicity at `t` holds when every nonempty finitely
  pinned set of members of `S` contains one whose singleton is finitely pinned, and fails
  when some such set consists of free members; `BF_σ` holds when every member of `S` is
  surjective, and fails at `e` on the one-object model's property, extended to hold of
  everything along `c`; Boolean Completeness at `e → t` fails on the same condition as
  there.
- **At `ℕ`, unlike the one-object model**: `ND_e` fails, since `c` identifies everything;
  and Atomlessness fails, since `{c}` is a possible proposition with nothing possible
  strictly below it. These are the corrections the survey in `Models/README.md` made to
  the paper's "all the same principles".

A pure sentence's truth at an object does not depend on the arrow it is reached by
(`sem_pure`), so `□P` holds at `ℕ` iff `P` holds at `ℕ` and at the point, and `◇P` iff at
one of them (`holds_box_iff`, `holds_dia_iff`): each principle is necessary, contingently
true, contingently false, or impossible according to its two verdicts.
-/

namespace Classicism.Meta.Intensional.Pointed

open CategoryTheory Premodel FunCat

noncomputable section

/-- Functions on `ℕ` under composition. -/
abbrev F : Type := Function.End ℕ

variable (S : Submonoid F)

/-- The arrows: the members of `S` on `ℕ`, anything from `ℕ` to the point (there is one
function), the identity of the point, and nothing from the point to `ℕ`. -/
def Arr : (i j : Two) → (Two.X i → Two.X j) → Prop
  | .nat, .nat, f => (f : F) ∈ S
  | .nat, .pt, _ => True
  | .pt, .pt, _ => True
  | .pt, .nat, _ => False

/-- The category. -/
abbrev cat : FunCat where
  Obj := Two
  X := Two.X
  Arr {i j} f := Arr S i j f
  arr_id i := by
    cases i
    · exact S.one_mem
    · trivial
  arr_comp {i j k} f g hf hg := by
    cases i <;> cases j <;> cases k
    · exact S.mul_mem hg hf
    all_goals trivial

theorem ne : ∀ i : (cat S).Ob, Nonempty ((cat S).X i)
  | .nat => ⟨(0 : ℕ)⟩
  | .pt => ⟨()⟩

/-- The model, based at `ℕ`. -/
noncomputable abbrev model : Premodel Signature.pure (cat S).Ob := (cat S).model Two.nat (ne S)

theorem model_isModel : (model S).IsModel := (cat S).model_isModel Two.nat (ne S)

/-- `ℕ`, the base, named as the model's base so that the two agree syntactically. -/
abbrev W₀ : (cat S).Ob := (model S).W₀

/-- The point. -/
abbrev W₁ : (cat S).Ob := Two.pt

/-! ### The arrows -/

variable {S}

/-- An arrow `ℕ → ℕ`, as a member of `S`. -/
def toS (k : W₀ S ⟶ W₀ S) : S := ⟨fn k, k.2⟩

/-- A member of `S`, as an arrow. -/
abbrev ofS (g : S) : W₀ S ⟶ W₀ S := arr (i := W₀ S) (j := W₀ S) (g : F) g.2

theorem ofS_toS (k : W₀ S ⟶ W₀ S) : ofS (toS k) = k := rfl

theorem toS_ofS (g : S) : toS (ofS g) = g := rfl

theorem toS_comp (k l : W₀ S ⟶ W₀ S) : toS (k ≫ l) = toS l * toS k := rfl

theorem smul_eq (g : S) (x : ℕ) : g • x = (g : F) x := rfl

theorem fn_ofS (g : S) (x : ℕ) : fn (ofS g) x = g • x := rfl

variable (S) in
/-- The arrow to the point. -/
abbrev c : W₀ S ⟶ W₁ S := arr (i := W₀ S) (j := W₁ S) (fun _ => ()) trivial

theorem ob_cases (V : (cat S).Ob) : V = W₀ S ∨ V = W₁ S := by
  cases V
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem W₀_ne_W₁ : W₀ S ≠ W₁ S := fun h => Two.noConfusion h

theorem eq_c (k : W₀ S ⟶ W₁ S) : k = c S := hom_ext (funext fun _ => rfl)

theorem eq_id_pt (k : W₁ S ⟶ W₁ S) : k = 𝟙 (W₁ S) := hom_ext (funext fun _ => rfl)

theorem no_back (k : W₁ S ⟶ W₀ S) : False := k.2

/-! ### Propositions at `ℕ`: sets of members of `S`, and possibly `c` -/

variable (S) in
/-- The propositions at `ℕ`, as intensions. -/
abbrev Prop' : Type := Intension (model S).inner .t (W₀ S)

/-- The tuple of a member of `S`. -/
abbrev tupN (g : S) : Tuple (model S).inner .t (W₀ S) := ⟨W₀ S, PUnit.unit, ofS g⟩

variable (S) in
/-- The tuple of `c`. -/
abbrev tupC : Tuple (model S).inner .t (W₀ S) := ⟨W₁ S, PUnit.unit, c S⟩

theorem tup_id : (⟨W₀ S, PUnit.unit, 𝟙 (W₀ S)⟩ : Tuple (model S).inner .t (W₀ S)) = tupN 1 := rfl

theorem tupN_injective : Function.Injective (tupN (S := S)) := by
  intro g g' e
  obtain ⟨_, h⟩ := Sigma.mk.inj_iff.mp e
  have := congrArg toS (Prod.mk.inj (eq_of_heq h)).2
  exact this

/-- Every tuple of a proposition at `ℕ` is `tupN g` or `tupC`. -/
theorem tuple_cases (t : Tuple (model S).inner .t (W₀ S)) : (∃ g, t = tupN g) ∨ t = tupC S := by
  obtain ⟨V, ⟨⟩, k⟩ := t
  obtain rfl | rfl := ob_cases V
  · exact Or.inl ⟨toS k, rfl⟩
  · right
    rw [eq_c k]

/-- **Pinning, characterized**: a proposition at `ℕ` is pinned down by `N` iff membership
of members of `S` in it depends only on their values on `N`. The point cannot tell arrows
apart: there is one arrow to it. -/
theorem pinnedO_iff (N : Set ℕ) (p : Prop' S) :
    (model S).PinnedO (W := W₀ S) (.rel .t) N p ↔
      ∀ g g' : S, (∀ x ∈ N, g • x = g' • x) → (tupN g ∈ p ↔ tupN g' ∈ p) := by
  constructor
  · intro hp g g' ha
    have e := hp (W₀ S) (ofS g) (ofS g') (fun x hx => ha x hx)
    simp only [Outer.map_rel] at e
    have := congrArg (fun P : Intension (model S).inner .t (W₀ S) =>
      (⟨W₀ S, PUnit.unit, 𝟙 (W₀ S)⟩ : Tuple (model S).inner .t (W₀ S)) ∈ P) e
    simpa [Intension.mem_map, Category.comp_id] using this
  · intro H V h i ha
    obtain rfl | rfl := ob_cases V
    · show Intension.map (model S).inner h p = Intension.map (model S).inner i p
      ext ⟨U, ⟨⟩, l⟩
      simp only [Intension.mem_map]
      obtain rfl | rfl := ob_cases U
      · exact H (toS l * toS h) (toS l * toS i) fun x hx => by
          have hx' : fn h x = fn i x := ha x hx
          show fn l (fn h x) = fn l (fn i x)
          rw [hx']
      · rw [eq_c (h ≫ l), eq_c (i ≫ l)]
    · rw [eq_c h, eq_c i]

/-- Pinning, for a proposition: members of `S` agreeing on `N` are in it together. -/
theorem mem_iff_of_pinned {N : Set ℕ} {p : Prop' S} (hp : (model S).PinnedO (W := W₀ S) (.rel .t) N p) {g g' : S}
    (ha : ∀ x ∈ N, g • x = g' • x) : tupN g ∈ p ↔ tupN g' ∈ p :=
  (pinnedO_iff N p).1 hp g g' ha

/-- Finitely pinned propositions: the inner ones. -/
def FinPinned' (p : Prop' S) : Prop := ∃ N : Set ℕ, N.Finite ∧ (model S).PinnedO (W := W₀ S) (.rel .t) N p

theorem finPinned'_Incl (p : (model S).Dom (W₀ S) (.rel .t)) : FinPinned' ((model S).Incl _ (W₀ S) p) :=
  Premodel.ideal_inner_finPinned (cat S).De (.rel .t) (W₀ S) p

/-- An inner proposition, from a finitely pinned one. -/
theorem exists_inner {q : Prop' S} (hq : FinPinned' q) :
    ∃ q' : (model S).Dom (W₀ S) (.rel .t), (model S).Incl _ (W₀ S) q' = q :=
  Premodel.ideal_pinned_inner (cat S).De .t (W₀ S) q hq

/-- A proposition given by a predicate on members of `S` and a verdict for `c`. -/
abbrev ofPred (P : S → Prop) (b : Prop) : Prop' S :=
  {t | (∃ g, t = tupN g ∧ P g) ∨ (t = tupC S ∧ b)}

theorem mem_ofPred_N {P : S → Prop} {b : Prop} {g : S} : tupN g ∈ ofPred P b ↔ P g := by
  constructor
  · rintro (⟨g', e, h⟩ | ⟨e, _⟩)
    · rw [tupN_injective e]; exact h
    · exact absurd (congrArg Sigma.fst e) W₀_ne_W₁
  · intro h; exact Or.inl ⟨g, rfl, h⟩

theorem mem_ofPred_C {P : S → Prop} {b : Prop} : tupC S ∈ ofPred P b ↔ b := by
  constructor
  · rintro (⟨g', e, _⟩ | ⟨_, h⟩)
    · exact absurd (congrArg Sigma.fst e).symm W₀_ne_W₁
    · exact h
  · intro h; exact Or.inr ⟨rfl, h⟩

/-- Such a proposition is pinned down by `N` when the predicate depends only on the values
on `N`. -/
theorem ofPred_pinned (P : S → Prop) (b : Prop) (N : Set ℕ)
    (h : ∀ g g' : S, (∀ x ∈ N, g • x = g' • x) → (P g ↔ P g')) :
    (model S).PinnedO (W := W₀ S) (.rel .t) N (ofPred P b) :=
  (pinnedO_iff N _).2 fun g g' ha => by rw [mem_ofPred_N, mem_ofPred_N]; exact h g g' ha

/-- Two propositions with the same members of `S` and the same verdict on `c` are equal. -/
theorem prop_ext {p q : Prop' S} (hN : ∀ g, tupN g ∈ p ↔ tupN g ∈ q) (hC : tupC S ∈ p ↔ tupC S ∈ q) :
    p = q := by
  ext t
  rcases tuple_cases t with ⟨g, rfl⟩ | rfl
  · exact hN g
  · exact hC

/-! ### Holding, at `ℕ` and at the point -/

variable (S)

local notation "A" => model S
local notation "Mo" => model_isModel S

/-- A variable holds at the identity of `ℕ` iff `1` is in its value. -/
theorem holds_var_id {Γ : Ctx} (v : Var Γ (.rel .t)) (g : IEnv ((A).Dom (W₀ S)) Γ) :
    (A).Holds (𝟙 (W₀ S)) (Term.var v) g ↔ tupN 1 ∈ (A).Incl _ (W₀ S) (g.get v) :=
  Premodel.holds_var _ _ _ _

/-- A variable holds after moving along `k` iff `k` is in its value. -/
theorem holds_var_push {Γ : Ctx} (v : Var Γ (.rel .t)) (g : IEnv ((A).Dom (W₀ S)) Γ)
    {V : (cat S).Ob} (k : W₀ S ⟶ V) :
    (A).Holds (𝟙 (W₀ S) ≫ k) (Term.var v) ((A).push k g) ↔
      (⟨V, PUnit.unit, k⟩ : Tuple (A).inner .t (W₀ S)) ∈ (A).Incl _ (W₀ S) (g.get v) := by
  rw [Premodel.holds_var]
  simp only [push, IEnv.get_map]
  rw [(A).incl_map, Intension.mem_map, Category.comp_id]
  exact Iff.rfl

/-- **`□P`, for pure `P`, holds at `ℕ` iff `P` holds at `ℕ` and at the point**: a pure
sentence does not see the arrow it is reached by. -/
theorem holds_box_iff {p : Sentence Signature.pure} (hp : p.pure = true) :
    (A).HoldsSentence (Term.box p) ↔ (A).HoldsSentence p ∧ (A).Holds (c S) p .nil := by
  rw [HoldsSentence, (A).holds_box Mo]
  constructor
  · intro H
    refine ⟨?_, ?_⟩
    · have := ((A).holds_id_comp _ _ _).1 (H (𝟙 _))
      rwa [IEnv.nil_eq ((A).push _ IEnv.nil)] at this
    · have := ((A).holds_id_comp _ _ _).1 (H (c S))
      rwa [IEnv.nil_eq ((A).push _ IEnv.nil)] at this
  · rintro ⟨h0, h1⟩ V k
    rw [IEnv.nil_eq ((A).push k IEnv.nil)]
    obtain rfl | rfl := ob_cases V
    · unfold Holds
      rw [(A).sem_pure p hp (𝟙 _ ≫ k) (𝟙 _)]
      exact h0
    · obtain rfl : k = c S := eq_c k
      exact ((A).holds_id_comp _ _ _).2 h1

/-- **`◇P`, for pure `P`, holds at `ℕ` iff `P` holds at `ℕ` or at the point.** -/
theorem holds_dia_iff {p : Sentence Signature.pure} (hp : p.pure = true) :
    (A).HoldsSentence (Term.dia p) ↔ (A).HoldsSentence p ∨ (A).Holds (c S) p .nil := by
  rw [HoldsSentence, (A).holds_dia Mo]
  constructor
  · rintro ⟨V, k, H⟩
    rw [IEnv.nil_eq ((A).push k IEnv.nil)] at H
    obtain rfl | rfl := ob_cases V
    · left
      unfold Holds at H
      rw [(A).sem_pure p hp (𝟙 _ ≫ k) (𝟙 _)] at H
      exact H
    · right
      obtain rfl : k = c S := eq_c k
      exact ((A).holds_id_comp _ _ _).1 H
  · rintro (h0 | h1)
    · refine ⟨W₀ S, 𝟙 _, ?_⟩
      rw [IEnv.nil_eq ((A).push _ IEnv.nil)]
      exact ((A).holds_id_comp _ _ _).2 h0
    · refine ⟨W₁ S, c S, ?_⟩
      rw [IEnv.nil_eq ((A).push _ IEnv.nil)]
      exact ((A).holds_id_comp _ _ _).2 h1

/-! ### At the point: a one-world model on one individual -/

/-- The one tuple of a proposition at the point: its identity. -/
theorem tuple_pt (t : Tuple (A).inner .t (W₁ S)) : t = ⟨W₁ S, PUnit.unit, 𝟙 (W₁ S)⟩ := by
  obtain ⟨V, ⟨⟩, k⟩ := t
  obtain rfl | rfl := ob_cases V
  · exact (no_back k).elim
  · rw [eq_id_pt k]

/-- A proposition at the point is `∅` or everything. -/
theorem prop_pt (p : Intension (A).inner .t (W₁ S)) : p = ∅ ∨ p = Set.univ := by
  by_cases h : (⟨W₁ S, PUnit.unit, 𝟙 (W₁ S)⟩ : Tuple (A).inner .t (W₁ S)) ∈ p
  · right; exact Set.eq_univ_of_forall fun t => (tuple_pt S t) ▸ h
  · left; exact Set.eq_empty_of_forall_notMem fun t ht => h ((tuple_pt S t) ▸ ht)

/-- Everything at the point is pinned down by `∅`: parallel arrows out of it are equal. -/
theorem pinned_pt (ρ : RTy) (F : Intension (A).inner ρ (W₁ S)) :
    (A).PinnedO (W := W₁ S) (.rel ρ) ∅ F := fun V h i _ => by
  obtain rfl | rfl := ob_cases V
  · exact (no_back h).elim
  · rw [eq_id_pt h, eq_id_pt i]

/-- So every intension at the point is inner: the point is full. -/
theorem inner_pt (ρ : RTy) (F : Intension (A).inner ρ (W₁ S)) :
    ∃ x : (A).Dom (W₁ S) (.rel ρ), (A).incl ρ (W₁ S) x = F :=
  Premodel.ideal_pinned_inner (cat S).De ρ (W₁ S) F ⟨∅, Set.finite_empty, pinned_pt S ρ F⟩

/-- **`ND_σ` holds at the point.** -/
theorem nd_pt (h : (A).W₀ ⟶ W₁ S) (σ : Ty) : (A).Holds h (Sentence.nd σ) .nil := by
  rw [(A).holds_nd_iff Mo]
  intro V k
  obtain rfl | rfl := ob_cases V
  · exact (no_back k).elim
  · rw [eq_id_pt k, CategoryTheory.Functor.map_id]
    exact Function.injective_id

/-- **`□ND_σ` holds at the point.** -/
theorem box_nd_pt (h : (A).W₀ ⟶ W₁ S) (σ : Ty) : (A).Holds h (Term.box (Sentence.nd σ)) .nil := by
  rw [(A).holds_box Mo]
  intro V k
  obtain rfl | rfl := ob_cases V
  · exact (no_back k).elim
  · rw [IEnv.nil_eq ((A).push k IEnv.nil)]
    exact nd_pt S _ σ

/-- **`BF_σ` holds at the point.** -/
theorem bf_pt (h : (A).W₀ ⟶ W₁ S) (σ : Ty) : (A).Holds h (Sentence.bf σ) .nil := by
  apply (A).holds_bf_of_surjective Mo σ h
  intro V k
  obtain rfl | rfl := ob_cases V
  · exact (no_back k).elim
  · rw [eq_id_pt k, CategoryTheory.Functor.map_id]
    exact Function.surjective_id

/-- **Actuality holds at the point**: `⊤` is the strongest truth. -/
theorem actuality_pt (h : (A).W₀ ⟶ W₁ S) : (A).Holds h P.Actuality.quoted .nil := by
  unfold P.Actuality.quoted
  rw [(A).holds_exists Mo]
  obtain ⟨p, hp⟩ := inner_pt S .t Set.univ
  refine ⟨p, ?_⟩
  rw [(A).holds_conj Mo, (A).holds_forall Mo]
  refine ⟨?_, fun q => ?_⟩
  · rw [Premodel.holds_var]
    show _ ∈ (A).incl .t (W₁ S) p
    rw [hp]; trivial
  · rw [(A).holds_imp Mo, (A).holds_eq Mo, (A).sem_disj Mo]
    intro hq
    show (A).incl .t (W₁ S) q = (A).incl .t (W₁ S) p ∪ (A).incl .t (W₁ S) q
    rw [hp, Set.univ_union]
    exact Set.eq_univ_of_forall fun t => (tuple_pt S t) ▸ hq

/-- **Atomicity at `t` holds at the point**: `⊤` is an atom. -/
theorem atomicityT_pt (h : (A).W₀ ⟶ W₁ S) : (A).Holds h P.AtomicityT.quoted .nil := by
  unfold P.AtomicityT.quoted
  rw [(A).holds_forall Mo]
  intro x
  rw [(A).holds_disj Mo, (A).holds_eq Mo, (A).sem_neg Mo, (A).sem_disj Mo, (A).sem_neg Mo,
    (A).holds_exists Mo]
  rcases prop_pt S ((A).incl .t (W₁ S) x) with hx | hx
  · left
    show ((A).incl .t (W₁ S) x)ᶜ = (A).incl .t (W₁ S) x ∪ ((A).incl .t (W₁ S) x)ᶜ
    rw [hx, Set.compl_empty, Set.empty_union]
  · right
    refine ⟨x, ?_⟩
    rw [(A).holds_conj Mo, (A).holds_eq Mo, (A).sem_disj Mo, (A).holds_forall Mo]
    refine ⟨fun z => ?_, ?_⟩
    · rw [(A).holds_iff Mo, (A).holds_conj Mo, (A).holds_eq Mo, (A).sem_disj Mo, (A).holds_neg Mo,
        (A).holds_eq Mo, (A).holds_eq Mo, (A).sem_neg Mo, (A).sem_disj Mo, (A).sem_neg Mo]
      show ((A).incl .t (W₁ S) x = (A).incl .t (W₁ S) z ∪ (A).incl .t (W₁ S) x ∧
          ¬ (A).incl .t (W₁ S) z = (A).incl .t (W₁ S) x) ↔
        ((A).incl .t (W₁ S) z)ᶜ = (A).incl .t (W₁ S) z ∪ ((A).incl .t (W₁ S) z)ᶜ
      rw [hx, Set.union_univ]
      have hne : (∅ : Intension (A).inner .t (W₁ S)) ≠ Set.univ := fun e =>
        Set.notMem_empty (⟨W₁ S, PUnit.unit, 𝟙 (W₁ S)⟩ : Tuple (A).inner .t (W₁ S)) (e ▸ Set.mem_univ _)
      rcases prop_pt S ((A).incl .t (W₁ S) z) with hz | hz <;> rw [hz]
      · exact ⟨fun _ => by rw [Set.compl_empty, Set.empty_union],
          fun _ => ⟨rfl, hne⟩⟩
      · refine ⟨fun h => absurd rfl h.2, fun e => ?_⟩
        rw [Set.compl_univ, Set.union_empty] at e
        exact absurd e hne
    · show (A).incl .t (W₁ S) x = (A).incl .t (W₁ S) x ∪ (A).incl .t (W₁ S) x
      rw [Set.union_self]

/-- **Boolean Completeness holds at the point, at every type**: the greatest lower bound
is the intersection, which is inner since everything at the point is. -/
theorem bc_pt (h : (A).W₀ ⟶ W₁ S) (ρ : RTy) : (A).Holds h (P.BooleanCompleteness.quoted ρ) .nil := by
  rw [MonoidModel.bc_quoted_eq, (A).holds_bc_iff Mo]
  intro X
  obtain ⟨y, hy⟩ := inner_pt S ρ {t | ∀ u : (A).Dom (W₁ S) (.rel ρ),
    (⟨W₁ S, (u, PUnit.unit), 𝟙 (W₁ S)⟩ : Tuple (A).inner (ρ ⇒ RTy.t) (W₁ S)) ∈ (A).incl _ (W₁ S) X →
      t ∈ (A).incl ρ (W₁ S) u}
  refine ⟨y, fun z => ?_⟩
  rw [hy]
  exact ⟨fun H t ht u hu => H u hu ht, fun H u hu t ht => H ht u hu⟩

/-! ### At `ℕ`: what the point changes -/

/-- **`ND_e` fails at `ℕ`**: `c` sends `0` and `1` to the point. -/
theorem not_nd_e : ¬ (A).HoldsSentence (Sentence.nd .e) := by
  intro H
  rw [HoldsSentence, (A).holds_nd_iff Mo] at H
  have := @H (W₁ S) (c S) (0 : ℕ) (1 : ℕ) rfl
  exact Nat.zero_ne_one this

/-- **Atomlessness fails at `ℕ`**: `{c}` is possible, and only `∅` is strictly below it. -/
theorem not_atomlessness : ¬ (A).HoldsSentence P.Atomlessness.quoted := by
  intro H
  rw [HoldsSentence] at H
  unfold P.Atomlessness.quoted at H
  rw [(A).holds_forall Mo] at H
  obtain ⟨p, hp⟩ := exists_inner (q := ofPred (fun _ => False) True)
    ⟨∅, Set.finite_empty, ofPred_pinned _ _ _ fun _ _ _ => Iff.rfl⟩
  have H := H p
  rw [(A).holds_imp Mo, (A).holds_dia Mo] at H
  obtain ⟨q, hq⟩ := (A).holds_exists Mo _ _ _ |>.1 (H ⟨W₁ S, c S, (holds_var_push S _ _ _).2 (by
    show _ ∈ (A).Incl _ (W₀ S) p
    rw [hp]; exact mem_ofPred_C.2 trivial)⟩)
  rw [(A).holds_conj Mo, (A).holds_conj Mo, (A).holds_dia Mo, (A).holds_eq Mo, (A).sem_disj Mo,
    (A).holds_neg Mo, (A).holds_eq Mo] at hq
  obtain ⟨⟨V, k, hk⟩, hle, hne⟩ := hq
  have hk : (⟨V, PUnit.unit, k⟩ : Tuple (A).inner .t (W₀ S)) ∈ (A).Incl _ (W₀ S) q :=
    (holds_var_push S _ _ _).1 hk
  -- `q ⊆ {c}`, `q ≠ {c}`
  have hsub : (A).Incl _ (W₀ S) q ⊆ (A).Incl _ (W₀ S) p := Set.union_eq_right.1 hle.symm
  have hq0 : (A).Incl _ (W₀ S) q = ∅ := by
    rcases tuple_cases ⟨V, PUnit.unit, k⟩ with ⟨g, e⟩ | e
    · exfalso
      have := hsub (e ▸ hk)
      rw [hp] at this
      exact mem_ofPred_N.1 this
    · apply Set.eq_empty_of_forall_notMem
      intro t ht
      apply hne
      apply Set.Subset.antisymm hsub
      intro t' ht'
      rw [hp] at ht'
      rcases tuple_cases t' with ⟨g, rfl⟩ | rfl
      · exact (mem_ofPred_N.1 ht').elim
      · exact e ▸ hk
  rw [hq0] at hk
  exact hk

/-! ### At `ℕ`: Actuality and Atomicity, as in the one-object model

The cuts of `MonoidModel` go through unchanged: they intersect with a condition on the
members of `S`, which says nothing about `c`. -/

/-- The members of `S` agreeing with `k` on `Y`, and `c`: a proposition pinned by `Y`. -/
abbrev agreeSet (Y : Set ℕ) (k : S) : Prop' S := ofPred (fun g => ∀ x ∈ Y, g • x = k • x) True

theorem agreeSet_pinned (Y : Set ℕ) (k : S) : (A).PinnedO (W := W₀ S) (.rel .t) Y (agreeSet S Y k) :=
  ofPred_pinned _ _ _ fun g g' ha => by
    constructor
    · intro h x hx; rw [← ha x hx]; exact h x hx
    · intro h x hx; rw [ha x hx]; exact h x hx

/-- **The cut.** A finitely pinned proposition containing a free `k` has a finitely pinned
proposition strictly below it still containing `k`. -/
theorem exists_ssubset_of_mem {p : Prop' S} {X : Set ℕ} (hX : X.Finite)
    (hp : (A).PinnedO (W := W₀ S) (.rel .t) X p) {k : S} (hk : tupN k ∈ p) (hfree : MonoidModel.Free k) :
    ∃ q : Prop' S, FinPinned' q ∧ q ⊆ p ∧ tupN k ∈ q ∧ q ≠ p := by
  obtain ⟨k', hagree, n, hn⟩ := hfree X hX
  refine ⟨p ∩ agreeSet S {n} k, ⟨X ∪ {n}, hX.union (Set.finite_singleton n),
    PinnedO.inter (A) (PinnedO.mono (A) Set.subset_union_left hp)
      (PinnedO.mono (A) Set.subset_union_right (agreeSet_pinned S {n} k))⟩,
    Set.inter_subset_left, ⟨hk, mem_ofPred_N.2 fun x hx => by rw [Set.mem_singleton_iff.1 hx]⟩, ?_⟩
  intro e
  have hk' : tupN k' ∈ p := (mem_iff_of_pinned hp hagree).2 hk
  have hmem : tupN k' ∈ p ∩ agreeSet S {n} k := by rw [e]; exact hk'
  exact hn (mem_ofPred_N.1 hmem.2 n rfl)

/-- **Actuality fails at `ℕ` when the identity is free.** -/
theorem not_actuality_of_free (hfree : MonoidModel.Free (1 : S)) : ¬ (A).HoldsSentence P.Actuality.quoted := by
  intro H
  rw [Premodel.HoldsSentence] at H
  unfold P.Actuality.quoted at H
  rw [(A).holds_exists Mo] at H
  obtain ⟨p, hp⟩ := H
  rw [(A).holds_conj Mo, (A).holds_forall Mo] at hp
  obtain ⟨hpt, hpq⟩ := hp
  obtain ⟨X, hX, hpin⟩ := finPinned'_Incl p
  have hk : tupN 1 ∈ (A).Incl _ (W₀ S) p := (holds_var_id S _ _).1 hpt
  obtain ⟨q, hqpin, hsub, hkq, hne⟩ := exists_ssubset_of_mem S hX hpin hk hfree
  obtain ⟨q', rfl⟩ := exists_inner hqpin
  have := hpq q'
  rw [(A).holds_imp Mo, (A).holds_eq Mo, (A).sem_disj Mo] at this
  have e := this ((holds_var_id S _ _).2 hkq)
  refine hne (Set.Subset.antisymm hsub fun t ht => ?_)
  show t ∈ (A).sem (𝟙 (A).W₀) (Term.var .zero) (.cons q' (.cons p .nil))
  rw [e]
  exact Or.inl ht

/-- **Actuality holds at `ℕ` when `{1}` is finitely pinned in `S`**: `{1}` is then the
strongest truth. -/
theorem actuality_of_pinned_one (h : MonoidModel.OnePinned S) :
    (A).HoldsSentence P.Actuality.quoted := by
  obtain ⟨N, hN, h⟩ := h
  rw [Premodel.HoldsSentence]
  unfold P.Actuality.quoted
  rw [(A).holds_exists Mo]
  obtain ⟨p, hp⟩ := exists_inner (q := ofPred (· = (1 : S)) False) ⟨N, hN, ofPred_pinned _ _ _ fun g g' ha => by
    constructor
    · rintro rfl; exact h g' fun x hx => (ha x hx).symm
    · rintro rfl; exact h g fun x hx => ha x hx⟩
  refine ⟨p, ?_⟩
  rw [(A).holds_conj Mo, (A).holds_forall Mo]
  refine ⟨(holds_var_id S _ _).2 (by show tupN 1 ∈ (A).Incl _ (W₀ S) p; rw [hp]; exact mem_ofPred_N.2 rfl),
    fun q => ?_⟩
  rw [(A).holds_imp Mo, (A).holds_eq Mo, (A).sem_disj Mo]
  intro hq
  have hq := (holds_var_id S _ _).1 hq
  show (A).Incl _ (W₀ S) q = (A).Incl _ (W₀ S) p ∪ (A).Incl _ (W₀ S) q
  refine (Set.union_eq_right.2 fun t ht => ?_).symm
  rw [hp] at ht
  rcases tuple_cases t with ⟨g, rfl⟩ | rfl
  · rw [mem_ofPred_N.1 ht]; exact hq
  · exact (mem_ofPred_C.1 ht).elim

/-- The atom condition of the quoted Atomicity at `t`, on inner propositions `a` and `z`:
`z` is strictly below `a` iff `z` is `⊥`. -/
theorem holds_atom_iff (a x : (A).Dom (W₀ S) (.rel .t)) :
    (A).Holds (𝟙 (W₀ S))
        (Term.forall' (Term.iff
          (Term.conj (Term.eq' Term.v1 (Term.disj Term.v0 Term.v1)) (Term.neg (Term.eq' Term.v0 Term.v1)))
          (Term.eq' (Term.neg Term.v0) (Term.disj Term.v0 (Term.neg Term.v0)))))
        (.cons a (.cons x .nil)) ↔
      ∀ z : (A).Dom (W₀ S) (.rel .t),
        (((A).Incl _ (W₀ S) a = (A).Incl _ (W₀ S) z ∪ (A).Incl _ (W₀ S) a ∧
          ¬ (A).Incl _ (W₀ S) z = (A).Incl _ (W₀ S) a) ↔
          ((A).Incl _ (W₀ S) z)ᶜ = (A).Incl _ (W₀ S) z ∪ ((A).Incl _ (W₀ S) z)ᶜ) := by
  rw [(A).holds_forall Mo]
  apply forall_congr'
  intro z
  rw [(A).holds_iff Mo, (A).holds_conj Mo, (A).holds_eq Mo, (A).sem_disj Mo, (A).holds_neg Mo,
    (A).holds_eq Mo, (A).holds_eq Mo, (A).sem_neg Mo, (A).sem_disj Mo, (A).sem_neg Mo]
  exact Iff.rfl

theorem eq_empty_of_compl (P : Prop' S) (h : Pᶜ = P ∪ Pᶜ) : P = ∅ :=
  Set.eq_empty_of_subset_empty fun x hx => (show x ∈ Pᶜ by rw [h]; exact Or.inl hx) hx

/-- **Atomicity at `t` fails at `ℕ`** when some nonzero finitely pinned proposition, not
containing `c`, consists of free members of `S`. -/
theorem not_atomicityT_of_free {p : Prop' S} (hp : FinPinned' p) {k₀ : S} (hk₀ : tupN k₀ ∈ p)
    (hc : tupC S ∉ p) (hfree : ∀ k : S, tupN k ∈ p → MonoidModel.Free k) :
    ¬ (A).HoldsSentence P.AtomicityT.quoted := by
  intro H
  rw [Premodel.HoldsSentence] at H
  unfold P.AtomicityT.quoted at H
  rw [(A).holds_forall Mo] at H
  obtain ⟨p', hp'⟩ := exists_inner hp
  have := H p'
  rw [(A).holds_disj Mo, (A).holds_eq Mo, (A).sem_neg Mo, (A).sem_disj Mo, (A).sem_neg Mo,
    (A).holds_exists Mo] at this
  rcases this with h1 | ⟨a, ha⟩
  · change ((A).Incl _ (W₀ S) p')ᶜ = (A).Incl _ (W₀ S) p' ∪ ((A).Incl _ (W₀ S) p')ᶜ at h1
    have := eq_empty_of_compl S _ h1
    rw [hp'] at this
    rw [this] at hk₀
    exact hk₀
  · rw [(A).holds_conj Mo, (A).holds_eq Mo, (A).sem_disj Mo] at ha
    obtain ⟨hatom, hle⟩ := ha
    have hz := (holds_atom_iff S a p').1 hatom
    have hsub : (A).Incl _ (W₀ S) a ⊆ p := by
      have : (A).Incl _ (W₀ S) p' = (A).Incl _ (W₀ S) a ∪ (A).Incl _ (W₀ S) p' := hle
      rw [hp'] at this
      exact Set.union_eq_right.1 this.symm
    have hane : (A).Incl _ (W₀ S) a ≠ ∅ := by
      intro e
      have := (hz a).2 (by rw [e, Set.compl_empty, Set.empty_union])
      exact this.2 rfl
    obtain ⟨t, ht⟩ := (Set.eq_empty_or_nonempty _).resolve_left hane
    rcases tuple_cases t with ⟨g, rfl⟩ | rfl
    · obtain ⟨X, hX, hpin⟩ := finPinned'_Incl a
      obtain ⟨q, hqpin, hqsub, hkq, hqne⟩ := exists_ssubset_of_mem S hX hpin ht (hfree _ (hsub ht))
      obtain ⟨q', rfl⟩ := exists_inner hqpin
      have := (hz q').1 ⟨(Set.union_eq_right.2 hqsub).symm, hqne⟩
      rw [eq_empty_of_compl S _ this] at hkq
      exact hkq
    · exact hc (hsub ht)

/-- **Atomicity at `t` holds at `ℕ`** when every nonzero proposition contains a tuple
whose singleton is finitely pinned: that singleton is an atom below it. -/
theorem atomicityT_of_atoms
    (h : ∀ p : Prop' S, FinPinned' p → p ≠ ∅ → ∃ t ∈ p, FinPinned' ({t} : Prop' S)) :
    (A).HoldsSentence P.AtomicityT.quoted := by
  rw [Premodel.HoldsSentence]
  unfold P.AtomicityT.quoted
  rw [(A).holds_forall Mo]
  intro p
  rw [(A).holds_disj Mo, (A).holds_eq Mo, (A).sem_neg Mo, (A).sem_disj Mo, (A).sem_neg Mo,
    (A).holds_exists Mo]
  by_cases hp0 : (A).Incl _ (W₀ S) p = ∅
  · left
    change ((A).Incl _ (W₀ S) p)ᶜ = (A).Incl _ (W₀ S) p ∪ ((A).Incl _ (W₀ S) p)ᶜ
    rw [hp0, Set.compl_empty, Set.empty_union]
  · right
    obtain ⟨t, ht, hpin⟩ := h _ (finPinned'_Incl p) hp0
    obtain ⟨a, ha⟩ := exists_inner hpin
    refine ⟨a, ?_⟩
    rw [(A).holds_conj Mo, (A).holds_eq Mo, (A).sem_disj Mo]
    refine ⟨(holds_atom_iff S a p).2 fun z => ?_, ?_⟩
    · rw [ha]
      constructor
      · rintro ⟨hz, hne⟩
        have hsub : (A).Incl _ (W₀ S) z ⊆ {t} := Set.union_eq_right.1 hz.symm
        rcases Set.subset_singleton_iff_eq.1 hsub with h0 | h1
        · rw [h0, Set.compl_empty, Set.empty_union]
        · exact absurd h1 hne
      · intro hz
        rw [eq_empty_of_compl S _ hz]
        exact ⟨by simp, fun e => Set.notMem_empty _ (e ▸ Set.mem_singleton t)⟩
    · show (A).Incl _ (W₀ S) p = (A).Incl _ (W₀ S) a ∪ (A).Incl _ (W₀ S) p
      rw [ha]
      exact (Set.union_eq_right.2 (Set.singleton_subset_iff.2 ht)).symm

/-- The singleton of `c` is pinned down by `∅`. -/
theorem singleton_c_pinned : FinPinned' ({tupC S} : Prop' S) := by
  refine ⟨∅, Set.finite_empty, ?_⟩
  have : ({tupC S} : Prop' S) = ofPred (fun _ => False) True :=
    prop_ext (fun g => ⟨fun h => absurd (congrArg Sigma.fst h) W₀_ne_W₁, fun h => (mem_ofPred_N.1 h).elim⟩)
      ⟨fun _ => mem_ofPred_C.2 trivial, fun _ => rfl⟩
  rw [this]
  exact ofPred_pinned _ _ _ fun _ _ _ => Iff.rfl

/-- The singleton of a member of `S` is pinned down by `N` when it is the only member with
its values on `N`. -/
theorem singleton_pinned_of (N : Set ℕ) (k : S) (hk : ∀ g : S, (∀ x ∈ N, g • x = k • x) → g = k) :
    (A).PinnedO (W := W₀ S) (.rel .t) N ({tupN k} : Prop' S) := by
  have : ({tupN k} : Prop' S) = ofPred (· = k) False :=
    prop_ext (fun g => ⟨fun h => mem_ofPred_N.2 (tupN_injective h), fun h => by rw [mem_ofPred_N.1 h]; rfl⟩)
      ⟨fun h => absurd (congrArg Sigma.fst h).symm W₀_ne_W₁, fun h => (mem_ofPred_C.1 h).elim⟩
  rw [this]
  exact ofPred_pinned _ _ _ fun g g' ha => by
    constructor
    · rintro rfl; exact hk g' fun x hx => (ha x hx).symm
    · rintro rfl; exact hk g fun x hx => ha x hx

/-- **Atomicity at `t` holds at `ℕ`** when every finitely pinned set of members of `S`
that is nonempty contains a member whose singleton is finitely pinned: a proposition with
no member of `S` is `{c}`, an atom. -/
theorem atomicityT_of_singletons (h : MonoidModel.Singletons S) :
    (A).HoldsSentence P.AtomicityT.quoted := by
  apply atomicityT_of_atoms
  rintro p ⟨N, hN, hp⟩ hne
  obtain ⟨t, ht⟩ := (Set.eq_empty_or_nonempty _).resolve_left hne
  rcases tuple_cases t with ⟨g, rfl⟩ | rfl
  · obtain ⟨k, hk, M, hM, hsing⟩ := h (fun g => tupN g ∈ p) ⟨N, hN, fun g g' ha => mem_iff_of_pinned hp ha⟩ g ht
    exact ⟨tupN k, hk, M, hM, singleton_pinned_of S M k hsing⟩
  · exact ⟨tupC S, ht, singleton_c_pinned S⟩

/-! ### At `ℕ`: `BF` -/

/-- **`BF` at every type holds at `ℕ` when every member of `S` is surjective**
(Proposition D.6): `c` is surjective too. -/
theorem bf_of_surjective (hs : ∀ k : S, Function.Surjective fun n : ℕ => k • n) (σ : Ty) :
    (A).HoldsSentence (Sentence.bf σ) := by
  refine Premodel.ideal_bf_of_surjective (cat S).De (W₀ := Two.nat) (fun {V} k => ?_) σ
  obtain rfl | rfl := ob_cases V
  · exact hs (toS k)
  · exact fun _ => ⟨(0 : ℕ), rfl⟩

/-- The property `λy. (ψ z → φ y)` at the individual `z`, and true of everything along
`c`. -/
def testPred (φ ψ : ℕ → Prop) (z : ℕ) : Tuple (A).inner (.arr .e .t) (W₀ S) → Prop
  | ⟨.nat, (y, _), k⟩ => ψ (fn k z) → φ y
  | ⟨.pt, _, _⟩ => True

theorem testPred_pinned (φ ψ : ℕ → Prop) (z : ℕ) :
    (A).PinnedO (W := W₀ S) (.rel (.arr .e .t)) {z} {t | testPred S φ ψ z t} := by
  intro V h i ha
  obtain rfl | rfl := ob_cases V
  · have hz : fn h z = fn i z := ha z rfl
    show Intension.map (A).inner h _ = Intension.map (A).inner i _
    ext ⟨U, ⟨y, ⟨⟩⟩, l⟩
    obtain rfl | rfl := ob_cases U
    · show (ψ (fn l (fn h z)) → φ y) ↔ (ψ (fn l (fn i z)) → φ y)
      rw [hz]
    · exact Iff.rfl
  · rw [eq_c h, eq_c i]

/-- **`BF_e` fails at `ℕ`** on the one-object model's property, true of everything along
`c`. -/
theorem not_bf_e (φ ψ : ℕ → Prop) (z : ℕ) (hw : MonoidModel.BFWitness S φ ψ z) :
    ¬ (A).HoldsSentence (Sentence.bf .e) := by
  obtain ⟨h1, h2⟩ := hw
  obtain ⟨X, hX⟩ := Premodel.ideal_pinned_inner (cat S).De (.arr .e .t) (W₀ S) {t | testPred S φ ψ z t}
    ⟨{z}, Set.finite_singleton z, testPred_pinned S φ ψ z⟩
  have hX' : (A).incl (.arr .e .t) (W₀ S) X = {t | testPred S φ ψ z t} := hX
  obtain ⟨k, hk, y, hy⟩ := h2
  refine (A).not_holds_bf_of Mo (𝟙 _) X (fun y V l => ?_) (ofS k) y ?_
  · rw [hX']
    obtain rfl | rfl := ob_cases V
    · exact h1 (toS l) y
    · trivial
  · rw [hX']
    exact fun h => hy (h hk)

/-! ### At `ℕ`: Boolean Completeness at `e → t`, as in the one-object model -/

/-- The haecceity of `m` at `ℕ`: along a member `k` of `S`, the individual `k • m`; along
`c`, the point. -/
def haecPred (m : ℕ) : Tuple (A).inner (.arr .e .t) (W₀ S) → Prop
  | ⟨.nat, (y, _), k⟩ => y = fn k m
  | ⟨.pt, _, _⟩ => True

theorem haec_pinned (m : ℕ) : (A).PinnedO (W := W₀ S) (.rel (.arr .e .t)) {m} {t | haecPred S m t} := by
  intro V h i ha
  obtain rfl | rfl := ob_cases V
  · have hm : fn h m = fn i m := ha m rfl
    show Intension.map (A).inner h _ = Intension.map (A).inner i _
    ext ⟨U, ⟨y, ⟨⟩⟩, l⟩
    obtain rfl | rfl := ob_cases U
    · show y = fn l (fn h m) ↔ y = fn l (fn i m)
      rw [hm]
    · exact Iff.rfl
  · rw [eq_c h, eq_c i]

/-- The properties including the haecceities of the members of `S'`, at `ℕ`; everything,
at the point. It does not look at the arrow. -/
def ubPred (S' : Set ℕ) : Tuple (A).inner (.arr (.rel (.arr .e .t)) .t) (W₀ S) → Prop
  | ⟨.nat, (u, _), _⟩ => ∀ m ∈ S', {t | haecPred S m t} ⊆ (A).incl _ (W₀ S) u
  | ⟨.pt, _, _⟩ => True

theorem ub_pinned (S' : Set ℕ) :
    (A).PinnedO (W := W₀ S) (.rel (.arr (.rel (.arr .e .t)) .t)) ∅ {t | ubPred S S' t} := by
  intro V h i _
  obtain rfl | rfl := ob_cases V
  · show Intension.map (A).inner h _ = Intension.map (A).inner i _
    ext ⟨U, ⟨u, ⟨⟩⟩, l⟩
    obtain rfl | rfl := ob_cases U
    · exact Iff.rfl
    · exact Iff.rfl
  · rw [eq_c h, eq_c i]

/-- The least property pinned down by `N'` including the haecceities of `S'`. -/
def lastPred (S' N' : Set ℕ) : Tuple (A).inner (.arr .e .t) (W₀ S) → Prop
  | ⟨.nat, (y, _), k⟩ => ∃ g' : S, (∀ x ∈ N', g' • x = fn k x) ∧ ∃ m' ∈ S', y = g' • m'
  | ⟨.pt, _, _⟩ => True

theorem last_pinned (S' N' : Set ℕ) :
    (A).PinnedO (W := W₀ S) (.rel (.arr .e .t)) N' {t | lastPred S S' N' t} := by
  intro V h i ha
  obtain rfl | rfl := ob_cases V
  · show Intension.map (A).inner h _ = Intension.map (A).inner i _
    ext ⟨U, ⟨y, ⟨⟩⟩, l⟩
    obtain rfl | rfl := ob_cases U
    · have e : ∀ x ∈ N', fn (h ≫ l) x = fn (i ≫ l) x := fun x hx => by
        have hx' : fn h x = fn i x := ha x hx
        show fn l (fn h x) = fn l (fn i x)
        rw [hx']
      show (∃ g' : S, (∀ x ∈ N', g' • x = fn (h ≫ l) x) ∧ _) ↔ (∃ g' : S, (∀ x ∈ N', g' • x = fn (i ≫ l) x) ∧ _)
      constructor
      · rintro ⟨g', hg', rest⟩
        exact ⟨g', fun x hx => (hg' x hx).trans (e x hx), rest⟩
      · rintro ⟨g', hg', rest⟩
        exact ⟨g', fun x hx => (hg' x hx).trans (e x hx).symm, rest⟩
    · exact Iff.rfl
  · rw [eq_c h, eq_c i]

/-- **Boolean Completeness at `e → t` fails at `ℕ`** on the condition that refutes it in the
one-object model (`MonoidModel.not_bc_of`). -/
theorem not_bc_of (S' : Set ℕ) (H : MonoidModel.BCWitness S S') :
    ¬ (A).HoldsSentence (P.BooleanCompleteness.quoted (.arr .e .t)) := by
  intro Hbc
  rw [MonoidModel.bc_quoted_eq, Premodel.HoldsSentence, (A).holds_bc_iff Mo] at Hbc
  obtain ⟨X, hX⟩ := Premodel.ideal_pinned_inner (cat S).De (.arr (.rel (.arr .e .t)) .t) (W₀ S)
    {t | ubPred S S' t} ⟨∅, Set.finite_empty, ub_pinned S S'⟩
  have hX' : (A).incl _ (W₀ S) X = {t | ubPred S S' t} := hX
  obtain ⟨y, hy⟩ := Hbc X
  have hH : ∀ m ∈ S', {t | haecPred S m t} ⊆ (A).incl _ (W₀ S) y := by
    intro m hm
    obtain ⟨z, hz⟩ := Premodel.ideal_pinned_inner (cat S).De (.arr .e .t) (W₀ S) {t | haecPred S m t}
      ⟨{m}, Set.finite_singleton m, haec_pinned S m⟩
    have hz' : (A).incl _ (W₀ S) z = {t | haecPred S m t} := hz
    rw [← hz']
    refine (hy z).1 fun u hu => ?_
    rw [hX'] at hu
    rw [hz']
    exact hu m hm
  have hyle := (hy y).2 subset_rfl
  obtain ⟨N, hN, hpin⟩ := Premodel.ideal_inner_finPinned (cat S).De (.rel (.arr .e .t)) (W₀ S) y
  obtain ⟨N', hN', h, g, hag, m, hmS, hsep⟩ := H N hN
  obtain ⟨u, hu⟩ := Premodel.ideal_pinned_inner (cat S).De (.arr .e .t) (W₀ S) {t | lastPred S S' N' t}
    ⟨N', hN', last_pinned S S' N'⟩
  have hu' : (A).incl _ (W₀ S) u = {t | lastPred S S' N' t} := hu
  have hsub := hyle u (by
    rw [hX']
    intro m' hm' t ht
    rw [hu']
    obtain ⟨V, ⟨y', ⟨⟩⟩, l⟩ := t
    obtain rfl | rfl := ob_cases V
    · exact ⟨toS l, fun _ _ => rfl, m', hm', ht⟩
    · trivial)
  -- `⟨g • m, h⟩` is in `y`, by pinning, but not in the least property pinned by `N'`
  have hg : (⟨W₀ S, (g • m, PUnit.unit), ofS g⟩ : Tuple (A).inner (.arr .e .t) (W₀ S)) ∈
      (A).incl _ (W₀ S) y := hH m hmS (show g • m = g • m from rfl)
  have e := hpin (W₀ S) (ofS g) (ofS h) (fun x hx => hag x hx)
  have := congrArg (fun P : Intension (A).inner (.arr .e .t) (W₀ S) =>
    (⟨W₀ S, (g • m, PUnit.unit), 𝟙 (W₀ S)⟩ : Tuple (A).inner (.arr .e .t) (W₀ S)) ∈ P) e
  simp only [Outer.map_rel, Intension.mem_map, Category.comp_id] at this
  have hτ := hsub (Eq.mp this hg)
  rw [hu'] at hτ
  obtain ⟨g', hg', m', hm', e'⟩ := hτ
  exact hsep g' hg' m' hm' e'.symm

/-! ### The paper's claim: `◇(□ND ∧ Atomicity)` -/

/-- **`◇(□ND_σ ∧ Atomicity)` holds at `ℕ`**, at the point. -/
theorem dia_box_nd_atomicityT (σ : Ty) :
    (A).HoldsSentence (Term.dia (Term.conj (Term.box (Sentence.nd σ)) P.AtomicityT.quoted)) := by
  rw [HoldsSentence, (A).holds_dia Mo]
  refine ⟨W₁ S, c S, ?_⟩
  rw [IEnv.nil_eq ((A).push _ IEnv.nil), (A).holds_conj Mo]
  exact ⟨box_nd_pt S _ σ, atomicityT_pt S _⟩

/-- A principle failing at `ℕ` and holding at the point is contingently false: `◇P`. -/
theorem dia_of_pt {p : Sentence Signature.pure} (hp : p.pure = true) (h : ∀ k : (A).W₀ ⟶ W₁ S, (A).Holds k p .nil) :
    (A).HoldsSentence (Term.dia p) :=
  (holds_dia_iff S hp).2 (Or.inr (h _))

/-- A principle holding at `ℕ` and at the point is necessary. -/
theorem box_of_pt {p : Sentence Signature.pure} (hp : p.pure = true) (h0 : (A).HoldsSentence p)
    (h : ∀ k : (A).W₀ ⟶ W₁ S, (A).Holds k p .nil) : (A).HoldsSentence (Term.box p) :=
  (holds_box_iff S hp).2 ⟨h0, h _⟩

/-! ### Statuses, as axiom sets holding at `ℕ` -/

theorem nd_pure (σ : Ty) : (Sentence.nd (Sig := Signature.pure) σ).pure = true := rfl
theorem bf_pure (σ : Ty) : (Sentence.bf (Sig := Signature.pure) σ).pure = true := rfl
theorem actuality_pure : P.Actuality.quoted.pure = true := rfl
theorem atomicityT_pure : P.AtomicityT.quoted.pure = true := rfl
theorem bc_pure (ρ : RTy) : (P.BooleanCompleteness.quoted ρ).pure = true := rfl

/-- **Contingently false**: failing at `ℕ`, holding at the point. -/
theorem holdsAx_cfalse {p : Sentence Signature.pure} (hp : p.pure = true) (h0 : ¬ (A).HoldsSentence p)
    (h1 : ∀ k : (A).W₀ ⟶ W₁ S, (A).Holds k p .nil) :
    (A).HoldsAx (AxiomSet.single (Term.neg p) ∪ AxiomSet.single (Term.dia p)) :=
  holdsAx_union (A) (holdsAx_single (A) (((A).holdsSentence_neg Mo _).2 h0))
    (holdsAx_single (A) (dia_of_pt S hp h1))

/-- **Necessary**: holding at `ℕ` and at the point. -/
theorem holdsAx_nec {p : Sentence Signature.pure} (hp : p.pure = true) (h0 : (A).HoldsSentence p)
    (h1 : ∀ k : (A).W₀ ⟶ W₁ S, (A).Holds k p .nil) :
    (A).HoldsAx (AxiomSet.single (Term.box p)) :=
  holdsAx_single (A) (box_of_pt S hp h0 h1)

/-- `□BF_σ` at every type, when `BF` holds at `ℕ` at every type. -/
theorem holdsAx_box_bf (hbf : ∀ σ, (A).HoldsSentence (Sentence.bf σ)) :
    (A).HoldsAx (AxiomSet.box P.Barcan.schema) := by
  rintro _ ⟨_, ⟨σ, -, rfl⟩, rfl⟩
  exact box_of_pt S (bf_pure σ) (hbf σ) fun k => bf_pt S k σ

/-- What holds at `ℕ` in every model with a point adjoined whose base refutes Boolean
Completeness at `e → t`: `ND_e` and Boolean Completeness contingently false, Atomlessness
false, and the paper's `◇(□ND_e ∧ Atomicity)`. -/
theorem holdsAx_common (hbc : ¬ (A).HoldsSentence (P.BooleanCompleteness.quoted (.arr .e .t))) :
    (A).HoldsAx (AxiomSet.single (Term.neg (Sentence.nd .e)) ∪ AxiomSet.single (Term.dia (Sentence.nd .e)) ∪
      (AxiomSet.single (Term.neg (P.BooleanCompleteness.quoted (.arr .e .t))) ∪
        AxiomSet.single (Term.dia (P.BooleanCompleteness.quoted (.arr .e .t)))) ∪
      AxiomSet.single (Term.neg P.Atomlessness.quoted) ∪
      AxiomSet.single (Term.dia (Term.conj (Term.box (Sentence.nd .e)) P.AtomicityT.quoted))) :=
  holdsAx_union (A) (holdsAx_union (A) (holdsAx_union (A)
    (holdsAx_cfalse S (nd_pure .e) (not_nd_e S) fun k => nd_pt S k .e)
    (holdsAx_cfalse S (bc_pure _) hbc fun k => bc_pt S k _))
    (holdsAx_single (A) (((A).holdsSentence_neg Mo _).2 (not_atomlessness S))))
    (holdsAx_single (A) (dia_box_nd_atomicityT S .e))

end

end Classicism.Meta.Intensional.Pointed
