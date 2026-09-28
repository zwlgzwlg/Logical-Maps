import Classicism.Semantics.IdeallyFull
import Classicism.Certified.Schemas
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.CategoryTheory.SingleObj

/-!
# Ideally full models over a monoid acting on `ℕ`

Appendix D's one-object models share a shape: a monoid `M` of functions on the
individuals `ℕ` (permutations, monotone surjections, the paper's `gₙ`, `fₙ`, `kₙ`), the
one-object category it gives, the identity action for `e`, and the ideally full model
over it. This module builds that model for any monoid acting on `ℕ`, and proves the
verdicts the parts share, each from the one feature of the monoid that decides it:

- **Actuality** fails when the identity can be perturbed off any finite set (`Free 1`),
  and holds when `{1}` is finitely pinned (`actuality_of_pinned_one`).
- **Atomlessness** holds when every arrow can be so perturbed (`Free k` for all `k`).
- **Atomicity at `t`** fails when some nonzero finitely pinned proposition consists of
  perturbable arrows, and holds when every nonzero proposition contains an arrow whose
  singleton is finitely pinned.
- **`ND` at `e`** fails when some arrow is not injective.
- **`BF`** holds at every type when every arrow is surjective (Proposition D.6), and
  fails at `e` on a property `λy. (ψ z → φ y)` when `ψ (k z) → φ (k y)` for all arrows
  and arguments but some arrow has `ψ (k z)` while `φ` fails somewhere.
- **Boolean Completeness at `e → t`** fails when properties including the haecceities of
  a set `S` can always be strengthened by pinning them down by more (`not_bc_of`): the
  upper bounds of those haecceities have no greatest lower bound. The criterion for any
  model, that Boolean Completeness is the existence of greatest lower bounds under
  inclusion of intensions, is `Premodel.holds_bc_iff`.

The paper's `Free` is its "there is a function that agrees with `h` on the finite set
and differs from it"; a proposition pinned down by `X` contains, with any arrow, every
arrow agreeing with it on `X` (`mem_iff_of_pinned`), and that is what every cut uses.
-/

namespace Classicism.Meta.Intensional.MonoidModel

open CategoryTheory Premodel

variable (M : Type) [Monoid M] [MulAction M ℕ]

/-- The one object. -/
abbrev star : SingleObj M := SingleObj.star M

instance : Subsingleton (SingleObj M) := inferInstanceAs (Subsingleton Unit)

variable {M} in
/-- An arrow of the one-object category, as the monoid element it is. -/
abbrev arrow {X Y : SingleObj M} (g : X ⟶ Y) : M := g

/-- The action of the monoid on the individuals `ℕ`, as an action of the category. -/
abbrev natAction : SingleObj M ⥤ Type where
  obj _ := ℕ
  map g := TypeCat.ofHom fun n => arrow g • n
  map_id _ := by
    ext n
    simp [arrow, SingleObj.id_as_one]
  map_comp f g := by
    ext n
    simp [arrow, SingleObj.comp_as_mul, mul_smul]

/-- The ideally full model over the monoid, with no constants. -/
noncomputable abbrev model : Premodel Signature.pure (SingleObj M) :=
  Premodel.ideal (natAction M) (star M) (fun _ => ⟨0⟩) (fun c => nomatch c)

theorem model_isModel : (model M).IsModel := Premodel.ideal_isModel (natAction M)

/-! ### Propositions as sets of arrows -/

/-- The propositions at the object, as intensions: sets of tuples `⟨(), g⟩`. -/
abbrev Prop' : Type := Intension (model M).inner .t (star M)

variable {M}

/-- The tuple of a monoid element. -/
abbrev tup (g : M) : Tuple (model M).inner .t (star M) := ⟨star M, PUnit.unit, (g : star M ⟶ star M)⟩

theorem tup_id : (⟨star M, PUnit.unit, 𝟙 (star M)⟩ : Tuple (model M).inner .t (star M)) = tup (1 : M) := by
  simp [tup, SingleObj.id_as_one]

theorem tup_injective : Function.Injective (tup (M := M)) := by
  intro g g' e
  obtain ⟨_, h⟩ := Sigma.mk.inj_iff.mp e
  exact (Prod.mk.inj (eq_of_heq h)).2

/-- Every tuple of a proposition is the tuple of a monoid element. -/
theorem tuple_eq (t : Tuple (model M).inner .t (star M)) : t = tup (arrow t.2.2) := by
  obtain ⟨V, ⟨⟩, g⟩ := t
  obtain rfl : V = star M := Subsingleton.elim _ _
  rfl

/-- Finitely pinned propositions: the inner ones. -/
def FinPinned' (p : Prop' M) : Prop := ∃ N : Set ℕ, N.Finite ∧ (model M).PinnedO (.rel .t) N p

theorem finPinned'_Incl (p : (model M).Dom (star M) (.rel .t)) : FinPinned' ((model M).Incl _ (star M) p) :=
  Premodel.ideal_inner_finPinned (natAction M) (.rel .t) (star M) p

/-- An inner proposition, from a finitely pinned one. -/
theorem exists_inner {q : Prop' M} (hq : FinPinned' q) :
    ∃ q' : (model M).Dom (star M) (.rel .t), (model M).Incl _ (star M) q' = q :=
  Premodel.ideal_pinned_inner (natAction M) .t (star M) q hq

/-- Pinning, for a proposition: two arrows agreeing on `N` are in it together. -/
theorem mem_iff_of_pinned {N : Set ℕ} {p : Prop' M} (hp : (model M).PinnedO (.rel .t) N p) {g g' : M}
    (ha : ∀ x ∈ N, g • x = g' • x) : tup g ∈ p ↔ tup g' ∈ p := by
  have e := hp (star M) (g : star M ⟶ star M) (g' : star M ⟶ star M) (fun x hx => ha x hx)
  simp only [Outer.map_rel] at e
  have := congrArg (fun S : Prop' M => (⟨star M, PUnit.unit, 𝟙 (star M)⟩ : Tuple (model M).inner .t (star M)) ∈ S) e
  simpa [Intension.mem_map, Category.comp_id] using this

/-- **Pinning, characterized**: a proposition is pinned down by `N` iff membership in it
depends only on the arrow's values on `N`. -/
theorem pinnedO_iff (N : Set ℕ) (p : Prop' M) :
    (model M).PinnedO (.rel .t) N p ↔
      ∀ g g' : M, (∀ x ∈ N, g • x = g' • x) → (tup g ∈ p ↔ tup g' ∈ p) := by
  constructor
  · intro hp g g' ha
    exact mem_iff_of_pinned hp ha
  · intro H V h i ha
    obtain rfl : V = star M := Subsingleton.elim _ _
    simp only [Outer.map_rel]
    ext ⟨U, ⟨⟩, g⟩
    obtain rfl : U = star M := Subsingleton.elim _ _
    simp only [Intension.mem_map, SingleObj.comp_as_mul]
    exact H (arrow g * arrow h) (arrow g * arrow i) fun x hx => by
      have hax : arrow h • x = arrow i • x := ha x hx
      rw [mul_smul, mul_smul, hax]

/-- A singleton `{k}` is pinned down by `N` when `k` is the only arrow with its values on
`N`. -/
theorem singleton_pinned_of (N : Set ℕ) (k : M) (hk : ∀ g : M, (∀ x ∈ N, g • x = k • x) → g = k) :
    (model M).PinnedO (.rel .t) N ({tup k} : Prop' M) := by
  rw [pinnedO_iff]
  intro g g' ha
  simp only [Set.mem_singleton_iff]
  constructor
  · intro e
    have e := tup_injective e
    rw [hk g' fun x hx => by rw [← ha x hx, e]]
  · intro e
    have e := tup_injective e
    rw [hk g fun x hx => by rw [ha x hx, e]]

/-- The proposition of the arrows satisfying a predicate. -/
abbrev ofPred (P : M → Prop) : Prop' M := {t | P (arrow t.2.2)}

theorem mem_ofPred {P : M → Prop} {g : M} : tup g ∈ ofPred P ↔ P g := Iff.rfl

/-- Such a proposition is pinned down by `N` when the predicate depends only on the values
on `N`. -/
theorem ofPred_pinned (P : M → Prop) (N : Set ℕ)
    (h : ∀ g g' : M, (∀ x ∈ N, g • x = g' • x) → (P g ↔ P g')) :
    (model M).PinnedO (.rel .t) N (ofPred P) :=
  (pinnedO_iff N _).2 fun g g' ha => h g g' ha

/-- The arrows agreeing with `k` on `Y`: a proposition pinned down by `Y`. -/
abbrev agreeSet (Y : Set ℕ) (k : M) : Prop' M := {t | ∀ x ∈ Y, arrow t.2.2 • x = k • x}

theorem agreeSet_pinned (Y : Set ℕ) (k : M) : (model M).PinnedO (.rel .t) Y (agreeSet Y k) := by
  intro V h i ha
  obtain rfl : V = star M := Subsingleton.elim _ _
  simp only [Outer.map_rel]
  ext ⟨U, ⟨⟩, g⟩
  simp only [Intension.mem_map, agreeSet, Set.mem_ofPred_eq, SingleObj.comp_as_mul]
  constructor
  · intro H x hx
    have := H x hx
    have hax : arrow h • x = arrow i • x := ha x hx
    show (arrow g * arrow i) • x = k • x
    rw [mul_smul, ← hax, ← mul_smul]; exact this
  · intro H x hx
    have := H x hx
    have hax : arrow h • x = arrow i • x := ha x hx
    show (arrow g * arrow h) • x = k • x
    rw [mul_smul, hax, ← mul_smul]; exact this

/-- `k` is **free** when off any finite set it can be perturbed: some arrow agrees with it
there and differs from it somewhere. -/
def Free (k : M) : Prop :=
  ∀ X : Set ℕ, X.Finite → ∃ k' : M, (∀ x ∈ X, k' • x = k • x) ∧ ∃ n : ℕ, k' • n ≠ k • n

/-- **The cut.** A finitely pinned proposition containing a free `k` has a finitely pinned
proposition strictly below it still containing `k`: intersect with the arrows agreeing
with `k` at a point where the perturbation differs. -/
theorem exists_ssubset_of_mem {p : Prop' M} {X : Set ℕ} (hX : X.Finite)
    (hp : (model M).PinnedO (.rel .t) X p) {k : M} (hk : tup k ∈ p) (hfree : Free k) :
    ∃ q : Prop' M, FinPinned' q ∧ q ⊆ p ∧ tup k ∈ q ∧ q ≠ p := by
  obtain ⟨k', hagree, n, hn⟩ := hfree X hX
  refine ⟨p ∩ agreeSet {n} k, ⟨X ∪ {n}, hX.union (Set.finite_singleton n),
    PinnedO.inter (model M) (PinnedO.mono (model M) Set.subset_union_left hp)
      (PinnedO.mono (model M) Set.subset_union_right (agreeSet_pinned {n} k))⟩,
    Set.inter_subset_left, ⟨hk, fun x hx => by rw [Set.mem_singleton_iff.1 hx]⟩, ?_⟩
  intro e
  have hk' : tup k' ∈ p := (mem_iff_of_pinned hp hagree).2 hk
  have hmem : tup k' ∈ p ∩ agreeSet {n} k := by rw [e]; exact hk'
  exact hn (hmem.2 n rfl)

/-! ### The verdicts -/

variable (M)

local notation "A" => model M
local notation "Mo" => model_isModel M

/-- A variable holds at the identity iff `1` is in its value. -/
theorem holds_var_id {Γ : Ctx} (v : Var Γ (.rel .t)) (g : IEnv ((A).Dom (star M)) Γ) :
    (A).Holds (𝟙 (star M)) (Term.var v) g ↔ tup 1 ∈ (A).Incl _ (star M) (g.get v) := by
  rw [Premodel.holds_var, tup_id]
  exact Iff.rfl

/-- A variable holds after moving along `k` iff `k` is in its value. -/
theorem holds_var_push {Γ : Ctx} (v : Var Γ (.rel .t)) (g : IEnv ((A).Dom (star M)) Γ)
    (k : star M ⟶ star M) :
    (A).Holds (𝟙 (star M) ≫ k) (Term.var v) ((A).push k g) ↔ tup (arrow k) ∈ (A).Incl _ (star M) (g.get v) := by
  rw [Premodel.holds_var]
  simp only [push, IEnv.get_map]
  rw [(A).incl_map, Intension.mem_map, Category.comp_id]
  exact Iff.rfl

/-- **Actuality fails when the identity is free.** -/
theorem not_actuality_of_free (hfree : Free (1 : M)) : ¬ (A).HoldsSentence P.Actuality.quoted := by
  intro H
  rw [Premodel.HoldsSentence] at H
  unfold P.Actuality.quoted at H
  rw [(A).holds_exists Mo] at H
  obtain ⟨p, hp⟩ := H
  rw [(A).holds_conj Mo, (A).holds_forall Mo] at hp
  obtain ⟨hpt, hpq⟩ := hp
  obtain ⟨X, hX, hpin⟩ := finPinned'_Incl p
  have hk : tup 1 ∈ (A).Incl _ (star M) p := (holds_var_id M _ _).1 hpt
  obtain ⟨q, hqpin, hsub, hkq, hne⟩ := exists_ssubset_of_mem hX hpin hk hfree
  obtain ⟨q', rfl⟩ := exists_inner hqpin
  have := hpq q'
  rw [(A).holds_imp Mo, (A).holds_eq Mo, (A).sem_disj Mo] at this
  have e := this ((holds_var_id M _ _).2 hkq)
  refine hne (Set.Subset.antisymm hsub fun t ht => ?_)
  show t ∈ (A).sem (𝟙 (A).W₀) (Term.var .zero) (.cons q' (.cons p .nil))
  rw [e]
  exact Or.inl ht

/-- **Actuality holds when `{1}` is finitely pinned**: it is then the strongest truth. -/
theorem actuality_of_pinned_one (h : FinPinned' ({tup 1} : Prop' M)) : (A).HoldsSentence P.Actuality.quoted := by
  rw [Premodel.HoldsSentence]
  unfold P.Actuality.quoted
  rw [(A).holds_exists Mo]
  obtain ⟨p, hp⟩ := exists_inner h
  refine ⟨p, ?_⟩
  rw [(A).holds_conj Mo, (A).holds_forall Mo]
  refine ⟨(holds_var_id M _ _).2 (by show tup (1 : M) ∈ (A).Incl _ (star M) p; rw [hp]; exact Set.mem_singleton _), fun q => ?_⟩
  rw [(A).holds_imp Mo, (A).holds_eq Mo, (A).sem_disj Mo]
  intro hq
  have hq := (holds_var_id M _ _).1 hq
  show (A).Incl _ (star M) q = (A).Incl _ (star M) p ∪ (A).Incl _ (star M) q
  rw [hp]
  exact (Set.union_eq_right.2 (Set.singleton_subset_iff.2 hq)).symm

/-- **Atomlessness holds when every arrow is free.** -/
theorem atomlessness_of_free (hfree : ∀ k : M, Free k) : (A).HoldsSentence P.Atomlessness.quoted := by
  rw [Premodel.HoldsSentence]
  unfold P.Atomlessness.quoted
  rw [(A).holds_forall Mo]
  intro p
  rw [(A).holds_imp Mo, (A).holds_dia Mo]
  rintro ⟨V, k, hk⟩
  obtain rfl : V = star M := Subsingleton.elim _ _
  have hk := (holds_var_push M _ _ _).1 hk
  obtain ⟨X, hX, hpin⟩ := finPinned'_Incl p
  obtain ⟨q, hqpin, hsub, hkq, hne⟩ := exists_ssubset_of_mem hX hpin hk (hfree _)
  obtain ⟨q', rfl⟩ := exists_inner hqpin
  rw [(A).holds_exists Mo]
  refine ⟨q', ?_⟩
  rw [(A).holds_conj Mo, (A).holds_conj Mo, (A).holds_dia Mo, (A).holds_eq Mo, (A).sem_disj Mo,
    (A).holds_neg Mo, (A).holds_eq Mo]
  refine ⟨⟨star M, k, (holds_var_push M _ _ _).2 hkq⟩, ?_, hne⟩
  show (A).Incl _ (star M) p = (A).Incl _ (star M) q' ∪ (A).Incl _ (star M) p
  exact (Set.union_eq_right.2 hsub).symm

/-- The atom condition of the quoted Atomicity at `t`, on inner propositions `a` and
`z`: `(a = z ∪ a ∧ z ≠ a) ↔ zᶜ = z ∪ zᶜ`, that is, `z` is strictly below `a` iff `z` is
`⊥`. -/
theorem holds_atom_iff (a : (A).Dom (star M) (.rel .t)) :
    (A).Holds (𝟙 (star M))
        (Term.forall' (Term.iff
          (Term.conj (Term.eq' Term.v1 (Term.disj Term.v0 Term.v1)) (Term.neg (Term.eq' Term.v0 Term.v1)))
          (Term.eq' (Term.neg Term.v0) (Term.disj Term.v0 (Term.neg Term.v0)))))
        (.cons a (.cons a .nil)) ↔
      ∀ z : (A).Dom (star M) (.rel .t),
        (((A).Incl _ (star M) a = (A).Incl _ (star M) z ∪ (A).Incl _ (star M) a ∧
          ¬ (A).Incl _ (star M) z = (A).Incl _ (star M) a) ↔
          ((A).Incl _ (star M) z)ᶜ = (A).Incl _ (star M) z ∪ ((A).Incl _ (star M) z)ᶜ) := by
  rw [(A).holds_forall Mo]
  apply forall_congr'
  intro z
  rw [(A).holds_iff Mo, (A).holds_conj Mo, (A).holds_eq Mo, (A).sem_disj Mo, (A).holds_neg Mo,
    (A).holds_eq Mo, (A).holds_eq Mo, (A).sem_neg Mo, (A).sem_disj Mo, (A).sem_neg Mo]
  exact Iff.rfl

/-- **Atomicity at `t` fails when some nonzero finitely pinned proposition consists of free
arrows**: no atom lies below it. -/
theorem not_atomicityT_of_free {p : Prop' M} (hp : FinPinned' p) (hne : p ≠ ∅)
    (hfree : ∀ k : M, tup k ∈ p → Free k) : ¬ (A).HoldsSentence P.AtomicityT.quoted := by
  intro H
  rw [Premodel.HoldsSentence] at H
  unfold P.AtomicityT.quoted at H
  rw [(A).holds_forall Mo] at H
  obtain ⟨p', hp'⟩ := exists_inner hp
  have := H p'
  rw [(A).holds_disj Mo, (A).holds_eq Mo, (A).sem_neg Mo, (A).sem_disj Mo, (A).sem_neg Mo,
    (A).holds_exists Mo] at this
  rcases this with h1 | ⟨a, ha⟩
  · -- `¬p = p ∨ ¬p`, i.e. `p ⊆ pᶜ`, i.e. `p = ∅`
    change ((A).Incl _ (star M) p')ᶜ = (A).Incl _ (star M) p' ∪ ((A).Incl _ (star M) p')ᶜ at h1
    rw [hp'] at h1
    apply hne
    apply Set.eq_empty_of_subset_empty
    intro x hx
    have : x ∈ pᶜ := by rw [h1]; exact Or.inl hx
    exact this hx
  · rw [(A).holds_conj Mo, (A).holds_eq Mo, (A).sem_disj Mo] at ha
    obtain ⟨hatom, hle⟩ := ha
    have hz := (holds_atom_iff M a).1 hatom
    -- `a ≤ p`: `p = a ∪ p`
    have hsub : (A).Incl _ (star M) a ⊆ p := by
      have : (A).Incl _ (star M) p' = (A).Incl _ (star M) a ∪ (A).Incl _ (star M) p' := hle
      rw [hp'] at this
      exact Set.union_eq_right.1 this.symm
    -- `a` is not `∅`
    have hane : (A).Incl _ (star M) a ≠ ∅ := by
      intro e
      have := (hz a).2 (by rw [e, Set.compl_empty, Set.empty_union])
      exact this.2 rfl
    obtain ⟨t, ht⟩ := (Set.eq_empty_or_nonempty _).resolve_left hane
    rw [tuple_eq t] at ht
    obtain ⟨X, hX, hpin⟩ := finPinned'_Incl a
    obtain ⟨q, hqpin, hqsub, hkq, hqne⟩ := exists_ssubset_of_mem hX hpin ht (hfree _ (hsub ht))
    obtain ⟨q', rfl⟩ := exists_inner hqpin
    have := (hz q').1 ⟨(Set.union_eq_right.2 hqsub).symm, hqne⟩
    have hq0 : (A).Incl _ (star M) q' = ∅ := by
      have h2 : (A).Incl _ (star M) q' ⊆ ((A).Incl _ (star M) q')ᶜ := by
        intro x hx; rw [this]; exact Or.inl hx
      exact Set.eq_empty_of_subset_empty fun x hx => h2 hx hx
    rw [hq0] at hkq
    exact hkq

/-- **Atomicity at `t` holds when every nonzero proposition contains an arrow whose
singleton is finitely pinned**: that singleton is an atom below it. -/
theorem atomicityT_of_singletons
    (h : ∀ p : Prop' M, FinPinned' p → p ≠ ∅ → ∃ k : M, tup k ∈ p ∧ FinPinned' ({tup k} : Prop' M)) :
    (A).HoldsSentence P.AtomicityT.quoted := by
  rw [Premodel.HoldsSentence]
  unfold P.AtomicityT.quoted
  rw [(A).holds_forall Mo]
  intro p
  rw [(A).holds_disj Mo, (A).holds_eq Mo, (A).sem_neg Mo, (A).sem_disj Mo, (A).sem_neg Mo,
    (A).holds_exists Mo]
  by_cases hp0 : (A).Incl _ (star M) p = ∅
  · left
    change ((A).Incl _ (star M) p)ᶜ = (A).Incl _ (star M) p ∪ ((A).Incl _ (star M) p)ᶜ
    rw [hp0, Set.compl_empty, Set.empty_union]
  · right
    obtain ⟨k, hk, hpin⟩ := h _ (finPinned'_Incl p) hp0
    obtain ⟨a, ha⟩ := exists_inner hpin
    refine ⟨a, ?_⟩
    rw [(A).holds_conj Mo, (A).holds_eq Mo, (A).sem_disj Mo]
    refine ⟨(holds_atom_iff M a).2 fun z => ?_, ?_⟩
    · rw [ha]
      constructor
      · rintro ⟨hz, hne⟩
        -- `z ⊆ {k}` and `z ≠ {k}`, so `z = ∅`
        have hsub : (A).Incl _ (star M) z ⊆ {tup k} := Set.union_eq_right.1 hz.symm
        rcases Set.subset_singleton_iff_eq.1 hsub with h0 | h1
        · rw [h0, Set.compl_empty, Set.empty_union]
        · exact absurd h1 hne
      · intro hz
        have h0 : (A).Incl _ (star M) z = ∅ := by
          have h2 : (A).Incl _ (star M) z ⊆ ((A).Incl _ (star M) z)ᶜ := by
            intro x hx; rw [hz]; exact Or.inl hx
          exact Set.eq_empty_of_subset_empty fun x hx => h2 hx hx
        rw [h0]
        exact ⟨by simp, fun e => Set.notMem_empty _ (e ▸ Set.mem_singleton (tup k))⟩
    · show (A).Incl _ (star M) p = (A).Incl _ (star M) a ∪ (A).Incl _ (star M) p
      rw [ha]
      exact (Set.union_eq_right.2 (Set.singleton_subset_iff.2 hk)).symm

/-- **`ND` at `e` fails when some arrow is not injective.** -/
theorem not_nd_e_of_not_injective (k : M) (hk : ¬ Function.Injective fun n : ℕ => k • n) :
    ¬ (A).HoldsSentence (Sentence.nd .e) := by
  intro H
  rw [Premodel.HoldsSentence, (A).holds_nd_iff Mo] at H
  exact hk (@H (star M) (k : star M ⟶ star M))

/-- **`BF` at every type holds when every arrow is surjective** (Proposition D.6). -/
theorem bf_of_surjective (hs : ∀ k : M, Function.Surjective fun n : ℕ => k • n) (σ : Ty) :
    (A).HoldsSentence (Sentence.bf σ) :=
  Premodel.ideal_bf_of_surjective (natAction M) (fun {_} k => hs (arrow k)) σ

/-- The property `λy. (ψ z → φ y)` at the individual `z`, as an intension of type `e → t`:
`⟨y, k⟩` is in it when `ψ (k • z) → φ y`. It is pinned down by `{z}`. -/
abbrev testProp (φ ψ : ℕ → Prop) (z : ℕ) : Intension (model M).inner (.arr .e .t) (star M) :=
  {t | ψ (arrow t.2.2 • z) → φ t.2.1.1}

theorem testProp_pinned (φ ψ : ℕ → Prop) (z : ℕ) :
    (A).PinnedO (.rel (.arr .e .t)) {z} (testProp M φ ψ z) := by
  intro V h i ha
  obtain rfl : V = star M := Subsingleton.elim _ _
  have hz : arrow h • z = arrow i • z := ha z rfl
  simp only [Outer.map_rel]
  ext ⟨U, ⟨y, ⟨⟩⟩, g⟩
  simp only [Intension.mem_map, testProp, Set.mem_ofPred_eq, SingleObj.comp_as_mul]
  show (ψ ((arrow g * arrow h) • z) → φ y) ↔ (ψ ((arrow g * arrow i) • z) → φ y)
  rw [mul_smul, mul_smul, hz]

/-- **`BF` at `e` fails** on the property `λy. (ψ z → φ y)`: every arrow `k` and argument
`y` have `ψ (k z) → φ (k y)`, so `∀y □Xy`; but some arrow `k` has `ψ (k z)` while `φ` fails
somewhere, so not `□∀y Xy`. -/
theorem not_bf_e (φ ψ : ℕ → Prop) (z : ℕ) (h1 : ∀ (k : M) (y : ℕ), ψ (k • z) → φ (k • y))
    (h2 : ∃ k : M, ψ (k • z) ∧ ∃ y, ¬ φ y) : ¬ (A).HoldsSentence (Sentence.bf .e) := by
  intro H
  rw [Premodel.HoldsSentence, Sentence.bf, (A).holds_forall Mo] at H
  obtain ⟨X, hX⟩ := Premodel.ideal_pinned_inner (natAction M) (.arr .e .t) (star M) (testProp M φ ψ z)
    ⟨{z}, Set.finite_singleton z, testProp_pinned M φ ψ z⟩
  have hX' : (A).incl (.arr .e .t) (A).W₀ X = testProp M φ ψ z := hX
  have H := H X
  rw [(A).holds_imp Mo] at H
  have H := H (by
    rw [(A).holds_forall Mo]
    intro y
    change ℕ at y
    rw [(A).holds_box Mo]
    intro V k
    obtain rfl : V = star M := Subsingleton.elim _ _
    rw [(A).holds_app (Γ := [Ty.e, Ty.rel (.arr .e .t)]) (σ := .e) (𝟙 (A).W₀ ≫ k) _ Term.v1 Term.v0
      (a' := arrow k • y) rfl]
    simp only [push]
    show (⟨star M, (arrow k • y, PUnit.unit), 𝟙 (star M)⟩ : Tuple (model M).inner (.arr .e .t) (star M))
      ∈ (A).incl _ (star M) (((A).inner _).map k X)
    rw [(A).incl_map, Intension.mem_map, Category.comp_id]
    rw [hX']
    exact h1 (arrow k) y)
  rw [(A).holds_box Mo] at H
  obtain ⟨k, hk, y, hy⟩ := h2
  have H := @H (star M) (k : star M ⟶ star M)
  rw [(A).holds_forall Mo] at H
  have H := H y
  rw [(A).holds_app (Γ := [Ty.e, Ty.rel (.arr .e .t)]) (σ := .e) (𝟙 (A).W₀ ≫ (k : star M ⟶ star M)) _
    Term.v1 Term.v0 (a' := y) rfl] at H
  simp only [push] at H
  change (⟨star M, (y, PUnit.unit), 𝟙 (star M)⟩ : Tuple (model M).inner (.arr .e .t) (star M))
    ∈ (A).incl _ (star M) (((A).inner _).map (k : star M ⟶ star M) X) at H
  rw [(A).incl_map, Intension.mem_map, Category.comp_id] at H
  rw [hX] at H
  exact hy (H hk)

/-! ### Boolean Completeness at `e → t`

The paper's argument (Appendix D, Part 2, and footnote 95): a property of properties with
no least upper bound. Fix a set `S` of individuals; the upper bounds of the haecceities of
the members of `S` are the properties whose extension along every arrow `k` contains
`k[S]`. That condition does not look at the arrow, so it is an element of the model
pinned down by `∅`, and a greatest lower bound of it would be a least such property.
There is none when finitely pinned properties can always be made stronger: a property
pinned down by `N` that contains the haecceities of `S` contains, along `h`, every `g • m`
with `m ∈ S` and `g` agreeing with `h` on `N`; the least one pinned down by a larger `N'`
contains only the `g' • m'` with `g'` agreeing with `h` on `N'`, and the monoid decides
whether that is fewer. -/

/-- The quoted Boolean Completeness is the sentence the semantic criterion is stated for. -/
theorem bc_quoted_eq (ρ : RTy) : P.BooleanCompleteness.quoted ρ = Sentence.bc ρ := rfl

/-- The haecceity of `m`, `λx. x = m`, as an intension of type `e → t` at an object: along
an arrow `k`, the individual `k • m`. -/
abbrev haec (V : SingleObj M) (m : ℕ) : Intension (model M).inner (.arr .e .t) V :=
  {t | t.2.1.1 = arrow t.2.2 • m}

theorem haec_pinned (m : ℕ) : (A).PinnedO (.rel (.arr .e .t)) {m} (haec M (star M) m) := by
  intro V h i ha
  obtain rfl : V = star M := Subsingleton.elim _ _
  have hm : arrow h • m = arrow i • m := ha m rfl
  simp only [Outer.map_rel]
  ext ⟨U, ⟨y, ⟨⟩⟩, g⟩
  simp only [Intension.mem_map, haec, Set.mem_ofPred_eq, SingleObj.comp_as_mul]
  show y = (arrow g * arrow h) • m ↔ y = (arrow g * arrow i) • m
  rw [mul_smul, mul_smul, hm]

/-- The properties including the haecceities of the members of `S`, as a property of
properties. It does not look at the arrow. -/
abbrev upperBounds (S : Set ℕ) : Intension (model M).inner (.arr (.rel (.arr .e .t)) .t) (star M) :=
  {t | ∀ m ∈ S, haec M t.1 m ⊆ (A).incl _ t.1 t.2.1.1}

theorem upperBounds_pinned (S : Set ℕ) :
    (A).PinnedO (.rel (.arr (.rel (.arr .e .t)) .t)) ∅ (upperBounds M S) :=
  fun _ _ _ _ => rfl

/-- The least property pinned down by `N'` including the haecceities of `S`: along `h`, the
`g' • m'` with `m' ∈ S` and `g'` agreeing with `h` on `N'`. -/
abbrev leastAbove (S N' : Set ℕ) : Intension (model M).inner (.arr .e .t) (star M) :=
  {t | ∃ g' : M, (∀ x ∈ N', g' • x = arrow t.2.2 • x) ∧ ∃ m' ∈ S, t.2.1.1 = g' • m'}

theorem leastAbove_pinned (S N' : Set ℕ) : (A).PinnedO (.rel (.arr .e .t)) N' (leastAbove M S N') := by
  intro V h i ha
  obtain rfl : V = star M := Subsingleton.elim _ _
  simp only [Outer.map_rel]
  ext ⟨U, ⟨y, ⟨⟩⟩, g⟩
  simp only [Intension.mem_map, leastAbove, Set.mem_ofPred_eq, SingleObj.comp_as_mul]
  have e : ∀ x ∈ N', (arrow g * arrow h) • x = (arrow g * arrow i) • x := fun x hx => by
    have hx' : arrow h • x = arrow i • x := ha x hx
    rw [mul_smul, mul_smul, hx']
  constructor
  · rintro ⟨g', hg', rest⟩
    exact ⟨g', fun x hx => (hg' x hx).trans (e x hx), rest⟩
  · rintro ⟨g', hg', rest⟩
    exact ⟨g', fun x hx => (hg' x hx).trans (e x hx).symm, rest⟩

/-- Pinning, for an intension of any relational type: two arrows agreeing on `N` hold of
the same arguments. -/
theorem mem_iff_of_pinnedR {ρ : RTy} {N : Set ℕ} {p : Intension (model M).inner ρ (star M)}
    (hp : (A).PinnedO (.rel ρ) N p) {g g' : M} (ha : ∀ x ∈ N, g • x = g' • x)
    (a : Args (model M).inner ρ (star M)) :
    (⟨star M, a, (g : star M ⟶ star M)⟩ : Tuple (model M).inner ρ (star M)) ∈ p ↔
      (⟨star M, a, (g' : star M ⟶ star M)⟩ : Tuple (model M).inner ρ (star M)) ∈ p := by
  have e := hp (star M) (g : star M ⟶ star M) (g' : star M ⟶ star M) (fun x hx => ha x hx)
  simp only [Outer.map_rel] at e
  have := congrArg (fun S : Intension (model M).inner ρ (star M) =>
    (⟨star M, a, 𝟙 (star M)⟩ : Tuple (model M).inner ρ (star M)) ∈ S) e
  simpa [Intension.mem_map, Category.comp_id] using this

/-- **Boolean Completeness at `e → t` fails** when finitely pinned properties including the
haecceities of `S` can always be strengthened: for every finite `N` there are a finite
`N'`, arrows `h` and `g` agreeing on `N`, and `m ∈ S`, such that no arrow agreeing with `h`
on `N'` sends a member of `S` to `g • m`. Then the upper bounds of those haecceities have
no greatest lower bound: one, `y`, would be pinned down by some finite `N`, would contain
`⟨g • m, h⟩`, and would be included in `leastAbove S N'`, which does not. -/
theorem not_bc_of (S : Set ℕ)
    (H : ∀ N : Set ℕ, N.Finite → ∃ N' : Set ℕ, N'.Finite ∧ ∃ h g : M, (∀ x ∈ N, g • x = h • x) ∧
      ∃ m ∈ S, ∀ g' : M, (∀ x ∈ N', g' • x = h • x) → ∀ m' ∈ S, g' • m' ≠ g • m) :
    ¬ (A).HoldsSentence (P.BooleanCompleteness.quoted (.arr .e .t)) := by
  intro Hbc
  rw [bc_quoted_eq, Premodel.HoldsSentence, (A).holds_bc_iff Mo] at Hbc
  obtain ⟨X, hX⟩ := Premodel.ideal_pinned_inner (natAction M) (.arr (.rel (.arr .e .t)) .t) (star M)
    (upperBounds M S) ⟨∅, Set.finite_empty, upperBounds_pinned M S⟩
  obtain ⟨y, hy⟩ := Hbc X
  -- every haecceity of a member of `S` is a lower bound, so is included in `y`
  have hH : ∀ m ∈ S, haec M (star M) m ⊆ (A).incl _ (star M) y := by
    intro m hm
    obtain ⟨z, hz⟩ := Premodel.ideal_pinned_inner (natAction M) (.arr .e .t) (star M) (haec M (star M) m)
      ⟨{m}, Set.finite_singleton m, haec_pinned M m⟩
    have hz' : (A).incl _ (star M) z = haec M (star M) m := hz
    rw [← hz']
    refine (hy z).1 fun u hu => ?_
    show (A).incl _ (star M) z ⊆ (A).incl _ (star M) u
    have hu' : (⟨star M, (u, PUnit.unit), 𝟙 (star M)⟩ :
        Tuple (model M).inner (.arr (.rel (.arr .e .t)) .t) (star M)) ∈ upperBounds M S := by
      rw [← hX]; exact hu
    rw [hz']
    exact hu' m hm
  -- `y` is included in every upper bound
  have hyle := (hy y).2 subset_rfl
  obtain ⟨N, hN, hpin⟩ := Premodel.ideal_inner_finPinned (natAction M) (.rel (.arr .e .t)) (star M) y
  obtain ⟨N', hN', h, g, hag, m, hmS, hsep⟩ := H N hN
  obtain ⟨u, hu⟩ := Premodel.ideal_pinned_inner (natAction M) (.arr .e .t) (star M) (leastAbove M S N')
    ⟨N', hN', leastAbove_pinned M S N'⟩
  have hu' : (A).incl _ (star M) u = leastAbove M S N' := hu
  have hsub := hyle u (by
    show _ ∈ (A).incl _ (star M) X
    rw [hX]
    intro m' hm' t ht
    show t ∈ (A).incl _ (star M) u
    rw [hu']
    exact ⟨arrow t.2.2, fun _ _ => rfl, m', hm', ht⟩)
  -- `⟨g • m, h⟩` is in `y`, by pinning, but not in `leastAbove S N'`
  have hτ : (⟨star M, (g • m, PUnit.unit), (h : star M ⟶ star M)⟩ : Tuple (model M).inner (.arr .e .t) (star M))
      ∈ (A).incl _ (star M) y :=
    (mem_iff_of_pinnedR M hpin (fun x hx => (hag x hx).symm) _).2
      (hH m hmS (show (⟨star M, (g • m, PUnit.unit), (g : star M ⟶ star M)⟩ :
        Tuple (model M).inner (.arr .e .t) (star M)) ∈ haec M (star M) m from rfl))
  have := hsub hτ
  change _ ∈ (A).incl _ (star M) u at this
  rw [hu'] at this
  obtain ⟨g', hg', m', hm', e⟩ := this
  exact hsep g' hg' m' hm' e.symm

end Classicism.Meta.Intensional.MonoidModel
