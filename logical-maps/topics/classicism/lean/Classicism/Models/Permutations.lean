import Classicism.Semantics.IdeallyFull
import Classicism.Semantics.IntensionalExamples
import Classicism.Certified.Schemas
import Mathlib.Logic.Equiv.Basic
import Mathlib.Algebra.Group.End

/-!
# Appendix D, Part 1: the permutation group of `ℕ`

The first of the paper's ideally full models (Classicism, Appendix D, "Part 1"): the
category with one object `ℕ` whose arrows are all the permutations of `ℕ`, the identity
action for `e`, and at each relational type the intensions pinned down by some finite set
of numbers. "There are infinitely many individuals, all playing distinct qualitative
roles, over which these roles can be redistributed in any way", and "the only
propositions and properties are ones that are about some finite collection of
individuals".

The verdicts, each a theorem about the quoted principle the map's records use:

- **`□ND_σ` and `□BF_σ` at every type** (`box_nd`, `box_bf`): every arrow is an
  isomorphism.
- **Actuality fails** (`not_actuality`): a true proposition `p` pinned down by a finite
  `X` is not the strongest truth, since `q := p ∩ {h | h n = n}` for `n ∉ X` is a truth
  strictly stronger than it, `p` containing a permutation that moves `n` and agrees with
  the identity on `X`.
- **Atomlessness holds** (`atomlessness`): the same cut, relative to any arrow in `p`
  rather than the identity.
- **Atomicity at `t` fails** (`not_atomicityT`): `⊤` has no atom below it, since any
  nonzero proposition has a nonzero proposition strictly below it.

One lemma does the work (`exists_ssubset_of_mem`): a finitely pinned proposition containing
an arrow `k` has a finitely pinned proposition strictly below it still containing `k`.
The model's Boolean Completeness failure, which the paper gets from Proposition 2.5, waits
on that proposition's certification (agenda item 2).
-/

namespace Classicism.Meta.Intensional.Perms

open CategoryTheory Premodel

/-- The permutation group of `ℕ`. -/
abbrev G : Type := Equiv.Perm ℕ

/-- The one object. -/
abbrev star : SingleObj G := SingleObj.star G

instance : Subsingleton (SingleObj G) := inferInstanceAs (Subsingleton Unit)

/-- An arrow of the one-object category, as the permutation it is. -/
abbrev perm {X Y : SingleObj G} (g : X ⟶ Y) : G := g

/-- The identity action of the permutations on the individuals `ℕ`. -/
abbrev natAction : SingleObj G ⥤ Type where
  obj _ := ℕ
  map g := TypeCat.ofHom (⇑(perm g))
  map_id _ := by
    ext n
    rfl
  map_comp _ _ := by
    ext n
    rfl

/-- **The model of Part 1**: ideally full over the permutations, with no constants. -/
noncomputable abbrev model : Premodel Signature.pure (SingleObj G) :=
  Premodel.ideal natAction star (fun _ => ⟨0⟩) (fun c => nomatch c)

theorem model_isModel : model.IsModel := Premodel.ideal_isModel natAction

local notation "M" => model_isModel

/-! ### Propositions as sets of permutations -/

/-- The propositions at the object, as intensions: sets of tuples `⟨(), g⟩`. -/
abbrev Prop' : Type := Intension (IdealT natAction) .t star

/-- The tuple of a permutation. -/
abbrev tup (g : G) : Tuple (IdealT natAction) .t star := ⟨star, PUnit.unit, (g : star ⟶ star)⟩

theorem tup_id : (⟨star, PUnit.unit, 𝟙 star⟩ : Tuple (IdealT natAction) .t star) = tup 1 := by
  simp [tup, SingleObj.id_as_one]

/-- Every tuple of a proposition is the tuple of a permutation. -/
theorem tuple_eq (t : Tuple (IdealT natAction) .t star) : t = tup (perm t.2.2) := by
  obtain ⟨V, ⟨⟩, g⟩ := t
  obtain rfl : V = star := Subsingleton.elim _ _
  rfl

/-- Pinning, for a proposition: two permutations agreeing on `N` are in it together. -/
theorem mem_iff_of_pinned {N : Set ℕ} {p : Prop'} (hp : model.PinnedO (.rel .t) N p) {g g' : G}
    (ha : ∀ x ∈ N, g x = g' x) : tup g ∈ p ↔ tup g' ∈ p := by
  have e := hp star (g : star ⟶ star) (g' : star ⟶ star) (fun x hx => ha x hx)
  simp only [Outer.map_rel] at e
  have := congrArg (fun S : Prop' => (⟨star, PUnit.unit, 𝟙 star⟩ : Tuple (IdealT natAction) .t star) ∈ S) e
  simpa [Intension.mem_map, Category.comp_id] using this

/-- "`h n = v`", a proposition pinned down by `{n}`. -/
abbrev fix (n v : ℕ) : Prop' := {t | perm t.2.2 n = v}

theorem fix_pinned (n v : ℕ) : model.PinnedO (.rel .t) {n} (fix n v) := by
  intro V h i ha
  obtain rfl : V = star := Subsingleton.elim _ _
  have hn : perm h n = perm i n := ha n rfl
  simp only [Outer.map_rel]
  ext ⟨U, ⟨⟩, g⟩
  simp only [Intension.mem_map, fix, Set.mem_ofPred_eq, SingleObj.comp_as_mul]
  show perm g (perm h n) = v ↔ perm g (perm i n) = v
  rw [hn]

/-- **The cut.** A finitely pinned proposition containing `k` has a finitely pinned
proposition strictly below it still containing `k`: intersect with "`h n = k n`" for an
`n` outside the pinning set. The proposition is strictly bigger because it also contains
the permutation that agrees with `k` on the pinning set and sends `n` elsewhere. -/
theorem exists_ssubset_of_mem {p : Prop'} {X : Set ℕ} (hX : X.Finite)
    (hp : model.PinnedO (.rel .t) X p) {k : G} (hk : tup k ∈ p) :
    ∃ q : Prop', (∃ Y : Set ℕ, Y.Finite ∧ model.PinnedO (.rel .t) Y q) ∧ q ⊆ p ∧ tup k ∈ q ∧ q ≠ p := by
  obtain ⟨n, hn⟩ := hX.exists_notMem
  obtain ⟨m, hm⟩ := ((hX.image k).union (Set.finite_singleton (k n))).exists_notMem
  refine ⟨p ∩ fix n (k n), ⟨X ∪ {n}, hX.union (Set.finite_singleton n),
    PinnedO.inter model (PinnedO.mono model Set.subset_union_left hp)
      (PinnedO.mono model Set.subset_union_right (fix_pinned n (k n)))⟩,
    Set.inter_subset_left, ⟨hk, show k n = k n from rfl⟩, ?_⟩
  intro e
  -- the permutation agreeing with `k` on `X` and sending `n` to `m`
  let k' : G := Equiv.swap (k n) m * k
  have hagree : ∀ x ∈ X, k' x = k x := by
    intro x hx
    show Equiv.swap (k n) m (k x) = k x
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h; exact hn (k.injective h ▸ hx)
    · intro h; exact hm (Or.inl ⟨x, hx, h⟩)
  have hk' : tup k' ∈ p := (mem_iff_of_pinned hp hagree).2 hk
  have hmem : tup k' ∈ p ∩ fix n (k n) := by rw [e]; exact hk'
  have hmn : k' n = k n := hmem.2
  have hm' : k' n = m := Equiv.swap_apply_left _ _
  exact hm (Or.inr (hm'.symm.trans hmn))

/-! ### The verdicts -/

/-- `□ND_σ` holds at every type: every permutation is an isomorphism. -/
theorem box_nd (σ : Ty) : model.HoldsSentence (Term.box (Sentence.nd σ)) :=
  model.holds_box_nd_of_groupoid M σ

/-- `□BF_σ` likewise. -/
theorem box_bf (σ : Ty) : model.HoldsSentence (Term.box (Sentence.bf σ)) :=
  model.holds_box_bf_of_groupoid M σ

/-- An inner proposition, from a finitely pinned one. -/
theorem exists_inner {q : Prop'} (hq : ∃ Y : Set ℕ, Y.Finite ∧ model.PinnedO (.rel .t) Y q) :
    ∃ q' : model.Dom star (.rel .t), model.Incl _ star q' = q :=
  Premodel.ideal_pinned_inner natAction .t star q hq

/-- A variable holds at the identity iff `1` is in its value. -/
theorem holds_var_id {Γ : Ctx} (v : Var Γ (.rel .t)) (g : IEnv (model.Dom star) Γ) :
    model.Holds (𝟙 star) (Term.var v) g ↔ tup 1 ∈ model.Incl _ star (g.get v) := by
  rw [Premodel.holds_var, tup_id]
  exact Iff.rfl

/-- The value of a variable moved along an arrow `k`, as a membership: `k` is in it. -/
theorem holds_var_push {Γ : Ctx} (v : Var Γ (.rel .t)) (g : IEnv (model.Dom star) Γ)
    (k : star ⟶ star) :
    model.Holds (𝟙 star ≫ k) (Term.var v) (model.push k g) ↔ tup (perm k) ∈ model.Incl _ star (g.get v) := by
  rw [Premodel.holds_var]
  simp only [push, IEnv.get_map]
  rw [model.incl_map, Intension.mem_map, Category.comp_id]
  exact Iff.rfl

/-- **Actuality fails.** -/
theorem not_actuality : ¬ model.HoldsSentence P.Actuality.quoted := by
  intro H
  rw [Premodel.HoldsSentence] at H
  unfold P.Actuality.quoted at H
  rw [model.holds_exists M] at H
  obtain ⟨p, hp⟩ := H
  rw [model.holds_conj M, model.holds_forall M] at hp
  obtain ⟨hpt, hpq⟩ := hp
  obtain ⟨X, hX, hpin⟩ := Premodel.ideal_inner_finPinned natAction (.rel .t) star p
  have hk : tup 1 ∈ model.Incl _ star p := (holds_var_id _ _).1 hpt
  obtain ⟨q, hqpin, hsub, hkq, hne⟩ := exists_ssubset_of_mem hX hpin hk
  obtain ⟨q', rfl⟩ := exists_inner hqpin
  have := hpq q'
  rw [model.holds_imp M, model.holds_eq M, model.sem_disj M] at this
  have e := this ((holds_var_id _ _).2 hkq)
  -- `e : q' = p ∪ q'`, so `p ⊆ q'`, so `q' = p`
  refine hne (Set.Subset.antisymm hsub fun t ht => ?_)
  show t ∈ model.sem (𝟙 model.W₀) (Term.var .zero) (.cons q' (.cons p .nil))
  rw [e]
  exact Or.inl ht

/-- **Atomlessness holds.** -/
theorem atomlessness : model.HoldsSentence P.Atomlessness.quoted := by
  rw [Premodel.HoldsSentence]
  unfold P.Atomlessness.quoted
  rw [model.holds_forall M]
  intro p
  rw [model.holds_imp M, model.holds_dia M]
  rintro ⟨V, k, hk⟩
  obtain rfl : V = star := Subsingleton.elim _ _
  have hk := (holds_var_push _ _ _).1 hk
  obtain ⟨X, hX, hpin⟩ := Premodel.ideal_inner_finPinned natAction (.rel .t) star p
  obtain ⟨q, hqpin, hsub, hkq, hne⟩ := exists_ssubset_of_mem hX hpin hk
  obtain ⟨q', rfl⟩ := exists_inner hqpin
  rw [model.holds_exists M]
  refine ⟨q', ?_⟩
  rw [model.holds_conj M, model.holds_conj M, model.holds_dia M, model.holds_eq M, model.sem_disj M,
    model.holds_neg M, model.holds_eq M]
  refine ⟨⟨star, k, ?_⟩, ?_, ?_⟩
  · exact (holds_var_push _ _ _).2 hkq
  · -- `p = q' ∪ p`
    show model.Incl _ star p = model.Incl _ star q' ∪ model.Incl _ star p
    exact (Set.union_eq_right.2 hsub).symm
  · -- `q' ≠ p`
    exact hne

/-- **Atomicity at `t` fails**: `⊤` has no atom below it. -/
theorem not_atomicityT : ¬ model.HoldsSentence P.AtomicityT.quoted := by
  intro H
  rw [Premodel.HoldsSentence] at H
  unfold P.AtomicityT.quoted at H
  rw [model.holds_forall M] at H
  obtain ⟨top, htop⟩ := exists_inner (q := Set.univ) ⟨∅, Set.finite_empty, PinnedO.univ model ∅⟩
  have := H top
  rw [model.holds_disj M, model.holds_eq M, model.sem_neg M, model.sem_disj M, model.sem_neg M,
    model.holds_exists M] at this
  rcases this with h1 | ⟨a, ha⟩
  · -- `¬⊤ = ⊤ ∨ ¬⊤`: `∅ = univ`
    change (model.Incl _ star top)ᶜ = model.Incl _ star top ∪ (model.Incl _ star top)ᶜ at h1
    rw [htop, Set.compl_univ, Set.union_empty] at h1
    exact Set.notMem_empty (tup 1) (h1 ▸ Set.mem_univ _)
  · rw [model.holds_conj M, model.holds_forall M] at ha
    obtain ⟨hatom, -⟩ := ha
    -- the atom condition at `z`: `(a = z ∪ a ∧ z ≠ a) ↔ zᶜ = z ∪ zᶜ`
    have hz : ∀ z : model.Dom star (.rel .t),
        ((model.Incl _ star a = model.Incl _ star z ∪ model.Incl _ star a ∧
          ¬ model.Incl _ star z = model.Incl _ star a) ↔
          (model.Incl _ star z)ᶜ = model.Incl _ star z ∪ (model.Incl _ star z)ᶜ) := by
      intro z
      have := hatom z
      rw [model.holds_iff M, model.holds_conj M, model.holds_eq M, model.sem_disj M, model.holds_neg M,
        model.holds_eq M, model.holds_eq M, model.sem_neg M, model.sem_disj M, model.sem_neg M] at this
      exact this
    -- `a` is not `∅`: at `z := a` the left side fails, so `aᶜ ≠ a ∪ aᶜ`
    have hne : model.Incl _ star a ≠ ∅ := by
      intro e
      have := (hz a).2 (by rw [e, Set.compl_empty, Set.empty_union])
      exact this.2 rfl
    obtain ⟨t, ht⟩ := (Set.eq_empty_or_nonempty _).resolve_left hne
    rw [tuple_eq t] at ht
    obtain ⟨X, hX, hpin⟩ := Premodel.ideal_inner_finPinned natAction (.rel .t) star a
    obtain ⟨q, hqpin, hsub, hkq, hqne⟩ := exists_ssubset_of_mem hX hpin ht
    obtain ⟨q', rfl⟩ := exists_inner hqpin
    -- `q'` is strictly below `a`, so by the atom condition `q'ᶜ = q' ∪ q'ᶜ`, i.e. `q' = ∅`
    have := (hz q').1 ⟨(Set.union_eq_right.2 hsub).symm, hqne⟩
    have hq0 : model.Incl _ star q' = ∅ := by
      have h2 : model.Incl _ star q' ⊆ (model.Incl _ star q')ᶜ := by
        intro x hx; rw [this]; exact Or.inl hx
      exact Set.eq_empty_of_subset_empty fun x hx => h2 hx hx
    rw [hq0] at hkq
    exact hkq

/-- The same for the `t`-instance of the type-indexed Atomicity, whose `¬_t` and `∨_t` read
as `¬` and `∨` do: the two sentences have the same value by `rfl`. -/
theorem not_atomicity_t : ¬ model.HoldsSentence (P.Atomicity.quoted RTy.t) := not_atomicityT

end Classicism.Meta.Intensional.Perms
