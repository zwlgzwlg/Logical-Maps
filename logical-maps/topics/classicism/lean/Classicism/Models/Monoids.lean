import Classicism.Models.MonoidModel
import Mathlib.Algebra.Group.Submonoid.MulAction
import Mathlib.Algebra.Group.Action.End
import Mathlib.Order.Monotone.Basic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.Nat.Even

/-!
# Appendix D, Parts 2 to 8: the models on monoids of functions on `ℕ`

The paper's remaining one-object models (Classicism, Appendix D, Parts 2 to 8), each the
ideally full model over a monoid of functions on `ℕ`, built by `MonoidModel` from the
submonoid of `Function.End ℕ`:

| part | monoid | ND | BF | Actuality | Atomicity | BC (`e → t`) |
| --- | --- | --- | --- | --- | --- | --- |
| 2 | monotone surjections | fails | holds | fails | fails | fails |
| 3 | monotone functions | fails | fails | fails | fails | fails |
| 4 | monotone, collapsing `0, 1` unless the identity | fails | fails | holds | fails | fails |
| 5 | as 4, surjective | fails | holds | holds | fails | fails |
| 6 | the identity and the truncations `gₙ m = min m n` | fails | fails | fails | holds | fails |
| 7 | the roundings `f_{2^j} m = 2^j ⌊m / 2^j⌋` | fails | fails | holds | holds | fails |
| 8 | the shifts `kₙ m = m ∸ n` | fails | holds | holds | holds | fails |

Each verdict is an instance of a lemma of `MonoidModel` at the one fact about the monoid
that decides it: an arrow that is not injective (`ND`), surjectivity of every arrow
(`BF`, by Proposition D.6) or a property `λy. (ψ z → φ y)` refuting it, whether an arrow
can be perturbed off any finite set (`Free`), and whether singletons are finitely pinned.
Atomlessness holds where every arrow is free (Parts 2 and 3). No Pure Contingency holds
in every model on a monoid (`Premodel.holdsAx_npc`), so each verdict is a verdict on the
principle's necessitation too; `Results/Schemas/Consistency.lean` states the packages.

Boolean Completeness fails at `e → t` in every part (Proposition D.5), by
`MonoidModel.not_bc_of`: the haecceities of a set `S` of numbers have no least upper
bound. The witnesses are the paper's. In Parts 2 to 5, `S` is the even numbers and one
pair of arrows serves all four monoids (`not_bc_of_mono`): `pred` and `step n`, which
agree up to `n + 1` and differ at `n + 2`, where `step n` sends the even `n + 2` to the
even `n`, which no monotone arrow agreeing with `pred` up to `n + 2` sends an even number
to. In Part 6, `S` is everything, with `gₙ` and the identity; in Part 7 everything, with
`f_{2^{j+1}}` and `f_{2^j}`; in Part 8 the evens, with `k_{n+1}` and `k_{n+2}`.

Part 7 is indexed by the exponent: `round j` is the paper's `f_{2^j}`, and `{f_{2^j}}` is
pinned down by `{2^j - 1, 2^j}` (two points rather than the paper's three, since an arrow
of this monoid sending `2^j` to itself and `2^j - 1` to `0` can only be `f_{2^j}`).

The paper's perturbations are made concrete: for a monotone surjection `k`, `k ∘ rep m`
with `rep m` repeating the value at `m` (surjective and monotone, so back in the monoid),
which differs from `k` because a monotone surjection is unbounded; for a monotone
function, `k` raised by one beyond `m`; for the truncations, `gₘ` itself.
-/

namespace Classicism.Meta.Intensional.Monoids

open CategoryTheory MonoidModel Premodel

/-- Functions on `ℕ` under composition, acting on `ℕ` by application. -/
abbrev F : Type := Function.End ℕ

theorem smul_eq {S : Submonoid F} (g : S) (n : ℕ) : g • n = (g : F) n := rfl

theorem mul_apply' {S : Submonoid F} (g h : S) (n : ℕ) : ((g * h : S) : F) n = (g : F) ((h : F) n) := rfl

theorem one_apply' {S : Submonoid F} (n : ℕ) : ((1 : S) : F) n = n := rfl

/-- A finite set of numbers lies below some bound. -/
theorem exists_bound {X : Set ℕ} (hX : X.Finite) : ∃ m : ℕ, ∀ x ∈ X, x ≤ m := by
  obtain ⟨m, hm⟩ := hX.bddAbove
  exact ⟨m, fun x hx => hm hx⟩

/-! ### Perturbations -/

/-- `rep m` repeats the value at `m`: the identity up to `m`, then one behind. Monotone
and surjective. -/
def rep (m : ℕ) : F := fun x => if x ≤ m then x else x - 1

theorem rep_mono (m : ℕ) : Monotone (rep m) := by
  intro x y hxy
  simp only [rep]
  split_ifs <;> omega

theorem rep_surj (m : ℕ) : Function.Surjective (rep m) := by
  intro y
  by_cases h : y ≤ m
  · exact ⟨y, by simp [rep, h]⟩
  · exact ⟨y + 1, by simp only [rep]; split_ifs <;> omega⟩

theorem rep_apply_of_le {m x : ℕ} (h : x ≤ m) : rep m x = x := by simp [rep, h]

theorem rep_apply_of_lt {m x : ℕ} (h : m < x) : rep m x = x - 1 := by
  simp only [rep]; split_ifs <;> omega

/-- A monotone surjection steps up somewhere beyond any bound. -/
theorem exists_step {k : F} (hk : Monotone k) (hs : Function.Surjective k) (m : ℕ) :
    ∃ x, m < x ∧ k (x - 1) ≠ k x := by
  by_contra h
  push_neg at h
  have hconst : ∀ x, m ≤ x → k x = k m := by
    intro x hx
    induction x, hx using Nat.le_induction with
    | base => rfl
    | succ x hx ih => rw [← ih, ← h (x + 1) (by omega)]; rfl
  obtain ⟨y, hy⟩ := hs (k m + 1)
  by_cases hym : m ≤ y
  · rw [hconst y hym] at hy; omega
  · have := hk (show y ≤ m by omega); omega

/-- `k` raised by one beyond `m`: monotone when `k` is. -/
def raise (k : F) (m : ℕ) : F := fun x => if m < x then k x + 1 else k x

theorem raise_mono {k : F} (hk : Monotone k) (m : ℕ) : Monotone (raise k m) := by
  intro x y hxy
  have := hk hxy
  simp only [raise]
  split_ifs <;> omega

theorem raise_apply_of_le {k : F} {m x : ℕ} (h : x ≤ m) : raise k m x = k x := by
  simp [raise, show ¬ m < x by omega]

/-! ### Boolean Completeness in the monotone parts

Parts 2 to 5 share a witness. Take `h = pred` and `g = step n`, which is `pred` up to
`n + 1` and then one further behind, so that `g (n + 2) = n`. For a bound `n` of the
pinning set with `n` even and at least `2`, the two agree there; but a monotone arrow
agreeing with `pred` up to `n + 2` sends an even number `≤ n + 2` to `0` or to an odd
number, and one beyond `n + 2` to at least `n + 1`, so never an even to `n`. -/

/-- The predecessor, truncated at `0`. -/
def pred : F := fun x => x - 1

/-- `pred` up to `n + 1`, then one further behind. -/
def step (n : ℕ) : F := fun x => if x ≤ n + 1 then x - 1 else x - 2

theorem pred_mono : Monotone pred := fun _ _ h => Nat.sub_le_sub_right h 1

theorem pred_surj : Function.Surjective pred := fun y => ⟨y + 1, by show y + 1 - 1 = y; omega⟩

theorem step_mono (n : ℕ) : Monotone (step n) := by
  intro x y hxy
  simp only [step]
  split_ifs <;> omega

theorem step_surj (n : ℕ) : Function.Surjective (step n) := by
  intro y
  by_cases hy : y ≤ n
  · exact ⟨y + 1, by simp only [step]; split_ifs <;> omega⟩
  · exact ⟨y + 2, by simp only [step]; split_ifs <;> omega⟩

/-- The Boolean Completeness witness in a monoid of monotone functions containing `pred`
and every `step n`, on the even numbers. -/
theorem bcWitness_mono (S : Submonoid F) (hmono : ∀ f ∈ S, Monotone f) (hpred : pred ∈ S)
    (hstep : ∀ n, step n ∈ S) : BCWitness S {m | Even m} := by
  intro N hN
  obtain ⟨b, hb⟩ := exists_bound hN
  refine ⟨{x | x ≤ 2 * b + 4}, Set.finite_le_nat _, ⟨pred, hpred⟩, ⟨step (2 * b + 2), hstep _⟩,
    fun x hx => ?_, 2 * b + 4, ⟨b + 2, by omega⟩, fun g' hg' m' hm' => ?_⟩
  · have := hb x hx
    show step (2 * b + 2) x = pred x
    simp only [step, pred]; split_ifs <;> omega
  · show (g' : F) m' ≠ step (2 * b + 2) (2 * b + 4)
    have hval : step (2 * b + 2) (2 * b + 4) = 2 * b + 2 := by simp only [step]; split_ifs <;> omega
    rw [hval]
    obtain ⟨r, hr⟩ := hm'
    by_cases hle : m' ≤ 2 * b + 4
    · have e : (g' : F) m' = m' - 1 := hg' m' hle
      rw [e]; omega
    · have e : (g' : F) (2 * b + 4) = 2 * b + 3 := (hg' (2 * b + 4) (Nat.le_refl _)).trans (by show 2 * b + 4 - 1 = 2 * b + 3; omega)
      have := hmono _ g'.2 (show 2 * b + 4 ≤ m' by omega)
      rw [e] at this; omega

/-- **Boolean Completeness at `e → t` fails in a monoid of monotone functions containing
`pred` and every `step n`**, on the haecceities of the even numbers. -/
theorem not_bc_of_mono (S : Submonoid F) (hmono : ∀ f ∈ S, Monotone f) (hpred : pred ∈ S)
    (hstep : ∀ n, step n ∈ S) :
    ¬ (model S).HoldsSentence (P.BooleanCompleteness.quoted (.arr .e .t)) :=
  not_bc_of S _ (bcWitness_mono S hmono hpred hstep)

/-! ### Part 2: the monotone surjections -/

/-- The monoid of monotone surjections of `ℕ`. -/
def monoSurj : Submonoid F where
  carrier := {f | Monotone f ∧ Function.Surjective f}
  one_mem' := ⟨monotone_id, Function.surjective_id⟩
  mul_mem' {f g} hf hg := ⟨hf.1.comp hg.1, hf.2.comp hg.2⟩

namespace MonoSurj

/-- Halving: a monotone surjection that is not injective. -/
def half : monoSurj := ⟨fun n => n / 2, fun _ _ h => Nat.div_le_div_right h, fun y => ⟨2 * y, by show 2 * y / 2 = y; omega⟩⟩

theorem half_not_injective : ¬ Function.Injective fun n : ℕ => half • n := by
  intro h
  have := @h 0 1 (by simp [smul_eq, half])
  exact absurd this (by decide)

/-- Every monotone surjection is free: compose with `rep m` beyond a bound of the finite
set. -/
theorem free (k : monoSurj) : Free k := by
  intro X hX
  obtain ⟨m, hm⟩ := exists_bound hX
  obtain ⟨x, hmx, hstep⟩ := exists_step k.2.1 k.2.2 m
  refine ⟨k * ⟨rep m, rep_mono m, rep_surj m⟩, fun y hy => ?_, x, ?_⟩
  · show (k : F) (rep m y) = (k : F) y
    rw [rep_apply_of_le (hm y hy)]
  · show (k : F) (rep m x) ≠ (k : F) x
    rw [rep_apply_of_lt hmx]
    exact hstep

theorem not_nd_e : ¬ (model monoSurj).HoldsSentence (Sentence.nd .e) :=
  not_nd_e_of_not_injective monoSurj half half_not_injective

theorem bf (σ : Ty) : (model monoSurj).HoldsSentence (Sentence.bf σ) :=
  bf_of_surjective monoSurj (fun k => k.2.2) σ

theorem not_actuality : ¬ (model monoSurj).HoldsSentence P.Actuality.quoted :=
  not_actuality_of_free monoSurj (free 1)

theorem atomlessness : (model monoSurj).HoldsSentence P.Atomlessness.quoted :=
  atomlessness_of_free monoSurj free

theorem not_atomicityT : ¬ (model monoSurj).HoldsSentence P.AtomicityT.quoted :=
  not_atomicityT_of_free monoSurj (p := Set.univ) ⟨∅, Set.finite_empty, PinnedO.univ _ ∅⟩
    (fun h => Set.notMem_empty (tup (1 : monoSurj)) (h ▸ Set.mem_univ _)) (fun k _ => free k)

theorem not_bc : ¬ (model monoSurj).HoldsSentence (P.BooleanCompleteness.quoted (.arr .e .t)) :=
  not_bc_of_mono monoSurj (fun _ h => h.1) ⟨pred_mono, pred_surj⟩ fun n => ⟨step_mono n, step_surj n⟩

end MonoSurj

/-! ### Part 3: the monotone functions -/

/-- The monoid of monotone functions on `ℕ`. -/
def mono : Submonoid F where
  carrier := {f | Monotone f}
  one_mem' := monotone_id
  mul_mem' {f g} hf hg := hf.comp hg

namespace Mono

/-- The constant `0`. -/
def zero : mono := ⟨fun _ => 0, monotone_const⟩

theorem zero_not_injective : ¬ Function.Injective fun n : ℕ => zero • n := by
  intro h
  have := @h 0 1 rfl
  exact absurd this (by decide)

/-- Every monotone function is free: raise it beyond a bound of the finite set. -/
theorem free (k : mono) : Free k := by
  intro X hX
  obtain ⟨m, hm⟩ := exists_bound hX
  refine ⟨⟨raise k m, raise_mono k.2 m⟩, fun y hy => ?_, m + 1, ?_⟩
  · show raise k m y = (k : F) y
    exact raise_apply_of_le (hm y hy)
  · show raise k m (m + 1) ≠ (k : F) (m + 1)
    simp [raise]

theorem not_nd_e : ¬ (model mono).HoldsSentence (Sentence.nd .e) :=
  not_nd_e_of_not_injective mono zero zero_not_injective

/-- `BF` at `e` fails, on the property "positive" at `0`: a monotone function sending `0`
somewhere positive sends everything there, but the successor does so and `0` is not
positive. -/
theorem bfWitness : BFWitness mono (· ≠ 0) (· ≠ 0) 0 :=
  ⟨fun k y h => by
      have := k.2 (Nat.zero_le y)
      simp only [smul_eq] at h ⊢
      omega,
    ⟨⟨fun n => n + 1, fun _ _ h => Nat.succ_le_succ h⟩, by simp [smul_eq], 0, by simp⟩⟩

theorem not_bf_e : ¬ (model mono).HoldsSentence (Sentence.bf .e) :=
  MonoidModel.not_bf_e mono (· ≠ 0) (· ≠ 0) 0 bfWitness.1 bfWitness.2

theorem not_actuality : ¬ (model mono).HoldsSentence P.Actuality.quoted :=
  not_actuality_of_free mono (free 1)

theorem atomlessness : (model mono).HoldsSentence P.Atomlessness.quoted :=
  atomlessness_of_free mono free

theorem not_atomicityT : ¬ (model mono).HoldsSentence P.AtomicityT.quoted :=
  not_atomicityT_of_free mono (p := Set.univ) ⟨∅, Set.finite_empty, PinnedO.univ _ ∅⟩
    (fun h => Set.notMem_empty (tup (1 : mono)) (h ▸ Set.mem_univ _)) (fun k _ => free k)

theorem not_bc : ¬ (model mono).HoldsSentence (P.BooleanCompleteness.quoted (.arr .e .t)) :=
  not_bc_of_mono mono (fun _ h => h) pred_mono step_mono

end Mono

/-! ### Part 4: monotone functions collapsing `0` and `1`, and the identity -/

/-- The monoid of monotone functions `f` with `f 0 = f 1`, together with the identity. -/
def mono01 : Submonoid F where
  carrier := {f | Monotone f ∧ (f 0 = f 1 ∨ f = id)}
  one_mem' := ⟨monotone_id, Or.inr rfl⟩
  mul_mem' {f g} hf hg := ⟨hf.1.comp hg.1, by
    rcases hg.2 with hg2 | rfl
    · left; show f (g 0) = f (g 1); rw [hg2]
    · rcases hf.2 with hf2 | rfl
      · left; exact hf2
      · right; rfl⟩

namespace Mono01

def zero : mono01 := ⟨fun _ => 0, monotone_const, Or.inl rfl⟩

theorem zero_not_injective : ¬ Function.Injective fun n : ℕ => zero • n := by
  intro h
  have := @h 0 1 rfl
  exact absurd this (by decide)

/-- A collapsing arrow is free: raise it beyond a bound at least `1`, which keeps `0` and
`1` collapsed. -/
theorem free_of_collapse (k : mono01) (hk : (k : F) 0 = (k : F) 1) : Free k := by
  intro X hX
  obtain ⟨m, hm⟩ := exists_bound hX
  have hmem : raise k (max m 1) ∈ mono01 := ⟨raise_mono k.2.1 _, Or.inl (by
    show raise k (max m 1) 0 = raise k (max m 1) 1
    rw [raise_apply_of_le (by omega), raise_apply_of_le (by omega)]
    exact hk)⟩
  refine ⟨⟨raise k (max m 1), hmem⟩, fun y hy => ?_, max m 1 + 1, ?_⟩
  · show raise k (max m 1) y = (k : F) y
    exact raise_apply_of_le (le_trans (hm y hy) (le_max_left _ _))
  · show raise k (max m 1) (max m 1 + 1) ≠ (k : F) (max m 1 + 1)
    simp [raise]

/-- The identity is the only arrow fixing `0` and `1`. -/
theorem eq_one_of_fix (g : mono01) (h0 : (g : F) 0 = 0) (h1 : (g : F) 1 = 1) : g = 1 := by
  rcases g.2.2 with h | h
  · rw [h0, h1] at h; exact absurd h (by decide)
  · exact Subtype.ext h

theorem not_nd_e : ¬ (model mono01).HoldsSentence (Sentence.nd .e) :=
  not_nd_e_of_not_injective mono01 zero zero_not_injective

/-- `BF` at `e` fails, on "positive" at `0`, with `λn. max n 1` as the arrow. -/
theorem bfWitness : BFWitness mono01 (· ≠ 0) (· ≠ 0) 0 :=
  ⟨fun k y h => by
      have := k.2.1 (Nat.zero_le y)
      simp only [smul_eq] at h ⊢
      omega,
    ⟨⟨fun n => max n 1, fun _ _ h => max_le_max_right 1 h, Or.inl rfl⟩, by simp [smul_eq], 0, by simp⟩⟩

theorem not_bf_e : ¬ (model mono01).HoldsSentence (Sentence.bf .e) :=
  MonoidModel.not_bf_e mono01 (· ≠ 0) (· ≠ 0) 0 bfWitness.1 bfWitness.2

/-- **Actuality holds**: `{1}` is pinned down by `{0, 1}`. -/
theorem onePinned : OnePinned mono01 :=
  ⟨{0, 1}, Set.toFinite _, fun g hg => eq_one_of_fix g (hg 0 (by simp)) (hg 1 (by simp))⟩

theorem actuality : (model mono01).HoldsSentence P.Actuality.quoted :=
  actuality_of_pinned_one mono01 ⟨{0, 1}, Set.toFinite _, singleton_pinned_of ({0, 1} : Set ℕ) 1 fun g hg =>
    eq_one_of_fix g (hg 0 (by simp)) (hg 1 (by simp))⟩

/-- The collapsing arrows, a proposition pinned down by `{0, 1}`. -/
abbrev collapse : Prop' mono01 := ofPred fun g : mono01 => (g : F) 0 = (g : F) 1

theorem collapse_pinned : (model mono01).PinnedO (.rel .t) ({0, 1} : Set ℕ) collapse :=
  ofPred_pinned _ _ fun g g' ha => by
    have h0 : (g : F) 0 = (g' : F) 0 := ha 0 (by simp)
    have h1 : (g : F) 1 = (g' : F) 1 := ha 1 (by simp)
    rw [h0, h1]

/-- **Atomicity at `t` fails**: the collapsing arrows are a nonzero proposition all of
whose arrows are free. -/
theorem not_atomicityT : ¬ (model mono01).HoldsSentence P.AtomicityT.quoted :=
  not_atomicityT_of_free mono01 (p := collapse) ⟨{0, 1}, Set.toFinite _, collapse_pinned⟩
    (fun h => Set.notMem_empty (tup zero) (h ▸ (mem_ofPred.2 rfl))) (fun k hk => free_of_collapse k (mem_ofPred.1 hk))

theorem not_bc : ¬ (model mono01).HoldsSentence (P.BooleanCompleteness.quoted (.arr .e .t)) :=
  not_bc_of_mono mono01 (fun _ h => h.1) ⟨pred_mono, Or.inl rfl⟩ fun n => ⟨step_mono n, Or.inl rfl⟩

end Mono01

/-! ### Part 5: the surjective ones among them -/

/-- The monoid of monotone surjections `f` with `f 0 = f 1`, together with the identity. -/
def monoSurj01 : Submonoid F where
  carrier := {f | Monotone f ∧ Function.Surjective f ∧ (f 0 = f 1 ∨ f = id)}
  one_mem' := ⟨monotone_id, Function.surjective_id, Or.inr rfl⟩
  mul_mem' {f g} hf hg := ⟨hf.1.comp hg.1, hf.2.1.comp hg.2.1, by
    rcases hg.2.2 with hg2 | rfl
    · left; show f (g 0) = f (g 1); rw [hg2]
    · rcases hf.2.2 with hf2 | rfl
      · left; exact hf2
      · right; rfl⟩

namespace MonoSurj01

def half : monoSurj01 :=
  ⟨fun n => n / 2, fun _ _ h => Nat.div_le_div_right h, fun y => ⟨2 * y, by show 2 * y / 2 = y; omega⟩, Or.inl rfl⟩

theorem half_not_injective : ¬ Function.Injective fun n : ℕ => half • n := by
  intro h
  have := @h 0 1 (by simp [smul_eq, half])
  exact absurd this (by decide)

theorem free_of_collapse (k : monoSurj01) (hk : (k : F) 0 = (k : F) 1) : Free k := by
  intro X hX
  obtain ⟨m, hm⟩ := exists_bound hX
  obtain ⟨x, hmx, hstep⟩ := exists_step k.2.1 k.2.2.1 (max m 1)
  have hmem : (k : F) ∘ rep (max m 1) ∈ monoSurj01 :=
    ⟨k.2.1.comp (rep_mono _), k.2.2.1.comp (rep_surj _), Or.inl (by
      show (k : F) (rep (max m 1) 0) = (k : F) (rep (max m 1) 1)
      rw [rep_apply_of_le (by omega), rep_apply_of_le (by omega)]
      exact hk)⟩
  refine ⟨⟨(k : F) ∘ rep (max m 1), hmem⟩, fun y hy => ?_, x, ?_⟩
  · show (k : F) (rep (max m 1) y) = (k : F) y
    rw [rep_apply_of_le (le_trans (hm y hy) (le_max_left _ _))]
  · show (k : F) (rep (max m 1) x) ≠ (k : F) x
    rw [rep_apply_of_lt hmx]
    exact hstep

theorem eq_one_of_fix (g : monoSurj01) (h0 : (g : F) 0 = 0) (h1 : (g : F) 1 = 1) : g = 1 := by
  rcases g.2.2.2 with h | h
  · rw [h0, h1] at h; exact absurd h (by decide)
  · exact Subtype.ext h

theorem not_nd_e : ¬ (model monoSurj01).HoldsSentence (Sentence.nd .e) :=
  not_nd_e_of_not_injective monoSurj01 half half_not_injective

theorem bf (σ : Ty) : (model monoSurj01).HoldsSentence (Sentence.bf σ) :=
  bf_of_surjective monoSurj01 (fun k => k.2.2.1) σ

theorem onePinned : OnePinned monoSurj01 :=
  ⟨{0, 1}, Set.toFinite _, fun g hg => eq_one_of_fix g (hg 0 (by simp)) (hg 1 (by simp))⟩

theorem actuality : (model monoSurj01).HoldsSentence P.Actuality.quoted :=
  actuality_of_pinned_one monoSurj01 ⟨{0, 1}, Set.toFinite _, singleton_pinned_of ({0, 1} : Set ℕ) 1 fun g hg =>
    eq_one_of_fix g (hg 0 (by simp)) (hg 1 (by simp))⟩

abbrev collapse : Prop' monoSurj01 := ofPred fun g : monoSurj01 => (g : F) 0 = (g : F) 1

theorem collapse_pinned : (model monoSurj01).PinnedO (.rel .t) ({0, 1} : Set ℕ) collapse :=
  ofPred_pinned _ _ fun g g' ha => by
    have h0 : (g : F) 0 = (g' : F) 0 := ha 0 (by simp)
    have h1 : (g : F) 1 = (g' : F) 1 := ha 1 (by simp)
    rw [h0, h1]

theorem not_atomicityT : ¬ (model monoSurj01).HoldsSentence P.AtomicityT.quoted :=
  not_atomicityT_of_free monoSurj01 (p := collapse) ⟨{0, 1}, Set.toFinite _, collapse_pinned⟩
    (fun h => Set.notMem_empty (tup half) (h ▸ (mem_ofPred.2 rfl))) (fun k hk => free_of_collapse k (mem_ofPred.1 hk))

theorem not_bc : ¬ (model monoSurj01).HoldsSentence (P.BooleanCompleteness.quoted (.arr .e .t)) :=
  not_bc_of_mono monoSurj01 (fun _ h => h.1) ⟨pred_mono, pred_surj, Or.inl rfl⟩
    fun n => ⟨step_mono n, step_surj n, Or.inl rfl⟩

end MonoSurj01

/-! ### Part 6: the identity and the truncations `gₙ` -/

/-- The truncation at `n`. -/
def trunc (n : ℕ) : F := fun m => min m n

/-- The monoid of the identity and the truncations. -/
def truncs : Submonoid F where
  carrier := {f | f = id ∨ ∃ n, f = trunc n}
  one_mem' := Or.inl rfl
  mul_mem' {f g} hf hg := by
    rcases hf with rfl | ⟨a, rfl⟩
    · exact hg
    · rcases hg with rfl | ⟨b, rfl⟩
      · exact Or.inr ⟨a, rfl⟩
      · exact Or.inr ⟨min a b, funext fun m => by
          show min (min m b) a = min m (min a b)
          omega⟩

namespace Truncs

/-- `gₙ`, as an element of the monoid. -/
def g (n : ℕ) : truncs := ⟨trunc n, Or.inr ⟨n, rfl⟩⟩

theorem g_apply (n m : ℕ) : (g n : F) m = min m n := rfl

theorem g_zero_not_injective : ¬ Function.Injective fun n : ℕ => g 0 • n := by
  intro h
  have := @h 0 1 rfl
  exact absurd this (by decide)

/-- The identity is free: `gₘ` agrees with it below `m`. -/
theorem free_one : Free (1 : truncs) := by
  intro X hX
  obtain ⟨m, hm⟩ := exists_bound hX
  refine ⟨g m, fun y hy => ?_, m + 1, ?_⟩
  · show min y m = y
    exact min_eq_left (hm y hy)
  · show min (m + 1) m ≠ m + 1
    omega

/-- `{gₙ}` is pinned down by `{n, n + 1}`. -/
theorem eq_g_of_agree (n : ℕ) (h : truncs) (hh : ∀ x ∈ ({n, n + 1} : Set ℕ), h • x = g n • x) : h = g n := by
  have h1 : (h : F) n = n := (hh n (by simp)).trans (by show min n n = n; omega)
  have h2 : (h : F) (n + 1) = n := (hh (n + 1) (by simp)).trans (by show min (n + 1) n = n; omega)
  rcases h.2 with e | ⟨j, e⟩
  · exfalso
    have : (h : F) (n + 1) = n + 1 := by rw [e]; rfl
    omega
  · apply Subtype.ext
    rw [e]
    have hj : j = n := by
      have := h2; rw [e] at this
      change min (n + 1) j = n at this
      omega
    rw [hj]; rfl

theorem g_pinned (n : ℕ) : (model truncs).PinnedO (.rel .t) ({n, n + 1} : Set ℕ) ({tup (g n)} : Prop' truncs) :=
  singleton_pinned_of _ _ (eq_g_of_agree n)

theorem not_nd_e : ¬ (model truncs).HoldsSentence (Sentence.nd .e) :=
  not_nd_e_of_not_injective truncs (g 0) g_zero_not_injective

/-- `BF` at `e` fails: an arrow sending `1` to `0` sends everything to `0`, but `g₀` does
so and `1` is not `0`. -/
theorem bfWitness : BFWitness truncs (· = 0) (· = 0) 1 :=
  ⟨fun k y h => by
      rcases k.2 with e | ⟨j, e⟩
      · exfalso; simp only [smul_eq] at h; rw [e] at h; exact absurd h (by decide)
      · simp only [smul_eq] at h ⊢; rw [e] at h ⊢; change min 1 j = 0 at h; show min y j = 0; omega,
    ⟨g 0, rfl, 1, by decide⟩⟩

theorem not_bf_e : ¬ (model truncs).HoldsSentence (Sentence.bf .e) :=
  MonoidModel.not_bf_e truncs (· = 0) (· = 0) 1 bfWitness.1 bfWitness.2

theorem not_actuality : ¬ (model truncs).HoldsSentence P.Actuality.quoted :=
  not_actuality_of_free truncs free_one

/-- **Atomicity at `t` holds**: every nonzero proposition contains some `gₙ`, whose
singleton is finitely pinned; a proposition containing only the identity would have to
contain the `gₘ` beyond its pinning set. -/
theorem atomicityT : (model truncs).HoldsSentence P.AtomicityT.quoted := by
  apply atomicityT_of_singletons
  rintro p ⟨X, hX, hp⟩ hne
  obtain ⟨t, ht⟩ := (Set.eq_empty_or_nonempty _).resolve_left hne
  rw [tuple_eq t] at ht
  rcases (arrow t.2.2).2 with e | ⟨n, e⟩
  · -- the identity: the `gₘ` beyond the pinning set is in `p` too
    obtain ⟨m, hm⟩ := exists_bound hX
    refine ⟨g m, ?_, {m, m + 1}, Set.toFinite _, g_pinned m⟩
    have hid : arrow t.2.2 = 1 := Subtype.ext e
    rw [hid] at ht
    exact (mem_iff_of_pinned hp fun y hy => by show min y m = y; exact min_eq_left (hm y hy)).2 ht
  · refine ⟨g n, ?_, {n, n + 1}, Set.toFinite _, g_pinned n⟩
    have : arrow t.2.2 = g n := Subtype.ext e
    rw [this] at ht
    exact ht

/-- **Boolean Completeness at `e → t` fails**, on the haecceities of all numbers: the
identity agrees with `gₙ` up to a bound `n` of the pinning set and sends `n + 1` to
itself, but the only arrow agreeing with `gₙ` at `n + 1` is `gₙ`, which sends nothing
beyond `n`. -/
theorem bcWitness : BCWitness truncs Set.univ := by
  intro N hN
  obtain ⟨n, hn⟩ := exists_bound hN
  refine ⟨{n + 1}, Set.finite_singleton _, g n, 1, fun x hx => ?_, n + 1, Set.mem_univ _,
    fun g' hg' m' _ => ?_⟩
  · show x = min x n
    have := hn x hx; omega
  · have h1 : (g' : F) (n + 1) = n := (hg' (n + 1) rfl).trans (by show min (n + 1) n = n; omega)
    show (g' : F) m' ≠ n + 1
    rcases g'.2 with e | ⟨j, e⟩
    · rw [e] at h1; exact absurd h1 (by show ¬ n + 1 = n; omega)
    · rw [e] at h1 ⊢
      change min (n + 1) j = n at h1
      show min m' j ≠ n + 1
      omega

theorem not_bc : ¬ (model truncs).HoldsSentence (P.BooleanCompleteness.quoted (.arr .e .t)) :=
  not_bc_of truncs _ bcWitness

/-- The monoid's side of Atomicity: a set of members pinned down by a finite set contains,
with the identity, the `gₘ` beyond that set; and every `{gₙ}` is pinned. -/
theorem singletons : Singletons truncs := by
  rintro P ⟨N, hN, hP⟩ k hk
  rcases k.2 with e | ⟨n, e⟩
  · obtain ⟨m, hm⟩ := exists_bound hN
    have hk1 : k = 1 := Subtype.ext e
    refine ⟨g m, (hP _ _ fun y hy => ?_).2 hk, {m, m + 1}, Set.toFinite _, eq_g_of_agree m⟩
    rw [hk1]; show min y m = y; exact min_eq_left (hm y hy)
  · have : k = g n := Subtype.ext e
    exact ⟨k, hk, {n, n + 1}, Set.toFinite _, this ▸ eq_g_of_agree n⟩

end Truncs

/-! ### Part 7: the roundings `fₙ` to multiples of powers of `2` -/

/-- Rounding down to a multiple of `2 ^ j`: the paper's `f_{2^j}`. -/
def round (j : ℕ) : F := fun m => 2 ^ j * (m / 2 ^ j)

theorem round_apply (j m : ℕ) : round j m = 2 ^ j * (m / 2 ^ j) := rfl

theorem round_zero : round 0 = id := funext fun m => by simp [round]

/-- `f_a ∘ f_b = f_{max a b}`. -/
theorem round_comp (a b : ℕ) : round a ∘ round b = round (max a b) := by
  funext m
  rcases le_total a b with hab | hba
  · rw [max_eq_right hab]
    show 2 ^ a * (2 ^ b * (m / 2 ^ b) / 2 ^ a) = 2 ^ b * (m / 2 ^ b)
    have e : 2 ^ b = 2 ^ a * 2 ^ (b - a) := by rw [← pow_add, Nat.add_sub_cancel' hab]
    rw [e, mul_assoc, Nat.mul_div_cancel_left _ (Nat.two_pow_pos a)]
  · rw [max_eq_left hba]
    show 2 ^ a * (2 ^ b * (m / 2 ^ b) / 2 ^ a) = 2 ^ a * (m / 2 ^ a)
    have e : 2 ^ a = 2 ^ b * 2 ^ (a - b) := by rw [← pow_add, Nat.add_sub_cancel' hba]
    rw [e, Nat.mul_div_mul_left _ _ (Nat.two_pow_pos b), Nat.div_div_eq_div_mul]

/-- The monoid of roundings. -/
def pow2 : Submonoid F where
  carrier := {f | ∃ j, f = round j}
  one_mem' := ⟨0, round_zero.symm⟩
  mul_mem' {f g} hf hg := by
    obtain ⟨a, rfl⟩ := hf
    obtain ⟨b, rfl⟩ := hg
    exact ⟨max a b, by show round a ∘ round b = round (max a b); exact round_comp a b⟩

namespace Pow2

/-- `f_{2^j}`, as an element of the monoid. -/
def f (j : ℕ) : pow2 := ⟨round j, ⟨j, rfl⟩⟩

theorem f_apply (j m : ℕ) : (f j : F) m = 2 ^ j * (m / 2 ^ j) := rfl

theorem f_one_not_injective : ¬ Function.Injective fun n : ℕ => f 1 • n := by
  intro h
  have := @h 0 1 rfl
  exact absurd this (by decide)

/-- An arrow sending `1` to `0` is `f_{2^j}` with `j ≥ 1`, so sends everything to an even
number. -/
theorem even_of_one_eq_zero (k : pow2) (hk : (k : F) 1 = 0) (y : ℕ) : Even ((k : F) y) := by
  obtain ⟨j, e⟩ := k.2
  rw [e] at hk ⊢
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := by
    refine ⟨j - 1, ?_⟩
    rcases j with _ | j
    · simp [round] at hk
    · rfl
  exact ⟨2 ^ i * (y / 2 ^ (i + 1)), by
    rw [round_apply, pow_succ, Nat.mul_assoc, Nat.two_mul, Nat.mul_add]⟩

/-- `{f_{2^j}}` is pinned down by `{2 ^ j - 1, 2 ^ j}`. -/
theorem eq_f_of_agree (j : ℕ) (h : pow2) (hh : ∀ x ∈ ({2 ^ j - 1, 2 ^ j} : Set ℕ), h • x = f j • x) :
    h = f j := by
  have h1 : (h : F) (2 ^ j) = 2 ^ j := (hh (2 ^ j) (by simp)).trans (by
    show 2 ^ j * (2 ^ j / 2 ^ j) = 2 ^ j
    rw [Nat.div_self (Nat.two_pow_pos j), mul_one])
  have h2 : (h : F) (2 ^ j - 1) = 0 := (hh (2 ^ j - 1) (by simp)).trans (by
    show 2 ^ j * ((2 ^ j - 1) / 2 ^ j) = 0
    rw [Nat.div_eq_of_lt (Nat.sub_one_lt (Nat.two_pow_pos j).ne'), Nat.mul_zero])
  obtain ⟨i, e⟩ := h.2
  rw [e] at h1 h2
  change 2 ^ i * (2 ^ j / 2 ^ i) = 2 ^ j at h1
  change 2 ^ i * ((2 ^ j - 1) / 2 ^ i) = 0 at h2
  have hij : i ≤ j := by
    by_contra hlt
    rw [Nat.div_eq_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) (not_le.1 hlt)), Nat.mul_zero] at h1
    exact (Nat.two_pow_pos j).ne' h1.symm
  have hji : j ≤ i := by
    rcases Nat.mul_eq_zero.1 h2 with h0 | h0
    · exact absurd h0 (Nat.two_pow_pos i).ne'
    · have hlt := (Nat.div_eq_zero_iff.1 h0).resolve_left (Nat.two_pow_pos i).ne'
      have hpos := Nat.two_pow_pos j
      exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).1 (by omega)
  apply Subtype.ext
  rw [e, le_antisymm hij hji]; rfl

theorem f_pinned (j : ℕ) :
    (model pow2).PinnedO (.rel .t) ({2 ^ j - 1, 2 ^ j} : Set ℕ) ({tup (f j)} : Prop' pow2) :=
  singleton_pinned_of _ _ (eq_f_of_agree j)

theorem not_nd_e : ¬ (model pow2).HoldsSentence (Sentence.nd .e) :=
  not_nd_e_of_not_injective pow2 (f 1) f_one_not_injective

/-- `BF` at `e` fails: every arrow sending `1` to `0` sends everything to an even number,
but `f₂` does so and `1` is odd. -/
theorem bfWitness : BFWitness pow2 Even (· = 0) 1 :=
  ⟨fun k y h => even_of_one_eq_zero k h y, ⟨f 1, rfl, 1, Nat.not_even_one⟩⟩

theorem not_bf_e : ¬ (model pow2).HoldsSentence (Sentence.bf .e) :=
  MonoidModel.not_bf_e pow2 Even (· = 0) 1 bfWitness.1 bfWitness.2

theorem one_eq_f : (1 : pow2) = f 0 := Subtype.ext round_zero.symm

theorem onePinned : OnePinned pow2 :=
  ⟨({2 ^ 0 - 1, 2 ^ 0} : Set ℕ), Set.toFinite _, fun g hg => by
    rw [one_eq_f]; exact eq_f_of_agree 0 g fun x hx => by rw [← one_eq_f]; exact hg x hx⟩

theorem singletons : Singletons pow2 := by
  rintro P - k hk
  obtain ⟨j, e⟩ := k.2
  have : k = f j := Subtype.ext e
  exact ⟨k, hk, {2 ^ j - 1, 2 ^ j}, Set.toFinite _, this ▸ eq_f_of_agree j⟩

theorem actuality : (model pow2).HoldsSentence P.Actuality.quoted :=
  actuality_of_pinned_one pow2 ⟨({2 ^ 0 - 1, 2 ^ 0} : Set ℕ), Set.toFinite _, by
    have : (1 : pow2) = f 0 := Subtype.ext round_zero.symm
    rw [this]; exact f_pinned 0⟩

/-- **Atomicity at `t` holds**: every singleton is finitely pinned. -/
theorem atomicityT : (model pow2).HoldsSentence P.AtomicityT.quoted := by
  apply atomicityT_of_singletons
  rintro p - hne
  obtain ⟨t, ht⟩ := (Set.eq_empty_or_nonempty _).resolve_left hne
  rw [tuple_eq t] at ht
  obtain ⟨j, e⟩ := (arrow t.2.2).2
  refine ⟨f j, ?_, {2 ^ j - 1, 2 ^ j}, Set.toFinite _, f_pinned j⟩
  have : arrow t.2.2 = f j := Subtype.ext e
  rw [this] at ht
  exact ht

/-- **Boolean Completeness at `e → t` fails**, on the haecceities of all numbers: for
`2 ^ j` beyond the pinning set, `f_{2^j}` and `f_{2^{j+1}}` agree on it (both are `0`
there), and `f_{2^j}` sends `2 ^ j` to itself; but the only arrow agreeing with
`f_{2^{j+1}}` on `{2^{j+1} - 1, 2^{j+1}}` is `f_{2^{j+1}}`, whose values are multiples of
`2^{j+1}`. -/
theorem bcWitness : BCWitness pow2 Set.univ := by
  intro N hN
  obtain ⟨b, hb⟩ := exists_bound hN
  have hbj : b < 2 ^ b := Nat.lt_two_pow_self
  refine ⟨{2 ^ (b + 1) - 1, 2 ^ (b + 1)}, Set.toFinite _, f (b + 1), f b, fun x hx => ?_, 2 ^ b,
    Set.mem_univ _, fun g' hg' m' _ => ?_⟩
  · have hx := hb x hx
    have h2 : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [pow_succ, Nat.mul_comm]
    show 2 ^ b * (x / 2 ^ b) = 2 ^ (b + 1) * (x / 2 ^ (b + 1))
    rw [Nat.div_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega), Nat.mul_zero, Nat.mul_zero]
  · rw [eq_f_of_agree (b + 1) g' hg']
    show 2 ^ (b + 1) * (m' / 2 ^ (b + 1)) ≠ 2 ^ b * (2 ^ b / 2 ^ b)
    rw [Nat.div_self (Nat.two_pow_pos b), mul_one]
    have h2 : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [pow_succ, Nat.mul_comm]
    rw [h2]
    intro e
    rcases Nat.eq_zero_or_pos (m' / (2 * 2 ^ b)) with h0 | hpos
    · rw [h0, Nat.mul_zero] at e; exact (Nat.two_pow_pos b).ne' e.symm
    · have := Nat.le_mul_of_pos_right (2 * 2 ^ b) hpos
      have := Nat.two_pow_pos b
      omega

theorem not_bc : ¬ (model pow2).HoldsSentence (P.BooleanCompleteness.quoted (.arr .e .t)) :=
  not_bc_of pow2 _ bcWitness

end Pow2

/-! ### Part 8: the shifts `kₙ` -/

/-- The shift by `n`, truncated. -/
def shift (n : ℕ) : F := fun m => m - n

/-- The monoid of shifts. -/
def shifts : Submonoid F where
  carrier := {f | ∃ n, f = shift n}
  one_mem' := ⟨0, funext fun m => by show m = m - 0; omega⟩
  mul_mem' {f g} hf hg := by
    obtain ⟨a, rfl⟩ := hf
    obtain ⟨b, rfl⟩ := hg
    exact ⟨a + b, funext fun m => by show m - b - a = m - (a + b); omega⟩

namespace Shifts

def k (n : ℕ) : shifts := ⟨shift n, ⟨n, rfl⟩⟩

theorem k_one_not_injective : ¬ Function.Injective fun n : ℕ => k 1 • n := by
  intro h
  have := @h 0 1 rfl
  exact absurd this (by decide)

theorem surj (h : shifts) : Function.Surjective fun n : ℕ => h • n := by
  obtain ⟨a, e⟩ := h.2
  intro y
  refine ⟨y + a, ?_⟩
  show (h : F) (y + a) = y
  rw [e]; show y + a - a = y; omega

/-- `{kₙ}` is pinned down by `{n + 1}`. -/
theorem eq_k_of_agree (n : ℕ) (h : shifts) (hh : ∀ x ∈ ({n + 1} : Set ℕ), h • x = k n • x) : h = k n := by
  have h1 : (h : F) (n + 1) = 1 := (hh (n + 1) rfl).trans (by show n + 1 - n = 1; omega)
  obtain ⟨j, e⟩ := h.2
  apply Subtype.ext
  rw [e]
  have hj : j = n := by
    rw [e] at h1; change n + 1 - j = 1 at h1; omega
  rw [hj]; rfl

theorem k_pinned (n : ℕ) : (model shifts).PinnedO (.rel .t) ({n + 1} : Set ℕ) ({tup (k n)} : Prop' shifts) :=
  singleton_pinned_of _ _ (eq_k_of_agree n)

theorem not_nd_e : ¬ (model shifts).HoldsSentence (Sentence.nd .e) :=
  not_nd_e_of_not_injective shifts (k 1) k_one_not_injective

theorem bf (σ : Ty) : (model shifts).HoldsSentence (Sentence.bf σ) :=
  bf_of_surjective shifts surj σ

theorem one_eq_k : (1 : shifts) = k 0 := Subtype.ext (funext fun m => by show m = m - 0; omega)

theorem onePinned : OnePinned shifts :=
  ⟨{1}, Set.finite_singleton _, fun g hg => by
    rw [one_eq_k]; exact eq_k_of_agree 0 g fun x hx => by rw [← one_eq_k]; exact hg x hx⟩

theorem singletons : Singletons shifts := by
  rintro P - h hh
  obtain ⟨n, e⟩ := h.2
  have : h = k n := Subtype.ext e
  exact ⟨h, hh, {n + 1}, Set.finite_singleton _, this ▸ eq_k_of_agree n⟩

theorem actuality : (model shifts).HoldsSentence P.Actuality.quoted :=
  actuality_of_pinned_one shifts ⟨{1}, Set.finite_singleton _, by
    have : (1 : shifts) = k 0 := Subtype.ext (funext fun m => by show m = m - 0; omega)
    rw [this]; exact k_pinned 0⟩

/-- **Atomicity at `t` holds**: every singleton is finitely pinned. -/
theorem atomicityT : (model shifts).HoldsSentence P.AtomicityT.quoted := by
  apply atomicityT_of_singletons
  rintro p - hne
  obtain ⟨t, ht⟩ := (Set.eq_empty_or_nonempty _).resolve_left hne
  rw [tuple_eq t] at ht
  obtain ⟨n, e⟩ := (arrow t.2.2).2
  refine ⟨k n, ?_, {n + 1}, Set.finite_singleton _, k_pinned n⟩
  have : arrow t.2.2 = k n := Subtype.ext e
  rw [this] at ht
  exact ht

/-- **Boolean Completeness at `e → t` fails**, on the haecceities of the even numbers: for
an even `n` bounding the pinning set, `k_{n+1}` and `k_{n+2}` agree on it (both are `0`
there), and `k_{n+2}` sends `n + 4` to `2`; but the only arrow agreeing with `k_{n+1}` at
`n + 2` is `k_{n+1}`, which sends an even number to `0` or to an odd number. -/
theorem bcWitness : BCWitness shifts {m | Even m} := by
  intro N hN
  obtain ⟨b, hb⟩ := exists_bound hN
  refine ⟨{2 * b + 2}, Set.finite_singleton _, k (2 * b + 1), k (2 * b + 2), fun x hx => ?_,
    2 * b + 4, ⟨b + 2, by omega⟩, fun g' hg' m' hm' => ?_⟩
  · have := hb x hx
    show x - (2 * b + 2) = x - (2 * b + 1)
    omega
  · rw [eq_k_of_agree (2 * b + 1) g' hg']
    obtain ⟨r, hr⟩ := hm'
    show m' - (2 * b + 1) ≠ 2 * b + 4 - (2 * b + 2)
    omega

theorem not_bc : ¬ (model shifts).HoldsSentence (P.BooleanCompleteness.quoted (.arr .e .t)) :=
  not_bc_of shifts _ bcWitness

end Shifts

end Classicism.Meta.Intensional.Monoids
