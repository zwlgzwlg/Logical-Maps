import Classicism.Models.Pointed
import Classicism.Models.Monoids

/-!
# Appendix D, Parts 1 to 8 with a point adjoined

The paper's remark after Part 8, for each of the eight monoid models: adjoin a point with
one arrow into it and none back (`Pointed.lean`). At the point every principle the paper
tracks holds; at `ℕ` each is as in the one-object model, except that `ND_e` and
Atomlessness fail in every part. Each verdict at `ℕ` is the `Pointed` lemma at the fact
about the monoid that `Monoids.lean` already proved for the one-object model.

| part | `ND` | `BF` | Actuality | Atomicity (`t`) | BC (`e → t`) | Atomlessness |
| --- | --- | --- | --- | --- | --- | --- |
| 1⁺ | c. false | necessary | c. false | c. false | c. false | fails |
| 2⁺ | c. false | necessary | c. false | c. false | c. false | fails |
| 3⁺ | c. false | c. false | c. false | c. false | c. false | fails |
| 4⁺ | c. false | c. false | necessary | c. false | c. false | fails |
| 5⁺ | c. false | necessary | necessary | c. false | c. false | fails |
| 6⁺ | c. false | c. false | c. false | necessary | c. false | fails |
| 7⁺ | c. false | c. false | necessary | necessary | c. false | fails |
| 8⁺ | c. false | necessary | necessary | necessary | c. false | fails |

"c. false" is false at `ℕ` and true at the point, so `¬P ∧ ◇P`; "necessary" is true at
both, so `□P`. `BF` is at every type where necessary, and at `e` where contingently
false. The rows are the survey's in `Models/README.md`.

Part 1's monoid is the bijections of `ℕ`, as a submonoid of the functions on `ℕ` like the
others, rather than the permutation group of `Permutations.lean`; the arguments are the
same.
-/

namespace Classicism.Meta.Intensional.PointedParts

open CategoryTheory Premodel MonoidModel Pointed Monoids

/-! ### Part 1⁺: the bijections -/

/-- The monoid of bijections of `ℕ`. -/
def bij : Submonoid Monoids.F where
  carrier := {f | Function.Bijective f}
  one_mem' := Function.bijective_id
  mul_mem' hf hg := hf.comp hg

namespace Bij

/-- Every bijection is free: move the image of a point outside the finite set to a fresh
value by a transposition. -/
theorem free (k : bij) : Free k := by
  intro X hX
  obtain ⟨n, hn⟩ := hX.exists_notMem
  obtain ⟨m, hm⟩ := ((hX.image (k : Monoids.F)).union (Set.finite_singleton ((k : Monoids.F) n))).exists_notMem
  refine ⟨⟨⇑(Equiv.swap ((k : Monoids.F) n) m) ∘ (k : Monoids.F), (Equiv.bijective _).comp k.2⟩, fun x hx => ?_, n, ?_⟩
  · show Equiv.swap ((k : Monoids.F) n) m ((k : Monoids.F) x) = (k : Monoids.F) x
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h; exact hn (k.2.1 h ▸ hx)
    · intro h; exact hm (Or.inl ⟨x, hx, h⟩)
  · show Equiv.swap ((k : Monoids.F) n) m ((k : Monoids.F) n) ≠ (k : Monoids.F) n
    rw [Equiv.swap_apply_left]
    exact fun h => hm (Or.inr h)

/-- The Boolean Completeness witness, on the even numbers: the transposition of `n + 1` and
`n + 2` against the identity. -/
theorem bcWitness : BCWitness bij {m | Even m} := by
  intro N hN
  obtain ⟨b, hb⟩ := hN.bddAbove
  refine ⟨{x | x ≤ 2 * b + 3}, Set.finite_le_nat _, 1,
    ⟨⇑(Equiv.swap (2 * b + 3) (2 * b + 4)), Equiv.bijective _⟩,
    fun x hx => ?_, 2 * b + 4, ⟨b + 2, by omega⟩, fun g' hg' m' hm' => ?_⟩
  · have := hb hx
    show Equiv.swap (2 * b + 3) (2 * b + 4) x = x
    exact Equiv.swap_apply_of_ne_of_ne (by omega) (by omega)
  · show (g' : Monoids.F) m' ≠ Equiv.swap (2 * b + 3) (2 * b + 4) (2 * b + 4)
    rw [Equiv.swap_apply_right]
    intro e
    have hfix : (g' : Monoids.F) (2 * b + 3) = 2 * b + 3 := hg' (2 * b + 3) (Nat.le_refl _)
    have := g'.2.1 (e.trans hfix.symm)
    obtain ⟨r, hr⟩ := hm'
    omega

theorem not_actuality : ¬ (Pointed.model bij).HoldsSentence P.Actuality.quoted :=
  not_actuality_of_free bij (free 1)

theorem not_atomicityT : ¬ (Pointed.model bij).HoldsSentence P.AtomicityT.quoted :=
  not_atomicityT_of_free bij (p := ofPred (fun _ => True) False)
    ⟨∅, Set.finite_empty, ofPred_pinned _ _ _ fun _ _ _ => Iff.rfl⟩ (k₀ := 1) (mem_ofPred_N.2 trivial)
    (fun h => mem_ofPred_C.1 h) (fun k _ => free k)

theorem bf (σ : Ty) : (Pointed.model bij).HoldsSentence (Sentence.bf σ) :=
  bf_of_surjective bij (fun k => k.2.2) σ

theorem not_bc : ¬ (Pointed.model bij).HoldsSentence (P.BooleanCompleteness.quoted (.arr .e .t)) :=
  Pointed.not_bc_of bij _ bcWitness

end Bij

/-! ### Part 2⁺: the monotone surjections -/

namespace MonoSurj

theorem not_actuality : ¬ (Pointed.model monoSurj).HoldsSentence P.Actuality.quoted :=
  not_actuality_of_free monoSurj (Monoids.MonoSurj.free 1)

theorem not_atomicityT : ¬ (Pointed.model monoSurj).HoldsSentence P.AtomicityT.quoted :=
  not_atomicityT_of_free monoSurj (p := ofPred (fun _ => True) False)
    ⟨∅, Set.finite_empty, ofPred_pinned _ _ _ fun _ _ _ => Iff.rfl⟩ (k₀ := 1) (mem_ofPred_N.2 trivial)
    (fun h => mem_ofPred_C.1 h) (fun k _ => Monoids.MonoSurj.free k)

theorem bf (σ : Ty) : (Pointed.model monoSurj).HoldsSentence (Sentence.bf σ) :=
  bf_of_surjective monoSurj (fun k => k.2.2) σ

theorem not_bc : ¬ (Pointed.model monoSurj).HoldsSentence (P.BooleanCompleteness.quoted (.arr .e .t)) :=
  Pointed.not_bc_of monoSurj _
    (bcWitness_mono monoSurj (fun _ h => h.1) ⟨pred_mono, pred_surj⟩ fun n => ⟨step_mono n, step_surj n⟩)

end MonoSurj

/-! ### Part 3⁺: the monotone functions -/

namespace Mono

theorem not_actuality : ¬ (Pointed.model mono).HoldsSentence P.Actuality.quoted :=
  not_actuality_of_free mono (Monoids.Mono.free 1)

theorem not_atomicityT : ¬ (Pointed.model mono).HoldsSentence P.AtomicityT.quoted :=
  not_atomicityT_of_free mono (p := ofPred (fun _ => True) False)
    ⟨∅, Set.finite_empty, ofPred_pinned _ _ _ fun _ _ _ => Iff.rfl⟩ (k₀ := 1) (mem_ofPred_N.2 trivial)
    (fun h => mem_ofPred_C.1 h) (fun k _ => Monoids.Mono.free k)

theorem not_bf_e : ¬ (Pointed.model mono).HoldsSentence (Sentence.bf .e) :=
  Pointed.not_bf_e mono _ _ _ Monoids.Mono.bfWitness

theorem not_bc : ¬ (Pointed.model mono).HoldsSentence (P.BooleanCompleteness.quoted (.arr .e .t)) :=
  Pointed.not_bc_of mono _ (bcWitness_mono mono (fun _ h => h) pred_mono step_mono)

end Mono

/-! ### Part 4⁺: monotone, collapsing `0` and `1` unless the identity -/

namespace Mono01

/-- The collapsing members, without `c`. -/
abbrev collapse : Pointed.Prop' mono01 := ofPred (fun g : mono01 => (g : Monoids.F) 0 = (g : Monoids.F) 1) False

theorem collapse_finPinned : FinPinned' collapse :=
  ⟨{0, 1}, Set.toFinite _, ofPred_pinned _ _ _ fun g g' ha => by
    have h0 : (g : Monoids.F) 0 = (g' : Monoids.F) 0 := ha 0 (by simp)
    have h1 : (g : Monoids.F) 1 = (g' : Monoids.F) 1 := ha 1 (by simp)
    rw [h0, h1]⟩

theorem actuality : (Pointed.model mono01).HoldsSentence P.Actuality.quoted :=
  actuality_of_pinned_one mono01 Monoids.Mono01.onePinned

theorem not_atomicityT : ¬ (Pointed.model mono01).HoldsSentence P.AtomicityT.quoted :=
  not_atomicityT_of_free mono01 collapse_finPinned (k₀ := Monoids.Mono01.zero) (mem_ofPred_N.2 rfl)
    (fun h => mem_ofPred_C.1 h) (fun k hk => Monoids.Mono01.free_of_collapse k (mem_ofPred_N.1 hk))

theorem not_bf_e : ¬ (Pointed.model mono01).HoldsSentence (Sentence.bf .e) :=
  Pointed.not_bf_e mono01 _ _ _ Monoids.Mono01.bfWitness

theorem not_bc : ¬ (Pointed.model mono01).HoldsSentence (P.BooleanCompleteness.quoted (.arr .e .t)) :=
  Pointed.not_bc_of mono01 _
    (bcWitness_mono mono01 (fun _ h => h.1) ⟨pred_mono, Or.inl rfl⟩ fun n => ⟨step_mono n, Or.inl rfl⟩)

end Mono01

/-! ### Part 5⁺: the surjective ones among them -/

namespace MonoSurj01

abbrev collapse : Pointed.Prop' monoSurj01 := ofPred (fun g : monoSurj01 => (g : Monoids.F) 0 = (g : Monoids.F) 1) False

theorem collapse_finPinned : FinPinned' collapse :=
  ⟨{0, 1}, Set.toFinite _, ofPred_pinned _ _ _ fun g g' ha => by
    have h0 : (g : Monoids.F) 0 = (g' : Monoids.F) 0 := ha 0 (by simp)
    have h1 : (g : Monoids.F) 1 = (g' : Monoids.F) 1 := ha 1 (by simp)
    rw [h0, h1]⟩

theorem actuality : (Pointed.model monoSurj01).HoldsSentence P.Actuality.quoted :=
  actuality_of_pinned_one monoSurj01 Monoids.MonoSurj01.onePinned

theorem not_atomicityT : ¬ (Pointed.model monoSurj01).HoldsSentence P.AtomicityT.quoted :=
  not_atomicityT_of_free monoSurj01 collapse_finPinned (k₀ := Monoids.MonoSurj01.half) (mem_ofPred_N.2 rfl)
    (fun h => mem_ofPred_C.1 h) (fun k hk => Monoids.MonoSurj01.free_of_collapse k (mem_ofPred_N.1 hk))

theorem bf (σ : Ty) : (Pointed.model monoSurj01).HoldsSentence (Sentence.bf σ) :=
  bf_of_surjective monoSurj01 (fun k => k.2.2.1) σ

theorem not_bc : ¬ (Pointed.model monoSurj01).HoldsSentence (P.BooleanCompleteness.quoted (.arr .e .t)) :=
  Pointed.not_bc_of monoSurj01 _
    (bcWitness_mono monoSurj01 (fun _ h => h.1) ⟨pred_mono, pred_surj, Or.inl rfl⟩
      fun n => ⟨step_mono n, step_surj n, Or.inl rfl⟩)

end MonoSurj01

/-! ### Part 6⁺: the identity and the truncations -/

namespace Truncs

theorem not_actuality : ¬ (Pointed.model truncs).HoldsSentence P.Actuality.quoted :=
  not_actuality_of_free truncs Monoids.Truncs.free_one

theorem atomicityT : (Pointed.model truncs).HoldsSentence P.AtomicityT.quoted :=
  atomicityT_of_singletons truncs Monoids.Truncs.singletons

theorem not_bf_e : ¬ (Pointed.model truncs).HoldsSentence (Sentence.bf .e) :=
  Pointed.not_bf_e truncs _ _ _ Monoids.Truncs.bfWitness

theorem not_bc : ¬ (Pointed.model truncs).HoldsSentence (P.BooleanCompleteness.quoted (.arr .e .t)) :=
  Pointed.not_bc_of truncs _ Monoids.Truncs.bcWitness

end Truncs

/-! ### Part 7⁺: the roundings -/

namespace Pow2

theorem actuality : (Pointed.model pow2).HoldsSentence P.Actuality.quoted :=
  actuality_of_pinned_one pow2 Monoids.Pow2.onePinned

theorem atomicityT : (Pointed.model pow2).HoldsSentence P.AtomicityT.quoted :=
  atomicityT_of_singletons pow2 Monoids.Pow2.singletons

theorem not_bf_e : ¬ (Pointed.model pow2).HoldsSentence (Sentence.bf .e) :=
  Pointed.not_bf_e pow2 _ _ _ Monoids.Pow2.bfWitness

theorem not_bc : ¬ (Pointed.model pow2).HoldsSentence (P.BooleanCompleteness.quoted (.arr .e .t)) :=
  Pointed.not_bc_of pow2 _ Monoids.Pow2.bcWitness

end Pow2

/-! ### Part 8⁺: the shifts -/

namespace Shifts

theorem actuality : (Pointed.model shifts).HoldsSentence P.Actuality.quoted :=
  actuality_of_pinned_one shifts Monoids.Shifts.onePinned

theorem atomicityT : (Pointed.model shifts).HoldsSentence P.AtomicityT.quoted :=
  atomicityT_of_singletons shifts Monoids.Shifts.singletons

theorem bf (σ : Ty) : (Pointed.model shifts).HoldsSentence (Sentence.bf σ) :=
  bf_of_surjective shifts Monoids.Shifts.surj σ

theorem not_bc : ¬ (Pointed.model shifts).HoldsSentence (P.BooleanCompleteness.quoted (.arr .e .t)) :=
  Pointed.not_bc_of shifts _ Monoids.Shifts.bcWitness

end Shifts

end Classicism.Meta.Intensional.PointedParts
