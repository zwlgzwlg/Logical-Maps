import Classicism.Models.Functions

/-!
# `BF` without `□BF`

Classicism, Appendix D, after Part 8: "One particularly interesting result is that we
can have BF without □BF. For this, we can use a two-object model `W₀ = ℕ` and
`W₁ = {0}`, with all functions from `Wᵢ` to `Wⱼ` as arrows." The ideally full model on
that category, based at `W₀`:

- **`BF_σ` holds at `W₀` at every type** (`bf`), "for the same reason that we found it to
  hold in Part 3 above when we considered the monoid of all functions on `ℕ`: for any
  function `f` and finite set `X`, there is a surjection that agrees with `f` on `X`"
  (`FunCat.bf_of_approx`). An arrow into `W₁` is itself surjective.
- **`BF_e` fails at `W₁`, so `□BF_e` fails at `W₀`** (`not_box_bf_e`): at `W₁`, on the
  property `λy. x = y` with `x` the one individual there, `∀y □(x = y)` holds, since
  every arrow sends `x` to its own image; but `□∀y (x = y)` does not, since along an arrow
  into `W₀` there are individuals other than the image of `x`.

The one point is `Unit` here, the paper's `{0}`.
-/

namespace Classicism.Meta.Intensional.ContingentBarcan

open CategoryTheory Premodel FunCat

/-- The category: all functions between the two sets. -/
abbrev cat : FunCat where
  Obj := Two
  X := Two.X
  Arr _ := True
  arr_id _ := trivial
  arr_comp _ _ := trivial

/-- `W₀ = ℕ`, the base. -/
abbrev W₀ : cat.Ob := Two.nat

/-- `W₁`, the point. -/
abbrev W₁ : cat.Ob := Two.pt

theorem ne : ∀ i : cat.Ob, Nonempty (cat.X i)
  | .nat => ⟨(0 : ℕ)⟩
  | .pt => ⟨()⟩

/-- The model, based at `W₀`. -/
noncomputable abbrev model : Premodel Signature.pure cat.Ob := cat.model W₀ ne

theorem model_isModel : model.IsModel := cat.model_isModel W₀ ne

local notation "Mo" => model_isModel

/-- Every arrow out of `W₀` agrees with a surjection on any finite set: into `W₀`, keep
the arrow up to a bound of the set and count up from `0` beyond it; into `W₁`, every
arrow is surjective. -/
theorem approx : ∀ (V : cat.Ob) (k : W₀ ⟶ V) (N : Set ℕ), N.Finite →
    ∃ j : W₀ ⟶ V, (∀ x ∈ N, fn k x = fn j x) ∧ Function.Surjective (fn j)
  | .nat, k, N, hN => by
    obtain ⟨b, hb⟩ := hN.bddAbove
    refine ⟨arr (i := W₀) (j := W₀) (fun x : ℕ => if x ≤ b then (fn k x : ℕ) else x - (b + 1)) trivial,
      fun x hx => ?_, fun (y : ℕ) => ⟨y + (b + 1), ?_⟩⟩
    · have : x ≤ b := hb hx
      show fn k x = if x ≤ b then fn k x else x - (b + 1)
      rw [if_pos this]
    · show (if y + (b + 1) ≤ b then (fn k (y + (b + 1)) : ℕ) else y + (b + 1) - (b + 1)) = y
      have : ¬ y + (b + 1) ≤ b := by omega
      rw [if_neg this]
      exact Nat.add_sub_cancel y (b + 1)
  | .pt, k, _, _ => ⟨k, fun _ _ => rfl, fun _ => ⟨(0 : ℕ), rfl⟩⟩

/-- **`BF_σ` holds at every type.** -/
theorem bf (σ : Ty) : model.HoldsSentence (Sentence.bf σ) :=
  cat.bf_of_approx W₀ ne (fun {V} k N hN => approx V k N hN) σ

/-- `λy. x = y` at `W₁`, `x` its one individual: along an arrow `l`, the image of `x`. -/
abbrev haecPt : Intension model.inner (.arr .e .t) W₁ :=
  {t | t.2.1.1 = fn t.2.2 ()}

theorem haecPt_pinned : model.PinnedO (W := W₁) (.rel (.arr .e .t)) ({()} : Set Unit) haecPt := by
  intro V h i ha
  have hx : fn h () = fn i () := ha () rfl
  simp only [Outer.map_rel]
  ext ⟨U, ⟨y, ⟨⟩⟩, g⟩
  simp only [Intension.mem_map, Set.mem_ofPred_eq]
  show y = fn g (fn h ()) ↔ y = fn g (fn i ())
  rw [hx]

/-- The arrow `W₀ → W₁`. -/
abbrev c : W₀ ⟶ W₁ := arr (i := W₀) (j := W₁) (fun _ => ()) trivial

/-- An arrow `W₁ → W₀`, picking `0`. -/
abbrev pick : W₁ ⟶ W₀ := arr (i := W₁) (j := W₀) (fun _ => (0 : ℕ)) trivial

/-- **`BF_e` fails at `W₁`**, reached from `W₀` along `c`. -/
theorem not_bf_e_at_W₁ : ¬ model.Holds (𝟙 W₀ ≫ c) (Sentence.bf .e) .nil := by
  obtain ⟨X, hX⟩ := Premodel.ideal_pinned_inner cat.De (.arr .e .t) W₁ haecPt
    ⟨({()} : Set Unit), Set.finite_singleton _, haecPt_pinned⟩
  have hX' : model.incl (.arr .e .t) W₁ X = haecPt := hX
  refine model.not_holds_bf_of Mo (𝟙 W₀ ≫ c) X (fun y V l => ?_) pick (1 : ℕ) ?_
  · rw [hX']
    show fn l y = fn l ()
    rfl
  · rw [hX']
    show ¬ (1 : ℕ) = 0
    omega

/-- **`□BF_e` fails at `W₀`.** -/
theorem not_box_bf_e : ¬ model.HoldsSentence (Term.box (Sentence.bf .e)) := by
  intro H
  rw [HoldsSentence, model.holds_box Mo] at H
  exact not_bf_e_at_W₁ (H c)

end Classicism.Meta.Intensional.ContingentBarcan
