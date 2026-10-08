import Classicism.Models.Monoids
import Mathlib.Logic.Equiv.Set
import Mathlib.Logic.Equiv.Nat
import Mathlib.Data.Nat.Nth
import Classicism.Semantics.FullModels

/-!
# The pair-preserving injections and the pair collapses

Dorr's model of 7 October 2026 for the group `finite-support-one-object`: the ideally full
model over the monoid of functions on `ℕ` that either identify `0` with `1` (the
*collapses*) or are injective and map `{0, 1}` onto itself (`pairInjCol`). It is the largest
submonoid of "injective or `f 0 = f 1`" containing every collapse.

- **Vicinity** holds, with witness the proposition `0 ≠ 1`, the injections: from an
  injection `k`, the inverse of `k` on a finite set extends to an injection `j` of the
  monoid, and `j ∘ k` agrees with the identity there (`vicinity`).
- **BF** holds at every type: every arrow agrees on any finite set with a surjective arrow
  (`bf`, by `Premodel.ideal_bf_of_approx`).
- **Atomlessness** holds: every arrow can be changed at a fresh point (`atomlessness`).
- **Rigid Power** fails at `e → t` with `F := ⊤` (`not_rigidPower`).

The perturbations: a collapse is changed by `Function.update` off `{0, 1}`; an injection by
following it with a transposition (`hit`). Finite partial injections extend to permutations
(`exists_perm_extend`).
-/

namespace Classicism.Meta.Intensional.Monoids

open CategoryTheory MonoidModel Premodel

/-- Injective, mapping `{0, 1}` onto itself. -/
def PairInj (f : F) : Prop := Function.Injective f ∧ ((f 0 = 0 ∧ f 1 = 1) ∨ (f 0 = 1 ∧ f 1 = 0))

/-- **The monoid**: the pair-preserving injections and the collapses of `0` with `1`. -/
def pairInjCol : Submonoid F where
  carrier := {f | PairInj f ∨ f 0 = f 1}
  one_mem' := Or.inl ⟨Function.injective_id, Or.inl ⟨rfl, rfl⟩⟩
  mul_mem' {f g} hf hg := by
    show PairInj (f ∘ g) ∨ f (g 0) = f (g 1)
    rcases hg with ⟨hgi, hg01⟩ | hg
    · rcases hf with ⟨hfi, hf01⟩ | hf
      · left
        refine ⟨hfi.comp hgi, ?_⟩
        rcases hg01 with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases hf01 with ⟨c, d⟩ | ⟨c, d⟩ <;>
          simp [Function.comp, a, b, c, d]
      · right
        rcases hg01 with ⟨a, b⟩ | ⟨a, b⟩ <;> simp [a, b, hf]
    · right; rw [hg]

namespace PairInjCol

abbrev K := pairInjCol

theorem fn_mul (g h : K) (n : ℕ) : ((g * h : K) : F) n = (g : F) ((h : F) n) := rfl

/-- An arrow is a pair-preserving injection or a collapse. -/
theorem cases (k : K) : PairInj (k : F) ∨ (k : F) 0 = (k : F) 1 := k.2

/-- An arrow not collapsing the pair is a pair-preserving injection. -/
theorem pairInj_of_ne {k : K} (h : (k : F) 0 ≠ (k : F) 1) : PairInj (k : F) :=
  (cases k).resolve_right h

theorem PairInj.ne {f : F} (h : PairInj f) : f 0 ≠ f 1 := fun e => by
  have := h.1 e; exact absurd this (by decide)

/-- A pair-preserving injection sends `{0, 1}` exactly onto `{0, 1}`. -/
theorem PairInj.mem01_iff {f : F} (h : PairInj f) (x : ℕ) : (f x = 0 ∨ f x = 1) ↔ (x = 0 ∨ x = 1) := by
  constructor
  · intro hx
    rcases h.2 with ⟨a, b⟩ | ⟨a, b⟩ <;> rcases hx with hx | hx
    · exact Or.inl (h.1 (hx.trans a.symm))
    · exact Or.inr (h.1 (hx.trans b.symm))
    · exact Or.inr (h.1 (hx.trans b.symm))
    · exact Or.inl (h.1 (hx.trans a.symm))
  · rintro (rfl | rfl) <;> rcases h.2 with ⟨a, b⟩ | ⟨a, b⟩ <;> simp [a, b]

/-! ### Extending finite partial injections -/

/-- A function injective on a finite set agrees there with a permutation of `ℕ`. -/
theorem exists_perm_extend {D : Set ℕ} (hD : D.Finite) (f : ℕ → ℕ) (hf : Set.InjOn f D) :
    ∃ σ : ℕ ≃ ℕ, ∀ x ∈ D, σ x = f x := by
  classical
  have hE : (f '' D).Finite := hD.image f
  have i1 : Infinite (Dᶜ : Set ℕ) := hD.infinite_compl.to_subtype
  have i2 : Infinite ((f '' D)ᶜ : Set ℕ) := hE.infinite_compl.to_subtype
  let g : (Dᶜ : Set ℕ) ≃ ((f '' D)ᶜ : Set ℕ) :=
    (Nat.Subtype.orderIsoOfNat _).toEquiv.symm.trans (Nat.Subtype.orderIsoOfNat _).toEquiv
  let b : D ≃ (f '' D) := Set.BijOn.equiv f (hf.bijOn_image)
  let σ : ℕ ≃ ℕ := ((Equiv.Set.sumCompl D).symm.trans (Equiv.sumCongr b g)).trans
    (Equiv.Set.sumCompl (f '' D))
  refine ⟨σ, fun x hx => ?_⟩
  simp [σ, Equiv.Set.sumCompl_symm_apply_of_mem hx, b]
  rfl

/-! ### Perturbations -/

/-- **Hitting a value at a fresh point.** Given `N ∋ 0, 1`, a point `x ∉ N` and a value `y`
not taken on `N` (any value, if the arrow is a collapse), some arrow agrees with `k` on `N`
and sends `x` to `y`. -/
theorem hit (k : K) {N : Set ℕ} (h0 : 0 ∈ N) (h1 : 1 ∈ N) {x : ℕ} (hx : x ∉ N) (y : ℕ)
    (hy : (k : F) 0 = (k : F) 1 ∨ ∀ n ∈ N, (k : F) n ≠ y) :
    ∃ k' : K, (∀ n ∈ N, (k' : F) n = (k : F) n) ∧ (k' : F) x = y := by
  classical
  have hx0 : x ≠ 0 := fun e => hx (e ▸ h0)
  have hx1 : x ≠ 1 := fun e => hx (e ▸ h1)
  by_cases hc : (k : F) 0 = (k : F) 1
  · let u : ℕ → ℕ := Function.update (fun n => (k : F) n) x y
    have u0 : u 0 = (k : F) 0 := Function.update_of_ne hx0.symm _ _
    have u1 : u 1 = (k : F) 1 := Function.update_of_ne hx1.symm _ _
    refine ⟨⟨u, Or.inr ?_⟩, fun n hn => ?_, ?_⟩
    · show u 0 = u 1
      rw [u0, u1, hc]
    · exact Function.update_of_ne (fun (e : n = x) => hx (e ▸ hn)) _ _
    · exact Function.update_self _ _ _
  · have hyN := hy.resolve_left hc
    have hk := pairInj_of_ne hc
    let s : F := ⇑(Equiv.swap y ((k : F) x))
    have hfix : ∀ n ∈ N, s ((k : F) n) = (k : F) n := fun n hn =>
      Equiv.swap_apply_of_ne_of_ne (hyN n hn) (fun e => hx (hk.1 e ▸ hn))
    refine ⟨⟨s * (k : F), Or.inl ⟨(Equiv.injective _).comp hk.1, ?_⟩⟩, fun n hn => hfix n hn, ?_⟩
    · show s ((k : F) 0) = 0 ∧ s ((k : F) 1) = 1 ∨ s ((k : F) 0) = 1 ∧ s ((k : F) 1) = 0
      rw [hfix 0 h0, hfix 1 h1]; exact hk.2
    · exact Equiv.swap_apply_right _ _

/-- A point outside a finite set. -/
theorem fresh {S : Set ℕ} (hS : S.Finite) : ∃ x, x ∉ S := hS.exists_notMem

/-- **Every arrow is free**: it can be changed at a point outside any finite set. -/
theorem free (k : K) : Free k := by
  intro X hX
  have hN : (X ∪ {0, 1}).Finite := hX.union (Set.toFinite _)
  obtain ⟨x, hx⟩ := fresh hN
  obtain ⟨y, hy⟩ := fresh ((hN.insert x).image (k : F))
  obtain ⟨k', hk', hx'⟩ := hit k (N := X ∪ {0, 1}) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) hx y
    (Or.inr fun n hn e => hy ⟨n, Or.inr hn, e⟩)
  refine ⟨k', fun n hn => hk' n (Or.inl hn), x, ?_⟩
  show (k' : F) x ≠ (k : F) x
  rw [hx']
  exact fun e => hy ⟨x, Or.inl rfl, e.symm⟩

/-- **Every arrow agrees on a finite set with a surjective one**: a collapse with a surjective
collapse, a pair-preserving injection with a permutation preserving the pair. -/
theorem approx (k : K) {N : Set ℕ} (hN : N.Finite) :
    ∃ j : K, (∀ x ∈ N, (j : F) x = (k : F) x) ∧ Function.Surjective (j : F) := by
  classical
  have hD : (N ∪ {0, 1}).Finite := hN.union (Set.toFinite _)
  by_cases hc : (k : F) 0 = (k : F) 1
  · obtain ⟨B, hB⟩ := exists_bound hD
    let j : ℕ → ℕ := fun x => if x ≤ B then (k : F) x else x - (B + 1)
    have h0 : (0 : ℕ) ≤ B := hB 0 (Or.inr (Or.inl rfl))
    have h1 : (1 : ℕ) ≤ B := hB 1 (Or.inr (Or.inr rfl))
    refine ⟨⟨j, Or.inr ?_⟩, fun x hx => ?_, fun y => ⟨y + (B + 1), ?_⟩⟩
    · show j 0 = j 1
      simp only [j, if_pos h0, if_pos h1, hc]
    · show j x = (k : F) x
      simp only [j, if_pos (hB x (Or.inl hx))]
    · show j (y + (B + 1)) = y
      simp only [j, if_neg (show ¬ (y + (B + 1) ≤ B) by omega)]
      omega
  · have hk := pairInj_of_ne hc
    obtain ⟨σ, hσ⟩ := exists_perm_extend hD (k : F) (hk.1.injOn)
    refine ⟨⟨⇑σ, Or.inl ⟨σ.injective, ?_⟩⟩, fun x hx => hσ x (Or.inl hx), σ.surjective⟩
    show σ 0 = 0 ∧ σ 1 = 1 ∨ σ 0 = 1 ∧ σ 1 = 0
    rw [hσ 0 (Or.inr (Or.inl rfl)), hσ 1 (Or.inr (Or.inr rfl))]
    exact hk.2

/-- **An inverse on a finite set**: for a pair-preserving injection `k` and finite `N`, some
arrow `j` undoes `k` on `N`. -/
theorem inverse {k : K} (hk : PairInj (k : F)) {N : Set ℕ} (hN : N.Finite) :
    ∃ j : K, ∀ x ∈ N, (j : F) ((k : F) x) = x := by
  classical
  have hD : ((k : F) '' (N ∪ {0, 1})).Finite := (hN.union (Set.toFinite _)).image _
  have hinv : ∀ x, Function.invFun (k : F) ((k : F) x) = x := Function.leftInverse_invFun hk.1
  obtain ⟨σ, hσ⟩ := exists_perm_extend hD (Function.invFun (k : F)) (by
    rintro _ ⟨a, -, rfl⟩ _ ⟨b, -, rfl⟩ e
    rw [hinv, hinv] at e; rw [e])
  have hσk : ∀ x ∈ N ∪ {0, 1}, σ ((k : F) x) = x := fun x hx => (hσ _ ⟨x, hx, rfl⟩).trans (hinv x)
  refine ⟨⟨⇑σ, Or.inl ⟨σ.injective, ?_⟩⟩, fun x hx => hσk x (Or.inl hx)⟩
  show σ 0 = 0 ∧ σ 1 = 1 ∨ σ 0 = 1 ∧ σ 1 = 0
  have e0 := hσk 0 (Or.inr (Or.inl rfl))
  have e1 := hσk 1 (Or.inr (Or.inr rfl))
  rcases hk.2 with ⟨a, b⟩ | ⟨a, b⟩
  · rw [a] at e0; rw [b] at e1; exact Or.inl ⟨e0, e1⟩
  · rw [a] at e0; rw [b] at e1; exact Or.inr ⟨e1, e0⟩

end PairInjCol

open PairInjCol in
/-- **Atomlessness**: every arrow is free. -/
theorem pairInjCol_atomlessness : (model pairInjCol).HoldsSentence P.Atomlessness.quoted :=
  atomlessness_of_free pairInjCol free

open PairInjCol in
/-- **BF at every type**, by approximating each arrow on a finite set by a surjective one. -/
theorem pairInjCol_bf (σ : Ty) : (model pairInjCol).HoldsSentence (Sentence.bf σ) :=
  Premodel.ideal_bf_of_approx (natAction pairInjCol) (fun {V} k N hN => by
    obtain ⟨j, hj, hs⟩ := approx (arrow k) hN
    exact ⟨(j : star pairInjCol ⟶ V), fun x hx => (hj x hx).symm, hs⟩) σ

open PairInjCol in
/-- **Vicinity**, with witness the proposition `0 ≠ 1`: from a pair-preserving injection `k`,
an arrow undoing `k` on the pinning set of a truth `q` reaches `q`. -/
theorem pairInjCol_vicinity : (model pairInjCol).HoldsSentence P.Vicinity.quoted := by
  have Mo : (model pairInjCol).IsModel := model_isModel pairInjCol
  rw [Premodel.HoldsSentence]
  unfold P.Vicinity.quoted
  rw [(model pairInjCol).holds_exists Mo]
  obtain ⟨p, hp⟩ := exists_inner (M := pairInjCol)
    (q := ofPred fun g : pairInjCol => (g : F) 0 ≠ (g : F) 1)
    ⟨{0, 1}, Set.toFinite _, ofPred_pinned (M := pairInjCol) _ _ fun (g g' : pairInjCol) ha => by
      have e0 : (g : F) 0 = (g' : F) 0 := ha 0 (Or.inl rfl)
      have e1 : (g : F) 1 = (g' : F) 1 := ha 1 (Or.inr rfl)
      rw [e0, e1]⟩
  refine ⟨p, ?_⟩
  rw [(model pairInjCol).holds_conj Mo, (model pairInjCol).holds_forall Mo]
  refine ⟨(holds_var_id pairInjCol _ _).2 (by
    show tup (1 : pairInjCol) ∈ (model pairInjCol).Incl _ (star pairInjCol) p
    rw [hp]; show (1 : F) 0 ≠ (1 : F) 1; decide), fun q => ?_⟩
  rw [(model pairInjCol).holds_imp Mo, (model pairInjCol).holds_eq Mo, (model pairInjCol).sem_disj Mo]
  intro hq
  have hq1 : tup 1 ∈ (model pairInjCol).Incl _ (star pairInjCol) q := (holds_var_id pairInjCol _ _).1 hq
  obtain ⟨N, hN, hpin⟩ := finPinned'_Incl q
  refine (Set.union_eq_right.2 ?_).symm
  rintro ⟨V, ⟨⟩, k⟩ ht
  cases V
  rw [(model pairInjCol).mem_sem_iff] at ht ⊢
  have hk : ((arrow (M := pairInjCol) k : pairInjCol) : F) 0 ≠ ((arrow (M := pairInjCol) k : pairInjCol) : F) 1 := by
    have := (holds_var_push pairInjCol _ _ k).1 ht
    change tup (arrow (M := pairInjCol) k) ∈ (model pairInjCol).Incl _ (star pairInjCol) p at this
    rw [hp] at this; exact this
  obtain ⟨j, hj⟩ := inverse (pairInj_of_ne hk) hN
  rw [(model pairInjCol).holds_dia Mo]
  refine ⟨star pairInjCol, (j : star pairInjCol ⟶ star pairInjCol), ?_⟩
  rw [Category.assoc, (model pairInjCol).push_push]
  refine (holds_var_push pairInjCol _ _ _).2 ?_
  show tup (j * arrow (M := pairInjCol) k) ∈ (model pairInjCol).Incl _ (star pairInjCol) q
  refine (mem_iff_of_pinned (M := pairInjCol) hpin fun x hx => ?_).2 hq1
  show (j : F) (((arrow (M := pairInjCol) k : pairInjCol) : F) x) = x
  exact hj x hx

/-! ### Rigid Power fails

Write `Z_g` for the set of `y` with `⟨y, g⟩` in a property `Z` of individuals. `SRig Z` is the
quoted `Rigid(Z)` unfolded: persistence along every arrow, and inextensibility at every world. -/

namespace PairInjCol

local notation "A" => model pairInjCol

/-- `Rigid(Z)` for a property of individuals at `V`, as the semantics unfolds it. -/
def SRig {V : SingleObj K} (Z : (A).Dom V (.rel (.arr .e .t))) : Prop :=
  (∀ {V₁ : SingleObj K} (k : V ⟶ V₁) (x : Args (A).inner (.arr .e .t) V₁),
      (⟨V₁, (x, k)⟩ : Tuple (A).inner (.arr .e .t) V) ∈ (A).incl (.arr .e .t) V Z →
        ∀ (U : SingleObj K) (k₁ : V₁ ⟶ U),
          (⟨U, (Args.map (A).inner (.arr .e .t) k₁ x, k ≫ k₁)⟩ : Tuple (A).inner (.arr .e .t) V) ∈
            (A).incl (.arr .e .t) V Z) ∧
    ∀ {V₁ : SingleObj K} (k : V ⟶ V₁) (X : (A).Dom V₁ (.rel (.arr .e .t))),
      (∀ (x : Args (A).inner (.arr .e .t) V₁),
          (⟨V₁, (x, k)⟩ : Tuple (A).inner (.arr .e .t) V) ∈ (A).incl (.arr .e .t) V Z →
            ∀ (U : SingleObj K) (k₁ : V₁ ⟶ U),
              (⟨U, (Args.map (A).inner (.arr .e .t) k₁ x, k₁)⟩ : Tuple (A).inner (.arr .e .t) V₁) ∈
                (A).incl (.arr .e .t) V₁ X) →
        ∀ {V₂ : SingleObj K} (k₁ : V₁ ⟶ V₂) (x : Args (A).inner (.arr .e .t) V₂),
          (⟨V₂, (x, k ≫ k₁)⟩ : Tuple (A).inner (.arr .e .t) V) ∈ (A).incl (.arr .e .t) V Z →
            (⟨V₂, (x, k₁)⟩ : Tuple (A).inner (.arr .e .t) V₁) ∈ (A).incl (.arr .e .t) V₁ X

/-- An arrow as an element of the monoid, as a function. -/
abbrev fn {V U : SingleObj K} (g : V ⟶ U) : ℕ → ℕ := ((arrow (M := K) g : K) : F)

theorem fn_comp {V U T : SingleObj K} (g : V ⟶ U) (h : U ⟶ T) (n : ℕ) : fn (g ≫ h) n = fn h (fn g n) := rfl

/-- The tuple `⟨y, g⟩` of a property of individuals. -/
abbrev tp {V U : SingleObj K} (y : ℕ) (g : V ⟶ U) : Tuple (A).inner (.arr .e .t) V := ⟨U, ((y, PUnit.unit), g)⟩

/-- Every entity is pinned down by a finite set containing `0` and `1`. -/
theorem pinned01 {V : SingleObj K} (Z : (A).Dom V (.rel (.arr .e .t))) :
    ∃ N : Set ℕ, N.Finite ∧ 0 ∈ N ∧ 1 ∈ N ∧
      ∀ (g g' : K) (y : ℕ), (∀ x ∈ N, (g : F) x = (g' : F) x) →
        (tp (U := V) y (g : V ⟶ V) ∈ (A).incl _ V Z ↔ tp (U := V) y (g' : V ⟶ V) ∈ (A).incl _ V Z) := by
  obtain rfl : V = star K := Subsingleton.elim _ _
  obtain ⟨N, hN, hpin⟩ : ∃ N : Set ℕ, N.Finite ∧ (A).PinnedO (.rel (.arr .e .t)) N ((A).Incl _ (star K) Z) :=
    Premodel.ideal_inner_finPinned (natAction K) (.rel (.arr .e .t)) (star K) Z
  refine ⟨N ∪ {0, 1}, hN.union ((Set.finite_singleton 1).insert 0), Or.inr (Or.inl rfl), Or.inr (Or.inr rfl),
    fun g g' y ha => ?_⟩
  have hpin' : (A).PinnedO (.rel (.arr .e .t)) ((N ∪ {0, 1} : Set ℕ)) ((A).Incl _ (star K) Z) :=
    PinnedO.mono _ Set.subset_union_left hpin
  exact mem_iff_of_pinnedR K hpin' (fun x hx => ha x hx) _

/-- **`⊤` is rigid**: its inextensibility is BF, by approximation by surjections. -/
theorem srig_top (T : (A).Dom (star K) (.rel (.arr .e .t))) (hT : ∀ t, t ∈ (A).incl _ (star K) T) :
    SRig T := by
  refine ⟨fun _ _ _ _ _ => hT _, fun {V₁} k X hX {V₂} k₁ x _ => ?_⟩
  obtain rfl : V₁ = star K := Subsingleton.elim _ _
  obtain rfl : V₂ = star K := Subsingleton.elim _ _
  obtain ⟨y, ⟨⟩⟩ := x
  obtain ⟨N, hN, -, -, hpin⟩ := pinned01 X
  obtain ⟨j, hj, hs⟩ := approx (arrow (M := K) k₁) hN
  obtain ⟨z, rfl⟩ := hs y
  have := hX (z, PUnit.unit) (hT _) (star K) (j : star K ⟶ star K)
  exact (hpin j (arrow (M := K) k₁) _ hj).1 this

/-- A property of individuals whose membership depends on the arrow only through a finite set. -/
theorem exists_prop (P : (ℕ → ℕ) → ℕ → Prop) (N : Set ℕ) (hN : N.Finite)
    (hP : ∀ f f' : K, (∀ x ∈ N, (f : F) x = (f' : F) x) → ∀ y, (P (f : F) y ↔ P (f' : F) y)) :
    ∃ Z : (A).Dom (star K) (.rel (.arr .e .t)),
      ∀ y (g : star K ⟶ star K), tp y g ∈ (A).incl _ (star K) Z ↔ P (fn g) y := by
  let I : Intension (A).inner (.arr .e .t) (star K) := {t | P (fn t.2.2) t.2.1.1}
  obtain ⟨Z, hZ⟩ := Premodel.ideal_pinned_inner (natAction K) (.arr .e .t) (star K) I ⟨N, hN, by
    intro V h i ha
    obtain rfl : V = star K := Subsingleton.elim _ _
    simp only [Outer.map_rel]
    ext ⟨U, ⟨y, ⟨⟩⟩, g⟩
    simp only [Intension.mem_map, I, Set.mem_ofPred_eq]
    exact hP (arrow (M := K) g * arrow (M := K) h) (arrow (M := K) g * arrow (M := K) i)
      (fun x hx => by
        show (arrow (M := K) g : F) ((arrow (M := K) h : F) x) = (arrow (M := K) g : F) ((arrow (M := K) i : F) x)
        have : (arrow (M := K) h : F) x = (arrow (M := K) i : F) x := ha x hx
        rw [this]) y⟩
  refine ⟨Z, fun y g => ?_⟩
  have hZ' : (A).incl _ (star K) Z = I := hZ
  rw [hZ']; exact Iff.rfl

/-- A collapse applied after a pair-preserving injection collapses `0` with `1`. -/
theorem col_after {k j : F} (hk : PairInj k) : j (k 0) = j (k 1) ↔ j 0 = j 1 := by
  rcases hk.2 with ⟨a, b⟩ | ⟨a, b⟩ <;> rw [a, b]; exact eq_comm

/-- `Y`: at a collapse everything, at a pair-preserving injection `k` everything but `k 2`. -/
theorem exists_Y : ∃ Y : (A).Dom (star K) (.rel (.arr .e .t)),
    ∀ y (g : star K ⟶ star K), tp y g ∈ (A).incl _ (star K) Y ↔ (fn g 0 = fn g 1 ∨ y ≠ fn g 2) :=
  exists_prop (fun f y => f 0 = f 1 ∨ y ≠ f 2) {0, 1, 2} (Set.toFinite _) fun f f' ha y => by
    have e0 : (f : F) 0 = (f' : F) 0 := ha 0 (Or.inl rfl)
    have e1 : (f : F) 1 = (f' : F) 1 := ha 1 (Or.inr (Or.inl rfl))
    have e2 : (f : F) 2 = (f' : F) 2 := ha 2 (Or.inr (Or.inr rfl))
    simp only [e0, e1, e2]

/-- **`Y` is rigid.** -/
theorem srig_Y (Y : (A).Dom (star K) (.rel (.arr .e .t)))
    (hY : ∀ y (g : star K ⟶ star K), tp y g ∈ (A).incl _ (star K) Y ↔ (fn g 0 = fn g 1 ∨ y ≠ fn g 2)) :
    SRig Y := by
  refine ⟨fun {V₁} k x hx U k₁ => ?_, fun {V₁} k X hX {V₂} k₁ x hx => ?_⟩
  · obtain rfl : V₁ = star K := Subsingleton.elim _ _
    obtain rfl : U = star K := Subsingleton.elim _ _
    obtain ⟨y, ⟨⟩⟩ := x
    have hx' := (hY y k).1 hx
    refine (hY (fn k₁ y) (k ≫ k₁)).2 ?_
    simp only [fn_comp]
    by_cases hc : fn k 0 = fn k 1
    · exact Or.inl (by rw [hc])
    · have hk := pairInj_of_ne hc
      rcases cases (arrow (M := K) k₁) with hj | hj
      · exact Or.inr fun e => (hx'.resolve_left hc) (hj.1 e)
      · exact Or.inl ((col_after hk).2 hj)
  · obtain rfl : V₁ = star K := Subsingleton.elim _ _
    obtain rfl : V₂ = star K := Subsingleton.elim _ _
    obtain ⟨y, ⟨⟩⟩ := x
    have hx' := (hY y (k ≫ k₁)).1 hx
    simp only [fn_comp] at hx'
    obtain ⟨N, hN, h0N, h1N, hpin⟩ := pinned01 X
    -- a fresh point sent to `y` by an arrow agreeing with `k₁` on `N`
    have finish : ∀ x, x ∉ N → x ≠ fn k 2 →
        (fn k₁ 0 = fn k₁ 1 ∨ ∀ n ∈ N, fn k₁ n ≠ y) → tp y k₁ ∈ (A).incl _ (star K) X := by
      intro x hxN hxk hcond
      obtain ⟨j', hj', hjx⟩ := hit (arrow (M := K) k₁) h0N h1N hxN y hcond
      have := hX (x, PUnit.unit) ((hY x k).2 (Or.inr hxk)) (star K) (j' : star K ⟶ star K)
      have h2 : tp (U := star K) y (j' : star K ⟶ star K) ∈ (A).incl _ (star K) X := by
        rw [← hjx]; exact this
      exact (hpin j' (arrow (M := K) k₁) y hj').1 h2
    obtain ⟨x, hx⟩ := fresh ((hN.insert (fn k 2)))
    have hxN : x ∉ N := fun h => hx (Or.inr h)
    have hxk : x ≠ fn k 2 := fun h => hx (Or.inl h)
    by_cases hA : ∃ n ∈ N, fn k₁ n = y
    · obtain ⟨n, hn, rfl⟩ := hA
      by_cases hnY : fn k 0 = fn k 1 ∨ n ≠ fn k 2
      · exact hX (n, PUnit.unit) ((hY n k).2 hnY) (star K) k₁
      · push Not at hnY
        obtain ⟨hc, rfl⟩ := hnY
        have hcol : fn k₁ (fn k 0) = fn k₁ (fn k 1) := hx'.resolve_right (by simp)
        exact finish x hxN hxk (Or.inl ((col_after (pairInj_of_ne hc)).1 hcol))
    · push Not at hA
      exact finish x hxN hxk (Or.inr hA)

/-- **Along a collapse, a rigid property has everything or finitely much in its extension.** -/
theorem collapse_ext (Z : (A).Dom (star K) (.rel (.arr .e .t))) (hZ : SRig Z) (m : star K ⟶ star K)
    (hm : fn m 0 = fn m 1) :
    (∀ b, tp b m ∈ (A).incl _ (star K) Z) ∨ {b | tp b m ∈ (A).incl _ (star K) Z}.Finite := by
  classical
  let S : Set ℕ := {y | tp y (𝟙 (star K)) ∈ (A).incl _ (star K) Z}
  by_cases hS : S.Finite
  · right
    obtain ⟨X, hX⟩ := exists_prop (fun f y => y ∈ f '' S) S hS fun f f' ha y => by
      have : (f : F) '' S = (f' : F) '' S := Set.image_congr ha
      rw [this]
    refine (hS.image (fn m)).subset fun b hb => ?_
    have h1 := hZ.2 (𝟙 (star K)) X (fun x hx U k₂ => by
      obtain rfl : U = star K := Subsingleton.elim _ _
      obtain ⟨y, ⟨⟩⟩ := x
      exact (hX _ k₂).2 ⟨y, hx, rfl⟩) m (b, PUnit.unit) (by rw [Category.id_comp]; exact hb)
    exact (hX b m).1 h1
  · left
    intro b
    obtain ⟨N, hN, h0N, h1N, hpin⟩ := pinned01 Z
    obtain ⟨x, hxS, hxN⟩ := (Set.Infinite.sdiff hS hN).nonempty
    obtain ⟨m', hm', hmx⟩ := hit (arrow (M := K) m) h0N h1N hxN b (Or.inl hm)
    have := hZ.1 (𝟙 (star K)) (x, PUnit.unit) hxS (star K) (m' : star K ⟶ star K)
    rw [Category.id_comp] at this
    have h2 : tp (U := star K) b (m' : star K ⟶ star K) ∈ (A).incl _ (star K) Z := by rw [← hmx]; exact this
    exact (hpin m' (arrow (M := K) m) b hm').1 h2

/-- `𝐗`: at `g`, the transports `k' · Z` of the rigid `Z` along arrows `k'` agreeing with `g` on
`{0, 1}`. -/
theorem exists_bigX : ∃ BX : (A).Dom (star K) (.rel (.arr (.rel (.arr .e .t)) .t)),
    ∀ (W : (A).Dom (star K) (.rel (.arr .e .t))) (g : star K ⟶ star K),
      (⟨star K, ((W, PUnit.unit), g)⟩ : Tuple (A).inner (.arr (.rel (.arr .e .t)) .t) (star K)) ∈
          (A).incl _ (star K) BX ↔
        ∃ Z : (A).Dom (star K) (.rel (.arr .e .t)), SRig Z ∧ ∃ k' : K,
          (k' : F) 0 = fn g 0 ∧ (k' : F) 1 = fn g 1 ∧ W = ((A).inner (.rel (.arr .e .t))).map (k' : star K ⟶ star K) Z := by
  let I : Intension (A).inner (.arr (.rel (.arr .e .t)) .t) (star K) :=
    {t | ∃ Z : (A).Dom (star K) (.rel (.arr .e .t)), SRig Z ∧ ∃ k' : K,
      (k' : F) 0 = fn t.2.2 0 ∧ (k' : F) 1 = fn t.2.2 1 ∧
        t.2.1.1 = ((A).inner (.rel (.arr .e .t))).map (k' : star K ⟶ t.1) Z}
  let N01 : Set ℕ := {0, 1}
  obtain ⟨BX, hBX⟩ := Premodel.ideal_pinned_inner (natAction K) (.arr (.rel (.arr .e .t)) .t) (star K) I
    ⟨N01, (show N01.Finite from (Set.finite_singleton (1 : ℕ)).insert 0), by
      intro V h i ha
      obtain rfl : V = star K := Subsingleton.elim _ _
      have e0 : fn h 0 = fn i 0 := ha (0 : ℕ) (Or.inl rfl)
      have e1 : fn h 1 = fn i 1 := ha (1 : ℕ) (Or.inr rfl)
      simp only [Outer.map_rel]
      ext ⟨U, ⟨W, ⟨⟩⟩, g⟩
      simp only [Intension.mem_map, I, Set.mem_ofPred_eq]
      show (∃ Z, SRig Z ∧ ∃ k' : K, (k' : F) 0 = fn g (fn h 0) ∧ (k' : F) 1 = fn g (fn h 1) ∧ _) ↔
        (∃ Z, SRig Z ∧ ∃ k' : K, (k' : F) 0 = fn g (fn i 0) ∧ (k' : F) 1 = fn g (fn i 1) ∧ _)
      rw [e0, e1]⟩
  refine ⟨BX, fun W g => ?_⟩
  have hBX' : (A).incl _ (star K) BX = I := hBX
  rw [hBX']; exact Iff.rfl

/-- **Rigid Power fails at `e → t`, with `F := ⊤`.** -/
theorem not_rigidPower : ¬ (A).HoldsSentence (P.RigidPower.quoted (.arr .e .t)) := by
  have Mo : (A).IsModel := model_isModel K
  intro H
  simp only [HoldsSentence, P.RigidPower.quoted, (A).holds_conj Mo, (A).holds_box Mo,
    (A).holds_forall Mo, (A).holds_imp Mo, holds_inclR Mo, sem_boxR Mo, sem_var, IEnv.get,
    IEnv.get_map, (A).incl_map, Intension.mem_map, Set.mem_ofPred_eq, Category.comp_id, Category.id_comp, push,
    (A).holds_eq Mo, (A).sem_orR Mo, holds_app_var1] at H
  obtain ⟨T, hT⟩ := exists_prop (fun _ _ => True) ∅ Set.finite_empty (fun _ _ _ _ => Iff.rfl)
  have hTall : ∀ t, t ∈ (A).incl _ (star K) T := by
    rintro ⟨U, ⟨y, ⟨⟩⟩, g⟩
    obtain rfl : U = star K := Subsingleton.elim _ _
    exact (hT y g).2 trivial
  obtain ⟨-, H1⟩ := H T (srig_top T hTall)
  obtain ⟨BX, hBX⟩ := exists_bigX
  obtain ⟨Y, hY⟩ := exists_Y
  have hTuniv : (A).incl _ (star K) T = Set.univ := Set.eq_univ_of_forall hTall
  have map_univ : ∀ (k : star K ⟶ star K),
      Intension.map (A).inner k (Set.univ : Intension (A).inner (.arr .e .t) (star K)) = Set.univ := fun k => by
    ext t; simp [Intension.mem_map]
  let c : star K ⟶ star K := (⟨fun _ => 0, Or.inr rfl⟩ : K)
  have H3 : (Y, PUnit.unit) ∈ Intension.ext' (A).inner (Intension.map (A).inner c ((A).incl _ (star K) BX)) := by
    refine @H1 (star K) (𝟙 _) BX ?_ (star K) c Y ⟨srig_Y Y hY, ?_⟩
    · intro a ha V k
      obtain rfl : V = star K := Subsingleton.elim _ _
      show (⟨star K, ((((A).inner _).map k a, PUnit.unit), 𝟙 (star K))⟩ :
        Tuple (A).inner (.arr (.rel (.arr .e .t)) .t) (star K)) ∈ Intension.map (A).inner k ((A).incl _ (star K) BX)
      rw [Intension.mem_map, Category.comp_id]
      exact (hBX _ k).2 ⟨a, ha.1, arrow (M := K) k, rfl, rfl, rfl⟩
    · refine (Set.union_eq_right.2 fun t _ => ?_).symm
      show t ∈ Intension.map (A).inner c (Intension.map (A).inner (𝟙 _) ((A).incl _ (star K) T))
      rw [hTuniv, map_univ, map_univ]; trivial
  have H4 : (⟨star K, ((Y, PUnit.unit), c)⟩ : Tuple (A).inner (.arr (.rel (.arr .e .t)) .t) (star K)) ∈
      (A).incl _ (star K) BX := by
    have := H3
    change (⟨star K, ((Y, PUnit.unit), 𝟙 (star K))⟩ : Tuple (A).inner (.arr (.rel (.arr .e .t)) .t) (star K)) ∈
      Intension.map (A).inner c ((A).incl _ (star K) BX) at this
    rwa [Intension.mem_map, Category.comp_id] at this
  obtain ⟨Z, hZ, k', e0, e1, hYZ⟩ := (hBX Y c).1 H4
  let m : star K ⟶ star K := k'
  have hk' : fn m 0 = fn m 1 := e0.trans e1.symm
  -- `Y`'s extension at the identity is everything but `2`, and it is `Z`'s at `k'`
  have hext : ∀ y, tp (U := star K) y m ∈ (A).incl _ (star K) Z ↔ y ≠ 2 := fun y => by
    have h1 : tp (U := star K) y (𝟙 (star K)) ∈ (A).incl _ (star K) Y ↔ tp (U := star K) y m ∈ (A).incl _ (star K) Z := by
      rw [hYZ, (A).incl_map, Intension.mem_map, Category.comp_id]
    rw [← h1, hY]
    show (0 = 1 ∨ y ≠ 2) ↔ y ≠ 2
    simp
  rcases collapse_ext Z hZ m hk' with h | h
  · exact (hext 2).1 (h 2) rfl
  · exact (Set.finite_singleton 2).infinite_compl (h.subset fun b hb => (hext b).2 hb)

end PairInjCol

end Classicism.Meta.Intensional.Monoids
