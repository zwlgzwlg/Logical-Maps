import Classicism.Semantics.IntensionalFacts
import Classicism.Syntax.Infinity
import Classicism.Syntax.ClosedTypes
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.OfFn

/-!
# Counting entities: the Infinity schemas in a model

The `n`-th instance of the Infinity schema at `σ`, `∃x₁ … xₙ. ⋀_{i<j} xᵢ ≠ xⱼ`, holds at a world
iff the world's domain at `σ` has `n` distinct members (`holds_count`): the block of `n`
existential quantifiers is `n` values, `blockEnv` (`holds_existsBlock`), the variables of the
block take those values (`semList_vars`), and pairwise distinctness is `List.Nodup`
(`holds_distinct`).

So the schema fails at a world with fewer than two individuals (the map's `one-individual`),
and at a world with finitely many propositions (`finitely-many-propositions`).

The sentences counting `n` entities are pure and in the paper's language (`closedTypes_count`),
so B for pure sentences fails where the evaluation object has `n` propositions but some world
after it, and every world after that, has fewer (`not_holds_b_count`, the map's
`fewer-propositions-after`).
-/

namespace Classicism.Meta.Intensional

/-! ### The counting sentences are in the paper's language -/

namespace Count

variable {Sig : Signature}

/-- `∃x₁ … xₙ. ⋀_{i<j} xᵢ ≠ xⱼ` at `σ`. -/
abbrev count (Sig : Signature) (σ : Ty) (n : Nat) : Sentence Sig :=
  Term.existsBlock (List.replicate n σ) (Term.distinct n (Terms.vars (List.replicate n σ) []))

/-- Every term of the tuple is in the paper's language. -/
def AllClosed {Γ : Ctx} : ∀ {σs : List Ty}, Terms Sig Γ σs → Prop
  | _, .nil => True
  | _, .cons a as => a.closedTypes = true ∧ AllClosed as

theorem allClosed_cons {Γ : Ctx} {σ : Ty} {σs : List Ty} :
    ∀ xs : Terms Sig Γ (σ :: σs), AllClosed xs → xs.head.closedTypes = true ∧ AllClosed xs.tail
  | .cons _ _, h => h

theorem allClosed_vars {σ : Ty} (hσ : σ.Closed) : ∀ (n : Nat) (Γ : Ctx),
    AllClosed (Terms.vars (Sig := Sig) (List.replicate n σ) Γ)
  | 0, _ => trivial
  | n + 1, Γ => ⟨by rw [Term.closedTypes_rename]; simpa [Term.closedTypes] using hσ,
      allClosed_vars hσ n (σ :: Γ)⟩

theorem closedTypes_neAll {Γ : Ctx} {σ : Ty} (hσ : σ.Closed) (a : Term Sig Γ σ)
    (ha : a.closedTypes = true) : ∀ (n : Nat) (xs : Terms Sig Γ (List.replicate n σ)),
    AllClosed xs → (Term.neAll a n xs).closedTypes = true
  | 0, _, _ => by simp [Term.neAll, Term.closedTypes]
  | n + 1, xs, h => by
    obtain ⟨h1, h2⟩ := allClosed_cons xs h
    simp [Term.neAll, Term.closedTypes, ha, h1, hσ, closedTypes_neAll hσ a ha n xs.tail h2]

theorem closedTypes_distinct {Γ : Ctx} {σ : Ty} (hσ : σ.Closed) : ∀ (n : Nat)
    (xs : Terms Sig Γ (List.replicate n σ)), AllClosed xs → (Term.distinct n xs).closedTypes = true
  | 0, _, _ => by simp [Term.distinct, Term.closedTypes]
  | n + 1, xs, h => by
    obtain ⟨h1, h2⟩ := allClosed_cons xs h
    simp [Term.distinct, Term.closedTypes, closedTypes_neAll hσ _ h1 n xs.tail h2,
      closedTypes_distinct hσ n xs.tail h2]

theorem closedTypes_existsBlock {σ : Ty} (hσ : σ.Closed) : ∀ (n : Nat) {Γ : Ctx}
    (p : Formula Sig (Ctx.block (List.replicate n σ) Γ)), p.closedTypes = true →
    (Term.existsBlock (List.replicate n σ) p).closedTypes = true
  | 0, _, _, h => h
  | n + 1, _, p, h => by
    show (Term.exists' (Term.existsBlock (List.replicate n σ) p)).closedTypes = true
    simp [Term.closedTypes, hσ, closedTypes_existsBlock hσ n p h]

theorem closedTypes_count {σ : Ty} (hσ : σ.Closed) (n : Nat) : (count Sig σ n).closedTypes = true :=
  closedTypes_existsBlock hσ n _ (closedTypes_distinct hσ n _ (allClosed_vars hσ n []))

/-- `P → □◇P` for a counting sentence is in the paper's language. -/
theorem closedTypes_b_count {σ : Ty} (hσ : σ.Closed) (n : Nat) :
    (Term.imp (count Sig σ n) (Term.box (Term.dia (count Sig σ n)))).closedTypes = true := by
  simp [Term.closedTypes, closedTypes_count hσ n]

end Count

open CategoryTheory

namespace Premodel

variable {Sig : Signature} {C : Type} [SmallCategory C] (A : Premodel Sig C)

/-- The assignment extended by `n` values for a block of variables of type `σ`, the first
outermost. -/
def blockEnv {W : C} {σ : Ty} : ∀ (n : Nat) {Γ : Ctx}, (Fin n → A.Dom W σ) → IEnv (A.Dom W) Γ →
    IEnv (A.Dom W) (Ctx.block (List.replicate n σ) Γ)
  | 0, _, _, g => g
  | n + 1, _, f, g => blockEnv n (fun i => f i.succ) (.cons (f 0) g)

/-- The variables outside the block keep their values. -/
theorem blockEnv_get_wkBlock {W : C} {σ : Ty} : ∀ (n : Nat) {Γ : Ctx} (f : Fin n → A.Dom W σ)
    (g : IEnv (A.Dom W) Γ) {τ : Ty} (v : Var Γ τ),
    (A.blockEnv n f g).get (Ren.wkBlock (List.replicate n σ) _ v) = g.get v
  | 0, _, _, _, _, _ => rfl
  | n + 1, _, f, g, _, v => blockEnv_get_wkBlock n (fun i => f i.succ) (.cons (f 0) g) (.succ v)

/-- The values of a tuple of terms of one type. -/
def semList {W : C} (h : A.W₀ ⟶ W) {Γ : Ctx} {σ : Ty} :
    ∀ (n : Nat), Terms Sig Γ (List.replicate n σ) → IEnv (A.Dom W) Γ → List (Outer A.inner σ W)
  | 0, _, _ => []
  | n + 1, xs, g => A.sem h xs.head g :: semList h n xs.tail g

/-- The variables of a block take its values. -/
theorem semList_vars {W : C} (h : A.W₀ ⟶ W) {σ : Ty} : ∀ (n : Nat) {Γ : Ctx}
    (f : Fin n → A.Dom W σ) (g : IEnv (A.Dom W) Γ),
    A.semList h n (Terms.vars (List.replicate n σ) Γ) (A.blockEnv n f g) =
      List.ofFn fun i => A.Incl σ W (f i)
  | 0, _, _, _ => rfl
  | n + 1, Γ, f, g => by
    rw [List.ofFn_succ, ← semList_vars h n (fun i => f i.succ) (.cons (f 0) g)]
    show A.sem h ((Term.var .zero : Term Sig (σ :: Γ) σ).rename (Ren.wkBlock (List.replicate n σ)))
        (A.blockEnv n (fun i => f i.succ) (.cons (f 0) g)) :: _ = _
    rw [A.sem_rename]
    congr 1
    show A.Incl σ W ((IEnv.ren _ _).get .zero) = _
    rw [IEnv.get_ren, A.blockEnv_get_wkBlock]
    rfl

/-- `fewer-propositions-after`: the evaluation object has `n` distinct propositions, and some
world after it, and every world after that, has fewer. -/
def FewerPropositionsAfter : Prop :=
  ∃ (n : Nat) (V : C) (_ : A.W₀ ⟶ V), (∃ f : Fin n → A.Dom A.W₀ (.rel .t), Function.Injective f) ∧
    ∀ (U : C) (_ : V ⟶ U) (f : Fin n → A.Dom U (.rel .t)), ¬ Function.Injective f

variable {A} (M : A.IsModel)
include M

/-- A block of existential quantifiers holds iff some values for it make the body hold. -/
theorem holds_existsBlock {W : C} (h : A.W₀ ⟶ W) {σ : Ty} : ∀ (n : Nat) {Γ : Ctx}
    (p : Formula Sig (Ctx.block (List.replicate n σ) Γ)) (g : IEnv (A.Dom W) Γ),
    A.Holds h (Term.existsBlock (List.replicate n σ) p) g ↔
      ∃ f : Fin n → A.Dom W σ, A.Holds h p (A.blockEnv n f g)
  | 0, _, p, g => ⟨fun hp => ⟨Fin.elim0, hp⟩, fun ⟨_, hp⟩ => hp⟩
  | n + 1, _, p, g => by
    show A.Holds h (Term.exists' (Term.existsBlock (List.replicate n σ) p)) g ↔ _
    rw [A.holds_exists M]
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨f, hf⟩ := (holds_existsBlock h n p (.cons x g)).1 hx
      exact ⟨Fin.cons x f, hf⟩
    · rintro ⟨f, hf⟩
      exact ⟨f 0, (holds_existsBlock h n p (.cons (f 0) g)).2 ⟨fun i => f i.succ, hf⟩⟩

theorem holds_neAll {W : C} (h : A.W₀ ⟶ W) {Γ : Ctx} {σ : Ty} (g : IEnv (A.Dom W) Γ)
    (a : Term Sig Γ σ) : ∀ (n : Nat) (xs : Terms Sig Γ (List.replicate n σ)),
    A.Holds h (Term.neAll a n xs) g ↔ ∀ v ∈ A.semList h n xs g, A.sem h a g ≠ v
  | 0, _ => ⟨fun _ _ hv => (nomatch hv), fun _ => A.holds_top M h g⟩
  | n + 1, xs => by
    rw [Term.neAll, A.holds_conj M, A.holds_neg M, A.holds_eq M, holds_neAll h g a n xs.tail]
    simp [semList]

/-- Pairwise distinctness holds iff the values are pairwise distinct. -/
theorem holds_distinct {W : C} (h : A.W₀ ⟶ W) {Γ : Ctx} {σ : Ty} (g : IEnv (A.Dom W) Γ) :
    ∀ (n : Nat) (xs : Terms Sig Γ (List.replicate n σ)),
    A.Holds h (Term.distinct n xs) g ↔ (A.semList h n xs g).Nodup
  | 0, _ => ⟨fun _ => List.nodup_nil, fun _ => A.holds_top M h g⟩
  | n + 1, xs => by
    rw [Term.distinct, A.holds_conj M, holds_neAll M h g, holds_distinct h g n xs.tail]
    simp only [semList, List.nodup_cons]
    exact and_congr_left' ⟨fun H hm => H _ hm rfl, fun H v hv e => H (e ▸ hv)⟩

/-- **The `n`-th instance of the Infinity schema at `σ` holds at a world iff the world has
`n` distinct members of type `σ`.** -/
theorem holds_count {W : C} (h : A.W₀ ⟶ W) (σ : Ty) (n : Nat) :
    A.Holds h (Term.existsBlock (List.replicate n σ)
      (Term.distinct n (Terms.vars (List.replicate n σ) []))) .nil ↔
      ∃ f : Fin n → A.Dom W σ, Function.Injective f := by
  rw [holds_existsBlock M h n]
  refine exists_congr fun f => ?_
  rw [holds_distinct M h, A.semList_vars h n f, List.nodup_ofFn]
  exact ⟨fun H _ _ e => H (congrArg _ e), fun H _ _ e => H (A.Incl_injective σ W e)⟩

/-- **B for the sentence counting `n` propositions fails** where the evaluation object has `n`
propositions and some world after it, and every world after that, has fewer. -/
theorem not_holds_b_count (hF : A.FewerPropositionsAfter) : ∃ n, ¬ A.Holds (𝟙 _)
    (Term.imp (Count.count Sig (.rel .t) n) (Term.box (Term.dia (Count.count Sig (.rel .t) n)))) .nil := by
  obtain ⟨n, V, k, h0, h1⟩ := hF
  refine ⟨n, fun H => ?_⟩
  rw [A.holds_imp M] at H
  have H := H ((holds_count M (𝟙 _) (.rel .t) n).2 h0)
  rw [A.holds_box M] at H
  have H := H k
  rw [A.holds_dia M] at H
  obtain ⟨U, j, hj⟩ := H
  rw [IEnv.nil_eq (A.push j _)] at hj
  obtain ⟨f, hf⟩ := (holds_count M _ (.rel .t) n).1 hj
  exact h1 U j f hf

end Premodel

end Classicism.Meta.Intensional
