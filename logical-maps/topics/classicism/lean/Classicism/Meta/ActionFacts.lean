import Classicism.Meta.ActionSoundness

/-!
# Facts about action models

The generalizations of Classicism, §"Exploring action models", that make particular
models easy to check: the clause for `□`, and three characterizations at the evaluation
object of an action model, for `ND_σ` (necessity of distinctness), `BF_σ` (the Barcan
formula) and the Fregean Axiom, each in terms of the arrows out of that object.

- **ND_σ holds iff `h^σ` is injective for every arrow `h` out of the object** (the paper's
  Proposition, (i)).
- **BF_σ holds if `h^σ` is surjective for every such arrow** ((ii)).
- **The Fregean Axiom holds iff any two propositions that agree on the identity arrow are
  equal.**

Each principle is a closed sentence of the object language, written here once; the
characterizations are for any arrow `h : W₀ → W`, so they serve at the root and at any
truncation.
-/

namespace Classicism.Meta

open CategoryTheory Term

variable {Sig : Signature}

/-! ### The sentences -/

namespace Sentence

/-- `ND_σ`: `∀x y. x ≠ y → □(x ≠ y)`. -/
def nd (σ : Ty) : Sentence Sig :=
  forall' (σ := σ) (forall' (σ := σ) (imp (neg (eq' v1 v0)) (box (neg (eq' v1 v0)))))

/-- `BF_σ`: `∀X. (∀x. □Xx) → □∀x. Xx`. -/
def bf (σ : Ty) : Sentence Sig :=
  forall' (σ := σ ⇒ RTy.t)
    (imp (forall' (σ := σ) (box (app v1 v0))) (box (forall' (σ := σ) (app v1 v0))))

/-- The Fregean Axiom: `∀p q. (p ↔ q) → p = q`. -/
def fregean : Sentence Sig :=
  forall' (σ := Ty.rel .t) (forall' (σ := Ty.rel .t) (imp (iff v1 v0) (eq' v1 v0)))

end Sentence

namespace Premodel

variable {C : Type} [SmallCategory C] (A : Premodel Sig C) (M : A.IsModel)
include M

/-! ### The clause for `□` -/

theorem sem_top {Γ : Ctx} {W : C} (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ) :
    A.sem h (top : Formula Sig Γ) g = Set.univ := by
  rw [top, A.sem_disj M, A.sem_neg M]
  exact Set.union_compl_self _

/-- `A, h, g ⊩ □P` iff `A, k∘h, k∘g ⊩ P` for every arrow `k` out of the object. -/
theorem holds_box {Γ : Ctx} {W : C} (h : A.W₀ ⟶ W) (p : Formula Sig Γ) (g : IEnv (A.Dom W) Γ) :
    A.Holds h (box p) g ↔ ∀ {V : C} (k : W ⟶ V), A.Holds (h ≫ k) p (A.push k g) := by
  rw [box, A.holds_eq M, A.sem_top M, Set.eq_univ_iff_forall]
  constructor
  · intro H V k
    exact (A.mem_sem_iff M h g p k).1 (H ⟨V, k⟩)
  · rintro H ⟨V, k⟩
    exact (A.mem_sem_iff M h g p k).2 (H k)

/-! ### `ND_σ` and injectivity -/

theorem holds_nd_iff (σ : Ty) {W : C} (h : A.W₀ ⟶ W) :
    A.Holds h (Sentence.nd σ) .nil ↔
      ∀ {V : C} (k : W ⟶ V), Function.Injective ((A.inner σ).map k) := by
  simp only [Sentence.nd, A.holds_forall M, A.holds_imp M, A.holds_neg M, A.holds_box M,
    A.holds_eq M]
  constructor
  · intro H V k a b hab
    by_contra hne
    exact H a b (fun e => hne (A.Incl_injective σ W e)) k (congrArg (A.Incl σ V) hab)
  · intro H a b hne V k e
    exact hne (congrArg (A.Incl σ W) (H k (A.Incl_injective σ V e)))

/-! ### `BF_σ` and surjectivity -/

theorem holds_bf_of_surjective (σ : Ty) {W : C} (h : A.W₀ ⟶ W)
    (hs : ∀ {V : C} (k : W ⟶ V), Function.Surjective ((A.inner σ).map k)) :
    A.Holds h (Sentence.bf σ) .nil := by
  simp only [Sentence.bf, A.holds_forall M, A.holds_imp M, A.holds_box M]
  intro X H V k a
  obtain ⟨b, rfl⟩ := hs k a
  exact H b k

/-! ### The Fregean Axiom -/

theorem holds_fregean_iff {W : C} (h : A.W₀ ⟶ W) :
    A.Holds h Sentence.fregean .nil ↔
      ∀ p q : A.Dom W (.rel .t),
        ((⟨W, 𝟙 W⟩ : Σ V, W ⟶ V) ∈ A.incl .t W p ↔ (⟨W, 𝟙 W⟩ : Σ V, W ⟶ V) ∈ A.incl .t W q) → p = q := by
  simp only [Sentence.fregean, A.holds_forall M, A.holds_imp M, A.holds_iff M, A.holds_eq M]
  constructor
  · intro H p q e
    exact A.Incl_injective _ W (H p q e)
  · intro H p q e
    exact congrArg (A.Incl _ W) (H p q e)

end Premodel

end Classicism.Meta
