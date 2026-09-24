import Classicism.Semantics.ActionFacts
import Classicism.Syntax.SentenceSchemas

/-!
# Properties of action models, and what holds in all models with them

The paper's classification of action models (Classicism, §"Exploring action models" and
§"Action models"): the base category has one object (an *M-set model*); the model is
*propositionally full* (every set of arrows out of an object is a proposition there),
*quasi-functionally full* (every well-behaved function with inner values is inner),
*full* (both). And the facts of the form "every instance of this schema holds in every
model with this property":

- **No Pure Contingency** — `P → □P` for every pure sentence `P` — holds in every
  one-object model: the value of a pure sentence depends only on the target of the arrow
  it is evaluated at, and in a one-object category every arrow has the same target.
- **The Fregean Axiom fails** in every propositionally full model whose base has a second
  arrow out of it: `⊤` and `{id}` agree at the identity but differ.

The facts about full models proper — a full premodel is a model, and `BF_σ` at the root
forces every `h^σ` out of it to be surjective — are in `ActionFull.lean`, with the
construction.
-/

namespace Classicism.Meta

open CategoryTheory

namespace Premodel

variable {Sig : Signature} {C : Type} [SmallCategory C] (A : Premodel Sig C)

/-! ### Properties -/

/-- Propositionally full: at every object, every set of arrows out of it is the inclusion
of an inner proposition. -/
def PropFull : Prop := ∀ W : C, Function.Surjective (A.incl .t W)

/-- Quasi-functionally full: at every arrow type and object, every outer function that is
well-behaved and takes inner values is inner. -/
def FunFull : Prop :=
  ∀ (σ : Ty) (ρ : RTy) (W : C) (F : RawR A.inner (.arr σ ρ) W),
    (∀ (V : C) (h : W ⟶ V) (x : A.Dom V σ), F V h x ∈ Set.range (A.incl ρ V)) →
    (∀ (V U : C) (h : W ⟶ V) (i : V ⟶ U) (x : A.Dom V σ),
      RawR.map A.inner ρ i (F V h x) = F U (h ≫ i) ((A.inner σ).map i x)) →
    F ∈ Set.range (A.incl (.arr σ ρ) W)

/-- Full: propositionally and quasi-functionally. -/
def Full : Prop := A.PropFull ∧ A.FunFull

/-! ### Pure terms do not see the arrow -/

/-- The value of a pure term depends on the arrow only through its target: with no
constants, nothing reads the arrow. -/
theorem sem_pure : ∀ {Γ : Ctx} {σ : Ty} {W : C} (t : Term Sig Γ σ), t.pure = true →
    ∀ (h h' : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ), A.sem h t g = A.sem h' t g
  | _, _, _, .var _, _, _, _, _ => rfl
  | _, _, _, .const _, hp, _, _, _ => by simp [Term.pure] at hp
  | _, _, _, .app f a, hp, h, h', g => by
    simp only [Term.pure, Bool.and_eq_true] at hp
    show A.apply (A.sem h f g) (A.sem h a g) = A.apply (A.sem h' f g) (A.sem h' a g)
    rw [sem_pure f hp.1 h h', sem_pure a hp.2 h h']
  | _, _, _, .lam b, hp, h, h', g => by
    show (fun U j x => A.sem (h ≫ j) b (.cons x (A.push j g)))
      = (fun U j x => A.sem (h' ≫ j) b (.cons x (A.push j g)))
    funext U j x
    exact sem_pure b hp (h ≫ j) (h' ≫ j) _
  | _, _, _, .and, _, _, _, _ | _, _, _, .or, _, _, _, _ | _, _, _, .not, _, _, _, _
  | _, _, _, .all _, _, _, _, _ | _, _, _, .ex _, _, _, _, _ | _, _, _, .eq _, _, _, _, _
  | _, _, _, .constR _, _, _, _, _ | _, _, _, .negR _, _, _, _, _ | _, _, _, .andR _, _, _, _, _
  | _, _, _, .orR _, _, _, _, _ | _, _, _, .coextR _, _, _, _, _ | _, _, _, .boxR _, _, _, _, _
  | _, _, _, .boxImpR _, _, _, _, _ => rfl

/-- **No Pure Contingency holds in every one-object model** (Classicism, §"Exploring
action models"). -/
theorem holdsAx_npc [Subsingleton C] (M : A.IsModel) : A.HoldsAx (AxiomSet.npc Sig) := by
  rintro a ⟨p, hp, rfl⟩
  rw [HoldsSentence, A.holds_imp M, A.holds_box M]
  intro H V k
  obtain rfl : V = A.W₀ := Subsingleton.elim _ _
  rw [IEnv.nil_eq (A.push k IEnv.nil)]
  unfold Holds at H ⊢
  rw [A.sem_pure p hp (𝟙 _ ≫ k) (𝟙 _)]
  exact H

/-! ### Propositional fullness refutes the Fregean Axiom -/

/-- In a propositionally full model with a second arrow out of the base, the Fregean Axiom
fails: `⊤` and `{id}` are propositions agreeing at the identity but different. -/
theorem not_fregean_of_propFull (M : A.IsModel) (hP : A.PropFull) {V : C} (k : A.W₀ ⟶ V)
    (hk : (⟨V, k⟩ : Σ V, A.W₀ ⟶ V) ≠ ⟨A.W₀, 𝟙 A.W₀⟩) :
    ¬ A.HoldsSentence Sentence.fregean := by
  intro H
  rw [HoldsSentence, A.holds_fregean_iff M] at H
  obtain ⟨p, hp⟩ := hP A.W₀ Set.univ
  obtain ⟨q, hq⟩ := hP A.W₀ {⟨A.W₀, 𝟙 A.W₀⟩}
  have e := H p q (by rw [hp, hq]; exact ⟨fun _ => Set.mem_singleton _, fun _ => Set.mem_univ _⟩)
  subst e
  rw [hp] at hq
  exact hk (Set.mem_singleton_iff.mp (hq ▸ Set.mem_univ _))

end Premodel

end Classicism.Meta
