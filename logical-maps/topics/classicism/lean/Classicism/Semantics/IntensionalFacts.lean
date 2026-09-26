import Classicism.Semantics.IntensionalSoundness
import Classicism.Syntax.Sentences

/-!
# Facts about intensional action models

The generalizations of Classicism, §"Exploring action models", that make particular
models easy to check, for the intensional form: the clauses for `□` and `◇`, and three
characterizations at the evaluation object of a model, for `ND_σ` (necessity of
distinctness), `BF_σ` (the Barcan formula) and the Fregean Axiom, each in terms of the
arrows out of that object.

- **ND_σ holds iff `h^σ` is injective for every arrow `h` out of the object** (the paper's
  Proposition, (i)).
- **BF_σ holds if `h^σ` is surjective for every such arrow** ((ii)).
- **The Fregean Axiom holds iff any two propositions that agree on the identity arrow are
  equal.**

Then **truncation**: the same premodel with a new base, in which `◇P` holds iff `P` holds
in some truncation and `□P` iff in every one. Where the action models of
`ActionFacts.lean` needed a lemma per reading to transfer to the truncation, here the
readings are defined from the actions and the inclusion alone, and transfer by `rfl`.
-/

namespace Classicism.Meta.Intensional

open CategoryTheory Term

variable {Sig : Signature}

namespace Premodel

variable {C : Type} [SmallCategory C] (A : Premodel Sig C) (M : A.IsModel)
include M

/-! ### The clauses for `□` and `◇` -/

/-- `A, h, g ⊩ □P` iff `A, k∘h, k∘g ⊩ P` for every arrow `k` out of the object. -/
theorem holds_box {Γ : Ctx} {W : C} (h : A.W₀ ⟶ W) (p : Formula Sig Γ) (g : IEnv (A.Dom W) Γ) :
    A.Holds h (box p) g ↔ ∀ {V : C} (k : W ⟶ V), A.Holds (h ≫ k) p (A.push k g) := by
  rw [box, A.holds_eq M, A.sem_top M, Set.eq_univ_iff_forall]
  constructor
  · intro H V k
    exact (A.mem_sem_iff h g p k).1 (H ⟨V, PUnit.unit, k⟩)
  · rintro H ⟨V, ⟨⟩, k⟩
    exact (A.mem_sem_iff h g p k).2 (H k)

/-- `A, h, g ⊩ ◇P` iff `A, k∘h, k∘g ⊩ P` for some arrow `k` out of the object. -/
theorem holds_dia {Γ : Ctx} {W : C} (h : A.W₀ ⟶ W) (p : Formula Sig Γ) (g : IEnv (A.Dom W) Γ) :
    A.Holds h (dia p) g ↔ ∃ (V : C) (k : W ⟶ V), A.Holds (h ≫ k) p (A.push k g) := by
  rw [dia, A.holds_neg M, A.holds_eq M, A.sem_bot M, ← Ne, ← Set.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨⟨V, ⟨⟩, k⟩, hk⟩
    exact ⟨V, k, (A.mem_sem_iff h g p k).1 hk⟩
  · rintro ⟨V, k, hk⟩
    exact ⟨⟨V, PUnit.unit, k⟩, (A.mem_sem_iff h g p k).2 hk⟩

/-! ### Sentences at the base, and consistency

What a model verdict needs to become a fact about the theory: `⊥` fails, `¬P` holds iff
`P` fails, `□P` gives `P` (the identity arrow), and the consequences for the axiom sets
that hold in the model: they are consistent, and no sentence failing in the model is
their theorem. -/

theorem not_holds_bot : ¬ A.HoldsSentence Term.bot := fun h => by
  rw [HoldsSentence, Holds, A.sem_bot M] at h
  exact h

theorem holdsSentence_neg (p : Sentence Sig) :
    A.HoldsSentence (Term.neg p) ↔ ¬ A.HoldsSentence p := A.holds_neg M (𝟙 A.W₀) IEnv.nil p

/-- `T` at the base: `□P` holding gives `P` holding, at the identity arrow. -/
theorem holdsSentence_of_box {p : Sentence Sig} (h : A.HoldsSentence (Term.box p)) :
    A.HoldsSentence p := by
  have := (A.holds_box M _ _ _).1 h (𝟙 A.W₀)
  rw [Category.comp_id, IEnv.nil_eq (A.push (𝟙 A.W₀) IEnv.nil)] at this
  exact this

omit M in
theorem holdsAx_empty : A.HoldsAx AxiomSet.empty := fun _ h => h.elim

omit M in
theorem holdsAx_single {a : Sentence Sig} (h : A.HoldsSentence a) : A.HoldsAx (AxiomSet.single a) :=
  fun _ hb => hb ▸ h

omit M in
theorem holdsAx_union {Ax₁ Ax₂ : AxiomSet Sig} (h₁ : A.HoldsAx Ax₁) (h₂ : A.HoldsAx Ax₂) :
    A.HoldsAx (Ax₁ ∪ Ax₂) := fun a ha => ha.elim (h₁ a) (h₂ a)

/-- **An axiom set true in an intensional action model is consistent** with Classicism. -/
theorem _root_.Classicism.Meta.AxiomSet.Consistent.of_model {Ax : AxiomSet Sig}
    (h : A.HoldsAx Ax) : Ax.Consistent :=
  fun hb => A.not_holds_bot M (A.theoremWith_holds M h hb)

/-- A sentence failing in a model of `C ∪ Ax` is not a theorem of `C ∪ Ax`. -/
theorem not_theorem_of_model {Ax : AxiomSet Sig} (h : A.HoldsAx Ax) {p : Sentence Sig}
    (hp : ¬ A.HoldsSentence p) : ¬ Theorem (Meta.C.axioms ∪ Ax) p :=
  fun hd => hp (A.theoremWith_holds M h hd)

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
        ((⟨W, PUnit.unit, 𝟙 W⟩ : Tuple A.inner .t W) ∈ A.incl .t W p ↔
          (⟨W, PUnit.unit, 𝟙 W⟩ : Tuple A.inner .t W) ∈ A.incl .t W q) → p = q := by
  simp only [Sentence.fregean, A.holds_forall M, A.holds_imp M, A.holds_iff M, A.holds_eq M]
  constructor
  · intro H p q e
    exact A.Incl_injective _ W (H p q e)
  · intro H p q e
    exact congrArg (A.Incl _ W) (H p q e)

end Premodel

/-! ### Truncation

The truncation of a premodel by an arrow `h : W₀ → V` (Classicism, §"Maximalism"): the
same actions with `V` as base and each constant's value moved along `h`. The paper also
discards the objects with no arrow from `V`, which change nothing (see the docstring of
`Premodel`); keeping them makes the paper's transfer lemma `⟦A⟧_{A_h, i} = ⟦A⟧_{A, i∘h}`
an induction on the same category. Consequences: a truncation of a model is a model, and
`◇P` holds iff `P` holds in some truncation, `□P` iff in every one. -/

namespace Premodel

variable {C : Type} [SmallCategory C] (A : Premodel Sig C)

/-- The truncation of `A` by `h`. Reducible, so that its fields are `A`'s to the
elaborator. -/
abbrev truncate {V : C} (h : A.W₀ ⟶ V) : Premodel Sig C :=
  { A with W₀ := V, I := fun c => (A.inner _).map h (A.I c) }

variable {V : C} (h : A.W₀ ⟶ V)

theorem truncate_Incl (σ : Ty) (W : C) : (A.truncate h).Incl σ W = A.Incl σ W := by
  cases σ <;> rfl

theorem truncate_apply {σ : Ty} {ρ : RTy} {W : C} (F : Intension A.inner (.arr σ ρ) W)
    (x : Outer A.inner σ W) : (A.truncate h).apply F x = A.apply F x := by
  ext ⟨U, a, j⟩
  simp only [apply, Set.mem_ofPred_eq, truncate_Incl]

/-- The paper's transfer lemma: `⟦A⟧_{A_h, i} = ⟦A⟧_{A, i∘h}`. The readings of the
constants are `A`'s by `rfl`, being defined from the actions and the inclusion alone. -/
theorem sem_truncate :
    ∀ {Γ : Ctx} {σ : Ty} {W : C} (i : V ⟶ W) (t : Term Sig Γ σ) (g : IEnv (A.Dom W) Γ),
      (A.truncate h).sem i t g = A.sem (h ≫ i) t g
  | _, _, _, _, .var v, g => by
    show (A.truncate h).Incl _ _ (g.get v) = A.Incl _ _ (g.get v)
    rw [truncate_Incl]
  | _, _, _, i, .const c, _ => by
    show (A.truncate h).Incl _ _ ((A.inner _).map i ((A.inner _).map h (A.I c)))
      = A.Incl _ _ ((A.inner _).map (h ≫ i) (A.I c))
    rw [truncate_Incl, Functor.map_comp]; rfl
  | _, _, _, i, .app f a, g => by
    show (A.truncate h).apply ((A.truncate h).sem i f g) ((A.truncate h).sem i a g)
      = A.apply (A.sem (h ≫ i) f g) (A.sem (h ≫ i) a g)
    rw [truncate_apply, sem_truncate i f g, sem_truncate i a g]
  | _, _, _, i, .lam b, g => by
    ext ⟨U, ⟨x, a⟩, j⟩
    rw [mem_sem_lam, mem_sem_lam, sem_truncate (i ≫ j) b, Category.assoc]
  | _, _, _, _, .and, _ | _, _, _, _, .or, _ | _, _, _, _, .not, _ | _, _, _, _, .all _, _
  | _, _, _, _, .ex _, _ | _, _, _, _, .eq _, _ | _, _, _, _, .constR _, _ | _, _, _, _, .negR _, _
  | _, _, _, _, .andR _, _ | _, _, _, _, .orR _, _ | _, _, _, _, .coextR _, _ | _, _, _, _, .boxR _, _
  | _, _, _, _, .boxImpR _, _ => rfl

theorem isModel_truncate (M : A.IsModel) : (A.truncate h).IsModel :=
  fun i t g => by rw [A.sem_truncate h, A.truncate_Incl h]; exact M (h ≫ i) t g

theorem holds_truncate {Γ : Ctx} {W : C} (i : V ⟶ W) (p : Formula Sig Γ)
    (g : IEnv (A.Dom W) Γ) : (A.truncate h).Holds i p g ↔ A.Holds (h ≫ i) p g := by
  unfold Holds; rw [A.sem_truncate h]

theorem holdsSentence_truncate (p : Sentence Sig) :
    (A.truncate h).HoldsSentence p ↔ A.Holds h p .nil := by
  rw [HoldsSentence, A.holds_truncate h, Category.comp_id]

/-- **`◇P` holds in `A` iff `P` holds in one of its truncations.** -/
theorem dia_iff_truncate (M : A.IsModel) (p : Sentence Sig) :
    A.HoldsSentence (dia p) ↔ ∃ (V : C) (h : A.W₀ ⟶ V), (A.truncate h).HoldsSentence p := by
  rw [HoldsSentence, A.holds_dia M]
  constructor
  · rintro ⟨V, k, hk⟩
    refine ⟨V, k, ?_⟩
    rw [A.holdsSentence_truncate]
    rw [Category.id_comp, IEnv.nil_eq (A.push k IEnv.nil)] at hk
    exact hk
  · rintro ⟨V, k, hk⟩
    refine ⟨V, k, ?_⟩
    rw [A.holdsSentence_truncate] at hk
    rw [Category.id_comp, IEnv.nil_eq (A.push k IEnv.nil)]
    exact hk

/-- **`□P` holds in `A` iff `P` holds in every truncation.** -/
theorem box_iff_truncate (M : A.IsModel) (p : Sentence Sig) :
    A.HoldsSentence (box p) ↔ ∀ (V : C) (h : A.W₀ ⟶ V), (A.truncate h).HoldsSentence p := by
  rw [HoldsSentence, A.holds_box M]
  constructor
  · intro H V k
    rw [A.holdsSentence_truncate]
    have := H k
    rw [Category.id_comp, IEnv.nil_eq (A.push k IEnv.nil)] at this
    exact this
  · intro H V k
    have := H V k
    rw [A.holdsSentence_truncate] at this
    rw [Category.id_comp, IEnv.nil_eq (A.push k IEnv.nil)]
    exact this

end Premodel

end Classicism.Meta.Intensional
