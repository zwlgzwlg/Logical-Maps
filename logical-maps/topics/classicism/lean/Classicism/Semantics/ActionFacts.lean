import Classicism.Semantics.ActionSoundness

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

theorem sem_bot {Γ : Ctx} {W : C} (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ) :
    A.sem h (bot : Formula Sig Γ) g = ∅ := by
  rw [bot, A.sem_conj M, A.sem_neg M]
  exact Set.inter_compl_self _

/-- `A, h, g ⊩ ◇P` iff `A, k∘h, k∘g ⊩ P` for some arrow `k` out of the object. -/
theorem holds_dia {Γ : Ctx} {W : C} (h : A.W₀ ⟶ W) (p : Formula Sig Γ) (g : IEnv (A.Dom W) Γ) :
    A.Holds h (dia p) g ↔ ∃ (V : C) (k : W ⟶ V), A.Holds (h ≫ k) p (A.push k g) := by
  rw [dia, A.holds_neg M, A.holds_eq M, A.sem_bot M, ← Ne, ← Set.nonempty_iff_ne_empty]
  constructor
  · rintro ⟨⟨V, k⟩, hk⟩
    exact ⟨V, k, (A.mem_sem_iff M h g p k).1 hk⟩
  · rintro ⟨V, k, hk⟩
    exact ⟨⟨V, k⟩, (A.mem_sem_iff M h g p k).2 hk⟩

/-! ### Sentences at the root, and consistency

What a model verdict needs to become a fact about the theory: `⊥` fails, `¬P` holds iff
`P` fails, `□P` gives `P` (the identity arrow), and the consequences for the axiom sets
that hold in the model — they are consistent, and no sentence failing in the model is
their theorem. -/

theorem not_holds_bot : ¬ A.HoldsSentence Term.bot := fun h => by
  rw [HoldsSentence, Holds, A.sem_bot M] at h
  exact h

theorem holdsSentence_neg (p : Sentence Sig) :
    A.HoldsSentence (Term.neg p) ↔ ¬ A.HoldsSentence p := A.holds_neg M (𝟙 A.W₀) IEnv.nil p

/-- `T` at the root: `□P` holding gives `P` holding, at the identity arrow. -/
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

/-- **An axiom set true in an action model is consistent** with Classicism. -/
theorem _root_.Classicism.Meta.AxiomSet.Consistent.of_model {Ax : AxiomSet Sig} (h : A.HoldsAx Ax) :
    Ax.Consistent := fun hb => A.not_holds_bot M (A.theoremWith_holds M h hb)

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
        ((⟨W, 𝟙 W⟩ : Σ V, W ⟶ V) ∈ A.incl .t W p ↔ (⟨W, 𝟙 W⟩ : Σ V, W ⟶ V) ∈ A.incl .t W q) → p = q := by
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

/-! The readings depend on the actions and the inclusion only, not on the base or the
constants; but as functions of the whole premodel, stuck at a type variable, Lean cannot
see that, so each is transferred by hand. -/

theorem truncate_Incl (σ : Ty) (W : C) : (A.truncate h).Incl σ W = A.Incl σ W := by
  cases σ <;> rfl

theorem truncate_dflt : ∀ (σ : Ty) (W : C), (A.truncate h).dflt σ W = A.dflt σ W
  | .e, _ => by simp only [dflt]
  | .rel .t, _ => by simp only [dflt]
  | .rel (.arr _ ρ), _ => by
    simp only [dflt]
    funext U _ _
    exact truncate_dflt (.rel ρ) U

theorem truncate_apply {σ : Ty} {ρ : RTy} {W : C} (F : RawR A.inner (.arr σ ρ) W)
    (x : RawT A.inner σ W) : (A.truncate h).apply F x = A.apply F x := by
  by_cases hx : x ∈ Set.range (A.Incl σ W)
  · obtain ⟨b, rfl⟩ := hx
    rw [A.apply_Incl, ← congrFun (truncate_Incl A h σ W) b, (A.truncate h).apply_Incl]
  · have hx' : x ∉ Set.range ((A.truncate h).Incl σ W) := by rw [truncate_Incl A h]; exact hx
    unfold apply
    rw [dif_neg hx, dif_neg hx', truncate_dflt]

theorem truncate_andRead (W : C) : (A.truncate h).andRead W = A.andRead W := rfl
theorem truncate_orRead (W : C) : (A.truncate h).orRead W = A.orRead W := rfl
theorem truncate_notRead (W : C) : (A.truncate h).notRead W = A.notRead W := rfl
theorem truncate_allRead (σ : Ty) (W : C) : (A.truncate h).allRead σ W = A.allRead σ W := rfl
theorem truncate_exRead (σ : Ty) (W : C) : (A.truncate h).exRead σ W = A.exRead σ W := rfl
theorem truncate_eqRead (σ : Ty) (W : C) : (A.truncate h).eqRead σ W = A.eqRead σ W := rfl

theorem truncate_topRead (W : C) : (A.truncate h).topRead W = A.topRead W := by
  simp only [topRead, truncate_apply, truncate_allRead, truncate_orRead, truncate_notRead]

theorem truncate_constRead : ∀ (ρ : RTy) (W : C), (A.truncate h).constRead ρ W = A.constRead ρ W
  | .t, _ => rfl
  | .arr _ ρ, _ => by
    funext _ _ _ U _ _
    simp only [constRead, truncate_apply, truncate_constRead ρ U]

theorem truncate_negRead : ∀ (ρ : RTy) (W : C), (A.truncate h).negRead ρ W = A.negRead ρ W
  | .t, _ => rfl
  | .arr _ ρ, _ => by
    funext _ _ _ U _ _
    simp only [negRead, truncate_apply, truncate_negRead ρ U, truncate_Incl]

theorem truncate_andRRead : ∀ (ρ : RTy) (W : C), (A.truncate h).andRRead ρ W = A.andRRead ρ W
  | .t, _ => rfl
  | .arr _ ρ, _ => by
    funext _ _ _ _ _ _ T _ _
    simp only [andRRead, truncate_apply, truncate_andRRead ρ T, truncate_Incl]

theorem truncate_orRRead : ∀ (ρ : RTy) (W : C), (A.truncate h).orRRead ρ W = A.orRRead ρ W
  | .t, _ => rfl
  | .arr _ ρ, _ => by
    funext _ _ _ _ _ _ T _ _
    simp only [orRRead, truncate_apply, truncate_orRRead ρ T, truncate_Incl]

theorem truncate_coextRead : ∀ (ρ : RTy) (W : C), (A.truncate h).coextRead ρ W = A.coextRead ρ W
  | .t, _ => by
    funext _ _ _ U _ _
    simp only [coextRead, truncate_apply, truncate_andRead, truncate_orRead, truncate_notRead]
  | .arr _ ρ, _ => by
    funext _ _ _ U _ _
    simp only [coextRead, truncate_apply, truncate_allRead, truncate_coextRead ρ, truncate_Incl]

theorem truncate_boxRead : ∀ (ρ : RTy) (W : C), (A.truncate h).boxRead ρ W = A.boxRead ρ W
  | .t, _ => by
    funext V _ _
    simp only [boxRead, truncate_apply, truncate_eqRead, truncate_topRead]
  | .arr _ ρ, _ => by
    funext _ _ _ U _ _
    simp only [boxRead, truncate_apply, truncate_boxRead ρ U, truncate_Incl]

theorem truncate_boxImpRead : ∀ (ρ : RTy) (W : C), (A.truncate h).boxImpRead ρ W = A.boxImpRead ρ W
  | .t, _ => by
    funext _ _ _ U _ _
    simp only [boxImpRead, truncate_apply, truncate_orRead, truncate_notRead]
  | .arr _ ρ, _ => by
    funext _ _ _ U _ _
    simp only [boxImpRead, truncate_apply, truncate_allRead, truncate_boxImpRead ρ, truncate_Incl]

/-- The paper's transfer lemma: `⟦A⟧_{A_h, i} = ⟦A⟧_{A, i∘h}`. -/
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
    show (fun U j x => (A.truncate h).sem (i ≫ j) b (.cons x (A.push j g)))
      = (fun U j x => A.sem ((h ≫ i) ≫ j) b (.cons x (A.push j g)))
    funext U j x
    exact (sem_truncate (i ≫ j) b _).trans
      (congrArg (fun k => A.sem k b (.cons x (A.push j g))) (Category.assoc h i j).symm)
  | _, _, _, _, .and, _ => truncate_andRead A h _
  | _, _, _, _, .or, _ => truncate_orRead A h _
  | _, _, _, _, .not, _ => truncate_notRead A h _
  | _, _, _, _, .all σ, _ => truncate_allRead A h σ _
  | _, _, _, _, .ex σ, _ => truncate_exRead A h σ _
  | _, _, _, _, .eq σ, _ => truncate_eqRead A h σ _
  | _, _, _, _, .constR ρ, _ => truncate_constRead A h ρ _
  | _, _, _, _, .negR ρ, _ => truncate_negRead A h ρ _
  | _, _, _, _, .andR ρ, _ => truncate_andRRead A h ρ _
  | _, _, _, _, .orR ρ, _ => truncate_orRRead A h ρ _
  | _, _, _, _, .coextR ρ, _ => truncate_coextRead A h ρ _
  | _, _, _, _, .boxR ρ, _ => truncate_boxRead A h ρ _
  | _, _, _, _, .boxImpR ρ, _ => truncate_boxImpRead A h ρ _

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

end Classicism.Meta
