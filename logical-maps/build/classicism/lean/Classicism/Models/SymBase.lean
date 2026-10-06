import Classicism.Semantics.Symmetric
import Classicism.Models.Functions
import Classicism.Models.Conditions
import Classicism.Semantics.Numerals

/-!
# Bases of symmetric ideally full models, and the group's arguments

A **base** (Dorr's Definition 15) is a category of sets and functions, with the identity
action for `e`, a base object, and at each object a group of permutations among its arrows
(`SymBase`). Its model is the symmetric ideally full premodel (`SymBase.model`), a model by
Proposition 20.

The map's group `symmetric-ideally-full` takes a base as its parameter; each of its
conditions is a predicate on bases, and each of its shared arguments a theorem about every
base meeting the argument's conditions.

- `actuality`: when the symmetry group, as a proposition, is finitely pinned
  (`SymmetryGroupPinned`), it is in the domain, true, and below every truth, so Actuality
  holds (`actuality_of_pinned`, through `Premodel.holds_actuality_of`).
-/

namespace Classicism.Meta.Intensional

open CategoryTheory

/-! ### Actuality from a true proposition below every truth -/

namespace Premodel

variable {C : Type} [SmallCategory C]

/-- **Actuality holds** where some proposition in the domain is true and entails every truth. -/
theorem holds_actuality_of {B : Premodel Signature.pure C} (M : B.IsModel) (a : B.Dom B.W₀ (.rel .t))
    (ha : (⟨B.W₀, PUnit.unit, 𝟙 B.W₀⟩ : Tuple B.inner .t B.W₀) ∈ B.incl .t B.W₀ a)
    (hle : ∀ p : B.Dom B.W₀ (.rel .t), (⟨B.W₀, PUnit.unit, 𝟙 B.W₀⟩ : Tuple B.inner .t B.W₀) ∈ B.incl .t B.W₀ p →
      B.incl .t B.W₀ a ⊆ B.incl .t B.W₀ p) :
    B.HoldsSentence P.Actuality.quoted := by
  rw [HoldsSentence]
  unfold P.Actuality.quoted
  rw [B.holds_exists M]
  refine ⟨a, ?_⟩
  rw [B.holds_conj M, B.holds_forall M]
  refine ⟨ha, fun q => ?_⟩
  rw [B.holds_imp M, B.holds_eq M, B.sem_disj M]
  intro hq
  show B.Incl (.rel .t) B.W₀ q = B.Incl (.rel .t) B.W₀ a ∪ B.Incl (.rel .t) B.W₀ q
  exact (Set.union_eq_right.2 (hle q hq)).symm

end Premodel


/-! ### Pullbacks along an arrow out of the base -/

namespace Premodel

variable {C : Type} [SmallCategory C] {Sig : Signature} (B : Premodel Sig C)

/-- The tuples at arrows out of the base agreeing on `X` with `k` followed by an arrow `j` for
which the tuple, at `j`, is in `b` (the ideally full models' `pullback`, for any premodel). -/
def pullbackG {ρ : RTy} {V : C} (k : B.W₀ ⟶ V) (X : Set (B.Dom B.W₀ .e)) (b : Intension B.inner ρ V) :
    Intension B.inner ρ B.W₀ :=
  {p | ∃ j : V ⟶ p.1, AgreeOn (B.inner .e) X p.2.2 (k ≫ j) ∧ (⟨p.1, p.2.1, j⟩ : Tuple B.inner ρ V) ∈ b}

variable {B}

theorem pullbackG_pinned {ρ : RTy} {V : C} (k : B.W₀ ⟶ V) (X : Set (B.Dom B.W₀ .e))
    (b : Intension B.inner ρ V) : B.PinnedO (.rel ρ) X (B.pullbackG k X b) := by
  intro U h i ha
  simp only [Outer.map_rel]
  ext ⟨T, a, l⟩
  simp only [Intension.mem_map, pullbackG, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j, hj, hb⟩
    exact ⟨j, ((ha.comp_right _ l).symm _).trans _ hj, hb⟩
  · rintro ⟨j, hj, hb⟩
    exact ⟨j, (ha.comp_right _ l).trans _ hj, hb⟩

theorem map_pullbackG {ρ : RTy} {V : C} (k : B.W₀ ⟶ V) {X : Set (B.Dom B.W₀ .e)} {Y : Set (B.Dom V .e)}
    (hXY : (B.inner .e).map k '' X = Y) {b : Intension B.inner ρ V} (hb : B.PinnedO (.rel ρ) Y b) :
    Intension.map B.inner k (B.pullbackG k X b) = b := by
  subst hXY
  ext ⟨T, a, l⟩
  simp only [Intension.mem_map, pullbackG, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j, hj, hb'⟩
    have e := hb T l j (by
      rintro y ⟨x, hx, rfl⟩
      have := hj x hx
      simpa [Functor.map_comp, types_comp_apply] using this)
    simp only [Outer.map_rel] at e
    have := congrArg (fun S : Intension B.inner ρ T => (⟨T, a, 𝟙 T⟩ : Tuple B.inner ρ T) ∈ S) e
    simp only [Intension.mem_map, Category.comp_id] at this
    exact this.mpr hb'
  · intro hb'
    exact ⟨l, AgreeOn.refl _ _ _, hb'⟩

/-- The pullback of a symmetric intension is symmetric: a symmetry moves the witness along. -/
theorem pullbackG_sym {G : ∀ V : C, Set (V ⟶ V)} {ρ : RTy} {V : C} (k : B.W₀ ⟶ V) (X : Set (B.Dom B.W₀ .e))
    {b : Intension B.inner ρ V} (hb : B.Sym G b) : B.Sym G (B.pullbackG k X b) := by
  rintro U a i g hg ⟨j, hj, hjb⟩
  refine ⟨j ≫ g, ?_, hb U a j g hg hjb⟩
  have := hj.comp_right _ g
  simpa [Category.assoc] using this

end Premodel

/-! ### Bases -/

/-- **A base** (Definition 15): a category of sets and functions, a base object with every
domain nonempty, and at each object a group of permutations among its arrows. -/
structure SymBase where
  F : FunCat
  G : ∀ V : F.Ob, Set (V ⟶ V)
  G_id : ∀ V, 𝟙 V ∈ G V
  G_comp : ∀ {V} {g s : V ⟶ V}, g ∈ G V → s ∈ G V → g ≫ s ∈ G V
  G_inv : SymGroup G
  W₀ : F.Ob
  ne : ∀ i, Nonempty (F.X i)

namespace SymBase

variable (S : SymBase)

/-- **The symmetric ideally full model of a base** (Definition 18). -/
noncomputable abbrev model : Premodel Signature.pure S.F.Ob :=
  Premodel.symIdeal S.F.De S.G S.W₀ S.ne (fun c => nomatch c)

theorem model_isModel : S.model.IsModel := symIdeal_isModel S.G_inv

/-- The symmetry group at the base object, as a proposition: the tuples of its members. -/
def groupProp : Intension (SymT S.F.De S.G) .t S.W₀ :=
  {p | ∃ g ∈ S.G S.W₀, p = (⟨S.W₀, PUnit.unit, g⟩ : Tuple (SymT S.F.De S.G) .t S.W₀)}

/-- `symmetry-group-pinned`: the symmetry group, the smallest symmetric set of arrows
containing the identity, is pinned down by a finite set. -/
def SymmetryGroupPinned : Prop :=
  ∃ N : Set (S.F.X S.W₀), N.Finite ∧ ∀ (V : S.F.Ob) (h i : S.W₀ ⟶ V), AgreeOn S.F.De N h i →
    Intension.map (SymT S.F.De S.G) h S.groupProp = Intension.map (SymT S.F.De S.G) i S.groupProp

variable {S}

theorem groupProp_sym : SymCond S.F.De S.G S.groupProp := by
  rintro V a k s hs ⟨g, hg, he⟩
  cases he
  exact ⟨g ≫ s, S.G_comp hg hs, rfl⟩

/-- **The group's argument `actuality`**: the symmetry group, finitely pinned, is a true
proposition in the domain entailing every truth. -/
theorem actuality_of_pinned (h : S.SymmetryGroupPinned) : S.model.HoldsSentence P.Actuality.quoted := by
  obtain ⟨a, ha⟩ := (mem_range_symIncl S.F.De S.G .t S.W₀ S.groupProp).2 ⟨h, groupProp_sym⟩
  have ha' : S.model.incl .t S.W₀ a = S.groupProp := ha
  refine Premodel.holds_actuality_of S.model_isModel a ?_ fun p hp => ?_
  · show (⟨S.W₀, PUnit.unit, 𝟙 S.W₀⟩ : Tuple (SymT S.F.De S.G) .t S.W₀) ∈ S.model.incl .t S.W₀ a
    rw [ha']; exact ⟨𝟙 _, S.G_id _, rfl⟩
  · show S.model.incl .t S.W₀ a ⊆ S.model.incl .t S.W₀ p
    rw [ha']
    rintro _ ⟨g, hg, rfl⟩
    exact Premodel.Sym.at_id (symIdeal_domSym .t S.W₀ p) PUnit.unit hg hp

/-! ### `barcan-fixes-or-omits` -/

variable (S) in
/-- `fixes-or-omits`: there is a distinguished individual at each object, fixed by the
symmetries there, such that every arrow out of the base either sends the base's to the
target's or omits the target's from its range, and some arrow does not send it there. -/
def FixesOrOmits : Prop :=
  ∃ d : ∀ V : S.F.Ob, S.F.X V,
    (∀ V (g : V ⟶ V), g ∈ S.G V → FunCat.fn g (d V) = d V) ∧
    (∀ V (k : S.W₀ ⟶ V), FunCat.fn k (d S.W₀) = d V ∨ ∀ x, FunCat.fn k x ≠ d V) ∧
    ∃ V, ∃ k : S.W₀ ⟶ V, FunCat.fn k (d S.W₀) ≠ d V

/-- The property of being other than the distinguished individual unless the world's arrow
sends the base's distinguished individual to it. -/
def fixedProp (d : ∀ V : S.F.Ob, S.F.X V) : Intension (SymT S.F.De S.G) (.arr .e .t) S.W₀ :=
  {p | FunCat.fn p.2.2 (d S.W₀) = d p.1 ∨ p.2.1.1 ≠ d p.1}

theorem fixedProp_mem (d : ∀ V : S.F.Ob, S.F.X V)
    (hd : ∀ V (g : V ⟶ V), g ∈ S.G V → FunCat.fn g (d V) = d V) :
    fixedProp d ∈ Set.range (S.model.incl (.arr .e .t) S.W₀) := by
  refine (mem_range_symIncl S.F.De S.G _ S.W₀ _).2 ⟨⟨{d S.W₀}, Set.finite_singleton _, fun V h i ha => ?_⟩, ?_⟩
  · have e : FunCat.fn h (d S.W₀) = FunCat.fn i (d S.W₀) := ha _ rfl
    ext ⟨U, ⟨y, ⟨⟩⟩, j⟩
    show FunCat.fn j (FunCat.fn h (d S.W₀)) = d U ∨ y ≠ d U ↔ FunCat.fn j (FunCat.fn i (d S.W₀)) = d U ∨ y ≠ d U
    rw [e]
  · rintro V ⟨y, ⟨⟩⟩ k g hg (hk : FunCat.fn k (d S.W₀) = d V ∨ y ≠ d V)
    show FunCat.fn g (FunCat.fn k (d S.W₀)) = d V ∨ FunCat.fn g y ≠ d V
    obtain ⟨g', hg', e₁, -⟩ := S.G_inv V g hg
    have hinj : Function.Injective (FunCat.fn g) := fun a b e => by
      have := congrArg (FunCat.fn g') e
      have e₁' := congrArg FunCat.fn e₁
      exact (congrFun e₁' a).symm.trans (this.trans (congrFun e₁' b))
    rcases hk with hk | hk
    · exact Or.inl (by rw [hk, hd V g hg])
    · exact Or.inr fun e => hk (hinj (e.trans (hd V g hg).symm))

/-- **The group's argument `barcan-fixes-or-omits`**: BF at `e` fails. Every individual
necessarily has the property, since an arrow either sends the distinguished individual to
the distinguished one or omits that from its range; but under an arrow that does neither the
distinguished individual lacks it. -/
theorem not_bf_e_of_fixesOrOmits (h : S.FixesOrOmits) : ¬ S.model.HoldsSentence (Sentence.bf .e) := by
  obtain ⟨d, hd, hfo, V₁, k₁, hk₁⟩ := h
  intro H
  have Mo : S.model.IsModel := S.model_isModel
  rw [Premodel.HoldsSentence, Sentence.bf, S.model.holds_forall Mo] at H
  obtain ⟨X, hX⟩ := fixedProp_mem d hd
  have hX' : S.model.incl (.arr .e .t) S.model.W₀ X = fixedProp d := hX
  have H := H X
  rw [S.model.holds_imp Mo] at H
  have H := H (by
    rw [S.model.holds_forall Mo]
    intro y
    rw [S.model.holds_box Mo]
    intro V k
    rw [S.model.holds_app (Γ := [Ty.e, Ty.rel (.arr .e .t)]) (σ := .e) (𝟙 S.model.W₀ ≫ k) _ Term.v1 Term.v0
      (a' := FunCat.fn k y) rfl]
    simp only [Premodel.push]
    show (⟨V, (FunCat.fn k y, PUnit.unit), 𝟙 V⟩ : Tuple S.model.inner (.arr .e .t) V)
      ∈ S.model.incl _ V ((S.model.inner _).map k X)
    erw [S.model.incl_map, Intension.mem_map, Category.comp_id, hX']
    show FunCat.fn k (d S.W₀) = d V ∨ FunCat.fn k y ≠ d V
    exact (hfo V k).imp_right fun h => h y)
  rw [S.model.holds_box Mo] at H
  have H := @H V₁ k₁
  rw [S.model.holds_forall Mo] at H
  have H := H (d V₁)
  rw [S.model.holds_app (Γ := [Ty.e, Ty.rel (.arr .e .t)]) (σ := .e) (𝟙 S.model.W₀ ≫ k₁) _
    Term.v1 Term.v0 (a' := d V₁) rfl] at H
  simp only [Premodel.push] at H
  change (⟨V₁, (d V₁, PUnit.unit), 𝟙 V₁⟩ : Tuple S.model.inner (.arr .e .t) V₁)
    ∈ S.model.incl _ V₁ ((S.model.inner _).map k₁ X) at H
  erw [S.model.incl_map, Intension.mem_map, Category.comp_id, hX'] at H
  change FunCat.fn k₁ (d S.W₀) = d V₁ ∨ d V₁ ≠ d V₁ at H
  exact H.elim hk₁ fun h => h rfl

/-! ### `relational-choice` -/

variable (S) in
/-- `transposable`: for each finite set `N` of individuals at the base, some property in the
domain has a nonempty extension there, and each individual in its extension is moved by a
symmetry that fixes `N` pointwise and fixes the property. -/
def Transposable : Prop :=
  ∀ N : Set (S.F.X S.W₀), N.Finite → ∃ A : S.model.Dom S.W₀ (.rel (.arr .e .t)),
    (∃ y, (⟨S.W₀, (y, PUnit.unit), 𝟙 S.W₀⟩ : Tuple S.model.inner (.arr .e .t) S.W₀) ∈ S.model.incl _ S.W₀ A) ∧
    ∀ y, (⟨S.W₀, (y, PUnit.unit), 𝟙 S.W₀⟩ : Tuple S.model.inner (.arr .e .t) S.W₀) ∈ S.model.incl _ S.W₀ A →
      ∃ g ∈ S.G S.W₀, AgreeOn S.F.De N g (𝟙 S.W₀) ∧ (S.model.inner _).map g A = A ∧ FunCat.fn g y ≠ y

/-- `U := λX y. X y ∨ ¬∃z. X z`, as an intension: blind to the arrow. -/
def choiceRel : Intension (SymT S.F.De S.G) (.arr (.rel (.arr .e .t)) (.arr .e .t)) S.W₀ :=
  {p | (⟨p.1, (p.2.1.2.1, PUnit.unit), 𝟙 p.1⟩ : Tuple (SymT S.F.De S.G) (.arr .e .t) p.1) ∈
      symIncl S.F.De S.G _ p.1 p.2.1.1 ∨
    ∀ z, (⟨p.1, (z, PUnit.unit), 𝟙 p.1⟩ : Tuple (SymT S.F.De S.G) (.arr .e .t) p.1) ∉ symIncl S.F.De S.G _ p.1 p.2.1.1}

theorem model_domSym : S.model.DomSym S.G := symIdeal_domSym

theorem choiceRel_mem : choiceRel (S := S) ∈ Set.range (S.model.incl _ S.W₀) := by
  refine (mem_range_symIncl S.F.De S.G _ S.W₀ _).2 ⟨⟨∅, Set.finite_empty, fun V h i _ => ?_⟩, ?_⟩
  · ext ⟨U, a, k⟩; exact Iff.rfl
  · rintro V ⟨A, y, ⟨⟩⟩ k g hg hp
    have hA := model_domSym (S := S) (.arr .e .t) V A
    obtain ⟨g', -, -, e₂⟩ := S.G_inv V g hg
    show (⟨V, ((S.model.inner .e).map g y, PUnit.unit), 𝟙 V⟩ : Tuple S.model.inner (.arr .e .t) V) ∈
        S.model.incl (.arr .e .t) V ((S.model.inner (.rel (.arr .e .t))).map g A) ∨
      ∀ z, (⟨V, (z, PUnit.unit), 𝟙 V⟩ : Tuple S.model.inner (.arr .e .t) V) ∉
        S.model.incl (.arr .e .t) V ((S.model.inner (.rel (.arr .e .t))).map g A)
    simp only [Premodel.mem_incl_map_id]
    rcases hp with hp | hp
    · exact Or.inl (Premodel.Sym.at_id hA (y, PUnit.unit) hg hp)
    · refine Or.inr fun z hz => hp ((S.model.inner .e).map g' z) ?_
      show (⟨V, ((S.model.inner .e).map g' z, PUnit.unit), 𝟙 V⟩ : Tuple S.model.inner (.arr .e .t) V) ∈
        S.model.incl (.arr .e .t) V A
      rw [← Premodel.Sym.at_id_iff S.G_inv hA _ hg]
      show (⟨V, ((S.model.inner .e).map g ((S.model.inner .e).map g' z), PUnit.unit), g⟩ :
        Tuple S.model.inner (.arr .e .t) V) ∈ _
      rw [S.model.map_map_inv e₂]
      exact hz

/-- **The group's argument `relational-choice`**: Relational Choice fails at `(e → t)` and `e`.
`U := λX y. X y ∨ ¬∃z. X z` is serial; a functional subrelation `R` of it is pinned down by a
finite `N`, so a symmetry fixing `N` pointwise fixes `R` (Lemma 19(iv)), and symmetry carries
`R A y` to `R (g A) (g y)`; for the `A` and `g` the condition gives, `g A = A` and `g y ≠ y`. -/
theorem not_rc_of_transposable (hT : S.Transposable) :
    ¬ S.model.HoldsSentence (P.RelationalChoice.quoted (.rel (.arr .e .t)) .e) := by
  have M : S.model.IsModel := S.model_isModel
  simp only [Premodel.HoldsSentence, P.RelationalChoice.quoted, S.model.holds_forall M, S.model.holds_imp M,
    S.model.holds_exists M, S.model.holds_conj M, Premodel.holds_app_var2, Premodel.holds_eq_var M, IEnv.get]
  intro H
  obtain ⟨U, hU⟩ := choiceRel_mem (S := S)
  obtain ⟨R, hfun, hsub⟩ := H U fun A => by
    by_cases hne : ∃ z, (⟨S.W₀, (z, PUnit.unit), 𝟙 S.W₀⟩ : Tuple S.model.inner (.arr .e .t) S.W₀) ∈
        S.model.incl _ S.W₀ A
    · obtain ⟨z, hz⟩ := hne
      exact ⟨z, by show _ ∈ S.model.incl _ S.W₀ U; rw [hU]; exact Or.inl hz⟩
    · obtain ⟨z⟩ := S.ne S.W₀
      exact ⟨z, by show _ ∈ S.model.incl _ S.W₀ U; rw [hU]; exact Or.inr fun z' hz' => hne ⟨z', hz'⟩⟩
  obtain ⟨N, hN, hpin⟩ := symIdeal_inner_finPinned (De := S.F.De) (G := S.G) (W₀ := S.W₀)
    (nonempty_e := S.ne) (I := S.model.I) (.rel _) S.W₀ R
  obtain ⟨A, ⟨y₀, hy₀⟩, hmove⟩ := hT N hN
  obtain ⟨y, hRy, huniq⟩ := hfun A
  have hyA : (⟨S.W₀, (y, PUnit.unit), 𝟙 S.W₀⟩ : Tuple S.model.inner (.arr .e .t) S.W₀) ∈
      S.model.incl _ S.W₀ A := by
    have h := hsub A y hRy
    change _ ∈ S.model.incl _ S.W₀ U at h
    rw [hU] at h
    exact h.resolve_right fun h' => h' y₀ hy₀
  obtain ⟨g, hg, hag, hgA, hgy⟩ := hmove y hyA
  -- symmetry: `R A y` at the identity gives `R (g A) (g y)` at `g`
  have h1 := Premodel.Sym.at_id (model_domSym (S := S) _ S.W₀ R) (A, (y, PUnit.unit)) hg hRy
  -- pinning: `g` agrees with the identity on `N`, so it fixes `R`
  have h2 : Intension.map S.model.inner g (S.model.incl _ S.W₀ R) = S.model.incl _ S.W₀ R := by
    have := hpin S.W₀ g (𝟙 _) hag
    simp only [Outer.map_rel, Intension.map_id] at this
    exact this
  have h3 : (⟨S.W₀, ((S.model.inner _).map g A, ((S.model.inner .e).map g y, PUnit.unit)), 𝟙 S.W₀⟩ :
      Tuple S.model.inner (.arr (.rel (.arr .e .t)) (.arr .e .t)) S.W₀) ∈ S.model.incl _ S.W₀ R := by
    rw [← h2, Intension.mem_map, Category.comp_id]
    exact h1
  rw [hgA] at h3
  exact hgy (huniq _ h3).symm

/-! ### The Axiom of Infinity -/

/-- The cardinalities all of whose instances are finite: blind to the arrow. -/
def finCards (σ : Ty) : Intension (SymT S.F.De S.G) (.arr (tC σ) .t) S.W₀ :=
  {p | ∀ P : S.model.Dom p.1 (tP σ), Premodel.holdsOf (B := S.model) (W := p.1) p.2.1.1 P →
    (Premodel.pext (B := S.model) P).Finite}

theorem finCards_mem (σ : Ty) : finCards (S := S) σ ∈ Set.range (S.model.incl _ S.W₀) := by
  refine (mem_range_symIncl S.F.De S.G _ S.W₀ _).2 ⟨⟨∅, Set.finite_empty, fun V h i _ => ?_⟩, ?_⟩
  · ext ⟨U, a, k⟩; exact Iff.rfl
  · rintro V ⟨Z, ⟨⟩⟩ k g hg (hZ : ∀ P, _ → _)
    intro P hP
    obtain ⟨g', hg', -, e₂⟩ := S.G_inv V g hg
    -- `g Z` holds of `P` iff `Z` holds of `g⁻¹ P`
    have h1 : Premodel.holdsOf (B := S.model) (W := V) Z ((S.model.inner _).map g' P) := by
      have hP' : (⟨V, (P, PUnit.unit), 𝟙 V⟩ : Tuple S.model.inner (.arr (tP σ) .t) V) ∈
          S.model.incl (.arr (tP σ) .t) V ((S.model.inner (.rel (.arr (tP σ) .t))).map g Z) := hP
      rw [Premodel.mem_incl_map_id (B := S.model) (ρ := .arr (tP σ) .t) Z, ← S.model.map_map_inv e₂ P] at hP'
      exact (Premodel.Sym.at_id_iff S.G_inv (model_domSym (S := S) (.arr (tP σ) .t) V Z) (_, PUnit.unit) hg).1 hP'
    have hfin := hZ _ h1
    -- and the extension of `P` is the preimage of that of `g⁻¹ P` under `g⁻¹`
    have hinj : Function.Injective ((S.model.inner σ).map g') := fun a b e => by
      rw [← S.model.map_map_inv e₂ a, ← S.model.map_map_inv e₂ b, e]
    refine (hfin.preimage hinj.injOn).subset fun u hu => ?_
    have hu' : (⟨V, (u, PUnit.unit), 𝟙 V⟩ : Tuple S.model.inner (.arr σ .t) V) ∈
        S.model.incl (.arr σ .t) V P := hu
    show (⟨V, ((S.model.inner σ).map g' u, PUnit.unit), 𝟙 V⟩ : Tuple S.model.inner (.arr σ .t) V) ∈
      S.model.incl (.arr σ .t) V ((S.model.inner (.rel (.arr σ .t))).map g' P)
    rw [Premodel.mem_incl_map_id (B := S.model) (ρ := .arr σ .t) P]
    exact Premodel.Sym.at_id (model_domSym (S := S) (.arr σ .t) V P) (u, PUnit.unit) hg' hu'

/-- **The Axiom of Infinity at `σ` holds where there are infinitely many entities of type `σ`**:
the finite cardinalities' property is in the domain. -/
theorem holds_axInf (σ : Ty) [Infinite (S.model.Dom S.W₀ σ)] :
    S.model.Holds (𝟙 _) (axInf σ) .nil := by
  obtain ⟨X, hX⟩ := finCards_mem (S := S) σ
  have : Infinite (S.model.Dom S.model.W₀ σ) := ‹_›
  exact Premodel.holds_axInf_of_finiteCards S.model_isModel (𝟙 _) σ ⟨X, by rw [Intension.ext']; erw [hX]; rfl⟩

variable (S) in
/-- `separable-collapses`: infinitely many pairs of individuals at the base, any two separated by
an arrow that collapses one and not the other. -/
def SeparableCollapses : Prop :=
  ∃ a b : ℕ → S.F.X S.W₀, ∀ i j, i ≠ j → ∃ V, ∃ k : S.W₀ ⟶ V,
    (FunCat.fn k (a i) = FunCat.fn k (b i) ∧ FunCat.fn k (a j) ≠ FunCat.fn k (b j)) ∨
    (FunCat.fn k (a j) = FunCat.fn k (b j) ∧ FunCat.fn k (a i) ≠ FunCat.fn k (b i))

/-- That an arrow collapses two individuals. -/
def collapseProp (x y : S.F.X S.W₀) : Intension (SymT S.F.De S.G) .t S.W₀ :=
  {p | FunCat.fn p.2.2 x = FunCat.fn p.2.2 y}

theorem collapseProp_mem (x y : S.F.X S.W₀) : collapseProp (S := S) x y ∈ Set.range (S.model.incl .t S.W₀) := by
  refine (mem_range_symIncl S.F.De S.G _ S.W₀ _).2 ⟨⟨{x, y}, Set.toFinite _, fun V h i ha => ?_⟩, ?_⟩
  · have ex : FunCat.fn h x = FunCat.fn i x := ha x (by simp)
    have ey : FunCat.fn h y = FunCat.fn i y := ha y (by simp)
    ext ⟨U, ⟨⟩, k⟩
    show FunCat.fn k (FunCat.fn h x) = FunCat.fn k (FunCat.fn h y) ↔ FunCat.fn k (FunCat.fn i x) = FunCat.fn k (FunCat.fn i y)
    rw [ex, ey]
  · rintro V ⟨⟩ k g hg (hk : FunCat.fn k x = FunCat.fn k y)
    show FunCat.fn g (FunCat.fn k x) = FunCat.fn g (FunCat.fn k y)
    rw [hk]

/-- **Separable collapses give infinitely many propositions.** -/
theorem infinite_props_of_separable (h : S.SeparableCollapses) : Infinite (S.model.Dom S.W₀ (.rel .t)) := by
  obtain ⟨a, b, hab⟩ := h
  choose f hf using fun i => collapseProp_mem (S := S) (a i) (b i)
  refine Infinite.of_injective f fun i j e => ?_
  by_contra hij
  obtain ⟨V, k, hk⟩ := hab i j hij
  have e' := congrArg (S.model.incl .t S.W₀) e
  rw [hf i, hf j] at e'
  have key : FunCat.fn k (a i) = FunCat.fn k (b i) ↔ FunCat.fn k (a j) = FunCat.fn k (b j) := by
    have := congrArg (fun A : Intension (SymT S.F.De S.G) .t S.W₀ => (⟨V, PUnit.unit, k⟩ : Tuple _ _ _) ∈ A) e'
    exact Iff.of_eq this
  rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h2 (key.1 h1)
  · exact h2 (key.2 h1)

/-! ### `barcan-surjective` -/

variable (S) in
/-- `surjective-arrows`: every arrow out of the base is surjective. -/
def SurjectiveArrows : Prop := ∀ V (k : S.W₀ ⟶ V), Function.Surjective (FunCat.fn k)

/-- **A surjective arrow out of the base is surjective on every domain**: an entity at its
target, pinned down by a finite `Y`, is the image of its pullback along a finite preimage
of `Y`, which is pinned down and symmetric. -/
theorem map_surjective_of {V : S.F.Ob} (k : S.W₀ ⟶ V) (hk : Function.Surjective (FunCat.fn k)) :
    ∀ σ : Ty, Function.Surjective ((S.model.inner σ).map k)
  | .e => hk
  | .var _ => hk
  | .rel ρ => by
    intro b
    obtain ⟨Y, hY, hb⟩ := symIdeal_inner_finPinned (De := S.F.De) (G := S.G) (W₀ := S.W₀)
      (nonempty_e := S.ne) (I := S.model.I) (.rel ρ) V b
    obtain ⟨X, hX, hXY⟩ := Premodel.exists_finite_image_eq (f := (S.model.inner .e).map k) hk hY
    have hpb := Premodel.pullbackG_sym (G := S.G) (B := S.model) k X (model_domSym (S := S) ρ V b)
    have hpin := Premodel.pullbackG_pinned (B := S.model) k X (S.model.incl ρ V b)
    obtain ⟨a, ha⟩ := (mem_range_symIncl S.F.De S.G ρ S.W₀ (S.model.pullbackG k X (S.model.incl ρ V b))).2
      ⟨⟨X, hX, fun U h i hag => hpin U h i hag⟩, hpb⟩
    refine ⟨a, S.model.Incl_injective _ V ?_⟩
    have ha' : S.model.incl ρ S.W₀ a = S.model.pullbackG k X (S.model.incl ρ V b) := ha
    erw [S.model.Incl_map, Outer.map_rel, S.model.Incl_rel ρ S.W₀ a, ha', Premodel.map_pullbackG k hXY hb]
    rfl

/-- **The group's argument `barcan-surjective`**: BF at every type, at the base. -/
theorem bf_of_surjective (hs : S.SurjectiveArrows) (σ : Ty) : S.model.HoldsSentence (Sentence.bf σ) :=
  S.model.holds_bf_of_surjective S.model_isModel σ (𝟙 _) fun k => map_surjective_of k (hs _ k) σ

/-! ### Boolean Completeness (Dorr's draft, §§4–5) -/

variable (S) in
/-- A finite `M` **separates** an arrow `h` from the base to itself (Definition 28): every arrow
agreeing with `h` on `M` is a symmetry. -/
def Separates (M : Set (S.F.X S.W₀)) (h : S.W₀ ⟶ S.W₀) : Prop :=
  ∀ h' : S.W₀ ⟶ S.W₀, AgreeOn S.F.De M h h' → h' ∈ S.G S.W₀

variable (S) in
/-- `hull-conditions`, the hypotheses of the draft's Theorem 36 with the constant closure
operation `M ↦ M ∪ M₀`: a finite `M₀` such that **(B1)** every finite `M ⊇ M₀` is amalgamable,
two arrows agreeing on `M`, the first not separated by `M`, being spliced on any finite `P`, `Q`
with `P ∩ Q ⊆ M`; and **(B2)** for finite `N ⊇ M₀`, `P` and `Q`, some symmetry fixes `N`
pointwise and moves `P ∖ N` off `Q`. -/
def HullConditions : Prop :=
  ∃ M₀ : Set (S.F.X S.W₀), M₀.Finite ∧
    (∀ M : Set (S.F.X S.W₀), M.Finite → M₀ ⊆ M → ∀ h : S.W₀ ⟶ S.W₀, ¬ S.Separates M h →
      ∀ h' : S.W₀ ⟶ S.W₀, AgreeOn S.F.De M h h' →
        ∀ P Q : Set (S.F.X S.W₀), P.Finite → Q.Finite → P ∩ Q ⊆ M →
          ∃ j : S.W₀ ⟶ S.W₀, AgreeOn S.F.De P j h' ∧ AgreeOn S.F.De Q j h) ∧
    (∀ N P Q : Set (S.F.X S.W₀), N.Finite → P.Finite → Q.Finite → M₀ ⊆ N →
      ∃ g ∈ S.G S.W₀, (∀ x ∈ N, FunCat.fn g x = x) ∧ ∀ x ∈ P, x ∉ N → FunCat.fn g x ∉ Q)

/-- Membership in an intension pinned down by `M` depends on the arrow only through `M`. -/
theorem mem_of_pinned {ρ : RTy} {M : Set (S.F.X S.W₀)} {X : Intension S.model.inner ρ S.W₀}
    (hp : S.model.PinnedO (.rel ρ) M X) {V : S.F.Ob} {h i : S.W₀ ⟶ V} (ha : AgreeOn S.F.De M h i)
    (a : Args S.model.inner ρ V) (hm : (⟨V, a, h⟩ : Tuple S.model.inner ρ S.W₀) ∈ X) :
    (⟨V, a, i⟩ : Tuple S.model.inner ρ S.W₀) ∈ X := by
  have e := hp V h i ha
  have := congrArg (fun A : Intension S.model.inner ρ V => (⟨V, a, 𝟙 V⟩ : Tuple S.model.inner ρ V) ∈ A) e
  simp only [Outer.map_rel, Intension.mem_map, Category.comp_id] at this
  exact this.mp hm

/-- The transport of an entity pinned down by `M` along `g` is pinned down by `g[M]`. -/
theorem pinned_map {ρ : RTy} {M : Set (S.F.X S.W₀)} {A : S.model.Dom S.W₀ (.rel ρ)}
    (hp : S.model.PinnedO (.rel ρ) M (S.model.incl ρ S.W₀ A)) (g : S.W₀ ⟶ S.W₀) :
    S.model.PinnedO (.rel ρ) (FunCat.fn g '' M) (S.model.incl ρ S.W₀ ((S.model.inner (.rel ρ)).map g A)) := by
  intro V h i ha
  simp only [Outer.map_rel]
  erw [S.model.incl_map, ← Intension.map_comp, ← Intension.map_comp]
  exact hp V (g ≫ h) (g ≫ i) (AgreeOn.comp S.F.De g ha)

/-- **Lemma 35**: the extension of `F`, pinned down by `M_F`, is closed under the symmetries
fixing `M_F` pointwise. -/
theorem orbit_ext {ρ : RTy} {MF : Set (S.F.X S.W₀)} {F : S.model.Dom S.W₀ (.rel (.arr (.rel ρ) .t))}
    (hpF : S.model.PinnedO (.rel _) MF (S.model.incl _ S.W₀ F)) {g : S.W₀ ⟶ S.W₀} (hg : g ∈ S.G S.W₀)
    (hfix : ∀ x ∈ MF, FunCat.fn g x = x) {A : S.model.Dom S.W₀ (.rel ρ)}
    (hA : (⟨S.W₀, (A, PUnit.unit), 𝟙 S.W₀⟩ : Tuple S.model.inner (.arr (.rel ρ) .t) S.W₀) ∈ S.model.incl _ S.W₀ F) :
    (⟨S.W₀, ((S.model.inner (.rel ρ)).map g A, PUnit.unit), 𝟙 S.W₀⟩ : Tuple S.model.inner (.arr (.rel ρ) .t) S.W₀) ∈
      S.model.incl _ S.W₀ F := by
  have h1 := Premodel.Sym.at_id (model_domSym (S := S) _ S.W₀ F) (A, PUnit.unit) hg hA
  exact mem_of_pinned hpF (h := g) (i := 𝟙 _) (fun x hx => hfix x hx) _ h1

/-- **Theorem 36** (the draft's main result), on one object: every property `F` of entities of a
relational type has a least upper bound, `⋃{A↑N | A ∈ ext F}` with `N := M_F ∪ M₀`, the union of
the hulls of its instances. -/
theorem lub_of_hull [Subsingleton S.F.Ob] (hH : S.HullConditions) (ρ : RTy)
    (F : S.model.Dom S.W₀ (.rel (.arr (.rel ρ) .t))) :
    ∃ y : S.model.Dom S.W₀ (.rel ρ), ∀ z : S.model.Dom S.W₀ (.rel ρ),
      (∀ u : S.model.Dom S.W₀ (.rel ρ),
        (⟨S.W₀, (u, PUnit.unit), 𝟙 S.W₀⟩ : Tuple S.model.inner (.arr (.rel ρ) .t) S.W₀) ∈ S.model.incl _ S.W₀ F →
          S.model.incl ρ S.W₀ u ⊆ S.model.incl ρ S.W₀ z) ↔
        S.model.incl ρ S.W₀ y ⊆ S.model.incl ρ S.W₀ z := by
  obtain ⟨M₀, hM₀, hB1, hB2⟩ := hH
  obtain ⟨MF, hMF, hpF⟩ := symIdeal_inner_finPinned (De := S.F.De) (G := S.G) (W₀ := S.W₀)
    (nonempty_e := S.ne) (I := S.model.I) (.rel _) S.W₀ F
  have hN : (MF ∪ M₀).Finite := hMF.union hM₀
  -- the union of the hulls at `N` of the instances
  let Y : Intension (SymT S.F.De S.G) ρ S.W₀ := {p | ∃ A : S.model.Dom S.W₀ (.rel ρ),
    (⟨S.W₀, (A, PUnit.unit), 𝟙 S.W₀⟩ : Tuple S.model.inner (.arr (.rel ρ) .t) S.W₀) ∈ S.model.incl _ S.W₀ F ∧
    ∃ h' : S.W₀ ⟶ p.1, AgreeOn S.F.De (MF ∪ M₀) p.2.2 h' ∧
      (⟨p.1, p.2.1, h'⟩ : Tuple S.model.inner ρ S.W₀) ∈ S.model.incl ρ S.W₀ A}
  obtain ⟨y, hy⟩ := (mem_range_symIncl S.F.De S.G ρ S.W₀ Y).2
    ⟨⟨MF ∪ M₀, hN, fun V h i ha => by
      ext ⟨U, v, k⟩
      constructor
      · rintro ⟨A, hA, h', hag, hm⟩
        exact ⟨A, hA, h', ((ha.comp_right S.F.De k).symm).trans S.F.De hag, hm⟩
      · rintro ⟨A, hA, h', hag, hm⟩
        exact ⟨A, hA, h', (ha.comp_right S.F.De k).trans S.F.De hag, hm⟩⟩,
    fun V v k g hg ⟨A, hA, h', hag, hm⟩ =>
      ⟨A, hA, h' ≫ g, hag.comp_right S.F.De g, (model_domSym (S := S) ρ S.W₀ A) V v h' g hg hm⟩⟩
  have hy' : S.model.incl ρ S.W₀ y = Y := hy
  refine ⟨y, fun z => ⟨fun hub => ?_, fun hle u hu => ?_⟩⟩
  · rw [hy']
    rintro ⟨V, v, h⟩ ⟨A, hA, h', hag, hm⟩
    obtain rfl : V = S.W₀ := Subsingleton.elim _ _
    obtain ⟨MU, hMU, hpU⟩ := symIdeal_inner_finPinned (De := S.F.De) (G := S.G) (W₀ := S.W₀)
      (nonempty_e := S.ne) (I := S.model.I) (.rel ρ) S.W₀ z
    obtain ⟨MA, hMA, hpA⟩ := symIdeal_inner_finPinned (De := S.F.De) (G := S.G) (W₀ := S.W₀)
      (nonempty_e := S.ne) (I := S.model.I) (.rel ρ) S.W₀ A
    -- move `A`'s support off `z`'s outside `N` (B2)
    obtain ⟨g, hg, hgfix, hgmove⟩ := hB2 (MF ∪ M₀) (MA ∪ (MF ∪ M₀)) (MU ∪ (MF ∪ M₀)) hN (hMA.union hN)
      (hMU.union hN) Set.subset_union_right
    obtain ⟨g', hg', e₁, e₂⟩ := S.G_inv _ g hg
    let A' := (S.model.inner (.rel ρ)).map g A
    have hA' := orbit_ext hpF hg (fun x hx => hgfix x (Or.inl hx)) hA
    have hg'fix : ∀ x ∈ MF ∪ M₀, FunCat.fn g' x = x := fun x hx => by
      have h0 : FunCat.fn g' (FunCat.fn g x) = x := congrFun (congrArg FunCat.fn e₁) x
      rwa [hgfix x hx] at h0
    let h'' := g' ≫ h'
    have hm'' : (⟨S.W₀, v, h''⟩ : Tuple S.model.inner ρ S.W₀) ∈ S.model.incl ρ S.W₀ A' := by
      erw [S.model.incl_map, Intension.mem_map, ← Category.assoc, e₁, Category.id_comp]
      exact hm
    have hag'' : AgreeOn S.F.De (MF ∪ M₀) h h'' := fun x hx => by
      show FunCat.fn h x = FunCat.fn h' (FunCat.fn g' x)
      rw [hg'fix x hx]; exact hag x hx
    have hpA' := pinned_map hpA g
    have hdisj : (FunCat.fn g '' MA ∪ (MF ∪ M₀)) ∩ (MU ∪ (MF ∪ M₀)) ⊆ MF ∪ M₀ := by
      rintro x ⟨hx1 | hx1, hx2⟩
      · obtain ⟨a, ha, rfl⟩ := hx1
        by_cases haN : a ∈ MF ∪ M₀
        · rw [hgfix a haN]; exact haN
        · exact absurd hx2 (hgmove a (Or.inl ha) haN)
      · exact hx1
    by_cases hsep : S.Separates (MF ∪ M₀) h
    · -- Case 1: `N` separates `h`; conjugate by `h⁻¹`
      have hhG := hsep h (AgreeOn.refl _ _ _)
      have hh''G := hsep h'' hag''
      obtain ⟨hi, hiG, eh₁, eh₂⟩ := S.G_inv _ h hhG
      let m := h'' ≫ hi
      have hmG : m ∈ S.G S.W₀ := S.G_comp hh''G hiG
      have hmfix : ∀ x ∈ MF ∪ M₀, FunCat.fn m x = x := fun x hx => by
        show FunCat.fn hi (FunCat.fn h'' x) = x
        have e : FunCat.fn h x = FunCat.fn h'' x := hag'' x hx
        rw [← e]
        exact congrFun (congrArg FunCat.fn eh₁) x
      have h1 := (model_domSym (S := S) ρ S.W₀ A') S.W₀ v h'' hi hiG hm''
      have h2 : (⟨S.W₀, Args.map S.model.inner ρ hi v, 𝟙 S.W₀⟩ : Tuple S.model.inner ρ S.W₀) ∈
          S.model.incl ρ S.W₀ ((S.model.inner (.rel ρ)).map m A') := by
        erw [S.model.incl_map, Intension.mem_map, Category.comp_id]
        exact h1
      have h3 := hub _ (orbit_ext hpF hmG (fun x hx => hmfix x (Or.inl hx)) hA') h2
      have h4 := (model_domSym (S := S) ρ S.W₀ z) S.W₀ _ (𝟙 _) h hhG h3
      rwa [S.model.args_map_map_inv eh₂, Category.id_comp] at h4
    · -- Case 2: splice (B1)
      obtain ⟨j, hj₁, hj₂⟩ := hB1 (MF ∪ M₀) hN Set.subset_union_right h hsep h'' hag''
        (FunCat.fn g '' MA ∪ (MF ∪ M₀)) (MU ∪ (MF ∪ M₀)) ((hMA.image _).union hN) (hMU.union hN) hdisj
      have h1 : (⟨S.W₀, v, j⟩ : Tuple S.model.inner ρ S.W₀) ∈ S.model.incl ρ S.W₀ A' :=
        mem_of_pinned hpA' (fun x hx => (hj₁ x (Or.inl hx)).symm) v hm''
      have h2 := hub _ hA' h1
      exact mem_of_pinned hpU (fun x hx => hj₂ x (Or.inl hx)) v h2
  · rintro ⟨V, v, k⟩ hm
    apply hle
    rw [hy']
    exact ⟨u, hu, k, AgreeOn.refl _ _ _, hm⟩

/-- The least upper bounds give the LUB form of Boolean Completeness at every type. -/
theorem holds_bc_lub [Subsingleton S.F.Ob] (hH : S.HullConditions) (ρ : RTy) :
    S.model.HoldsSentence (P.BooleanCompletenessLUB.quoted ρ) := by
  have M : S.model.IsModel := S.model_isModel
  simp only [Premodel.HoldsSentence, P.BooleanCompletenessLUB.quoted, S.model.holds_forall M,
    S.model.holds_exists M, S.model.holds_iff M, S.model.holds_imp M, S.model.holds_leR M]
  intro X
  obtain ⟨y, hy⟩ := lub_of_hull hH ρ X
  refine ⟨y, fun z => Iff.trans (forall_congr' fun u => imp_congr ?_ Iff.rfl) (hy z)⟩
  rw [S.model.holds_app (a' := u) _ _ _ _ rfl]
  rfl

end SymBase

end Classicism.Meta.Intensional
