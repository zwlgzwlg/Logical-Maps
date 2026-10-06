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
finite `N`, so a symmetry fixing `N` pointwise fixes `R` (Lemma 21), and symmetry carries
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

end SymBase

end Classicism.Meta.Intensional
