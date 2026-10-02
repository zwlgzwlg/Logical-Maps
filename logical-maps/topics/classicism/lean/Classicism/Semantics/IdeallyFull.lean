import Classicism.Semantics.IntensionalFull
import Classicism.Syntax.Constants
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Lattice

/-!
# Ideally full intensional action models

Appendix D of *Classicism*, "Consistency results using non-full action models", in the
intensional form of Cian's draft *Boolean Completeness without Rigid Comprehension*
(§"Ideally-full models"): the technique for building non-full action models, and the
proposition that makes it work.

Fix an action `De` for `e`. Two arrows `h, i : W → V` **agree on** a set `N ⊆ W^e` when
they send its members to the same individuals. An element `x` of an action `F` at `W` is
**pinned down by** `N` when any two arrows out of `W` agreeing on `N` act on it alike,
`h^F x = i^F x` (Definition D.2), and it is **finitely pinned** when some finite `N` pins
it down: the ideal of finite subsets, the only ideal the paper's examples use, is built
in. The **ideally full** premodel takes, at each relational type, exactly the intensions
that are finitely pinned (Definition D.3, condition (ii) and (iii) at once, since a
relation is an intension), with `e` as given.

**Proposition D.4: an ideally full premodel is a model.** The paper proves it through the
combinator form of the sufficiency condition; here it is the induction on terms that the
full models no longer needed (`sem_pinned`): if a finite `N` pins down every value of the
assignment and every constant the term mentions, it pins down the term's value. The
cases are the draft's closure lemma. A variable or constant is pinned by hypothesis; the
logical constants are pinned by `∅`, their readings not seeing the arrow; an application
is pinned because application commutes with the action of arrows for every intension
(`apply_map`); and an abstraction is pinned because its value depends on the arrow only
through the constants (`sem_congr_const`) and on the assignment, both of which two arrows
agreeing on `N` treat alike. Then `ideal_isModel`: for a term, take the union of the
finitely many finite sets that pin the assignment's values and the term's constants.

Then Proposition D.6: if every arrow out of the base is surjective on individuals, `BF`
holds at every type; the witness at the base for an element `b` pinned by `Y` is the
intension of tuples `⟨x̄, i⟩` such that `i` agrees on a preimage of `Y` with `j ∘ h` for
some `⟨x̄, j⟩ ∈ b`.
-/

namespace Classicism.Meta.Intensional

open CategoryTheory

variable {C : Type} [SmallCategory C] (De : C ⥤ Type)

/-! ### Agreement and pinning -/

/-- Two arrows agree on a set of individuals. -/
def AgreeOn {W V : C} (N : Set (De.obj W)) (h i : W ⟶ V) : Prop :=
  ∀ x ∈ N, De.map h x = De.map i x

theorem AgreeOn.mono {W V : C} {N M : Set (De.obj W)} (hNM : N ⊆ M) {h i : W ⟶ V}
    (ha : AgreeOn De M h i) : AgreeOn De N h i :=
  fun x hx => ha x (hNM hx)

theorem AgreeOn.union_left {W V : C} {N M : Set (De.obj W)} {h i : W ⟶ V}
    (ha : AgreeOn De (N ∪ M) h i) : AgreeOn De N h i :=
  ha.mono De Set.subset_union_left

theorem AgreeOn.union_right {W V : C} {N M : Set (De.obj W)} {h i : W ⟶ V}
    (ha : AgreeOn De (N ∪ M) h i) : AgreeOn De M h i :=
  ha.mono De Set.subset_union_right

theorem AgreeOn.refl {W V : C} (N : Set (De.obj W)) (h : W ⟶ V) : AgreeOn De N h h := fun _ _ => rfl

theorem AgreeOn.symm {W V : C} {N : Set (De.obj W)} {h i : W ⟶ V} (ha : AgreeOn De N h i) :
    AgreeOn De N i h := fun x hx => (ha x hx).symm

theorem AgreeOn.trans {W V : C} {N : Set (De.obj W)} {h i j : W ⟶ V} (h₁ : AgreeOn De N h i)
    (h₂ : AgreeOn De N i j) : AgreeOn De N h j := fun x hx => (h₁ x hx).trans (h₂ x hx)

/-- Arrows agreeing on `N` still agree after a further arrow. -/
theorem AgreeOn.comp_right {W V U : C} {N : Set (De.obj W)} {h i : W ⟶ V} (ha : AgreeOn De N h i)
    (l : V ⟶ U) : AgreeOn De N (h ≫ l) (i ≫ l) := fun x hx => by
  simp only [Functor.map_comp, types_comp_apply]
  rw [ha x hx]

/-- If `h', i'` agree on `h[N]`, then `h ≫ h'` and `h ≫ i'` agree on `N`. -/
theorem AgreeOn.comp {W V U : C} {N : Set (De.obj W)} (h : W ⟶ V) {h' i' : V ⟶ U}
    (ha : AgreeOn De (De.map h '' N) h' i') : AgreeOn De N (h ≫ h') (h ≫ i') := by
  intro x hx
  have := ha (De.map h x) ⟨x, hx, rfl⟩
  simpa [Functor.map_comp] using this

/-- An element of an action `F` at `W` is pinned down by `N`. -/
def PinnedBy (F : C ⥤ Type) {W : C} (N : Set (De.obj W)) (x : F.obj W) : Prop :=
  ∀ (V : C) (h i : W ⟶ V), AgreeOn De N h i → F.map h x = F.map i x

theorem PinnedBy.mono {F : C ⥤ Type} {W : C} {N M : Set (De.obj W)} (hNM : N ⊆ M) {x : F.obj W}
    (hx : PinnedBy De F N x) : PinnedBy De F M x :=
  fun _ h i ha => hx _ h i (ha.mono De hNM)

/-- Closure (i): the action of `h` on an element pinned by `N` is pinned by `h[N]`. -/
theorem PinnedBy.map {F : C ⥤ Type} {W V : C} {N : Set (De.obj W)} {x : F.obj W}
    (hx : PinnedBy De F N x) (h : W ⟶ V) : PinnedBy De F (De.map h '' N) (F.map h x) := by
  intro U h' i' ha
  have := hx _ (h ≫ h') (h ≫ i') (ha.comp De h)
  simpa [Functor.map_comp] using this

/-- Finitely pinned: pinned down by some finite set. -/
def FinPinned (F : C ⥤ Type) {W : C} (x : F.obj W) : Prop :=
  ∃ N : Set (De.obj W), N.Finite ∧ PinnedBy De F N x

theorem FinPinned.map {F : C ⥤ Type} {W V : C} {x : F.obj W} (hx : FinPinned De F x) (h : W ⟶ V) :
    FinPinned De F (F.map h x) :=
  let ⟨N, hN, hp⟩ := hx
  ⟨De.map h '' N, hN.image _, hp.map De h⟩

/-- The subaction of the finitely pinned elements of an action. -/
abbrev pinnedAction (F : C ⥤ Type) : C ⥤ Type where
  obj W := {x : F.obj W // FinPinned De F x}
  map {W V} h := TypeCat.ofHom fun x => ⟨F.map h x.1, x.2.map De h⟩
  map_id W := by
    ext ⟨x, hx⟩ : 3
    simp
  map_comp h i := by
    ext ⟨x, hx⟩ : 3
    simp

/-! ### Pinning in a premodel, and the induction of Proposition D.4

Stated for any intensional action premodel, with agreement of arrows read through its
action for `e`: what pins down the values of the assignment and the constants a term
mentions pins down the term's value. -/

namespace Premodel

variable {Sig : Signature} (B : Premodel Sig C)

/-- An outer element at `σ` is pinned down by a set of individuals `N` when two arrows
agreeing on `N` (through the action for `e`) act on it alike. -/
def PinnedO (σ : Ty) {W : C} (N : Set (B.Dom W .e)) (x : Outer B.inner σ W) : Prop :=
  ∀ (V : C) (h i : W ⟶ V), AgreeOn (B.inner .e) N h i → Outer.map B.inner σ h x = Outer.map B.inner σ i x

theorem PinnedO.mono {σ : Ty} {W : C} {N M : Set (B.Dom W .e)} (hNM : N ⊆ M) {x : Outer B.inner σ W}
    (hx : B.PinnedO σ N x) : B.PinnedO σ M x :=
  fun _ h i ha => hx _ h i (ha.mono _ hNM)

/-- Closure (ii): the set operations preserve pinning by `N`. -/
theorem PinnedO.inter {ρ : RTy} {W : C} {N : Set (B.Dom W .e)} {p q : Intension B.inner ρ W}
    (hp : B.PinnedO (.rel ρ) N p) (hq : B.PinnedO (.rel ρ) N q) : B.PinnedO (.rel ρ) N (p ∩ q) := by
  intro V h i ha
  have hp' := hp V h i ha; have hq' := hq V h i ha
  simp only [Outer.map_rel] at hp' hq' ⊢
  rw [Intension.map_inter, Intension.map_inter, hp', hq']

theorem PinnedO.union {ρ : RTy} {W : C} {N : Set (B.Dom W .e)} {p q : Intension B.inner ρ W}
    (hp : B.PinnedO (.rel ρ) N p) (hq : B.PinnedO (.rel ρ) N q) : B.PinnedO (.rel ρ) N (p ∪ q) := by
  intro V h i ha
  have hp' := hp V h i ha; have hq' := hq V h i ha
  simp only [Outer.map_rel] at hp' hq' ⊢
  rw [Intension.map_union, Intension.map_union, hp', hq']

theorem PinnedO.compl {ρ : RTy} {W : C} {N : Set (B.Dom W .e)} {p : Intension B.inner ρ W}
    (hp : B.PinnedO (.rel ρ) N p) : B.PinnedO (.rel ρ) N pᶜ := by
  intro V h i ha
  have hp' := hp V h i ha
  simp only [Outer.map_rel] at hp' ⊢
  rw [Intension.map_compl, Intension.map_compl, hp']

theorem PinnedO.univ {ρ : RTy} {W : C} (N : Set (B.Dom W .e)) :
    B.PinnedO (.rel ρ) N (Set.univ : Intension B.inner ρ W) := fun _ _ _ _ => rfl

theorem PinnedO.empty {ρ : RTy} {W : C} (N : Set (B.Dom W .e)) :
    B.PinnedO (.rel ρ) N (∅ : Intension B.inner ρ W) := fun _ _ _ _ => rfl

/-- Pinning of an inclusion, in terms of the inner element's action. -/
theorem pinnedO_Incl_iff (σ : Ty) {W : C} (N : Set (B.Dom W .e)) (x : B.Dom W σ) :
    B.PinnedO σ N (B.Incl σ W x) ↔
      ∀ (V : C) (h i : W ⟶ V), AgreeOn (B.inner .e) N h i → (B.inner σ).map h x = (B.inner σ).map i x := by
  constructor
  · intro hp V h i ha
    apply B.Incl_injective
    rw [B.Incl_map, B.Incl_map]
    exact hp V h i ha
  · intro hp V h i ha
    rw [← B.Incl_map, ← B.Incl_map, hp V h i ha]

/-- The value of a term depends on the arrow only through the values of the constants it
mentions. -/
theorem sem_congr_const :
    ∀ {Γ : Ctx} {σ : Ty} {W : C} (t : Term Sig Γ σ) (h h' : B.W₀ ⟶ W),
      (∀ c ∈ t.consts, (B.inner _).map h (B.I c) = (B.inner _).map h' (B.I c)) →
      ∀ (g : IEnv (B.Dom W) Γ), B.sem h t g = B.sem h' t g
  | _, _, _, .var _, _, _, _, _ => rfl
  | _, _, _, .const c, h, h', hc, _ => by
    show B.Incl _ _ ((B.inner _).map h (B.I c)) = B.Incl _ _ ((B.inner _).map h' (B.I c))
    rw [hc c (Set.mem_singleton c)]
  | _, _, _, .app f a, h, h', hc, g => by
    show B.apply (B.sem h f g) (B.sem h a g) = B.apply (B.sem h' f g) (B.sem h' a g)
    rw [sem_congr_const f h h' (fun c hc' => hc c (Term.consts_app_left f a hc')) g,
      sem_congr_const a h h' (fun c hc' => hc c (Term.consts_app_right f a hc')) g]
  | _, _, _, .lam b, h, h', hc, g => by
    ext ⟨U, ⟨x, a⟩, j⟩
    rw [mem_sem_lam, mem_sem_lam,
      sem_congr_const b (h ≫ j) (h' ≫ j) (fun c hc' => by
        rw [Functor.map_comp, Functor.map_comp]
        show (B.inner _).map j ((B.inner _).map h (B.I c)) = (B.inner _).map j ((B.inner _).map h' (B.I c))
        rw [hc c hc'])]
  | _, _, _, .and, _, _, _, _ | _, _, _, .or, _, _, _, _ | _, _, _, .not, _, _, _, _
  | _, _, _, .all _, _, _, _, _ | _, _, _, .ex _, _, _, _, _ | _, _, _, .eq _, _, _, _, _
  | _, _, _, .constR _, _, _, _, _ | _, _, _, .negR _, _, _, _, _ | _, _, _, .andR _, _, _, _, _
  | _, _, _, .orR _, _, _, _, _ | _, _, _, .coextR _, _, _, _, _ | _, _, _, .boxR _, _, _, _, _
  | _, _, _, .inclR _, _, _, _, _ => rfl

/-- Closure (iii), for the application of an intension to an outer element: pinned by
what pins the two. -/
theorem pinnedO_apply {σ : Ty} {ρ : RTy} {W : C} {N : Set (B.Dom W .e)}
    {F : Intension B.inner (.arr σ ρ) W} {x : Outer B.inner σ W}
    (hF : B.PinnedO (.rel (.arr σ ρ)) N F) (hx : B.PinnedO σ N x) : B.PinnedO (.rel ρ) N (B.apply F x) := by
  intro V h i ha
  rw [Outer.map_rel, Outer.map_rel, ← B.apply_map, ← B.apply_map, hx V h i ha]
  have := hF V h i ha
  rw [Outer.map_rel, Outer.map_rel] at this
  rw [this]

/-- An assignment whose values are all pinned by `N` is moved alike by two arrows
agreeing on `N`. -/
theorem push_eq_of_pinned {Γ : Ctx} {W V : C} (g : IEnv (B.Dom W) Γ) (N : Set (B.Dom W .e))
    (hg : ∀ τ (v : Var Γ τ), B.PinnedO τ N (B.Incl τ W (g.get v))) {h i : W ⟶ V}
    (ha : AgreeOn (B.inner .e) N h i) : B.push h g = B.push i g := by
  apply IEnv.ext
  intro τ v
  simp only [push, IEnv.get_map]
  exact (B.pinnedO_Incl_iff τ N (g.get v)).1 (hg τ v) V h i ha

/-- **The induction of Proposition D.4.** If `N` pins down every value of the assignment
and every constant the term mentions, it pins down the term's value. A variable or
constant by hypothesis; the logical constants by `rfl`, their readings not seeing the
arrow; an application since application commutes with the action of arrows; an
abstraction since its value depends on the arrow only through the constants and on the
assignment, which two arrows agreeing on `N` treat alike. -/
theorem sem_pinned : ∀ {Γ : Ctx} {σ : Ty} {W : C} (h : B.W₀ ⟶ W) (t : Term Sig Γ σ)
    (g : IEnv (B.Dom W) Γ) (N : Set (B.Dom W .e)),
    (∀ τ (v : Var Γ τ), B.PinnedO τ N (B.Incl τ W (g.get v))) →
    (∀ c ∈ t.consts, B.PinnedO _ N (B.Incl _ W ((B.inner _).map h (B.I c)))) →
    B.PinnedO σ N (B.sem h t g)
  | _, _, _, _, .var v, g, N, hg, _ => hg _ v
  | _, _, _, _, .const c, _, N, _, hc => hc c (Set.mem_singleton c)
  | _, _, _, h, .app f a, g, N, hg, hc =>
    B.pinnedO_apply (sem_pinned h f g N hg (fun c hc' => hc c (Term.consts_app_left f a hc')))
      (sem_pinned h a g N hg (fun c hc' => hc c (Term.consts_app_right f a hc')))
  | _, _, _, h, .lam b, g, N, hg, hc => by
    intro V h' i' ha
    rw [← B.sem_push, ← B.sem_push, B.push_eq_of_pinned g N hg ha]
    apply B.sem_congr_const
    intro c hc'
    rw [Functor.map_comp, Functor.map_comp]
    exact (B.pinnedO_Incl_iff _ N _).1 (hc c hc') V h' i' ha
  | _, _, _, _, .and, _, _, _, _ | _, _, _, _, .or, _, _, _, _ | _, _, _, _, .not, _, _, _, _
  | _, _, _, _, .all _, _, _, _, _ | _, _, _, _, .ex _, _, _, _, _ | _, _, _, _, .eq _, _, _, _, _
  | _, _, _, _, .constR _, _, _, _, _ | _, _, _, _, .negR _, _, _, _, _
  | _, _, _, _, .andR _, _, _, _, _ | _, _, _, _, .orR _, _, _, _, _
  | _, _, _, _, .coextR _, _, _, _, _ | _, _, _, _, .boxR _, _, _, _, _
  | _, _, _, _, .inclR _, _, _, _, _ => fun _ _ _ _ => rfl

/-- The values of an assignment are pinned by one finite set, when every inner element is
finitely pinned. -/
theorem env_finPinned
    (hfin : ∀ (σ : Ty) (W : C) (x : B.Dom W σ), ∃ N : Set (B.Dom W .e), N.Finite ∧ B.PinnedO σ N (B.Incl σ W x)) :
    ∀ {Γ : Ctx} {W : C} (g : IEnv (B.Dom W) Γ),
      ∃ N : Set (B.Dom W .e), N.Finite ∧ ∀ τ (v : Var Γ τ), B.PinnedO τ N (B.Incl τ W (g.get v))
  | _, _, .nil => ⟨∅, Set.finite_empty, fun _ v => nomatch v⟩
  | _, _, .cons x g => by
    obtain ⟨N, hN, hg⟩ := env_finPinned hfin g
    obtain ⟨M, hM, hx⟩ := hfin _ _ x
    refine ⟨N ∪ M, hN.union hM, fun τ v => ?_⟩
    cases v with
    | zero => exact PinnedO.mono B Set.subset_union_right hx
    | succ v => exact PinnedO.mono B Set.subset_union_left (hg _ v)

/-- The constants a term mentions, moved along an arrow, are pinned by one finite set. -/
theorem consts_finPinned
    (hfin : ∀ (σ : Ty) (W : C) (x : B.Dom W σ), ∃ N : Set (B.Dom W .e), N.Finite ∧ B.PinnedO σ N (B.Incl σ W x))
    {Γ : Ctx} {σ : Ty} {W : C} (h : B.W₀ ⟶ W) (t : Term Sig Γ σ) :
    ∃ N : Set (B.Dom W .e), N.Finite ∧
      ∀ c ∈ t.consts, B.PinnedO _ N (B.Incl _ W ((B.inner _).map h (B.I c))) := by
  classical
  choose N hN using fun c : Sig.Const => hfin (Sig.typeOf c) W ((B.inner _).map h (B.I c))
  refine ⟨⋃ c ∈ t.consts, N c, (Term.consts_finite t).biUnion fun c _ => (hN c).1, fun c hc => ?_⟩
  exact PinnedO.mono B (Set.subset_biUnion_of_mem (u := N) hc) (hN c).2

/-- **Proposition D.4, abstractly.** A premodel whose inner elements are exactly the
finitely pinned ones is a model: for a term, take the union of the finite sets that pin
the assignment's values and the term's constants. -/
theorem isModel_of_pinned
    (hfin : ∀ (σ : Ty) (W : C) (x : B.Dom W σ), ∃ N : Set (B.Dom W .e), N.Finite ∧ B.PinnedO σ N (B.Incl σ W x))
    (hinner : ∀ (ρ : RTy) (W : C) (F : Intension B.inner ρ W),
      (∃ N : Set (B.Dom W .e), N.Finite ∧ B.PinnedO (.rel ρ) N F) → F ∈ Set.range (B.incl ρ W)) :
    B.IsModel := fun {_ σ W} h t g => by
  obtain ⟨N, hN, hg⟩ := B.env_finPinned hfin g
  obtain ⟨M, hM, hc⟩ := B.consts_finPinned hfin h t
  have hp := B.sem_pinned h t g (N ∪ M)
    (fun τ v => PinnedO.mono B Set.subset_union_left (hg τ v))
    (fun c hc' => PinnedO.mono B Set.subset_union_right (hc c hc'))
  cases σ with
  | e => exact ⟨_, rfl⟩
  | rel ρ => exact hinner ρ W _ ⟨N ∪ M, hN.union hM, hp⟩
  | var _ => exact ⟨_, rfl⟩

end Premodel

/-! ### The ideally full domains -/

/-- The ideally full inner action at a type: `De` at `e`; at a relational type, the
finitely pinned intensions over its arguments. -/
noncomputable abbrev IdealT (σ : Ty) : C ⥤ Type :=
  @Ty.rec (fun _ => C ⥤ Type) (fun _ => C ⥤ Type) De
    (fun _ ih => pinnedAction De (intensionAction ih)) (fun _ => De)
    pointAction (fun _ _ ihσ ihρ => prodAction ihσ ihρ) σ

/-- The arguments of a relational type, as an action. -/
noncomputable abbrev IdealArgs (ρ : RTy) : C ⥤ Type :=
  @RTy.rec (fun _ => C ⥤ Type) (fun _ => C ⥤ Type) De
    (fun _ ih => pinnedAction De (intensionAction ih)) (fun _ => De)
    pointAction (fun _ _ ihσ ihρ => prodAction ihσ ihρ) ρ

/-- The ideally full inner action at a relational type. -/
noncomputable abbrev IdealR (ρ : RTy) : C ⥤ Type := pinnedAction De (intensionAction (IdealArgs De ρ))

example : IdealT De .e = De := rfl
example (ρ : RTy) : IdealT De (.rel ρ) = IdealR De ρ := rfl
example (V : C) : (IdealArgs De .t).obj V = PUnit := rfl
example (σ : Ty) (ρ : RTy) (V : C) :
    (IdealArgs De (.arr σ ρ)).obj V = ((IdealT De σ).obj V × (IdealArgs De ρ).obj V) := rfl

/-- The raw intensions over the ideal arguments, the type an element of `IdealR` lives in. -/
abbrev IdealRaw (ρ : RTy) (W : C) : Type := Set (Σ V : C, (IdealArgs De ρ).obj V × (W ⟶ V))

/-- The two spellings of the arguments, related. -/
def idealArgs : ∀ (ρ : RTy) (V : C), Args (IdealT De) ρ V → (IdealArgs De ρ).obj V
  | .t, _, _ => PUnit.unit
  | .arr _ ρ, V, a => (a.1, idealArgs ρ V a.2)

/-- Its inverse. -/
def idealArgs' : ∀ (ρ : RTy) (V : C), (IdealArgs De ρ).obj V → Args (IdealT De) ρ V
  | .t, _, _ => PUnit.unit
  | .arr _ ρ, V, a => (a.1, idealArgs' ρ V a.2)

theorem idealArgs_idealArgs' : ∀ (ρ : RTy) (V : C) (a : (IdealArgs De ρ).obj V),
    idealArgs De ρ V (idealArgs' De ρ V a) = a
  | .t, _, _ => rfl
  | .arr _ ρ, V, a => by
    show (a.1, idealArgs De ρ V (idealArgs' De ρ V a.2)) = a
    exact Prod.ext rfl (idealArgs_idealArgs' ρ V a.2)

theorem idealArgs'_idealArgs : ∀ (ρ : RTy) (V : C) (a : Args (IdealT De) ρ V),
    idealArgs' De ρ V (idealArgs De ρ V a) = a
  | .t, _, _ => rfl
  | .arr _ ρ, V, a => by
    show (a.1, idealArgs' De ρ V (idealArgs De ρ V a.2)) = a
    exact Prod.ext rfl (idealArgs'_idealArgs ρ V a.2)

/-- A raw intension over the ideal arguments, read as an intension: the preimage under
`idealArgs`. -/
def idealRead (ρ : RTy) (W : C) (A : IdealRaw De ρ W) : Intension (IdealT De) ρ W :=
  {p | (⟨p.1, idealArgs De ρ p.1 p.2.1, p.2.2⟩ : Σ V : C, (IdealArgs De ρ).obj V × (W ⟶ V)) ∈ A}

/-- And back: the preimage under `idealArgs'`. -/
def idealRead' (ρ : RTy) (W : C) (F : Intension (IdealT De) ρ W) : IdealRaw De ρ W :=
  {p | (⟨p.1, idealArgs' De ρ p.1 p.2.1, p.2.2⟩ : Tuple (IdealT De) ρ W) ∈ F}

theorem idealRead_idealRead' (ρ : RTy) (W : C) (F : Intension (IdealT De) ρ W) :
    idealRead De ρ W (idealRead' De ρ W F) = F := by
  ext ⟨V, a, i⟩
  simp [idealRead, idealRead', idealArgs'_idealArgs]

theorem idealRead'_idealRead (ρ : RTy) (W : C) (A : IdealRaw De ρ W) :
    idealRead' De ρ W (idealRead De ρ W A) = A := by
  ext ⟨V, a, i⟩
  simp [idealRead, idealRead', idealArgs_idealArgs']

theorem idealRead_map (ρ : RTy) {W V : C} (h : W ⟶ V) (A : IdealRaw De ρ W) :
    idealRead De ρ V ((intensionAction (IdealArgs De ρ)).map h A) = Intension.map (IdealT De) h (idealRead De ρ W A) := by
  ext ⟨U, a, i⟩
  exact Iff.rfl

theorem idealRead'_map (ρ : RTy) {W V : C} (h : W ⟶ V) (F : Intension (IdealT De) ρ W) :
    idealRead' De ρ V (Intension.map (IdealT De) h F) = (intensionAction (IdealArgs De ρ)).map h (idealRead' De ρ W F) := by
  ext ⟨U, a, i⟩
  exact Iff.rfl

/-- The inclusion of the ideally full domain into the intensions. -/
def idealIncl (ρ : RTy) (W : C) (A : (IdealR De ρ).obj W) : Intension (IdealT De) ρ W :=
  idealRead De ρ W A.1

theorem idealIncl_map (ρ : RTy) {W V : C} (h : W ⟶ V) (A : (IdealR De ρ).obj W) :
    idealIncl De ρ V ((IdealR De ρ).map h A) = Intension.map (IdealT De) h (idealIncl De ρ W A) :=
  idealRead_map De ρ h A.1

theorem idealIncl_injective (ρ : RTy) (W : C) : Function.Injective (idealIncl De ρ W) := by
  intro A B e
  apply Subtype.ext
  have := congrArg (idealRead' De ρ W) e
  rwa [idealIncl, idealIncl, idealRead'_idealRead, idealRead'_idealRead] at this

/-- An intension over the ideal actions is the inclusion of an element of the ideally full
domain iff it is finitely pinned. -/
theorem mem_range_idealIncl (ρ : RTy) (W : C) (F : Intension (IdealT De) ρ W) :
    F ∈ Set.range (idealIncl De ρ W) ↔
      ∃ N : Set (De.obj W), N.Finite ∧
        ∀ (V : C) (h i : W ⟶ V), AgreeOn De N h i →
          Intension.map (IdealT De) h F = Intension.map (IdealT De) i F := by
  constructor
  · rintro ⟨⟨A, N, hN, hA⟩, rfl⟩
    refine ⟨N, hN, fun V h i ha => ?_⟩
    show Intension.map (IdealT De) h (idealRead De ρ W A) = Intension.map (IdealT De) i (idealRead De ρ W A)
    rw [← idealRead_map, ← idealRead_map, hA V h i ha]
  · rintro ⟨N, hN, hF⟩
    refine ⟨⟨idealRead' De ρ W F, N, hN, fun V h i ha => ?_⟩, ?_⟩
    · show (intensionAction (IdealArgs De ρ)).map h (idealRead' De ρ W F)
        = (intensionAction (IdealArgs De ρ)).map i (idealRead' De ρ W F)
      rw [← idealRead'_map, ← idealRead'_map, hF V h i ha]
    · exact idealRead_idealRead' De ρ W F

/-- The ideally full intensional action premodel on a category with a chosen base, given
the action for `e` with nonempty domains and the constants, each an element of the
ideally full domain of its type. -/
noncomputable def Premodel.ideal {Sig : Signature} (W₀ : C)
    (nonempty_e : ∀ W : C, Nonempty (De.obj W))
    (I : ∀ c : Sig.Const, (IdealT De (Sig.typeOf c)).obj W₀) : Premodel Sig C where
  W₀ := W₀
  inner := IdealT De
  nonempty_e := nonempty_e
  incl := idealIncl De
  incl_map := idealIncl_map De
  incl_injective := idealIncl_injective De
  I := I

/-! ### Proposition D.4: an ideally full premodel is a model -/

namespace Premodel

variable {Sig : Signature} {W₀ : C}
  {nonempty_e : ∀ W : C, Nonempty (De.obj W)}
  {I : ∀ c : Sig.Const, (IdealT De (Sig.typeOf c)).obj W₀}

local notation "A" => Premodel.ideal De W₀ nonempty_e I

/-- Every inner element of the ideally full premodel is finitely pinned: an individual by
itself, a relation by the finite set that admitted it. -/
theorem ideal_inner_finPinned : ∀ (σ : Ty) (W : C) (x : (A).Dom W σ),
    ∃ N : Set ((A).Dom W .e), N.Finite ∧ (A).PinnedO σ N ((A).Incl σ W x)
  | .e, W, x => ⟨{x}, Set.finite_singleton x, fun _ _ _ ha => ha x rfl⟩
  | .rel ρ, W, x => (mem_range_idealIncl De ρ W _).1 ⟨x, rfl⟩
  | .var _, W, x => ⟨{x}, Set.finite_singleton x, fun _ _ _ ha => ha x rfl⟩

/-- Every finitely pinned intension is inner. -/
theorem ideal_pinned_inner (ρ : RTy) (W : C) (F : Intension (A).inner ρ W)
    (hF : ∃ N : Set ((A).Dom W .e), N.Finite ∧ (A).PinnedO (.rel ρ) N F) :
    F ∈ Set.range ((A).incl ρ W) :=
  (mem_range_idealIncl De ρ W F).2 hF

/-- **Proposition D.4: an ideally full premodel is an intensional action model.** -/
theorem ideal_isModel : (A).IsModel :=
  (A).isModel_of_pinned (ideal_inner_finPinned De) (ideal_pinned_inner De)

/-! ### Proposition D.6: surjectivity on individuals gives `BF`

If every arrow out of the base is surjective on individuals, then it is surjective on
the ideally full domain of every type, so `BF_σ` holds at the base for every `σ`. Given
`b` at `V` pinned down by a finite `Y`, choose a finite `X` at the base with `k[X] = Y`;
the intension of tuples `⟨x̄, i⟩` such that `i` agrees on `X` with `k ∘ j` for some
`⟨x̄, j⟩ ∈ b` is pinned down by `X`, and `k` sends it to `b`. -/

/-- A finite set in the image of a surjection is the image of a finite set. -/
theorem exists_finite_image_eq {α β : Type} {f : α → β} (hf : Function.Surjective f)
    {Y : Set β} (hY : Y.Finite) : ∃ X : Set α, X.Finite ∧ f '' X = Y := by
  classical
  choose g hg using hf
  refine ⟨g '' Y, hY.image g, ?_⟩
  rw [Set.image_image]
  exact (Set.image_congr fun y _ => hg y).trans (Set.image_id Y)

/-- The witness at the base: the tuples whose arrow agrees on `X` with `k ∘ j` for some
`⟨x̄, j⟩` in the intension. -/
def pullback {ρ : RTy} {V : C} (k : W₀ ⟶ V) (X : Set ((A).Dom W₀ .e)) (b : Intension (A).inner ρ V) :
    Intension (A).inner ρ W₀ :=
  {p | ∃ j : V ⟶ p.1, AgreeOn ((A).inner .e) X p.2.2 (k ≫ j) ∧ (⟨p.1, p.2.1, j⟩ : Tuple (A).inner ρ V) ∈ b}

theorem pullback_pinned {ρ : RTy} {V : C} (k : W₀ ⟶ V) (X : Set ((A).Dom W₀ .e))
    (b : Intension (A).inner ρ V) : (A).PinnedO (.rel ρ) X (pullback De k X b) := by
  intro U h i ha
  simp only [Outer.map_rel]
  ext ⟨T, a, l⟩
  simp only [Intension.mem_map, pullback, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j, hj, hb⟩
    exact ⟨j, ((ha.comp_right _ l).symm _).trans _ hj, hb⟩
  · rintro ⟨j, hj, hb⟩
    exact ⟨j, (ha.comp_right _ l).trans _ hj, hb⟩

theorem map_pullback {ρ : RTy} {V : C} (k : W₀ ⟶ V) {X : Set ((A).Dom W₀ .e)} {Y : Set ((A).Dom V .e)}
    (hXY : ((A).inner .e).map k '' X = Y) {b : Intension (A).inner ρ V} (hb : (A).PinnedO (.rel ρ) Y b) :
    Intension.map (A).inner k (pullback De k X b) = b := by
  subst hXY
  ext ⟨T, a, l⟩
  simp only [Intension.mem_map, pullback, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨j, hj, hb'⟩
    -- `l` and `j` agree on `k[X]`, so `b` contains `⟨a, l⟩` iff it contains `⟨a, j⟩`
    have e := hb T l j (by
      rintro y ⟨x, hx, rfl⟩
      have := hj x hx
      simpa [Functor.map_comp, types_comp_apply] using this)
    simp only [Outer.map_rel] at e
    have := congrArg (fun S : Intension (A).inner ρ T => (⟨T, a, 𝟙 T⟩ : Tuple (A).inner ρ T) ∈ S) e
    simp only [Intension.mem_map, Category.comp_id] at this
    exact this.mpr hb'
  · intro hb'
    exact ⟨l, AgreeOn.refl _ _ _, hb'⟩

/-- An arrow out of the base surjective on individuals is surjective on every domain. -/
theorem ideal_map_surjective_of {V : C} (k : W₀ ⟶ V) (hk : Function.Surjective (De.map k)) :
    ∀ σ : Ty, Function.Surjective (((A).inner σ).map k)
  | .e => hk
  | .var _ => hk
  | .rel ρ => by
    intro b
    obtain ⟨Y, hY, hb⟩ := ideal_inner_finPinned De (.rel ρ) V b
    obtain ⟨X, hX, hXY⟩ := exists_finite_image_eq (f := ((A).inner .e).map k) hk hY
    obtain ⟨a, ha⟩ := ideal_pinned_inner De ρ W₀ (pullback De k X ((A).Incl _ V b))
      ⟨X, hX, pullback_pinned De k X _⟩
    refine ⟨a, (A).Incl_injective _ V ?_⟩
    rw [(A).Incl_map, Outer.map_rel, (A).Incl_rel ρ W₀ a, ha, map_pullback De k hXY hb]

/-- Every arrow out of the base surjective on individuals is surjective on every domain. -/
theorem ideal_map_surjective (hs : ∀ {V : C} (k : W₀ ⟶ V), Function.Surjective (De.map k)) :
    ∀ (σ : Ty) {V : C} (k : W₀ ⟶ V), Function.Surjective (((A).inner σ).map k) :=
  fun σ _ k => ideal_map_surjective_of De k (hs k) σ

/-- **Proposition D.6.** If every arrow out of the base is surjective on individuals,
`BF_σ` holds at the base for every `σ`. -/
theorem ideal_bf_of_surjective (hs : ∀ {V : C} (k : W₀ ⟶ V), Function.Surjective (De.map k)) (σ : Ty) :
    (A).HoldsSentence (Sentence.bf σ) :=
  (A).holds_bf_of_surjective (ideal_isModel De) σ (𝟙 W₀) fun k => ideal_map_surjective De hs σ k

/-! ### Surjective off any finite set gives `BF`

The paper's argument for the monoid of all functions on `ℕ` (Appendix D, Part 3, and the
two-object model after Part 8): `BF` needs less than every arrow being surjective. It is
enough that every arrow out of the base agrees, on any finite set, with an arrow that is
surjective on individuals. For if `∀y □Xy` at the base while `⟨a, k⟩` is not in the
value of `X`, with `X` pinned down by a finite `N`, take `j` agreeing with `k` on `N` and
surjective, so that `a = j^σ b` for some `b`; then `□Xb` puts `⟨a, j⟩` in `X`, and so, by
pinning, `⟨a, k⟩`. -/

/-- **`BF` from approximation by surjections.** If every arrow out of the base agrees on
any finite set of individuals with an arrow surjective on individuals, `BF_σ` holds at the
base for every `σ`. -/
theorem ideal_bf_of_approx
    (happrox : ∀ {V : C} (k : W₀ ⟶ V) (N : Set (De.obj W₀)), N.Finite →
      ∃ j : W₀ ⟶ V, AgreeOn De N k j ∧ Function.Surjective (De.map j)) (σ : Ty) :
    (A).HoldsSentence (Sentence.bf σ) := by
  have Mo : (A).IsModel := ideal_isModel De
  have key : ∀ (X : (A).Dom W₀ (.rel (σ ⇒ RTy.t))) {V : C} (l : W₀ ⟶ V) (c : (A).Dom V σ),
      (A).Holds (𝟙 W₀ ≫ l) (Term.app Term.v1 Term.v0) (.cons c ((A).push l (.cons X .nil))) ↔
        (⟨V, (c, PUnit.unit), l⟩ : Tuple (A).inner (σ ⇒ RTy.t) W₀) ∈ (A).incl _ W₀ X :=
    fun X _ l c => (A).holds_app_push (𝟙 W₀) l X c .nil
  simp only [HoldsSentence, Sentence.bf, (A).holds_forall Mo, (A).holds_imp Mo, (A).holds_box Mo]
  intro X H V k a
  obtain ⟨N, hN, hX⟩ := ideal_inner_finPinned De (.rel (σ ⇒ RTy.t)) W₀ X
  obtain ⟨j, hj, hsj⟩ := happrox k N hN
  obtain ⟨b, rfl⟩ := ideal_map_surjective_of De j hsj σ a
  have hb := (key X j _).1 (H b j)
  -- pinning moves `⟨j^σ b, j⟩` to `⟨j^σ b, k⟩`
  have e : Intension.map (A).inner k ((A).incl _ W₀ X) = Intension.map (A).inner j ((A).incl _ W₀ X) :=
    hX V k j hj
  have := congrArg (fun S : Intension (A).inner (σ ⇒ RTy.t) V =>
    (⟨V, (((A).inner σ).map j b, PUnit.unit), 𝟙 V⟩ : Tuple (A).inner (σ ⇒ RTy.t) V) ∈ S) e
  simp only [Intension.mem_map, Category.comp_id] at this
  have h1 := (Intension.mem_map (A).inner k _ _).1 (Eq.mpr this hb)
  simp only [Category.comp_id] at h1
  exact (key X k _).2 h1

end Premodel

end Classicism.Meta.Intensional
