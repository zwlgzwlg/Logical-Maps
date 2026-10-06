import Classicism.Semantics.IdeallyFull

/-!
# Symmetric intensions, and symmetric ideally full models

Dorr, *Boolean Completeness does not imply Rigid Comprehension* (draft of 30 July 2026),
§2, Definitions 15–18 and Proposition 20. A **base** adds to a category a group `G_W` of
automorphisms of each object (Definition 15). An intension `A` at `W` is **symmetric**
when `⟨x̄, h⟩ ∈ A` gives `⟨g x̄, g ∘ h⟩ ∈ A` for every `g ∈ G_{trg h}` (Definition 17):
relabelling the world `h` by `g` turns it into `g ∘ h` and the arguments into `g x̄`, and `A`
is indifferent to that. The **symmetric ideally full premodel** has as its relational
domains the intensions that are symmetric and finitely pinned (Definition 18), or, with the
per-object ideals of Appendix D, pinned down by a member of the ideal at their object
(`PinIdeal`; the draft's §6 puts the improper ideal at an object).

Here `G` is any family of sets of arrows `G V ⊆ (V ⟶ V)` closed under inverses
(`SymGroup.inv`), which is all the proofs use; in `Lean`, `h ≫ g` is `g ∘ h`.

- **Symmetry is preserved** by the action of arrows (`Sym.map`, Lemma 19(i)) and by
  application to any argument (`sym_apply`, Lemma 19(iii)); and the reading of every
  logical constant is symmetric when the domains are (`sym_negRead` and the rest).
- **Every term denotes a symmetric intension** when the domains are symmetric
  (`sem_symmetric`), by induction on terms: an abstraction because its value moves along
  `g` as the value of its body does (`sem_push`).
- **Proposition 20**: a premodel whose relational domains are exactly the symmetric
  finitely pinned intensions is a model (`isModel_of_pinned_sym`), combining this with the
  induction of Proposition D.4 (`sem_pinned`). The construction itself is
  `Premodel.symIdeal`, a model by `symIdeal_isModel`.
-/

namespace Classicism.Meta.Intensional

open CategoryTheory

variable {C : Type} [SmallCategory C]

/-- The symmetries at each object are closed under inverses: the condition that makes the
symmetry condition a biconditional (Dorr's draft, after Definition 17). -/
def SymGroup (G : ∀ V : C, Set (V ⟶ V)) : Prop :=
  ∀ (V : C) (g : V ⟶ V), g ∈ G V → ∃ g' ∈ G V, g ≫ g' = 𝟙 V ∧ g' ≫ g = 𝟙 V

/-- **An ideal of pinning sets** at each object, as in Appendix D's per-object ideals: it holds
the finite sets and is closed under binary unions and under images along arrows. The domains of
a symmetric ideally full premodel hold the symmetric intensions pinned down by a member of the
ideal at their object; the improper ideal, every set, admits every symmetric intension. -/
structure PinIdeal (De : C ⥤ Type) where
  mem : ∀ W : C, Set (Set (De.obj W))
  finite : ∀ {W : C} {N : Set (De.obj W)}, N.Finite → N ∈ mem W
  union : ∀ {W : C} {N M : Set (De.obj W)}, N ∈ mem W → M ∈ mem W → N ∪ M ∈ mem W
  image : ∀ {W V : C} (h : W ⟶ V) {N : Set (De.obj W)}, N ∈ mem W → De.map h '' N ∈ mem V

/-- The ideal of finite sets at every object. -/
def PinIdeal.fin (De : C ⥤ Type) : PinIdeal De where
  mem _ := {N | N.Finite}
  finite h := h
  union h₁ h₂ := Set.Finite.union h₁ h₂
  image _ _ h := h.image _

/-- The ideal is closed under finite unions. -/
theorem PinIdeal.biUnion {De : C ⥤ Type} (J : PinIdeal De) {ι : Type*} {s : Set ι} (hs : s.Finite)
    {W : C} {f : ι → Set (De.obj W)} (hf : ∀ i ∈ s, f i ∈ J.mem W) : (⋃ i ∈ s, f i) ∈ J.mem W := by
  classical
  have key : ∀ T : Finset ι, (∀ i ∈ T, f i ∈ J.mem W) → (⋃ i ∈ (T : Set ι), f i) ∈ J.mem W := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; simpa using J.finite Set.finite_empty
    | insert a T _ ih =>
      intro h
      rw [Finset.coe_insert, Set.biUnion_insert]
      exact J.union (h a (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
  simpa using key hs.toFinset fun i hi => hf i (hs.mem_toFinset.1 hi)

namespace Premodel

variable {Sig : Signature} (B : Premodel Sig C) (G : ∀ V : C, Set (V ⟶ V))

/-- **A symmetric intension** (Definition 17). -/
def Sym {ρ : RTy} {W : C} (A : Intension B.inner ρ W) : Prop :=
  ∀ (V : C) (a : Args B.inner ρ V) (k : W ⟶ V) (g : V ⟶ V), g ∈ G V →
    (⟨V, a, k⟩ : Tuple B.inner ρ W) ∈ A → (⟨V, Args.map B.inner ρ g a, k ≫ g⟩ : Tuple B.inner ρ W) ∈ A

/-- Symmetry of an outer element: of an intension; nothing at `e`. -/
def SymO : ∀ (σ : Ty) {W : C}, Outer B.inner σ W → Prop
  | .rel _, _, A => B.Sym G A
  | .e, _, _ => True
  | .var _, _, _ => True

/-- The domains are symmetric: every inner relation is. -/
def DomSym : Prop := ∀ (ρ : RTy) (W : C) (x : B.Dom W (.rel ρ)), B.Sym G (B.incl ρ W x)

variable {B G}

theorem symO_Incl (hD : B.DomSym G) : ∀ (σ : Ty) (W : C) (x : B.Dom W σ), B.SymO G σ (B.Incl σ W x)
  | .rel ρ, W, x => hD ρ W x
  | .e, _, _ => trivial
  | .var _, _, _ => trivial

/-- With inverses, symmetry is a biconditional. -/
theorem Sym.iff (hG : SymGroup G) {ρ : RTy} {W : C} {A : Intension B.inner ρ W} (hA : B.Sym G A)
    {V : C} (a : Args B.inner ρ V) (k : W ⟶ V) {g : V ⟶ V} (hg : g ∈ G V) :
    (⟨V, Args.map B.inner ρ g a, k ≫ g⟩ : Tuple B.inner ρ W) ∈ A ↔ (⟨V, a, k⟩ : Tuple B.inner ρ W) ∈ A := by
  refine ⟨fun h => ?_, hA V a k g hg⟩
  obtain ⟨g', hg', e₁, -⟩ := hG V g hg
  have := hA V _ _ g' hg' h
  rwa [← Args.map_comp, e₁, Args.map_id, Category.assoc, e₁, Category.comp_id] at this

/-- An element of an inner domain moved by `g` and back. -/
theorem map_map_inv {σ : Ty} {V : C} {g g' : V ⟶ V} (e : g' ≫ g = 𝟙 V) (x : B.Dom V σ) :
    (B.inner σ).map g ((B.inner σ).map g' x) = x := by
  rw [← FunctorToTypes.map_comp_apply, e, FunctorToTypes.map_id_apply]

theorem args_map_map_inv {ρ : RTy} {V : C} {g g' : V ⟶ V} (e : g' ≫ g = 𝟙 V) (a : Args B.inner ρ V) :
    Args.map B.inner ρ g (Args.map B.inner ρ g' a) = a := by
  rw [← Args.map_comp, e, Args.map_id]

/-- **Lemma 19(i)**: the action of an arrow preserves symmetry. -/
theorem Sym.map {ρ : RTy} {W V : C} (h : W ⟶ V) {A : Intension B.inner ρ W} (hA : B.Sym G A) :
    B.Sym G (Intension.map B.inner h A) := by
  intro U a k g hg ha
  simp only [Intension.mem_map] at ha ⊢
  rw [← Category.assoc]
  exact hA U a (h ≫ k) g hg ha

/-- **Lemma 19(iii)**, symmetry: applying a symmetric intension to any argument. -/
theorem sym_apply {σ : Ty} {ρ : RTy} {W : C} {F : Intension B.inner (.arr σ ρ) W}
    (hF : B.Sym G F) (x : Outer B.inner σ W) : B.Sym G (B.apply F x) := by
  rintro V a k g hg ⟨x', hx', hF'⟩
  refine ⟨(B.inner σ).map g x', ?_, hF V (x', a) k g hg hF'⟩
  rw [B.Incl_map, hx', Outer.map_comp]

/-! ### The readings of the logical constants are symmetric -/

section readings

/-- Symmetry at the identity: `⟨x̄, 1⟩ ∈ A` gives `⟨g x̄, g⟩ ∈ A`. -/
theorem Sym.at_id {ρ : RTy} {V : C} {A : Intension B.inner ρ V} (hA : B.Sym G A) (a : Args B.inner ρ V)
    {g : V ⟶ V} (hg : g ∈ G V) (h : (⟨V, a, 𝟙 V⟩ : Tuple B.inner ρ V) ∈ A) :
    (⟨V, Args.map B.inner ρ g a, g⟩ : Tuple B.inner ρ V) ∈ A := by
  have := hA V a (𝟙 V) g hg h
  rwa [Category.id_comp] at this

theorem Sym.at_id_iff (hG : SymGroup G) {ρ : RTy} {V : C} {A : Intension B.inner ρ V} (hA : B.Sym G A)
    (a : Args B.inner ρ V) {g : V ⟶ V} (hg : g ∈ G V) :
    (⟨V, Args.map B.inner ρ g a, g⟩ : Tuple B.inner ρ V) ∈ A ↔ (⟨V, a, 𝟙 V⟩ : Tuple B.inner ρ V) ∈ A := by
  have := Sym.iff hG hA a (𝟙 V) hg
  rwa [Category.id_comp] at this

/-- The value of a relation moved by `g` at a tuple, at the identity. -/
theorem mem_incl_map_id {ρ : RTy} {V : C} (X : B.Dom V (.rel ρ)) (b : Args B.inner ρ V) (g : V ⟶ V) :
    (⟨V, b, 𝟙 V⟩ : Tuple B.inner ρ V) ∈ B.incl ρ V ((B.inner (.rel ρ)).map g X) ↔
      (⟨V, b, g⟩ : Tuple B.inner ρ V) ∈ B.incl ρ V X := by
  rw [B.incl_map, Intension.mem_map, Category.comp_id]

variable (hG : SymGroup G) (hD : B.DomSym G)
include hG hD

theorem sym_negRead (ρ : RTy) (W : C) : B.Sym G (B.negRead ρ W) := by
  rintro V ⟨X, a⟩ k g hg (hX : _ ∉ _)
  show (⟨V, Args.map B.inner ρ g a, 𝟙 V⟩ : Tuple B.inner ρ V) ∉ B.incl ρ V ((B.inner (.rel ρ)).map g X)
  rw [mem_incl_map_id, Sym.at_id_iff hG (hD ρ V X) a hg]
  exact hX

theorem sym_andRead (ρ : RTy) (W : C) : B.Sym G (B.andRead ρ W) := by
  rintro V ⟨X, Y, a⟩ k g hg ⟨hX, hY⟩
  show (⟨V, Args.map B.inner ρ g a, 𝟙 V⟩ : Tuple B.inner ρ V) ∈ B.incl ρ V ((B.inner (.rel ρ)).map g X) ∧
    (⟨V, Args.map B.inner ρ g a, 𝟙 V⟩ : Tuple B.inner ρ V) ∈ B.incl ρ V ((B.inner (.rel ρ)).map g Y)
  rw [mem_incl_map_id, mem_incl_map_id]
  exact ⟨Sym.at_id (hD ρ V X) a hg hX, Sym.at_id (hD ρ V Y) a hg hY⟩

theorem sym_orRead (ρ : RTy) (W : C) : B.Sym G (B.orRead ρ W) := by
  rintro V ⟨X, Y, a⟩ k g hg (hXY : _ ∨ _)
  show (⟨V, Args.map B.inner ρ g a, 𝟙 V⟩ : Tuple B.inner ρ V) ∈ B.incl ρ V ((B.inner (.rel ρ)).map g X) ∨
    (⟨V, Args.map B.inner ρ g a, 𝟙 V⟩ : Tuple B.inner ρ V) ∈ B.incl ρ V ((B.inner (.rel ρ)).map g Y)
  rw [mem_incl_map_id, mem_incl_map_id]
  exact hXY.imp (Sym.at_id (hD ρ V X) a hg) (Sym.at_id (hD ρ V Y) a hg)

theorem sym_constRead (ρ : RTy) (W : C) : B.Sym G (B.constRead ρ W) := by
  rintro V ⟨p, a⟩ k g hg (hp : (⟨V, PUnit.unit, 𝟙 V⟩ : Tuple B.inner .t V) ∈ B.incl .t V p)
  show (⟨V, PUnit.unit, 𝟙 V⟩ : Tuple B.inner .t V) ∈ B.incl .t V ((B.inner (.rel .t)).map g p)
  rw [mem_incl_map_id]
  exact Sym.at_id (hD .t V p) PUnit.unit hg hp

theorem sym_allRead (σ : Ty) (W : C) : B.Sym G (B.allRead σ W) := by
  rintro V ⟨X, ⟨⟩⟩ k g hg (hX : ∀ a, _)
  intro a
  show (⟨V, (a, PUnit.unit), 𝟙 V⟩ : Tuple B.inner (.arr σ .t) V) ∈
    B.incl (.arr σ .t) V ((B.inner (.rel (.arr σ .t))).map g X)
  obtain ⟨g', -, -, e₂⟩ := hG V g hg
  rw [mem_incl_map_id, ← B.map_map_inv e₂ a]
  exact Sym.at_id (hD _ V X) (((B.inner σ).map g' a), PUnit.unit) hg (hX _)

theorem sym_exRead (σ : Ty) (W : C) : B.Sym G (B.exRead σ W) := by
  rintro V ⟨X, ⟨⟩⟩ k g hg ⟨a, hX⟩
  refine ⟨(B.inner σ).map g a, ?_⟩
  show (⟨V, ((B.inner σ).map g a, PUnit.unit), 𝟙 V⟩ : Tuple B.inner (.arr σ .t) V) ∈
    B.incl (.arr σ .t) V ((B.inner (.rel (.arr σ .t))).map g X)
  rw [mem_incl_map_id]
  exact Sym.at_id (hD _ V X) (a, PUnit.unit) hg hX

theorem sym_eqRead (σ : Ty) (W : C) : B.Sym G (B.eqRead σ W) := by
  rintro V ⟨x, y, ⟨⟩⟩ k g hg (hxy : x = y)
  show (B.inner σ).map g x = (B.inner σ).map g y
  rw [hxy]

theorem sym_coextRead (ρ : RTy) (W : C) : B.Sym G (B.coextRead ρ W) := by
  rintro V ⟨X, Y, ⟨⟩⟩ k g hg (hXY : ∀ a, _)
  intro a
  show (⟨V, a, 𝟙 V⟩ : Tuple B.inner ρ V) ∈ B.incl ρ V ((B.inner (.rel ρ)).map g X) ↔
    (⟨V, a, 𝟙 V⟩ : Tuple B.inner ρ V) ∈ B.incl ρ V ((B.inner (.rel ρ)).map g Y)
  obtain ⟨g', -, -, e₂⟩ := hG V g hg
  rw [mem_incl_map_id, mem_incl_map_id, ← B.args_map_map_inv e₂ a,
    Sym.at_id_iff hG (hD ρ V X) _ hg, Sym.at_id_iff hG (hD ρ V Y) _ hg]
  exact hXY _

theorem sym_inclRead (ρ : RTy) (W : C) : B.Sym G (B.inclRead ρ W) := by
  rintro V ⟨X, Y, ⟨⟩⟩ k g hg (hXY : ∀ a, _)
  intro a
  show (⟨V, a, 𝟙 V⟩ : Tuple B.inner ρ V) ∈ B.incl ρ V ((B.inner (.rel ρ)).map g X) →
    (⟨V, a, 𝟙 V⟩ : Tuple B.inner ρ V) ∈ B.incl ρ V ((B.inner (.rel ρ)).map g Y)
  obtain ⟨g', -, -, e₂⟩ := hG V g hg
  rw [mem_incl_map_id, mem_incl_map_id, ← B.args_map_map_inv e₂ a,
    Sym.at_id_iff hG (hD ρ V X) _ hg, Sym.at_id_iff hG (hD ρ V Y) _ hg]
  exact hXY _

omit hG hD in
theorem sym_boxRead (ρ : RTy) (W : C) : B.Sym G (B.boxRead ρ W) := by
  rintro V ⟨X, a⟩ k g hg (hX : ∀ U j, _)
  intro U j
  show (⟨U, Args.map B.inner ρ j (Args.map B.inner ρ g a), j⟩ : Tuple B.inner ρ V) ∈
    B.incl ρ V ((B.inner (.rel ρ)).map g X)
  rw [B.incl_map, Intension.mem_map, ← Args.map_comp]
  exact hX U (g ≫ j)

end readings

/-! ### Every term denotes a symmetric intension -/

/-- **The symmetry half of Proposition 20.** If the domains are symmetric and the
symmetries are closed under inverses, the value of every term, under any assignment, is
symmetric. -/
theorem sem_symmetric (hG : SymGroup G) (hD : B.DomSym G) :
    ∀ {Γ : Ctx} {σ : Ty} {W : C} (h : B.W₀ ⟶ W) (t : Term Sig Γ σ) (g : IEnv (B.Dom W) Γ),
      B.SymO G σ (B.sem h t g)
  | _, _, W, _, .var v, g => symO_Incl hD _ W (g.get v)
  | _, _, W, h, .const c, _ => symO_Incl hD _ W _
  | _, _, _, h, .app f a, g => sym_apply (sem_symmetric hG hD h f g) _
  | _, _, W, h, .lam (σ := σ) (ρ := ρ) b, g => by
    rintro V ⟨x, a⟩ k s hs hb
    rw [mem_sem_lam] at hb ⊢
    -- the body's value is symmetric, and moves along `s` as the body does (`sem_push`)
    have h1 := Sym.at_id (sem_symmetric hG hD (h ≫ k) b (.cons x (B.push k g))) a hs hb
    have hp := B.sem_push (h ≫ k) b (.cons x (B.push k g)) s
    have e2 : B.push s (IEnv.cons x (B.push k g)) =
        IEnv.cons ((B.inner σ).map s x) (B.push (k ≫ s) g) := by
      show IEnv.cons ((B.inner σ).map s x) (B.push s (B.push k g)) = _
      rw [B.push_push]
    rw [← Category.assoc]
    show (⟨V, Args.map B.inner ρ s a, 𝟙 V⟩ : Tuple B.inner ρ V) ∈
      B.sem ((h ≫ k) ≫ s) b (IEnv.cons ((B.inner σ).map s x) (B.push (k ≫ s) g))
    rw [← e2, hp]
    show _ ∈ Intension.map B.inner s _
    rw [Intension.mem_map, Category.comp_id]
    exact h1
  | _, _, W, _, .and, _ => sym_andRead hG hD _ W
  | _, _, W, _, .or, _ => sym_orRead hG hD _ W
  | _, _, W, _, .not, _ => sym_negRead hG hD _ W
  | _, _, W, _, .all _, _ => sym_allRead hG hD _ W
  | _, _, W, _, .ex _, _ => sym_exRead hG hD _ W
  | _, _, W, _, .eq _, _ => sym_eqRead hG hD _ W
  | _, _, W, _, .constR _, _ => sym_constRead hG hD _ W
  | _, _, W, _, .negR _, _ => sym_negRead hG hD _ W
  | _, _, W, _, .andR _, _ => sym_andRead hG hD _ W
  | _, _, W, _, .orR _, _ => sym_orRead hG hD _ W
  | _, _, W, _, .coextR _, _ => sym_coextRead hG hD _ W
  | _, _, W, _, .boxR _, _ => sym_boxRead _ W
  | _, _, W, _, .inclR _, _ => sym_inclRead hG hD _ W

/-- The values of an assignment are pinned by one member of the ideal. -/
theorem env_idealPinned (J : PinIdeal (B.inner .e))
    (hfin : ∀ (σ : Ty) (W : C) (x : B.Dom W σ), ∃ N, N ∈ J.mem W ∧ B.PinnedO σ N (B.Incl σ W x)) :
    ∀ {Γ : Ctx} {W : C} (g : IEnv (B.Dom W) Γ),
      ∃ N, N ∈ J.mem W ∧ ∀ τ (v : Var Γ τ), B.PinnedO τ N (B.Incl τ W (g.get v))
  | _, _, .nil => ⟨∅, J.finite Set.finite_empty, fun _ v => nomatch v⟩
  | _, _, .cons x g => by
    obtain ⟨N, hN, hg⟩ := env_idealPinned J hfin g
    obtain ⟨M, hM, hx⟩ := hfin _ _ x
    refine ⟨N ∪ M, J.union hN hM, fun τ v => ?_⟩
    cases v with
    | zero => exact PinnedO.mono B Set.subset_union_right hx
    | succ v => exact PinnedO.mono B Set.subset_union_left (hg _ v)

/-- The constants a term mentions, moved along an arrow, are pinned by one member of the ideal. -/
theorem consts_idealPinned (J : PinIdeal (B.inner .e))
    (hfin : ∀ (σ : Ty) (W : C) (x : B.Dom W σ), ∃ N, N ∈ J.mem W ∧ B.PinnedO σ N (B.Incl σ W x))
    {Γ : Ctx} {σ : Ty} {W : C} (h : B.W₀ ⟶ W) (t : Term Sig Γ σ) :
    ∃ N, N ∈ J.mem W ∧
      ∀ c ∈ t.consts, B.PinnedO _ N (B.Incl _ W ((B.inner _).map h (B.I c))) := by
  classical
  choose N hN using fun c : Sig.Const => hfin (Sig.typeOf c) W ((B.inner _).map h (B.I c))
  refine ⟨⋃ c ∈ t.consts, N c, J.biUnion (Term.consts_finite t) fun c _ => (hN c).1, fun c hc => ?_⟩
  exact PinnedO.mono B (Set.subset_biUnion_of_mem (u := N) hc) (hN c).2

/-- **Proposition 20, abstractly.** A premodel whose inner elements are pinned down by members
of an ideal and symmetric, and whose domains hold every symmetric intension so pinned, is a
model. -/
theorem isModel_of_pinned_sym (J : PinIdeal (B.inner .e)) (hG : SymGroup G) (hD : B.DomSym G)
    (hfin : ∀ (σ : Ty) (W : C) (x : B.Dom W σ), ∃ N, N ∈ J.mem W ∧ B.PinnedO σ N (B.Incl σ W x))
    (hinner : ∀ (ρ : RTy) (W : C) (F : Intension B.inner ρ W),
      (∃ N, N ∈ J.mem W ∧ B.PinnedO (.rel ρ) N F) → B.Sym G F →
        F ∈ Set.range (B.incl ρ W)) :
    B.IsModel := fun {_ σ W} h t g => by
  obtain ⟨N, hN, hg⟩ := B.env_idealPinned J hfin g
  obtain ⟨M, hM, hc⟩ := B.consts_idealPinned J hfin h t
  have hp := B.sem_pinned h t g (N ∪ M)
    (fun τ v => PinnedO.mono B Set.subset_union_left (hg τ v))
    (fun c hc' => PinnedO.mono B Set.subset_union_right (hc c hc'))
  have hs := sem_symmetric hG hD h t g
  cases σ with
  | e => exact ⟨_, rfl⟩
  | rel ρ => exact hinner ρ W _ ⟨N ∪ M, J.union hN hM, hp⟩ hs
  | var _ => exact ⟨_, rfl⟩

end Premodel


/-! ### The symmetric ideally full premodel (Definition 18) -/

section construction

variable (De : C ⥤ Type) (G : ∀ V : C, Set (V ⟶ V)) (J : PinIdeal De)

/-- Pinned down by a member of the ideal. -/
def IdealPinned (F : C ⥤ Type) {W : C} (x : F.obj W) : Prop :=
  ∃ N, N ∈ J.mem W ∧ PinnedBy De F N x

theorem IdealPinned.map {F : C ⥤ Type} {W V : C} {x : F.obj W} (hx : IdealPinned De J F x) (h : W ⟶ V) :
    IdealPinned De J F (F.map h x) :=
  let ⟨N, hN, hp⟩ := hx
  ⟨De.map h '' N, J.image h hN, hp.map De h⟩

/-- Symmetry of a raw intension over an action of arguments. -/
def RawSym (F : C ⥤ Type) {W : C} (A : (intensionAction F).obj W) : Prop :=
  ∀ (V : C) (a : F.obj V) (k : W ⟶ V) (g : V ⟶ V), g ∈ G V →
    (⟨V, a, k⟩ : Σ V : C, F.obj V × (W ⟶ V)) ∈ A → (⟨V, F.map g a, k ≫ g⟩ : Σ V : C, F.obj V × (W ⟶ V)) ∈ A

/-- **Lemma 19(i)**, for raw intensions. -/
theorem RawSym.map {F : C ⥤ Type} {W V : C} (h : W ⟶ V) {A : (intensionAction F).obj W}
    (hA : RawSym G F A) : RawSym G F ((intensionAction F).map h A) := by
  intro U a k g hg ha
  have := hA U a (h ≫ k) g hg ha
  show (⟨U, F.map g a, h ≫ (k ≫ g)⟩ : Σ V : C, F.obj V × (W ⟶ V)) ∈ A
  rwa [← Category.assoc]

/-- The subaction of the symmetric finitely pinned intensions over an action of arguments. -/
abbrev symPinnedAction (F : C ⥤ Type) : C ⥤ Type where
  obj W := {A : (intensionAction F).obj W // IdealPinned De J (intensionAction F) A ∧ RawSym G F A}
  map {W V} h := TypeCat.ofHom fun A => ⟨(intensionAction F).map h A.1, A.2.1.map De J h, RawSym.map G h A.2.2⟩
  map_id W := by
    ext ⟨x, hx⟩ : 3
    simp
  map_comp h i := by
    ext ⟨x, hx⟩ : 3
    simp

/-- The symmetric ideally full inner action at a type: `De` at `e`; at a relational type,
the symmetric finitely pinned intensions over its arguments. -/
noncomputable abbrev SymT (σ : Ty) : C ⥤ Type :=
  @Ty.rec (fun _ => C ⥤ Type) (fun _ => C ⥤ Type) De
    (fun _ ih => symPinnedAction De G J ih) (fun _ => De)
    pointAction (fun _ _ ihσ ihρ => prodAction ihσ ihρ) σ

/-- The arguments of a relational type, as an action. -/
noncomputable abbrev SymArgs (ρ : RTy) : C ⥤ Type :=
  @RTy.rec (fun _ => C ⥤ Type) (fun _ => C ⥤ Type) De
    (fun _ ih => symPinnedAction De G J ih) (fun _ => De)
    pointAction (fun _ _ ihσ ihρ => prodAction ihσ ihρ) ρ

/-- The symmetric ideally full inner action at a relational type. -/
noncomputable abbrev SymR (ρ : RTy) : C ⥤ Type := symPinnedAction De G J (SymArgs De G J ρ)

example (ρ : RTy) : SymT De G J (.rel ρ) = SymR De G J ρ := rfl

/-- The raw intensions over the arguments. -/
abbrev SymRaw (ρ : RTy) (W : C) : Type := Set (Σ V : C, (SymArgs De G J ρ).obj V × (W ⟶ V))

/-- The two spellings of the arguments, related. -/
def symArgs : ∀ (ρ : RTy) (V : C), Args (SymT De G J) ρ V → (SymArgs De G J ρ).obj V
  | .t, _, _ => PUnit.unit
  | .arr _ ρ, V, a => (a.1, symArgs ρ V a.2)

def symArgs' : ∀ (ρ : RTy) (V : C), (SymArgs De G J ρ).obj V → Args (SymT De G J) ρ V
  | .t, _, _ => PUnit.unit
  | .arr _ ρ, V, a => (a.1, symArgs' ρ V a.2)

theorem symArgs_symArgs' : ∀ (ρ : RTy) (V : C) (a : (SymArgs De G J ρ).obj V),
    symArgs De G J ρ V (symArgs' De G J ρ V a) = a
  | .t, _, _ => rfl
  | .arr _ ρ, V, a => by
    show (a.1, symArgs De G J ρ V (symArgs' De G J ρ V a.2)) = a
    exact Prod.ext rfl (symArgs_symArgs' ρ V a.2)

theorem symArgs'_symArgs : ∀ (ρ : RTy) (V : C) (a : Args (SymT De G J) ρ V),
    symArgs' De G J ρ V (symArgs De G J ρ V a) = a
  | .t, _, _ => rfl
  | .arr _ ρ, V, a => by
    show (a.1, symArgs' De G J ρ V (symArgs De G J ρ V a.2)) = a
    exact Prod.ext rfl (symArgs'_symArgs ρ V a.2)

/-- The arrows act alike on the two spellings. -/
theorem symArgs_map : ∀ (ρ : RTy) {V V' : C} (j : V ⟶ V') (a : Args (SymT De G J) ρ V),
    symArgs De G J ρ V' (Args.map (SymT De G J) ρ j a) = (SymArgs De G J ρ).map j (symArgs De G J ρ V a)
  | .t, _, _, _, _ => rfl
  | .arr σ ρ, V, V', j, a => by
    show ((SymT De G J σ).map j a.1, symArgs De G J ρ V' (Args.map (SymT De G J) ρ j a.2)) =
      ((SymT De G J σ).map j a.1, (SymArgs De G J ρ).map j (symArgs De G J ρ V a.2))
    rw [symArgs_map ρ j a.2]

theorem symArgs'_map (ρ : RTy) {V V' : C} (j : V ⟶ V') (b : (SymArgs De G J ρ).obj V) :
    symArgs' De G J ρ V' ((SymArgs De G J ρ).map j b) = Args.map (SymT De G J) ρ j (symArgs' De G J ρ V b) := by
  rw [← symArgs_symArgs' De G J ρ V b, ← symArgs_map, symArgs'_symArgs, symArgs'_symArgs]

/-- A raw intension read as an intension, and back. -/
def symRead (ρ : RTy) (W : C) (A : SymRaw De G J ρ W) : Intension (SymT De G J) ρ W :=
  {p | (⟨p.1, symArgs De G J ρ p.1 p.2.1, p.2.2⟩ : Σ V : C, (SymArgs De G J ρ).obj V × (W ⟶ V)) ∈ A}

def symRead' (ρ : RTy) (W : C) (F : Intension (SymT De G J) ρ W) : SymRaw De G J ρ W :=
  {p | (⟨p.1, symArgs' De G J ρ p.1 p.2.1, p.2.2⟩ : Tuple (SymT De G J) ρ W) ∈ F}

theorem symRead_symRead' (ρ : RTy) (W : C) (F : Intension (SymT De G J) ρ W) :
    symRead De G J ρ W (symRead' De G J ρ W F) = F := by
  ext ⟨V, a, i⟩
  simp [symRead, symRead', symArgs'_symArgs]

theorem symRead'_symRead (ρ : RTy) (W : C) (A : SymRaw De G J ρ W) :
    symRead' De G J ρ W (symRead De G J ρ W A) = A := by
  ext ⟨V, a, i⟩
  simp [symRead, symRead', symArgs_symArgs']

theorem symRead_map (ρ : RTy) {W V : C} (h : W ⟶ V) (A : SymRaw De G J ρ W) :
    symRead De G J ρ V ((intensionAction (SymArgs De G J ρ)).map h A) =
      Intension.map (SymT De G J) h (symRead De G J ρ W A) := by
  ext ⟨U, a, i⟩
  exact Iff.rfl

theorem symRead'_map (ρ : RTy) {W V : C} (h : W ⟶ V) (F : Intension (SymT De G J) ρ W) :
    symRead' De G J ρ V (Intension.map (SymT De G J) h F) =
      (intensionAction (SymArgs De G J ρ)).map h (symRead' De G J ρ W F) := by
  ext ⟨U, a, i⟩
  exact Iff.rfl

/-- The inclusion of the domain into the intensions. -/
def symIncl (ρ : RTy) (W : C) (A : (SymR De G J ρ).obj W) : Intension (SymT De G J) ρ W :=
  symRead De G J ρ W A.1

theorem symIncl_map (ρ : RTy) {W V : C} (h : W ⟶ V) (A : (SymR De G J ρ).obj W) :
    symIncl De G J ρ V ((SymR De G J ρ).map h A) = Intension.map (SymT De G J) h (symIncl De G J ρ W A) :=
  symRead_map De G J ρ h A.1

theorem symIncl_injective (ρ : RTy) (W : C) : Function.Injective (symIncl De G J ρ W) := by
  intro A B e
  apply Subtype.ext
  have := congrArg (symRead' De G J ρ W) e
  rwa [symIncl, symIncl, symRead'_symRead, symRead'_symRead] at this

/-- Symmetry of an intension over the symmetric actions (`Premodel.Sym` for this premodel). -/
def SymCond {ρ : RTy} {W : C} (F : Intension (SymT De G J) ρ W) : Prop :=
  ∀ (V : C) (a : Args (SymT De G J) ρ V) (k : W ⟶ V) (g : V ⟶ V), g ∈ G V →
    (⟨V, a, k⟩ : Tuple (SymT De G J) ρ W) ∈ F → (⟨V, Args.map (SymT De G J) ρ g a, k ≫ g⟩ : Tuple (SymT De G J) ρ W) ∈ F

/-- An intension over the symmetric actions is in the domain iff it is finitely pinned and
symmetric. -/
theorem mem_range_symIncl (ρ : RTy) (W : C) (F : Intension (SymT De G J) ρ W) :
    F ∈ Set.range (symIncl De G J ρ W) ↔
      (∃ N : Set (De.obj W), N ∈ J.mem W ∧
        ∀ (V : C) (h i : W ⟶ V), AgreeOn De N h i →
          Intension.map (SymT De G J) h F = Intension.map (SymT De G J) i F) ∧ SymCond De G J F := by
  constructor
  · rintro ⟨⟨A, ⟨N, hN, hA⟩, hS⟩, rfl⟩
    refine ⟨⟨N, hN, fun V h i ha => ?_⟩, ?_⟩
    · show Intension.map (SymT De G J) h (symRead De G J ρ W A) = Intension.map (SymT De G J) i (symRead De G J ρ W A)
      rw [← symRead_map, ← symRead_map, hA V h i ha]
    · intro V a k g hg ha
      show (⟨V, symArgs De G J ρ V (Args.map (SymT De G J) ρ g a), k ≫ g⟩ : Σ V : C, (SymArgs De G J ρ).obj V × (W ⟶ V)) ∈ A
      rw [symArgs_map]
      exact hS V _ k g hg ha
  · rintro ⟨⟨N, hN, hF⟩, hS⟩
    refine ⟨⟨symRead' De G J ρ W F, ⟨N, hN, fun V h i ha => ?_⟩, ?_⟩, ?_⟩
    · show (intensionAction (SymArgs De G J ρ)).map h (symRead' De G J ρ W F)
        = (intensionAction (SymArgs De G J ρ)).map i (symRead' De G J ρ W F)
      rw [← symRead'_map, ← symRead'_map, hF V h i ha]
    · intro V b k g hg hb
      show (⟨V, symArgs' De G J ρ V ((SymArgs De G J ρ).map g b), k ≫ g⟩ : Tuple (SymT De G J) ρ W) ∈ F
      rw [symArgs'_map]
      exact hS V _ k g hg hb
    · exact symRead_symRead' De G J ρ W F

/-- **The symmetric ideally full premodel** (Definition 18): its relational domains are the
symmetric finitely pinned intensions. -/
noncomputable def _root_.Classicism.Meta.Intensional.Premodel.symIdeal {Sig : Signature} (W₀ : C)
    (nonempty_e : ∀ W : C, Nonempty (De.obj W))
    (I : ∀ c : Sig.Const, (SymT De G J (Sig.typeOf c)).obj W₀) : Premodel Sig C where
  W₀ := W₀
  inner := SymT De G J
  nonempty_e := nonempty_e
  incl := symIncl De G J
  incl_map := symIncl_map De G J
  incl_injective := symIncl_injective De G J
  I := I

variable {De G J} {Sig : Signature} {W₀ : C} {nonempty_e : ∀ W : C, Nonempty (De.obj W)}
  {I : ∀ c : Sig.Const, (SymT De G J (Sig.typeOf c)).obj W₀}

local notation "A" => Premodel.symIdeal De G J W₀ nonempty_e I

theorem symIdeal_domSym : (A).DomSym G := fun ρ W x =>
  ((mem_range_symIncl De G J ρ W _).1 ⟨x, rfl⟩).2

theorem symIdeal_inner_finPinned : ∀ (σ : Ty) (W : C) (x : (A).Dom W σ),
    ∃ N : Set ((A).Dom W .e), N ∈ J.mem W ∧ (A).PinnedO σ N ((A).Incl σ W x)
  | .e, W, x => ⟨{x}, J.finite (Set.finite_singleton x), fun _ _ _ ha => ha x rfl⟩
  | .rel ρ, W, x => ((mem_range_symIncl De G J ρ W _).1 ⟨x, rfl⟩).1
  | .var _, W, x => ⟨{x}, J.finite (Set.finite_singleton x), fun _ _ _ ha => ha x rfl⟩

/-- **Proposition 20: a symmetric ideally full premodel is an intensional action model.** -/
theorem symIdeal_isModel (hG : SymGroup G) : (A).IsModel :=
  (A).isModel_of_pinned_sym J hG symIdeal_domSym symIdeal_inner_finPinned
    fun ρ W F hp hs => (mem_range_symIncl De G J ρ W F).2 ⟨hp, hs⟩

end construction

end Classicism.Meta.Intensional
