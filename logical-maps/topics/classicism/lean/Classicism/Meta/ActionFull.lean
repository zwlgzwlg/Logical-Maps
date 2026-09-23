import Classicism.Meta.ActionSoundness
import Classicism.Meta.ActionFacts

/-!
# Full action models

The paper's *full* action models (Classicism, §"Exploring action models"): the inner
domain at `t` is the whole powerset action, and at `σ → ρ` the whole exponential action of
the inner domains at `σ` and `ρ`, the well-behaved functions on pairs `⟨h, x⟩`. A rooted
category, an action for `e` with nonempty domains, and an interpretation of the constants
then determine a full action premodel, and the theorem of this module is that it is an
action **model**: the value of every term is inner.

That is the paper's remark that a full premodel "uniquely determines a full action
model", and its proof is the induction the paper leaves implicit: inner-ness and the
transport lemma together (the application case of each needs the other), with the
logical constants checked one by one to be well-behaved, and the type-subscripted
operations by a second induction on the size of their type, since each reads as its
unfolding does.
-/

namespace Classicism.Meta

open CategoryTheory

variable {C : Type} [SmallCategory C]

/-! ### The powerset and exponential actions -/

/-- The powerset action: at `W`, the sets of arrows out of `W`; an arrow acts by division. -/
abbrev powerAction (C : Type) [SmallCategory C] : C ⥤ Type where
  obj W := Set (Σ V : C, W ⟶ V)
  map {W V} h := TypeCat.ofHom fun (X : Set (Σ U : C, W ⟶ U)) =>
    ({p : Σ U : C, V ⟶ U | (⟨p.1, h ≫ p.2⟩ : Σ U : C, W ⟶ U) ∈ X} : Set (Σ U : C, V ⟶ U))
  map_id W := by
    ext X ⟨V, i⟩; simp
  map_comp h i := by
    ext X ⟨V, j⟩; simp [Category.assoc]

/-- A well-behaved function on pairs `⟨h : W → V, x ∈ F V⟩` into `G`. -/
def ExpElem (F G : C ⥤ Type) (W : C) : Type :=
  {α : ∀ V : C, (W ⟶ V) → F.obj V → G.obj V //
    ∀ (V U : C) (h : W ⟶ V) (i : V ⟶ U) (x : F.obj V), G.map i (α V h x) = α U (h ≫ i) (F.map i x)}

/-- The exponential action of two actions: at `W` the well-behaved functions; an arrow
acts by precomposition. -/
def expAction (F G : C ⥤ Type) : C ⥤ Type where
  obj W := ExpElem F G W
  map {W V} h := TypeCat.ofHom fun (α : ExpElem F G W) =>
    (⟨fun U i x => α.1 U (h ≫ i) x, fun U T i j x => by
      rw [α.2 U T (h ≫ i) j x, Category.assoc]⟩ : ExpElem F G V)
  map_id W := by
    ext α : 3; apply Subtype.ext; funext U i x
    show α.1 U (𝟙 W ≫ i) x = α.1 U i x
    rw [Category.id_comp]
  map_comp h i := by
    ext α : 3; apply Subtype.ext; funext U j x
    show α.1 U ((h ≫ i) ≫ j) x = α.1 U (h ≫ (i ≫ j)) x
    rw [Category.assoc]

/-! ### The full inner domains -/

variable (De : C ⥤ Type)

/-- The full inner action at a type: `De` at `e`; at `t` the powerset action; at `σ → ρ`
the exponential of the full actions. Through the recursor of the mutual inductive, so
that it reduces by iota at a constructor. -/
noncomputable abbrev FullT (σ : Ty) : C ⥤ Type :=
  @Ty.rec (fun _ => C ⥤ Type) (fun _ => C ⥤ Type) De (fun _ ih => ih) (powerAction C)
    (fun _ _ ihσ ihρ => expAction ihσ ihρ) σ

/-- The same at a relational type. -/
noncomputable abbrev FullR (ρ : RTy) : C ⥤ Type :=
  @RTy.rec (fun _ => C ⥤ Type) (fun _ => C ⥤ Type) De (fun _ ih => ih) (powerAction C)
    (fun _ _ ihσ ihρ => expAction ihσ ihρ) ρ

example : FullT De .e = De := rfl
example (ρ : RTy) : FullT De (.rel ρ) = FullR De ρ := rfl
example : FullR De .t = powerAction C := rfl
example (σ : Ty) (ρ : RTy) : FullR De (.arr σ ρ) = expAction (FullT De σ) (FullR De ρ) := rfl

/-- The inclusion of the full inner domains into the outer ones: the identity at `t`, and
at an arrow the function's values included. -/
noncomputable def fullIncl : ∀ (ρ : RTy) (W : C), (FullR De ρ).obj W → RawR (FullT De) ρ W
  | .t, _, X => X
  | .arr _ ρ, _, α => fun V h x => fullIncl ρ V (α.1 V h x)

theorem fullIncl_map : ∀ (ρ : RTy) {W V : C} (h : W ⟶ V) (x : (FullR De ρ).obj W),
    fullIncl De ρ V ((FullR De ρ).map h x) = RawR.map (FullT De) ρ h (fullIncl De ρ W x)
  | .t, _, _, _, _ => rfl
  | .arr _ ρ, _, _, h, α => by
    funext U i x
    exact rfl

theorem fullIncl_injective : ∀ (ρ : RTy) (W : C), Function.Injective (fullIncl De ρ W)
  | .t, _ => fun _ _ e => e
  | .arr σ ρ, W => fun α β e => by
    apply Subtype.ext
    funext V h x
    exact fullIncl_injective ρ V (congrFun (congrFun (congrFun e V) h) x)

theorem fullIncl_wellBehaved (σ : Ty) (ρ : RTy) {W V U : C} (α : (FullR De (.arr σ ρ)).obj W)
    (h : W ⟶ V) (i : V ⟶ U) (x : (FullT De σ).obj V) :
    RawR.map (FullT De) ρ i (fullIncl De (.arr σ ρ) W α V h x)
      = fullIncl De (.arr σ ρ) W α U (h ≫ i) ((FullT De σ).map i x) := by
  exact (fullIncl_map De ρ i (α.1 V h x)).symm.trans (congrArg (fullIncl De ρ U) (α.2 V U h i x))

/-- The full action premodel on a rooted category, given the action for `e` and the
constants. -/
noncomputable def Premodel.full {Sig : Signature} (W₀ : C) (rooted : ∀ W : C, Nonempty (W₀ ⟶ W))
    (nonempty_e : ∀ W : C, Nonempty (De.obj W))
    (I : ∀ c : Sig.Const, (FullT De (Sig.typeOf c)).obj W₀) : Premodel Sig C where
  W₀ := W₀
  rooted := rooted
  inner := FullT De
  nonempty_e := nonempty_e
  incl := fullIncl De
  incl_map := fullIncl_map De
  incl_injective := fullIncl_injective De
  wellBehaved := fullIncl_wellBehaved De
  app_inner := fun _ _ {_ _} α h x => ⟨α.1 _ h x, rfl⟩
  I := I

/-! ### The full premodel is a model -/

namespace Premodel

variable {Sig : Signature} {W₀ : C} {rooted : ∀ W : C, Nonempty (W₀ ⟶ W)}
  {nonempty_e : ∀ W : C, Nonempty (De.obj W)}
  {I : ∀ c : Sig.Const, (FullT De (Sig.typeOf c)).obj W₀}

local notation "A" => Premodel.full De W₀ rooted nonempty_e I

/-- In a full premodel, an outer element of arrow type is inner iff its values are inner
and it is well-behaved. -/
theorem full_mem_range_arr {σ : Ty} {ρ : RTy} {W : C} (F : RawR (FullT De) (.arr σ ρ) W) :
    F ∈ Set.range (fullIncl De (.arr σ ρ) W) ↔
      (∀ (V : C) (h : W ⟶ V) (x : (FullT De σ).obj V), F V h x ∈ Set.range (fullIncl De ρ V)) ∧
      (∀ (V U : C) (h : W ⟶ V) (i : V ⟶ U) (x : (FullT De σ).obj V),
        RawR.map (FullT De) ρ i (F V h x) = F U (h ≫ i) ((FullT De σ).map i x)) := by
  constructor
  · rintro ⟨α, rfl⟩
    exact ⟨fun V h x => ⟨α.1 V h x, rfl⟩, fun V U h i x => fullIncl_wellBehaved De σ ρ α h i x⟩
  · rintro ⟨hv, hn⟩
    refine ⟨⟨fun V h x => (hv V h x).choose, fun V U h i x => ?_⟩, ?_⟩
    · apply fullIncl_injective De ρ
      exact (fullIncl_map De ρ i _).trans
        (((congrArg (RawR.map (FullT De) ρ i) (hv V h x).choose_spec).trans (hn V U h i x)).trans
          (hv U (h ≫ i) _).choose_spec.symm)
    · funext V h x
      exact (hv V h x).choose_spec

/-- Everything at `t` is inner. -/
theorem full_mem_range_t {W : C} (X : RawR (FullT De) .t W) : X ∈ Set.range (fullIncl De .t W) :=
  ⟨X, rfl⟩

/-! #### The logical constants are inner

Each reading is well-behaved at both levels and takes inner values; the checks are the
paper's remark that the logical constants "do not care about the first co-ordinate", plus
that division commutes with the set operations. -/

theorem mem_map_t {W V : C} (k : W ⟶ V) (X : RawR (FullT De) .t W) (q : Σ U : C, V ⟶ U) :
    q ∈ RawR.map (FullT De) .t k X ↔ (⟨q.1, k ≫ q.2⟩ : Σ U : C, W ⟶ U) ∈ X := Iff.rfl

theorem full_and_inner (W : C) :
    (A).andRead W ∈ Set.range ((A).incl (.arr (.rel .t) (.arr (.rel .t) .t)) W) := by
  refine (full_mem_range_arr De _).2 ⟨fun V h p => ?_, fun V U h i p => ?_⟩
  · refine (full_mem_range_arr De _).2 ⟨fun U j q => full_mem_range_t De _, fun U T j k q => ?_⟩
    ext ⟨S, l⟩
    show (⟨S, k ≫ l⟩ : Σ X : C, U ⟶ X) ∈ (RawR.map (FullT De) .t j p ∩ q : Set _) ↔
      (⟨S, l⟩ : Σ X : C, T ⟶ X) ∈
        (RawR.map (FullT De) .t (j ≫ k) p ∩ RawR.map (FullT De) .t k q : Set _)
    show ((⟨S, j ≫ (k ≫ l)⟩ : Σ X : C, V ⟶ X) ∈ p ∧ (⟨S, k ≫ l⟩ : Σ X : C, U ⟶ X) ∈ q) ↔
      ((⟨S, (j ≫ k) ≫ l⟩ : Σ X : C, V ⟶ X) ∈ p ∧ (⟨S, k ≫ l⟩ : Σ X : C, U ⟶ X) ∈ q)
    rw [Category.assoc]
  · funext T j q
    show (RawR.map (FullT De) .t (i ≫ j) p ∩ q : Set _)
      = RawR.map (FullT De) .t j (RawR.map (FullT De) .t i p) ∩ q
    rw [RawR.map_comp]

theorem full_or_inner (W : C) :
    (A).orRead W ∈ Set.range ((A).incl (.arr (.rel .t) (.arr (.rel .t) .t)) W) := by
  refine (full_mem_range_arr De _).2 ⟨fun V h p => ?_, fun V U h i p => ?_⟩
  · refine (full_mem_range_arr De _).2 ⟨fun U j q => full_mem_range_t De _, fun U T j k q => ?_⟩
    ext ⟨S, l⟩
    show (⟨S, k ≫ l⟩ : Σ X : C, U ⟶ X) ∈ (RawR.map (FullT De) .t j p ∪ q : Set _) ↔
      (⟨S, l⟩ : Σ X : C, T ⟶ X) ∈
        (RawR.map (FullT De) .t (j ≫ k) p ∪ RawR.map (FullT De) .t k q : Set _)
    show ((⟨S, j ≫ (k ≫ l)⟩ : Σ X : C, V ⟶ X) ∈ p ∨ (⟨S, k ≫ l⟩ : Σ X : C, U ⟶ X) ∈ q) ↔
      ((⟨S, (j ≫ k) ≫ l⟩ : Σ X : C, V ⟶ X) ∈ p ∨ (⟨S, k ≫ l⟩ : Σ X : C, U ⟶ X) ∈ q)
    rw [Category.assoc]
  · funext T j q
    show (RawR.map (FullT De) .t (i ≫ j) p ∪ q : Set _)
      = RawR.map (FullT De) .t j (RawR.map (FullT De) .t i p) ∪ q
    rw [RawR.map_comp]

theorem full_not_inner (W : C) :
    (A).notRead W ∈ Set.range ((A).incl (.arr (.rel .t) .t) W) := by
  refine (full_mem_range_arr De _).2 ⟨fun V h p => full_mem_range_t De _, fun V U h i p => ?_⟩
  ext ⟨S, l⟩
  exact Iff.rfl

theorem full_all_inner (σ : Ty) (W : C) :
    (A).allRead σ W ∈ Set.range ((A).incl (.arr (.rel (.arr σ .t)) .t) W) := by
  refine (full_mem_range_arr De _).2 ⟨fun V h α => full_mem_range_t De _, fun V U h i α => ?_⟩
  ext ⟨S, l⟩
  show (∀ a : (FullT De σ).obj S, (⟨S, 𝟙 S⟩ : Σ T, S ⟶ T) ∈ fullIncl De (.arr σ .t) V α S (i ≫ l) a) ↔
    (∀ a : (FullT De σ).obj S, (⟨S, 𝟙 S⟩ : Σ T, S ⟶ T) ∈ fullIncl De (.arr σ .t) U ((FullR De _).map i α) S l a)
  exact Iff.rfl

theorem full_ex_inner (σ : Ty) (W : C) :
    (A).exRead σ W ∈ Set.range ((A).incl (.arr (.rel (.arr σ .t)) .t) W) := by
  refine (full_mem_range_arr De _).2 ⟨fun V h α => full_mem_range_t De _, fun V U h i α => ?_⟩
  ext ⟨S, l⟩
  show (∃ a : (FullT De σ).obj S, (⟨S, 𝟙 S⟩ : Σ T, S ⟶ T) ∈ fullIncl De (.arr σ .t) V α S (i ≫ l) a) ↔
    (∃ a : (FullT De σ).obj S, (⟨S, 𝟙 S⟩ : Σ T, S ⟶ T) ∈ fullIncl De (.arr σ .t) U ((FullR De _).map i α) S l a)
  exact Iff.rfl

theorem full_eq_inner (σ : Ty) (W : C) :
    (A).eqRead σ W ∈ Set.range ((A).incl (.arr σ (.arr σ .t)) W) := by
  refine (full_mem_range_arr De _).2 ⟨fun V h a => ?_, fun V U h i a => ?_⟩
  · refine (full_mem_range_arr De _).2 ⟨fun U j b => full_mem_range_t De _, fun U T j k b => ?_⟩
    ext ⟨S, l⟩
    show (FullT De σ).map (k ≫ l) ((FullT De σ).map j a) = (FullT De σ).map (k ≫ l) b ↔
      (FullT De σ).map l ((FullT De σ).map (j ≫ k) a) = (FullT De σ).map l ((FullT De σ).map k b)
    simp only [Functor.map_comp, types_comp_apply]
  · funext T j b
    ext ⟨S, l⟩
    show (FullT De σ).map l ((FullT De σ).map (i ≫ j) a) = (FullT De σ).map l b ↔
      (FullT De σ).map l ((FullT De σ).map j ((FullT De σ).map i a)) = (FullT De σ).map l b
    simp only [Functor.map_comp, types_comp_apply]

/-! #### The induction -/

/-- The largest size of a type subscript in a term: the measure of the second induction,
since an operation at `σ → ρ` reads as its unfolding, which mentions the operation at
`ρ`. -/
noncomputable def _root_.Classicism.Meta.Term.rsize : ∀ {Γ : Ctx} {σ : Ty}, Term Sig Γ σ → Nat
  | _, _, .var _ => 0
  | _, _, .const _ => 0
  | _, _, .app f a => max f.rsize a.rsize
  | _, _, .lam b => b.rsize
  | _, _, .and => 0
  | _, _, .or => 0
  | _, _, .not => 0
  | _, _, .all _ => 0
  | _, _, .ex _ => 0
  | _, _, .eq _ => 0
  | _, _, .constR ρ => sizeOf ρ
  | _, _, .negR ρ => sizeOf ρ
  | _, _, .andR ρ => sizeOf ρ
  | _, _, .orR ρ => sizeOf ρ
  | _, _, .coextR ρ => sizeOf ρ
  | _, _, .boxR ρ => sizeOf ρ
  | _, _, .boxImpR ρ => sizeOf ρ

/-- What the combined induction proves of a term: its value is inner, and transport. -/
def FullP {Γ : Ctx} {σ : Ty} (t : Term Sig Γ σ) : Prop :=
  ∀ {W : C} (h : W₀ ⟶ W) (g : IEnv ((A).Dom W) Γ),
    (A).sem h t g ∈ Set.range ((A).Incl σ W) ∧
    ∀ {V : C} (i : W ⟶ V), (A).sem (h ≫ i) t ((A).push i g) = RawT.map (A).inner σ i ((A).sem h t g)

theorem Ty.sizeOf_pos : ∀ σ : Ty, 0 < sizeOf σ
  | .e => by simp
  | .rel ρ => by simp only [Ty.rel.sizeOf_spec]; omega

theorem fullP_of_unfold {Γ : Ctx} {σ : Ty} (t u : Term Sig Γ σ)
    (e : ∀ {W : C} (h : W₀ ⟶ W) (g : IEnv ((A).Dom W) Γ), (A).sem h t g = (A).sem h u g)
    (hu : FullP De (I := I) (rooted := rooted) (nonempty_e := nonempty_e) u)
    (hb : ∀ {W : C} (h : W₀ ⟶ W) (g : IEnv ((A).Dom W) Γ) {V : C} (i : W ⟶ V),
      (A).sem (h ≫ i) t ((A).push i g) = RawT.map (A).inner σ i ((A).sem h t g)) :
    FullP De (I := I) (rooted := rooted) (nonempty_e := nonempty_e) t :=
  fun h g => ⟨e h g ▸ (hu h g).1, hb h g⟩

theorem full_step (n : Nat)
    (ih : ∀ m < n, ∀ {Γ : Ctx} {σ : Ty} (t : Term Sig Γ σ), t.rsize < m →
      FullP De (I := I) (rooted := rooted) (nonempty_e := nonempty_e) t) :
    ∀ {Γ : Ctx} {σ : Ty} (t : Term Sig Γ σ), t.rsize < n →
      FullP De (I := I) (rooted := rooted) (nonempty_e := nonempty_e) t
  | _, _, .var v, _ => fun h g => ⟨⟨g.get v, rfl⟩, fun i => by
      simp only [sem, push, IEnv.get_map]; rw [(A).Incl_map]⟩
  | _, _, .const c, _ => fun h g => ⟨⟨_, rfl⟩, fun i => by
      show (A).Incl _ _ (((A).inner _).map (h ≫ i) ((A).I c))
        = RawT.map (A).inner _ i ((A).Incl _ _ (((A).inner _).map h ((A).I c)))
      rw [Functor.map_comp, ← (A).Incl_map]; rfl⟩
  | _, _, .app f a, hn => fun h g => by
    have hf := full_step n ih f (lt_of_le_of_lt (le_max_left _ _) hn) h g
    have ha := full_step n ih a (lt_of_le_of_lt (le_max_right _ _) hn) h g
    obtain ⟨α, hα⟩ := Set.mem_range.mp hf.1
    obtain ⟨b, hb⟩ := Set.mem_range.mp ha.1
    refine ⟨?_, fun i => ?_⟩
    · show (A).apply ((A).sem h f g) ((A).sem h a g) ∈ _
      rw [← hα, ← hb, (A).apply_Incl]
      exact (A).app_inner _ _ α (𝟙 _) b
    · show (A).apply ((A).sem (h ≫ i) f ((A).push i g)) ((A).sem (h ≫ i) a ((A).push i g))
        = RawR.map (A).inner _ i ((A).apply ((A).sem h f g) ((A).sem h a g))
      rw [hf.2 i, ha.2 i, ← hα, ← hb]
      exact (A).apply_map i α b
  | _, _, .lam (σ := σ) (ρ := ρ) b, hn => fun h g => by
    have hb := fun {V} (i : _ ⟶ V) (x : (A).Dom V σ) =>
      full_step n ih b hn (h ≫ i) (.cons x ((A).push i g))
    refine ⟨?_, fun i => ?_⟩
    · show (fun V i x => (A).sem (h ≫ i) b (.cons x ((A).push i g))) ∈ Set.range (fullIncl De (.arr σ ρ) _)
      refine (full_mem_range_arr De _).2 ⟨fun V i x => (hb i x).1, fun V U i j x => ?_⟩
      refine ((hb i x).2 j).symm.trans ?_
      exact (congrArg (fun k => (A).sem k b (.cons ((FullT De σ).map j x) ((A).push j ((A).push i g))))
          (Category.assoc h i j)).trans
        (congrArg (fun E => (A).sem (h ≫ (i ≫ j)) b (.cons ((FullT De σ).map j x) E)) ((A).push_push i j g))
    · funext U j x
      exact (congrArg (fun k => (A).sem k b (.cons x ((A).push j ((A).push i g)))) (Category.assoc h i j)).trans
        (congrArg (fun E => (A).sem (h ≫ (i ≫ j)) b (.cons x E)) ((A).push_push i j g))
  | _, _, .and, _ => fun h g => ⟨full_and_inner De _, fun _ => rfl⟩
  | _, _, .or, _ => fun h g => ⟨full_or_inner De _, fun _ => rfl⟩
  | _, _, .not, _ => fun h g => ⟨full_not_inner De _, fun _ => rfl⟩
  | _, _, .all σ, _ => fun h g => ⟨full_all_inner De σ _, fun _ => rfl⟩
  | _, _, .ex σ, _ => fun h g => ⟨full_ex_inner De σ _, fun _ => rfl⟩
  | _, _, .eq σ, _ => fun h g => ⟨full_eq_inner De σ _, fun _ => rfl⟩
  | _, _, .constR ρ, hn => by
    cases ρ with
    | t => exact (fullP_of_unfold De (.constR .t) ((Term.unfoldConst .t).get rfl) (fun _ _ => rfl)
        (ih 1 (by have hn' : sizeOf RTy.t < n := hn; simp only [RTy.t.sizeOf_spec] at hn'; omega) _
          (by simp [Term.unfoldConst, Term.rsize])) (by intros; rfl))
    | arr σ ρ => exact (fullP_of_unfold De (.constR (σ ⇒ ρ)) ((Term.unfoldConst (σ ⇒ ρ)).get rfl) (fun _ _ => rfl)
        (ih (sizeOf ρ + 1) (by
          have hn' : sizeOf (σ ⇒ ρ) < n := hn
          simp only [RTy.arr.sizeOf_spec] at hn'; have := Ty.sizeOf_pos σ; omega) _
          (by simp [Term.unfoldConst, Term.rsize])) (by intros; rfl))
  | _, _, .negR ρ, hn => by
    cases ρ with
    | t => exact (fullP_of_unfold De (.negR .t) ((Term.unfoldNeg .t).get rfl) (fun _ _ => rfl)
        (ih 1 (by have hn' : sizeOf RTy.t < n := hn; simp only [RTy.t.sizeOf_spec] at hn'; omega) _
          (by simp [Term.unfoldNeg, Term.rsize])) (by intros; rfl))
    | arr σ ρ => exact (fullP_of_unfold De (.negR (σ ⇒ ρ)) ((Term.unfoldNeg (σ ⇒ ρ)).get rfl) (fun _ _ => rfl)
        (ih (sizeOf ρ + 1) (by
          have hn' : sizeOf (σ ⇒ ρ) < n := hn
          simp only [RTy.arr.sizeOf_spec] at hn'; have := Ty.sizeOf_pos σ; omega) _
          (by simp [Term.unfoldNeg, Term.rsize])) (by intros; rfl))
  | _, _, .andR ρ, hn => by
    cases ρ with
    | t => exact (fullP_of_unfold De (.andR .t) ((Term.unfoldAnd .t).get rfl) (fun _ _ => rfl)
        (ih 1 (by have hn' : sizeOf RTy.t < n := hn; simp only [RTy.t.sizeOf_spec] at hn'; omega) _
          (by simp [Term.unfoldAnd, Term.rsize])) (by intros; rfl))
    | arr σ ρ => exact (fullP_of_unfold De (.andR (σ ⇒ ρ)) ((Term.unfoldAnd (σ ⇒ ρ)).get rfl) (fun _ _ => rfl)
        (ih (sizeOf ρ + 1) (by
          have hn' : sizeOf (σ ⇒ ρ) < n := hn
          simp only [RTy.arr.sizeOf_spec] at hn'; have := Ty.sizeOf_pos σ; omega) _
          (by simp [Term.unfoldAnd, Term.rsize])) (by intros; rfl))
  | _, _, .orR ρ, hn => by
    cases ρ with
    | t => exact (fullP_of_unfold De (.orR .t) ((Term.unfoldOr .t).get rfl) (fun _ _ => rfl)
        (ih 1 (by have hn' : sizeOf RTy.t < n := hn; simp only [RTy.t.sizeOf_spec] at hn'; omega) _
          (by simp [Term.unfoldOr, Term.rsize])) (by intros; rfl))
    | arr σ ρ => exact (fullP_of_unfold De (.orR (σ ⇒ ρ)) ((Term.unfoldOr (σ ⇒ ρ)).get rfl) (fun _ _ => rfl)
        (ih (sizeOf ρ + 1) (by
          have hn' : sizeOf (σ ⇒ ρ) < n := hn
          simp only [RTy.arr.sizeOf_spec] at hn'; have := Ty.sizeOf_pos σ; omega) _
          (by simp [Term.unfoldOr, Term.rsize])) (by intros; rfl))
  | _, _, .coextR ρ, hn => by
    cases ρ with
    | t => exact (fullP_of_unfold De (.coextR .t) ((Term.unfoldCoext .t).get rfl) (fun _ _ => rfl)
        (ih 1 (by have hn' : sizeOf RTy.t < n := hn; simp only [RTy.t.sizeOf_spec] at hn'; omega) _
          (by simp [Term.unfoldCoext, Term.rsize])) (by intros; rfl))
    | arr σ ρ => exact (fullP_of_unfold De (.coextR (σ ⇒ ρ)) ((Term.unfoldCoext (σ ⇒ ρ)).get rfl) (fun _ _ => rfl)
        (ih (sizeOf ρ + 1) (by
          have hn' : sizeOf (σ ⇒ ρ) < n := hn
          simp only [RTy.arr.sizeOf_spec] at hn'; have := Ty.sizeOf_pos σ; omega) _
          (by simp [Term.unfoldCoext, Term.rsize])) (by intros; rfl))
  | _, _, .boxR ρ, hn => by
    cases ρ with
    | t => exact (fullP_of_unfold De (.boxR .t) ((Term.unfoldBox .t).get rfl) (fun _ _ => rfl)
        (ih 1 (by have hn' : sizeOf RTy.t < n := hn; simp only [RTy.t.sizeOf_spec] at hn'; omega) _
          (by simp [Term.unfoldBox, Term.rsize])) (by intros; rfl))
    | arr σ ρ => exact (fullP_of_unfold De (.boxR (σ ⇒ ρ)) ((Term.unfoldBox (σ ⇒ ρ)).get rfl) (fun _ _ => rfl)
        (ih (sizeOf ρ + 1) (by
          have hn' : sizeOf (σ ⇒ ρ) < n := hn
          simp only [RTy.arr.sizeOf_spec] at hn'; have := Ty.sizeOf_pos σ; omega) _
          (by simp [Term.unfoldBox, Term.rsize])) (by intros; rfl))
  | _, _, .boxImpR ρ, hn => by
    cases ρ with
    | t => exact (fullP_of_unfold De (.boxImpR .t) ((Term.unfoldBoxImp .t).get rfl) (fun _ _ => rfl)
        (ih 1 (by have hn' : sizeOf RTy.t < n := hn; simp only [RTy.t.sizeOf_spec] at hn'; omega) _
          (by simp [Term.unfoldBoxImp, Term.rsize])) (by intros; rfl))
    | arr σ ρ => exact (fullP_of_unfold De (.boxImpR (σ ⇒ ρ)) ((Term.unfoldBoxImp (σ ⇒ ρ)).get rfl) (fun _ _ => rfl)
        (ih (sizeOf ρ + 1) (by
          have hn' : sizeOf (σ ⇒ ρ) < n := hn
          simp only [RTy.arr.sizeOf_spec] at hn'; have := Ty.sizeOf_pos σ; omega) _
          (by simp [Term.unfoldBoxImp, Term.rsize])) (by intros; rfl))

theorem fullP_all (n : Nat) : ∀ {Γ : Ctx} {σ : Ty} (t : Term Sig Γ σ), t.rsize < n →
    FullP De (I := I) (rooted := rooted) (nonempty_e := nonempty_e) t :=
  full_step De n fun m _ => fullP_all m
termination_by n

/-- **A full premodel is an action model.** -/
theorem full_isModel : (A).IsModel :=
  fun h t g => (fullP_all De (t.rsize + 1) t (Nat.lt_succ_self _) h g).1

/-! ### `BF_σ` forces surjectivity

The paper's Proposition, (iii): in a full model, if `BF_σ` holds at the root then every
`h^σ` out of the root is surjective. The witness is the predicate "is the image, under
the arrow, of something at the root", an element of the full domain at `σ → t`. -/

/-- `α⟨i, b⟩ = {k | k^σ b = k^σ (i^σ a) for some a ∈ W₀^σ}`. -/
noncomputable def rootImage (σ : Ty) : (FullR De (.arr σ .t)).obj W₀ :=
  ⟨fun U i b => {q : Σ T : C, U ⟶ T | ∃ a : (FullT De σ).obj W₀,
      (FullT De σ).map q.2 b = (FullT De σ).map q.2 ((FullT De σ).map i a)},
   fun U T i j b => by
     ext ⟨S, l⟩
     show (∃ a : (FullT De σ).obj W₀, (FullT De σ).map (j ≫ l) b
         = (FullT De σ).map (j ≫ l) ((FullT De σ).map i a)) ↔
       (∃ a : (FullT De σ).obj W₀, (FullT De σ).map l ((FullT De σ).map j b)
         = (FullT De σ).map l ((FullT De σ).map (i ≫ j) a))
     simp only [Functor.map_comp, types_comp_apply]⟩

theorem full_bf_surjective (σ : Ty) (H : (A).HoldsSentence (Sentence.bf σ)) :
    ∀ {V : C} (k : W₀ ⟶ V), Function.Surjective ((FullT De σ).map k) := by
  intro V k c
  have M : (A).IsModel := full_isModel De
  rw [HoldsSentence, Sentence.bf, (A).holds_forall M] at H
  have H := H (rootImage De σ)
  rw [(A).holds_imp M] at H
  have H := H (by
    rw [(A).holds_forall M]
    intro b
    rw [(A).holds_box M]
    intro U j
    rw [(A).holds_app _ _ _ _ (a' := (FullT De σ).map j b) rfl]
    show (⟨U, 𝟙 U⟩ : Σ T, U ⟶ T) ∈ (rootImage De σ).1 U (j ≫ 𝟙 U) ((FullT De σ).map j b)
    exact ⟨b, by rw [Category.comp_id]⟩)
  rw [(A).holds_box M] at H
  have H := H k
  rw [(A).holds_forall M] at H
  have H := H c
  rw [(A).holds_app _ _ _ _ (a' := c) rfl] at H
  obtain ⟨a, ha⟩ : ∃ a : (FullT De σ).obj W₀,
      (FullT De σ).map (𝟙 V) c = (FullT De σ).map (𝟙 V) ((FullT De σ).map (k ≫ 𝟙 V) a) := H
  simp only [Functor.map_id, types_id_apply, Category.comp_id] at ha
  exact ⟨a, ha.symm⟩

end Premodel

end Classicism.Meta
