import Classicism.Semantics.IntensionalFacts

/-!
# Full intensional action models

The paper's *full* action models, in the intensional form: the inner domain at every
relational type is the whole outer domain, every set of tuples an element. A base object,
an action for `e` with nonempty domains, and an interpretation of the constants then
determine a full premodel, and it is a model at once: the model condition asks that the
value of every term be inner, and here everything is. Where the applicative form
(`ActionFull.lean`) needed an induction on terms to show that every value is well-behaved
and takes inner values, the intensional form builds that into the representation.

The domains are defined by recursion on the type, through the recursor of the mutual
inductive: the arguments of a relational type form an action (the product of the inner
actions), and the domain at that type is the action of intensions over it. The general
`Args` of `Intensional.lean` is the same product written with the inner actions named,
so at a variable type the two are related by an explicit bijection, `fullArgs`, and the
inclusion of the full domain into the intensions is the preimage under it.

Then the paper's Proposition, (iii): in a full model, `BF_σ` at the base forces every
`h^σ` out of it to be surjective.
-/

namespace Classicism.Meta.Intensional

open CategoryTheory

variable {C : Type} [SmallCategory C]

/-! ### Actions of intensions, of products, and of the point -/

/-- The action of intensions over an action `F` of arguments: at `W`, the sets of tuples
`⟨V, a, h⟩` with `h : W → V` and `a ∈ F V`; an arrow acts by precomposition. -/
abbrev intensionAction (F : C ⥤ Type) : C ⥤ Type where
  obj W := Set (Σ V : C, F.obj V × (W ⟶ V))
  map {W V} h := TypeCat.ofHom fun (A : Set (Σ U : C, F.obj U × (W ⟶ U))) =>
    ({p : Σ U : C, F.obj U × (V ⟶ U) | (⟨p.1, p.2.1, h ≫ p.2.2⟩ : Σ U : C, F.obj U × (W ⟶ U)) ∈ A} :
      Set (Σ U : C, F.obj U × (V ⟶ U)))
  map_id W := by
    ext A ⟨V, a, i⟩; simp
  map_comp h i := by
    ext A ⟨U, a, j⟩; simp [Category.assoc]

/-- The action with one element at every object: the arguments of `t`. -/
abbrev pointAction : C ⥤ Type where
  obj _ := PUnit
  map _ := TypeCat.ofHom id

/-- The product of two actions, pointwise. -/
abbrev prodAction (F G : C ⥤ Type) : C ⥤ Type where
  obj V := F.obj V × G.obj V
  map {V V'} j := TypeCat.ofHom fun a => (F.map j a.1, G.map j a.2)
  map_id V := by
    ext ⟨x, y⟩ <;> simp
  map_comp j k := by
    ext ⟨x, y⟩ <;> simp

/-! ### The full inner domains -/

variable (De : C ⥤ Type)

/-- The full inner action at a type: `De` at `e`; at a relational type, the intensions over
its arguments. Through the recursor of the mutual inductive, so that it reduces by iota
at a constructor. -/
noncomputable abbrev FullT (σ : Ty) : C ⥤ Type :=
  @Ty.rec (fun _ => C ⥤ Type) (fun _ => C ⥤ Type) De (fun _ ih => intensionAction ih)
    pointAction (fun _ _ ihσ ihρ => prodAction ihσ ihρ) σ

/-- The action of the arguments of a relational type: the point at `t`, and at `σ → ρ`
the product of the full action at `σ` with the arguments of `ρ`. -/
noncomputable abbrev FullArgs (ρ : RTy) : C ⥤ Type :=
  @RTy.rec (fun _ => C ⥤ Type) (fun _ => C ⥤ Type) De (fun _ ih => intensionAction ih)
    pointAction (fun _ _ ihσ ihρ => prodAction ihσ ihρ) ρ

/-- The full inner action at a relational type. -/
noncomputable abbrev FullR (ρ : RTy) : C ⥤ Type := intensionAction (FullArgs De ρ)

example : FullT De .e = De := rfl
example (ρ : RTy) : FullT De (.rel ρ) = FullR De ρ := rfl
example (V : C) : (FullArgs De .t).obj V = PUnit := rfl
example (σ : Ty) (ρ : RTy) (V : C) :
    (FullArgs De (.arr σ ρ)).obj V = ((FullT De σ).obj V × (FullArgs De ρ).obj V) := rfl

/-- The arguments of `Intensional.lean`, over the full actions, to the full arguments: the
identity, componentwise. -/
def fullArgs : ∀ (ρ : RTy) (V : C), Args (FullT De) ρ V → (FullArgs De ρ).obj V
  | .t, _, _ => PUnit.unit
  | .arr _ ρ, V, a => (a.1, fullArgs ρ V a.2)

/-- Its inverse. -/
def fullArgs' : ∀ (ρ : RTy) (V : C), (FullArgs De ρ).obj V → Args (FullT De) ρ V
  | .t, _, _ => PUnit.unit
  | .arr _ ρ, V, a => (a.1, fullArgs' ρ V a.2)

theorem fullArgs_fullArgs' : ∀ (ρ : RTy) (V : C) (a : (FullArgs De ρ).obj V),
    fullArgs De ρ V (fullArgs' De ρ V a) = a
  | .t, _, _ => rfl
  | .arr _ ρ, V, a => by
    show (a.1, fullArgs De ρ V (fullArgs' De ρ V a.2)) = a
    exact Prod.ext rfl (fullArgs_fullArgs' ρ V a.2)

theorem fullArgs'_fullArgs : ∀ (ρ : RTy) (V : C) (a : Args (FullT De) ρ V),
    fullArgs' De ρ V (fullArgs De ρ V a) = a
  | .t, _, _ => rfl
  | .arr _ ρ, V, a => by
    show (a.1, fullArgs' De ρ V (fullArgs De ρ V a.2)) = a
    exact Prod.ext rfl (fullArgs'_fullArgs ρ V a.2)

/-- The inclusion of the full inner domains into the intensions: the preimage under
`fullArgs`, which is a bijection. -/
def fullIncl (ρ : RTy) (W : C) (A : Set (Σ V : C, (FullArgs De ρ).obj V × (W ⟶ V))) :
    Intension (FullT De) ρ W :=
  {p | (⟨p.1, fullArgs De ρ p.1 p.2.1, p.2.2⟩ : Σ V : C, (FullArgs De ρ).obj V × (W ⟶ V)) ∈ A}

@[simp] theorem mem_fullIncl (ρ : RTy) (W : C) (A : Set (Σ V : C, (FullArgs De ρ).obj V × (W ⟶ V)))
    (p : Tuple (FullT De) ρ W) :
    p ∈ fullIncl De ρ W A ↔
      (⟨p.1, fullArgs De ρ p.1 p.2.1, p.2.2⟩ : Σ V : C, (FullArgs De ρ).obj V × (W ⟶ V)) ∈ A :=
  Iff.rfl

theorem fullIncl_map (ρ : RTy) {W V : C} (h : W ⟶ V) (A : Set (Σ V : C, (FullArgs De ρ).obj V × (W ⟶ V))) :
    fullIncl De ρ V ((FullR De ρ).map h A) = Intension.map (FullT De) h (fullIncl De ρ W A) := by
  ext ⟨U, a, i⟩
  exact Iff.rfl

theorem fullIncl_injective (ρ : RTy) (W : C) : Function.Injective (fullIncl De ρ W) := by
  intro A B e
  apply Set.ext
  rintro ⟨V, a, i⟩
  have := congrArg (fun S : Intension (FullT De) ρ W => (⟨V, fullArgs' De ρ V a, i⟩ : Tuple (FullT De) ρ W) ∈ S) e
  simpa [fullArgs_fullArgs'] using this

/-- Every intension is the inclusion of an element of the full domain. -/
theorem fullIncl_surjective (ρ : RTy) (W : C) : Function.Surjective (fullIncl De ρ W) := by
  intro F
  refine ⟨{p | (⟨p.1, fullArgs' De ρ p.1 p.2.1, p.2.2⟩ : Tuple (FullT De) ρ W) ∈ F}, ?_⟩
  ext ⟨V, a, i⟩
  simp [fullArgs'_fullArgs]

/-- At `t` the inclusion is the identity. -/
theorem fullIncl_t (W : C) (A : Set (Σ V : C, (FullArgs De .t).obj V × (W ⟶ V))) :
    fullIncl De .t W A = A := by
  ext ⟨V, ⟨⟩, i⟩
  exact Iff.rfl

/-- The full intensional action premodel on a category with a chosen base, given the action
for `e` and the constants. -/
noncomputable def Premodel.full {Sig : Signature} (W₀ : C)
    (nonempty_e : ∀ W : C, Nonempty (De.obj W))
    (I : ∀ c : Sig.Const, (FullT De (Sig.typeOf c)).obj W₀) : Premodel Sig C where
  W₀ := W₀
  inner := FullT De
  nonempty_e := nonempty_e
  incl := fullIncl De
  incl_map := fullIncl_map De
  incl_injective := fullIncl_injective De
  I := I

/-! ### The full premodel is a model -/

namespace Premodel

variable {Sig : Signature} {W₀ : C}
  {nonempty_e : ∀ W : C, Nonempty (De.obj W)}
  {I : ∀ c : Sig.Const, (FullT De (Sig.typeOf c)).obj W₀}

local notation "A" => Premodel.full De W₀ nonempty_e I

/-- **A full premodel is an intensional action model**: every outer element is inner. -/
theorem full_isModel : (A).IsModel := fun {_ σ W} h t g => by
  cases σ with
  | e => exact ⟨_, rfl⟩
  | rel ρ => exact fullIncl_surjective De ρ W _

/-! ### `BF_σ` forces surjectivity

The paper's Proposition, (iii): in a full model, if `BF_σ` holds at the base then every
`h^σ` out of the base is surjective. The witness is the predicate "is the image, under
the arrow, of something at the base", an intension of type `σ → t` at the base, which is
an element of the full domain. -/

/-- `⟨b, k⟩ ∈ rootImage` iff `b = k^σ a` for some `a` at the base. -/
noncomputable def rootImage (σ : Ty) : Set (Σ V : C, (FullArgs De (.arr σ .t)).obj V × (W₀ ⟶ V)) :=
  {p | ∃ a : (FullT De σ).obj W₀, p.2.1.1 = (FullT De σ).map p.2.2 a}

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
    show ∃ a : (FullT De σ).obj W₀, (FullT De σ).map j b = (FullT De σ).map (j ≫ 𝟙 U) a
    exact ⟨b, by rw [Category.comp_id]⟩)
  rw [(A).holds_box M] at H
  have H := H k
  rw [(A).holds_forall M] at H
  have H := H c
  rw [(A).holds_app _ _ _ _ (a' := c) rfl] at H
  obtain ⟨a, ha⟩ : ∃ a : (FullT De σ).obj W₀, c = (FullT De σ).map (k ≫ 𝟙 V) a := H
  rw [Category.comp_id] at ha
  exact ⟨a, ha.symm⟩

end Premodel

end Classicism.Meta.Intensional
