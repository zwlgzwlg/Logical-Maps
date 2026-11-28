import Classicism.Coalesced.StoneLeaves

/-!
# A coalesced model with freely specified Stone leaf profiles

Each component is a pointed native action model. Its copies are indexed by labels.
The arrows into it are pairs of a label and an arrow from its base. At a distinguished
component the label set carries a topology; locally constant profiles are admitted
there, and no continuity condition is imposed elsewhere. The copies share the
component's original interpretation of all signature constants.
-/

namespace Classicism.Meta.Coalesced.StoneFan

open CategoryTheory CategoryTheory.Sigma Classicism.Meta.Intensional

variable {Sig : Signature} {ι : Type} {C : ι → Type} [∀ k, SmallCategory (C k)]
  (A : ∀ k, Premodel Sig (C k)) (L : ι → Type)

/-- Tagged distinguished arrows retain distinct coordinates for distinct labels. -/
def arrows : RootArrows C where
  R := Sigma.desc fun k =>
    { obj := fun V => L k × ((A k).W₀ ⟶ V)
      map := fun j => TypeCat.ofHom fun h => (h.1, h.2 ≫ j)
      map_id := fun _ => by ext ⟨x, h⟩ <;> first | rfl | exact Category.comp_id h
      map_comp := fun j j' => by ext ⟨x, h⟩ <;> first | rfl | exact (Category.assoc h j j').symm }
  End := PUnit
  one := PUnit.unit
  mul _ _ := PUnit.unit
  act _ h := h
  one_mul _ := rfl
  mul_one _ := rfl
  mul_assoc _ _ _ := rfl
  act_one _ := rfl
  act_mul _ _ _ := rfl
  act_natural _ _ _ := rfl

abbrev baseArrow (k : ι) (x : L k) : (arrows A L).R.obj ⟨k, (A k).W₀⟩ :=
  (x, 𝟙 (A k).W₀)

/-- Products only over distinct component models, independently of the size of the
label spaces. With one old component and a singleton individual leaf, this is
canonically isomorphic to the old individual domain. -/
def atom (σ : Ty) : AtomAction (arrows A L) A σ where
  D := ∀ k, (A k).Dom (A k).W₀ σ
  tr {k} {_} h a := ((A k).inner σ).map h.2 (a k)
  trE _ a := a
  tr_map {k} {_} {_} j h a := ((A k).inner σ).map_comp_apply h.2 j (a k)
  tr_act _ _ _ := rfl
  trE_one _ := rfl
  trE_mul _ _ _ := rfl

variable (leaf : ι) [TopologicalSpace (L leaf)]

abbrev sel : Selector (arrows A L) A :=
  StoneLeaves.selector (baseArrow A L leaf) (fun _ _ => rfl)

noncomputable abbrev action : RootAction (arrows A L) A :=
  selAction (atom A L .e) (fun i => atom A L (.var i)) (sel A L leaf)

/-- The root row and the profile at every labelled component base vary independently.
This is the gluing construction for relations at every arity. -/
def tuples {ρ : RTy} {B : Type} (row : Set B)
    (y : ∀ k, L k → (A k).Dom (A k).W₀ (.rel ρ)) :
    Set (RootTuple (arrows A L) A ρ B)
  | .inl (_, b) => b ∈ row
  | .inr ⟨k, U, a, (x, j)⟩ => (⟨U, a, j⟩ : Tuple (A k).inner ρ (A k).W₀) ∈
      (A k).incl ρ _ (y k x)

theorem transport_tuples {ρ : RTy} {B : Type} (row : Set B)
    (y : ∀ k, L k → (A k).Dom (A k).W₀ (.rel ρ))
    {k : ι} {V : C k} (x : L k) (j : (A k).W₀ ⟶ V) :
    rootTransport (tuples A L row y) (k := k) (V := V) (x, j) =
      (A k).incl ρ V (((A k).inner (.rel ρ)).map j (y k x)) := by
  rw [(A k).incl_map]; rfl

noncomputable abbrev args (ρ : RTy) :=
  selArgsT (atom A L .e) (fun i => atom A L (.var i)) (sel A L leaf) ρ

/-- A completely arbitrary current extension and arbitrary component coordinates are
admitted whenever the distinguished leaf profile is locally constant. -/
noncomputable def glue {ρ : RTy} (row : Set (args A L leaf ρ))
    (y : ∀ k, L k → (A k).Dom (A k).W₀ (.rel ρ))
    (hy : IsLocallyConstant (y leaf)) : (action A L leaf).D (.rel ρ) := by
  refine ⟨tuples A L row y, fun {k V} h => ⟨_, (transport_tuples A L row y h.1 h.2).symm⟩, ?_⟩
  change IsLocallyConstant (fun x => rootTransport (tuples A L row y)
    (k := leaf) (V := (A leaf).W₀) (x, 𝟙 _))
  have e (x : L leaf) := (transport_tuples A L row y x (𝟙 _)).trans
    (congrArg ((A leaf).incl ρ _) (((A leaf).inner (.rel ρ)).map_id_apply _ (y leaf x)))
  exact (funext e).symm ▸ hy.comp ((A leaf).incl ρ _)

theorem tr_glue {ρ : RTy} (row : Set (args A L leaf ρ))
    (y : ∀ k, L k → (A k).Dom (A k).W₀ (.rel ρ)) (hy : IsLocallyConstant (y leaf))
    (k : ι) (x : L k) :
    (action A L leaf).tr _ (baseArrow A L k x) (glue A L leaf row y hy) = y k x := by
  apply (A k).incl_injective ρ _
  refine (incl_relLevel_tr (sel A L leaf) ρ _ (baseArrow A L k x) _).trans ?_
  exact (transport_tuples A L row y x (𝟙 _)).trans
    (congrArg ((A k).incl ρ _) (((A k).inner (.rel ρ)).map_id_apply _ (y k x)))

/-- Lift one value from each component, with homogeneous interpretations across its
labels. -/
noncomputable def lift : ∀ σ, (∀ k, (A k).Dom (A k).W₀ σ) → (action A L leaf).D σ
  | .e, y => y
  | .var _, y => y
  | .rel _, y => glue A L leaf ∅ (fun k _ => y k) (IsLocallyConstant.const _)

theorem tr_lift : ∀ σ (y : ∀ k, (A k).Dom (A k).W₀ σ) (k : ι) (x : L k),
    (action A L leaf).tr σ (baseArrow A L k x) (lift A L leaf σ y) = y k
  | .e, y, k, _ => ((A k).inner .e).map_id_apply _ (y k)
  | .var i, y, k, _ => ((A k).inner (.var i)).map_id_apply _ (y k)
  | .rel _, y, k, x => tr_glue A L leaf ∅ (fun k _ => y k) (IsLocallyConstant.const _) k x

noncomputable abbrev rootI (c : Sig.Const) : (action A L leaf).D (Sig.typeOf c) :=
  lift A L leaf _ (fun k => (A k).I c)

theorem component_eq {k : ι} {V : C k} (x : L k) (j : (A k).W₀ ⟶ V) :
    (action A L leaf).component (rootI A L leaf) (k := k) (V := V) (x, j) =
      (A k).truncate j := by
  apply congrArg ((A k).rebase V)
  funext c
  have h := (action A L leaf).tr_map _ j (baseArrow A L k x) (rootI A L leaf c)
  rw [tr_lift] at h
  change (action A L leaf).tr _ (k := k) (V := V) (x, 𝟙 _ ≫ j) _ = _ at h
  rwa [Category.id_comp] at h

noncomputable abbrev nonemptyRoot : Nonempty (atom A L .e).D :=
  ⟨fun k => Classical.choice ((A k).nonempty_e _)⟩

noncomputable abbrev model : Premodel Sig (CoalescedSum (arrows A L)) :=
  (action A L leaf).coalescedSum
    (selIncl (atom A L .e) (fun i => atom A L (.var i)) (sel A L leaf))
    (nonemptyRoot A L) (rootI A L leaf)

theorem isModel (hA : ∀ k, (A k).IsModel) : (model A L leaf).IsModel := by
  apply StoneLeaves.isModel (baseArrow A L leaf) (fun _ _ => rfl) _ _ _ _
    (fun _ => IsLocallyConstant.of_constant _ (fun _ _ => rfl))
    (fun _ _ => IsLocallyConstant.of_constant _ (fun _ _ => rfl)) ((A leaf).I)
    (fun c x => tr_lift A L leaf _ _ leaf x)
  intro k V h
  exact (component_eq A L leaf h.1 h.2).symm ▸ (A k).isModel_truncate h.2 (hA k)

/-- Every possibility from any labelled component remains possible at the new root,
including each instance witnessed by an old Maximalist component. -/
theorem preserves_dia (hA : ∀ k, (A k).IsModel) {k : ι} (x : L k)
    (p : Sentence Sig) (hp : (A k).HoldsSentence (Term.dia p)) :
    (model A L leaf).HoldsSentence (Term.dia p) := by
  obtain ⟨V, j, hj⟩ := ((A k).dia_iff_truncate (hA k) p).1 hp
  apply (action A L leaf).holds_dia_of_component _ _ _ (isModel A L leaf hA)
    (k := k) (V := V) (x, j)
  rwa [component_eq]

#print axioms isModel
#print axioms preserves_dia

end Classicism.Meta.Coalesced.StoneFan
