import Classicism.Coalesced.StoneFan
import Classicism.Certified.Signatures

/-! Exact native coordinates of each relational domain and inheritance of the map's
Maximalism schemata in their possibility formulations. -/

namespace Classicism.Meta.Coalesced.StoneFan

open CategoryTheory CategoryTheory.Sigma Classicism.Meta.Intensional

variable {Sig : Signature} {ι : Type} {C : ι → Type} [∀ k, SmallCategory (C k)]
  (A : ∀ k, Premodel Sig (C k)) (L : ι → Type) (leaf : ι) [TopologicalSpace (L leaf)]

def Coordinates (ρ : RTy) :=
  Set (args A L leaf ρ) × {y : ∀ k, L k → (A k).Dom (A k).W₀ (.rel ρ) //
    IsLocallyConstant (y leaf)}

def row {ρ : RTy} (a : (action A L leaf).D (.rel ρ)) : Set (args A L leaf ρ) :=
  {b | Sum.inl (PUnit.unit, b) ∈ a.1}

noncomputable def profile {ρ : RTy} (a : (action A L leaf).D (.rel ρ))
    (k : ι) (x : L k) := (action A L leaf).tr _ (baseArrow A L k x) a

theorem local_profile {ρ : RTy} (a : (action A L leaf).D (.rel ρ)) :
    IsLocallyConstant (profile A L leaf a leaf) :=
  StoneLeaves.entity_local (baseArrow A L leaf) (fun _ _ => rfl)
    (atom A L .e) (fun i => atom A L (.var i))
    (fun _ => IsLocallyConstant.of_constant _ (fun _ _ => rfl))
    (fun _ _ => IsLocallyConstant.of_constant _ (fun _ _ => rfl)) _ a

/-- A set of root tuples is entirely determined by its current extension and
its intensions at the labelled component bases, since every external arrow factors
through its labelled base arrow. -/
theorem glue_profile {ρ : RTy} (a : (action A L leaf).D (.rel ρ)) :
    glue A L leaf (row A L leaf a) (profile A L leaf a) (local_profile A L leaf a) = a := by
  apply Subtype.ext
  apply Set.ext
  intro p
  rcases p with ⟨⟨⟩, b⟩ | ⟨k, U, b, x, j⟩
  · rfl
  · have h := congrArg (fun X : Intension (A k).inner ρ (A k).W₀ =>
        (⟨U, b, j⟩ : Tuple (A k).inner ρ (A k).W₀) ∈ X)
      (incl_relLevel_tr (sel A L leaf) ρ _ (baseArrow A L k x) a)
    change ((⟨U, b, j⟩ : Tuple (A k).inner ρ (A k).W₀) ∈
      (A k).incl ρ _ (profile A L leaf a k x)) ↔ Sum.inr ⟨k, U, b, x, j⟩ ∈ a.1
    apply Iff.of_eq
    refine h.trans ?_
    change (Sum.inr ⟨k, U, b, x, 𝟙 _ ≫ j⟩ ∈ a.1) = _
    rw [Category.id_comp]

/-- The classification is a bijection for all relational types, including the
propositional type and all graph types. -/
noncomputable def coordinatesEquiv (ρ : RTy) :
    (action A L leaf).D (.rel ρ) ≃ Coordinates A L leaf ρ where
  toFun a := ⟨row A L leaf a, ⟨profile A L leaf a, local_profile A L leaf a⟩⟩
  invFun z := glue A L leaf z.1 z.2.1 z.2.2
  left_inv := glue_profile A L leaf
  right_inv := by
    rintro ⟨R, y, hy⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      funext k x
      exact tr_glue A L leaf R y hy k x

/-- Signature Maximalism in the map's native possibility formulation transfers
from any component with a label. -/
theorem preserves_maximalism (M : ∀ k, (A k).IsModel) {k : ι} (x : L k)
    (old : (A k).HoldsAx (AxiomSet.possibilityC Sig)) :
    (model A L leaf).HoldsAx (AxiomSet.possibilityC Sig) := by
  rintro _ ⟨ht, p, hcons, rfl⟩
  exact preserves_dia A L leaf M x p (old _ ⟨ht, p, hcons, rfl⟩)

theorem preserves_pure_maximalism (M : ∀ k, (A k).IsModel) {k : ι} (x : L k)
    (old : (A k).HoldsAx (AxiomSet.pureVersion AxiomSet.possibilityC)) :
    (model A L leaf).HoldsAx (AxiomSet.pureVersion AxiomSet.possibilityC) := by
  rintro _ ⟨_, ⟨ht, p, hcons, rfl⟩, rfl⟩
  exact preserves_dia A L leaf M x (Term.ofPure p)
    (old _ ⟨_, ⟨ht, p, hcons, rfl⟩, rfl⟩)

#print axioms coordinatesEquiv
#print axioms preserves_maximalism
#print axioms preserves_pure_maximalism

end Classicism.Meta.Coalesced.StoneFan
