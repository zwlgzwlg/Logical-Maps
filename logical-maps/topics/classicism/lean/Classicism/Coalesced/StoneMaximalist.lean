import Classicism.Coalesced.StoneRigidity
import Classicism.Coalesced.Complete
import Classicism.Semantics.IntensionalFull
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finite.Sigma

/-! Concrete Stone fans on the map's canonical Maximalist model. -/

namespace Classicism.Meta.Coalesced.StoneFan.Canonical

open CategoryTheory Classicism.Meta.Intensional

/-- A family with one old category and one leaf category. -/
def sides (O K : Type) : Bool → Type
  | false => O
  | true => K

instance sideCategory {O K : Type} [SmallCategory O] [SmallCategory K] :
    (i : Bool) → SmallCategory (sides O K i)
  | false => inferInstanceAs (SmallCategory O)
  | true => inferInstanceAs (SmallCategory K)

variable (Sig : Signature) [Countable Sig.Const]

abbrev Old := CoalescedSum (baseArrows (canonicalFamily Sig))

variable {K : Type} [SmallCategory K] (B : Premodel Sig K)

noncomputable def family : ∀ i, Premodel Sig (sides (Old Sig) K i)
  | false => maximalist Sig
  | true => B

def labels (X : Type) : Bool → Type
  | false => Unit
  | true => X

instance leafTopology (X : Type) [TopologicalSpace X] : TopologicalSpace (labels X true) :=
  inferInstanceAs (TopologicalSpace X)

variable (X : Type) [TopologicalSpace X]

noncomputable abbrev fan := model (family Sig B) (labels X) true

theorem components (hB : B.IsModel) : ∀ i, (family Sig B i).IsModel
  | false => maximalist_isModel
  | true => hB

/-- A fixed native model with any given label space and leaf model. For a
countable signature of closed types it satisfies both Maximalism schemata. -/
theorem fan_maximalist (hS : Sig.Closed) (hB : B.IsModel) :
    (fan Sig B X).IsModel ∧
    (fan Sig B X).HoldsAx (AxiomSet.possibilityC Sig) ∧
    (fan Sig B X).HoldsAx (AxiomSet.pureVersion AxiomSet.possibilityC) :=
  ⟨isModel _ _ _ (components Sig B hB),
    preserves_maximalism (family Sig B) (labels X) true (components Sig B hB)
      (k := false) () (maximalist_possibilityC hS),
    preserves_pure_maximalism (family Sig B) (labels X) true (components Sig B hB)
      (k := false) () (maximalist_possibility hS)⟩

/-- The single point and single arrow of the leaf carry a single individual.
All relational types receive their full intension domains. -/
abbrev terminalIndividuals : Fin 1 ⥤ Type := (Functor.const (Fin 1)).obj Unit

noncomputable def terminalValue : ∀ σ : Ty, (FullT terminalIndividuals σ).obj 0
  | .e => ()
  | .var _ => ()
  | .rel _ => ∅

omit [Countable Sig.Const] in
noncomputable def terminal : Premodel Sig (Fin 1) :=
  Premodel.full terminalIndividuals 0 (fun _ => ⟨()⟩) (fun c => terminalValue (Sig.typeOf c))

/-- Every native simple type, including every higher predicate type, has a finite
domain at the full terminal component. -/
theorem terminal_finite (σ : Ty) (W : Fin 1) : Finite ((FullT terminalIndividuals σ).obj W) := by
  refine @Ty.rec (fun σ => ∀ W : Fin 1, Finite ((FullT terminalIndividuals σ).obj W))
    (fun ρ => ∀ W : Fin 1, Finite ((FullArgs terminalIndividuals ρ).obj W)) ?_ ?_ ?_ ?_ ?_ σ W
  · intro V
    exact inferInstanceAs (Finite Unit)
  · intro ρ ih V
    change Finite (Set (Σ U : Fin 1, (FullArgs terminalIndividuals ρ).obj U × (V ⟶ U)))
    let _ (U : Fin 1) : Finite ((FullArgs terminalIndividuals ρ).obj U) := ih U
    infer_instance
  · intro i V
    exact inferInstanceAs (Finite Unit)
  · intro V
    exact inferInstanceAs (Finite PUnit)
  · intro σ ρ hσ hρ V
    let _ := hσ V
    let _ := hρ V
    exact inferInstanceAs (Finite ((FullT terminalIndividuals σ).obj V × (FullArgs terminalIndividuals ρ).obj V))

/-- Terminal propositions are exactly ordinary truth values. -/
def terminalPropEquiv : (FullT terminalIndividuals (.rel .t)).obj 0 ≃ Prop where
  toFun p := (⟨0, PUnit.unit, 𝟙 0⟩ : Σ U : Fin 1, PUnit × ((0 : Fin 1) ⟶ U)) ∈ p
  invFun b := fun _ => b
  left_inv p := by
    ext ⟨U, ⟨⟩, j⟩
    obtain rfl : U = (0 : Fin 1) := Subsingleton.elim _ _
    obtain rfl : j = 𝟙 (0 : Fin 1) := Subsingleton.elim _ _
    rfl
  right_inv _ := rfl

/-- The locally constant terminal proposition profiles are exactly the clopen sets.
The displayed set consists of the labels on which the terminal proposition holds. -/
noncomputable def terminalClopens : LocallyConstant X ((FullT terminalIndividuals (.rel .t)).obj 0) ≃
    TopologicalSpace.Clopens X where
  toFun f := ⟨{x | terminalPropEquiv (f x)}, by
    simpa using (f.isLocallyConstant.comp terminalPropEquiv).isClopen_fiber True⟩
  invFun c := ⟨fun x => terminalPropEquiv.symm (x ∈ c), by
    apply IsLocallyConstant.comp (f := fun x : X => x ∈ c) _ terminalPropEquiv.symm
    apply IsLocallyConstant.iff_isOpen_fiber.2
    intro b
    by_cases hb : b
    · simpa [hb, Set.preimage] using c.isOpen
    · simp [hb, Set.preimage]
      exact c.isClosed.isOpen_compl⟩
  left_inv f := by
    ext x : 1
    exact terminalPropEquiv.symm_apply_apply (f x)
  right_inv c := by
    apply SetLike.ext
    intro x
    exact Iff.of_eq (terminalPropEquiv.apply_symm_apply (x ∈ c))

private abbrev OldProp := (maximalist Sig).Dom (maximalist Sig).W₀ (.rel .t)

private abbrev LeafProp := (FullT terminalIndividuals (.rel .t)).obj 0

private def putProfiles (o : OldProp Sig) (l : X → LeafProp) :
    ∀ k, labels X k → (family Sig (terminal Sig) k).Dom (family Sig (terminal Sig) k).W₀ (.rel .t)
  | false, _ => o
  | true, x => l x

/-- The carrier of native propositions at the actual constructed root has one
truth bit, one old proposition, and one arbitrary clopen subset of the leaf space. -/
noncomputable def propositionCoordinates :
    (fan Sig (terminal Sig) X).Dom (fan Sig (terminal Sig) X).W₀ (.rel .t) ≃
      Prop × OldProp Sig × TopologicalSpace.Clopens X :=
  (coordinatesEquiv (family Sig (terminal Sig)) (labels X) true .t).trans
  { toFun := fun v => (PUnit.unit ∈ v.1, v.2.1 false (),
      terminalClopens X ⟨v.2.1 true, v.2.2⟩)
    invFun := fun v => ⟨fun _ => v.1, ⟨putProfiles Sig X v.2.1 ((terminalClopens X).symm v.2.2),
      ((terminalClopens X).symm v.2.2).isLocallyConstant⟩⟩
    left_inv := by
      rintro ⟨row, f, h⟩
      apply Prod.ext
      · ext ⟨⟩
        rfl
      · apply Subtype.ext
        funext k x
        cases k with
        | false => cases x; rfl
        | true =>
          exact congrArg (fun g : LocallyConstant X LeafProp => g x) ((terminalClopens X).symm_apply_apply ⟨f true,h⟩)
    right_inv := by
      rintro ⟨b, o, c⟩
      apply Prod.ext rfl
      exact Prod.ext rfl ((terminalClopens X).apply_symm_apply c) }

/-- No external model input is needed. The source of all old witnesses is the
canonical Maximalist, and the full singleton terminal interprets every constant.
The label space can in particular be the Stone space chosen for the CBA catalogue. -/
theorem singleton_fan_maximalist (hS : Sig.Closed) :
    (fan Sig (terminal Sig) X).IsModel ∧
    (fan Sig (terminal Sig) X).HoldsAx (AxiomSet.possibilityC Sig) ∧
    (fan Sig (terminal Sig) X).HoldsAx (AxiomSet.pureVersion AxiomSet.possibilityC) :=
  fan_maximalist Sig (terminal Sig) X hS (Premodel.full_isModel _)

omit [Countable Sig.Const] in
private theorem terminal_subset_iff (a b : LeafProp) :
    (terminal Sig).incl .t 0 a ⊆ (terminal Sig).incl .t 0 b ↔
      (terminalPropEquiv a → terminalPropEquiv b) := by
  change fullIncl terminalIndividuals .t 0 a ⊆ fullIncl terminalIndividuals .t 0 b ↔ _
  rw [fullIncl_t, fullIncl_t]
  constructor
  · intro h ha
    exact h ha
  · rintro h ⟨U, ⟨⟩, j⟩ ha
    obtain rfl : U = (0 : Fin 1) := Subsingleton.elim _ _
    obtain rfl : j = 𝟙 (0 : Fin 1) := Subsingleton.elim _ _
    exact h ha

/-- Modal implication between any two native propositions in this concrete model
is precisely implication on the truth bit, inclusion on the old intensions, and
inclusion on the actual clopen subsets of the chosen topological space. -/
theorem proposition_order (a b : (fan Sig (terminal Sig) X).Dom (fan Sig (terminal Sig) X).W₀ (.rel .t)) :
    (fan Sig (terminal Sig) X).Holds (𝟙 (fan Sig (terminal Sig) X).W₀)
      (Term.box (Term.imp (.var .zero) (.var (.succ .zero)))) (.cons a (.cons b .nil)) ↔
      ((propositionCoordinates Sig X a).1 → (propositionCoordinates Sig X b).1) ∧
      (maximalist Sig).incl .t _ (propositionCoordinates Sig X a).2.1 ⊆
        (maximalist Sig).incl .t _ (propositionCoordinates Sig X b).2.1 ∧
      (propositionCoordinates Sig X a).2.2 ≤ (propositionCoordinates Sig X b).2.2 := by
  let A := family Sig (terminal Sig)
  have M := components Sig (terminal Sig) (Premodel.full_isModel _)
  apply (entailment_iff_coordinates A (labels X) true M a b).trans
  constructor
  · rintro ⟨row, prof⟩
    refine ⟨fun h => row h, prof false (), ?_⟩
    intro x hx
    exact (terminal_subset_iff Sig _ _).1 (prof true x) hx
  · rintro ⟨hb, ho, hc⟩
    constructor
    · rintro ⟨⟩ h
      exact hb h
    · intro k x
      cases k with
      | false => cases x; exact ho
      | true => exact (terminal_subset_iff Sig _ _).2 (fun h => hc (x := x) h)

#print axioms singleton_fan_maximalist
#print axioms propositionCoordinates
#print axioms proposition_order
#print axioms terminal_finite

end Classicism.Meta.Coalesced.StoneFan.Canonical
