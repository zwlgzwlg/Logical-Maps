import Classicism.StrongPossibility.ProxyFibres
import Classicism.Coalesced.PointedPair
import Classicism.Coalesced.DistinguishedDefinable
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

/-! The full two-exit test model used to read one tuple at an old site. The
old component has arbitrary Henkin domains. The other component is the full
classical hierarchy on the set of private labels. -/

namespace Classicism.Meta.ProxyDiagonal

open CategoryTheory Classicism.Meta.Intensional Classicism.Meta.Coalesced

noncomputable section

variable {Sig : Signature} {C : Type} [SmallCategory C]
abbrev IndividualNames (Sig : Signature) := {c : Sig.Const // Sig.typeOf c = Ty.e}

def oldNameAt (O : Premodel Sig C) (c : IndividualNames Sig) : O.Dom O.W₀ .e :=
  castD (D := O.Dom O.W₀) c.2 (O.I c.1)

abbrev privateAction (N : Type) (b : Bool) : SingleObj Unit ⥤ Type :=
  (Functor.const _).obj (Label N b)

variable {N : Type} {b : Bool}
variable (named : IndividualNames Sig → Label N b)

def privateValueAt (c : Sig.Const) : ∀ (σ : Ty), Sig.typeOf c = σ →
    ((FullT (privateAction N b) σ).obj (SingleObj.star Unit))
  | .e, h => named ⟨c,h⟩
  | .var _, _ => .ctrl false
  | .rel _, _ => ∅

abbrev privateModel : Premodel Sig (SingleObj Unit) :=
  Premodel.full (privateAction N b) (SingleObj.star Unit) (fun _ => ⟨.ctrl false⟩)
    (fun c => privateValueAt named c _ rfl)

theorem private_isModel : (privateModel named).IsModel := Premodel.full_isModel _

theorem private_name (c : IndividualNames Sig) :
    oldNameAt (privateModel named) c = named c := by
  rcases c with ⟨c,h⟩
  change castD (D := fun σ => (FullT (privateAction N b) σ).obj (SingleObj.star Unit))
    h (privateValueAt named c _ rfl) = named ⟨c,h⟩
  have aux : ∀ τ (q : Sig.typeOf c = τ),
      castD (D := fun σ => (FullT (privateAction N b) σ).obj (SingleObj.star Unit))
        q (privateValueAt named c _ rfl) = privateValueAt named c τ q := by
    intro τ q
    cases q
    rfl
  exact aux _ h

/-- The old value of the six control names is the common anchor. -/
structure Controls (O : Premodel Sig C) where
  name : Fin 6 → IndividualNames Sig
  injective : Function.Injective name
  anchor : O.Dom O.W₀ .e
  fixed (i : Fin 6) : oldNameAt O (name i) = anchor

def Six.get {α : Type} (x : Six α) : Fin 6 → α :=
  ![x.a0,x.a1,x.b0,x.b1,x.c0,x.c1]

variable (O : Premodel Sig C) (K : Controls O)
variable (u : Fin 6 → O.Dom O.W₀ .e) (colour : Bool)

def slot (n : IndividualNames Sig) : ProxyInd (IndividualNames Sig) colour := by
  classical
  exact if h : ∃ i, K.name i = n then proxyControls.get (Classical.choose h)
    else ⟨.name n,⟨0, Nat.zero_lt_succ _⟩⟩

theorem slot_control (i : Fin 6) :
    slot O K colour (K.name i) = proxyControls.get i := by
  classical
  have H : ∃ j, K.name j = K.name i := ⟨i,rfl⟩
  simp only [slot, dif_pos H]
  rw [K.injective (Classical.choose_spec H)]

theorem slot_old (n : IndividualNames Sig) :
    oldImage u K.anchor (oldNameAt O) (slot O K colour n) = oldNameAt O n := by
  classical
  by_cases h : ∃ i, K.name i = n
  · obtain ⟨i,rfl⟩ := h
    rw [slot_control, K.fixed]
    fin_cases i <;> rfl
  · simp only [slot, dif_neg h]
    rfl

abbrev leaf := privateModel (fun n => privateImage (slot O K colour n))
abbrev proj := oldImage (b := colour) u K.anchor (oldNameAt O)
abbrev prj := privateImage (N := IndividualNames Sig) (b := colour)

def names : PointedPair.Names O (leaf O K colour) (proj O K u colour) (prj (Sig := Sig) colour) where
  lift c h := slot O K colour ⟨c,h⟩
  old c h := slot_old O K u colour ⟨c,h⟩
  priv c h := (private_name (fun n => privateImage (slot O K colour n)) ⟨c,h⟩).symm

abbrev site := PointedPair.model O (leaf O K colour) (proj O K u colour) (prj (Sig := Sig) colour)
  (names O K u colour) ⟨controlInd false 0⟩

theorem site_isModel (h : O.IsModel) : (site O K u colour).IsModel :=
  PointedPair.isModel _ _ _ _ _ _ h (private_isModel _)

end
end Classicism.Meta.ProxyDiagonal
