import Classicism.Coalesced.StoneInterval
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# A Stone space for a set-indexed catalogue of Boolean algebras

Use the prime spectrum of the Boolean ring of the product algebra. Its clopens
are the product itself, and each factor is a principal interval. The same single
native Maximalist fan consequently realizes every catalogue factor at its root.
-/

namespace Classicism.Meta.Coalesced.StoneFan.Canonical

open CategoryTheory Classicism.Meta.Intensional TopologicalSpace

/-- Stone representation in the order form used by native entailment. -/
noncomputable def booleanClopens (B : Type) [BooleanAlgebra B] :
    B ≃o Clopens (PrimeSpectrum (AsBoolRing B)) := by
  let e : B ≃o {v : AsBoolRing B // IsIdempotentElem v} :=
    { toFun := fun b => ⟨toBoolRing b, BooleanRing.isIdempotentElem _⟩
      invFun := fun v => ofBoolRing v.1
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := fun {a b} =>
        (ofBoolRing_le_ofBoolRing_iff (a := toBoolRing a) (b := toBoolRing b)).symm }
  exact e.trans PrimeSpectrum.isIdempotentElemEquivClopens

variable {ι : Type} (B : ι → Type) [∀ i, BooleanAlgebra (B i)]

/-- The spectrum is chosen once for the entire family of algebras. -/
abbrev catalogueSpace := PrimeSpectrum (AsBoolRing (∀ i, B i))

private noncomputable def putFactor (i : ι) (b : B i) : ∀ j, B j := by
  classical
  exact Function.update (fun _ => ⊥) i b

private theorem putFactor_self (i : ι) (b : B i) : putFactor B i b i = b := by
  classical
  simp [putFactor]

private theorem putFactor_other {i j : ι} (h : j ≠ i) (b : B i) :
    putFactor B i b j = ⊥ := by
  classical
  simp [putFactor, h]

private noncomputable def factorInterval (i : ι) :
    B i ≃o Set.Iic (putFactor B i ⊤) where
  toFun b := ⟨putFactor B i b, by
    intro j
    by_cases h : j = i
    · subst j; simp only [putFactor_self, le_top]
    · simp only [putFactor_other B h, le_refl]⟩
  invFun x := x.1 i
  left_inv b := putFactor_self B i b
  right_inv x := by
    apply Subtype.ext
    funext j
    change putFactor B i (x.1 i) j = x.1 j
    by_cases h : j = i
    · subst j; exact putFactor_self B i _
    · rw [putFactor_other B h]
      have hx := x.2 j
      rw [putFactor_other B h] at hx
      exact (le_antisymm hx bot_le).symm
  map_rel_iff' := by
    intro a b
    change (∀ j, putFactor B i a j ≤ putFactor B i b j) ↔ a ≤ b
    constructor
    · intro h
      simpa only [putFactor_self] using h i
    · intro h j
      by_cases hj : j = i
      · subst j; simpa only [putFactor_self] using h
      · simp only [putFactor_other B hj, le_refl]

noncomputable def catalogueClopen (i : ι) : Clopens (catalogueSpace B) :=
  booleanClopens (∀ i, B i) (putFactor B i ⊤)

noncomputable def catalogueInterval (i : ι) : B i ≃o Set.Iic (catalogueClopen B i) :=
  (factorInterval B i).trans ((booleanClopens (∀ i, B i)).Iic _)

variable (Sig : Signature) [Countable Sig.Const]

/-- In one concrete native fan on the catalogue spectrum, any catalogue factor
identified with a typed current carrier is represented by a whole native
entailment interval and an admitted mixed graph. -/
theorem realizes_catalogue_graph {σ : Ty} (i : ι)
    (E : Set ((fan Sig (terminal Sig) (catalogueSpace B)).Dom
      (fan Sig (terminal Sig) (catalogueSpace B)).W₀ σ))
    (R : E → E → Prop) (f : E ≃ B i) (hf : ∀ a b, R a b ↔ f a ≤ f b) :
    HasIntervalGraph Sig (catalogueSpace B) E R := by
  apply realizes_interval_graph Sig _ E R (catalogueClopen B i) (f.trans (catalogueInterval B i).toEquiv)
  exact fun a b => (hf a b).trans (catalogueInterval B i).le_iff_le.symm

/-- Every Boolean algebra carried by a subset of the fixed bounding type is
one factor. This index and its spectrum are chosen before the typed root carrier. -/
structure BoundedAlgebra (κ : Type) where
  carrier : Set κ
  algebra : BooleanAlgebra carrier

instance {κ : Type} (i : BoundedAlgebra κ) : BooleanAlgebra i.carrier := i.algebra

abbrev boundedSpace (κ : Type) := catalogueSpace (fun i : BoundedAlgebra κ => i.carrier)

/-- Every actual Boolean algebra whose carrier embeds in κ is represented in the
same fixed maximalist fan, even if its carrier is given only after choosing that
fan. Its Boolean algebra order is the order read by the graph. -/
theorem realizes_bounded_graph (κ : Type) {σ : Ty}
    (E : Set ((fan Sig (terminal Sig) (boundedSpace κ)).Dom
      (fan Sig (terminal Sig) (boundedSpace κ)).W₀ σ)) [BooleanAlgebra E] (f : E ↪ κ) :
    HasIntervalGraph Sig (boundedSpace κ) E (fun a b => a ≤ b) := by
  let e := Equiv.ofInjective f f.injective
  let i : BoundedAlgebra κ := ⟨Set.range f, e.symm.booleanAlgebra⟩
  apply realizes_catalogue_graph (fun j : BoundedAlgebra κ => j.carrier) Sig i E _ e
  intro a b
  change (a ≤ b) ↔ e.symm (e a) ≤ e.symm (e b)
  simp only [Equiv.symm_apply_apply]

/-- The same fan satisfies both Maximalism schemata and represents every
current typed Boolean algebra bounded by κ. The signature condition comes from the
upstream canonical Maximalist existence theorem. -/
theorem maximalist_represents_bounded (hS : Sig.Closed) (κ : Type) :
    let P := fan Sig (terminal Sig) (boundedSpace κ)
    P.IsModel ∧ P.HoldsAx (AxiomSet.possibilityC Sig) ∧
      P.HoldsAx (AxiomSet.pureVersion AxiomSet.possibilityC) ∧
      ∀ (σ : Ty) (E : Set (P.Dom P.W₀ σ)) [BooleanAlgebra E], (E ↪ κ) →
        HasIntervalGraph Sig (boundedSpace κ) E (fun a b => a ≤ b) := by
  obtain ⟨hM, hSig, hPure⟩ := singleton_fan_maximalist Sig (boundedSpace κ) hS
  exact ⟨hM, hSig, hPure, fun _ _ _ f => realizes_bounded_graph Sig κ _ f⟩

#print axioms maximalist_represents_bounded
#print axioms realizes_bounded_graph
#print axioms booleanClopens
#print axioms catalogueInterval
#print axioms realizes_catalogue_graph

end Classicism.Meta.Coalesced.StoneFan.Canonical
