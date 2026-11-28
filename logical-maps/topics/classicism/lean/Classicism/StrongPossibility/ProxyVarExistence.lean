import Classicism.Semantics.VariableExistence
import Classicism.Coalesced.DistinguishedDefinable
import Classicism.StrongPossibility.TypedSignature

/-! In the distinguished definable construction the root elements of a variable
sort are exactly the typed names of that sort. -/

namespace Classicism.Meta.Coalesced.DistinguishedDefinable

open CategoryTheory Intensional

variable {Sig : Signature} {ι : Type} {C : ι → Type} [∀ k, SmallCategory (C k)]
variable (A : ∀ k, Premodel Sig (C k)) (ne : Nonempty (names (Sig := Sig) .e))

/-- This new point has exactly one variable-sort element per typed name.
Component witnesses alone do not supply elements of its variable domains. -/
theorem holdsAx_varExistence_iff_names (M : ∀ k, (A k).IsModel) :
    (model A ne).HoldsAx AxiomSet.varExistence ↔
      ∀ i, Nonempty (names (Sig := Sig) (.var i)) :=
  (model A ne).holdsAx_varExistence_iff (isModel A ne M)

end Classicism.Meta.Coalesced.DistinguishedDefinable

namespace Classicism.Meta.TypedSignature

open CategoryTheory Intensional

variable {Sig Extra : Signature} {C : Type} [SmallCategory C]

/-- Forgetting a family of auxiliary constants preserves variable existence,
even when none of those variable sorts has a name in the old signature. -/
theorem holdsAx_varExistence_restrict_iff (B : Premodel (sum Sig Extra) C) (M : B.IsModel) :
    (restrict B).HoldsAx AxiomSet.varExistence ↔ B.HoldsAx AxiomSet.varExistence :=
  ((restrict B).holdsAx_varExistence_iff (restrict_isModel B M)).trans
    (B.holdsAx_varExistence_iff M).symm

end Classicism.Meta.TypedSignature

namespace Classicism.Meta.Coalesced.DistinguishedDefinable

open CategoryTheory Intensional TypedSignature

variable {Sig Extra : Signature} {ι : Type} {C : ι → Type} [∀ k, SmallCategory (C k)]

/-- A fresh name in each variable sort suffices at the enlarged distinguished
root. After forgetting them, the witnesses remain in its inner carriers. -/
theorem restricted_model_holdsAx_varExistence
    (A : ∀ k, Premodel (sum Sig Extra) (C k))
    (ne : Nonempty (names (Sig := sum Sig Extra) .e)) (M : ∀ k, (A k).IsModel)
    (v : ∀ i, ∃ c : Extra.Const, Extra.typeOf c = .var i) :
    (restrict (model A ne)).HoldsAx AxiomSet.varExistence := by
  apply (holdsAx_varExistence_restrict_iff _ (isModel A ne M)).2
  apply (holdsAx_varExistence_iff_names A ne M).2
  intro i
  obtain ⟨c, hc⟩ := v i
  exact ⟨⟨.inr c, hc⟩⟩

end Classicism.Meta.Coalesced.DistinguishedDefinable
