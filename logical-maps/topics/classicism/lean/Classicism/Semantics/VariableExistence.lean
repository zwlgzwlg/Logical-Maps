import Classicism.Completeness.TypeVariables
import Classicism.Semantics.IntensionalFacts

/-! Variable-sort witnesses at a pointed model and its continuations. -/

namespace Classicism.Meta.Intensional.Premodel

open CategoryTheory

variable {Sig : Signature} {C : Type} [SmallCategory C] (A : Premodel Sig C)

/-- One native existence instance at an arbitrary history. -/
theorem holds_exists_self_iff (M : A.IsModel) {W : C} (h : A.W₀ ⟶ W)
    (σ : Ty) :
    A.Holds h (Term.exists' (σ := σ) (Term.eq' (Term.var .zero) (Term.var .zero))) .nil ↔
      Nonempty (A.Dom W σ) := by
  rw [A.holds_exists M]
  exact ⟨fun ⟨x, _⟩ => ⟨x⟩, fun ⟨x⟩ => ⟨x, (A.holds_eq M _ _ _ _).2 rfl⟩⟩

/-- The variable-existence schema quantifies over the variable sorts at the
designated point. -/
theorem holdsAx_varExistence_iff (M : A.IsModel) :
    A.HoldsAx AxiomSet.varExistence ↔ ∀ i, Nonempty (A.Dom A.W₀ (.var i)) := by
  constructor
  · intro H i
    exact (A.holds_exists_self_iff M (𝟙 _) (.var i)).1 (H _ ⟨i, rfl⟩)
  · rintro H _ ⟨i, rfl⟩
    exact (A.holds_exists_self_iff M (𝟙 _) (.var i)).2 (H i)

/-- Existing variable witnesses transport to the distinguished point at the
end of any specified history. -/
theorem holdsAx_varExistence_truncate (M : A.IsModel) (H : A.HoldsAx AxiomSet.varExistence)
    {W : C} (h : A.W₀ ⟶ W) : (A.truncate h).HoldsAx AxiomSet.varExistence := by
  apply ((A.truncate h).holdsAx_varExistence_iff (A.isModel_truncate h M)).2
  intro i
  obtain ⟨x⟩ := (A.holdsAx_varExistence_iff M).1 H i
  exact ⟨(A.inner (.var i)).map h x⟩

end Classicism.Meta.Intensional.Premodel
