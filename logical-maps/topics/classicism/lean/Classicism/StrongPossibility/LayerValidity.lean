import Classicism.StrongPossibility.LowerTransfer
import Classicism.Semantics.VariableExistence

/-! Every term in the two-layer model is admitted. Upstairs the upper rows of
its denotation are unrestricted and its vertical restriction is an old term.
This argument handles abstractions with parameters of arbitrary types. -/

namespace Classicism.Meta.StrongPossibility.Layers
open CategoryTheory Intensional
noncomputable section

variable {Sig : Signature} {U C : Type} [SmallCategory U] [SmallCategory C]
  (π : U ⥤ C) (O : Premodel Sig C) (E : Domain π O .e)

/-- The only restriction on an intension at an upper site is that the
intension seen at its vertical exit is an admitted old relation. -/
private theorem admit_upper {u : U} {ρ : RTy} (X : Intension (inner π O E) ρ (.upper u))
    (b : O.Dom (π.obj u) (.rel ρ))
    (hb : incl π O E ρ (.lower (π.obj u)) b =
      Intension.map (inner π O E) (Site.cross π (𝟙 (π.obj u))) X) :
    X ∈ Set.range (incl π O E ρ (.upper u)) := by
  refine ⟨(fun p => (⟨.upper p.1, (newArgs π O E ρ (u := p.1)).symm p.2.1,
    Site.up π p.2.2⟩ : Tuple (inner π O E) ρ (.upper u)) ∈ X, b), ?_⟩
  ext ⟨v, a, j⟩
  cases v with
  | upper v =>
    change (⟨.upper v, (newArgs π O E ρ (u := v)).symm ((newArgs π O E ρ (u := v)) a), j⟩ :
      Tuple (inner π O E) ρ (.upper u)) ∈ X ↔ _
    rw [Equiv.symm_apply_apply]
  | lower v =>
    have H := Set.ext_iff.mp hb ⟨.lower v, a, Site.down π j⟩
    change ((⟨v, (oldArgs π O E ρ (z := v)) a, j⟩ : Tuple O.inner ρ _) ∈ O.incl ρ _ b) ↔ _
    change ((⟨v, (oldArgs π O E ρ (z := v)) a, j⟩ : Tuple O.inner ρ _) ∈ O.incl ρ _ b) ↔
      (⟨.lower v, a, Site.cross π (𝟙 (π.obj u) ≫ j)⟩ : Tuple (inner π O E) ρ (.upper u)) ∈ X at H
    simpa only [Category.id_comp] using H

variable (u : U) (base : O.W₀ ⟶ π.obj u) (ne : ∀ v, Nonempty (E.upper.obj v))
  (lift : O.Dom (π.obj u) .e → E.upper.obj u)
local notation "A" => model π O E u base ne lift

variable (section_lift : ∀ x, E.project.app u (lift x) = x)
include section_lift

/-- Whole old denotations and unrestricted upper rows suffice for every term. -/
theorem isModel (M : O.IsModel) : (A).IsModel := by
  have lower {Γ : Ctx} {ρ : RTy} {z : C} (h : π.obj u ⟶ z)
      (t : Term Sig Γ (.rel ρ)) (g : IEnv (O.Dom z) Γ) :
      (A).sem (Site.cross π h) t g ∈ Set.range ((A).Incl (.rel ρ) (.lower z)) := by
    obtain ⟨b, hb⟩ := M (base ≫ h) t g
    refine ⟨b, oldOuter_injective π O E (.rel ρ) z ?_⟩
    rw [old_incl, old_sem π O E u base ne lift section_lift]
    exact hb
  intro Γ σ W h t g
  cases σ with
  | e => exact ⟨_, rfl⟩
  | var i => exact ⟨_, rfl⟩
  | rel ρ =>
    cases W with
    | lower z => exact lower h t g
    | upper v =>
      let vertical := Site.cross π (𝟙 (π.obj v))
      let j : (A).W₀ ⟶ Site.lower (π.obj v) := h ≫ vertical
      obtain ⟨b, hb⟩ := lower j t ((A).push vertical g)
      apply admit_upper π O E _ b
      exact hb.trans ((A).sem_push h t g vertical)

/-- At every variable sort the upper carrier is the corresponding old carrier.
Transporting the old witnesses along the chosen base arrow supplies all the
variable-existence instances in the new model. -/
theorem holdsAx_varExistence (M : O.IsModel) (vars : O.HoldsAx AxiomSet.varExistence) :
    (A).HoldsAx AxiomSet.varExistence := by
  apply ((A).holdsAx_varExistence_iff (isModel π O E u base ne lift section_lift M)).2
  intro i
  obtain ⟨x⟩ := (O.holdsAx_varExistence_iff M).1 vars i
  exact ⟨(O.inner (.var i)).map base x⟩

end
end Classicism.Meta.StrongPossibility.Layers
