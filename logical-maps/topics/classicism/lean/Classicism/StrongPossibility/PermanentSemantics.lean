import Classicism.StrongPossibility.Permanent
import Classicism.Semantics.FullModels

namespace Classicism.Meta.UnarySP
open CategoryTheory Intensional Term Classicism.Proofs.UnarySP

/-- The arrow making a distinction permanent preserves it on every continuation. -/
theorem holds_permanent_iff {Sig : Signature} {C : Type} [SmallCategory C]
    (B : Premodel Sig C) (M : B.IsModel) :
    B.HoldsSentence (ofPure (Sig := Sig) permanent.term) ↔
      ∀ x y : B.Dom B.W₀ .e, x ≠ y → ∃ (V : C) (h : B.W₀ ⟶ V),
        ∀ (U : C) (k : V ⟶ U), (B.inner .e).map (h ≫ k) x ≠ (B.inner .e).map (h ≫ k) y := by
  change B.Holds (𝟙 _) (forall' (forall' (σ := .e) (Term.imp (neg (eq' v1 v0))
    (dia (box (neg (eq' v1 v0))))))) .nil ↔ _
  simp only [B.holds_forall M, B.holds_imp M, B.holds_dia M, B.holds_box M]
  simp only [B.holds_neg M, B.holds_eq_var M, IEnv.get_map, IEnv.get, Functor.map_comp_apply]

end Classicism.Meta.UnarySP
