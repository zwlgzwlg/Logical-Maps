import Classicism.StrongPossibility.ProxySignature
import Classicism.StrongPossibility.ProxyReading

/-! The six fresh names and the closed proxy diagonal under a change of signature. -/

namespace Classicism.Meta.ProxyDiagonal

open CategoryTheory Intensional Term ProxySignature

variable {Sig : Signature} {Γ : Ctx}

/-- The six controls in the order used by the start, old, and private tests. -/
def Six.ofFin {α : Type} (v : Fin 6 → α) : Six α :=
  ⟨v 0, v 1, v 2, v 3, v 4, v 5⟩

abbrev namedControls : Names (Extended Sig) Γ := Six.ofFin control

variable {C : Type} [SmallCategory C] (A : Premodel Sig C)
variable (v : Fin 6 → A.Dom A.W₀ .e) {W V : C}

/-- The expanded constants denote the six transported individuals at every history,
in any binder context. -/
theorem read_namedControls (h : A.W₀ ⟶ W) (g : IEnv (A.Dom W) Γ) :
    read (expand A v) h g namedControls = move A h (Six.ofFin v) := rfl

theorem read_namedControls_id (g : IEnv (A.Dom A.W₀) Γ) :
    read (expand A v) (𝟙 A.W₀) g namedControls = Six.ofFin v := by
  rw [read_namedControls]
  simp [move, Six.map, Six.ofFin]

theorem read_namedControls_comp (h : A.W₀ ⟶ W) (k : W ⟶ V) (g : IEnv (A.Dom W) Γ) :
    read (expand A v) (h ≫ k) (A.push k g) namedControls =
      move A k (move A h (Six.ofFin v)) :=
  read_push (expand A v) h k g namedControls

set_option maxHeartbeats 1200000 in
theorem lift_Q : lift (Q (Sig := Sig)) = Q := rfl

set_option maxHeartbeats 1200000 in
theorem lift_rho : lift (rho (Sig := Sig)) = rho := rfl

theorem lift_d : lift (d (Sig := Sig)) = d := by
  change Term.app (lift Q) (lift rho) = _
  rw [lift_Q, lift_rho]
  rfl

theorem lift_Q_app (f : Term Sig [] Tester) : lift (.app Q f) = .app Q (lift f) := by
  change Term.app (lift Q) (lift f) = _
  rw [lift_Q]

theorem lift_f_d (f : Term Sig [] Tester) : lift (.app f d) = .app (lift f) d := by
  change Term.app (lift f) (lift d) = _
  rw [lift_d]

theorem lift_bad (f : Term Sig [] Tester) : lift (bad f) = bad (lift f) := by
  change conj (eq' (lift (.app Q f)) (lift d)) (neg (eq' (lift (.app f d)) top)) = _
  rw [lift_Q_app, lift_d, lift_f_d]
  rfl

/-- Whole old values of both sides of the diagonal are preserved at every history. -/
theorem sem_named_Q_app (h : A.W₀ ⟶ W) (f : Term Sig [] Tester) :
    (expand A v).sem h (.app Q (lift f)) .nil = A.sem h (.app Q f) .nil := by
  simpa only [lift_Q_app] using sem_expand_lift A v h (.app Q f) .nil

theorem sem_named_f_d (h : A.W₀ ⟶ W) (f : Term Sig [] Tester) :
    (expand A v).sem h (.app (lift f) d) .nil = A.sem h (.app f d) .nil := by
  simpa only [lift_f_d] using sem_expand_lift A v h (.app f d) .nil

theorem holds_named_bad (h : A.W₀ ⟶ W) (f : Term Sig [] Tester) :
    (expand A v).Holds h (bad (lift f)) .nil ↔ A.Holds h (bad f) .nil := by
  rw [← lift_bad, holds_lift]

end Classicism.Meta.ProxyDiagonal
