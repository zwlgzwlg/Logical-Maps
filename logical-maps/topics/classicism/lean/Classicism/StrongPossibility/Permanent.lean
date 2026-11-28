import Classicism.StrongPossibility.Unary

/-! A pure guard for both Strong Possibility theorems. -/

namespace Classicism.Proofs.UnarySP
open Classicism.P Classicism.Paper

/-- Every current distinction between individuals can become permanent. -/
def permanent : Prop := ∀ x y : e, x ≠ y → ◇ (□ (x ≠ y))

/-- Ask to restore the present distinction. It is already present at the visit
by necessity of identity, so the visit supplies a permanent distinction. -/
theorem reflect_permanent : DiaNe permanent → permanent :=
  fun visit x y distinct => dia_dia _ (dia_mono _ _
    (nec% (fun (h : ◇ (x ≠ y) ∧ permanent) => h.2 x y (ne_of_dia_ne x y h.1)))
    (diaNe_char permanent (x ≠ y) visit distinct))

/-- The two strongly possible laws give opposite answers about permanence here. -/
theorem permanent_contradiction (Q : Family) :
    DiaNe permanent → DiaNe (guarded Q permanent) → False :=
  fun visit guard => excludes_guard Q permanent guard (reflect_permanent visit)

end Classicism.Proofs.UnarySP

#classicism_quote_term Classicism.Proofs.UnarySP.permanent
#classicism_derive Classicism.Proofs.UnarySP.reflect_permanent
#classicism_derive Classicism.Proofs.UnarySP.permanent_contradiction
