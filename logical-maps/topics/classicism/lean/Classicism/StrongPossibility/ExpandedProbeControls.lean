import Classicism.StrongPossibility.ProbeModel
import Classicism.StrongPossibility.ProxySignature

/-! The six named controls for a test family over an arbitrary old model. -/
namespace Classicism.Meta.ProxyDiagonal

open CategoryTheory Intensional ProxySignature

variable {Sig : Signature} {C : Type} [SmallCategory C]

/-- All six fresh names are distinct symbols even when they denote the same old anchor. -/
def expandedControls (A : Premodel Sig C) (anchor : A.Dom A.W₀ .e) :
    Controls (expand A (fun _ => anchor)) where
  name i := ⟨Sum.inr i, rfl⟩
  injective := by
    intro i j hij
    exact Sum.inr.inj (congrArg Subtype.val hij)
  anchor := anchor
  fixed _ := rfl

end Classicism.Meta.ProxyDiagonal
