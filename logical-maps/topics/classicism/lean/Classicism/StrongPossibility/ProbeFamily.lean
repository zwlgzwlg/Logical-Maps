import Classicism.StrongPossibility.ProbeModel
import Classicism.StrongPossibility.ProxyCode

/-! The direct old component and one pointed test for every old arrow and every
tuple, including tuples whose entries are new at that arrow. -/

namespace Classicism.Meta.ProxyDiagonal.Family

open CategoryTheory Classicism.Meta.Intensional Classicism.Meta.Coalesced
noncomputable section

variable {Sig : Signature} {C : Type} [SmallCategory C]
variable (O : Premodel Sig C) (K : Controls O)

structure Address where
  z : C
  h : O.W₀ ⟶ z
  tuple : Six (O.Dom z .e)

def transported {z : C} (h : O.W₀ ⟶ z) : Controls (O.truncate h) where
  name := K.name
  injective := K.injective
  anchor := (O.inner .e).map h K.anchor
  fixed i := by
    change castD (D := O.Dom z) (K.name i).2
      ((O.inner _).map h (O.I (K.name i).1)) = _
    rw [← castD_map (D := O.Dom O.W₀) (D' := O.Dom z) (fun σ => (O.inner σ).map h)]
    exact congrArg ((O.inner .e).map h) (K.fixed i)

variable (bits : Address O → Bool)

abbrev test (a : Address O) :=
  site (O.truncate a.h) (transported O K a.h) a.tuple.get (bits a)

def Cat : Option (Address O) → Type
  | none => C
  | some a => CoalescedSum (baseArrows (PointedPair.components (O.truncate a.h)
      (leaf (O.truncate a.h) (transported O K a.h) (bits a))))

instance : ∀ i, SmallCategory (Cat O K bits i)
  | none => inferInstanceAs (SmallCategory C)
  | some _ => CoalescedSum.category _

def components : ∀ i, Premodel Sig (Cat O K bits i)
  | none => O
  | some a => test O K bits a

abbrev act := DistinguishedDefinable.action (components O K bits)
abbrev ne : Nonempty (DistinguishedDefinable.names (Sig := Sig) .e) := ⟨K.name 0⟩

abbrev model := DistinguishedDefinable.model (components O K bits) (ne O K)

theorem isModel (o : O.IsModel) : (model O K bits).IsModel :=
  DistinguishedDefinable.isModel _ _ (fun
    | none => o
    | some a => site_isModel _ _ _ _ (O.isModel_truncate a.h o))

end
end Classicism.Meta.ProxyDiagonal.Family
