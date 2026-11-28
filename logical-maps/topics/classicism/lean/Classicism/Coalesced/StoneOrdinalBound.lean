import Classicism.Coalesced.StoneOrdinals
import Classicism.Coalesced.StoneMaximalist

/-! A bound for the actual inexact ordinal carrier, chosen independently of the
topology or cardinality of the later leaf space. -/

namespace Classicism.Meta.Coalesced.StoneFan.Canonical

open CategoryTheory Classicism.Meta.Intensional Ordinals

noncomputable section

variable (Sig : Signature) [Countable Sig.Const]

private abbrev A := family Sig (terminal Sig)

/-- Actual individuals depend on the component domains, independently of their labels. -/
abbrev OrdinalIndividuals := ∀ k, (A Sig k).Dom (A Sig k).W₀ .e

/-- A Boolean truth table on pairs of *current extensions* for the order and field. -/
abbrev OrdinalTable := Set (Set (OrdinalIndividuals Sig × OrdinalIndividuals Sig × PUnit.{1}) ×
  Set (OrdinalIndividuals Sig × PUnit.{1}))

/-- A fixed bound made out of the actual individual carrier and the two original
component carriers. It contains no reference to the eventual leaf space. -/
abbrev OrdinalBound :=
  OrdinalTable Sig × (A Sig false).Dom (A Sig false).W₀ (.rel (carrier .e)) ×
    Set ((A Sig true).Dom (A Sig true).W₀ (.rel (carrier .e)))

variable (X : Type) [TopologicalSpace X]

private noncomputable abbrev P := fan Sig (terminal Sig) X
private noncomputable abbrev w := (P Sig X).W₀
private abbrev O := (P Sig X).Dom (w Sig X) (.rel (carrier .e))

/-- The actual entities satisfying the deep impredicative predicate. -/
abbrev ActualOrdinal := {a : O Sig X // (P Sig X).Holds (𝟙 (w Sig X)) (ordinalFormula .e) (.cons a .nil)}

private def encodeTable (a : O Sig X) : OrdinalTable Sig :=
  {u | ∃ (R : (P Sig X).Dom (w Sig X) (.rel (binary .e)))
      (F : (P Sig X).Dom (w Sig X) (.rel (unary .e))),
    ((P Sig X).incl (binary .e) (w Sig X) R).ext' (P Sig X).inner = u.1 ∧
    ((P Sig X).incl (unary .e) (w Sig X) F).ext' (P Sig X).inner = u.2 ∧
      row₂ (W := w Sig X) (P Sig X) a R F}

private abbrev proj (a : O Sig X) := profile (A Sig) (labels X) true a

private def encode (a : ActualOrdinal Sig X) : OrdinalBound Sig :=
  (encodeTable Sig X a.1, proj Sig X a.1 false (), Set.range (proj Sig X a.1 true))

/-- Every actual inexact ordinal injects into the fixed bound, for every X
including an empty space. The leaf coordinate uses the range of a constant map,
so the proof does not need a chosen leaf. -/
def ordinalEmbedding : ActualOrdinal Sig X ↪ OrdinalBound Sig where
  toFun := encode Sig X
  inj' := by
    intro a b hab
    apply Subtype.ext
    apply (coordinatesEquiv (A Sig) (labels X) true (carrier .e)).injective
    have ht : encodeTable Sig X a.1 = encodeTable Sig X b.1 := congrArg Prod.fst hab
    have ho : proj Sig X a.1 false () = proj Sig X b.1 false () := congrArg (fun v => v.2.1) hab
    have hl : Set.range (proj Sig X a.1 true) = Set.range (proj Sig X b.1 true) :=
      congrArg (fun v => v.2.2) hab
    let M := components Sig (terminal Sig) (Premodel.full_isModel _)
    apply Prod.ext
    · change row (A Sig) (labels X) true a.1 = row (A Sig) (labels X) true b.1
      ext u
      obtain ⟨R, F, ⟨⟩⟩ := u
      change row₂ (W := w Sig X) (P Sig X) a.1 R F ↔ row₂ (W := w Sig X) (P Sig X) b.1 R F
      have mem (d : ActualOrdinal Sig X) :
          row₂ (W := w Sig X) (P Sig X) d.1 R F ↔
          (((P Sig X).incl (binary .e) (w Sig X) R).ext' (P Sig X).inner, ((P Sig X).incl (unary .e) (w Sig X) F).ext' (P Sig X).inner) ∈ encodeTable Sig X d.1 := by
        constructor
        · exact fun hh => ⟨R, F, rfl, rfl, hh⟩
        · rintro ⟨R', F', hR, hF, hd⟩
          have hc := ordinal_current_extensional (A Sig) (labels X) true M d.1 d.2
          exact (hc F' F R' R hF hR).1 hd
      rw [mem a, mem b, ht]
    · apply Subtype.ext
      funext k x
      cases k with
      | false => cases x; exact ho
      | true =>
        have hx : proj Sig X a.1 true x ∈ Set.range (proj Sig X b.1 true) :=
          hl ▸ Set.mem_range_self x
        obtain ⟨z, hz⟩ := hx
        exact hz.symm.trans (ordinal_leaf_uniform (A Sig) (labels X) true M b.1 b.2 z x)

#print axioms ordinalEmbedding

end
end Classicism.Meta.Coalesced.StoneFan.Canonical
