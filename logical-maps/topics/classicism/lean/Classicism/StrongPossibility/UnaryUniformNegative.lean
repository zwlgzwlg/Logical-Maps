import Classicism.StrongPossibility.PermanentSemantics
import Classicism.StrongPossibility.UnaryLicences
import Classicism.StrongPossibility.UnarySeparation

/-! A descriptor root with two representatives of each named individual.
The representatives coincide on every exit. The canonical family still
witnesses ordinary Maximalism in the original signature. -/

noncomputable section
namespace Classicism.Meta.UnarySP

open CategoryTheory Intensional Coalesced DistinguishedDefinable Term
open StrongPossibility Classicism.Proofs.UnarySP

variable {Sig : Signature} [Countable Sig.Const]

private def copies (Sig : Signature) : Representatives Sig where
  carrier := names (Sig := Sig) .e × Bool
  read := Prod.fst
  named n := (n, false)
  read_named _ := rfl

/-- An individual and its copy differ at the root. Every exit identifies them,
and the identity at the root has an exit as a continuation. -/
private theorem copies_fail_permanent (hS : Sig.Closed) (n : names (Sig := Sig) .e)
    (ne : Nonempty (copies Sig).carrier) :
    ¬ (Representatives.model (canonicalFamily Sig) (copies Sig) ne).HoldsSentence
      (ofPure permanent.term) := by
  let A := canonicalFamily Sig
  let B := Representatives.model A (copies Sig) ne
  have M : B.IsModel := Representatives.isModel A (copies Sig) ne canonicalFamily_isModel
  obtain ⟨w, _⟩ := Completeness.exists_world (Ax := AxiomSet.empty) hS (fun _ h => h.elim)
    (AxiomSet.Consistent.of_model B M B.holdsAx_empty)
  intro guard
  let x : B.Dom B.W₀ .e := (n, false)
  let y : B.Dom B.W₀ .e := (n, true)
  have diff : x ≠ y := fun e => Bool.noConfusion (congrArg Prod.snd e)
  obtain ⟨V, h, stays⟩ := (holds_permanent_iff B M).1 guard x y diff
  cases V with
  | root =>
    exact stays (.of ⟨w, (A w).W₀⟩) (CoalescedSum.arr (baseArrows A) (dist A w)) rfl
  | of site =>
    rcases site with ⟨i, z⟩
    exact stays (.of ⟨i,z⟩) (𝟙 _) rfl

theorem guarded_permanent_licence (hS : Sig.Closed) (hn : Nonempty (names (Sig := Sig) .e)) :
    AxiomSet.Consistent (AxiomSet.maximalist ∪ AxiomSet.single
      (guardedAt (ofPure (Sig := Sig) permanent.term))) := by
  let n := Classical.choice hn
  let ne : Nonempty (copies Sig).carrier := ⟨(n,false)⟩
  apply representatives_licence hS (copies Sig) ne
  exact guard_of_descriptors (copies Sig) ne
    (UnaryCanonical.canonical_separation (UnarySeparation.predecessors Sig)) _
    (copies_fail_permanent hS n ne)

end Classicism.Meta.UnarySP
