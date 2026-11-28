import Classicism.StrongPossibility.ProbeCover
import Classicism.StrongPossibility.ProbeColours
import Classicism.StrongPossibility.ProxyCanonicalCore
import Classicism.StrongPossibility.ExpandedProbeControls
import Classicism.StrongPossibility.AuxSignature

/-! Every failure of f(d) in a pointed model with inhabited variable sorts yields
a pointed model refuting the whole identity Qf = d. All temporary names are
forgotten before the new witness is passed to canonical completeness. -/

namespace Classicism.Meta.ProxyDiagonal
open CategoryTheory Intensional Coalesced Term
noncomputable section

namespace Family
variable {Sig : Signature} {C : Type} [SmallCategory C] (O : Premodel Sig C) (K : Controls O)
local notation "bits" => colours O
local notation "A" => model O K bits
local notation "F" => components O K bits

theorem tests (M : O.IsModel) :
    Tests A (rootTuple O K bits) ((A).sem (𝟙 _) d .nil) where
  start := source_start O K bits
  isolated := isolated O K bits
  sound := sound_tests O K
  cover := cover_d O K bits M (colour_direct O)

theorem directHolds (p : Sentence Sig) :
    (A).Holds (direct O K bits (𝟙 O.W₀)) p .nil ↔ O.HoldsSentence p := by
  have H := (act O K bits).holds_arr_sentence (DistinguishedDefinable.inclusion F)
    (ne O K) (DistinguishedDefinable.value F) (k := none) (dist F none) p
  rw [component_dist (DistinguishedDefinable.transports F)] at H
  exact H

theorem rejects_identity (M : O.IsModel) (f : Term Sig [] Tester)
    (h : ¬ O.HoldsSentence (.app f d)) : ¬ (A).HoldsSentence (eq' (.app Q f) d) := by
  apply marked_term_separation A (isModel O K bits M) (𝟙 _) (rootTuple O K bits)
    (tests O K M) f (direct O K bits (𝟙 _)) (direct_old O K bits _)
  rw [Category.id_comp]
  exact fun H => h ((directHolds O K _).1 H)
end Family

private theorem aux_test_failure {Sig : Signature} {C : Type} [SmallCategory C]
    (O : Premodel Sig C) (V : ∀ i, O.Dom O.W₀ (.var i)) (f : Term Sig [] Tester) :
    (AuxSignature.expand O V).HoldsSentence (.app (AuxSignature.lift f) d) ↔ O.HoldsSentence (.app f d) := by
  rw [← AuxSignature.lift_f_d]
  exact TypedSignature.holdsSentence_lift _ _

private theorem strip_aux {Sig : Signature} {C : Type} [SmallCategory C]
    (B : Premodel (AuxSignature.Extended Sig) C) (f : Term Sig [] Tester) :
    (AuxSignature.restrict B).HoldsSentence (eq' (.app Q f) d) ↔
      B.HoldsSentence (eq' (.app Q (AuxSignature.lift f)) d) := by
  have E : AuxSignature.lift (eq' (.app Q f) d) = eq' (.app Q (AuxSignature.lift f)) d := by
    change eq' (AuxSignature.lift (.app Q f)) (AuxSignature.lift d) = _
    rw [AuxSignature.lift_Q_app, AuxSignature.lift_d]
  rw [← E]
  exact (TypedSignature.holdsSentence_lift _ _).symm

private theorem strip_controls {Sig : Signature} {C : Type} [SmallCategory C]
    (B : Premodel (ProxySignature.Extended Sig) C) (f : Term Sig [] Tester) :
    (ProxySignature.restrict B).HoldsSentence (eq' (.app Q f) d) ↔
      B.HoldsSentence (eq' (.app Q (ProxySignature.lift f)) d) := by
  have E : ProxySignature.lift (eq' (.app Q f) d) = eq' (.app Q (ProxySignature.lift f)) d := by
    change eq' (ProxySignature.lift (.app Q f)) (ProxySignature.lift d) = _
    rw [lift_Q_app, lift_d]
  rw [← E]
  exact (ProxySignature.holds_lift _ _ _ .nil).symm

theorem predecessors (Sig : Signature) : Predecessors Sig := by
  intro C _ O M hvar he f hf
  let anchor := Classical.choice he
  let A := ProxySignature.expand O (fun _ => anchor)
  have Ma : A.IsModel := ProxySignature.expand_isModel O M (fun _ => anchor)
  let K := expandedControls O anchor
  let v : ∀ i, A.Dom A.W₀ (.var i) := fun i => Classical.choice ((O.holdsAx_varExistence_iff M).mp hvar i)
  let B := AuxSignature.expand A v
  have Mb : B.IsModel := AuxSignature.expand_isModel A Ma v
  let Kb := AuxSignature.keepControls A K v
  let bits := Family.colours B
  let P := Family.model B Kb bits
  have Mp : P.IsModel := Family.isModel B Kb bits Mb
  let Pc := AuxSignature.restrict P
  have Mc : Pc.IsModel := AuxSignature.restrict_isModel P Mp
  let F := ProxySignature.lift f
  have fail : ¬ A.HoldsSentence (.app F d) := by
    intro H
    apply hf
    change Intension.True _ (A.sem (𝟙 _) (.app F d) .nil) at H
    change Intension.True O.inner (O.sem (𝟙 _) (.app f d) .nil)
    rw [← sem_named_f_d O (fun _ => anchor) (𝟙 _) f]
    exact H
  have reject := Family.rejects_identity B Kb Mb (AuxSignature.lift F)
    (fun H => fail ((aux_test_failure A v F).1 H))
  refine ⟨_, _, ProxySignature.restrict Pc, ProxySignature.restrict_isModel Pc Mc, ?_, ?_⟩
  · apply ((ProxySignature.restrict Pc).holdsAx_varExistence_iff (ProxySignature.restrict_isModel Pc Mc)).mpr
    exact fun i => ⟨AuxSignature.variableName i⟩
  · exact fun H => reject ((strip_aux P F).1 ((strip_controls Pc f).1 H))

end
end Classicism.Meta.ProxyDiagonal
