import Classicism.StrongPossibility.ProbeDirectRows
import Classicism.StrongPossibility.ProxySeparation

/-! A colour is computed in the original old model, before adjoining any
probes. Every tagged tuple, including choices of different members of the
same private fibre, reads that colour. -/

namespace Classicism.Meta.ProxyDiagonal
open CategoryTheory Intensional Coalesced
noncomputable section

namespace Family
variable {Sig : Signature} {C : Type} [SmallCategory C] (O : Premodel Sig C) (K : Controls O)

def colours (a : Address O) : Bool := by
  classical
  exact decide (row O (O.sem (𝟙 _) d .nil) a.h a.tuple)

theorem colour_direct (a : Address O) :
    colours O a = true ↔ row O (O.sem (𝟙 _) d .nil) a.h a.tuple := by
  classical
  simp [colours]

variable (bits : Address O → Bool)
local notation "A" => model O K bits
local notation "F" => components O K bits

theorem copy_sem_row (t : Term Sig [] S) (a : Address O) {z : C} (j : a.z ⟶ z)
    (u : Six (O.Dom z .e)) :
    row A ((A).sem (𝟙 _) t .nil) (fromTestOld O K bits a j) u ↔
      row O (O.sem (𝟙 _) t .nil) (a.h ≫ j) u := by
  let Z := O.truncate a.h
  let T := transported O K a.h
  let L := leaf Z T (bits a)
  let G := PointedPair.components Z L
  let v := CoalescedSum.arr (baseArrows G) (x := ⟨false,z⟩) j
  refine (distinguished_row F (act O K bits) (DistinguishedDefinable.inclusion F)
    (ne O K) (DistinguishedDefinable.value F) (DistinguishedDefinable.transports F)
    t (some a) v u).trans ?_
  refine (distinguished_row G _ _ ⟨controlInd false 0⟩ _ (PointedPair.transports Z L _ _ (names Z T a.tuple.get (bits a)))
    t false j u).trans ?_
  have eqv := O.sem_truncate a.h (𝟙 a.z) t .nil
  rw [Category.comp_id] at eqv
  have mv := O.sem_push (𝟙 _) t .nil a.h
  simp only [Category.id_comp, Premodel.push, IEnv.map] at mv
  change row O ((O.truncate a.h).sem (𝟙 a.z) t .nil) j u ↔ _
  rw [eqv, mv]
  exact row_map O _ _ _ _

local notation "B" => model O K (colours O)
local notation "c" => rootTuple O K (colours O)
local notation "dB" => Premodel.sem (model O K (colours O)) (𝟙 _) d IEnv.nil

theorem read_colour (a : Address O) (u : Six ((B).Dom (testAt O K (colours O) a) .e))
    (h : tagged B (move B (entry O K (colours O) a) c) u) :
    hasBit B (move B (entry O K (colours O) a) c) ↔
      row B dB (entry O K (colours O) a ≫ oldExit O K (colours O) a)
        (move B (oldExit O K (colours O) a) u) := by
  rw [entry_controls] at h ⊢
  rw [tag_projects O K (colours O) a u h]
  change _ ↔ row B dB (entry O K (colours O) a ≫ intoOld O K (colours O) a (𝟙 a.z)) _
  rw [entry_then_old, copy_sem_row, Category.comp_id]
  exact (bit_at O K (colours O) a).trans (colour_direct O a)

theorem sound_tests {Y} (j : (B).W₀ ⟶ Y) (hj : (move B j c).isTest) :
    ∃ (V : _) (v : Y ⟶ V), (move B v (move B j c)).isOld ∧
      (∀ {U} (l : Y ⟶ U), (move B l (move B j c)).isOld → ∃ f : V ⟶ U, l = v ≫ f) ∧
      ∀ u, tagged B (move B j c) u →
        (hasBit B (move B j c) ↔ row B dB (j ≫ v) (move B v u)) := by
  refine only_test O K (colours O) (fun Y j =>
    ∃ (V : _) (v : Y ⟶ V), (move B v (move B j c)).isOld ∧
      (∀ {U} (l : Y ⟶ U), (move B l (move B j c)).isOld → ∃ f : V ⟶ U, l = v ≫ f) ∧
      ∀ u, tagged B (move B j c) u →
        (hasBit B (move B j c) ↔ row B dB (j ≫ v) (move B v u))) ?_ j hj
  intro a
  refine ⟨_, oldExit O K (colours O) a, ?_, ?_, read_colour O K a⟩
  · rw [entry_controls]
    exact exit_old O K _ a
  · rw [entry_controls]
    exact fun l h => any_old O K _ a l h

end Family
end
end Classicism.Meta.ProxyDiagonal
