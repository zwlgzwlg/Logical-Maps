import Classicism.StrongPossibility.ProjectionCoherence
import Classicism.StrongPossibility.ProbeDirectRows
import Classicism.StrongPossibility.ProxySeparation

/-! Old-address coverage in the concrete two-level proxy family. -/

namespace Classicism.Meta.ProxyDiagonal.Family

open CategoryTheory Intensional Coalesced

noncomputable section

variable {Sig : Signature} {C : Type} [SmallCategory C]
variable (O : Premodel Sig C) (K : Controls O) (bits : Address O → Bool)

local notation "A" => model O K bits
local notation "F" => components O K bits
local notation "R" => baseArrows F

private theorem rowAtImage {Cat : Type} [SmallCategory Cat] (B : Premodel Sig Cat)
    {W V : Cat} (p : B.Dom W S) (k : W ⟶ V) (u : Six (B.Dom V .e)) :
    row B (B.incl S W p) k u ↔
      row B (B.incl S V ((B.inner S).map k p)) (𝟙 V) u := by
  rw [B.incl_map, row_map, Category.comp_id]

/-- Reading an upper-root relation at a copied old tuple gives exactly the
direct old reading, also after an arbitrary old continuation. -/
theorem duplicate_row (a : Address O) {z : C} (k : a.z ⟶ z)
    (p : (A).Dom (A).W₀ S) (u : Six (O.Dom z .e)) :
    row A ((A).incl S _ p) (entry O K bits a ≫ intoOld O K bits a k) u ↔
      row A ((A).incl S _ p) (direct O K bits (a.h ≫ k)) u := by
  refine (rowAtImage A p (entry O K bits a ≫ intoOld O K bits a k) u).trans
    (Iff.trans ?_ (rowAtImage A p (direct O K bits (a.h ≫ k)) u).symm)
  apply iff_of_eq
  apply congrArg (fun q : O.Dom z S => row O (O.incl S z q) (𝟙 z) u)
  refine (((A).inner S).map_comp_apply (entry O K bits a) (intoOld O K bits a k) p).trans ?_
  exact projection_coherence O K bits a k S p

/-- Classify only the final history. This covers both direct old addresses
and the old sectors of all proxies, including tuples first available there. -/
theorem old_origin {Y : CoalescedSum R} (w : (A).W₀ ⟶ Y)
    (H : (move A w (rootTuple O K bits)).isOld) (u : Six ((A).Dom Y .e)) :
    ∃ a : Address O, ∀ p : (A).Dom (A).W₀ S,
      row A ((A).incl S _ p) (direct O K bits a.h) a.tuple ↔
        row A ((A).incl S _ p) w u := by
  match Y, w with
  | .root, ⟨⟩ =>
    exact False.elim ((by decide : (2:Fin 6) ≠ 3) (K.injective H))
  | .of ⟨none,z⟩, h => exact ⟨⟨z,h,u⟩, fun _ => Iff.rfl⟩
  | .of ⟨some a,.root⟩, ⟨⟩ =>
    exact False.elim ((entry_test O K bits a).2.1 H)
  | .of ⟨some a,.of ⟨false,z⟩⟩, h =>
    refine ⟨⟨z,a.h ≫ h,u⟩, fun p => ?_⟩
    exact (duplicate_row O K bits a h p u).symm
  | .of ⟨some a,.of ⟨true,⟨⟩⟩⟩, ⟨⟩ =>
    have hp := (exit_private O K bits a).2.1
    rw [← entry_controls O K bits a, ← move_comp] at hp
    exact False.elim (hp H)

/-- The exact field type of Tests.cover at the source of the concrete family. -/
abbrev Covers (X : Intension (A).inner S (A).W₀) : Prop :=
  ∀ {Z : CoalescedSum R} (w : (A).W₀ ⟶ Z), (move A w (rootTuple O K bits)).isOld →
  ∀ {Y : CoalescedSum R} (k : Z ⟶ Y) (u : Six ((A).Dom Y .e)),
    ∃ (T V : CoalescedSum R) (j : (A).W₀ ⟶ T) (v : T ⟶ V) (t : Six ((A).Dom T .e)),
      (move A j (rootTuple O K bits)).isTest ∧ tagged A (move A j (rootTuple O K bits)) t ∧
      (move A v (move A j (rootTuple O K bits))).isOld ∧
      (∀ {D : CoalescedSum R} (l : T ⟶ D), (move A l (move A j (rootTuple O K bits))).isOld →
        ∃ f : V ⟶ D, l = v ≫ f) ∧
      ((∃ x, Size 7 (kernel A (move A j (rootTuple O K bits)) x)) ↔ row A X (w ≫ k) u) ∧
      (∀ p : (A).Dom (A).W₀ S, row A ((A).incl S _ p) (j ≫ v) (move A v t) ↔
                                row A ((A).incl S _ p) (w ≫ k) u)

/-- The cover field of the semantic Tests interface. The output target is any
admitted relation whose rows on the direct old component give the proxy bits. -/
theorem cover_of_programmed (X : Intension (A).inner S (A).W₀)
    (admitted : ∃ p : (A).Dom (A).W₀ S, (A).incl S _ p = X)
    (program : ∀ a : Address O, bits a = true ↔ row A X (direct O K bits a.h) a.tuple) :
    Covers O K bits X := by
  intro Z w hw Y k u
  obtain ⟨pX,rfl⟩ := admitted
  have old : (move A (w ≫ k) (rootTuple O K bits)).isOld := by
    rw [move_comp]
    exact old_moves A _ hw k
  obtain ⟨a,copy⟩ := old_origin O K bits (w ≫ k) old u
  refine ⟨_,_,entry O K bits a,oldExit O K bits a,chosen O K bits a,entry_test O K bits a,?_⟩
  rw [entry_controls O K bits a]
  refine ⟨chosen_tags O K bits a,exit_old O K bits a,fun l H => any_old O K bits a l H,
    (bit_at O K bits a).trans ((program a).trans (copy pX)),?_⟩
  intro p
  rw [tag_projects O K bits a _ (chosen_tags O K bits a)]
  refine Iff.trans ?_ (copy p)
  have same := duplicate_row O K bits a (𝟙 a.z) p a.tuple
  simpa only [Category.comp_id] using same

/-- Programming on the original component suffices for the native diagonal
term, since the direct route preserves its full intension. -/
theorem cover_d (M : O.IsModel)
    (program : ∀ a : Address O, bits a = true ↔ row O (O.sem (𝟙 _) d .nil) a.h a.tuple) :
    Covers O K bits ((A).sem (𝟙 _) d .nil) := by
  apply cover_of_programmed O K bits
  · exact Set.mem_range.mp (isModel O K bits M (𝟙 _) d .nil)
  · exact fun a => (program a).trans (direct_sem_row O K bits d a.h a.tuple).symm

end
end Classicism.Meta.ProxyDiagonal.Family
