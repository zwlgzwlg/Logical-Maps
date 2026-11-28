import Classicism.StrongPossibility.ProbeGeometry

/-! Read a closed six-place relation at any distinguished entrance. The tuple
may contain individuals first available at a later object. -/

namespace Classicism.Meta.ProxyDiagonal
open CategoryTheory Intensional Coalesced
noncomputable section

/-- Transport along a distinguished entrance preserves each row of a closed term. -/
theorem distinguished_row {Sig : Signature} {ι : Type} {C : ι → Type} [∀ k, SmallCategory (C k)]
    (B : ∀ k, Premodel Sig (C k)) (ra : RootAction (baseArrows B) B) (ri : RootIncl ra)
    (ne : Nonempty (ra.D Ty.e)) (val : ∀ c : Sig.Const, ra.D (Sig.typeOf c))
    (hv : TransportsConstants ra val)
    (t : Term Sig [] S) (i : ι) {Z : C i} (h : (B i).W₀ ⟶ Z) (u : Six ((B i).Dom Z .e)) :
    let A := ra.coalescedSum ri ne val
    row A (A.sem (𝟙 _) t .nil) (CoalescedSum.arr (baseArrows B) (x := ⟨i,Z⟩) h) u ↔
      row (B i) ((B i).sem (𝟙 _) t .nil) h u := by
  let A := ra.coalescedSum ri ne val
  let e := CoalescedSum.arr (baseArrows B) (x := ⟨i,(B i).W₀⟩) (dist B i)
  have hp := A.sem_push (𝟙 _) t .nil e
  simp only [Category.id_comp, Premodel.push, IEnv.map] at hp
  have trans : ra.transport (k := i) (dist B i) (A.sem (𝟙 _) t .nil) = (B i).sem (𝟙 _) t .nil :=
    (congrArg (ra.compI (k := i)) hp.symm).trans
      ((ra.sem_arr ri ne val (k := i) (dist B i) t .nil).trans
        ((B i).rebase_sem_congr (funext fun c => hv c i) (𝟙 _) t .nil))
  have H := ra.mem_transport (k := i) (dist B i) (A.sem (𝟙 _) t .nil)
    (⟨Z,sixArgs (B i) u,h⟩ : Tuple (B i).inner S (B i).W₀)
  rw [trans] at H
  change row (B i) ((B i).sem (𝟙 _) t .nil) h u ↔ row A (A.sem (𝟙 _) t .nil)
    (CoalescedSum.arr (baseArrows B) (x := ⟨i,Z⟩) (𝟙 (B i).W₀ ≫ h)) u at H
  simpa only [Category.id_comp] using H.symm

namespace Family
variable {Sig : Signature} {C : Type} [SmallCategory C]
variable (O : Premodel Sig C) (K : Controls O) (bits : Address O → Bool)
local notation "A" => model O K bits
local notation "F" => components O K bits

theorem direct_sem_row (t : Term Sig [] S) {Z : C} (h : O.W₀ ⟶ Z) (u : Six (O.Dom Z .e)) :
    row A ((A).sem (𝟙 _) t .nil) (direct O K bits h) u ↔ row O (O.sem (𝟙 _) t .nil) h u :=
  distinguished_row F (act O K bits) (DistinguishedDefinable.inclusion F) (ne O K)
    (DistinguishedDefinable.value F) (DistinguishedDefinable.transports F) t none h u

end Family
end
end Classicism.Meta.ProxyDiagonal
