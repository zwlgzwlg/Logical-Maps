import Classicism.Coalesced.DistinguishedDefinable
import Classicism.StrongPossibility.ProbeFamily

/-!
# Agreement on the old component along every proxy

The upper root uses a single closed descriptor for each of its entities. The
direct component is the old premodel. A proxy component has its own root and
two exits, with old component the truncation at a specified old arrow.
-/

namespace Classicism.Meta.Coalesced.ProjectionCoherence

open CategoryTheory Classicism.Meta.Intensional

variable {Sig : Signature}

section Transport

variable {J : Type} {C : J → Type} [∀ j, SmallCategory (C j)]
variable (A : ∀ j, Premodel Sig (C j))

/-- At every old arrow the whole projected entity denotes its descriptor. -/
theorem descriptorAlong (σ : Ty) (x : (DistinguishedDefinable.action A).D σ)
    {j : J} {V : C j} (h : (A j).W₀ ⟶ V) :
    (A j).Incl σ V ((DistinguishedDefinable.action A).tr σ (k := j) h x) =
      (A j).sem h (DistinguishedDefinable.descriptor A σ x) .nil := by
  have tr := (DistinguishedDefinable.action A).tr_map σ h (dist A j) x
  change (DistinguishedDefinable.action A).tr σ (k := j) (𝟙 _ ≫ h) x = _ at tr
  rw [Category.id_comp] at tr
  rw [tr, (A j).Incl_map, ← DistinguishedDefinable.descriptor_at]
  simpa only [Category.id_comp, Premodel.push, IEnv.map] using
    ((A j).sem_push (𝟙 _) (DistinguishedDefinable.descriptor A σ x) .nil h).symm

variable (RA : RootAction (baseArrows A) A) (RI : RootIncl RA)
    (ne : Nonempty (RA.D .e)) (I : ∀ c : Sig.Const, RA.D (Sig.typeOf c))
local notation "B" => RA.coalescedSum RI ne I

/-- A named closed denotation at a second root has precisely its component
denotation on the entire continuation, with the component names in force. -/
theorem closedProjection (names : TransportsConstants RA I) {σ : Ty}
    (s : Term Sig [] σ) (y : RA.D σ)
    (root : (B).Incl σ (B).W₀ y = (B).sem (𝟙 _) s .nil)
    {j : J} {V : C j} (h : (A j).W₀ ⟶ V) :
    (A j).Incl σ V (RA.tr σ (k := j) h y) = (A j).sem h s .nil := by
  let a := CoalescedSum.arr (baseArrows A) (x := ⟨j,V⟩) h
  have e : (B).Incl σ _ (((B).inner σ).map a y) = (B).sem a s .nil := by
    refine ((B).Incl_map σ a y).trans ((congrArg (Outer.map (B).inner σ a) root).trans ?_)
    simpa only [Category.id_comp, Premodel.push, IEnv.map] using ((B).sem_push (𝟙 _) s .nil a).symm
  refine (RA.compO_Incl RI ne I σ _).symm.trans ?_
  refine (congrArg (RA.compO (k := j) σ) e).trans ?_
  refine (RA.sem_arr RI ne I h s .nil).trans ?_
  refine ((A j).rebase_sem_congr (funext fun c => tr_eq_map names c h) (𝟙 V) s .nil).trans ?_
  simpa only [Category.comp_id] using (A j).sem_truncate h (𝟙 V) s .nil

end Transport

end Classicism.Meta.Coalesced.ProjectionCoherence

namespace Classicism.Meta.ProxyDiagonal.Family

open CategoryTheory Classicism.Meta.Intensional Classicism.Meta.Coalesced
open Coalesced.ProjectionCoherence

noncomputable section

variable {Sig : Signature} {C : Type} [SmallCategory C]
variable (O : Premodel Sig C) (K : Controls O) (bits : Address O → Bool)

/-- The route through the proxy and the direct route have literally equal
old entities after every further old arrow, at every native type. -/
theorem projection_coherence (a : Address O) {U : C} (j : a.z ⟶ U)
    (σ : Ty) (x : (act O K bits).D σ) :
    (PointedPair.action (O.truncate a.h)
      (leaf (O.truncate a.h) (transported O K a.h) (bits a))
      (proj (O.truncate a.h) (transported O K a.h) a.tuple.get (bits a))
      (prj (Sig := Sig) (bits a))).tr σ (k := false) (V := U) j
        ((act O K bits).tr σ (dist (components O K bits) (some a)) x) =
    (act O K bits).tr σ (k := none) (V := U) (a.h ≫ j) x := by
  let A := components O K bits
  let Z := O.truncate a.h
  let T := transported O K a.h
  let L := leaf Z T (bits a)
  let B := PointedPair.components Z L
  let l := proj Z T a.tuple.get (bits a)
  let r := prj (Sig := Sig) (bits a)
  let N := names Z T a.tuple.get (bits a)
  let RA := PointedPair.action Z L l r
  let RI := PointedPair.incl Z L l r
  let I := PointedPair.value Z L l r N
  let ne' : Nonempty (ProxyInd (IndividualNames Sig) (bits a)) := ⟨controlInd false 0⟩
  let d := DistinguishedDefinable.descriptor A σ x
  let y := (act O K bits).tr σ (dist A (some a)) x
  have hd : (test O K bits a).Incl σ _ y = (test O K bits a).sem (𝟙 _) d .nil :=
    (DistinguishedDefinable.descriptor_at A σ x (some a)).symm
  have H := closedProjection B RA RI ne' I (PointedPair.transports Z L l r N)
    d y hd (j := false) (V := U) j
  apply O.Incl_injective σ U
  refine (congrFun (O.truncate_Incl a.h σ U) (RA.tr σ (k := false) (V := U) j y)).symm.trans ?_
  refine H.trans ((O.sem_truncate a.h j d .nil).trans ?_)
  exact (descriptorAlong A σ x (j := none) (V := U) (a.h ≫ j)).symm

end
end Classicism.Meta.ProxyDiagonal.Family
