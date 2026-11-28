import Classicism.StrongPossibility.ProbeFamily
import Classicism.StrongPossibility.ProxyRecovery
import Classicism.StrongPossibility.ProxyNamedControls

/-! Normal forms for arrows from the source and its test sites. The private
kernel at a test object is equality of its projections to the private leaf. -/

namespace Classicism.Meta.ProxyDiagonal.Family
open CategoryTheory CategoryTheory.Sigma Intensional Coalesced

noncomputable section
variable {Sig : Signature} {C : Type} [SmallCategory C]
variable (O : Premodel Sig C) (K : Controls O) (bits : Address O → Bool)

local notation "A" => model O K bits
local notation "F" => components O K bits
local notation "R" => baseArrows F

abbrev source : CoalescedSum R := .root
abbrev oldAt (z : C) : CoalescedSum R := .of ⟨none,z⟩
abbrev testAt (a : Address O) : CoalescedSum R := .of ⟨some a, .root⟩
abbrev target (a : Address O) (z : C) : CoalescedSum R := .of ⟨some a, .of ⟨false,z⟩⟩
abbrev terminal (a : Address O) : CoalescedSum R := .of ⟨some a, .of ⟨true,SingleObj.star Unit⟩⟩

abbrev direct {z : C} (h : O.W₀ ⟶ z) : source O K bits ⟶ oldAt O K bits z := h
abbrev entry (a : Address O) : source O K bits ⟶ testAt O K bits a := 𝟙 (F (some a)).W₀
abbrev innerR (a : Address O) := baseArrows (PointedPair.components (O.truncate a.h)
  (leaf (O.truncate a.h) (transported O K a.h) (bits a)))

abbrev oldExit (a : Address O) : testAt O K bits a ⟶ target O K bits a a.z :=
  CoalescedSum.inc R (k := some a) (CoalescedSum.arr (innerR O K bits a) (x := ⟨false,a.z⟩) (𝟙 a.z))
abbrev privateExit (a : Address O) : testAt O K bits a ⟶ terminal O K bits a :=
  CoalescedSum.inc R (k := some a)
    (CoalescedSum.arr (innerR O K bits a) (x := ⟨true,SingleObj.star Unit⟩) (𝟙 (SingleObj.star Unit)))

abbrev rootTuple : Six ((A).Dom (A).W₀ .e) := Six.ofFin K.name
abbrev oldTuple (z : C) (h : O.W₀ ⟶ z) : Six (O.Dom z .e) :=
  Six.ofFin (fun _ => (O.inner .e).map h K.anchor)

theorem direct_controls {z : C} (h : O.W₀ ⟶ z) :
    move A (direct O K bits h) (rootTuple O K bits) = oldTuple O K z h := by
  have e : ∀ i, ((A).inner .e).map (direct O K bits h) (K.name i) = (O.inner .e).map h K.anchor :=
    fun i => congrArg ((O.inner .e).map h) (K.fixed i)
  exact congrArg Six.ofFin (funext e)

theorem entry_controls (a : Address O) :
    move A (entry O K bits a) (rootTuple O K bits) = proxyControls := by
  have e (i : Fin 6) : ((A).inner .e).map (entry O K bits a) (K.name i) = proxyControls.get i := by
    let n := K.name i
    let OO := O.truncate a.h
    let KK := transported O K a.h
    let src := names OO KK a.tuple.get (bits a)
    let N := test O K bits a
    change (N.inner .e).map (𝟙 _) (oldNameAt N n) = _
    rw [Functor.map_id_apply]
    have castVal : ∀ τ (h : Sig.typeOf n.1 = τ),
        castD (D := N.Dom N.W₀) h (N.I n.1) =
          PointedPair.valueAt _ _ _ _ src n.1 τ h := by
      intro τ h
      cases h
      rfl
    exact (castVal _ n.2).trans (slot_control OO KK (bits a) i)
  exact congrArg Six.ofFin (funext e)

theorem old_projection (a : Address O) (x : (A).Dom (testAt O K bits a) .e) :
    ((A).inner .e).map (oldExit O K bits a) x =
    oldImage a.tuple.get ((O.inner .e).map a.h K.anchor) (oldNameAt (O.truncate a.h)) x :=
  (O.inner .e).map_id_apply _ _

theorem private_projection (a : Address O) (x : (A).Dom (testAt O K bits a) .e) :
    ((A).inner .e).map (privateExit O K bits a) x = privateImage x := rfl

theorem entry_test (a : Address O) : (move A (entry O K bits a) (rootTuple O K bits)).isTest := by
  rw [entry_controls]
  refine ⟨fun h => h rfl, ?_, ?_⟩
  · intro h
    cases h
  · intro h
    cases h

theorem direct_old {z : C} (h : O.W₀ ⟶ z) : (move A (direct O K bits h) (rootTuple O K bits)).isOld := by
  rw [direct_controls]
  rfl

theorem exit_old (a : Address O) : (move A (oldExit O K bits a) proxyControls).isOld := by
  change ((A).inner .e).map _ _ = ((A).inner .e).map _ _
  rw [old_projection, old_projection]
  rfl

theorem exit_private (a : Address O) : (move A (privateExit O K bits a) proxyControls).isPriv := by
  refine ⟨fun h => h rfl, ?_, rfl⟩
  intro h
  cases h

/-- Eliminate an arrow whose source is already in a component. -/
theorem from_component {ι : Type} {C' : ι → Type} [∀ i, SmallCategory (C' i)]
    (R' : RootArrows C') {i : ι} {X : C' i}
    (P : ∀ Y : CoalescedSum R', (.of ⟨i,X⟩ ⟶ Y) → Prop)
    (comp : ∀ (Y : C' i) (k : X ⟶ Y), P _ (CoalescedSum.inc R' k)) :
    ∀ (Y : CoalescedSum R') (k : .of ⟨i,X⟩ ⟶ Y), P Y k
  | .root, k => nomatch k
  | .of _, SigmaHom.mk k => comp _ k

abbrev compOld (a : Address O) {z v : C} (j : z ⟶ v) :
    target O K bits a z ⟶ target O K bits a v :=
  CoalescedSum.inc R (k := some a) (CoalescedSum.inc (innerR O K bits a) (k := false) j)

abbrev intoOld (a : Address O) {z : C} (j : a.z ⟶ z) : testAt O K bits a ⟶ target O K bits a z :=
  CoalescedSum.inc R (k := some a) (CoalescedSum.arr (innerR O K bits a) (x := ⟨false,z⟩) j)

theorem old_factor_eq (a : Address O) {z : C} (j : a.z ⟶ z) :
    oldExit O K bits a ≫ compOld O K bits a j = intoOld O K bits a j := by
  exact congrArg (intoOld O K bits a) (Category.id_comp j)

theorem any_old (a : Address O) {Y : CoalescedSum R} (k : testAt O K bits a ⟶ Y)
    (h : (move A k proxyControls).isOld) :
    ∃ l : target O K bits a a.z ⟶ Y, k = oldExit O K bits a ≫ l := by
  revert h
  apply from_component R (i := some a) (X := CoalescedSum.root)
    (fun Y k => (move A k proxyControls).isOld → ∃ l, k = oldExit O K bits a ≫ l) _ Y k
  intro Z j
  match Z, j with
  | .root, ⟨⟩ => intro h; cases h
  | .of ⟨false,z⟩, j =>
    intro _
    exact ⟨compOld O K bits a j, (old_factor_eq O K bits a j).symm⟩
  | .of ⟨true,⟨⟩⟩, j => intro h; cases j; cases h

theorem any_private (a : Address O) {Y : CoalescedSum R} (k : testAt O K bits a ⟶ Y)
    (h : (move A k proxyControls).isPriv) :
    ∃ l : terminal O K bits a ⟶ Y, k = privateExit O K bits a ≫ l := by
  revert h
  apply from_component R (i := some a) (X := CoalescedSum.root)
    (fun Y k => (move A k proxyControls).isPriv → ∃ l, k = privateExit O K bits a ≫ l) _ Y k
  intro Z j
  match Z, j with
  | .root, ⟨⟩ => intro h; exact False.elim (by cases h.2.2)
  | .of ⟨false,z⟩, j =>
    intro h
    apply False.elim
    apply h.2.1
    rfl
  | .of ⟨true,⟨⟩⟩, j =>
    intro _
    cases j
    exact ⟨𝟙 _, (Category.comp_id _).symm⟩

theorem test_kernel (a : Address O) (x y : (A).Dom (testAt O K bits a) .e) :
    kernel A (W := testAt O K bits a) proxyControls x y ↔ privateImage x = privateImage y :=
  kernel_of_private A (privateExit O K bits a) proxyControls (exit_private O K bits a)
    (fun k h => any_private O K bits a k h) x y

theorem bit_at (a : Address O) :
    (∃ x, Size 7 (kernel A (W := testAt O K bits a) proxyControls x)) ↔ bits a = true := by
  have k (x : (A).Dom (testAt O K bits a) .e) :
      kernel A (W := testAt O K bits a) proxyControls x =
        fun y => privateImage x = privateImage y := funext fun y => propext (test_kernel O K bits a x y)
  simp only [k]
  exact marker_iff

abbrev chosen (a : Address O) : Six ((A).Dom (testAt O K bits a) .e) :=
  Six.ofFin (fun i => picked i)

theorem tag_at (a : Address O) (n : Nat) (x : (A).Dom (testAt O K bits a) .e) :
    Size n (kernel A (W := testAt O K bits a) proxyControls x) ↔ x.1.width = n := by
  have k : kernel A (W := testAt O K bits a) proxyControls x =
        fun y => privateImage x = privateImage y := funext fun y => propext (test_kernel O K bits a x y)
  rw [k]
  exact tag_iff_width _ _

theorem chosen_tags (a : Address O) : tagged A (W := testAt O K bits a) proxyControls (chosen O K bits a) := by
  unfold tagged
  exact ⟨(tag_at O K bits a _ _).2 rfl,(tag_at O K bits a _ _).2 rfl,
    (tag_at O K bits a _ _).2 rfl,(tag_at O K bits a _ _).2 rfl,
    (tag_at O K bits a _ _).2 rfl,(tag_at O K bits a _ _).2 rfl⟩

theorem tag_projects (a : Address O) (v : Six ((A).Dom (testAt O K bits a) .e))
    (H : tagged A (W := testAt O K bits a) proxyControls v) :
    move A (oldExit O K bits a) v = a.tuple := by
  have each (i : Fin 6) (x : (A).Dom (testAt O K bits a) .e)
      (hi : Size (i.val+1) (kernel A (W := testAt O K bits a) proxyControls x)) :
      ((A).inner .e).map (oldExit O K bits a) x = a.tuple.get i := by
    rw [old_projection]
    apply projected_tag _ _ _ _ i
    exact (tag_iff_width _ _).mpr ((tag_at O K bits a _ _).mp hi)
  have e := congrArg Six.ofFin (show (fun i => ((A).inner .e).map (oldExit O K bits a) (v.get i)) =
      (fun i => a.tuple.get i) from funext (fun i => by
        fin_cases i
        · exact each 0 _ H.1
        · exact each 1 _ H.2.1
        · exact each 2 _ H.2.2.1
        · exact each 3 _ H.2.2.2.1
        · exact each 4 _ H.2.2.2.2.1
        · exact each 5 _ H.2.2.2.2.2))
  exact e

abbrev fromTestOld (a : Address O) {z : C} (j : a.z ⟶ z) :
    source O K bits ⟶ target O K bits a z :=
  CoalescedSum.arr R (x := ⟨some a, .of ⟨false,z⟩⟩)
    (CoalescedSum.arr (innerR O K bits a) (x := ⟨false,z⟩) j)

abbrev fromTestPrivate (a : Address O) : source O K bits ⟶ terminal O K bits a :=
  CoalescedSum.arr R (x := ⟨some a, .of ⟨true,SingleObj.star Unit⟩⟩)
    (CoalescedSum.arr (innerR O K bits a) (x := ⟨true,SingleObj.star Unit⟩) (𝟙 _))

/-- The five possible shapes of any arrow out of the probe source. -/
theorem cases_from_root (P : ∀ Y : CoalescedSum R, (source O K bits ⟶ Y) → Prop)
    (idP : P _ (𝟙 _))
    (directP : ∀ z (h : O.W₀ ⟶ z), P _ (direct O K bits h))
    (entryP : ∀ a, P _ (entry O K bits a))
    (oldP : ∀ a z (j : a.z ⟶ z), P _ (fromTestOld O K bits a j))
    (leafP : ∀ a, P _ (fromTestPrivate O K bits a)) :
    ∀ Y k, P Y k
  | .root, ⟨⟩ => idP
  | .of ⟨none,z⟩, h => directP z h
  | .of ⟨some a,.root⟩, ⟨⟩ => entryP a
  | .of ⟨some a,.of ⟨false,z⟩⟩, j => oldP a z j
  | .of ⟨some a,.of ⟨true,⟨⟩⟩⟩, ⟨⟩ => leafP a

theorem entry_then_old (a : Address O) {z : C} (j : a.z ⟶ z) :
    entry O K bits a ≫ intoOld O K bits a j = fromTestOld O K bits a j := by
  let v := CoalescedSum.arr (innerR O K bits a) (x := ⟨false,z⟩) j
  exact congrArg (CoalescedSum.arr R (x := ⟨some a,_⟩)) (Category.id_comp v)

theorem entry_then_private (a : Address O) :
    entry O K bits a ≫ privateExit O K bits a = fromTestPrivate O K bits a := by
  let v := CoalescedSum.arr (innerR O K bits a) (x := ⟨true,SingleObj.star Unit⟩) (𝟙 _)
  exact congrArg (CoalescedSum.arr R (x := ⟨some a,_⟩)) (Category.id_comp v)

theorem dup_controls (a : Address O) {z : C} (j : a.z ⟶ z) :
    move A (fromTestOld O K bits a j) (rootTuple O K bits) =
      Six.ofFin (fun _ => (O.inner .e).map j ((O.inner .e).map a.h K.anchor)) := by
  refine (congrArg (fun k => move A k (rootTuple O K bits)) (entry_then_old O K bits a j).symm).trans ?_
  refine (move_comp A _ _ _).trans ?_
  exact congrArg (move A (intoOld O K bits a j)) (entry_controls O K bits a)

theorem leaf_controls (a : Address O) :
    move A (fromTestPrivate O K bits a) (rootTuple O K bits) =
      proxyControls.map (privateImage (N := IndividualNames Sig) (b := bits a)) := by
  refine (congrArg (fun k => move A k (rootTuple O K bits)) (entry_then_private O K bits a).symm).trans ?_
  refine (move_comp A _ _ _).trans ?_
  exact congrArg (move A (privateExit O K bits a)) (entry_controls O K bits a)

theorem source_start : (rootTuple O K bits).isStart :=
  fun h => (by decide : (0 : Fin 6) ≠ 1) (K.injective h)

theorem isolated : ∀ {V : CoalescedSum R} (j : source O K bits ⟶ V),
    (move A j (rootTuple O K bits)).isStart →
    ∃ e : V = source O K bits, j ≫ eqToHom e = 𝟙 _ := by
  apply cases_from_root O K bits
  · exact fun _ => ⟨rfl, Category.comp_id _⟩
  · intro z h H
    rw [direct_controls] at H
    exact (H rfl).elim
  · intro a H
    exact ((entry_test O K bits a).1 H).elim
  · intro a z j H
    rw [dup_controls] at H
    exact (H rfl).elim
  · intro a H
    rw [leaf_controls] at H
    exact (H rfl).elim

theorem only_test (P : ∀ Y : CoalescedSum R, (source O K bits ⟶ Y) → Prop)
    (atTest : ∀ a, P _ (entry O K bits a)) : ∀ {Y} (j : source O K bits ⟶ Y),
    (move A j (rootTuple O K bits)).isTest → P Y j := by
  apply cases_from_root O K bits
  · intro H
    exact (H.1 ((move_id A _).symm ▸ source_start O K bits)).elim
  · intro z h H
    exact (H.2.1 (direct_old O K bits h)).elim
  · exact fun a _ => atTest a
  · intro a z j H
    rw [dup_controls] at H
    exact (H.2.1 rfl).elim
  · intro a H
    rw [leaf_controls] at H
    exact (H.2.2 rfl).elim

end
end Classicism.Meta.ProxyDiagonal.Family
