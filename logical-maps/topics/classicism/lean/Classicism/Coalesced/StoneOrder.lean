import Classicism.Coalesced.StoneCoordinates

/-! The modal entailment order on native propositions is inclusion of their
intensions. Every native relational intension at the Stone root is ordered by
its current row and its labelled component intensions independently. -/

namespace Classicism.Meta.Coalesced.StoneFan

open CategoryTheory CategoryTheory.Sigma Classicism.Meta.Intensional

/-- In any native intensional model, necessary implication is inclusion of the two
propositional intensions at the specified arrow and assignment. -/
theorem box_imp_iff_subset {Sig : Signature} {C : Type} [SmallCategory C]
    (B : Premodel Sig C) (M : B.IsModel) {Γ : Ctx} {W : C} (h : B.W₀ ⟶ W)
    (g : IEnv (B.Dom W) Γ) (p q : Formula Sig Γ) :
    B.Holds h (Term.box (Term.imp p q)) g ↔ B.sem h p g ⊆ B.sem h q g := by
  rw [B.holds_box M]
  constructor
  · rintro H ⟨V, ⟨⟩, j⟩ hp
    apply (B.mem_sem_iff h g q j).2
    exact (B.holds_imp M _ _ p q).1 (H j) ((B.mem_sem_iff h g p j).1 hp)
  · intro H V j
    apply (B.holds_imp M _ _ p q).2
    intro hp
    exact (B.mem_sem_iff h g q j).1 (H ((B.mem_sem_iff h g p j).2 hp))

variable {Sig : Signature} {ι : Type} {C : ι → Type} [∀ k, SmallCategory (C k)]
  (A : ∀ k, Premodel Sig (C k)) (L : ι → Type) (leaf : ι) [TopologicalSpace (L leaf)]

/-- Native inclusion at the root is exactly pointwise inclusion of the current row
and all component profile intensions. -/
theorem incl_iff_coordinates {ρ : RTy} (a b : (action A L leaf).D (.rel ρ)) :
    (model A L leaf).incl ρ (CoalescedSum.base (arrows A L)) a ⊆ (model A L leaf).incl ρ (CoalescedSum.base (arrows A L)) b ↔
      row A L leaf a ⊆ row A L leaf b ∧
        ∀ k x, (A k).incl ρ _ (profile A L leaf a k x) ⊆
          (A k).incl ρ _ (profile A L leaf b k x) := by
  let ae := atom A L .e
  let av := fun i => atom A L (.var i)
  let sl := sel A L leaf
  have hrep (c : (action A L leaf).D (.rel ρ)) :
      tuples A L (row A L leaf c) (profile A L leaf c) = c.1 :=
    congrArg Subtype.val (glue_profile A L leaf c)
  have hn : (model A L leaf).incl ρ (CoalescedSum.base (arrows A L)) a ⊆ (model A L leaf).incl ρ (CoalescedSum.base (arrows A L)) b ↔ a.1 ⊆ b.1 := by
    constructor
    · intro h q hq
      have t := @h (ofRT ae av sl q)
      change (toRT ae av sl (ofRT ae av sl q) ∈ a.1 →
        toRT ae av sl (ofRT ae av sl q) ∈ b.1) at t
      rw [toRT_ofRT] at t
      exact t hq
    · intro h q
      exact @h (toRT ae av sl q)
  rw [hn, ← hrep a, ← hrep b]
  constructor
  · intro H
    refine ⟨fun z hz => @H (Sum.inl (PUnit.unit, z)) hz, ?_⟩
    rintro k x ⟨U, args', j⟩ hy
    exact @H (.inr ⟨k, U, args', x, j⟩) hy
  · rintro ⟨hrow, hprofile⟩ (⟨⟨⟩, z⟩ | ⟨k, U, args', x, j⟩)
    · exact @hrow z
    · exact fun hz => hprofile k x (a := ⟨U, args', j⟩) hz

/-- The root's modal entailment comparison on two actual proposition variables,
expressed in the deep language, is the product order on their coordinates. -/
theorem entailment_iff_coordinates (M : ∀ k, (A k).IsModel)
    (a b : (action A L leaf).D (.rel .t)) :
    (model A L leaf).Holds (𝟙 (CoalescedSum.base (arrows A L)))
      (Term.box (Term.imp (.var .zero) (.var (.succ .zero)))) (.cons a (.cons b .nil)) ↔
      row A L leaf a ⊆ row A L leaf b ∧
        ∀ k x, (A k).incl .t _ (profile A L leaf a k x) ⊆
          (A k).incl .t _ (profile A L leaf b k x) := by
  exact (box_imp_iff_subset _ (isModel A L leaf M) _ _ _ _).trans (incl_iff_coordinates A L leaf a b)

#print axioms entailment_iff_coordinates

end Classicism.Meta.Coalesced.StoneFan
