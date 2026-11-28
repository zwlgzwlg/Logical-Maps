import Classicism.Coalesced.StonePowerClosed

/-! Every current order satisfying the native CBA formula on a full-current
point yields a Mathlib Boolean algebra with exactly that order. -/

namespace Classicism.Meta.Coalesced.StoneFan.PowerClosed

open CategoryTheory Classicism.Meta.Intensional Ordinals
open _root_.Classicism.StoneMP

noncomputable section
local instance nativeTyStoneBooleanAlgebra (α : Type) : _root_.Classicism.Ty α := ⟨()⟩

private theorem pair_sub {α : Type} {P : Set α} (a b : P) :
    ∀ u : α, (u = a.1 ∨ u = b.1) → P u := by
  rintro _ (rfl | rfl)
  · exact a.2
  · exact b.2

theorem algebra_of_cba {α : Type} {P : Set α} {R : α → α → Prop} (valid : CBA P R) :
    ∃ A : BooleanAlgebra P, ∀ x y : P, A.le x y ↔ R x.1 y.1 := by
  classical
  obtain ⟨order, sups, infs, dist, o, i, ends, comps⟩ := valid
  let join (x y : P) := Classical.choose (sups _ (pair_sub x y))
  let meet (x y : P) := Classical.choose (infs _ (pair_sub x y))
  have hj (x y : P) : Joins P R x.1 y.1 (join x y) := Classical.choose_spec (sups _ (pair_sub x y))
  have hm (x y : P) : Meets P R x.1 y.1 (meet x y) := Classical.choose_spec (infs _ (pair_sub x y))
  let sup (x y : P) : P := ⟨join x y, (hj x y).1⟩
  let inf (x y : P) : P := ⟨meet x y, (hm x y).1⟩
  have su_unique {S : α → Prop} {a b : α} (h : Supremum P R S a) (k : Supremum P R S b) :
      a = b := order.2.2.1 a b (h.2.2 b k.1 k.2.1) (k.2.2 a h.1 h.2.1)
  have in_unique {S : α → Prop} {a b : α} (h : Infimum P R S a) (k : Infimum P R S b) :
      a = b := order.2.2.1 a b (k.2.2 a h.1 h.2.1) (h.2.2 b k.1 k.2.1)
  let : Lattice P := {
    le := fun x y => R x.1 y.1
    le_refl := fun x => order.2.1 x.1 x.2
    le_trans := fun _ _ _ => order.2.2.2 _ _ _
    le_antisymm := fun _ _ h k => Subtype.ext (order.2.2.1 _ _ h k)
    sup := sup
    le_sup_left := fun x y => (hj x y).2.1 _ (Or.inl rfl)
    le_sup_right := fun x y => (hj x y).2.1 _ (Or.inr rfl)
    sup_le := fun x y z hx hy => (hj x y).2.2 _ z.2 (fun a h => h.elim (fun e => e ▸ hx) (fun e => e ▸ hy))
    inf := inf
    inf_le_left := fun x y => (hm x y).2.1 _ (Or.inl rfl)
    inf_le_right := fun x y => (hm x y).2.1 _ (Or.inr rfl)
    le_inf := fun z x y hx hy => (hm x y).2.2 _ z.2 (fun a h => h.elim (fun e => e ▸ hx) (fun e => e ▸ hy)) }
  let : DistribLattice P := DistribLattice.ofInfSupLe fun x y z => le_of_eq (Subtype.ext (su_unique
    (dist _ _ _ _ _ _ _ x.2 y.2 z.2 (hj y z) (hm x (sup y z)) (hm x y) (hm x z)) (hj (inf x y) (inf x z))))
  let : BoundedOrder P := {
    bot := ⟨o,ends.1⟩
    top := ⟨i,ends.2.1⟩
    bot_le := fun x => (ends.2.2 x.1 x.2).1
    le_top := fun x => (ends.2.2 x.1 x.2).2 }
  let : ComplementedLattice P := ⟨fun x => by
    obtain ⟨y, hy, hmeet, hjoin⟩ := comps x.1 x.2
    exact ⟨⟨y,hy⟩, ⟨disjoint_iff.mpr (Subtype.ext (in_unique (hm x ⟨y,hy⟩) hmeet)),
      codisjoint_iff.mpr (Subtype.ext (su_unique (hj x ⟨y,hy⟩) hjoin))⟩⟩⟩
  exact ⟨DistribLattice.booleanAlgebraOfComplemented P, fun _ _ => Iff.rfl⟩

variable {Sig : Signature} {K : Type} [SmallCategory K] (B : Premodel Sig K)
  (M : B.IsModel) {W : K} (h : B.W₀ ⟶ W)

abbrev cbaTerm {Sig : Signature} (σ : Ty) : Formula Sig [.rel (binary σ), .rel (unary σ)] :=
  unaryBody (unaryBody (Term.ofPure (CBA.term σ)))

include M

theorem cba_from_holds {σ : Ty} (full : CurrentFull (W := W) B)
    (P : B.Dom W (.rel (unary σ))) (R : B.Dom W (.rel (binary σ)))
    (valid : B.Holds h (cbaTerm σ) (.cons R (.cons P .nil))) : CBA (trace₁ B P) (row₂ B R) := by
  dsimp only [cbaTerm, CBA.term, Term.ofPure_lam, unaryBody] at valid
  simp only [Term.ofPure_app, Term.ofPure_var, Term.ofPure_lam, Term.ofPure_and, Term.ofPure_not,
    Term.ofPure_or, Term.ofPure_all, Term.ofPure_ex, Term.ofPure_eq, B.holds_conj M, B.holds_disj M, B.holds_neg M, ← imp_iff_not_or,
    B.holds_forall M, B.holds_exists M, Premodel.holds_eq_var M,
    Premodel.holds_app_var1, Premodel.holds_app_var2, IEnv.get] at valid
  obtain ⟨order, sups, infs, dist, ends⟩ := valid
  refine ⟨order, ?_, ?_, dist, ends⟩
  · intro S sub
    obtain ⟨Q, eq⟩ := unary_surjective B full σ S
    subst S
    exact sups Q sub
  · intro S sub
    obtain ⟨Q, eq⟩ := unary_surjective B full σ S
    subst S
    exact infs Q sub

#print axioms cba_from_holds
#print axioms algebra_of_cba

end
end Classicism.Meta.Coalesced.StoneFan.PowerClosed
