import Classicism.StrongPossibility.TypedSignature
import Classicism.StrongPossibility.ProxyNamedControls
import Classicism.StrongPossibility.ProbeModel

/-! A temporary name for each metalogical type variable. These names are used
inside the probe. The theory of the resulting point can be taken in the old
signature by forgetting them. -/

namespace Classicism.Meta.AuxSignature

open CategoryTheory Intensional ProxyDiagonal

/-- One new symbol of type `var i` for each i. -/
def Names : Signature := ⟨Nat, Ty.var⟩

abbrev Extended (Sig : Signature) := TypedSignature.sum Sig Names

variable {Sig : Signature} {Γ : Ctx} {σ : Ty}

noncomputable abbrev lift (t : Term Sig Γ σ) : Term (Extended Sig) Γ σ :=
  TypedSignature.lift t

abbrev marker (i : Nat) : Term (Extended Sig) Γ (.var i) :=
  TypedSignature.fresh (Extra := Names) i

variable {C : Type} [SmallCategory C]

abbrev expand (A : Premodel Sig C) (v : ∀ i, A.Dom A.W₀ (.var i)) : Premodel (Extended Sig) C :=
  TypedSignature.expand (Extra := Names) A v

abbrev restrict (B : Premodel (Extended Sig) C) : Premodel Sig C :=
  TypedSignature.restrict B

theorem expand_isModel (A : Premodel Sig C) (M : A.IsModel) (v : ∀ i, A.Dom A.W₀ (.var i)) :
    (expand A v).IsModel := TypedSignature.expand_isModel (Extra := Names) A M v

theorem restrict_isModel (B : Premodel (Extended Sig) C) (M : B.IsModel) :
    (restrict B).IsModel := TypedSignature.restrict_isModel B M

theorem sem_marker (A : Premodel Sig C) (v : ∀ i, A.Dom A.W₀ (.var i))
    {W : C} (h : A.W₀ ⟶ W) (i : Nat) (g : IEnv (A.Dom W) Γ) :
    (expand A v).sem h (marker i) g = (A.inner (.var i)).map h (v i) := rfl

/-- Keep the six previously chosen controls, even when their denotations coincide. -/
def keepControls (A : Premodel Sig C) (K : Controls A) (v : ∀ i, A.Dom A.W₀ (.var i)) :
    Controls (expand A v) where
  name i := ⟨Sum.inl (K.name i).1, (K.name i).2⟩
  injective := by
    intro i j hij
    exact K.injective (Subtype.ext (Sum.inl.inj (congrArg Subtype.val hij)))
  anchor := K.anchor
  fixed := K.fixed

/-- The auxiliary language supplies a name of every variable type at a descriptor root. -/
def variableName (i : Nat) :
    {c : (Extended Sig).Const // (Extended Sig).typeOf c = Ty.var i} :=
  ⟨Sum.inr i, rfl⟩

set_option maxHeartbeats 1200000 in
theorem lift_Q : lift (Q (Sig := Sig)) = Q := rfl

set_option maxHeartbeats 1200000 in
theorem lift_rho : lift (rho (Sig := Sig)) = rho := rfl

theorem lift_d : lift (d (Sig := Sig)) = d := by
  change Term.app (lift Q) (lift rho) = _
  rw [lift_Q, lift_rho]
  rfl

theorem lift_Q_app (f : Term Sig [] Tester) : lift (.app Q f) = .app Q (lift f) := by
  change Term.app (lift Q) (lift f) = _
  rw [lift_Q]

theorem lift_f_d (f : Term Sig [] Tester) : lift (.app f d) = .app (lift f) d := by
  change Term.app (lift f) (lift d) = _
  rw [lift_d]

theorem lift_bad (f : Term Sig [] Tester) : lift (bad f) = bad (lift f) := by
  change Term.conj (Term.eq' (lift (.app Q f)) (lift d)) (Term.neg (Term.eq' (lift (.app f d)) Term.top)) = _
  rw [lift_Q_app, lift_d, lift_f_d]
  rfl

/-- This works for every descriptor, even if it contains a variable type internally. -/
theorem holds_bad_restrict (B : Premodel (Extended Sig) C) {W : C} (h : B.W₀ ⟶ W)
    (f : Term Sig [] Tester) :
    B.Holds h (bad (lift f)) .nil ↔ (restrict B).Holds h (bad f) .nil := by
  rw [← lift_bad]
  exact TypedSignature.holds_lift _ _ _ _

theorem sem_expand_Q_app (A : Premodel Sig C) (v : ∀ i, A.Dom A.W₀ (.var i))
    {W : C} (h : A.W₀ ⟶ W) (f : Term Sig [] Tester) :
    (expand A v).sem h (.app Q (lift f)) .nil = A.sem h (.app Q f) .nil := by
  simpa only [lift_Q_app] using TypedSignature.sem_expand_lift (Extra := Names) A v h (.app Q f) .nil

end Classicism.Meta.AuxSignature
