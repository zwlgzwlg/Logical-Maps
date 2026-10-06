import Classicism.Semantics.FullModels
import Classicism.Semantics.Counting
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Numerals: the Axioms of Infinity in a model

The finite cardinalities of a type `σ` are built from `𝟎_σ := λF. ∀u. ¬Fu` and
`Suc_σ Y := λF. ∃x. Fx ∧ Y(λu. Fu ∧ u ≠ x)` (`zeroT`, `sucT`), and the Axiom of Infinity at `σ`
is `¬∃Z. FiniteCardinality_σ(Z) ∧ Z(λu. ⊤)` (`axInf`, the quotation of the map's Axioms at `e`
and `t` by `rfl`). In a model, at a world `W`:

- `Suc_σ Y` holds of `F` iff `Y` holds of `F` less one of its instances (`mem_suc`), and `𝟎_σ`
  of `F` iff `F` has none (`mem_zero`); so the `n`-th numeral holds of exactly the properties
  with `n` instances (`mem_numeral`), and is a finite cardinality (`numeral_finCard`).
- **With finitely many entities of type `σ`** at `W`, the numeral counting them holds of the
  universal property, so the Axiom of Infinity fails there (`not_holds_axInf_of_finite`).
- **In an extensionally full model with infinitely many**, the property of holding only of
  properties with finitely many instances is in the domain; `𝟎` has it and `Suc` keeps it,
  so every finite cardinality has it, and none holds of the universal property: the Axiom
  holds (`holds_axInf_of_infinite`).
-/

namespace Classicism.Meta.Intensional

open CategoryTheory

/-- Properties of entities of type `σ`. -/
abbrev tP (σ : Ty) : Ty := .rel (.arr σ .t)
/-- Cardinalities of entities of type `σ`. -/
abbrev tC (σ : Ty) : Ty := .rel (.arr (tP σ) .t)

/-- `𝟎_σ := λF. ∀u. ¬Fu`. -/
def zeroT (σ : Ty) : Term Signature.pure [] (tC σ) :=
  .lam (Term.forall' (Term.neg (Term.app (Term.var Var.zero.succ) (Term.var .zero))))

/-- `λu. Fu ∧ u ≠ x`, with `x` and `F` free. -/
def minusT (σ : Ty) : Term Signature.pure [σ, tP σ] (tP σ) :=
  .lam (Term.conj (Term.app (Term.var Var.zero.succ.succ) (Term.var .zero))
    (Term.neg (Term.eq' (Term.var .zero) (Term.var Var.zero.succ))))

/-- `Suc_σ Y := λF. ∃x. Fx ∧ Y(λu. Fu ∧ u ≠ x)`, with `Y` free. -/
def sucT (σ : Ty) : Term Signature.pure [tC σ] (tC σ) :=
  .lam (Term.exists' (Term.conj (Term.app (Term.var Var.zero.succ) (Term.var .zero))
    (Term.app (Term.var Var.zero.succ.succ) ((minusT σ).rename (Ren.lift (Ren.lift Ren.ofEmpty))))))

/-- The Axiom of Infinity at `σ`, with its numerals named. -/
def axInf (σ : Ty) : Formula Signature.pure [] :=
  Term.neg (Term.exists' (σ := tC σ) (Term.conj
    (Term.forall' (σ := .rel (.arr (tC σ) .t)) (Term.imp
      (Term.conj (Term.app (Term.var .zero) ((zeroT σ).rename Ren.ofEmpty))
        (Term.forall' (σ := tC σ) (Term.imp (Term.app (Term.var Var.zero.succ) (Term.var .zero))
          (Term.app (Term.var Var.zero.succ) ((sucT σ).rename (Ren.lift Ren.ofEmpty))))))
      (Term.app (Term.var .zero) (Term.var Var.zero.succ))))
    (Term.app (Term.var .zero) (Term.lam Term.top))))

theorem axiomOfInfinityE_eq : P.AxiomOfInfinityE.quoted = axInf .e := rfl
theorem axiomOfInfinityT_eq : P.AxiomOfInfinityT.quoted = axInf (.rel .t) := rfl
theorem possibleInfinityE_eq : P.PossibleInfinityE.quoted = Term.dia (axInf .e) := rfl
theorem possibleInfinityT_eq : P.PossibleInfinityT.quoted = Term.dia (axInf (.rel .t)) := rfl

namespace Premodel

variable {C : Type} [SmallCategory C] {B : Premodel Signature.pure C} (M : B.IsModel)

/-- The extension of a property at the world. -/
def pext {W : C} {σ : Ty} (P : B.Dom W (tP σ)) : Set (B.Dom W σ) :=
  {u | (⟨W, (u, PUnit.unit), 𝟙 W⟩ : Tuple B.inner (.arr σ .t) W) ∈ B.incl _ W P}

/-- Whether a cardinality holds of a property, at the world. -/
def holdsOf {W : C} {σ : Ty} (Z : B.Dom W (tC σ)) (P : B.Dom W (tP σ)) : Prop :=
  (⟨W, (P, PUnit.unit), 𝟙 W⟩ : Tuple B.inner (.arr (tP σ) .t) W) ∈ B.incl _ W Z

include M

/-- `F` less `x`, the value of `minusT`. -/
noncomputable def minus {W : C} (h : B.W₀ ⟶ W) {σ : Ty} (P : B.Dom W (tP σ)) (x : B.Dom W σ) :
    B.Dom W (tP σ) :=
  Classical.choose (M h (minusT σ) (.cons x (.cons P .nil)))

theorem minus_spec {W : C} (h : B.W₀ ⟶ W) {σ : Ty} (P : B.Dom W (tP σ)) (x : B.Dom W σ) :
    B.Incl _ W (minus M h P x) = B.sem h (minusT σ) (.cons x (.cons P .nil)) :=
  Classical.choose_spec (M h (minusT σ) (.cons x (.cons P .nil)))

theorem pext_minus {W : C} (h : B.W₀ ⟶ W) {σ : Ty} (P : B.Dom W (tP σ)) (x : B.Dom W σ) :
    pext (minus M h P x) = pext P \ {x} := by
  ext u
  show _ ∈ B.Incl (tP σ) W _ ↔ _
  rw [minus_spec, minusT, mem_sem_lam, Category.comp_id, B.push_id]
  show B.Holds h _ _ ↔ _
  rw [B.holds_conj M, B.holds_neg M, holds_eq_var M, holds_app_var1]
  rfl

/-- `𝟎_σ` holds of exactly the properties with no instances. -/
theorem holdsOf_zero {W : C} (h : B.W₀ ⟶ W) {σ : Ty} (z : B.Dom W (tC σ))
    (hz : B.Incl _ W z = B.sem h (zeroT σ) .nil) (P : B.Dom W (tP σ)) :
    holdsOf z P ↔ pext P = ∅ := by
  show _ ∈ B.Incl (tC σ) W z ↔ _
  rw [hz, zeroT, mem_sem_lam, Category.comp_id]
  show B.Holds h _ _ ↔ _
  rw [B.holds_forall M, Set.eq_empty_iff_forall_notMem]
  refine forall_congr' fun u => ?_
  rw [B.holds_neg M, holds_app_var1]
  rfl

/-- `Suc_σ Y` holds of `F` iff `Y` holds of `F` less one of its instances. -/
theorem holdsOf_suc {W : C} (h : B.W₀ ⟶ W) {σ : Ty} (Y s : B.Dom W (tC σ))
    (hs : B.Incl _ W s = B.sem h (sucT σ) (.cons Y .nil)) (P : B.Dom W (tP σ)) :
    holdsOf s P ↔ ∃ x ∈ pext P, holdsOf Y (minus M h P x) := by
  show _ ∈ B.Incl (tC σ) W s ↔ _
  rw [hs, sucT, mem_sem_lam, Category.comp_id, B.push_id]
  show B.Holds h _ _ ↔ _
  rw [B.holds_exists M]
  refine exists_congr fun x => ?_
  rw [B.holds_conj M, holds_app_var1]
  refine and_congr Iff.rfl ?_
  rw [B.holds_app h _ _ _ (a' := minus M h P x) (by
    rw [minus_spec, B.sem_rename]
    exact congrArg _ (IEnv.ext fun _ v => by cases v with
      | zero => rfl
      | succ v => cases v with
        | zero => rfl
        | succ v => exact nomatch v))]
  rfl

/-- The numerals' values at the world: `𝟎`, then `Suc` of the last. -/
noncomputable def numeral {W : C} (h : B.W₀ ⟶ W) (σ : Ty) : ℕ → B.Dom W (tC σ)
  | 0 => Classical.choose (M h (zeroT σ) .nil)
  | n + 1 => Classical.choose (M h (sucT σ) (.cons (numeral h σ n) .nil))

theorem numeral_zero_spec {W : C} (h : B.W₀ ⟶ W) (σ : Ty) :
    B.Incl _ W (numeral M h σ 0) = B.sem h (zeroT σ) .nil :=
  Classical.choose_spec (M h (zeroT σ) .nil)

theorem numeral_succ_spec {W : C} (h : B.W₀ ⟶ W) (σ : Ty) (n : ℕ) :
    B.Incl _ W (numeral M h σ (n + 1)) = B.sem h (sucT σ) (.cons (numeral M h σ n) .nil) :=
  Classical.choose_spec (M h (sucT σ) (.cons (numeral M h σ n) .nil))

/-- **The `n`-th numeral holds of exactly the properties with `n` instances.** -/
theorem holdsOf_numeral {W : C} (h : B.W₀ ⟶ W) (σ : Ty) :
    ∀ (n : ℕ) (P : B.Dom W (tP σ)), holdsOf (numeral M h σ n) P ↔ (pext P).encard = n
  | 0, P => by
    rw [holdsOf_zero M h _ (numeral_zero_spec M h σ), Nat.cast_zero, Set.encard_eq_zero]
  | n + 1, P => by
    rw [holdsOf_suc M h _ _ (numeral_succ_spec M h σ n)]
    constructor
    · rintro ⟨x, hx, hY⟩
      rw [holdsOf_numeral h σ n, pext_minus] at hY
      rw [← Set.encard_sdiff_singleton_add_one hx, hY]
      rfl
    · intro hP
      obtain ⟨x, hx⟩ : (pext P).Nonempty := Set.nonempty_of_encard_ne_zero (by rw [hP]; simp)
      refine ⟨x, hx, ?_⟩
      rw [holdsOf_numeral h σ n, pext_minus]
      have h2 : (pext P \ {x}).encard + 1 = (n : ℕ∞) + 1 := by
        rw [Set.encard_sdiff_singleton_add_one hx, hP]
        norm_cast
      exact WithTop.add_right_cancel ENat.one_ne_top h2

/-- The universal property `λu. ⊤` has every entity as an instance. -/
theorem pext_top {W : C} (h : B.W₀ ⟶ W) {σ : Ty} {Γ : Ctx} (g : IEnv (B.Dom W) Γ) (u : B.Dom W (tP σ))
    (hu : B.Incl _ W u = B.sem h (Term.lam (σ := σ) Term.top) g) : pext u = Set.univ := by
  ext x
  show _ ∈ B.Incl (tP σ) W u ↔ _
  rw [hu, mem_sem_lam]
  exact iff_of_true (B.holds_top M _ _) trivial

/-- **With finitely many entities of type `σ` at a world, the Axiom of Infinity fails there**: the
numeral counting them is a finite cardinality holding of the universal property. -/
theorem not_holds_axInf_of_finite {W : C} (h : B.W₀ ⟶ W) (σ : Ty) [Finite (B.Dom W σ)] :
    ¬ B.Holds h (axInf σ) .nil := by
  rw [axInf, B.holds_neg M, not_not, B.holds_exists M]
  refine ⟨numeral M h σ (Nat.card (B.Dom W σ)), (B.holds_conj M _ _ _ _).2 ⟨?_, ?_⟩⟩
  · rw [B.holds_forall M]
    intro X
    rw [B.holds_imp M, B.holds_conj M, B.holds_forall M]
    rintro ⟨hX0, hstep⟩
    have e0 : B.Incl _ W (numeral M h σ 0) = B.sem h ((zeroT σ).rename Ren.ofEmpty)
        (.cons X (.cons (numeral M h σ (Nat.card (B.Dom W σ))) .nil)) := by
      rw [B.sem_rename, IEnv.nil_eq (IEnv.ren _ _)]
      exact numeral_zero_spec M h σ
    have h0 := (B.holds_app h _ (Term.var .zero) _ e0).1 hX0
    have key : ∀ n, (⟨W, (numeral M h σ n, PUnit.unit), 𝟙 W⟩ : Tuple B.inner (.arr (tC σ) .t) W) ∈
        B.sem h (Term.var .zero) (.cons X (.cons (numeral M h σ (Nat.card (B.Dom W σ))) .nil)) := by
      intro n
      induction n with
      | zero => exact h0
      | succ n ih =>
        have hs := (B.holds_imp M _ _ _ _).1 (hstep (numeral M h σ n))
          ((B.holds_app h _ (Term.var Var.zero.succ) (Term.var .zero) (a' := numeral M h σ n) rfl).2 ih)
        have e1 : B.Incl _ W (numeral M h σ (n + 1)) = B.sem h ((sucT σ).rename (Ren.lift Ren.ofEmpty))
            (.cons (numeral M h σ n) (.cons X (.cons (numeral M h σ (Nat.card (B.Dom W σ))) .nil))) := by
          rw [B.sem_rename]
          exact (numeral_succ_spec M h σ n).trans (congrArg _ (IEnv.ext fun _ v => by cases v <;> rfl))
        exact (B.holds_app h _ _ _ e1).1 hs
    exact (B.holds_app h _ (Term.var .zero) (Term.var Var.zero.succ)
      (a' := numeral M h σ (Nat.card (B.Dom W σ))) rfl).2 (key _)
  · obtain ⟨u, hu⟩ := M h (Term.lam Term.top : Term Signature.pure [tC σ] (tP σ))
      (.cons (numeral M h σ (Nat.card (B.Dom W σ))) .nil)
    rw [B.holds_app h _ _ _ (a' := u) hu]
    show holdsOf (numeral M h σ (Nat.card (B.Dom W σ))) u
    rw [holdsOf_numeral M h σ _ u, pext_top M h _ u hu, Set.encard_univ, ENat.card_eq_coe_natCard _]

/-- **The Axiom of Infinity holds at a world with infinitely many entities of type `σ`** where
the property of holding only of properties with finitely many instances is in the domain: `𝟎`
has it, `Suc` keeps it, and no cardinality with it holds of the universal property. -/
theorem holds_axInf_of_finiteCards {W : C} (h : B.W₀ ⟶ W) (σ : Ty) [Infinite (B.Dom W σ)]
    (hX : ∃ X : B.Dom W (.rel (.arr (tC σ) .t)),
      (B.incl _ W X).ext' B.inner = {a | ∀ P, holdsOf a.1 P → (pext P).Finite}) :
    B.Holds h (axInf σ) .nil := by
  rw [axInf, B.holds_neg M, B.holds_exists M]
  rintro ⟨Z, hZ⟩
  rw [B.holds_conj M] at hZ
  obtain ⟨hFC, hZtop⟩ := hZ
  obtain ⟨X, hX⟩ := hX
  rw [B.holds_forall M] at hFC
  have hXZ := (B.holds_imp M _ _ _ _).1 (hFC X) ?_
  · rw [B.holds_app h _ (Term.var .zero) (Term.var Var.zero.succ) (a' := Z) rfl] at hXZ
    have hZX : (Z, PUnit.unit) ∈ (B.incl _ W X).ext' B.inner := hXZ
    rw [hX] at hZX
    obtain ⟨u, hu⟩ := M h (Term.lam Term.top : Term Signature.pure [tC σ] (tP σ)) (.cons Z .nil)
    rw [B.holds_app h _ _ _ (a' := u) hu] at hZtop
    have := hZX u hZtop
    rw [pext_top M h _ u hu] at this
    exact Set.infinite_univ this
  · rw [B.holds_conj M, B.holds_forall M]
    obtain ⟨z0, hz0⟩ := M h (zeroT σ) .nil
    refine ⟨?_, fun Y => ?_⟩
    · rw [B.holds_app h _ _ _ (a' := z0) (by rw [B.sem_rename, IEnv.nil_eq (IEnv.ren _ _)]; exact hz0)]
      show (z0, PUnit.unit) ∈ (B.incl _ W X).ext' B.inner
      rw [hX]
      intro P hP
      rw [(holdsOf_zero M h z0 hz0 P).1 hP]
      exact Set.finite_empty
    · rw [B.holds_imp M]
      intro hY
      rw [B.holds_app h _ (Term.var Var.zero.succ) (Term.var .zero) (a' := Y) rfl] at hY
      obtain ⟨s, hs⟩ := M h (sucT σ) (.cons Y .nil)
      rw [B.holds_app h _ _ _ (a' := s)
        (by rw [B.sem_rename]; exact hs.trans (congrArg _ (IEnv.ext fun _ v => by cases v <;> rfl)))]
      show (s, PUnit.unit) ∈ (B.incl _ W X).ext' B.inner
      have hY' : (Y, PUnit.unit) ∈ (B.incl _ W X).ext' B.inner := hY
      rw [hX] at hY' ⊢
      intro P hP
      obtain ⟨x, -, hm⟩ := (holdsOf_suc M h Y s hs P).1 hP
      have := hY' _ hm
      rw [pext_minus] at this
      exact (this.insert x).subset fun y hy => by
        by_cases e : y = x
        · exact Or.inl e
        · exact Or.inr ⟨hy, e⟩

/-- **In an extensionally full model with infinitely many entities of type `σ` at a world, the
Axiom of Infinity holds there**: the property of holding only of properties with finitely many
instances is in the domain, `𝟎` has it, `Suc` keeps it, and no cardinality with it holds of
the universal property. -/
theorem holds_axInf_of_infinite (hE : B.ExtFull) {W : C} (h : B.W₀ ⟶ W) (σ : Ty)
    [Infinite (B.Dom W σ)] : B.Holds h (axInf σ) .nil :=
  holds_axInf_of_finiteCards M h σ (hE (.arr (tC σ) .t) W _)


/-- **Possible Infinity at `σ` fails where every world has finitely many entities of type `σ`.** -/
theorem not_holds_dia_axInf_of_finite {W : C} (h : B.W₀ ⟶ W) (σ : Ty)
    (hfin : ∀ {V : C} (_ : W ⟶ V), Finite (B.Dom V σ)) :
    ¬ B.Holds h (Term.dia (axInf σ)) .nil := by
  rw [B.holds_dia M]
  rintro ⟨V, k, hk⟩
  have := hfin k
  exact not_holds_axInf_of_finite M (h ≫ k) σ hk

/-- The Infinity schema at `σ` holds at a world with infinitely many entities of type `σ`. -/
theorem holds_count_of_infinite {W : C} (h : B.W₀ ⟶ W) (σ : Ty) [Infinite (B.Dom W σ)] (n : ℕ) :
    B.Holds h (Term.existsBlock (List.replicate n σ)
      (Term.distinct n (Terms.vars (List.replicate n σ) []))) .nil :=
  (holds_count M h σ n).2 ⟨fun i => Infinite.natEmbedding _ i.val,
    fun _ _ e => Fin.ext ((Infinite.natEmbedding _).injective e)⟩

end Premodel

end Classicism.Meta.Intensional
