import Classicism.Coalesced.StonePowerClosed
import Classicism.Syntax.Normalize

/-! The revised smallness formula bounds the cardinality of its actual
extension by the strong-limit cut in a canonical fan. -/

namespace Classicism.Meta.Coalesced.StoneFan.PowerClosed

open CategoryTheory Classicism.Meta.Intensional Ordinals
open scoped Cardinal

noncomputable section

set_option maxRecDepth 25000
set_option maxHeartbeats 9000000
local instance nativeTyStoneSmall (α : Type) : _root_.Classicism.Ty α := ⟨()⟩

variable {Sig : Signature} {K : Type} [SmallCategory K] (B : Premodel Sig K)
  (M : B.IsModel) {W : K} (h : B.W₀ ⟶ W)

private def rename₁ {Γ : Ctx} {σ : Ty} (x : Var Γ σ) : Ren [σ] Γ
  | _, .zero => x

abbrev at₁ {Γ : Ctx} {σ : Ty} (p : Formula Sig [σ]) (x : Var Γ σ) :=
  p.rename (rename₁ x)

theorem holds_at₁ {Γ : Ctx} {σ : Ty} (p : Formula Sig [σ]) (g : IEnv (B.Dom W) Γ) (x : Var Γ σ) :
    B.Holds h (at₁ p x) g ↔ B.Holds h p (.cons (g.get x) .nil) := by
  unfold at₁ Premodel.Holds
  rw [B.sem_rename]
  rfl

abbrev saTerm {Sig : Signature} (η σ : Ty) : Formula Sig [.rel (unary σ), .rel (unary η)] :=
  unaryBody (unaryBody (Term.ofPure (Classicism.StoneMP.SmallAbove.term σ η)))

include M in
theorem holds_smallAbove_iff {η σ : Ty} (full : CurrentFull (W := W) B)
    (H : B.Dom W (.rel (unary η))) (X : B.Dom W (.rel (unary σ))) :
    B.Holds h (saTerm η σ) (.cons X (.cons H .nil)) ↔
      ¬ ∃ Y : B.Dom W (.rel (unary σ)), trace₁ B Y ⊆ trace₁ B X ∧
        #(trace₁ B H) < #(trace₁ B Y) ∧ B.Holds h (pcTerm σ) (.cons Y .nil) := by
  have eq : saTerm (Sig := Sig) η σ = Term.neg (Term.exists' (Term.conj
      (subPair .zero (.succ .zero)) (Term.conj (at₂ (smallerTerm η σ) (.succ (.succ .zero)) .zero)
        (at₁ (pcTerm σ) .zero)))) := rfl
  rw [eq, B.holds_neg M, B.holds_exists M]
  simp only [B.holds_conj M, holds_subPair B M h, holds_at₂, holds_at₁, IEnv.get,
    holds_smaller B M h full]

abbrev smallTerm {Sig : Signature} (σ : Ty) : Formula Sig [.rel (unary σ)] :=
  unaryBody (Term.ofPure (Classicism.StoneMP.Small.term σ))

abbrev ordPredicate {Sig : Signature} : Term Sig [] (.rel (unary (.rel (carrier .e)))) :=
  .lam (ordinalFormula .e)

private def saInst (σ : Ty) : Sub Sig [.rel (unary σ), .rel (unary (.rel (carrier .e)))] [.rel (unary σ)]
  | _, .zero => .var .zero
  | _, .succ .zero => ordPredicate.close

theorem small_conversion (σ : Ty) :
    smallTerm (Sig := Sig) σ ≡ (saTerm (.rel (carrier .e)) σ).subst (saInst σ) := by
  exact Conv.of_nf 1 _ _ rfl


abbrev ordinalEntity := value B M h ordPredicate .nil

theorem ordinal_row :
    trace₁ B (ordinalEntity B M h) = {a | B.Holds h (ordinalFormula .e) (.cons a .nil)} := by
  ext a
  change (⟨W, (a, PUnit.unit), 𝟙 W⟩ : Tuple B.inner (unary (.rel (carrier .e))) W) ∈
    B.Incl _ W (value B M h (.lam (ordinalFormula .e)) .nil) ↔ _
  rw [incl_value, B.mem_sem_lam, Category.comp_id, B.push_id]
  rfl

private theorem posSmall {σ : Ty} (X : B.Dom W (.rel (unary σ))) :
    B.Holds h (smallTerm σ) (.cons X .nil) ↔
      B.Holds h (saTerm (.rel (carrier .e)) σ) (.cons X (.cons (ordinalEntity B M h) .nil)) := by
  unfold Premodel.Holds
  rw [B.sem_conv M (small_conversion σ), B.sem_subst M]
  have eq : B.subEnv M h (saInst σ) (.cons X .nil) = .cons X (.cons (ordinalEntity B M h) .nil) := by
    apply IEnv.ext
    intro τ v
    apply B.Incl_injective
    rw [B.Incl_subEnv_get]
    cases v with
    | zero => rfl
    | succ v =>
      cases v with
      | zero =>
        change B.sem h ordPredicate.close (.cons X .nil) = B.Incl _ _ (ordinalEntity B M h)
        rw [B.sem_close, incl_value]
      | succ v => nomatch v
  rw [eq]

/-- A large represented carrier contains a represented power-closed subcarrier
strictly above the actual ordinals, and thus fails revised smallness. -/
theorem small_cardinal_lt {σ : Ty} (full : CurrentFull (W := W) B) (X : B.Dom W (.rel (unary σ)))
    (μ : Cardinal) (cut : Cardinal.IsStrongLimit μ)
    (bound : #(trace₁ B (ordinalEntity B M h)) < μ)
    (small : B.Holds h (smallTerm σ) (.cons X .nil)) :
    #(trace₁ B X) < μ := by
  by_contra! large
  have enough : #μ.out ≤ #(trace₁ B X) := by simpa using large
  obtain ⟨f⟩ := (Cardinal.le_def _ _).mp enough
  let j : μ.out → B.Dom W σ := fun t => (f t).1
  have inj : Function.Injective j := Subtype.val_injective.comp f.injective
  obtain ⟨Y, hY⟩ := unary_surjective B full σ (Set.range j)
  have size : #(trace₁ B Y) = μ := by rw [hY, Cardinal.mk_range_eq j inj, Cardinal.mk_out]
  apply (holds_smallAbove_iff B M h full _ _).1 ((posSmall B M h X).1 small)
  refine ⟨Y, ?_, size.symm ▸ bound, powerClosed_of_cut B M h full Y (size.symm ▸ cut)⟩
  rw [hY]
  rintro _ ⟨t,rfl⟩
  exact (f t).2

#print axioms small_cardinal_lt

end
end Classicism.Meta.Coalesced.StoneFan.PowerClosed
