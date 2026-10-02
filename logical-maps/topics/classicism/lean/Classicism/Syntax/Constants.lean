import Classicism.Syntax.Term
import Mathlib.Data.Set.Finite.Basic

/-!
# The constants of a term

`Term.consts`, the set of nonlogical constants occurring in a term, and its finiteness.
A model condition that is checked term by term needs only the constants the term
mentions; this is what lets an ideally full premodel over any signature be a model, with
no assumption that all its constants are pinned down by one finite set.
-/

namespace Classicism.Meta

variable {Sig : Signature}

namespace Term

/-- The nonlogical constants occurring in a term. -/
def consts : ∀ {Γ : Ctx} {σ : Ty}, Term Sig Γ σ → Set Sig.Const
  | _, _, .var _ => ∅
  | _, _, .const c => {c}
  | _, _, .app f a => f.consts ∪ a.consts
  | _, _, .lam b => b.consts
  | _, _, .and | _, _, .or | _, _, .not | _, _, .all _ | _, _, .ex _ | _, _, .eq _ => ∅
  | _, _, .constR _ | _, _, .negR _ | _, _, .andR _ | _, _, .orR _ | _, _, .coextR _
  | _, _, .boxR _ | _, _, .inclR _ => ∅

theorem consts_finite : ∀ {Γ : Ctx} {σ : Ty} (t : Term Sig Γ σ), t.consts.Finite
  | _, _, .var _ => Set.finite_empty
  | _, _, .const _ => Set.finite_singleton _
  | _, _, .app f a => (consts_finite f).union (consts_finite a)
  | _, _, .lam b => consts_finite b
  | _, _, .and | _, _, .or | _, _, .not | _, _, .all _ | _, _, .ex _ | _, _, .eq _ => Set.finite_empty
  | _, _, .constR _ | _, _, .negR _ | _, _, .andR _ | _, _, .orR _ | _, _, .coextR _
  | _, _, .boxR _ | _, _, .inclR _ => Set.finite_empty

theorem consts_app_left {Γ : Ctx} {σ : Ty} {ρ : RTy} (f : Term Sig Γ (σ ⇒ ρ)) (a : Term Sig Γ σ) :
    f.consts ⊆ (Term.app f a).consts := Set.subset_union_left

theorem consts_app_right {Γ : Ctx} {σ : Ty} {ρ : RTy} (f : Term Sig Γ (σ ⇒ ρ)) (a : Term Sig Γ σ) :
    a.consts ⊆ (Term.app f a).consts := Set.subset_union_right

theorem consts_lam {Γ : Ctx} {σ : Ty} {ρ : RTy} (b : Term Sig (σ :: Γ) ρ) :
    (Term.lam b).consts = b.consts := rfl

/-- A term with no constants: the purity of `Term.pure`, as a set. -/
theorem consts_eq_empty_of_pure : ∀ {Γ : Ctx} {σ : Ty} (t : Term Sig Γ σ), t.pure = true → t.consts = ∅
  | _, _, .var _, _ => rfl
  | _, _, .const _, h => by simp [Term.pure] at h
  | _, _, .app f a, h => by
    simp only [Term.pure, Bool.and_eq_true] at h
    show f.consts ∪ a.consts = ∅
    rw [consts_eq_empty_of_pure f h.1, consts_eq_empty_of_pure a h.2, Set.empty_union]
  | _, _, .lam b, h => consts_eq_empty_of_pure b h
  | _, _, .and, _ | _, _, .or, _ | _, _, .not, _ | _, _, .all _, _ | _, _, .ex _, _
  | _, _, .eq _, _ | _, _, .constR _, _ | _, _, .negR _, _ | _, _, .andR _, _ | _, _, .orR _, _
  | _, _, .coextR _, _ | _, _, .boxR _, _ | _, _, .inclR _, _ => rfl

end Term

end Classicism.Meta
