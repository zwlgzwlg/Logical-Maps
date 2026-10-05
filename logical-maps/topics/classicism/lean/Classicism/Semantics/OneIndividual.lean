import Classicism.Semantics.FullModels

/-!
# One individual: the Axiom of Infinity at `e` fails

The map's argument `one-individual`: at a world with a single individual, the numeral
`Suc_e 𝟎_e` is a finite cardinality, and it holds of the universal property, so the Axiom of
Infinity at `e`, `¬∃Z. FiniteCardinality_e(Z) ∧ Z(λu. ⊤)`, fails there
(`not_holds_axiomOfInfinityE`); where every world has a single individual, so does Possible
Infinity, its possibility (`not_holds_possibleInfinityE`).

The numerals are closed terms, so their values are in every model's domain, and they do not
depend on the variables around them: the Axiom's quotation is `zeroE` and `sucE`, renamed into
their places (`axiomOfInfinityE_quoted_eq`, by `rfl`).
-/

namespace Classicism.Meta.Intensional

open CategoryTheory Term

/-- Properties of individuals, `e → t`. -/
abbrev τP : Ty := .rel (.arr .e .t)
/-- Cardinalities of individuals, `(e → t) → t`. -/
abbrev τC : Ty := .rel (.arr τP .t)

/-- `𝟎_e := λF. ∀u. ¬Fu`. -/
def zeroE : Term Signature.pure [] τC :=
  .lam (Term.forall' (Term.neg (Term.app (Term.var Var.zero.succ) (Term.var .zero))))

/-- `Suc_e Y := λF. ∃x. Fx ∧ Y(λu. Fu ∧ u ≠ x)`, with `Y` its one free variable. -/
def sucE : Term Signature.pure [τC] τC :=
  .lam (Term.exists' (Term.conj (Term.app (Term.var Var.zero.succ) (Term.var .zero))
    (Term.app (Term.var Var.zero.succ.succ) (Term.lam (Term.conj (Term.app (Term.var Var.zero.succ.succ) (Term.var .zero))
      (Term.neg (Term.eq' (Term.var .zero) (Term.var Var.zero.succ))))))))

/-- The Axiom of Infinity at `e`, with its numerals named. -/
theorem axiomOfInfinityE_quoted_eq : P.AxiomOfInfinityE.quoted =
    Term.neg (Term.exists' (σ := τC) (Term.conj
      (Term.forall' (σ := .rel (.arr τC .t)) (Term.imp
        (Term.conj (Term.app (Term.var .zero) (zeroE.rename Ren.ofEmpty))
          (Term.forall' (σ := τC) (Term.imp (Term.app (Term.var Var.zero.succ) (Term.var .zero))
            (Term.app (Term.var Var.zero.succ) (sucE.rename (Ren.lift Ren.ofEmpty))))))
        (Term.app (Term.var .zero) (Term.var Var.zero.succ))))
      (Term.app (Term.var .zero) (Term.lam Term.top)))) := rfl

namespace Premodel

variable {C : Type} [SmallCategory C] {B : Premodel Signature.pure C} (M : B.IsModel)
include M

/-- **The Axiom of Infinity at `e` fails at a world with one individual**: `Suc_e 𝟎_e` is a
finite cardinality holding of the universal property. -/
theorem not_holds_axiomOfInfinityE {W : C} (h : B.W₀ ⟶ W) (h1 : Subsingleton (B.Dom W .e)) :
    ¬ B.Holds h P.AxiomOfInfinityE.quoted .nil := by
  rw [axiomOfInfinityE_quoted_eq, B.holds_neg M, not_not, B.holds_exists M]
  obtain ⟨z0, hz0⟩ := M h zeroE .nil
  obtain ⟨s1, hs1⟩ := M h sucE (.cons z0 .nil)
  refine ⟨s1, (B.holds_conj M _ _ _ _).2 ⟨?_, ?_⟩⟩
  · -- `Suc 𝟎` is a finite cardinality: any `X` with `X 𝟎` and closed under `Suc` has `X (Suc 𝟎)`
    rw [B.holds_forall M]
    intro X
    rw [B.holds_imp M, B.holds_conj M, B.holds_forall M]
    rintro ⟨hX0, hstep⟩
    have hstep := (B.holds_imp M _ _ _ _).1 (hstep z0)
    have e1 : B.Incl τC W s1 =
        B.sem h (sucE.rename (Ren.lift Ren.ofEmpty)) (.cons z0 (.cons X (.cons s1 .nil))) := by
      rw [B.sem_rename]
      exact hs1.trans (congrArg _ (IEnv.ext fun _ v => by cases v <;> rfl))
    have e0 : B.Incl τC W z0 = B.sem h (zeroE.rename Ren.ofEmpty) (.cons X (.cons s1 .nil)) := by
      rw [B.sem_rename, IEnv.nil_eq (IEnv.ren _ _)]
      exact hz0
    have hX0' := (B.holds_app h _ (Term.var .zero) _ e0).1 hX0
    have hstep' := hstep ((B.holds_app h _ (Term.var Var.zero.succ) (Term.var .zero) (a' := z0) rfl).2 hX0')
    exact (B.holds_app h _ (Term.var .zero) (Term.var Var.zero.succ) (a' := s1) rfl).2
      ((B.holds_app h _ _ _ e1).1 hstep')
  · -- `Suc 𝟎` holds of `λu. ⊤`: the one individual is all there is
    obtain ⟨u1, hu1⟩ := M h (Term.lam Term.top : Term Signature.pure [τC] τP) (.cons s1 .nil)
    rw [B.holds_app h _ _ _ (a' := u1) hu1]
    show _ ∈ B.Incl τC W s1
    rw [hs1, sucE, mem_sem_lam, Category.comp_id, B.push_id]
    obtain ⟨x⟩ := B.nonempty_e W
    refine (B.holds_exists M _ _ _).2 ⟨x, (B.holds_conj M _ _ _ _).2 ⟨?_, ?_⟩⟩
    · rw [holds_app_var1]
      show _ ∈ B.Incl τP W u1
      rw [hu1, mem_sem_lam]
      exact B.holds_top M _ _
    · obtain ⟨v, hv⟩ := M h (Term.lam (Term.conj (Term.app (Term.var Var.zero.succ.succ) (Term.var .zero))
        (Term.neg (Term.eq' (Term.var .zero) (Term.var Var.zero.succ)))) : Term Signature.pure [.e, τP, τC] τP)
        (.cons x (.cons u1 (.cons z0 .nil)))
      rw [B.holds_app h _ _ _ (a' := v) hv]
      show _ ∈ B.Incl τC W z0
      rw [hz0, zeroE, mem_sem_lam, Category.comp_id]
      show B.Holds h _ _
      rw [B.holds_forall M]
      intro u
      rw [B.holds_neg M, holds_app_var1]
      show _ ∉ B.Incl τP W v
      rw [hv, mem_sem_lam, Category.comp_id, B.push_id]
      show ¬ B.Holds h _ _
      rw [B.holds_conj M, B.holds_neg M, holds_eq_var M]
      exact fun ⟨_, hne⟩ => hne (Subsingleton.elim _ _)

/-- **Possible Infinity at `e` fails where every world has one individual.** -/
theorem not_holds_possibleInfinityE {W : C} (h : B.W₀ ⟶ W)
    (h1 : ∀ V : C, Subsingleton (B.Dom V .e)) : ¬ B.Holds h P.PossibleInfinityE.quoted .nil := by
  show ¬ B.Holds h (dia P.AxiomOfInfinityE.quoted) .nil
  rw [B.holds_dia M]
  rintro ⟨V, k, hk⟩
  rw [IEnv.nil_eq (B.push k .nil)] at hk
  exact not_holds_axiomOfInfinityE M (h ≫ k) (h1 V) hk

end Premodel

end Classicism.Meta.Intensional
