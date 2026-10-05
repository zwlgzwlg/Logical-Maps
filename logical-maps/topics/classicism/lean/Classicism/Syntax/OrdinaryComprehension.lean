import Classicism.Syntax.Blocks
import Classicism.Syntax.Entailment

/-!
# Ordinary Comprehension

**Ordinary Comprehension** (Classicism, §2.3, p. 27): every formula `P` with distinguished
variables `ȳ` defines a coextensive relation, `∃X. ∀ȳ. X ȳ ↔ P`, for `X` fresh and the
other free variables of `P`, a block `z̄`, closed universally:

    ∀z̄. ∃X. ∀ȳ. X ȳ ↔ P

It is a theorem of `C` at every instance (`ordinaryComprehension_theorem`): the witness
is `λȳ. P`, and `(λȳ. P) ȳ` converts to `P` (`Conv.appBlock_lamBlock_vars`).
-/

namespace Classicism.Meta

variable {Sig : Signature}

namespace Sub

/-- Two lifts over a block compose to the lift of the composite. -/
theorem compRen_liftBlock_liftBlock : ∀ (σs : List Ty) {Γ Δ Θ : Ctx} (s : Sub Sig Δ Θ) (r : Ren Γ Δ),
    Sub.compRen (Sub.liftBlock σs s) (Ren.liftBlock σs r) = Sub.liftBlock σs (Sub.compRen s r)
  | [], _, _, _, _, _ => rfl
  | σ :: σs, _, _, _, s, r => by
    show Sub.compRen (Sub.liftBlock σs (Sub.lift s)) (Ren.liftBlock σs (Ren.lift r)) =
      Sub.liftBlock σs (Sub.lift (Sub.compRen s r))
    rw [compRen_liftBlock_liftBlock σs (Sub.lift s) (Ren.lift r), Sub.lift_compRen]

/-- The identity, lifted over a block, is the identity. -/
theorem liftBlock_id : ∀ (σs : List Ty) {Γ : Ctx}, Sub.liftBlock σs (Sub.id : Sub Sig Γ Γ) = Sub.id
  | [], _ => rfl
  | σ :: σs, _ => by
    show Sub.liftBlock σs (Sub.lift Sub.id (σ := σ)) = Sub.id
    rw [Sub.lift_id, liftBlock_id σs]

end Sub

namespace Term

/-- The instance of Ordinary Comprehension at the formula `P`, with distinguished
variables `ȳ` and the rest `z̄`: `∀z̄. ∃X. ∀ȳ. X ȳ ↔ P`. -/
def ordinaryComprehension (zs ys : List Ty) (P : Formula Sig (Ctx.block ys (Ctx.block zs []))) :
    Sentence Sig :=
  forallBlock zs (exists' (σ := Ty.rel (ys ⇒* RTy.t))
    (forallBlock ys (iff
      (appBlock ((Term.var .zero : Term Sig ((ys ⇒* RTy.t) :: Ctx.block zs []) (ys ⇒* RTy.t)).rename
        (Ren.wkBlock ys)) (Terms.vars ys _))
      (P.rename (Ren.liftBlock ys Ren.shift)))))

end Term

namespace AxiomSet

variable (Sig)

/-- **Ordinary Comprehension**: its instances at every formula of the signature's
language; at the pure signature, the map's principle. -/
def ordinaryComprehension : AxiomSet Sig := fun a => a.closedTypes = true ∧
  ∃ (zs ys : List Ty) (P : Formula Sig (Ctx.block ys (Ctx.block zs []))),
    a = Term.ordinaryComprehension zs ys P

end AxiomSet

/-- **Every instance of Ordinary Comprehension is a theorem of `C`**: `λȳ. P` is the
witness. -/
theorem ordinaryComprehension_theorem (zs ys : List Ty)
    (P : Formula Sig (Ctx.block ys (Ctx.block zs []))) :
    C.Theorem (Term.ordinaryComprehension zs ys P) := by
  apply Derivable.allIBlock zs
  apply Derivable.exIβ (Term.lamBlock ys P)
  rw [Term.instantiate, Term.subst_forallBlock]
  apply Derivable.allIBlock ys
  show Derivable _ _ (Term.iff
    ((Term.appBlock _ (Terms.vars ys _)).subst _) ((P.rename (Ren.liftBlock ys Ren.shift)).subst _))
  rw [Term.subst_appBlock, Terms.vars_subst_liftBlock, Term.subst_rename, Term.subst_rename,
    Sub.compRen_liftBlock_wkBlock, Sub.compRen_liftBlock_liftBlock, Sub.compRen_cons_shift,
    Sub.liftBlock_id, Term.subst_id]
  have e : Term.subst (Ren.compSub (Ren.wkBlock ys) (Sub.cons (Term.lamBlock ys P) Sub.id))
      (Term.var .zero : Term Sig ((ys ⇒* RTy.t) :: Ctx.block zs []) (ys ⇒* RTy.t)) =
      (Term.lamBlock ys P).rename (Ren.wkBlock ys) := rfl
  rw [e]
  have c := Conv.appBlock_lamBlock_vars ys P
  exact Derivable.iffI (Derivable.conv Derivable.hyp₀ c) (Derivable.conv Derivable.hyp₀ (Conv.symm c))

/-- `classicism-implies-ordinary-comprehension-r`: every instance is a theorem of `C`. -/
theorem AxiomSet.ordinaryComprehension_entails :
    AxiomSet.empty ⟹ AxiomSet.ordinaryComprehension Sig := by
  rintro a ⟨_, zs, ys, P, rfl⟩
  exact Theorem.ofC (ordinaryComprehension_theorem zs ys P)

end Classicism.Meta
