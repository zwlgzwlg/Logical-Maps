import Classicism.Syntax.Entailment

/-!
# Closed types are inhabited, and `⊤_ρ ≠ ⊥_ρ`

Every closed type has an inhabitant `C` can use: a closed term at a relational type, `⊤_ρ`,
and at `e` the witness of Existence. So a universal over a closed type whose body does not
mention its variable gives the body (`Derivable.of_forall_weaken`). Hence `⊤_ρ ≠ ⊥_ρ` is a
theorem of `C` at every closed relational type (`C.topR_ne_botR`): at `t` it is `⊤ ≠ ⊥`,
and at `σ → ρ`, an identity `λz. ⊤_ρ = λz. ⊥_ρ`, applied to an inhabitant of `σ`, would
give `⊤_ρ = ⊥_ρ`. At a type with a type variable among its argument types there may be no
inhabitant, and `C` does not prove it.
-/

namespace Classicism.Meta

variable {Sig : Signature}

/-- `⊤_t` converts to `⊤`. -/
theorem Conv.topR_t {Γ : Ctx} : (Term.topR RTy.t : Term Sig Γ _) ≡ Term.top :=
  Conv.trans (Conv.app_congr (Conv.delta rfl) (Conv.refl _)) (Conv.beta _ _)

/-- `⊥_t` converts to `⊥`. -/
theorem Conv.botR_t {Γ : Ctx} : (Term.botR RTy.t : Term Sig Γ _) ≡ Term.bot :=
  Conv.trans (Conv.app_congr (Conv.delta rfl) (Conv.refl _)) (Conv.beta _ _)

/-- `⊤_{σ→ρ}` converts to `λz. ⊤_ρ`. -/
theorem Conv.topR_arr {Γ : Ctx} (σ : Ty) (ρ : RTy) :
    (Term.topR (σ ⇒ ρ) : Term Sig Γ _) ≡ Term.lam (Term.topR ρ) :=
  Conv.trans (Conv.app_congr (Conv.delta rfl) (Conv.refl _)) (Conv.beta _ _)

/-- `⊥_{σ→ρ}` converts to `λz. ⊥_ρ`. -/
theorem Conv.botR_arr {Γ : Ctx} (σ : Ty) (ρ : RTy) :
    (Term.botR (σ ⇒ ρ) : Term Sig Γ _) ≡ Term.lam (Term.botR ρ) :=
  Conv.trans (Conv.app_congr (Conv.delta rfl) (Conv.refl _)) (Conv.beta _ _)

namespace Derivable

/-- **A closed type is inhabited**: a universal over it, with a body not mentioning its
variable, gives the body, in any theory with Existence at `e`. -/
theorem of_forall_weaken {Ax : AxiomSet Sig} (hE : Ax existence_e) {Γ : Ctx}
    {Δ : List (Formula Sig Γ)} {φ : Formula Sig Γ} :
    ∀ (σ : Ty), σ.Closed → Derivable Ax Δ (Term.forall' (σ := σ) φ.weaken) → Derivable Ax Δ φ
  | .e, _, h => by
    have hex : Derivable Ax Δ (Term.exists' (σ := Ty.e) (Term.eq' Term.v0 Term.v0)) := ax hE
    refine exE hex ?_
    have h₁ : Derivable Ax (Hyps.weaken Δ)
        (Term.forall' ((φ.weaken (τ := Ty.e)).rename (Ren.lift Ren.shift))) :=
      rename (Ren.shift (σ := Ty.e)) h
    have h₂ : Derivable Ax (Hyps.weaken Δ)
        (((φ.weaken (τ := Ty.e)).rename (Ren.lift Ren.shift)).instantiate (Term.var .zero)) :=
      allEβ h₁ (Term.var .zero)
    have e : ((φ.weaken (τ := Ty.e)).rename (Ren.lift Ren.shift)).instantiate (Term.var .zero) =
        φ.weaken (τ := Ty.e) := by
      rw [← Term.weaken_rename, Term.instantiate_weaken]
    rw [e] at h₂
    exact weaken₁ h₂
  | .rel ρ, _, h => by
    have := allEβ h (Term.topR ρ)
    rwa [Term.instantiate_weaken] at this
  | .var i, hc, _ => absurd hc (Ty.not_closed_var i)

end Derivable

/-- **`⊤_ρ ≠ ⊥_ρ` at every closed relational type**, a theorem of `C`. -/
theorem C.topR_ne_botR : ∀ (ρ : RTy), ρ.Closed →
    C.Theorem (Sig := Sig) (Term.neg (Term.eq' (Term.topR ρ) (Term.botR ρ)))
  | .t, _ => by
    refine Derivable.conv (p := Term.neg (Term.eq' Term.top Term.bot)) ?_
      (Conv.app_congr (Conv.refl _) (Conv.app_congr (Conv.app_congr (Conv.refl _)
        (Conv.symm Conv.topR_t)) (Conv.symm Conv.botR_t)))
    refine Derivable.notI (q := Term.top) Derivable.top ?_
    exact Derivable.botE (Derivable.eqMp Derivable.hyp₀ Derivable.top)
  | .arr σ ρ, hc => by
    have ih := C.topR_ne_botR ρ hc.2
    let L : Term Sig [] (σ ⇒ ρ) := Term.lam (Term.topR ρ)
    let L' : Term Sig [] (σ ⇒ ρ) := Term.lam (Term.botR ρ)
    refine Derivable.conv (p := Term.neg (Term.eq' L L')) ?_
      (Conv.app_congr (Conv.refl _) (Conv.app_congr (Conv.app_congr (Conv.refl _)
        (Conv.symm (Conv.topR_arr σ ρ))) (Conv.symm (Conv.botR_arr σ ρ))))
    refine Derivable.notI (q := Term.eq' (Term.topR ρ) (Term.botR ρ)) ?_ (Derivable.weaken₁ ih)
    refine Derivable.of_forall_weaken C.axioms.existence_e σ hc.1 (Derivable.allI ?_)
    have h₀ : Meta.Derivable (C.axioms (Sig := Sig)) (Hyps.weaken (σ := σ) [Term.eq' L L'])
        (Term.eq' L.weaken L'.weaken) :=
      Derivable.rename (Ren.shift (σ := σ) (Γ := []))
        (Derivable.hyp₀ (Ax := C.axioms) (Δ := []) (p := Term.eq' L L'))
    have h := Derivable.eqCongrFun h₀ (Term.var .zero)
    exact Derivable.conv h (Conv.app_congr (Conv.app_congr (Conv.refl _) (Conv.beta _ _)) (Conv.beta _ _))

end Classicism.Meta
