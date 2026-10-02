import Classicism.Syntax.SentenceSchemas

/-!
# Strong Possibility

The distinctness-preserving modality of Classicism, §2.6: `□_≠p := ∃q. q ∧ □(◇q → p)`
(`P.BoxNe` in the shallow layer), and its dual `◇_≠p := ¬□_≠¬p` (`Term.diaNe`).
**Strong Possibility** is `◇_≠P` for each closed sentence `P` consistent with Maximalist
Classicism: at the pure signature the map's Strong Possibility (pure), with `Max(C)`; at a
signature `Σ`, Strong Possibility (signature `Σ`), with `Max(C(Σ))`. The source leaves its
consistency open.
-/

namespace Classicism.Meta

variable {Sig : Signature}

/-- `◇_≠p := ¬∃q. q ∧ □(◇q → ¬p)`, the dual of `□_≠`. -/
def Term.diaNe {Γ : Ctx} (p : Formula Sig Γ) : Formula Sig Γ :=
  Term.neg (Term.exists' (σ := Ty.t)
    (Term.conj Term.v0 (Term.box (Term.imp (Term.dia Term.v0) (Term.neg p.weaken)))))

namespace AxiomSet

variable (Sig)

/-- **Strong Possibility**: `◇_≠P` for each sentence `P` consistent with Maximalist
Classicism. -/
def strongPossibility : AxiomSet Sig := fun a =>
  ∃ p : Sentence Sig, Consistent (maximalist ∪ single p) ∧ a = Term.diaNe p

end AxiomSet

end Classicism.Meta
