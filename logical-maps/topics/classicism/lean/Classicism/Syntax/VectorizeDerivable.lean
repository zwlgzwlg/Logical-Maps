import Classicism.Syntax.Vectorize
import Classicism.Syntax.Entailment

/-!
# The vectorization theorem

**A derivation survives vectorization.** If `p` is derivable from hypotheses `Δ`, then the
vectorization of `p` along any assignment `θ` is derivable from the vectorizations of `Δ`,
in any theory whose axioms vectorize to axioms: Classicism itself among them, whose one
axiom, Existence at `e`, mentions no type variable. So a theorem of `C` stated at a type
variable `var i` is a theorem at every list of types put in its place, the empty list
included.

The proof is by induction on the derivation, with the generic translation
(`Term.vecG`), which commutes with substitution on the nose: each rule goes to its block
version (`Syntax/Blocks.lean`), Subst to Subst with the hole translated, and conversion to
conversion. The readable translation (`Term.vec`) then follows, since the two are
convertible.

This is the theorem behind the list forms of the map's principles: a certified rule
`foo.rule : ∀ σ …, C.Theorem (P.quoted σ … → Q.quoted σ …)` is uniform in its types, so
it holds at `var 0`, and vectorizing it there gives the rule between the list forms
(`history/VECTORIZATION-PLAN.md`, D5 and D6).
-/

namespace Classicism.Meta

variable {Sig : Signature}

section
variable (θ : Assign) (hc : Sig.VecFixed θ)

/-- Hypotheses, translated by the generic translation. -/
abbrev Hyps.vecG {Γ : Ctx} (Δ : List (Formula Sig Γ)) : List (Formula Sig (Ctx.vec θ Γ)) :=
  Δ.map (Term.vecG1 θ hc)

/-- Hypotheses, translated by the readable translation. -/
noncomputable abbrev Hyps.vec {Γ : Ctx} (Δ : List (Formula Sig Γ)) :
    List (Formula Sig (Ctx.vec θ Γ)) :=
  Δ.map (Term.vec1 θ hc)

theorem Term.vecG1_weaken {Γ : Ctx} {σ : Ty} {ρ : RTy} (a : Term Sig Γ ρ) :
    (a.weaken (τ := σ)).vecG1 θ hc = (a.vecG1 θ hc).rename (Ren.wkBlock (σ.vec θ)) := by
  rw [Term.vecG1, Term.vecG_weaken]; rfl

theorem Hyps.vecG_weaken {Γ : Ctx} {σ : Ty} (Δ : List (Formula Sig Γ)) :
    Hyps.vecG θ hc (Hyps.weaken (σ := σ) Δ) = Hyps.wkBlock (σ.vec θ) (Hyps.vecG θ hc Δ) := by
  simp only [Hyps.vecG, Hyps.weaken, Hyps.wkBlock, List.map_map]
  congr 1
  funext a
  exact Term.vecG1_weaken θ hc a

/-- Existence at `e`, the one logical axiom, is its own vectorization. -/
theorem existence_e_vecG1 : (existence_e : Sentence Sig).vecG1 θ hc = existence_e := rfl

/-- The logical axioms vectorize to logical axioms. -/
theorem Logical.vecG1 {a : Sentence Sig} (h : Logical a) : Logical (a.vecG1 θ hc) := by
  cases h; rfl

/-- An axiom set **vectorizes**: each axiom's vectorization is an axiom. -/
def AxiomSet.VecClosed (Ax : AxiomSet Sig) : Prop := ∀ a, Ax a → Ax (a.vecG1 θ hc)

theorem AxiomSet.VecClosed.logical {Ax : AxiomSet Sig} (h : AxiomSet.VecClosed θ hc Ax) :
    AxiomSet.VecClosed θ hc Ax.logical :=
  fun _ ha => ⟨h _ ha.1, Logical.vecG1 θ hc ha.2⟩

theorem C.vecClosed : AxiomSet.VecClosed θ hc (C.axioms (Sig := Sig)) :=
  fun _ h => Logical.vecG1 θ hc h

theorem C.vecClosedMinus : AxiomSet.VecClosed θ hc (C.axiomsMinus (Sig := Sig)) :=
  fun _ h => h.elim

namespace Derivable

/-- **The vectorization theorem**, for the generic translation: a derivation from `Δ` in a
theory gives a derivation of the vectorization from the vectorized hypotheses, in any
theory containing the vectorized axioms and, for Subst's premises, whose logical part
contains the vectorized logical part. -/
theorem vecG : ∀ {Ax Ax' : AxiomSet Sig}, (∀ a, Ax a → Ax' (a.vecG1 θ hc)) →
    (∀ a, Ax.logical a → Ax'.logical (a.vecG1 θ hc)) →
    ∀ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ},
      Derivable Ax Δ p → Derivable Ax' (Hyps.vecG θ hc Δ) (p.vecG1 θ hc)
  | _, _, _, _, _, _, _, hyp h => hyp (List.mem_map_of_mem h)
  | _, _, hA, _, _, _, _, ax (a := a) h => by
    rw [Term.vecG1_close]; exact ax (hA a h)
  | _, _, hA, hL, _, _, _, andI h₁ h₂ => andI (vecG hA hL h₁) (vecG hA hL h₂)
  | _, _, hA, hL, _, _, _, andE₁ h => andE₁ (vecG hA hL h)
  | _, _, hA, hL, _, _, _, andE₂ h => andE₂ (vecG hA hL h)
  | _, _, hA, hL, _, _, _, orI₁ h => orI₁ (vecG hA hL h)
  | _, _, hA, hL, _, _, _, orI₂ h => orI₂ (vecG hA hL h)
  | _, _, hA, hL, _, _, _, orE h h₁ h₂ => orE (vecG hA hL h) (vecG hA hL h₁) (vecG hA hL h₂)
  | _, _, hA, hL, _, _, _, notI h₁ h₂ => notI (vecG hA hL h₁) (vecG hA hL h₂)
  | _, _, hA, hL, _, _, _, notE h₁ h₂ => notE (vecG hA hL h₁) (vecG hA hL h₂)
  | _, _, _, _, _, _, _, em p => em _
  | _, _, hA, hL, _, _, _, allE (σ := σ) h a => allEC (σ.vec θ) (vecG hA hL h) (a.vecG θ hc)
  | _, _, hA, hL, _, Δ, _, allI (σ := σ) h => by
    have h' := vecG hA hL h
    rw [Hyps.vecG_weaken] at h'
    exact allIC (σ.vec θ) h'
  | _, _, hA, hL, _, _, _, exI (σ := σ) a h => exIC (σ.vec θ) (a.vecG θ hc) (vecG hA hL h)
  | _, _, hA, hL, _, Δ, _, exE (σ := σ) (F := F) (r := r) h h' => by
    have h'' := vecG hA hL h'
    have e₁ : (Term.app F.weaken (Term.var .zero) : Formula Sig (σ :: _)).vecG1 θ hc
        = Term.appBlock ((F.vecG1 θ hc).rename (Ren.wkBlock (σ.vec θ))) (Terms.vars (σ.vec θ) _) := by
      show Term.appBlock ((F.weaken (τ := σ)).vecG1 θ hc) _ = _
      rw [Term.vecG1_weaken]; rfl
    have e₂ : Hyps.vecG θ hc (Term.app F.weaken (Term.var .zero) :: Hyps.weaken (σ := σ) Δ)
        = Term.appBlock ((F.vecG1 θ hc).rename (Ren.wkBlock (σ.vec θ))) (Terms.vars (σ.vec θ) _) ::
          Hyps.wkBlock (σ.vec θ) (Hyps.vecG θ hc Δ) := by
      show Term.vecG1 θ hc (Term.app F.weaken (Term.var .zero) : Formula Sig (σ :: _)) ::
        Hyps.vecG θ hc (Hyps.weaken (σ := σ) Δ) = _
      rw [e₁, Hyps.vecG_weaken]
    rw [e₂, Term.vecG1_weaken] at h''
    exact exEC (σ.vec θ) (vecG hA hL h) h''
  | _, _, _, _, _, _, _, refl a => reflC (a.vecG θ hc)
  | _, _, hA, hL, _, _, _, ll (σ := σ) F h₁ h₂ =>
    llC (σ.vec θ) (F.vecG1 θ hc) (vecG hA hL h₁) (vecG hA hL h₂)
  | _, _, hA, hL, _, _, _, conv h c => conv (vecG hA hL h) (Term.vecG_conv θ hc c).head1
  | Ax, Ax', hA, hL, _, _, _, subst (P := P) (Q := Q) C h₁ h₂ h₃ => by
    have hL' : ∀ a, Ax.logical.logical a → Ax'.logical.logical (a.vecG1 θ hc) :=
      fun a ha => ⟨hL a ha.1, Logical.vecG1 θ hc ha.2⟩
    have h₁' := vecG hL hL' h₁
    have h₂' := vecG hL hL' h₂
    have h₃' := vecG hA hL h₃
    rw [Hole.vecG1_plug] at h₃' ⊢
    exact subst (C.vec θ hc) h₁' h₂' h₃'

/-- Derivability from hypotheses transfers along their conversion. -/
theorem conv_hyps {Ax : AxiomSet Sig} {Γ : Ctx} {α : Type} (f g : α → Formula Sig Γ) :
    ∀ (Δ : List α) {p : Formula Sig Γ}, (∀ q ∈ Δ, f q ≡ g q) →
      Derivable Ax (Δ.map f) p → Derivable Ax (Δ.map g) p
  | [], _, _, h => h
  | q :: Δ, _, hq, h => by
    have h₁ := conv_hyps f g Δ (fun q' h' => hq q' (List.mem_cons_of_mem _ h')) (impI h)
    exact impE (weaken₁ h₁) (conv hyp₀ (Conv.symm (hq q (List.mem_cons_self ..))))

/-- **The vectorization theorem.** -/
theorem vec {Ax Ax' : AxiomSet Sig} (hA : ∀ a, Ax a → Ax' (a.vecG1 θ hc))
    (hL : ∀ a, Ax.logical a → Ax'.logical (a.vecG1 θ hc))
    {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ} (h : Derivable Ax Δ p) :
    Derivable Ax' (Hyps.vec θ hc Δ) (p.vec1 θ hc) :=
  conv_hyps _ _ Δ (fun q _ => Conv.symm (Term.vec1_conv_vecG1 θ hc q))
    (conv (vecG θ hc hA hL h) (Conv.symm (Term.vec1_conv_vecG1 θ hc p)))

/-- The vectorization theorem, in a theory whose axioms vectorize. -/
theorem vec_of_vecClosed {Ax : AxiomSet Sig} (hAx : AxiomSet.VecClosed θ hc Ax)
    {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ} (h : Derivable Ax Δ p) :
    Derivable Ax (Hyps.vec θ hc Δ) (p.vec1 θ hc) :=
  vec θ hc hAx (hAx.logical θ hc) h

end Derivable

/-- A theorem of a theory whose axioms vectorize: its vectorization is one too. -/
theorem Theorem.vec {Ax : AxiomSet Sig} (hAx : AxiomSet.VecClosed θ hc Ax) {p : Sentence Sig}
    (h : Theorem Ax p) : Theorem Ax (p.vec1 θ hc) :=
  Derivable.vec_of_vecClosed θ hc hAx h

/-- **A theorem of Classicism, vectorized, is a theorem of Classicism.** -/
theorem C.Theorem.vec {p : Sentence Sig} (h : C.Theorem p) : C.Theorem (p.vec1 θ hc) :=
  Meta.Theorem.vec θ hc (C.vecClosed θ hc) h

/-- The same for `C⁻`. -/
theorem C.TheoremMinus.vec {p : Sentence Sig} (h : C.TheoremMinus p) :
    C.TheoremMinus (p.vec1 θ hc) :=
  Meta.Theorem.vec θ hc (C.vecClosedMinus θ hc) h

end

/-! ### Signatures whose constants are left alone -/

/-- A signature whose constants have closed types: every assignment leaves them alone. -/
theorem Signature.VecFixed.of_closed {Sig : Signature} (h : ∀ c, (Sig.typeOf c).Closed)
    (θ : Assign) : Sig.VecFixed θ :=
  fun c => Ty.vec_closed θ (h c)

/-- The pure signature has no constants. -/
theorem Signature.pure_vecFixed (θ : Assign) : Signature.pure.VecFixed θ :=
  fun c => nomatch c

end Classicism.Meta
