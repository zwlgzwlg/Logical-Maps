import Classicism.Syntax.Pure

/-!
# Conservativity of `C(Σ)` over `C`

A pure sentence derivable in `C(Σ)` from pure axioms is derivable in `C` from the same
axioms (`Theorem.toPure`), for every signature `Σ` of the paper's language, one whose
constants all have closed types (`Signature.Closed`). With `Derivable.ofPure`, the other
direction, `C(Σ)` and `C` prove the same pure sentences from the same pure axioms.

The proof is syntactic. A derivation in `C(Σ)` is weakened into the context of one
individual variable `x`, and then every constant is eliminated (`Term.elim`): a constant of
type `e` becomes `x`, and a constant of a relational type `ρ` a term of that type built
from `x` (`Term.inhabit`). The elimination commutes with renaming, substitution,
conversion and holes, so it carries the derivation to one in the pure language with `x`
free, of the same pure sentence (a pure term is left as it is). Existence at `e`, the one
axiom of `C` beyond its rules, then discharges `x`.

A constant of a type variable would have no term to become: `∃v. v = v` at that type is
then a pure theorem of `C(Σ)` that `C` does not prove. So the theorem is for closed
signatures, which are the paper's.
-/

namespace Classicism.Meta

/-- A signature of the paper's language: every constant has a closed type, a type of `R`. -/
def Signature.Closed (Sig : Signature) : Prop := ∀ c, (Sig.typeOf c).Closed

variable {Sig : Signature}

namespace Term

/-! ### Eliminating the constants -/

/-- A term of the relational type `ρ`, built from the individual variable `x`: `x = x` at
`t`, and a constant function at `σ → ρ`. -/
def inhabitR : ∀ {Γ : Ctx}, Var Γ Ty.e → (ρ : RTy) → Term Signature.pure Γ ρ
  | _, x, .t => eq' (.var x) (.var x)
  | _, x, .arr _ ρ => .lam (inhabitR (.succ x) ρ)

/-- A term of any type but a type variable, built from the individual variable `x`. -/
def inhabit {Γ : Ctx} (x : Var Γ Ty.e) : (σ : Ty) → (∀ i, σ ≠ .var i) → Term Signature.pure Γ σ
  | .e, _ => .var x
  | .rel ρ, _ => inhabitR x ρ
  | .var i, h => absurd rfl (h i)

/-- The type of a constant of a closed signature is not a type variable. -/
theorem _root_.Classicism.Meta.Signature.Closed.not_var (hS : Sig.Closed) (c : Sig.Const) :
    ∀ i, Sig.typeOf c ≠ .var i :=
  fun i e => Ty.not_closed_var i (e ▸ hS c)

/-- **The elimination of the constants**: each constant of `e` becomes the variable `x`,
each constant of a relational type a term of that type built from `x`. -/
def elim (hS : Sig.Closed) : ∀ {Γ : Ctx} {σ : Ty}, Var Γ Ty.e → Term Sig Γ σ → Term Signature.pure Γ σ
  | _, _, _, .var v => .var v
  | _, _, x, .const c => inhabit x _ (hS.not_var c)
  | _, _, x, .app f a => .app (elim hS x f) (elim hS x a)
  | _, _, x, .lam b => .lam (elim hS (.succ x) b)
  | _, _, _, .and => .and
  | _, _, _, .or => .or
  | _, _, _, .not => .not
  | _, _, _, .all σ => .all σ
  | _, _, _, .ex σ => .ex σ
  | _, _, _, .eq σ => .eq σ
  | _, _, _, .constR ρ => .constR ρ
  | _, _, _, .negR ρ => .negR ρ
  | _, _, _, .andR ρ => .andR ρ
  | _, _, _, .orR ρ => .orR ρ
  | _, _, _, .coextR ρ => .coextR ρ
  | _, _, _, .boxR ρ => .boxR ρ
  | _, _, _, .inclR ρ => .inclR ρ

variable (hS : Sig.Closed)

theorem rename_inhabitR : ∀ {Γ Δ : Ctx} (r : Ren Γ Δ) (x : Var Γ Ty.e) (ρ : RTy),
    (inhabitR x ρ).rename r = inhabitR (r _ x) ρ
  | _, _, _, _, .t => rfl
  | _, _, r, x, .arr _ ρ => by simp [inhabitR, rename_inhabitR (Ren.lift r) (.succ x) ρ]

theorem rename_inhabit {Γ Δ : Ctx} (r : Ren Γ Δ) (x : Var Γ Ty.e) :
    ∀ (σ : Ty) (h : ∀ i, σ ≠ .var i), (inhabit x σ h).rename r = inhabit (r _ x) σ h
  | .e, _ => rfl
  | .rel ρ, _ => rename_inhabitR r x ρ
  | .var i, h => absurd rfl (h i)

/-- Elimination commutes with renaming, the variable `x` renamed with the rest. -/
theorem rename_elim : ∀ {Γ Δ : Ctx} (r : Ren Γ Δ) (x : Var Γ Ty.e) {σ : Ty} (a : Term Sig Γ σ),
    (elim hS x a).rename r = elim hS (r _ x) (a.rename r)
  | _, _, _, _, _, .var _ | _, _, _, _, _, .and | _, _, _, _, _, .or
  | _, _, _, _, _, .not | _, _, _, _, _, .all _ | _, _, _, _, _, .ex _ | _, _, _, _, _, .eq _
  | _, _, _, _, _, .constR _ | _, _, _, _, _, .negR _ | _, _, _, _, _, .andR _
  | _, _, _, _, _, .orR _ | _, _, _, _, _, .coextR _ | _, _, _, _, _, .boxR _
  | _, _, _, _, _, .inclR _ => rfl
  | _, _, r, x, _, .const c => rename_inhabit r x _ _
  | _, _, r, x, _, .app f a => by
    simp only [elim, rename_app, rename_elim r x f, rename_elim r x a]
  | _, _, r, x, _, .lam b => by
    simp only [elim, rename_lam, rename_elim (Ren.lift r) (.succ x) b]; rfl

theorem elim_weaken {Γ : Ctx} {τ σ : Ty} (x : Var Γ Ty.e) (a : Term Sig Γ σ) :
    elim hS (.succ x) (a.weaken (τ := τ)) = (elim hS x a).weaken :=
  (rename_elim hS Ren.shift x a).symm

theorem subst_inhabitR : ∀ {Γ Δ : Ctx} (s : Sub Signature.pure Γ Δ) (x : Var Γ Ty.e)
    (y : Var Δ Ty.e), s _ x = .var y → ∀ ρ : RTy, (inhabitR x ρ).subst s = inhabitR y ρ
  | _, _, _, _, _, h, .t => by simp [inhabitR, h]
  | _, _, s, x, y, h, .arr _ ρ => by
    simp only [inhabitR, subst_lam]
    rw [subst_inhabitR (Sub.lift s) (.succ x) (.succ y) (by simp [h]; rfl) ρ]

theorem subst_inhabit {Γ Δ : Ctx} (s : Sub Signature.pure Γ Δ) (x : Var Γ Ty.e) (y : Var Δ Ty.e)
    (h : s _ x = .var y) :
    ∀ (σ : Ty) (hσ : ∀ i, σ ≠ .var i), (inhabit x σ hσ).subst s = inhabit y σ hσ
  | .e, _ => h
  | .rel ρ, _ => subst_inhabitR s x y h ρ
  | .var i, hσ => absurd rfl (hσ i)

/-- A substitution with its constants eliminated, the variable `y` of its target standing
for them. -/
def _root_.Classicism.Meta.Sub.elim {Γ Δ : Ctx} (y : Var Δ Ty.e) (s : Sub Sig Γ Δ) :
    Sub Signature.pure Γ Δ :=
  fun _ v => elim hS y (s _ v)

theorem _root_.Classicism.Meta.Sub.elim_lift {Γ Δ : Ctx} (y : Var Δ Ty.e) (s : Sub Sig Γ Δ) {σ : Ty} :
    Sub.elim hS (.succ y) (Sub.lift s (σ := σ)) = Sub.lift (Sub.elim hS y s) := by
  funext τ v
  cases v with
  | zero => rfl
  | succ v => exact elim_weaken hS y (s _ v)

/-- Elimination commutes with substitution, when the substitution sends the variable `x`
to the variable `y` that stands for the constants after it. -/
theorem subst_elim : ∀ {Γ Δ : Ctx} (s : Sub Sig Γ Δ) (x : Var Γ Ty.e) (y : Var Δ Ty.e),
    s _ x = .var y → ∀ {σ : Ty} (a : Term Sig Γ σ),
    (elim hS x a).subst (Sub.elim hS y s) = elim hS y (a.subst s)
  | _, _, _, _, _, _, _, .var _ | _, _, _, _, _, _, _, .and | _, _, _, _, _, _, _, .or
  | _, _, _, _, _, _, _, .not | _, _, _, _, _, _, _, .all _ | _, _, _, _, _, _, _, .ex _
  | _, _, _, _, _, _, _, .eq _ | _, _, _, _, _, _, _, .constR _ | _, _, _, _, _, _, _, .negR _
  | _, _, _, _, _, _, _, .andR _ | _, _, _, _, _, _, _, .orR _ | _, _, _, _, _, _, _, .coextR _
  | _, _, _, _, _, _, _, .boxR _ | _, _, _, _, _, _, _, .inclR _ => rfl
  | _, _, s, x, y, h, _, .const c =>
    subst_inhabit (Sub.elim hS y s) x y (by simp only [Sub.elim, h]; rfl) _ _
  | _, _, s, x, y, h, _, .app f a => by
    simp only [elim, subst_app, subst_elim s x y h f, subst_elim s x y h a]
  | _, _, s, x, y, h, _, .lam b => by
    simp only [elim, subst_lam]
    rw [← Sub.elim_lift, subst_elim (Sub.lift s) (.succ x) (.succ y) (by simp [h]; rfl) b]

theorem elim_instantiate {Γ : Ctx} {σ τ : Ty} (x : Var Γ Ty.e) (b : Term Sig (σ :: Γ) τ)
    (a : Term Sig Γ σ) :
    elim hS x (b.instantiate a) = (elim hS (.succ x) b).instantiate (elim hS x a) := by
  have e : Sub.elim hS x (Sub.cons a Sub.id) = Sub.cons (elim hS x a) Sub.id := by
    funext τ v; cases v <;> rfl
  simp only [instantiate]
  rw [← e, subst_elim hS (Sub.cons a Sub.id) (.succ x) x rfl b]

/-- The unfoldings are the same with the constants eliminated: they have none. -/
theorem unfoldR_elim {Γ : Ctx} {σ : Ty} (x : Var Γ Ty.e) :
    ∀ {a b : Term Sig Γ σ}, a.unfoldR = some b → (elim hS x a).unfoldR = some (elim hS x b)
  | .var _, _, h | .const _, _, h | .app _ _, _, h | .lam _, _, h | .and, _, h | .or, _, h
  | .not, _, h | .all _, _, h | .ex _, _, h | .eq _, _, h => nomatch h
  | .constR ρ, _, h | .negR ρ, _, h | .andR ρ, _, h | .orR ρ, _, h | .coextR ρ, _, h
  | .boxR ρ, _, h | .inclR ρ, _, h => by
    cases ρ <;> (simp only [unfoldR, unfoldConst, unfoldNeg, unfoldAnd, unfoldOr, unfoldCoext,
      unfoldBox, unfoldIncl, Option.some.injEq] at h; subst h; rfl)

/-- A pure term, read in a signature, has nothing to eliminate. -/
theorem elim_ofPure : ∀ {Γ : Ctx} {σ : Ty} (x : Var Γ Ty.e) (a : Term Signature.pure Γ σ),
    elim hS x (ofPure (Sig := Sig) a) = a
  | _, _, _, .var _ | _, _, _, .and | _, _, _, .or
  | _, _, _, .not | _, _, _, .all _ | _, _, _, .ex _ | _, _, _, .eq _
  | _, _, _, .constR _ | _, _, _, .negR _ | _, _, _, .andR _ | _, _, _, .orR _
  | _, _, _, .coextR _ | _, _, _, .boxR _ | _, _, _, .inclR _ => rfl
  | _, _, _, .const c => nomatch c
  | _, _, x, .app f a => by
    simp only [ofPure_app, elim, elim_ofPure x f, elim_ofPure x a]
  | _, _, x, .lam b => by
    simp only [ofPure_lam, elim, elim_ofPure (.succ x) b]

end Term

/-! ### Conversion -/

theorem Beta.elim (hS : Sig.Closed) {Γ : Ctx} {σ : Ty} (x : Var Γ Ty.e) {a b : Term Sig Γ σ}
    (h : Beta a b) : Beta (Term.elim hS x a) (Term.elim hS x b) := by
  cases h with
  | intro b a =>
    show Beta (.app (.lam (Term.elim hS (.succ x) b)) (Term.elim hS x a)) _
    rw [Term.elim_instantiate]
    exact Beta.intro _ _

theorem Eta.elim (hS : Sig.Closed) {Γ : Ctx} {σ : Ty} (x : Var Γ Ty.e) {a b : Term Sig Γ σ}
    (h : Eta a b) : Eta (Term.elim hS x a) (Term.elim hS x b) := by
  cases h with
  | intro f =>
    show Eta (.lam (.app (Term.elim hS (.succ x) f.weaken) (.var .zero))) (Term.elim hS x f)
    rw [Term.elim_weaken]
    exact Eta.intro _

theorem Step.elim (hS : Sig.Closed) : ∀ {Γ : Ctx} {σ : Ty} (x : Var Γ Ty.e) {a b : Term Sig Γ σ},
    Step BetaEta a b → Step BetaEta (Term.elim hS x a) (Term.elim hS x b)
  | _, _, x, _, _, .here h => .here (h.elim (fun h => Or.inl (Beta.elim hS x h))
      (fun h => h.elim (fun h => Or.inr (Or.inl (Eta.elim hS x h)))
        (fun h => Or.inr (Or.inr (Term.unfoldR_elim hS x h)))))
  | _, _, x, _, _, .appL h => .appL (Step.elim hS x h)
  | _, _, x, _, _, .appR h => .appR (Step.elim hS x h)
  | _, _, x, _, _, .lam h => .lam (Step.elim hS (.succ x) h)

theorem Conv.elim (hS : Sig.Closed) {Γ : Ctx} {σ : Ty} (x : Var Γ Ty.e) {a b : Term Sig Γ σ}
    (h : a ≡ b) : Term.elim hS x a ≡ Term.elim hS x b := by
  induction h with
  | rel h => exact EqvGen.rel (Step.elim hS x h)
  | refl _ => exact EqvGen.refl _
  | symm _ ih => exact EqvGen.symm ih
  | trans _ _ ih₁ ih₂ => exact EqvGen.trans ih₁ ih₂

/-! ### Holes -/

namespace Hole

/-- The variable `x`, carried under the binders above the hole. -/
def var : ∀ {Γ Γ' : Ctx} {σ τ : Ty}, Hole Sig Γ σ Γ' τ → Var Γ Ty.e → Var Γ' Ty.e
  | _, _, _, _, .hole, x => x
  | _, _, _, _, .appL C _, x => var C x
  | _, _, _, _, .appR _ C, x => var C x
  | _, _, _, _, .lam C, x => var C (.succ x)

/-- A hole with its constants eliminated. -/
def elim (hS : Sig.Closed) : ∀ {Γ Γ' : Ctx} {σ τ : Ty}, Var Γ Ty.e → Hole Sig Γ σ Γ' τ →
    Hole Signature.pure Γ σ Γ' τ
  | _, _, _, _, _, .hole => .hole
  | _, _, _, _, x, .appL C b => .appL (elim hS x C) (Term.elim hS x b)
  | _, _, _, _, x, .appR f C => .appR (Term.elim hS x f) (elim hS x C)
  | _, _, _, _, x, .lam C => .lam (elim hS (.succ x) C)

theorem plug_elim (hS : Sig.Closed) : ∀ {Γ Γ' : Ctx} {σ τ : Ty} (x : Var Γ Ty.e)
    (C : Hole Sig Γ σ Γ' τ) (a : Term Sig Γ' τ),
    Term.elim hS x (C.plug a) = (elim hS x C).plug (Term.elim hS (C.var x) a)
  | _, _, _, _, _, .hole, _ => rfl
  | _, _, _, _, x, .appL C b, a => by simp only [plug, elim, var, Term.elim, plug_elim hS x C a]
  | _, _, _, _, x, .appR f C, a => by simp only [plug, elim, var, Term.elim, plug_elim hS x C a]
  | _, _, _, _, x, .lam C, a => by simp only [plug, elim, var, Term.elim, plug_elim hS (.succ x) C a]

end Hole

/-! ### Derivations -/

theorem Hyps.map_elim_weaken (hS : Sig.Closed) {Γ : Ctx} {σ : Ty} (x : Var Γ Ty.e)
    (Δ : List (Formula Sig Γ)) :
    (Hyps.weaken (σ := σ) Δ).map (Term.elim hS (.succ x)) = Hyps.weaken (Δ.map (Term.elim hS x)) := by
  simp only [Hyps.weaken, List.map_map]
  congr 1
  funext a
  exact Term.elim_weaken hS x a

/-- The axioms of a derivation in a signature are pure, those of a pure axiom set `Ax'`;
and its logical axioms are among the logical ones of `Ax'`. -/
structure PureAxioms (Ax : AxiomSet Sig) (Ax' : AxiomSet Signature.pure) : Prop where
  ax : ∀ a, Ax a → ∃ p, Ax' p ∧ a = Term.ofPure p
  logical : ∀ a, Ax.logical a → ∃ p, Ax'.logical p ∧ a = Term.ofPure p

theorem PureAxioms.logical' {Ax : AxiomSet Sig} {Ax' : AxiomSet Signature.pure}
    (h : PureAxioms Ax Ax') : PureAxioms Ax.logical Ax'.logical where
  ax := h.logical
  logical a ha := (h.logical a ha.1).elim fun p ⟨hp, e⟩ => ⟨p, ⟨hp, hp.2⟩, e⟩

/-- **A derivation in a closed signature from pure axioms, with its constants eliminated,
is a derivation in the pure language** from those axioms, in the same context, the
variable `x` standing for the constants. By induction on the derivation, as
`Derivable.ofPure` is. -/
theorem Derivable.elim (hS : Sig.Closed) : ∀ {Ax : AxiomSet Sig} {Ax' : AxiomSet Signature.pure},
    PureAxioms Ax Ax' → ∀ {Γ : Ctx} (x : Var Γ Ty.e) {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ},
    Derivable Ax Δ p → Derivable Ax' (Δ.map (Term.elim hS x)) (Term.elim hS x p)
  | _, _, _, _, _, _, _, hyp h => hyp (List.mem_map.2 ⟨_, h, rfl⟩)
  | _, _, hA, _, x, _, _, ax (a := a) h => by
    obtain ⟨p, hp, rfl⟩ := hA.ax a h
    rw [← Term.ofPure_close, Term.elim_ofPure]
    exact ax hp
  | _, _, hA, _, x, _, _, andI h₁ h₂ => andI (elim hS hA x h₁) (elim hS hA x h₂)
  | _, _, hA, _, x, _, _, andE₁ h => andE₁ (elim hS hA x h)
  | _, _, hA, _, x, _, _, andE₂ h => andE₂ (elim hS hA x h)
  | _, _, hA, _, x, _, _, orI₁ h => orI₁ (elim hS hA x h)
  | _, _, hA, _, x, _, _, orI₂ h => orI₂ (elim hS hA x h)
  | _, _, hA, _, x, _, _, orE h h₁ h₂ => orE (elim hS hA x h) (elim hS hA x h₁) (elim hS hA x h₂)
  | _, _, hA, _, x, _, _, notI h₁ h₂ => notI (elim hS hA x h₁) (elim hS hA x h₂)
  | _, _, hA, _, x, _, _, notE h₁ h₂ => notE (elim hS hA x h₁) (elim hS hA x h₂)
  | _, _, _, _, _, _, _, em _ => em _
  | _, _, hA, _, x, _, _, allE h a => allE (elim hS hA x h) (Term.elim hS x a)
  | _, _, hA, _, x, _, _, exI a h => exI (Term.elim hS x a) (elim hS hA x h)
  | _, _, hA, _, x, _, _, allI h => by
    have := elim hS hA (.succ x) h
    rw [Hyps.map_elim_weaken] at this
    exact allI this
  | _, _, hA, _, x, Δ, _, exE (F := F) (r := q) h h' => by
    have this := elim hS hA (.succ x) h'
    have e : (Term.app F.weaken (.var .zero) :: Hyps.weaken Δ).map (Term.elim hS (.succ x))
        = Term.app (Term.elim hS x F).weaken (.var .zero) :: Hyps.weaken (Δ.map (Term.elim hS x)) := by
      simp only [List.map_cons, Hyps.map_elim_weaken, Term.elim, Term.elim_weaken]
    rw [e, Term.elim_weaken] at this
    exact exE (elim hS hA x h) this
  | _, _, _, _, _, _, _, refl a => refl _
  | _, _, hA, _, x, _, _, ll F h₁ h₂ => ll (Term.elim hS x F) (elim hS hA x h₁) (elim hS hA x h₂)
  | _, _, hA, _, x, _, _, subst C h₁ h₂ h₃ => by
    have h₁' := elim hS hA.logical' (C.var x) h₁
    have h₂' := elim hS hA.logical' (C.var x) h₂
    have h₃' := elim hS hA x h₃
    rw [Hole.plug_elim] at h₃' ⊢
    exact subst (C.elim hS x) h₁' h₂' h₃'
  | _, _, hA, _, x, _, _, conv h c => conv (elim hS hA x h) (Conv.elim hS x c)

/-- **Conservativity**: a pure sentence derivable in a closed signature from pure axioms
is derivable in the pure language from them, provided they include Existence at `e`. -/
theorem Theorem.toPure (hS : Sig.Closed) {Ax : AxiomSet Sig} {Ax' : AxiomSet Signature.pure}
    (hA : PureAxioms Ax Ax') (hE : Ax' existence_e) {p : Sentence Signature.pure}
    (h : Theorem Ax (Term.ofPure p)) : Theorem Ax' p := by
  have h₁ := Derivable.rename (Ren.shift (σ := Ty.e)) h
  rw [← Term.ofPure_rename] at h₁
  have h₂ := Derivable.elim hS hA .zero h₁
  rw [Term.elim_ofPure] at h₂
  have hex : Theorem Ax' existence_e := by
    have := Derivable.ax (Ax := Ax') (Δ := []) hE
    rwa [show (existence_e (Sig := Signature.pure)).close = existence_e from Term.rename_id' _] at this
  exact Derivable.exE hex (Derivable.weaken h₂ (List.nil_subset _))

end Classicism.Meta
