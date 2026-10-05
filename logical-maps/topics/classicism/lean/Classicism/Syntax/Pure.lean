import Classicism.Syntax.Axioms

/-!
# The pure language inside every signature

A term of the pure language — no constants — is a term of the language of any signature,
and a derivation in the pure language is a derivation in any signature: `Term.ofPure`
reads the one into the other, and `Derivable.ofPure` carries derivations across. So a
theorem of `C` in the pure language is a theorem of `C(Σ)` for every `Σ`. This is what
lets a lemma proved in the shallow layer and certified at `Signature.pure`, where the
map's principles live, be applied inside a metalogical proof about a signature `Σ`: the
sentence schemas (`SentenceSchemas.lean`) are stated for any `Sig`, and the
object-level steps they need are certified once and carried over by `ofPure`.

The other direction — a pure sentence that is a theorem of `C(Σ)` is a theorem of `C` —
is the conservativity of the signature extension, which the map proves through
completeness (`possibility-signature-r-implies-possibility-schema-r`). It is proved
syntactically in `Conservativity.lean`: each constant is replaced by a variable, and the
variable discharged by Existence.

Everything is by structural recursion on terms, holes, conversions and derivations, as
`rename` is (`Term.lean`, `Conversion.lean`, `Derivation.lean`); the reading of terms is
written through `Term.rec` like `rename`, so that the kernel evaluates it quickly when a
certified sentence is carried into a signature.
-/

namespace Classicism.Meta

variable {Sig : Signature}

/-! ### Terms -/

namespace Term

/-- The structural implementation of `ofPure`. -/
def ofPureImpl : ∀ {Γ : Ctx} {σ : Ty}, Term Signature.pure Γ σ → Term Sig Γ σ
  | _, _, .var v => .var v
  | _, _, .const c => nomatch c
  | _, _, .app f a => .app (ofPureImpl f) (ofPureImpl a)
  | _, _, .lam b => .lam (ofPureImpl b)
  | _, _, .and => .and
  | _, _, .or => .or
  | _, _, .not => .not
  | _, _, .all σ => .all σ
  | _, _, .ex σ => .ex σ
  | _, _, .eq σ => .eq σ
  | _, _, .constR ρ => .constR ρ
  | _, _, .negR ρ => .negR ρ
  | _, _, .andR ρ => .andR ρ
  | _, _, .orR ρ => .orR ρ
  | _, _, .coextR ρ => .coextR ρ
  | _, _, .boxR ρ => .boxR ρ
  | _, _, .inclR ρ => .inclR ρ

/-- A term of the pure language, read in the signature `Sig`: the same tree, which has
no constant to read. Through `Term.rec`, as `rename` is, for the kernel's sake. -/
@[implemented_by ofPureImpl]
def ofPure : ∀ {Γ : Ctx} {σ : Ty}, Term Signature.pure Γ σ → Term Sig Γ σ :=
  fun {_ _} t =>
    Term.rec (motive := fun Γ σ _ => Term Sig Γ σ)
      (var := fun v => Term.var v)
      (const := fun c => Empty.elim c)
      (app := fun _ _ f a => Term.app f a)
      (lam := fun _ b => Term.lam b)
      (and := Term.and) (or := Term.or) (not := Term.not)
      (all := fun σ => Term.all σ) (ex := fun σ => Term.ex σ) (eq := fun σ => Term.eq σ)
      (constR := fun ρ => Term.constR ρ) (negR := fun ρ => Term.negR ρ)
      (andR := fun ρ => Term.andR ρ) (orR := fun ρ => Term.orR ρ)
      (coextR := fun ρ => Term.coextR ρ) (boxR := fun ρ => Term.boxR ρ)
      (inclR := fun ρ => Term.inclR ρ)
      t

section
variable {Γ : Ctx}
@[simp] theorem ofPure_var {σ : Ty} (v : Var Γ σ) : ofPure (Sig := Sig) (.var v) = .var v := rfl
@[simp] theorem ofPure_app {σ : Ty} {ρ : RTy} (f : Term Signature.pure Γ (σ ⇒ ρ)) (a : Term Signature.pure Γ σ) :
    ofPure (Sig := Sig) (.app f a) = .app (ofPure f) (ofPure a) := rfl
@[simp] theorem ofPure_lam {σ : Ty} {ρ : RTy} (b : Term Signature.pure (σ :: Γ) ρ) :
    ofPure (Sig := Sig) (.lam b) = .lam (ofPure b) := rfl
@[simp] theorem ofPure_and : ofPure (Sig := Sig) (Γ := Γ) .and = .and := rfl
@[simp] theorem ofPure_or : ofPure (Sig := Sig) (Γ := Γ) .or = .or := rfl
@[simp] theorem ofPure_not : ofPure (Sig := Sig) (Γ := Γ) .not = .not := rfl
@[simp] theorem ofPure_all (σ : Ty) : ofPure (Sig := Sig) (Γ := Γ) (.all σ) = .all σ := rfl
@[simp] theorem ofPure_ex (σ : Ty) : ofPure (Sig := Sig) (Γ := Γ) (.ex σ) = .ex σ := rfl
@[simp] theorem ofPure_eq (σ : Ty) : ofPure (Sig := Sig) (Γ := Γ) (.eq σ) = .eq σ := rfl
@[simp] theorem ofPure_constR (ρ : RTy) : ofPure (Sig := Sig) (Γ := Γ) (.constR ρ) = .constR ρ := rfl
@[simp] theorem ofPure_negR (ρ : RTy) : ofPure (Sig := Sig) (Γ := Γ) (.negR ρ) = .negR ρ := rfl
@[simp] theorem ofPure_andR (ρ : RTy) : ofPure (Sig := Sig) (Γ := Γ) (.andR ρ) = .andR ρ := rfl
@[simp] theorem ofPure_orR (ρ : RTy) : ofPure (Sig := Sig) (Γ := Γ) (.orR ρ) = .orR ρ := rfl
@[simp] theorem ofPure_coextR (ρ : RTy) : ofPure (Sig := Sig) (Γ := Γ) (.coextR ρ) = .coextR ρ := rfl
@[simp] theorem ofPure_boxR (ρ : RTy) : ofPure (Sig := Sig) (Γ := Γ) (.boxR ρ) = .boxR ρ := rfl
@[simp] theorem ofPure_inclR (ρ : RTy) : ofPure (Sig := Sig) (Γ := Γ) (.inclR ρ) = .inclR ρ := rfl
end

/-- Reading a pure term in a signature changes none of its types. -/
@[simp] theorem closedTypes_ofPure :
    ∀ {Γ : Ctx} {σ : Ty} (t : Term Signature.pure Γ σ),
      (ofPure (Sig := Sig) t).closedTypes = t.closedTypes
  | _, _, .var _ | _, _, .and | _, _, .or | _, _, .not | _, _, .all _ | _, _, .ex _ | _, _, .eq _
  | _, _, .constR _ | _, _, .negR _ | _, _, .andR _ | _, _, .orR _ | _, _, .coextR _
  | _, _, .boxR _ | _, _, .inclR _ => rfl
  | _, _, .const c => nomatch c
  | _, _, .app f a => by
    simp [ofPure_app, Term.closedTypes, closedTypes_ofPure f, closedTypes_ofPure a]
  | _, _, .lam b => by
    simp [ofPure_lam, Term.closedTypes, closedTypes_ofPure b]

/-- Reading into a signature commutes with renaming. -/
theorem ofPure_rename : ∀ {Γ Δ : Ctx} (r : Ren Γ Δ) {σ : Ty} (a : Term Signature.pure Γ σ),
    ofPure (Sig := Sig) (a.rename r) = (ofPure a).rename r
  | _, _, _, _, .var _ | _, _, _, _, .and | _, _, _, _, .or
  | _, _, _, _, .not | _, _, _, _, .all _ | _, _, _, _, .ex _ | _, _, _, _, .eq _
  | _, _, _, _, .constR _ | _, _, _, _, .negR _ | _, _, _, _, .andR _ | _, _, _, _, .orR _
  | _, _, _, _, .coextR _ | _, _, _, _, .boxR _ | _, _, _, _, .inclR _ => rfl
  | _, _, _, _, .const c => nomatch c
  | _, _, r, _, .app f a => by simp [ofPure_rename r f, ofPure_rename r a]
  | _, _, r, _, .lam b => by simp [ofPure_rename (Ren.lift r) b]

theorem ofPure_weaken {Γ : Ctx} {τ σ : Ty} (a : Term Signature.pure Γ σ) :
    ofPure (Sig := Sig) (a.weaken (τ := τ)) = (ofPure a).weaken := ofPure_rename _ a

theorem ofPure_close {Γ : Ctx} {σ : Ty} (a : Term Signature.pure [] σ) :
    ofPure (Sig := Sig) (a.close (Γ := Γ)) = (ofPure a).close := ofPure_rename _ a

/-- A substitution, read into a signature. -/
def _root_.Classicism.Meta.Sub.ofPure {Γ Δ : Ctx} (s : Sub Signature.pure Γ Δ) : Sub Sig Γ Δ :=
  fun _ v => Term.ofPure (s _ v)

theorem _root_.Classicism.Meta.Sub.ofPure_lift {Γ Δ : Ctx} (s : Sub Signature.pure Γ Δ) {σ : Ty} :
    Sub.ofPure (Sig := Sig) (Sub.lift s (σ := σ)) = Sub.lift (Sub.ofPure s) := by
  funext τ v
  cases v with
  | zero => rfl
  | succ v => exact ofPure_weaken _

theorem _root_.Classicism.Meta.Sub.ofPure_cons_id {Γ : Ctx} {σ : Ty} (a : Term Signature.pure Γ σ) :
    Sub.ofPure (Sig := Sig) (Sub.cons a Sub.id) = Sub.cons (ofPure a) Sub.id := by
  funext τ v; cases v <;> rfl

/-- Reading into a signature commutes with substitution. -/
theorem ofPure_subst : ∀ {Γ Δ : Ctx} (s : Sub Signature.pure Γ Δ) {σ : Ty} (a : Term Signature.pure Γ σ),
    ofPure (Sig := Sig) (a.subst s) = (ofPure a).subst (Sub.ofPure s)
  | _, _, _, _, .var _ | _, _, _, _, .and | _, _, _, _, .or
  | _, _, _, _, .not | _, _, _, _, .all _ | _, _, _, _, .ex _ | _, _, _, _, .eq _
  | _, _, _, _, .constR _ | _, _, _, _, .negR _ | _, _, _, _, .andR _ | _, _, _, _, .orR _
  | _, _, _, _, .coextR _ | _, _, _, _, .boxR _ | _, _, _, _, .inclR _ => rfl
  | _, _, _, _, .const c => nomatch c
  | _, _, s, _, .app f a => by simp [ofPure_subst s f, ofPure_subst s a]
  | _, _, s, _, .lam b => by simp [ofPure_subst (Sub.lift s) b, Sub.ofPure_lift]

theorem ofPure_instantiate {Γ : Ctx} {σ τ : Ty} (b : Term Signature.pure (σ :: Γ) τ)
    (a : Term Signature.pure Γ σ) :
    ofPure (Sig := Sig) (b.instantiate a) = (ofPure b).instantiate (ofPure a) := by
  simp only [Term.instantiate, ofPure_subst, Sub.ofPure_cons_id]

/-- The unfoldings are the same in every signature. -/
theorem unfoldR_ofPure : ∀ {Γ : Ctx} {σ : Ty} (a : Term Signature.pure Γ σ),
    (ofPure (Sig := Sig) a).unfoldR = a.unfoldR.map ofPure
  | _, _, .var _ | _, _, .and | _, _, .or
  | _, _, .not | _, _, .all _ | _, _, .ex _ | _, _, .eq _
  | _, _, .app _ _ | _, _, .lam _ => rfl
  | _, _, .const c => nomatch c
  | _, _, .constR ρ | _, _, .negR ρ | _, _, .andR ρ | _, _, .orR ρ
  | _, _, .coextR ρ | _, _, .boxR ρ | _, _, .inclR ρ => by cases ρ <;> rfl

end Term

/-! ### Conversion -/

theorem Beta.ofPure {Γ : Ctx} {σ : Ty} {a b : Term Signature.pure Γ σ} (h : Beta a b) :
    Beta (Term.ofPure (Sig := Sig) a) (Term.ofPure b) := by
  cases h with
  | intro b a =>
    show Beta (.app (.lam (Term.ofPure b)) (Term.ofPure a)) _
    rw [Term.ofPure_instantiate]
    exact Beta.intro _ _

theorem Eta.ofPure {Γ : Ctx} {σ : Ty} {a b : Term Signature.pure Γ σ} (h : Eta a b) :
    Eta (Term.ofPure (Sig := Sig) a) (Term.ofPure b) := by
  cases h with
  | intro f =>
    show Eta (.lam (.app (Term.ofPure f.weaken) (.var .zero))) (Term.ofPure f)
    rw [Term.ofPure_weaken]
    exact Eta.intro _

theorem Delta.ofPure {Γ : Ctx} {σ : Ty} {a b : Term Signature.pure Γ σ} (h : Delta a b) :
    Delta (Term.ofPure (Sig := Sig) a) (Term.ofPure b) := by
  unfold Delta at *
  rw [Term.unfoldR_ofPure, h]; rfl

theorem BetaEta.ofPure {Γ : Ctx} {σ : Ty} {a b : Term Signature.pure Γ σ} (h : BetaEta a b) :
    BetaEta (Term.ofPure (Sig := Sig) a) (Term.ofPure b) :=
  h.elim (fun h => Or.inl (Beta.ofPure h))
    (fun h => h.elim (fun h => Or.inr (Or.inl (Eta.ofPure h))) (fun h => Or.inr (Or.inr (Delta.ofPure h))))

theorem Step.ofPure : ∀ {Γ : Ctx} {σ : Ty} {a b : Term Signature.pure Γ σ}, Step BetaEta a b →
    Step BetaEta (Term.ofPure (Sig := Sig) a) (Term.ofPure b)
  | _, _, _, _, .here h => .here (BetaEta.ofPure h)
  | _, _, _, _, .appL h => .appL (Step.ofPure h)
  | _, _, _, _, .appR h => .appR (Step.ofPure h)
  | _, _, _, _, .lam h => .lam (Step.ofPure h)

theorem Conv.ofPure {Γ : Ctx} {σ : Ty} {a b : Term Signature.pure Γ σ} (h : a ≡ b) :
    Term.ofPure (Sig := Sig) a ≡ Term.ofPure b := by
  induction h with
  | rel h => exact EqvGen.rel (Step.ofPure h)
  | refl _ => exact EqvGen.refl _
  | symm _ ih => exact EqvGen.symm ih
  | trans _ _ ih₁ ih₂ => exact EqvGen.trans ih₁ ih₂

/-! ### Holes -/

namespace Hole

/-- A hole of the pure language, read in a signature. -/
def ofPure : ∀ {Γ Γ' : Ctx} {σ τ : Ty}, Hole Signature.pure Γ σ Γ' τ → Hole Sig Γ σ Γ' τ
  | _, _, _, _, .hole => .hole
  | _, _, _, _, .appL C b => .appL (ofPure C) (Term.ofPure b)
  | _, _, _, _, .appR f C => .appR (Term.ofPure f) (ofPure C)
  | _, _, _, _, .lam C => .lam (ofPure C)

theorem plug_ofPure : ∀ {Γ Γ' : Ctx} {σ τ : Ty} (C : Hole Signature.pure Γ σ Γ' τ)
    (a : Term Signature.pure Γ' τ), Term.ofPure (Sig := Sig) (C.plug a) = (ofPure C).plug (Term.ofPure a)
  | _, _, _, _, .hole, _ => rfl
  | _, _, _, _, .appL C b, a => by simp only [plug, ofPure, Term.ofPure_app, plug_ofPure C a]
  | _, _, _, _, .appR f C, a => by simp only [plug, ofPure, Term.ofPure_app, plug_ofPure C a]
  | _, _, _, _, .lam C, a => by simp only [plug, ofPure, Term.ofPure_lam, plug_ofPure C a]

end Hole

/-! ### Axiom sets and derivations -/

/-- An axiom set of the pure language, read in a signature: the same sentences. The
map's type-indexed principles at a signature `Σ` are `P.schema.ofPure`. -/
def AxiomSet.ofPure (Ax : AxiomSet Signature.pure) : AxiomSet Sig :=
  fun a => ∃ p, Ax p ∧ a = Term.ofPure p

theorem AxiomSet.mem_ofPure {Ax : AxiomSet Signature.pure} {p : Sentence Signature.pure} (h : Ax p) :
    Ax.ofPure (Sig := Sig) (Term.ofPure p) := ⟨p, h, rfl⟩

/-- `existence_e` is the same sentence in every signature, so the logical part is read
into the logical part. -/
theorem AxiomSet.logical_ofPure (Ax : AxiomSet Signature.pure) :
    ∀ a, (Ax.logical).ofPure (Sig := Sig) a → (Ax.ofPure).logical a
  | _, ⟨p, ⟨hp, hl⟩, e⟩ => ⟨⟨p, hp, e⟩, by subst e; rw [show p = existence_e from hl]; rfl⟩

theorem Hyps.map_ofPure_weaken {Γ : Ctx} {σ : Ty} (Δ : List (Formula Signature.pure Γ)) :
    (Hyps.weaken (σ := σ) Δ).map (Term.ofPure (Sig := Sig)) = Hyps.weaken (Δ.map Term.ofPure) := by
  simp only [Hyps.weaken, List.map_map]
  congr 1
  funext a
  exact Term.ofPure_weaken a

/-- **A derivation in the pure language is a derivation in every signature**, from the
same axioms read there. By induction on the derivation, as `rename` is; Subst's premises
are carried into the logical part by `logical_ofPure`. -/
theorem Derivable.ofPure : ∀ {Ax : AxiomSet Signature.pure} {Γ : Ctx}
    {Δ : List (Formula Signature.pure Γ)} {p : Formula Signature.pure Γ},
    Derivable Ax Δ p → Derivable (Ax.ofPure (Sig := Sig)) (Δ.map Term.ofPure) (Term.ofPure p)
  | _, _, _, _, hyp h => hyp (List.mem_map.2 ⟨_, h, rfl⟩)
  | _, _, _, _, ax (a := a) h => by rw [Term.ofPure_close]; exact ax ⟨a, h, rfl⟩
  | _, _, _, _, andI h₁ h₂ => andI (ofPure h₁) (ofPure h₂)
  | _, _, _, _, andE₁ h => andE₁ (ofPure h)
  | _, _, _, _, andE₂ h => andE₂ (ofPure h)
  | _, _, _, _, orI₁ h => orI₁ (ofPure h)
  | _, _, _, _, orI₂ h => orI₂ (ofPure h)
  | _, _, _, _, orE h h₁ h₂ => orE (ofPure h) (ofPure h₁) (ofPure h₂)
  | _, _, _, _, notI h₁ h₂ => notI (ofPure h₁) (ofPure h₂)
  | _, _, _, _, notE h₁ h₂ => notE (ofPure h₁) (ofPure h₂)
  | _, _, _, _, em p => em _
  | _, _, _, _, allE h a => allE (ofPure h) (Term.ofPure a)
  | _, _, _, _, exI a h => exI (Term.ofPure a) (ofPure h)
  | _, _, _, _, allI h => by
    have := ofPure h
    rw [Hyps.map_ofPure_weaken] at this
    exact allI this
  | _, _, Δ, _, exE (F := F) (r := q) h h' => by
    have this := ofPure h'
    have e : (Term.app F.weaken (.var .zero) :: Hyps.weaken Δ).map (Term.ofPure (Sig := Sig))
        = Term.app (Term.ofPure F).weaken (.var .zero) :: Hyps.weaken (Δ.map Term.ofPure) := by
      simp only [List.map_cons, Hyps.map_ofPure_weaken, Term.ofPure_app, Term.ofPure_var,
        Term.ofPure_weaken]
    rw [e, Term.ofPure_weaken] at this
    exact exE (ofPure h) this
  | _, _, _, _, refl a => refl _
  | _, _, _, _, ll F h₁ h₂ => ll (Term.ofPure F) (ofPure h₁) (ofPure h₂)
  | _, _, _, _, subst C h₁ h₂ h₃ => by
    have h₁' := ofPure h₁
    have h₂' := ofPure h₂
    have h₃' := ofPure h₃
    rw [Hole.plug_ofPure] at h₃' ⊢
    exact subst C.ofPure (mono (AxiomSet.logical_ofPure _) h₁') (mono (AxiomSet.logical_ofPure _) h₂') h₃'
  | _, _, _, _, conv h c => conv (ofPure h) (Conv.ofPure c)

theorem Theorem.ofPure {Ax : AxiomSet Signature.pure} {p : Sentence Signature.pure} (h : Theorem Ax p) :
    Theorem (Ax.ofPure (Sig := Sig)) (Term.ofPure p) :=
  Derivable.ofPure h

/-- The logical axioms of the pure language are logical axioms of every signature. -/
theorem logical_ofPure_subset :
    ∀ a, AxiomSet.ofPure (Meta.Logical (Sig := Signature.pure)) (Sig := Sig) a → Meta.Logical a
  | _, ⟨_, hl, e⟩ => by subst e; rw [show _ = existence_e from hl]; rfl

/-- **A theorem of `C` in the pure language is a theorem of `C` in every signature.** -/
theorem C.Theorem.ofPure {p : Sentence Signature.pure} (h : C.Theorem p) :
    C.Theorem (Sig := Sig) (Term.ofPure p) :=
  Derivable.mono logical_ofPure_subset (Derivable.ofPure h)

theorem C.TheoremMinus.ofPure {p : Sentence Signature.pure} (h : C.TheoremMinus p) :
    C.TheoremMinus (Sig := Sig) (Term.ofPure p) :=
  Derivable.mono (fun _ ⟨_, h, _⟩ => h.elim) (Derivable.ofPure h)

end Classicism.Meta
