import Classicism.Meta.Conversion

/-!
# Derivability

`Derivable Ax Δ p` says that the formula `p` is derivable from the hypotheses `Δ` in the
system `H` extended by the sentences in `Ax` as axioms. It is an inductive relation, so it
is *by definition* the smallest relation closed under the rules: the paper's notion of an
`H`-theory, "the smallest theory closed under those rules and containing all instances of
those axiom-schemes" (Classicism, §1.1), with the theory's own axioms as the parameter.
A proof of `Derivable Ax Δ p` is a derivation tree, built from the constructors below, and
that is all a derivation ever needs to be; see the README on why derivations are not a
separate datatype.

The rules are those of `H` in **natural-deduction form**, which is the form Lean's proof
terms have and the form the translator from strict proofs will emit. Hypotheses are a
list `Δ` beside the variable context `Γ`; a variable rule with an eigenvariable, `allI` and
`exE`, weakens every hypothesis into the extended context, which is the side condition
"`v` not free in the hypotheses" made structural.

* PC is the introduction and elimination rules for `∧`, `∨` and `¬`, with excluded middle,
  from which every tautology is derivable.
* UI and EG are `allE` and `exI`, with an arbitrary term `F : σ → t` in the quantifier's
  argument position, as the paper states them; Gen and Inst are `allI` and `exE`.
* Ref and LL are `refl` and `subst`.
* β and η are the single rule `conv`: a derivation transfers along conversion.
* The axioms of the theory are cited by `ax`, at any context, since they are sentences.

Nothing is a special rule. Classicism is `Derivable Classicism.axioms`, the eleven closed
identities of `Classicism/Meta/Axioms.lean` as the axiom set, and its closure under the
rule of Equivalence is a theorem to be proved, Appendix A.
-/

namespace Classicism.Meta

variable {Sig : Signature}

/-- The renaming from the empty context into any context. -/
def Ren.ofEmpty {Γ : Ctx} : Ren [] Γ := fun _ v => nomatch v

/-- A closed term, placed in a context. -/
abbrev Term.close {Γ : Ctx} {σ : Ty} (a : Term Sig [] σ) : Term Sig Γ σ := a.rename Ren.ofEmpty

/-- A list of hypotheses, weakened into a context with one more variable. -/
abbrev Hyps.weaken {Γ : Ctx} {σ : Ty} (Δ : List (Formula Sig Γ)) : List (Formula Sig (σ :: Γ)) :=
  Δ.map Term.weaken

/-- A set of axioms: a property of sentences. -/
abbrev AxiomSet (Sig : Signature) : Type := Sentence Sig → Prop

/-- Derivability in `H` plus the axioms `Ax`, from hypotheses `Δ`, in context `Γ`. -/
inductive Derivable (Ax : AxiomSet Sig) : ∀ {Γ : Ctx}, List (Formula Sig Γ) → Formula Sig Γ → Prop
  /-- A hypothesis. -/
  | hyp {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ} :
      p ∈ Δ → Derivable Ax Δ p
  /-- An axiom of the theory, at any context. -/
  | ax {Γ : Ctx} {Δ : List (Formula Sig Γ)} {a : Sentence Sig} :
      Ax a → Derivable Ax Δ a.close
  /-- `∧`-introduction. -/
  | andI {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      Derivable Ax Δ p → Derivable Ax Δ q → Derivable Ax Δ (Term.conj p q)
  /-- `∧`-elimination, left. -/
  | andE₁ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      Derivable Ax Δ (Term.conj p q) → Derivable Ax Δ p
  /-- `∧`-elimination, right. -/
  | andE₂ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      Derivable Ax Δ (Term.conj p q) → Derivable Ax Δ q
  /-- `∨`-introduction, left. -/
  | orI₁ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      Derivable Ax Δ p → Derivable Ax Δ (Term.disj p q)
  /-- `∨`-introduction, right. -/
  | orI₂ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      Derivable Ax Δ q → Derivable Ax Δ (Term.disj p q)
  /-- `∨`-elimination: by cases. -/
  | orE {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q r : Formula Sig Γ} :
      Derivable Ax Δ (Term.disj p q) → Derivable Ax (p :: Δ) r → Derivable Ax (q :: Δ) r →
      Derivable Ax Δ r
  /-- `¬`-introduction: what yields a contradiction is false. -/
  | notI {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      Derivable Ax (p :: Δ) q → Derivable Ax (p :: Δ) (Term.neg q) → Derivable Ax Δ (Term.neg p)
  /-- `¬`-elimination: from a contradiction, anything. -/
  | notE {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      Derivable Ax Δ p → Derivable Ax Δ (Term.neg p) → Derivable Ax Δ q
  /-- Excluded middle, which makes the propositional fragment classical. -/
  | em {Γ : Ctx} {Δ : List (Formula Sig Γ)} (p : Formula Sig Γ) :
      Derivable Ax Δ (Term.disj p (Term.neg p))
  /-- `UI`: `∀σ F → F A`, for any predicate term `F`. -/
  | allE {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σ : Ty} {F : Term Sig Γ (σ ⇒ RTy.t)} :
      Derivable Ax Δ (.app (.all σ) F) → (a : Term Sig Γ σ) → Derivable Ax Δ (.app F a)
  /-- `Gen`: from `b`, derived with a fresh variable and hypotheses not mentioning it,
  `∀v. b`. -/
  | allI {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σ : Ty} {b : Formula Sig (σ :: Γ)} :
      Derivable Ax (Hyps.weaken Δ) b → Derivable Ax Δ (Term.forall' b)
  /-- `EG`: `F A → ∃σ F`. -/
  | exI {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σ : Ty} {F : Term Sig Γ (σ ⇒ RTy.t)}
      (a : Term Sig Γ σ) : Derivable Ax Δ (.app F a) → Derivable Ax Δ (.app (.ex σ) F)
  /-- `Inst`: from `∃σ F`, and `r` derived from `F v` for a fresh `v`, `r`. -/
  | exE {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σ : Ty} {F : Term Sig Γ (σ ⇒ RTy.t)}
      {r : Formula Sig Γ} :
      Derivable Ax Δ (.app (.ex σ) F) →
      Derivable Ax (Term.app F.weaken (.var .zero) :: Hyps.weaken Δ) r.weaken →
      Derivable Ax Δ r
  /-- `Ref`: `A = A`. -/
  | refl {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σ : Ty} (a : Term Sig Γ σ) :
      Derivable Ax Δ (Term.eq' a a)
  /-- `LL`: from `A = B` and `F A`, `F B`. -/
  | subst {Γ : Ctx} {Δ : List (Formula Sig Γ)} {σ : Ty} {a b : Term Sig Γ σ}
      (F : Term Sig Γ (σ ⇒ RTy.t)) :
      Derivable Ax Δ (Term.eq' a b) → Derivable Ax Δ (.app F a) → Derivable Ax Δ (.app F b)
  /-- `β` and `η`: derivability transfers along conversion. -/
  | conv {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ} :
      Derivable Ax Δ p → p ≡ q → Derivable Ax Δ q

/-- `p` is a theorem of the theory `Ax`: derivable from no hypotheses, in the empty
context. -/
abbrev Theorem (Ax : AxiomSet Sig) (p : Sentence Sig) : Prop := Derivable Ax [] p

namespace Derivable

variable {Ax : AxiomSet Sig}

/-! ### Structural facts -/

theorem _root_.List.map_subset_of_subset {α β : Type} (f : α → β) {l l' : List α}
    (h : l ⊆ l') : l.map f ⊆ l'.map f := by
  intro x hx
  rw [List.mem_map] at hx ⊢
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨a, h ha, rfl⟩

/-- Weakening: more hypotheses derive no less. Admissible, by induction on the derivation;
the eigenvariable rules need that weakening commutes with the context extension. -/
theorem weaken : ∀ {Γ : Ctx} {Δ Δ' : List (Formula Sig Γ)} {p : Formula Sig Γ},
    Derivable Ax Δ p → Δ ⊆ Δ' → Derivable Ax Δ' p
  | _, _, _, _, hyp h, hs => hyp (hs h)
  | _, _, _, _, ax h, _ => ax h
  | _, _, _, _, andI h₁ h₂, hs => andI (weaken h₁ hs) (weaken h₂ hs)
  | _, _, _, _, andE₁ h, hs => andE₁ (weaken h hs)
  | _, _, _, _, andE₂ h, hs => andE₂ (weaken h hs)
  | _, _, _, _, orI₁ h, hs => orI₁ (weaken h hs)
  | _, _, _, _, orI₂ h, hs => orI₂ (weaken h hs)
  | _, _, _, _, orE h h₁ h₂, hs =>
    orE (weaken h hs) (weaken h₁ (List.cons_subset_cons _ hs)) (weaken h₂ (List.cons_subset_cons _ hs))
  | _, _, _, _, notI h₁ h₂, hs =>
    notI (weaken h₁ (List.cons_subset_cons _ hs)) (weaken h₂ (List.cons_subset_cons _ hs))
  | _, _, _, _, notE h₁ h₂, hs => notE (weaken h₁ hs) (weaken h₂ hs)
  | _, _, _, _, em p, _ => em p
  | _, _, _, _, allE h a, hs => allE (weaken h hs) a
  | _, _, _, _, allI h, hs => allI (weaken h (List.map_subset_of_subset _ hs))
  | _, _, _, _, exI a h, hs => exI a (weaken h hs)
  | _, _, _, _, exE h h', hs =>
    exE (weaken h hs) (weaken h' (List.cons_subset_cons _ (List.map_subset_of_subset _ hs)))
  | _, _, _, _, refl a, _ => refl a
  | _, _, _, _, subst F h₁ h₂, hs => subst F (weaken h₁ hs) (weaken h₂ hs)
  | _, _, _, _, conv h c, hs => conv (weaken h hs) c

/-- Hypotheses, renamed. -/
abbrev _root_.Classicism.Meta.Hyps.rename {Γ Δ : Ctx} (r : Ren Γ Δ) (Δ' : List (Formula Sig Γ)) :
    List (Formula Sig Δ) := Δ'.map (Term.rename r)

theorem _root_.Classicism.Meta.Hyps.weaken_rename {Γ Δ : Ctx} {σ : Ty} (r : Ren Γ Δ)
    (Δ' : List (Formula Sig Γ)) :
    Hyps.weaken (σ := σ) (Hyps.rename r Δ') = Hyps.rename (Ren.lift r) (Hyps.weaken Δ') := by
  simp only [Hyps.weaken, Hyps.rename, List.map_map]
  congr 1
  funext a
  exact Term.weaken_rename r a

/-- Renaming the variables: a derivation in one context gives a derivation in any context
it maps into. Admissible by induction; the eigenvariable rules lift the renaming. -/
theorem rename : ∀ {Γ Δ : Ctx} (r : Ren Γ Δ) {Δ' : List (Formula Sig Γ)} {p : Formula Sig Γ},
    Derivable Ax Δ' p → Derivable Ax (Hyps.rename r Δ') (p.rename r)
  | _, _, r, _, _, hyp h => hyp (List.mem_map.2 ⟨_, h, rfl⟩)
  | _, _, r, _, _, ax (a := a) h => by
    have : (Term.close a).rename r = Term.close a := by
      simp only [Term.close, Term.rename_rename]
      congr 1; funext σ v; exact nomatch v
    rw [this]; exact ax h
  | _, _, r, _, _, andI h₁ h₂ => andI (rename r h₁) (rename r h₂)
  | _, _, r, _, _, andE₁ h => andE₁ (rename r h)
  | _, _, r, _, _, andE₂ h => andE₂ (rename r h)
  | _, _, r, _, _, orI₁ h => orI₁ (rename r h)
  | _, _, r, _, _, orI₂ h => orI₂ (rename r h)
  | _, _, r, _, _, orE h h₁ h₂ => orE (rename r h) (rename r h₁) (rename r h₂)
  | _, _, r, _, _, notI h₁ h₂ => notI (rename r h₁) (rename r h₂)
  | _, _, r, _, _, notE h₁ h₂ => notE (rename r h₁) (rename r h₂)
  | _, _, r, _, _, em p => em _
  | _, _, r, _, _, allE h a => allE (rename r h) (a.rename r)
  | _, _, r, _, _, allI h => by
    have := rename (Ren.lift r) h
    rw [← Hyps.weaken_rename] at this
    exact allI this
  | _, _, r, _, _, exI a h => exI (a.rename r) (rename r h)
  | _, _, r, Δ', _, exE (σ := σ) (F := F) (r := q) h h' => by
    have this := rename (Ren.lift r) h'
    have e₁ : Hyps.rename (Ren.lift r) (Term.app F.weaken (.var .zero) :: Hyps.weaken Δ')
        = Term.app (F.rename r).weaken (.var .zero) :: Hyps.weaken (Hyps.rename r Δ') := by
      simp only [Hyps.rename, List.map_cons, Hyps.weaken_rename, Term.weaken_rename]
      rfl
    have e₂ : q.weaken.rename (Ren.lift r) = (q.rename r).weaken (τ := σ) :=
      (Term.weaken_rename (τ := σ) r q).symm
    rw [e₁, e₂] at this
    exact exE (rename r h) this
  | _, _, r, _, _, refl a => refl _
  | _, _, r, _, _, subst F h₁ h₂ => subst (F.rename r) (rename r h₁) (rename r h₂)
  | _, _, r, _, _, conv h c => conv (rename r h) (Conv.rename r c)

/-- A theorem holds in every context, from any hypotheses. -/
theorem ofTheorem {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Sentence Sig} (h : Theorem Ax p) :
    Derivable Ax Δ p.close :=
  weaken (rename Ren.ofEmpty h) (fun _ h => nomatch h)

/-- A hypothesis just added. -/
theorem hyp₀ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ} :
    Derivable Ax (p :: Δ) p := hyp (List.mem_cons_self ..)

/-- Add one hypothesis. -/
theorem weaken₁ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ}
    (h : Derivable Ax Δ p) : Derivable Ax (q :: Δ) p :=
  weaken h (List.subset_cons_self _ _)

/-- More axioms derive no less. -/
theorem mono {Ax' : AxiomSet Sig} (hA : ∀ a, Ax a → Ax' a) :
    ∀ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ},
      Derivable Ax Δ p → Derivable Ax' Δ p
  | _, _, _, hyp h => hyp h
  | _, _, _, ax h => ax (hA _ h)
  | _, _, _, andI h₁ h₂ => andI (mono hA h₁) (mono hA h₂)
  | _, _, _, andE₁ h => andE₁ (mono hA h)
  | _, _, _, andE₂ h => andE₂ (mono hA h)
  | _, _, _, orI₁ h => orI₁ (mono hA h)
  | _, _, _, orI₂ h => orI₂ (mono hA h)
  | _, _, _, orE h h₁ h₂ => orE (mono hA h) (mono hA h₁) (mono hA h₂)
  | _, _, _, notI h₁ h₂ => notI (mono hA h₁) (mono hA h₂)
  | _, _, _, notE h₁ h₂ => notE (mono hA h₁) (mono hA h₂)
  | _, _, _, em p => em p
  | _, _, _, allE h a => allE (mono hA h) a
  | _, _, _, allI h => allI (mono hA h)
  | _, _, _, exI a h => exI a (mono hA h)
  | _, _, _, exE h h' => exE (mono hA h) (mono hA h')
  | _, _, _, refl a => refl a
  | _, _, _, subst F h₁ h₂ => subst F (mono hA h₁) (mono hA h₂)
  | _, _, _, conv h c => conv (mono hA h) c

/-! ### The defined connectives

`→` is `¬p ∨ q` and `↔` a conjunction of two of those, so their rules are derived. -/

variable {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p q : Formula Sig Γ}

/-- `→`-introduction, by excluded middle on the antecedent. -/
theorem impI (h : Derivable Ax (p :: Δ) q) : Derivable Ax Δ (Term.imp p q) :=
  orE (em p) (orI₂ h) (orI₁ hyp₀)

/-- `→`-elimination, modus ponens. -/
theorem impE (h : Derivable Ax Δ (Term.imp p q)) (hp : Derivable Ax Δ p) : Derivable Ax Δ q :=
  orE h (notE (weaken₁ hp) hyp₀) hyp₀

theorem iffI (h₁ : Derivable Ax (p :: Δ) q) (h₂ : Derivable Ax (q :: Δ) p) :
    Derivable Ax Δ (Term.iff p q) :=
  andI (impI h₁) (impI h₂)

theorem iffE₁ (h : Derivable Ax Δ (Term.iff p q)) (hp : Derivable Ax Δ p) : Derivable Ax Δ q :=
  impE (andE₁ h) hp

theorem iffE₂ (h : Derivable Ax Δ (Term.iff p q)) (hq : Derivable Ax Δ q) : Derivable Ax Δ p :=
  impE (andE₂ h) hq

/-- `⊤` is a theorem of every theory: it is an instance of excluded middle. -/
theorem top : Derivable Ax Δ Term.top := em _

/-- From `⊥`, anything. -/
theorem botE (h : Derivable Ax Δ Term.bot) : Derivable Ax Δ p := notE (andE₁ h) (andE₂ h)

/-- Symmetry of identity, from `Ref` and `LL` at the predicate `λz. z = a`. -/
theorem eqSymm {σ : Ty} {a b : Term Sig Γ σ} (h : Derivable Ax Δ (Term.eq' a b)) :
    Derivable Ax Δ (Term.eq' b a) :=
  have h₁ : Derivable Ax Δ (.app (.lam (Term.eq' (.var .zero) a.weaken)) b) :=
    subst (.lam (Term.eq' (.var .zero) a.weaken)) h
      (conv (refl a) (Conv.symm (by
        have := Conv.beta (Sig := Sig) (Γ := Γ) (Term.eq' (.var .zero) a.weaken) a
        simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using this)))
  conv h₁ (by
    have := Conv.beta (Sig := Sig) (Γ := Γ) (Term.eq' (.var .zero) a.weaken) b
    simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using this)

/-! ### Leibniz's Law in the forms the translator meets

The strict layer's proofs are equational: Lean's `congrArg`, `Eq.trans`, `Eq.symm`,
`Eq.mpr` and `congrFun` are each `LL` at a particular predicate, and these are their
derivations. Each ends in a `conv` that β-reduces the predicate's application. -/

/-- The conversion `(λz. B) a ≡ B[a]`, for use in the rules below. -/
theorem _root_.Classicism.Meta.Conv.beta' {σ : Ty} {ρ : RTy} (b : Term Sig (σ :: Γ) ρ)
    (a : Term Sig Γ σ) : Term.app (.lam b) a ≡ b.instantiate a := Conv.beta b a

/-- Transitivity: from `a = b` and `b = c`, `a = c`, by `LL` at `λz. a = z`. -/
theorem eqTrans {σ : Ty} {a b c : Term Sig Γ σ} (h₁ : Derivable Ax Δ (Term.eq' a b))
    (h₂ : Derivable Ax Δ (Term.eq' b c)) : Derivable Ax Δ (Term.eq' a c) :=
  have h : Derivable Ax Δ (.app (.lam (Term.eq' a.weaken (.var .zero))) c) :=
    subst (.lam (Term.eq' a.weaken (.var .zero))) h₂ (conv h₁ (Conv.symm (by
      have := Conv.beta' (Sig := Sig) (Γ := Γ) (Term.eq' a.weaken (.var .zero)) b
      simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using this)))
  conv h (by
    have := Conv.beta' (Sig := Sig) (Γ := Γ) (Term.eq' a.weaken (.var .zero)) c
    simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using this)

/-- Congruence: from `a = b`, `F a = F b`, by `LL` at `λz. F a = F z`. This is Lean's
`congrArg`. -/
theorem eqCongr {σ : Ty} {ρ : RTy} (F : Term Sig Γ (σ ⇒ ρ)) {a b : Term Sig Γ σ}
    (h : Derivable Ax Δ (Term.eq' a b)) :
    Derivable Ax Δ (Term.eq' (.app F a) (.app F b)) :=
  have h' : Derivable Ax Δ (.app (.lam (Term.eq' (.app F.weaken a.weaken) (.app F.weaken (.var .zero)))) b) :=
    subst _ h (conv (refl (.app F a)) (Conv.symm (by
      have := Conv.beta' (Sig := Sig) (Γ := Γ)
        (Term.eq' (.app F.weaken a.weaken) (.app F.weaken (.var .zero))) a
      simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using this)))
  conv h' (by
    have := Conv.beta' (Sig := Sig) (Γ := Γ)
      (Term.eq' (.app F.weaken a.weaken) (.app F.weaken (.var .zero))) b
    simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using this)

/-- From `f = g`, `f a = g a`, by `LL` at `λz. f a = z a`. This is Lean's `congrFun`. -/
theorem eqCongrFun {σ : Ty} {ρ : RTy} {f g : Term Sig Γ (σ ⇒ ρ)}
    (h : Derivable Ax Δ (Term.eq' f g)) (a : Term Sig Γ σ) :
    Derivable Ax Δ (Term.eq' (.app f a) (.app g a)) :=
  have h' : Derivable Ax Δ (.app (.lam (Term.eq' (.app f.weaken a.weaken) (.app (.var .zero) a.weaken))) g) :=
    subst _ h (conv (refl (.app f a)) (Conv.symm (by
      have := Conv.beta' (Sig := Sig) (Γ := Γ)
        (Term.eq' (.app f.weaken a.weaken) (.app (.var .zero) a.weaken)) f
      simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using this)))
  conv h' (by
    have := Conv.beta' (Sig := Sig) (Γ := Γ)
      (Term.eq' (.app f.weaken a.weaken) (.app (.var .zero) a.weaken)) g
    simpa [Term.instantiate, Term.subst_rename, Term.subst_id] using this)

/-- From `p = q` and `p`, `q`: `LL` at the identity predicate `λz. z`. Lean's `Eq.mp`. -/
theorem eqMp {p q : Formula Sig Γ} (h : Derivable Ax Δ (Term.eq' p q)) (hp : Derivable Ax Δ p) :
    Derivable Ax Δ q :=
  conv (subst (.lam (.var .zero)) h (conv hp (Conv.symm (Conv.beta' (.var .zero) p))))
    (Conv.beta' (.var .zero) q)

/-- From `p = q` and `q`, `p`. Lean's `Eq.mpr`. -/
theorem eqMpr {p q : Formula Sig Γ} (h : Derivable Ax Δ (Term.eq' p q)) (hq : Derivable Ax Δ q) :
    Derivable Ax Δ p :=
  eqMp (eqSymm h) hq

/-! ### The same rules, with the β-redex contracted

Lean's typing of an application substitutes, so the type of `h a` is the instantiated
body, where the rule `allE` yields the application `F a`. These variants conclude with
`instantiate`, which computes to the same tree the quoter reads from Lean's type, so no
conversion step is needed at the use site; the kernel evaluates the substitution. -/

theorem allEβ {σ : Ty} {b : Formula Sig (σ :: Γ)} (h : Derivable Ax Δ (Term.forall' b))
    (a : Term Sig Γ σ) : Derivable Ax Δ (b.instantiate a) :=
  conv (allE h a) (Conv.beta' b a)

theorem exIβ {σ : Ty} {b : Formula Sig (σ :: Γ)} (a : Term Sig Γ σ)
    (h : Derivable Ax Δ (b.instantiate a)) : Derivable Ax Δ (Term.exists' b) :=
  exI a (conv h (Conv.symm (Conv.beta' b a)))

theorem substβ {σ : Ty} {a b : Term Sig Γ σ} (P : Formula Sig (σ :: Γ))
    (h₁ : Derivable Ax Δ (Term.eq' a b)) (h₂ : Derivable Ax Δ (P.instantiate a)) :
    Derivable Ax Δ (P.instantiate b) :=
  conv (subst (.lam P) h₁ (conv h₂ (Conv.symm (Conv.beta' P a)))) (Conv.beta' P b)

theorem eqCongrβ {σ : Ty} {ρ : RTy} (B : Term Sig (σ :: Γ) ρ) {a b : Term Sig Γ σ}
    (h : Derivable Ax Δ (Term.eq' a b)) :
    Derivable Ax Δ (Term.eq' (B.instantiate a) (B.instantiate b)) :=
  have h' := eqCongr (.lam B) h
  conv h' (Conv.app_congr (Conv.app_congr (Conv.refl _) (Conv.beta' B a)) (Conv.beta' B b))

theorem eqCongrFunβ {σ : Ty} {ρ : RTy} {b₁ b₂ : Term Sig (σ :: Γ) ρ}
    (h : Derivable Ax Δ (Term.eq' (Term.lam b₁) (Term.lam b₂))) (a : Term Sig Γ σ) :
    Derivable Ax Δ (Term.eq' (b₁.instantiate a) (b₂.instantiate a)) :=
  have h' := eqCongrFun h a
  conv h' (Conv.app_congr (Conv.app_congr (Conv.refl _) (Conv.beta' b₁ a)) (Conv.beta' b₂ a))

end Derivable

end Classicism.Meta
