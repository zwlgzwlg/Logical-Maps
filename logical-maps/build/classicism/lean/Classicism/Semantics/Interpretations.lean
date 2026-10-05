import Classicism.Semantics.IntensionalTheory
import Classicism.Syntax.WitnessedPossibility

/-!
# Interpreting the signature: constants with pure definitions

A model of the pure language becomes a model of a signature `Σ` once each constant of `Σ` is
given a value in the domain at the base (`Premodel.interp`). The map's models interpret `Σ`
by one of two conventions (`Background`, "Interpretation of Σ"). This file is the first,
**`Σ` by tops**: every constant is relational and denotes the top element of its type
(`Premodel.SigmaTop`, the map's condition `sigma-top`).

The tool is **substitution of definitions for constants** (`Term.substConsts`). When each
constant `c` denotes, at the base, what a closed pure term `f c` denotes there, then every
term of `Σ` denotes, at every arrow and under every assignment, what the pure term with each
`c` replaced by `f c` denotes (`sem_substConsts`). Two consequences:

- the premodel is a model as soon as its pure reduct is (`isModel_of_definitions`): the
  interpretation adds nothing a pure term could not already denote. So the reinterpretation
  `B.withTop M` of any model `B` of the pure language, with one constant of type `t` denoting
  `⊤` (`Signature.sigmaTop`, admitted), is a model (`withTop_isModel`);
- a sentence of `Σ` holds iff the pure sentence with the definitions substituted does
  (`holdsSentence_substConsts`), so No Pure Contingency gives No Contingency relative to `Σ`
  (`holdsAx_nc_of_definitions`): the map's argument `sigma-top-npc`.

And with `Σ` by tops, Independence relative to `Σ` fails at `c ≠ ⊤_ρ`, the closed pure term
`⊤_ρ` denoting what `c` does (`not_holdsAx_independence_of_sigmaTop`): the map's argument
`sigma-top`.
-/

namespace Classicism.Meta

namespace Term

variable {Sig : Signature}

/-- Replace each constant `c` by the closed pure term `f c`. Through `Term.rec`, as `ofPure`
is, for the kernel's sake. -/
noncomputable def substConsts (f : ∀ c : Sig.Const, Term Signature.pure [] (Sig.typeOf c)) :
    ∀ {Γ : Ctx} {σ : Ty}, Term Sig Γ σ → Term Signature.pure Γ σ :=
  fun {_ _} t =>
    Term.rec (motive := fun Γ σ _ => Term Signature.pure Γ σ)
      (var := fun v => Term.var v)
      (const := fun c => (f c).rename Ren.ofEmpty)
      (app := fun _ _ f a => Term.app f a)
      (lam := fun _ b => Term.lam b)
      (and := Term.and) (or := Term.or) (not := Term.not)
      (all := fun σ => Term.all σ) (ex := fun σ => Term.ex σ) (eq := fun σ => Term.eq σ)
      (constR := fun ρ => Term.constR ρ) (negR := fun ρ => Term.negR ρ)
      (andR := fun ρ => Term.andR ρ) (orR := fun ρ => Term.orR ρ)
      (coextR := fun ρ => Term.coextR ρ) (boxR := fun ρ => Term.boxR ρ)
      (inclR := fun ρ => Term.inclR ρ)
      t

theorem ofPure_topR {Γ : Ctx} (ρ : RTy) :
    Term.ofPure (Sig := Sig) (Γ := Γ) (Term.topR ρ) = Term.topR ρ := rfl

theorem cast_closedTypes_const {Γ : Ctx} (c : Sig.Const) {τ : Ty} (h : Sig.typeOf c = τ) :
    (h ▸ Term.const c : Term Sig Γ τ).closedTypes = decide τ.Closed := by
  subst h; rfl

variable (f : ∀ c : Sig.Const, Term Signature.pure [] (Sig.typeOf c))

/-- Substitution keeps a term in the paper's language when each definition of a constant of
closed type is. -/
theorem closedTypes_substConsts (hf : ∀ c, (Sig.typeOf c).Closed → (f c).closedTypes = true) :
    ∀ {Γ : Ctx} {σ : Ty} (t : Term Sig Γ σ), t.closedTypes = true → (t.substConsts f).closedTypes = true
  | _, _, .var _, h | _, _, .and, h | _, _, .or, h | _, _, .not, h | _, _, .all _, h
  | _, _, .ex _, h | _, _, .eq _, h | _, _, .constR _, h | _, _, .negR _, h | _, _, .andR _, h
  | _, _, .orR _, h | _, _, .coextR _, h | _, _, .boxR _, h | _, _, .inclR _, h => h
  | _, _, .const c, h => by
    show ((f c).rename Ren.ofEmpty).closedTypes = true
    rw [closedTypes_rename]
    exact hf c (by simpa [closedTypes] using h)
  | _, _, .app g a, h => by
    simp only [closedTypes, Bool.and_eq_true] at h
    show (Term.app (g.substConsts f) (a.substConsts f)).closedTypes = true
    simp only [closedTypes, Bool.and_eq_true]
    exact ⟨closedTypes_substConsts hf g h.1, closedTypes_substConsts hf a h.2⟩
  | _, _, .lam b, h => by
    simp only [closedTypes, Bool.and_eq_true] at h
    show (Term.lam (b.substConsts f)).closedTypes = true
    simp only [closedTypes, Bool.and_eq_true]
    exact ⟨h.1, closedTypes_substConsts hf b h.2⟩

end Term

namespace Intensional

open CategoryTheory

variable {Sig : Signature} {C : Type} [SmallCategory C]

namespace Premodel

/-! ### Reinterpreting a model of the pure language -/

/-- A premodel of the pure language with the constants of `Sig` given the values `I`. -/
abbrev interp (B : Premodel Signature.pure C) (Sig : Signature)
    (I : ∀ c : Sig.Const, B.Dom B.W₀ (Sig.typeOf c)) : Premodel Sig C where
  W₀ := B.W₀
  inner := B.inner
  nonempty_e := B.nonempty_e
  incl := B.incl
  incl_map := B.incl_map
  incl_injective := B.incl_injective
  I := I

theorem interp_Incl (B : Premodel Signature.pure C) (Sig : Signature)
    (I : ∀ c : Sig.Const, B.Dom B.W₀ (Sig.typeOf c)) :
    ∀ (σ : Ty) (W : C) (x : B.Dom W σ), (B.interp Sig I).Incl σ W x = B.Incl σ W x
  | .e, _, _ => rfl
  | .rel _, _, _ => rfl
  | .var _, _, _ => rfl

theorem interp_apply (B : Premodel Signature.pure C) (Sig : Signature)
    (I : ∀ c : Sig.Const, B.Dom B.W₀ (Sig.typeOf c)) {σ : Ty} {ρ : RTy} {W : C}
    (F : Intension B.inner (.arr σ ρ) W) (x : Outer B.inner σ W) :
    (B.interp Sig I).apply F x = B.apply F x := by
  ext p
  simp only [apply, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨x', h1, h2⟩
  · exact ⟨x', (B.interp_Incl Sig I _ _ x').symm.trans h1, h2⟩
  · exact ⟨x', (B.interp_Incl Sig I _ _ x').trans h1, h2⟩

/-- Its reduct is the model reinterpreted. -/
theorem reduct_interp (B : Premodel Signature.pure C) (Sig : Signature)
    (I : ∀ c : Sig.Const, B.Dom B.W₀ (Sig.typeOf c)) : (B.interp Sig I).reduct = B :=
  (rfl : _ = B.reduct).trans (reduct_pure B)

/-- A principle at every signature holds in the reinterpretation iff it holds in the model. -/
theorem holdsAx_interp_ofPure {B : Premodel Signature.pure C} {Sig : Signature}
    {I : ∀ c : Sig.Const, B.Dom B.W₀ (Sig.typeOf c)} {Ax : AxiomSet Signature.pure} :
    (B.interp Sig I).HoldsAx (AxiomSet.ofPure Ax) ↔ B.HoldsAx (AxiomSet.ofPure Ax) := by
  rw [holdsAx_ofPure, holdsAx_ofPure, reduct_interp, reduct_pure]

/-! ### Definitions of the constants -/

section definitions

variable (B : Premodel Signature.pure C) {Sig : Signature}
  (I : ∀ c : Sig.Const, B.Dom B.W₀ (Sig.typeOf c)) (f : ∀ c : Sig.Const, Term Signature.pure [] (Sig.typeOf c))

/-- Each constant denotes, at the base, what its definition `f c`, a closed pure term,
denotes. -/
def Definitions : Prop :=
  ∀ c, B.Incl _ _ (I c) = B.sem (𝟙 B.W₀) (f c) .nil

variable {B I f}

/-- Then at every arrow: both sides are carried along it alike (`sem_push`). -/
theorem Definitions.at (hD : B.Definitions I f) (c : Sig.Const) {W : C} (h : B.W₀ ⟶ W) :
    B.Incl _ W ((B.inner _).map h (I c)) = B.sem h (f c) .nil := by
  have H := B.sem_push (𝟙 B.W₀) (f c) .nil h
  rw [IEnv.nil_eq (B.push h .nil), Category.id_comp] at H
  rw [B.Incl_map, hD c, H]

/-- **A term of `Σ` denotes what the pure term with the definitions substituted denotes.** -/
theorem sem_substConsts (hD : B.Definitions I f) :
    ∀ {Γ : Ctx} {σ : Ty} {W : C} (h : B.W₀ ⟶ W) (t : Term Sig Γ σ) (g : IEnv (B.Dom W) Γ),
      (B.interp Sig I).sem h t g = B.sem h (t.substConsts f) g
  | _, _, _, _, .var v, g => B.interp_Incl Sig I _ _ (g.get v)
  | _, _, _, h, .const c, g => by
    show (B.interp Sig I).Incl _ _ ((B.inner _).map h (I c)) = B.sem h ((f c).rename Ren.ofEmpty) g
    rw [interp_Incl, B.sem_rename, IEnv.nil_eq (IEnv.ren _ _)]
    exact hD.at c h
  | _, _, _, h, .app t a, g => by
    show (B.interp Sig I).apply ((B.interp Sig I).sem h t g) ((B.interp Sig I).sem h a g) =
      B.apply (B.sem h (t.substConsts f) g) (B.sem h (a.substConsts f) g)
    rw [sem_substConsts hD h t g, sem_substConsts hD h a g, interp_apply]
  | _, _, _, h, .lam b, g => by
    ext p
    show _ ∈ (B.interp Sig I).sem (h ≫ p.2.2) b _ ↔ _ ∈ B.sem (h ≫ p.2.2) (b.substConsts f) _
    rw [sem_substConsts hD _ b]
  | _, _, _, _, .and, _ | _, _, _, _, .or, _ | _, _, _, _, .not, _ | _, _, _, _, .all _, _
  | _, _, _, _, .ex _, _ | _, _, _, _, .eq _, _ | _, _, _, _, .constR _, _
  | _, _, _, _, .negR _, _ | _, _, _, _, .andR _, _ | _, _, _, _, .orR _, _
  | _, _, _, _, .coextR _, _ | _, _, _, _, .boxR _, _ | _, _, _, _, .inclR _, _ => rfl

/-- **The reinterpretation of a model, its constants given pure definitions, is a model**: the
interpretation adds nothing a pure term could not already denote. -/
theorem isModel_interp (hD : B.Definitions I f) (M : B.IsModel) : (B.interp Sig I).IsModel :=
  fun h t g => by
    obtain ⟨x, hx⟩ := M h (t.substConsts f) g
    exact ⟨x, (B.interp_Incl Sig I _ _ x).trans (hx.trans (sem_substConsts hD h t g).symm)⟩

theorem holdsSentence_substConsts (hD : B.Definitions I f) (p : Sentence Sig) :
    (B.interp Sig I).HoldsSentence p ↔ B.HoldsSentence (p.substConsts f) := by
  unfold HoldsSentence Holds
  rw [sem_substConsts hD]

/-- **No Pure Contingency gives No Contingency relative to `Σ`**, when each constant of closed
type has a definition in the paper's language: a sentence of `Σ` is necessary iff the pure
sentence with the definitions substituted is. -/
theorem holdsAx_nc_of_definitions (hD : B.Definitions I f)
    (hf : ∀ c, (Sig.typeOf c).Closed → (f c).closedTypes = true)
    (hN : B.HoldsAx (AxiomSet.noContingency Signature.pure)) :
    (B.interp Sig I).HoldsAx (AxiomSet.noContingency Sig) := by
  rintro _ ⟨hc, p, rfl⟩
  rw [holdsSentence_substConsts hD]
  exact hN _ ⟨Term.closedTypes_substConsts f hf _ hc, _, rfl⟩

end definitions

/-! ### `Σ` by tops -/

/-- `sigma-top`: every constant of `Σ` is relational and denotes the top element of its type. -/
def SigmaTop (A : Premodel Sig C) : Prop :=
  ∀ c, ∃ (ρ : RTy) (e : Sig.typeOf c = .rel ρ),
    A.HoldsSentence (Term.eq' (e ▸ Term.const c : Term Sig [] (.rel ρ)) (Term.topR ρ))

/-- The signature of one constant of type `t`, read as `⊤` under `sigma-top`. -/
def _root_.Classicism.Meta.Signature.sigmaTop : Signature := ⟨Unit, fun _ => .rel .t⟩

theorem _root_.Classicism.Meta.Signature.sigmaTop_admitted : Signature.sigmaTop.Admitted :=
  ⟨fun _ => trivial, ⟨(), fun h => nomatch h⟩⟩

/-- The top proposition at the base of a model. -/
noncomputable def topProp {B : Premodel Signature.pure C} (M : B.IsModel) : B.Dom B.W₀ (.rel .t) :=
  Classical.choose (M (𝟙 B.W₀) (Term.topR .t) .nil)

theorem incl_topProp {B : Premodel Signature.pure C} (M : B.IsModel) :
    B.Incl _ _ (topProp M) = B.sem (𝟙 B.W₀) (Term.topR .t) .nil :=
  Classical.choose_spec (M (𝟙 B.W₀) (Term.topR .t) .nil)

/-- **A model of the pure language, with `Σ` a constant of type `t` denoting `⊤`.** -/
noncomputable abbrev withTop (B : Premodel Signature.pure C) (M : B.IsModel) :
    Premodel Signature.sigmaTop C :=
  B.interp Signature.sigmaTop fun _ => topProp M

/-- The constant's definition: `⊤`. -/
def topDef : ∀ c : Signature.sigmaTop.Const, Term Signature.pure [] (Signature.sigmaTop.typeOf c) :=
  fun _ => Term.topR .t

theorem withTop_definitions {B : Premodel Signature.pure C} (M : B.IsModel) :
    B.Definitions (fun _ => topProp M) topDef := fun _ => incl_topProp M

theorem withTop_isModel {B : Premodel Signature.pure C} (M : B.IsModel) : (B.withTop M).IsModel :=
  isModel_interp (withTop_definitions M) M

theorem withTop_sigmaTop {B : Premodel Signature.pure C} (M : B.IsModel) : (B.withTop M).SigmaTop :=
  fun c => ⟨.t, rfl, by
    rw [HoldsSentence, (B.withTop M).holds_eq (withTop_isModel M),
      sem_substConsts (withTop_definitions M), sem_substConsts (withTop_definitions M)]
    show B.sem _ ((Term.topR .t).rename Ren.ofEmpty) .nil = B.sem _ (Term.topR .t) .nil
    rw [B.sem_rename, IEnv.nil_eq (IEnv.ren _ _)]⟩

/-! ### The arguments `sigma-top` and `sigma-top-npc` -/

/-- Under `sigma-top`, the constants' definitions: `⊤` at their types. -/
noncomputable def topDefs {A : Premodel Sig C} (hT : A.SigmaTop) :
    ∀ c : Sig.Const, Term Signature.pure [] (Sig.typeOf c) :=
  fun c => (hT c).choose_spec.choose.symm ▸ Term.topR (hT c).choose

section sigmaTop

variable {A : Premodel Sig C} (M : A.IsModel)
include M

omit M in
theorem cast_definition {τ : Ty} {ρ : RTy} (e : τ = .rel ρ) (t : Term Sig [] τ)
    (s : Term Signature.pure [] (.rel ρ)) (x : A.Dom A.W₀ τ) (hx : A.sem (𝟙 A.W₀) t .nil = A.Incl τ _ x)
    (hs : A.sem (𝟙 A.W₀) (e ▸ t) .nil = A.reduct.sem (𝟙 A.W₀) s .nil) :
    A.reduct.Incl τ _ x = A.reduct.sem (𝟙 A.W₀) (e.symm ▸ s) .nil := by
  subst e
  exact (A.reduct_Incl _ _ x).trans (hx.symm.trans hs)

omit M in
theorem cast_closedTypes {Γ : Ctx} {τ : Ty} {ρ : RTy} (e : τ = .rel ρ) (s : Term Signature.pure Γ (.rel ρ)) :
    (e.symm ▸ s : Term Signature.pure Γ τ).closedTypes = s.closedTypes := by
  subst e; rfl

theorem topDefs_definitions (hT : A.SigmaTop) : A.reduct.Definitions A.I (topDefs hT) := fun c => by
  have H := (A.holds_eq M _ _ _ _).1 (hT c).choose_spec.choose_spec
  refine cast_definition _ (Term.const c) _ (A.I c) ?_ (H.trans (A.sem_ofPure (𝟙 _) (Term.topR _) .nil))
  show A.Incl _ _ ((A.inner _).map (𝟙 _) (A.I c)) = _
  rw [CategoryTheory.Functor.map_id]; rfl

theorem topDefs_closedTypes (hT : A.SigmaTop) (c : Sig.Const) (hc : (Sig.typeOf c).Closed) :
    (topDefs hT c).closedTypes = true := by
  unfold topDefs
  rw [cast_closedTypes (hT c).choose_spec.choose]
  have hρ : (hT c).choose.Closed := by
    have := (hT c).choose_spec.choose
    rw [this] at hc; exact hc
  simp [Term.closedTypes, hρ]

/-- **`sigma-top-npc`: No Contingency relative to `Σ`** holds where `Σ` is interpreted by tops
and No Pure Contingency holds. -/
theorem holdsAx_nc_of_sigmaTop (hT : A.SigmaTop)
    (hN : A.HoldsAx (AxiomSet.ofPure (AxiomSet.noContingency Signature.pure))) :
    A.HoldsAx (AxiomSet.noContingency Sig) :=
  holdsAx_nc_of_definitions (B := A.reduct) (topDefs_definitions M hT) (topDefs_closedTypes M hT)
    ((holdsAx_ofPure A _).1 hN)

/-- **`sigma-top`: Independence relative to `Σ` fails**: `c ≠ ⊤_ρ` is an instance, `⊤_ρ`
being a closed pure term, and `c = ⊤_ρ` holds. -/
theorem not_holdsAx_independence_of_sigmaTop (hS : Sig.Admitted) (hT : A.SigmaTop) :
    ¬ A.HoldsAx (AxiomSet.independence Sig) := by
  obtain ⟨c, -⟩ := hS.2
  obtain ⟨ρ, e, H⟩ := hT c
  have hc : (Sig.typeOf c).Closed := hS.1 c
  have hρ : ρ.Closed := by rw [e] at hc; exact hc
  intro hI
  have := hI (Term.neg (Term.eq' (e ▸ Term.const c) (Term.appBlock (Term.ofPure (Term.topR ρ))
    (Terms.consts [])))) ⟨by
      have h1 : (e ▸ Term.const c : Term Sig [] (.rel ρ)).closedTypes = true := by
        rw [Term.cast_closedTypes_const c e]; simpa using hρ
      have h2 : (Term.ofPure (Sig := Sig) (Γ := []) (Term.topR ρ)).closedTypes = true := by
        rw [Term.closedTypes_ofPure]; simp [Term.closedTypes, hρ]
      show (Term.neg (Term.eq' (e ▸ Term.const c : Term Sig [] (.rel ρ))
        (Term.ofPure (Term.topR ρ)))).closedTypes = true
      simp only [Term.closedTypes, h1, h2, Bool.and_true, Bool.true_and,
        decide_eq_true_eq]
      exact hρ,
    c, [], ρ, e, Term.topR ρ, List.nodup_singleton c, rfl⟩
  exact (A.holds_neg M _ _ _).1 this H

end sigmaTop

end Premodel

end Intensional

end Classicism.Meta
