import Classicism.Tools.QuoteTerm
import Classicism.Principles.Comprehension
import Classicism.Coalesced.StoneRigidity
import Classicism.Coalesced.StoneCurrent

/-!
# The native inexact ordinals in the Stone fan

The definitions through `Ordinal` reproduce the October 2026 PR 28 verification
by OpenAI Codex, prompted by Andrew Bacon, in the files
`MathematicalContingency/{Definitions,CarrierTheory,InductiveOrdinals}.lean`.
The quotation tool reflects these definitions into the action model's deep syntax.
The current-row and leaf-uniformity theorems concern this quoted predicate.
-/

namespace Classicism.StoneOrdinal

variable {σ : Type} [Ty σ]

def StrictOrderOn {σ : Type} [Ty σ] (A : σ → Prop) (L : σ → σ → Prop) : Prop :=
  (∀ x y, L x y → A x ∧ A y) ∧
  (∀ x, A x → ¬ L x x) ∧
  (∀ x y z, A x → A y → A z → L x y → L y z → L x z) ∧
  (∀ x y, A x → A y → x = y ∨ L x y ∨ L y x)
def WellOrderOn {σ : Type} [Ty σ] (A : σ → Prop) (L : σ → σ → Prop) : Prop :=
  StrictOrderOn A L ∧ ∀ X : σ → Prop, (∀ x, X x → A x) → (∃ x, X x) →
    ∃ x, X x ∧ ∀ y, X y → ¬ L y x
def Segment {σ : Type} [Ty σ] (A : σ → Prop) (L : σ → σ → Prop) (a : σ) : σ → Prop :=
  fun x => A x ∧ L x a
def RestrictOrder (L : σ → σ → Prop) (A : σ → Prop) : σ → σ → Prop :=
  fun x y => A x ∧ A y ∧ L x y

abbrev OrdinalCarrier (σ : Type) := (σ → σ → Prop) → (σ → Prop) → Prop
def OrdZero (σ : Type) [Ty σ] : OrdinalCarrier σ := fun R A => WellOrderOn A R
def OrdSuc (α : OrdinalCarrier σ) : OrdinalCarrier σ := fun R A =>
  WellOrderOn A R ∧ ∃ a, A a ∧ α (RestrictOrder R (Segment A R a)) (Segment A R a)
def OrdLim (Y : OrdinalCarrier σ → Prop) : OrdinalCarrier σ := fun R A =>
  WellOrderOn A R ∧ ∀ β, Y β → β R A
def OrdClosed (Z : OrdinalCarrier σ → Prop) : Prop :=
  Z (OrdZero σ) ∧ (∀ α, Z α → Z (OrdSuc α)) ∧
    ∀ Y, Rigid Y → (∀ β, Y β → Z β) → Z (OrdLim Y)
def Ordinal (α : OrdinalCarrier σ) : Prop := ∀ Z, OrdClosed Z → Z α

def RigidFamily (Y : OrdinalCarrier σ → Prop) : Prop := Rigid Y

end Classicism.StoneOrdinal

#classicism_quote_term Classicism.StoneOrdinal.OrdZero Classicism.StoneOrdinal.OrdSuc
  Classicism.StoneOrdinal.OrdLim Classicism.StoneOrdinal.OrdClosed Classicism.StoneOrdinal.Ordinal
  Classicism.StoneOrdinal.RigidFamily

namespace Classicism.Meta.Coalesced.StoneFan.Ordinals

noncomputable section

open CategoryTheory Classicism.Meta.Intensional

abbrev unary (σ : Ty) : RTy := .arr σ .t
abbrev binary (σ : Ty) : RTy := .arr σ (.arr σ .t)
abbrev carrier (σ : Ty) : RTy := .arr (.rel (binary σ)) (.arr (.rel (unary σ)) .t)

/-- Extract the body for use with an assigned native parameter. The terms used
below are checked by reduction to be lambda abstractions. -/
private def body {Sig : Signature} {Γ : Ctx} {σ : Ty} {ρ : RTy} :
    Term Sig Γ (.rel (.arr σ ρ)) → Term Sig (σ :: Γ) (.rel ρ)
  | .lam p => p
  | _ => Term.botR ρ

variable {Sig : Signature} {σ : Ty}

abbrev zeroTerm (σ : Ty) : Term Sig [] (carrier σ) :=
  Term.ofPure (Classicism.StoneOrdinal.OrdZero.term σ)

abbrev succTerm (σ : Ty) : Term Sig [.rel (carrier σ)] (carrier σ) :=
  body (Term.ofPure (Classicism.StoneOrdinal.OrdSuc.term σ))

abbrev limTerm (σ : Ty) : Term Sig [.rel (unary (.rel (carrier σ)))] (carrier σ) :=
  body (Term.ofPure (Classicism.StoneOrdinal.OrdLim.term σ))

abbrev ordinalFormula (σ : Ty) : Formula Sig [.rel (carrier σ)] :=
  body (Term.ofPure (Classicism.StoneOrdinal.Ordinal.term σ))

abbrev closedFormula (σ : Ty) : Formula Sig [.rel (unary (.rel (carrier σ)))] :=
  body (Term.ofPure (Classicism.StoneOrdinal.OrdClosed.term σ))

private theorem ordinal_body (σ : Ty) :
    Term.ofPure (Sig := Sig) (Classicism.StoneOrdinal.Ordinal.term σ) = .lam (ordinalFormula σ) := rfl

/-- Closure and the actual ordinal property are calculated in the full deep
language, with a separate identity of denotation for each term's shallow source. -/
private theorem ordinalFormula_def (σ : Ty) :
    ordinalFormula (Sig := Sig) σ =
      Term.forall' (Term.imp ((closedFormula σ).rename (Ren.lift (Ren.shift (Γ := []) (σ := .rel (carrier σ)))))
        (.app (.var .zero) (.var (.succ .zero)))) := rfl

private def emptyRen (Γ : Ctx) : Ren [] Γ := fun _ v => nomatch v

private abbrev openAt {η τ : Ty} {Γ : Ctx} (t : Term Sig [η] τ) : Term Sig (η :: Γ) τ :=
  t.rename (Ren.lift (emptyRen Γ))

abbrev rigidFormula (σ : Ty) : Formula Sig [.rel (unary (.rel (carrier σ)))] :=
  body (Term.ofPure (Classicism.StoneOrdinal.RigidFamily.term σ))



private theorem closedFormula_def (σ : Ty) :
    closedFormula (Sig := Sig) σ =
      Term.conj (.app (.var .zero) (zeroTerm σ).close)
        (Term.conj (Term.forall' (Term.imp (.app (.var (.succ .zero)) (.var .zero))
          (.app (.var (.succ .zero)) (openAt (succTerm σ)))))
          (Term.forall' (Term.imp (openAt (rigidFormula σ)) (Term.imp
            (Term.forall' (Term.imp (.app (.var (.succ .zero)) (.var .zero))
              (.app (.var (.succ (.succ .zero))) (.var .zero))))
            (.app (.var (.succ .zero)) (openAt (limTerm σ))))))) := rfl

variable {K : Type} [SmallCategory K] (B : Premodel Sig K) (M : B.IsModel)
    {W : K} (h : B.W₀ ⟶ W)

abbrev current {η : Ty} (Z : B.Dom W (.rel (unary η))) (a : B.Dom W η) :=
  (a, PUnit.unit) ∈ (B.incl _ W Z).ext' B.inner

include M

/-- The quoted impredicative ordinal predicate tests exactly the admitted
families satisfying its actual closure formula. -/
theorem holds_ordinal (a : B.Dom W (.rel (carrier σ))) :
    B.Holds h (ordinalFormula σ) (.cons a .nil) ↔
      ∀ Z : B.Dom W (.rel (unary (.rel (carrier σ)))),
        B.Holds h (closedFormula σ) (.cons Z .nil) → current B Z a := by
  rw [ordinalFormula_def, B.holds_forall M]
  constructor <;> intro H Z <;> specialize H Z
  · apply (B.holds_imp M _ _ _ _).1 at H
    intro hZ
    apply (Premodel.holds_app_var1 (A := B) h (.cons Z (.cons a .nil)) .zero (.succ .zero)).1
    apply H
    unfold Premodel.Holds at *
    rwa [B.sem_rename]
  · apply (B.holds_imp M _ _ _ _).2
    intro hZ
    apply (Premodel.holds_app_var1 (A := B) h (.cons Z (.cons a .nil)) .zero (.succ .zero)).2
    apply H
    unfold Premodel.Holds at *
    rwa [B.sem_rename] at hZ

/-- Denotation chosen from the model's actual domain by its term-closure condition. -/
noncomputable def value {Γ : Ctx} {τ : Ty} (q : Term Sig Γ τ) (g : IEnv (B.Dom W) Γ) : B.Dom W τ :=
  Classical.choose (M h q g)

theorem incl_value {Γ : Ctx} {τ : Ty} (q : Term Sig Γ τ) (g : IEnv (B.Dom W) Γ) :
    B.Incl τ W (value B M h q g) = B.sem h q g :=
  Classical.choose_spec (M h q g)

private theorem value_var {Γ : Ctx} {η : Ty} (g : IEnv (B.Dom W) Γ) (v : Var Γ η) :
    value B M h (.var v) g = g.get v :=
  B.Incl_injective η W (incl_value B M h (.var v) g)

private theorem current_app {Γ : Ctx} {η : Ty} (g : IEnv (B.Dom W) Γ)
    (Z : Var Γ (.rel (unary η))) (t : Term Sig Γ η) :
    B.Holds h (.app (.var Z) t) g ↔ current B (g.get Z) (value B M h t g) :=
  B.holds_app h g _ _ (incl_value B M h t g)

private theorem value_open {η τ : Ty} {Γ : Ctx} (t : Term Sig [η] τ)
    (a : B.Dom W η) (g : IEnv (B.Dom W) Γ) :
    value B M h (openAt t) (.cons a g) = value B M h t (.cons a .nil) := by
  apply B.Incl_injective τ W
  rw [incl_value, incl_value, openAt, B.sem_rename]
  rfl

private theorem value_close {τ : Ty} {Γ : Ctx} (t : Term Sig [] τ) (g : IEnv (B.Dom W) Γ) :
    value B M h t.close g = value B M h t .nil := by
  apply B.Incl_injective τ W
  rw [incl_value, incl_value, B.sem_close]

/-- Native realization of the three closure clauses. -/
theorem holds_closed (Z : B.Dom W (.rel (unary (.rel (carrier σ))))) :
    B.Holds h (closedFormula σ) (.cons Z .nil) ↔
      current B Z (value B M h (zeroTerm σ) .nil) ∧
      (∀ a, current B Z a → current B Z (value B M h (succTerm σ) (.cons a .nil))) ∧
      ∀ Y, B.Holds h (rigidFormula σ) (.cons Y .nil) →
        (∀ a, current B Y a → current B Z a) →
          current B Z (value B M h (limTerm σ) (.cons Y .nil)) := by
  rw [closedFormula_def]
  simp only [B.holds_conj M, B.holds_forall M, B.holds_imp M,
    current_app B M h, value_var B M h, value_open B M h, value_close B M h, IEnv.get, current]
  apply and_congr_right
  intro _
  apply and_congr_right
  intro _
  apply forall_congr'
  intro Y
  unfold Premodel.Holds
  rw [openAt, B.sem_rename]
  rfl

private abbrev pointTest {Γ : Ctx} {η : Ty} (y z : Var Γ (.rel (unary η))) : Formula Sig Γ :=
  Term.forall' (Term.imp (.app (.var (.succ y)) (.var .zero))
    (Term.box (.app (.var (.succ z)) (.var .zero))))

private abbrev pointIncl {Γ : Ctx} {η : Ty} (y z : Var Γ (.rel (unary η))) : Formula Sig Γ :=
  Term.forall' (Term.imp (.app (.var (.succ y)) (.var .zero))
    (.app (.var (.succ z)) (.var .zero)))

private theorem pointTest_iff {Γ : Ctx} {η : Ty} (g : IEnv (B.Dom W) Γ) (y z : Var Γ (.rel (unary η))) :
    B.Holds h (pointTest y z) g ↔ B.Holds h (UnaryRigid.test (.var y) (.var z)) g := by
  rw [UnaryRigid.holds_test B M h g _ _ (g.get y) (g.get z) rfl rfl]
  simp only [pointTest, B.holds_forall M, B.holds_imp M, Premodel.holds_app_var1, B.holds_box M,
    IEnv.get_map, IEnv.get, Intension.ext', B.incl_map, Intension.mem_map, Category.comp_id]
  rfl

private theorem pointIncl_iff {Γ : Ctx} {η : Ty} (g : IEnv (B.Dom W) Γ) (y z : Var Γ (.rel (unary η))) :
    B.Holds h (pointIncl y z) g ↔ B.Holds h (UnaryRigid.incl (.var y) (.var z)) g := by
  simp only [pointIncl, B.holds_forall M, B.holds_imp M, Premodel.holds_app_var1, IEnv.get,
    UnaryRigid.incl, Premodel.holds_inclR M]
  constructor
  · intro H
    rintro ⟨b, ⟨⟩⟩
    exact H b
  · intro H b
    exact H (b, PUnit.unit)

/-- In every native action model the quoted PR 28 occurrence of rigidity agrees
with the map's primitive inclusion-and-box presentation. -/
theorem holds_rigid (Y : B.Dom W (.rel (unary (.rel (carrier σ))))) :
    B.Holds h (rigidFormula σ) (.cons Y .nil) ↔
      B.Holds h UnaryRigid.rigid (.cons Y .nil) := by
  change B.Holds h (Term.conj (Term.box (pointTest .zero .zero))
    (Term.box (Term.forall' (Term.imp (pointTest (.succ .zero) .zero)
      (Term.box (pointIncl (.succ .zero) .zero)))))) (.cons Y .nil) ↔ _
  simp only [UnaryRigid.rigid, UnaryRigid.persistent, UnaryRigid.inextensible, B.holds_conj M,
    B.holds_box M, B.holds_forall M, B.holds_imp M, ← pointTest_iff B M, ← pointIncl_iff B M]

/-- At a point admitting the designated current test set Q, induction under the
actual deep ordinal definition may use Q. No global extension fullness is needed. -/
theorem ordinal_induction_at (Q : B.Dom W (.rel (carrier σ)) → Prop)
    (represented : ∃ Z, ∀ a, current B Z a ↔ Q a)
    (hz : Q (value B M h (zeroTerm σ) .nil))
    (hs : ∀ a, Q a → Q (value B M h (succTerm σ) (.cons a .nil)))
    (hl : ∀ Y, B.Holds h UnaryRigid.rigid (.cons Y .nil) →
      (∀ a, current B Y a → Q a) → Q (value B M h (limTerm σ) (.cons Y .nil)))
    (a : B.Dom W (.rel (carrier σ))) (ha : B.Holds h (ordinalFormula σ) (.cons a .nil)) : Q a := by
  obtain ⟨Z, hZ⟩ := represented
  apply (hZ a).1
  apply (holds_ordinal B M h a).1 ha Z
  apply (holds_closed B M h Z).2
  refine ⟨(hZ _).2 hz, fun b hb => (hZ _).2 (hs b ((hZ _).1 hb)), ?_⟩
  intro Y hy hall
  exact (hZ _).2 (hl Y ((holds_rigid B M h Y).1 hy) (fun b hb => (hZ b).1 (hall b hb)))

/-- The current row of a curried binary relation on two (possibly distinct) sorts. -/
abbrev row₂ {η δ : Ty} (u : B.Dom W (.rel (.arr η (.arr δ .t))))
    (a : B.Dom W η) (b : B.Dom W δ) : Prop :=
  (a, b, PUnit.unit) ∈ (B.incl _ W u).ext' B.inner

private theorem current_lam {Γ : Ctx} {η : Ty} (g : IEnv (B.Dom W) Γ) (t : Formula Sig (η :: Γ))
    (a : B.Dom W η) : current B (value B M h (.lam t) g) a ↔ B.Holds h t (.cons a g) := by
  change (⟨W, (a, PUnit.unit), 𝟙 W⟩ : Tuple B.inner (unary η) W) ∈ B.Incl (.rel (unary η)) W (value B M h (.lam t) g) ↔ _
  rw [incl_value, B.mem_sem_lam, Category.comp_id, B.push_id]
  rfl

private theorem row₂_lam {Γ : Ctx} {η δ : Ty} (g : IEnv (B.Dom W) Γ) (t : Formula Sig (δ :: η :: Γ))
    (a : B.Dom W η) (b : B.Dom W δ) :
    row₂ B (value B M h (.lam (.lam t)) g) a b ↔ B.Holds h t (.cons b (.cons a g)) := by
  change (⟨W, (a, b, PUnit.unit), 𝟙 W⟩ : Tuple B.inner (.arr η (.arr δ .t)) W) ∈ B.Incl (.rel (.arr η (.arr δ .t))) W (value B M h (.lam (.lam t)) g) ↔ _
  rw [incl_value, B.mem_sem_lam, Category.comp_id, B.push_id, B.mem_sem_lam, Category.comp_id, B.push_id]
  rfl

private theorem current_app₂ {Γ : Ctx} {η δ : Ty} (g : IEnv (B.Dom W) Γ)
    (R : Var Γ (.rel (.arr η (.arr δ .t)))) (u : Term Sig Γ η) (v : Term Sig Γ δ) :
    B.Holds h (.app (.app (.var R) u) v) g ↔
      row₂ B (g.get R) (value B M h u g) (value B M h v g) := by
  rw [B.holds_app h g _ _ (incl_value B M h v g)]
  change _ ∈ B.apply (B.Incl _ W (g.get R)) (B.sem h u g) ↔ _
  rw [← incl_value B M h u g, B.apply_Incl]
  simp [Intension.ext', Intension.mem_app, row₂]
  rfl

/-- The actual application of an ordinal candidate depends only on the current
extensions of its order and field, independently of their possible intensions. -/
def CurrentExtensional (a : B.Dom W (.rel (carrier σ))) : Prop :=
  ∀ (F G : B.Dom W (.rel (unary σ))) (P Q : B.Dom W (.rel (binary σ))),
    (B.incl _ W F).ext' B.inner = (B.incl _ W G).ext' B.inner →
    (B.incl _ W P).ext' B.inner = (B.incl _ W Q).ext' B.inner →
    (row₂ B a P F ↔ row₂ B a Q G)

private abbrev woBody (σ : Ty) : Formula Sig [.rel (unary σ), .rel (binary σ)] :=
  body (body (zeroTerm σ))

private theorem holds_wellOrder_congr (F G : B.Dom W (.rel (unary σ))) (P Q : B.Dom W (.rel (binary σ)))
    (hF : (B.incl _ W F).ext' B.inner = (B.incl _ W G).ext' B.inner)
    (hP : (B.incl _ W P).ext' B.inner = (B.incl _ W Q).ext' B.inner) :
    B.Holds h (woBody σ) (.cons F (.cons P .nil)) ↔
      B.Holds h (woBody σ) (.cons G (.cons Q .nil)) := by
  dsimp only [woBody, zeroTerm, Classicism.StoneOrdinal.OrdZero.term, Term.ofPure_lam, body]
  simp only [Term.ofPure_app, Term.ofPure_var, Term.ofPure_lam, Term.ofPure_and, Term.ofPure_not,
    Term.ofPure_or, Term.ofPure_all, Term.ofPure_ex, Term.ofPure_eq, B.holds_conj M,
    B.holds_forall M, B.holds_imp M, B.holds_disj M, B.holds_neg M, B.holds_exists M,
    Premodel.holds_eq_var M, Premodel.holds_app_var1, Premodel.holds_app_var2, IEnv.get, hF, hP]

private theorem zero_extensional :
    CurrentExtensional B (value B M h (zeroTerm σ) .nil) := by
  intro F G P Q hf hp
  have termEq : zeroTerm (Sig := Sig) σ = Term.lam (Term.lam (woBody σ)) := rfl
  rw [termEq, row₂_lam, row₂_lam]
  exact holds_wellOrder_congr B M h F G P Q hf hp

private abbrev sucBody (σ : Ty) : Formula Sig [.rel (unary σ), .rel (binary σ), .rel (carrier σ)] :=
  body (body (succTerm σ))

private theorem succ_extensional (a : B.Dom W (.rel (carrier σ))) (ha : CurrentExtensional B a) :
    CurrentExtensional B (value B M h (succTerm σ) (.cons a .nil)) := by
  intro F G P Q hf hp
  have termEq : succTerm (Sig := Sig) σ = Term.lam (Term.lam (sucBody σ)) := rfl
  rw [termEq, row₂_lam, row₂_lam]
  dsimp only [sucBody, succTerm, Classicism.StoneOrdinal.OrdSuc.term, Term.ofPure_lam, body]
  simp only [Term.ofPure_app, Term.ofPure_var, Term.ofPure_lam, Term.ofPure_and, Term.ofPure_not,
    Term.ofPure_or, Term.ofPure_all, Term.ofPure_ex, Term.ofPure_eq, B.holds_conj M,
    B.holds_forall M, B.holds_imp M, B.holds_disj M, B.holds_neg M, B.holds_exists M,
    Premodel.holds_eq_var M, current_app₂ B M h, Premodel.holds_app_var1, IEnv.get, value_var B M h,
    row₂, hf, hp]
  apply and_congr_right
  intro _
  apply exists_congr
  intro x
  apply and_congr_right
  intro _
  apply ha
  · ext y
    obtain ⟨y, ⟨⟩⟩ := y
    change current B _ y ↔ current B _ y
    rw [current_lam, current_lam]
    simp only [B.holds_conj M, Premodel.holds_app_var1, Premodel.holds_app_var2, IEnv.get, hf, hp]
  · ext y
    obtain ⟨a, b, ⟨⟩⟩ := y
    change row₂ B _ a b ↔ row₂ B _ a b
    rw [row₂_lam, row₂_lam]
    simp only [B.holds_conj M, Premodel.holds_app_var1, Premodel.holds_app_var2, IEnv.get, hf, hp]

private abbrev limBody (σ : Ty) :
    Formula Sig [.rel (unary σ), .rel (binary σ), .rel (unary (.rel (carrier σ)))] :=
  body (body (limTerm σ))

private theorem limit_extensional (Y : B.Dom W (.rel (unary (.rel (carrier σ)))))
    (hy : ∀ a, current B Y a → CurrentExtensional B a) :
    CurrentExtensional B (value B M h (limTerm σ) (.cons Y .nil)) := by
  intro F G P Q hf hp
  have termEq : limTerm (Sig := Sig) σ = Term.lam (Term.lam (limBody σ)) := rfl
  rw [termEq, row₂_lam, row₂_lam]
  dsimp only [limBody, limTerm, Classicism.StoneOrdinal.OrdLim.term, Term.ofPure_lam, body]
  simp only [Term.ofPure_app, Term.ofPure_var, Term.ofPure_lam, Term.ofPure_and, Term.ofPure_not,
    Term.ofPure_or, Term.ofPure_all, Term.ofPure_ex, Term.ofPure_eq, B.holds_conj M,
    B.holds_forall M, B.holds_imp M, B.holds_disj M, B.holds_neg M, B.holds_exists M,
    Premodel.holds_eq_var M, Premodel.holds_app_var1, Premodel.holds_app_var2, IEnv.get, hf, hp]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro a
  exact imp_congr_right fun ha => hy a ha F G P Q hf hp

omit M

section Fan

variable {ι : Type} {C : ι → Type} [∀ k, SmallCategory (C k)]
  (A : ∀ k, Premodel Sig (C k)) (L : ι → Type) (leaf : ι) [TopologicalSpace (L leaf)]
  (m : ∀ k, (A k).IsModel)

local notation "F" => model A L leaf
local notation "R" => action A L leaf
local notation "w" => CoalescedSum.base (arrows A L)
local notation "mF" => isModel A L leaf m

include m

/-- The distinguished leaf values of a term in the chosen model are determined
by the transported values of its parameters there. -/
private theorem leaf_value {Γ : Ctx} {ρ : RTy} (t : Term Sig Γ (.rel ρ))
    (g : IEnv (R).D Γ) (x : L leaf) :
    (A leaf).incl ρ _ (profile A L leaf (value F mF (𝟙 w) t g) leaf x) =
      (A leaf).sem (𝟙 _) t (g.map fun η => (R).tr η (baseArrow A L leaf x)) := by
  let ri := selIncl (atom A L .e) (fun i => atom A L (.var i)) (sel A L leaf)
  have ht := ri.incl_tr ρ (baseArrow A L leaf x) (value F mF (𝟙 w) t g)
  have hv := incl_value F mF (𝟙 w) t g
  change ri.incl ρ (value F mF (𝟙 w) t g) = _ at hv
  rw [hv] at ht
  exact ht.trans ((StoneLeaves.transport_sem (baseArrow A L leaf) (fun _ _ => rfl) _ _ _ _
    PUnit.unit t g x).trans ((A leaf).rebase_sem_congr
      (funext fun c => tr_lift A L leaf _ (fun k => (A k).I c) leaf x) (𝟙 _) t _))

/-- In every Stone fan all actual native inexact ordinals have the same value
at all homogeneous leaves. The constructed root provides the impredicative
test, and native inextensibility discharges the limit clause. -/
theorem ordinal_leaf_uniform (a : (R).D (.rel (carrier σ)))
    (ha : (F).Holds (𝟙 w) (ordinalFormula σ) (.cons a .nil)) :
    ∀ x z : L leaf, profile A L leaf a leaf x = profile A L leaf a leaf z := by
  let Q (b : (R).D (.rel (carrier σ))) :=
    ∀ x z : L leaf, profile A L leaf b leaf x = profile A L leaf b leaf z
  apply ordinal_induction_at F mF (𝟙 w) Q _ _ _ _ a ha
  · let E : Set (Args (F).inner (unary (.rel (carrier σ))) w) := {v | Q v.1}
    obtain ⟨Z, hZ⟩ := current_ext_full A L leaf m _ E
    refine ⟨Z, fun b => ?_⟩
    unfold current
    rw [hZ]
    rfl
  · intro x z
    apply (A leaf).incl_injective _ _
    exact (leaf_value A L leaf m (zeroTerm σ) .nil x).trans
      (leaf_value A L leaf m (zeroTerm σ) .nil z).symm
  · intro b hb x z
    apply (A leaf).incl_injective _ _
    have e : IEnv.map (fun η => (R).tr η (baseArrow A L leaf x)) (.cons b .nil) =
        IEnv.map (fun η => (R).tr η (baseArrow A L leaf z)) (.cons b .nil) :=
      congrArg (fun q => IEnv.cons q .nil) (hb x z)
    exact (leaf_value A L leaf m (succTerm σ) (.cons b .nil) x).trans
      ((congrArg (fun env => (A leaf).sem (𝟙 _) (succTerm σ) env) e).trans
        (leaf_value A L leaf m (succTerm σ) (.cons b .nil) z).symm)
  · intro Y hy hm x z
    apply (A leaf).incl_injective _ _
    have hY := rigid_uniform_family A L leaf m Y hy (fun b hb => hm b hb) x z
    have e : IEnv.map (fun η => (R).tr η (baseArrow A L leaf x)) (.cons Y .nil) =
        IEnv.map (fun η => (R).tr η (baseArrow A L leaf z)) (.cons Y .nil) :=
      congrArg (fun q => IEnv.cons q .nil) hY
    exact (leaf_value A L leaf m (limTerm σ) (.cons Y .nil) x).trans
      ((congrArg (fun env => (A leaf).sem (𝟙 _) (limTerm σ) env) e).trans
        (leaf_value A L leaf m (limTerm σ) (.cons Y .nil) z).symm)

/-- Every actual inexact ordinal also depends only on the current extensions
of its order and field. This theorem and leaf uniformity give the two defining
conditions of the ordinal bounding set in the Stone construction. -/
theorem ordinal_current_extensional (a : (R).D (.rel (carrier σ)))
    (ha : (F).Holds (𝟙 w) (ordinalFormula σ) (.cons a .nil)) : CurrentExtensional (σ := σ) (W := w) F a := by
  apply ordinal_induction_at F mF (𝟙 w) (CurrentExtensional (σ := σ) (W := w) F) _ (zero_extensional F mF (𝟙 w))
    (succ_extensional F mF (𝟙 w)) (fun Y _ => limit_extensional F mF (𝟙 w) Y) a ha
  let E : Set (Args (F).inner (unary (.rel (carrier σ))) w) := {v | CurrentExtensional (σ := σ) (W := w) F v.1}
  obtain ⟨Z, hZ⟩ := current_ext_full A L leaf m _ E
  refine ⟨Z, fun b => ?_⟩
  unfold current
  rw [hZ]
  rfl

#print axioms ordinal_current_extensional
#print axioms ordinal_induction_at
#print axioms ordinal_leaf_uniform

end Fan

end

end Classicism.Meta.Coalesced.StoneFan.Ordinals
