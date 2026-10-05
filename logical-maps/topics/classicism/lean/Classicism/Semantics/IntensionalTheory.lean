import Classicism.Semantics.IntensionalFacts
import Classicism.Syntax.ClosedTypes
import Classicism.Syntax.Pure
import Classicism.Syntax.Conservativity

/-!
# The theory of a model, and models of the pure language

What a model's verdicts need in order to become the map's statements about it.

- **The theory of a model** (`theory`): the sentences holding in it. In an intensional
  action model it is consistent (`theory_consistent`) and complete (`theory_complete`), and it
  entails a schema iff the schema holds in the model (`theory_entails_iff`). So a model of an
  admitted signature satisfying `S₁, …, Sₘ` and violating `V₁, …, Vₖ` gives the map's model
  statement, `∃ Sig Ax, Consistent Ax ∧ Complete Ax ∧ Entails Ax S₁ ∧ … ∧ ¬ Entails Ax V₁ ∧ …`,
  with `Ax` its theory (`entails_of_holdsAx`, `not_entails_of_not_holdsAx`).
- **The pure reduct** (`reduct`): the same premodel with the constants forgotten. A pure
  sentence read in the signature holds iff it holds in the reduct (`holdsSentence_ofPure`),
  so a principle given at every signature as `P.X.schemaIn` holds in a model iff its pure
  schema holds in the reduct (`holdsAx_ofPure`). For a premodel of the pure language the
  reduct is the premodel itself (`reduct_pure`), which is how the verdicts proved for the
  models of `Models/` are read as verdicts on the map's principles (`holdsAx_schemaIn_iff`).
-/

namespace Classicism.Meta.Intensional

open CategoryTheory

variable {Sig : Signature} {C : Type} [SmallCategory C]

namespace Premodel

variable (A : Premodel Sig C)

/-- The theory of a premodel: the sentences holding in it. -/
def theory : AxiomSet Sig := fun p => A.HoldsSentence p

/-- The premodel's signature is one the map's statements range over: its constants have
closed types and one has a type other than `e`. -/
@[nolint unusedArguments]
def Admitted (_A : Premodel Sig C) : Prop := Sig.Admitted

section theory

variable {A} (M : A.IsModel)
include M

/-- The theory of a model is consistent with Classicism. -/
theorem theory_consistent : A.theory.Consistent :=
  AxiomSet.Consistent.of_model A M fun _ h => h

/-- The theory of a model is complete: it contains each sentence or its negation. -/
theorem theory_complete : A.theory.Complete := fun p _ =>
  (em (A.HoldsSentence p)).imp Theorem.ax fun h => Theorem.ax ((A.holdsSentence_neg M p).2 h)

/-- The theory of a model entails a schema iff the schema holds in the model. -/
theorem theory_entails_iff (D : AxiomSet Sig) : AxiomSet.Entails A.theory D ↔ A.HoldsAx D :=
  ⟨fun e => A.entails_holds M e fun _ h => h, fun h a ha => Theorem.ax (h a ha)⟩

theorem entails_of_holdsAx {D : AxiomSet Sig} (h : A.HoldsAx D) : AxiomSet.Entails A.theory D :=
  (theory_entails_iff M D).2 h

theorem not_entails_of_not_holdsAx {D : AxiomSet Sig} (h : ¬ A.HoldsAx D) :
    ¬ AxiomSet.Entails A.theory D :=
  fun e => h ((theory_entails_iff M D).1 e)

end theory

/-! ### The pure reduct -/

/-- The pure reduct: the same premodel, its constants forgotten. -/
def reduct : Premodel Signature.pure C where
  W₀ := A.W₀
  inner := A.inner
  nonempty_e := A.nonempty_e
  incl := A.incl
  incl_map := A.incl_map
  incl_injective := A.incl_injective
  I := fun c => nomatch c

theorem reduct_Incl : ∀ (σ : Ty) (W : C) (x : A.Dom W σ), A.reduct.Incl σ W x = A.Incl σ W x
  | .e, _, _ => rfl
  | .rel _, _, _ => rfl
  | .var _, _, _ => rfl

theorem reduct_apply {σ : Ty} {ρ : RTy} {W : C} (F : Intension A.inner (.arr σ ρ) W)
    (x : Outer A.inner σ W) : A.reduct.apply F x = A.apply F x := by
  ext p
  simp only [apply, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨x', h1, h2⟩
  · exact ⟨x', (A.reduct_Incl _ _ x').symm.trans h1, h2⟩
  · exact ⟨x', (A.reduct_Incl _ _ x').trans h1, h2⟩

/-- A pure term read in the signature has the value it has in the reduct. -/
theorem sem_ofPure : ∀ {Γ : Ctx} {σ : Ty} {W : C} (h : A.W₀ ⟶ W) (t : Term Signature.pure Γ σ)
    (g : IEnv (A.Dom W) Γ), A.sem h (Term.ofPure t) g = A.reduct.sem h t g
  | _, _, _, _, .var v, g => (A.reduct_Incl _ _ (g.get v)).symm
  | _, _, _, _, .const c, _ => nomatch c
  | _, _, _, h, .app f a, g => by
    rw [Term.ofPure_app]
    simp only [sem]
    rw [sem_ofPure h f g, sem_ofPure h a g]
    exact (A.reduct_apply _ _).symm
  | _, _, _, h, .lam b, g => by
    rw [Term.ofPure_lam]
    simp only [sem]
    ext p
    simp only [Set.mem_ofPred_eq]
    rw [sem_ofPure _ b]
    rfl
  | _, _, _, _, .and, _ => rfl
  | _, _, _, _, .or, _ => rfl
  | _, _, _, _, .not, _ => rfl
  | _, _, _, _, .all _, _ => rfl
  | _, _, _, _, .ex _, _ => rfl
  | _, _, _, _, .eq _, _ => rfl
  | _, _, _, _, .constR _, _ => rfl
  | _, _, _, _, .negR _, _ => rfl
  | _, _, _, _, .andR _, _ => rfl
  | _, _, _, _, .orR _, _ => rfl
  | _, _, _, _, .coextR _, _ => rfl
  | _, _, _, _, .boxR _, _ => rfl
  | _, _, _, _, .inclR _, _ => rfl

theorem holdsSentence_ofPure (p : Sentence Signature.pure) :
    A.HoldsSentence (Term.ofPure p) ↔ A.reduct.HoldsSentence p := by
  unfold HoldsSentence Holds
  rw [sem_ofPure]
  rfl

/-- A pure schema read in the signature holds in a premodel iff it holds in the reduct. -/
theorem holdsAx_ofPure (Ax : AxiomSet Signature.pure) :
    A.HoldsAx (AxiomSet.ofPure Ax) ↔ A.reduct.HoldsAx Ax :=
  ⟨fun h p hp => (A.holdsSentence_ofPure p).1 (h _ ⟨p, hp, rfl⟩),
   fun h _ ⟨p, hp, e⟩ => e ▸ (A.holdsSentence_ofPure p).2 (h p hp)⟩

/-- The reduct of a model is a model: the value of a pure term in it is the value of the term
read in the signature, which is inner. -/
theorem reduct_isModel (M : A.IsModel) : A.reduct.IsModel := fun h t g => by
  obtain ⟨x, hx⟩ := M h (Term.ofPure t) g
  exact ⟨x, (A.reduct_Incl _ _ x).trans (hx.trans (A.sem_ofPure h t g))⟩

/-- A premodel of the pure language is its own reduct. -/
theorem reduct_pure (B : Premodel Signature.pure C) : B.reduct = B := by
  cases B
  simp only [reduct, mk.injEq, heq_eq_eq, true_and]
  funext c
  exact nomatch c

/-- In a premodel of the pure language, a principle at every signature, `P.X.schemaIn`,
holds iff its schema does. -/
theorem holdsAx_schemaIn_iff (B : Premodel Signature.pure C) (Ax : AxiomSet Signature.pure) :
    B.HoldsAx (AxiomSet.ofPure Ax) ↔ B.HoldsAx Ax := by
  rw [holdsAx_ofPure, reduct_pure]

end Premodel

end Classicism.Meta.Intensional
