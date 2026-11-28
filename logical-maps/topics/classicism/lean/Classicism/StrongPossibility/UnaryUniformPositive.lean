import Classicism.StrongPossibility.PermanentSemantics
import Classicism.StrongPossibility.UnaryLicences
import Classicism.Semantics.IntensionalFull
import Mathlib.CategoryTheory.SingleObj

/-! At the ordinary descriptor root every pair of distinct individuals can
become permanently distinct. Each individual is a name, and a classical
model can interpret all the individual names distinctly. -/

noncomputable section
namespace Classicism.Meta.UnarySP
open CategoryTheory Intensional Coalesced DistinguishedDefinable Term
open Classicism.Proofs.UnarySP

variable {Sig : Signature}
private abbrev Individual := names (Sig := Sig) .e

private abbrev classicalIndividuals (Sig : Signature) : SingleObj Unit ⥤ Type :=
  (Functor.const _).obj Sig.Const

private def classicalValue (c : Sig.Const) : ∀ τ : Ty,
    (FullT (classicalIndividuals Sig) τ).obj (SingleObj.star Unit)
  | .e => c
  | .var _ => c
  | .rel _ => ∅

private def nameValue {C : Type} [SmallCategory C] (B : Premodel Sig C)
    (x : Individual (Sig := Sig)) : B.Dom B.W₀ .e :=
  castD (D := B.Dom B.W₀) x.2 (B.I x.1)

private theorem sem_name {C : Type} [SmallCategory C] (B : Premodel Sig C)
    (x : Individual (Sig := Sig)) {V : C} (h : B.W₀ ⟶ V) {Γ : Ctx}
    (env : IEnv (B.Dom V) Γ) :
    B.sem h (constAt x.1 x.2) env = (B.inner .e).map h (nameValue B x) := by
  rw [sem_constAt]
  exact (castD_map (D := B.Dom B.W₀) (D' := B.Dom V) (fun τ => (B.inner τ).map h)
    x.2 (B.I x.1)).symm

private abbrev apart (x y : Individual (Sig := Sig)) : Sentence Sig :=
  neg (eq' (constAt x.1 x.2) (constAt y.1 y.2))

private theorem consistently_box_apart (x y : Individual (Sig := Sig)) (hxy : x ≠ y) :
    AxiomSet.Consistent (AxiomSet.single (box (apart x y))) := by
  let B : Premodel Sig (SingleObj Unit) := Premodel.full (classicalIndividuals Sig)
    (SingleObj.star Unit) (fun _ => ⟨x.1⟩) (fun c => classicalValue c (Sig.typeOf c))
  have M : B.IsModel := Premodel.full_isModel _
  have denotes (n : Individual (Sig := Sig)) : nameValue B n = n.1 := by
    have castValue (c : Sig.Const) (τ : Ty) (h : Sig.typeOf c = τ) :
        castD (D := fun σ => (FullT (classicalIndividuals Sig) σ).obj (SingleObj.star Unit))
          h (classicalValue c (Sig.typeOf c)) = classicalValue c τ := by cases h; rfl
    exact castValue n.1 .e n.2
  apply AxiomSet.Consistent.of_model B M
  apply B.holdsAx_single
  rw [Premodel.HoldsSentence, B.holds_box M]
  intro V k
  rw [B.holds_neg M, B.holds_eq M, sem_name B x, sem_name B y]
  change nameValue B x ≠ nameValue B y
  rw [denotes, denotes]
  exact fun same => hxy (Subtype.ext same)

/-- The ordinary Maximalist root can make any named pair's distinction permanent. -/
theorem permanent_licence [Countable Sig.Const] (hS : Sig.Closed)
    (hn : Nonempty (names (Sig := Sig) .e)) :
    AxiomSet.Consistent (AxiomSet.maximalist ∪
      AxiomSet.single (ofPure (Sig := Sig) permanent.term)) := by
  let A := canonicalFamily Sig
  let R := ordinary Sig
  let B := Representatives.model A R hn
  have M : B.IsModel := Representatives.isModel A R hn canonicalFamily_isModel
  apply representatives_licence hS R hn
  apply (holds_permanent_iff B M).2
  intro x y hxy
  have closed : (box (apart x y)).closedTypes = true := by
    have nameClosed (c : Sig.Const) {τ : Ty} (hc : Sig.typeOf c = τ) :
        (constAt (Γ := []) c hc).closedTypes = true := by
      cases hc
      simpa only [constAt, Term.closedTypes] using (decide_eq_true (hS c))
    simp [apart, nameClosed]
  have visit := (Representatives.action A R).holds_dia_of_completeSig (Representatives.value A R)
    (Representatives.inclusion A R) hn M (representatives_complete hS R)
    closed (consistently_box_apart x y hxy)
  change B.Holds (𝟙 _) (dia (box (apart x y))) .nil at visit
  simp only [B.holds_dia M, B.holds_box M, apart, B.holds_neg M, B.holds_eq M,
    Category.id_comp] at visit
  have denotes (n : Individual (Sig := Sig)) : nameValue B n = n := by
    exact Representatives.cast_value A R n.1 n.2
  obtain ⟨V, h, separated⟩ := visit
  refine ⟨V, h, fun U k => ?_⟩
  have distinct := separated k
  rw [sem_name B x, sem_name B y, denotes x, denotes y] at distinct
  exact distinct

end Classicism.Meta.UnarySP
