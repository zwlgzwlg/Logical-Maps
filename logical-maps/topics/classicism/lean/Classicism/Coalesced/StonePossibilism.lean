import Classicism.Coalesced.StoneSmall
import Classicism.Coalesced.StoneBooleanAlgebra
import Classicism.Semantics.IntensionalTheory
import Classicism.Semantics.Interpretations
import Classicism.Results.SentenceSchemas.PossibilityDistinctness

/-! Joint native realization of revised Mathematical Possibilism and the two
Maximalism schemata in one concrete Stone fan, at countable closed signatures. -/

namespace Classicism.Meta.Coalesced.StoneFan.Canonical

open CategoryTheory Classicism.Meta.Intensional Ordinals PowerClosed
open _root_.Classicism.StoneMP
open scoped Cardinal

noncomputable section
local instance nativeTyStonePossibilism (α : Type) : _root_.Classicism.Ty α := ⟨()⟩

abbrev representedTerm {Sig : Signature} (σ : Ty) : Formula Sig [.rel (binary σ), .rel (unary σ)] :=
  unaryBody (unaryBody (Term.ofPure (Represented.term σ)))

variable (Sig : Signature) [Countable Sig.Const] (X : Type) [TopologicalSpace X]

private noncomputable abbrev P := fan Sig (terminal Sig) X
private noncomputable abbrev W := (P Sig X).W₀

private theorem graph_order_iso {α β : Type} (A : Set α) (R : α → α → Prop) (D : Set β)
    (L : β → β → Prop) (I : α → β → Prop) (f : A ≃ D)
    (hf : ∀ a q, I a q ↔ ∃ ha : a ∈ A, (f ⟨a,ha⟩).1 = q)
    (ho : ∀ a b : A, R a.1 b.1 ↔ L (f a).1 (f b).1) : OrderIso I A R D L := by
  have maps : Maps I A D := by
    refine ⟨?_, ?_, ?_⟩
    · intro a q h
      obtain ⟨ha,rfl⟩ := (hf a q).mp h
      exact ⟨ha,(f ⟨a,ha⟩).2⟩
    · intro a ha
      exact ⟨_, (f ⟨a,ha⟩).2, (hf _ _).mpr ⟨ha, rfl⟩⟩
    · intro a p q hp hq
      obtain ⟨_,rfl⟩ := (hf _ _).mp hp
      obtain ⟨_,rfl⟩ := (hf _ _).mp hq
      rfl
  refine ⟨⟨⟨maps, ?_⟩, ⟨maps, ?_⟩⟩, ?_⟩
  · intro a b q ha hb
    obtain ⟨ha,rfl⟩ := (hf _ _).mp ha
    obtain ⟨hb, e⟩ := (hf _ _).mp hb
    exact congrArg Subtype.val (f.injective (Subtype.ext e.symm))
  · intro y hy
    let a := f.symm ⟨y,hy⟩
    exact ⟨a.1, a.2, (hf _ _).mpr ⟨a.2, congrArg Subtype.val (f.apply_symm_apply ⟨y,hy⟩)⟩⟩
  · intro a b p q hp hq
    obtain ⟨ha,rfl⟩ := (hf _ _).mp hp
    obtain ⟨hb,rfl⟩ := (hf _ _).mp hq
    exact ho ⟨a,ha⟩ ⟨b,hb⟩

theorem holds_represented {σ : Ty} (M : (P Sig X).IsModel)
    (A : (P Sig X).Dom (W Sig X) (.rel (unary σ)))
    (R : (P Sig X).Dom (W Sig X) (.rel (binary σ)))
    (valid : HasIntervalGraph Sig X (trace₁ (P Sig X) A) (fun a b => row₂ (P Sig X) R a.1 b.1)) :
    (P Sig X).Holds (𝟙 _) (representedTerm σ) (.cons R (.cons A .nil)) := by
  let B := P Sig X
  obtain ⟨p,f,G,hG,hO⟩ := valid
  have gr (a q) : row₂ B G a q ↔ ∃ ha, (f ⟨a,ha⟩).1 = q := by
    have eq := hG a q
    rw [graphMember, Premodel.holds_app_var2] at eq
    exact eq
  have good := graph_order_iso (trace₁ B A) (row₂ B R) {q | rootEntails Sig X q p} (rootEntails Sig X)
    (row₂ B G) f gr hO
  dsimp only [representedTerm, Represented.term, Term.ofPure_lam, unaryBody]
  simp only [Term.ofPure_app, Term.ofPure_var, Term.ofPure_lam, Term.ofPure_and, Term.ofPure_not,
    Term.ofPure_or, Term.ofPure_all, Term.ofPure_ex, Term.ofPure_eq,
    (P Sig X).holds_exists M]
  refine ⟨p, G, ?_⟩
  simp only [_root_.Classicism.StoneMP.OrderIso, Bijects, Injects, Surjects, Maps, rootEntails,
    box_imp_iff_subset (P Sig X) M, iff_def] at good
  simp only [box_imp_iff_subset (P Sig X) M, (P Sig X).holds_conj M, (P Sig X).holds_imp M,
    (P Sig X).holds_forall M, (P Sig X).holds_exists M, Premodel.holds_eq_var M,
    Premodel.holds_app_var1, Premodel.holds_app_var2, IEnv.get]
  exact good


/-- The map's revised, type-indexed Mathematical Possibilism schema with the
inexact ordinal guard and represented membership powers from the PR 28 source. -/
def revisedMathematicalPossibilism (Sig : Signature) : AxiomSet Sig := fun a =>
  ∃ σ : Ty, a = Term.ofPure (MPAt.term σ)

private abbrev stoneBound (Sig : Signature) [Countable Sig.Const] := (ordinalCut Sig).out
private abbrev stoneSpace (Sig : Signature) [Countable Sig.Const] := boundedSpace (stoneBound Sig)

/-- One canonical fan satisfies revised Mathematical Possibilism and both
versions of Maximalism simultaneously. -/
theorem possibility_mathematical_possibilism (hS : Sig.Closed) :
    let P := fan Sig (terminal Sig) (boundedSpace (ordinalCut Sig).out)
    P.IsModel ∧ P.HoldsAx (AxiomSet.possibilityC Sig) ∧
      P.HoldsAx (AxiomSet.pureVersion AxiomSet.possibilityC) ∧
      P.HoldsAx (revisedMathematicalPossibilism Sig) := by
  let space := stoneSpace Sig
  let F := fan Sig (terminal Sig) space
  obtain ⟨M, sigMax, pureMax⟩ := singleton_fan_maximalist Sig space hS
  refine ⟨M, sigMax, pureMax, ?_⟩
  rintro a ⟨σ,rfl⟩
  have eq : Term.ofPure (Sig := Sig) (MPAt.term σ) = Term.forall' (Term.forall'
      (Term.imp (cbaTerm σ) (Term.imp (at₁ (smallTerm σ) (.succ .zero)) (representedTerm σ)))) := rfl
  change F.Holds (𝟙 _) (Term.ofPure (MPAt.term σ)) .nil
  rw [eq, F.holds_forall M]
  intro A
  rw [F.holds_forall M]
  intro R
  rw [F.holds_imp M, F.holds_imp M, holds_at₁]
  intro cba small
  have full : CurrentFull (W := F.W₀) F :=
    current_ext_full _ _ true (components Sig (terminal Sig) (Premodel.full_isModel _))
  obtain ⟨alg, horder⟩ := algebra_of_cba (cba_from_holds F M _ full A R cba)
  let : BooleanAlgebra (trace₁ F A) := alg
  have bound : #(trace₁ F (ordinalEntity F M (𝟙 F.W₀))) < ordinalCut Sig := by
    rw [ordinal_row]
    exact actual_ordinal_lt_cut Sig space
  have card := small_cardinal_lt F M _ full A (ordinalCut Sig) (cut_strong_limit Sig) bound small
  have fits : #(trace₁ F A) ≤ #(stoneBound Sig) := by
    change #(trace₁ F A) ≤ #(ordinalCut Sig).out
    simpa using card.le
  obtain ⟨j⟩ := (Cardinal.le_def _ _).mp fits
  have graph := realizes_bounded_graph Sig (stoneBound Sig) (trace₁ F A) j
  apply holds_represented Sig space M A R
  have ordEq : (fun x y : trace₁ F A => row₂ F R x.1 y.1) = (fun x y : trace₁ F A => x ≤ y) :=
    funext₂ fun x y => propext (horder x y).symm
  rw [ordEq]
  exact graph


/-- The official map form of each Maximalism schema uses distinctness. -/
theorem maximalist_mathematical_possibilism (hS : Sig.Closed) :
    let P := fan Sig (terminal Sig) (boundedSpace (ordinalCut Sig).out)
    P.IsModel ∧ P.HoldsAx (AxiomSet.distinctnessC Sig) ∧
      P.HoldsAx (AxiomSet.pureVersion AxiomSet.distinctnessC) ∧
      P.HoldsAx (revisedMathematicalPossibilism Sig) := by
  let F := fan Sig (terminal Sig) (boundedSpace (ordinalCut Sig).out)
  obtain ⟨M, hs, hp, hm⟩ := possibility_mathematical_possibilism Sig hS
  have pureBridge : AxiomSet.Entails (AxiomSet.pureVersion (Sig := Sig) AxiomSet.possibilityC)
      (AxiomSet.pureVersion AxiomSet.distinctnessC) := by
    rintro _ ⟨p, h, rfl⟩
    exact Derivable.mono (AxiomSet.ofPure_union_subset _) (Theorem.ofPure (possibility_entails_distinctness _ p h))
  exact ⟨M, F.entails_holds M (possibility_entails_distinctness _) hs, F.entails_holds M pureBridge hp, hm⟩
#print axioms maximalist_mathematical_possibilism


/-- The existential model statement in the map's native complete-theory
convention. One propositional constant supplies an admitted signature. -/
theorem joint_complete_theory :
    ∃ (S : Signature) (_ : S.Admitted) (Ax : AxiomSet S),
      Ax.Consistent ∧ Ax.Complete ∧
      Ax.Entails (AxiomSet.distinctnessC S) ∧
      Ax.Entails (AxiomSet.pureVersion AxiomSet.distinctnessC) ∧
      Ax.Entails (revisedMathematicalPossibilism S) := by
  let S := Signature.sigmaTop
  let : Countable S.Const := inferInstanceAs (Countable Unit)
  let F := fan S (terminal S) (boundedSpace (ordinalCut S).out)
  obtain ⟨M, sigMax, pureMax, mp⟩ := maximalist_mathematical_possibilism S Signature.sigmaTop_admitted.1
  exact ⟨S, Signature.sigmaTop_admitted, F.theory, F.theory_consistent M, F.theory_complete M,
    F.entails_of_holdsAx M sigMax, F.entails_of_holdsAx M pureMax, F.entails_of_holdsAx M mp⟩

#print axioms joint_complete_theory

end
end Classicism.Meta.Coalesced.StoneFan.Canonical
