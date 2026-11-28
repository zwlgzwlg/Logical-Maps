import Classicism.Coalesced.StoneMaximalist
import Classicism.Coalesced.StoneCurrent

/-!
# Principal intervals at the Stone root

A clopen leaf set gives a native proposition with empty old and current parts.
Its native entailment interval is exactly the clopen interval. A representation
of any current subcarrier in that clopen interval therefore lifts to an admitted
mixed graph on actual entities of the canonical Maximalist fan.
-/

namespace Classicism.Meta.Coalesced.StoneFan.Canonical

open CategoryTheory Classicism.Meta.Intensional TopologicalSpace

variable (Sig : Signature) [Countable Sig.Const] (X : Type) [TopologicalSpace X]

private noncomputable abbrev P := fan Sig (terminal Sig) X
private noncomputable abbrev W := (P Sig X).W₀
abbrev RootProp := (P Sig X).Dom (W Sig X) (.rel .t)

/-- The order formula in the actual language at the designated root. -/
def rootEntails (a b : RootProp Sig X) : Prop :=
  (P Sig X).Holds (𝟙 (W Sig X))
    (Term.box (Term.imp (.var .zero) (.var (.succ .zero)))) (.cons a (.cons b .nil))

private theorem old_empty :
    ∃ q : (maximalist Sig).Dom (maximalist Sig).W₀ (.rel .t), (maximalist Sig).incl .t _ q = ∅ := by
  let O := maximalist Sig
  have M : O.IsModel := maximalist_isModel
  obtain ⟨q, hq⟩ := M (𝟙 O.W₀) (Term.bot (Sig := Sig) (Γ := [])) .nil
  exact ⟨q, hq.trans (O.sem_bot M _ _)⟩

private noncomputable def oldBottom := Classical.choose (old_empty Sig)

private theorem incl_oldBottom :
    (maximalist Sig).incl .t _ (oldBottom Sig) = ∅ :=
  Classical.choose_spec (old_empty Sig)

/-- A clopen leaf coordinate, extended by bottom at all old and current coordinates. -/
noncomputable def fromClopen (c : Clopens X) : RootProp Sig X :=
  (propositionCoordinates Sig X).symm (False, oldBottom Sig, c)

theorem fromClopen_entails (a b : Clopens X) :
    rootEntails Sig X (fromClopen Sig X a) (fromClopen Sig X b) ↔ a ≤ b := by
  rw [rootEntails, proposition_order]
  simp [fromClopen]

/-- A native proposition below a clopen coordinate has zero current and old coordinates. -/
theorem entails_fromClopen {a : RootProp Sig X} {c : Clopens X} :
    rootEntails Sig X a (fromClopen Sig X c) ↔
      a = fromClopen Sig X ((propositionCoordinates Sig X a).2.2) ∧
      (propositionCoordinates Sig X a).2.2 ≤ c := by
  constructor
  · intro ha
    obtain ⟨hc, ho, hleaf⟩ := (proposition_order Sig X _ _).1 ha
    simp only [fromClopen, Equiv.apply_symm_apply] at hc ho hleaf
    have hold : (propositionCoordinates Sig X a).2.1 = oldBottom Sig := by
      apply (maximalist Sig).incl_injective .t _
      apply Set.Subset.antisymm ho
      exact Set.Subset.trans (le_of_eq (incl_oldBottom Sig)) (Set.empty_subset _)
    refine ⟨(propositionCoordinates Sig X).injective ?_, hleaf⟩
    rw [fromClopen, Equiv.apply_symm_apply]
    exact Prod.ext (propext ⟨hc, False.elim⟩) (Prod.ext hold rfl)
  · rintro ⟨h, hc⟩
    exact (congrArg (fun z => rootEntails Sig X z (fromClopen Sig X c)) h).mpr
      ((fromClopen_entails Sig X _ _).2 hc)

/-- Every point of the native principal interval has a unique clopen coordinate. -/
noncomputable def intervalEquiv (c : Clopens X) :
    Set.Iic c ≃ {p : RootProp Sig X // rootEntails Sig X p (fromClopen Sig X c)} where
  toFun z := ⟨fromClopen Sig X z.1, (fromClopen_entails Sig X _ _).2 z.2⟩
  invFun p := ⟨(propositionCoordinates Sig X p.1).2.2, ((entails_fromClopen Sig X).1 p.2).2⟩
  left_inv z := Subtype.ext <| congrArg (fun p => p.2.2)
    ((propositionCoordinates Sig X).apply_symm_apply (False, oldBottom Sig, z.1))
  right_inv p := Subtype.ext ((entails_fromClopen Sig X).1 p.2).1.symm

theorem intervalEquiv_order {c : Clopens X} (a b : Set.Iic c) :
    rootEntails Sig X (intervalEquiv Sig X c a).1 (intervalEquiv Sig X c b).1 ↔ a ≤ b :=
  fromClopen_entails Sig X _ _

/-- The deep binary application formula used to read a mixed representation graph. -/
def graphMember {σ : Ty} (G : (P Sig X).Dom (W Sig X) (.rel (.arr σ (.arr (.rel .t) .t))))
    (a : (P Sig X).Dom (W Sig X) σ) (p : RootProp Sig X) : Prop :=
  (P Sig X).Holds (𝟙 (W Sig X))
    (.app (.app (.var (.succ (.succ .zero))) (.var (.succ .zero))) (.var .zero))
    (.cons p (.cons a (.cons G .nil)))

/-- An admitted mixed graph whose restriction to a current carrier is an order
bijection onto a principal interval of native propositions. -/
def HasIntervalGraph {σ : Ty} (E : Set ((P Sig X).Dom (W Sig X) σ))
    (R : E → E → Prop) : Prop :=
    ∃ (p : RootProp Sig X)
      (f : E ≃ {q : RootProp Sig X // rootEntails Sig X q p})
      (G : (P Sig X).Dom (W Sig X) (.rel (.arr σ (.arr (.rel .t) .t)))),
      (∀ a q, graphMember Sig X G a q ↔ ∃ ha : a ∈ E, (f ⟨a, ha⟩).1 = q) ∧
      (∀ a b, R a b ↔ rootEntails Sig X (f a).1 (f b).1)

/-- A clopen-interval representation of a current ordered subcarrier gives a
native proposition and a single admitted typed graph. Its fibres are exactly the
graph of a bijection onto the entire native entailment interval, and the deep
necessary-implication formula reads the given order on its domain. -/
theorem realizes_interval_graph {σ : Ty} (E : Set ((P Sig X).Dom (W Sig X) σ))
    (R : E → E → Prop) (c : Clopens X) (e : E ≃ Set.Iic c)
    (he : ∀ a b, R a b ↔ e a ≤ e b) :
    HasIntervalGraph Sig X E R := by
  let f := e.trans (intervalEquiv Sig X c)
  let rel (a : (P Sig X).Dom (W Sig X) σ) (q : RootProp Sig X) :=
    ∃ ha : a ∈ E, (f ⟨a, ha⟩).1 = q
  have M := components Sig (terminal Sig) (Premodel.full_isModel _)
  obtain ⟨G, hg⟩ := realizes_mixed_graph (family Sig (terminal Sig)) (labels X) true M rel
  refine ⟨fromClopen Sig X c, f, G, hg, ?_⟩
  intro a b
  exact (he a b).trans (intervalEquiv_order Sig X (e a) (e b)).symm

#print axioms realizes_interval_graph
#print axioms intervalEquiv
#print axioms intervalEquiv_order

end Classicism.Meta.Coalesced.StoneFan.Canonical
