import Classicism.Semantics.FullModels
import Classicism.Semantics.IntensionalExamples

/-!
# What the arrows of a model decide

The map's general arguments whose conditions are about the arrows out of the evaluation point
(Classicism, Proposition 3.24, with fullness supplying the surjectivity or the
non-injectivity):

- **`epic-arrows`**: in a full model whose arrows out of every reachable object are
  epimorphisms and act surjectively on the individuals, transport is onto at every type, so
  `BF` holds at every world (`holds_box_bf_of_epic`): `full-epic-barcan`.
- **`invertible-arrows`**: `ND` and `BF` at every world (`holds_box_nd_of_invertible`,
  `holds_box_bf_of_invertible`).
- **`retractions`**: every arrow out of the evaluation object has a retraction, so its
  transport is injective, and `ND` holds there (`holds_nd_of_retractions`).
- **`unretracted-arrow`**: in a full model, an arrow out of the evaluation object without a
  retraction transports `⊥` and `{1}` alike, so `ND_t` fails (`not_holds_nd_t_of_unretracted`).
- **`nonidentity-arrow`**: in a full model, `⊤` and `{1}` differ, so the Fregean Axiom fails
  (`Premodel.not_fregean_of_propFull`).
-/

namespace Classicism.Meta.Intensional

open CategoryTheory

namespace Premodel

variable {Sig : Signature} {C : Type} [SmallCategory C] (A : Premodel Sig C)

/-- `epic-arrows`: every arrow out of every object reachable from the evaluation point is an
epimorphism and acts surjectively on the individuals. -/
def EpicArrows : Prop :=
  ∀ {V U : C} (_ : A.W₀ ⟶ V) (k : V ⟶ U), Epi k ∧ Function.Surjective ((A.inner .e).map k)

/-- `invertible-arrows`: every arrow out of every object reachable from the evaluation point is
invertible. -/
def InvertibleArrows : Prop := ∀ {V U : C} (_ : A.W₀ ⟶ V) (k : V ⟶ U), IsIso k

/-- `retractions`: every arrow out of the evaluation object has a retraction. -/
def Retractions : Prop := ∀ {V : C} (k : A.W₀ ⟶ V), ∃ r : V ⟶ A.W₀, k ≫ r = 𝟙 A.W₀

/-- `unretracted-arrow`: some arrow out of the evaluation object has no retraction. -/
def UnretractedArrow : Prop := ∃ (V : C) (k : A.W₀ ⟶ V), ∀ m : V ⟶ A.W₀, k ≫ m ≠ 𝟙 A.W₀

/-- `nonidentity-arrow`: some arrow out of the evaluation object is not its identity. -/
def NonidentityArrow : Prop :=
  ∃ (V : C) (k : A.W₀ ⟶ V), (⟨V, PUnit.unit, k⟩ : Tuple A.inner .t A.W₀) ≠ ⟨A.W₀, PUnit.unit, 𝟙 A.W₀⟩

variable {A} (M : A.IsModel)
include M

omit M in
/-- In a full model, transport along an epimorphism is onto at every relational type. -/
theorem full_map_surjective_of_epi (hF : A.Full) {W V : C} (k : W ⟶ V) [Epi k] (ρ : RTy) :
    Function.Surjective ((A.inner (.rel ρ)).map k) := by
  intro y
  obtain ⟨x, hx⟩ := hF ρ W {p | ∃ m : V ⟶ p.1, p.2.2 = k ≫ m ∧
    (⟨p.1, p.2.1, m⟩ : Tuple A.inner ρ V) ∈ A.incl ρ V y}
  refine ⟨x, A.incl_injective ρ V ?_⟩
  rw [A.incl_map, hx]
  ext ⟨U, a, m⟩
  simp only [Intension.mem_map, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨m', e, hm'⟩
    rwa [(cancel_epi k).1 e]
  · intro hm
    exact ⟨m, rfl, hm⟩

/-- `BF` at every type of the paper's language, at a world all of whose arrows out are
epimorphisms acting surjectively on the individuals, in a full model. -/
theorem holds_bf_of_epic (hF : A.Full) (hE : A.EpicArrows) {W : C} (h : A.W₀ ⟶ W) (σ : Ty)
    (hσ : σ.Closed) : A.Holds h (Sentence.bf σ) .nil :=
  A.holds_bf_of_surjective M σ h fun {V} k => by
    have := (hE h k).1
    cases σ with
    | e => exact (hE h k).2
    | rel ρ => exact full_map_surjective_of_epi hF k ρ
    | var i => exact absurd hσ (Ty.not_closed_var i)

theorem holds_box_bf_of_epic (hF : A.Full) (hE : A.EpicArrows) {W : C} (h : A.W₀ ⟶ W) (σ : Ty)
    (hσ : σ.Closed) : A.Holds h (Term.box (Sentence.bf σ)) .nil := by
  rw [A.holds_box M]
  intro V k
  exact holds_bf_of_epic M hF hE (h ≫ k) σ hσ

theorem holds_box_nd_of_invertible (hI : A.InvertibleArrows) {W : C} (h : A.W₀ ⟶ W) (σ : Ty) :
    A.Holds h (Term.box (Sentence.nd σ)) .nil := by
  rw [A.holds_box M]
  intro V k
  exact A.holds_nd_of_iso M σ (h ≫ k) fun k' => hI (h ≫ k) k'

theorem holds_box_bf_of_invertible (hI : A.InvertibleArrows) {W : C} (h : A.W₀ ⟶ W) (σ : Ty) :
    A.Holds h (Term.box (Sentence.bf σ)) .nil := by
  rw [A.holds_box M]
  intro V k
  exact A.holds_bf_of_iso M σ (h ≫ k) fun k' => hI (h ≫ k) k'

/-- `ND` at every type holds at the base when every arrow out of it has a retraction: the
transport along the arrow is undone by the transport along the retraction. -/
theorem holds_nd_of_retractions (hr : A.Retractions) (σ : Ty) : A.HoldsSentence (Sentence.nd σ) := by
  rw [HoldsSentence, A.holds_nd_iff M]
  intro V k
  obtain ⟨r, hr⟩ := hr k
  intro x y e
  have := congrArg ((A.inner σ).map r) e
  simp only [← Functor.map_comp_apply, hr, Functor.map_id_apply] at this
  exact this

/-- In a full model, an arrow out of the evaluation object with no retraction transports `⊥`
and `{1}` alike, so `ND_t` fails. -/
theorem not_holds_nd_t_of_unretracted (hF : A.Full) (hU : A.UnretractedArrow) :
    ¬ A.HoldsSentence (Sentence.nd (.rel .t)) := by
  obtain ⟨V, k, hk⟩ := hU
  rw [HoldsSentence, A.holds_nd_iff M]
  intro H
  obtain ⟨x, hx⟩ := hF .t A.W₀ ∅
  obtain ⟨y, hy⟩ := hF .t A.W₀ {⟨A.W₀, PUnit.unit, 𝟙 A.W₀⟩}
  have e : (A.inner (.rel .t)).map k x = (A.inner (.rel .t)).map k y := by
    apply A.incl_injective .t V
    rw [A.incl_map, A.incl_map, hx, hy]
    ext ⟨U, a, m⟩
    simp only [Intension.mem_map, Set.mem_empty_iff_false, Set.mem_singleton_iff, false_iff]
    intro he
    obtain ⟨rfl, hh⟩ := Sigma.mk.inj_iff.mp he
    exact hk m (Prod.mk.inj (eq_of_heq hh)).2
  have := H k e
  subst this
  rw [hx] at hy
  exact Set.singleton_ne_empty _ hy.symm

end Premodel

end Classicism.Meta.Intensional
