import Classicism.Coalesced.DistinguishedDefinable
import Classicism.Coalesced.Complete
import Classicism.Semantics.FullModels

/-! The current extension of a named relation can be empty or full while its
values at all distinguished entrances remain fixed. -/

namespace Classicism.Meta.Coalesced.DescriptorColours

open CategoryTheory Classicism.Meta.Intensional

variable {Sig : Signature} {ι : Type} {C : ι → Type} [∀ k, SmallCategory (C k)]
variable (A : ∀ k, Premodel Sig (C k))

def colouredTuples {ρ : RTy} {RA : Type} (colour : Bool)
    (y : ∀ k, (A k).Dom (A k).W₀ (.rel ρ)) : Set (RootTuple (baseArrows A) A ρ RA)
  | .inl _ => colour = true
  | .inr q => unionTuples A (RA := RA) y (.inr q)

theorem transport_colouredTuples {ρ : RTy} {RA : Type} (colour : Bool)
    (y : ∀ k, (A k).Dom (A k).W₀ (.rel ρ)) {k : ι} {V : C k} (h : (A k).W₀ ⟶ V) :
    rootTransport (colouredTuples A (RA := RA) colour y) h =
      (A k).incl ρ V (((A k).inner (.rel ρ)).map h (y k)) :=
  rootTransport_unionTuples A (RA := RA) y h

noncomputable def valueAt (colour : Bool) (c : Sig.Const) :
    ∀ (σ : Ty), Sig.typeOf c = σ → (DistinguishedDefinable.action A).D σ
  | .e, h => ⟨c, h⟩
  | .var _, h => ⟨c, h⟩
  | .rel ρ, h =>
    let y := fun k => castD (D := (A k).Dom (A k).W₀) h ((A k).I c)
    ⟨colouredTuples A colour y, fun j => ⟨_, (transport_colouredTuples A colour y j).symm⟩,
      constAt c h, fun k => by
        rw [transport_colouredTuples, sem_constAt]
        simp only [Functor.map_id_apply]
        rfl⟩

noncomputable abbrev value (colour : Bool) (c : Sig.Const) := valueAt A colour c _ rfl

theorem cast_value (colour : Bool) (c : Sig.Const) {σ : Ty} (h : Sig.typeOf c = σ) :
    castD (D := (DistinguishedDefinable.action A).D) h (value A colour c) =
      valueAt A colour c σ h := by
  cases h
  rfl

theorem transportsAt (colour : Bool) (c : Sig.Const) (k : ι) :
    ∀ (σ : Ty) (h : Sig.typeOf c = σ),
    (DistinguishedDefinable.action A).tr σ (dist A k) (valueAt A colour c σ h) =
    castD (D := (A k).Dom (A k).W₀) h ((A k).I c)
  | .e, _ => (A k).inner _ |>.map_id_apply _ _
  | .var _, _ => (A k).inner _ |>.map_id_apply _ _
  | .rel ρ, h => by
    apply (A k).incl_injective ρ _
    refine (incl_relLevel_tr (DistinguishedDefinable.selector A) ρ _ (dist A k) _).trans ?_
    let y := fun j => castD (D := (A j).Dom (A j).W₀) h ((A j).I c)
    exact (transport_colouredTuples A colour y _).trans
      (congrArg ((A k).incl ρ _) (((A k).inner (.rel ρ)).map_id_apply _ (y k)))

theorem transports (colour : Bool) :
    TransportsConstants (DistinguishedDefinable.action A) (value A colour) :=
  fun c k => transportsAt A colour c k _ rfl

variable (ne : Nonempty (DistinguishedDefinable.names (Sig := Sig) .e))
noncomputable abbrev model (colour : Bool) :=
  (DistinguishedDefinable.action A).coalescedSum (DistinguishedDefinable.inclusion A) ne
    (value A colour)

theorem isModel (M : ∀ k, (A k).IsModel) (colour : Bool) : (model A ne colour).IsModel :=
  (model A ne colour).isModel_of_reductAt
    (Premodel.reductAt_isModel (DistinguishedDefinable.isModel A ne M))

/-- The name has empty current extension iff the colour is false. -/
def emptyRow (c : Sig.Const) {ρ : RTy} (h : Sig.typeOf c = .rel ρ) : Sentence Sig :=
  let p : Term Sig [] (.rel ρ) := constAt c h
  .app (.app (.inclR ρ) p) (.app (.negR ρ) p)

theorem current_name_row (colour : Bool) (c : Sig.Const) {ρ : RTy}
    (h : Sig.typeOf c = .rel ρ) (a : Args (model A ne colour).inner ρ (model A ne colour).W₀) :
    (⟨_, a, 𝟙 _⟩ : Tuple (model A ne colour).inner ρ _) ∈
       (model A ne colour).sem (𝟙 _) (constAt (Γ := []) c h) .nil ↔ colour = true := by
  rw [sem_constAt, Functor.map_id_apply]
  change _ ∈ (DistinguishedDefinable.inclusion A).incl ρ
    (castD (D := (DistinguishedDefinable.action A).D) h (value A colour c)) ↔ _
  rw [cast_value]
  rfl

/-- The pure guard separating one and two current individuals. -/
def twoIndividuals (S : Signature) : Sentence S :=
  .exists' (.exists' (σ := .e) (.neg (.eq' (.var (.succ (.zero : Var [.e] .e))) (.var .zero))))


section Semantics

variable {V : Type} [SmallCategory V] (B : Premodel Sig V) (M : B.IsModel)

include M in
theorem holds_twoIndividuals : B.HoldsSentence (twoIndividuals Sig) ↔
    ∃ x y : B.Dom B.W₀ .e, x ≠ y := by
  simp only [twoIndividuals, Premodel.HoldsSentence, B.holds_exists M, B.holds_neg M,
    B.holds_eq_var M, IEnv.get]

include M in
theorem nonempty_arguments {W : V} (h : B.W₀ ⟶ W) :
    ∀ (ρ : RTy), ρ.Closed → Nonempty (Args B.inner ρ W)
  | .t, _ => ⟨PUnit.unit⟩
  | .arr σ ρ, hc => by
    obtain ⟨tail⟩ := nonempty_arguments h ρ hc.2
    have hs : Nonempty (B.Dom W σ) := by
      cases σ with
      | e => exact B.nonempty_e W
      | var n => exact False.elim hc.1
      | rel r =>
        obtain ⟨x, _⟩ := M h (Term.topR (Γ := []) r) .nil
        exact ⟨x⟩
    exact ⟨(Classical.choice hs, tail)⟩

end Semantics

theorem holds_emptyRow (M : ∀ k, (A k).IsModel) (colour : Bool)
    (c : Sig.Const) {ρ : RTy} (h : Sig.typeOf c = .rel ρ) (hc : ρ.Closed) :
    (model A ne colour).HoldsSentence (emptyRow c h) ↔ colour = false := by
  let B := model A ne colour
  have m : B.IsModel := isModel A ne M colour
  change B.Holds (𝟙 _) _ .nil ↔ _
  rw [emptyRow, B.holds_inclR m, B.sem_negR m]
  change (∀ a : Args B.inner ρ B.W₀, _ ∈ _ → ¬ _ ∈ _) ↔ _
  constructor
  · intro H
    obtain ⟨a⟩ := nonempty_arguments B m (𝟙 _) ρ hc
    cases he : colour with
    | false => rfl
    | true =>
      have hx := (current_name_row A ne colour c h a).2 he
      exact (H a hx hx).elim
  · intro he a hx _
    exact Bool.noConfusion (he.symm.trans ((current_name_row A ne colour c h a).1 hx))

theorem closed_constAt {c : Sig.Const} {σ : Ty} (h : Sig.typeOf c = σ) (hc : σ.Closed) :
    (constAt (Γ := []) c h).closedTypes = true := by
  cases h
  simp [constAt, Term.closedTypes, hc]

theorem closed_emptyRow {c : Sig.Const} {ρ : RTy} (h : Sig.typeOf c = .rel ρ) (hc : ρ.Closed) :
    (emptyRow c h).closedTypes = true := by
  have hn := closed_constAt h hc
  simp [emptyRow, Term.closedTypes, hn, hc]

theorem closed_twoIndividuals (S : Signature) : (twoIndividuals S).closedTypes = true := rfl

def individualNames (X : Type) : Signature := ⟨X, fun _ => .e⟩

instance {X : Type} [Countable X] : Countable (individualNames X).Const := inferInstanceAs (Countable X)

theorem individualNames_closed (X : Type) : (individualNames X).Closed := fun _ => trivial

theorem namedIndividual (X : Type) [Nonempty X] :
    Nonempty (DistinguishedDefinable.names (Sig := individualNames X) .e) :=
  ⟨⟨(Classical.choice inferInstance : X), rfl⟩⟩

theorem one_name (A : ∀ k, Premodel (individualNames Unit) (C k)) (M : ∀ k, (A k).IsModel) :
    ¬ (model A (namedIndividual Unit) false).HoldsSentence (twoIndividuals _) := by
  rw [holds_twoIndividuals _ (isModel A _ M _)]
  rintro ⟨x, y, h⟩
  apply h
  apply Subtype.ext
  exact @Subsingleton.elim Unit inferInstance x.1 y.1

theorem two_names (A : ∀ k, Premodel (individualNames Bool) (C k)) (M : ∀ k, (A k).IsModel) :
    (model A (namedIndividual Bool) false).HoldsSentence (twoIndividuals _) := by
  rw [holds_twoIndividuals _ (isModel A _ M _)]
  exact ⟨⟨false, rfl⟩, ⟨true, rfl⟩, fun e => Bool.noConfusion (congrArg Subtype.val e)⟩


/-- With all closed consistent sentences represented at the entrances, each colour gives
ordinary Maximalism in the signature. -/
theorem complete_components (colour : Bool)
    (hc : ∀ p : Sentence Sig, p.closedTypes = true → AxiomSet.Consistent (AxiomSet.single p) →
      ∃ k, (A k).HoldsSentence p) :
    (DistinguishedDefinable.action A).CompleteComponentsSig (value A colour) := by
  intro p hp cons
  obtain ⟨k, hk⟩ := hc p hp cons
  exact ⟨k, (A k).W₀, dist A k, by rw [component_dist (transports A colour) k]; exact hk⟩

section Canonical

variable {S : Signature} [Countable S.Const] (hS : S.Closed)
variable (hn : Nonempty (DistinguishedDefinable.names (Sig := S) .e))

include hS

theorem holds_max (colour : Bool) :
    (model (canonicalFamily S) hn colour).HoldsAx AxiomSet.maximalist :=
  Premodel.holdsAx_union _ (Premodel.holdsAx_empty _)
    (RootAction.holdsAx_distinctnessC_of_complete _ _ _ _
      (isModel _ hn canonicalFamily_isModel colour)
      (complete_components _ colour (canonicalFamily_complete hS)))

theorem licence (colour : Bool) {p : Sentence S}
    (hw : (model (canonicalFamily S) hn colour).HoldsSentence p) :
    AxiomSet.Consistent (AxiomSet.maximalist ∪ AxiomSet.single p) :=
  AxiomSet.Consistent.of_model _ (isModel _ hn canonicalFamily_isModel colour)
    (Premodel.holdsAx_union _ (holds_max hS hn colour) (Premodel.holdsAx_single _ hw))

theorem pure_licence (colour : Bool) {p : Sentence Signature.pure}
    (hw : (model (canonicalFamily S) hn colour).HoldsSentence (Term.ofPure p)) :
    AxiomSet.Consistent (AxiomSet.maximalist ∪ AxiomSet.single p) := by
  let B := model (canonicalFamily S) hn colour
  have M : B.IsModel := isModel _ hn canonicalFamily_isModel colour
  have H : B.HoldsAx (AxiomSet.pureVersion AxiomSet.distinctnessC) :=
    RootAction.holdsAx_distinctness_of_complete _ _ _ _ M
      (RootAction.CompleteComponentsSig.complete _ _ hS
        (complete_components _ colour (canonicalFamily_complete hS)))
  apply AxiomSet.Consistent.of_model B.reduct (B.reduct_isModel M)
  apply B.reduct.holdsAx_union
  · exact B.reduct.holdsAx_union B.reduct.holdsAx_empty ((B.holdsAx_ofPure _).1 H)
  · exact B.reduct.holdsAx_single ((B.holdsSentence_ofPure p).1 hw)

end Canonical

end Classicism.Meta.Coalesced.DescriptorColours
