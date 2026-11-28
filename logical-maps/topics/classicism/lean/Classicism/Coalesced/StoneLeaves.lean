import Classicism.Coalesced.Full
import Mathlib.Topology.LocallyConstant.Basic

/-!
# Locally constant profiles in a coalesced action model

The points of a topological space index parallel root arrows to a common component
object. A root relation must land on every component and have locally constant
transport on these arrows. No restriction is placed on the current extension or on
transports to separate components beyond landing. With homogeneous interpretations
of the signature on the distinguished family, these domains are closed under the
native intensional semantics of all terms.
-/

namespace Classicism.Meta.Coalesced.StoneLeaves

open CategoryTheory CategoryTheory.Sigma Classicism.Meta.Intensional

variable {Sig : Signature} {ι : Type} {C : ι → Type} [∀ k, SmallCategory (C k)]
  {S : RootArrows C} {A : ∀ k, Premodel Sig (C k)}
  {L : Type} [TopologicalSpace L] {k : ι} {V : C k}
  (r : L → S.R.obj ⟨k, V⟩) (fixed : ∀ m x, S.act m (r x) = r x)

include fixed in
/-- A root endomorphism fixes every indexed leaf arrow. This holds in particular when
the root has only its identity. -/
def selector : Selector S A where
  sel _ _ := {X | IsLocallyConstant (fun x => rootTransport X (r x))}
  shift_mem _ _ m X h := by
    change IsLocallyConstant (fun x => rootTransport X (r x)) at h
    change IsLocallyConstant (fun x => rootTransport {q | shift m q ∈ X} (r x))
    simpa only [rootTransport_shift, fixed] using h

variable (ae : AtomAction S A .e) (av : ∀ i, AtomAction S A (.var i))

local notation "sel" => selector (A := A) r fixed
local notation "RA" => selAction ae av sel
local notation "RI" => selIncl ae av sel

/-- Local constancy of the injected component values entails local constancy of the
underlying entities, by injectivity of the native component inclusion. -/
private theorem reflect_local {B D : Type*} {f : L → B} {j : B → D}
    (hinj : Function.Injective j) (h : IsLocallyConstant (j ∘ f)) :
    IsLocallyConstant f := by
  apply (IsLocallyConstant.iff_eventually_eq _).2
  intro x
  exact (h.eventually_eq x).mono fun _ e => hinj e

/-- Every admitted root entity has a locally constant leaf profile. The two atomic
clauses are input data. At every relational type this follows from the selector. -/
theorem entity_local
    (he : ∀ a : ae.D, IsLocallyConstant (fun x => ae.tr (r x) a))
    (hv : ∀ i (a : (av i).D), IsLocallyConstant (fun x => (av i).tr (r x) a)) :
    ∀ (σ : Ty) (a : (RA).D σ), IsLocallyConstant (fun x => (RA).tr σ (r x) a)
  | .e, a => he a
  | .var i, a => hv i a
  | .rel ρ, a => by
    apply reflect_local ((A k).incl_injective ρ V)
    change IsLocallyConstant (fun x => (A k).incl ρ V ((relLevel sel ρ _).tr (r x) a))
    have ht (x : L) := incl_relLevel_tr sel ρ _ (r x) a
    simp_rw [ht]
    exact a.2.2

/-- An open term has a finite variable context, so its entire transported assignment
is locally constant whenever each of its entries is locally constant. -/
private theorem env_local {D E : Ty → Type}
    (tr : ∀ σ, L → D σ → E σ)
    (h : ∀ σ a, IsLocallyConstant (fun x => tr σ x a)) :
    ∀ {Γ : Ctx} (g : IEnv D Γ),
      IsLocallyConstant (fun x => g.map (fun σ => tr σ x))
  | _, .nil => IsLocallyConstant.const _
  | _, .cons a g => (h _ a).comp₂ (env_local tr h g) IEnv.cons

variable (ne : Nonempty ae.D) (I : ∀ c : Sig.Const,
  (selAction ae av (selector (A := A) r fixed)).D (Sig.typeOf c))

local notation "P" => RootAction.coalescedSum RA RI ne I

/-- The actual transported relational denotation is the component denotation of the
same term under the transported environment, at every indexed leaf. -/
theorem transport_sem (m : S.End) {Γ : Ctx} {ρ : RTy}
    (t : Term Sig Γ (.rel ρ)) (g : IEnv (RA).D Γ) (x : L) :
    (RA).transport (r x) ((P).sem (CoalescedSum.endo S m) t g) =
      ((RA).component I (r x)).sem (𝟙 V) t (g.map fun σ => (RA).tr σ (r x)) := by
  have h := congrArg (RA).compI
    ((P).sem_push (CoalescedSum.endo S m) t g (CoalescedSum.arr S (r x))).symm
  change (RA).transport (r x) ((P).sem (CoalescedSum.endo S m) t g) =
    (RA).compO (.rel ρ) ((P).sem (CoalescedSum.arr S (S.act m (r x))) t
      (g.map fun σ => (RA).tr σ (r x))) at h
  rw [fixed] at h
  exact h.trans ((RA).sem_arr RI ne I (r x) t _)

/-- Homogeneous leaf interpretations make the sliced denotation of every open term
locally constant. The term evaluator is the native evaluator, including quantification,
modality, relational abstraction, and application. -/
theorem term_local
    (he : ∀ a : ae.D, IsLocallyConstant (fun x => ae.tr (r x) a))
    (hv : ∀ i (a : (av i).D), IsLocallyConstant (fun x => (av i).tr (r x) a))
    (J : ∀ c : Sig.Const, (A k).Dom V (Sig.typeOf c))
    (hc : ∀ c x, (RA).tr _ (r x) (I c) = J c)
    (m : S.End) {Γ : Ctx} {ρ : RTy} (t : Term Sig Γ (.rel ρ)) (g : IEnv (RA).D Γ) :
    IsLocallyConstant (fun x => (RA).transport (r x) ((P).sem (CoalescedSum.endo S m) t g)) := by
  have hg := env_local (fun σ x => (RA).tr σ (r x)) (entity_local r fixed ae av he hv) g
  have e (x : L) := (transport_sem r fixed ae av ne I m t g x).trans
    ((A k).rebase_sem_congr (funext fun c => hc c x) (𝟙 V) t _)
  simp_rw [e]
  exact hg.comp (fun g' => ((A k).rebase V J).sem (𝟙 V) t g')

/-- The selected coalesced premodel is a native action model. Only the component
model conditions, atomic leaf profiles, and homogeneous interpretation of constants
are assumed. Root closure and all higher-type closure follow. -/
theorem isModel
    (he : ∀ a : ae.D, IsLocallyConstant (fun x => ae.tr (r x) a))
    (hv : ∀ i (a : (av i).D), IsLocallyConstant (fun x => (av i).tr (r x) a))
    (J : ∀ c : Sig.Const, (A k).Dom V (Sig.typeOf c))
    (hc : ∀ c x, (RA).tr _ (r x) (I c) = J c)
    (hQ : (RA).ComponentsAreModels I) : (P).IsModel := by
  apply ((RA).isModel_iff RI ne I).2
  refine ⟨hQ, (rootClosed_iff_selected ae av sel ne I hQ).2 ?_⟩
  intro m Γ ρ t g
  change IsLocallyConstant (fun x => rootTransport {q | ofRT ae av sel q ∈
    (P).sem (CoalescedSum.endo S m) t g} (r x))
  exact term_local r fixed ae av ne I he hv J hc m t g

#print axioms isModel

end Classicism.Meta.Coalesced.StoneLeaves
