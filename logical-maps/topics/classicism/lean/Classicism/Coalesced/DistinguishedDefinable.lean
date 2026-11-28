import Classicism.Coalesced.Definable
import Classicism.Coalesced.Distinguished

/-!
# Definable domains with one distinguished entrance to each component

At the new root, an entity has one closed term as its description on all
distinguished entrances. The interpretation of the constants in each component
is fixed in advance. The current row of a relation may be freely chosen.
-/

namespace Classicism.Meta.Coalesced.DistinguishedDefinable

open CategoryTheory Classicism.Meta.Intensional

variable {Sig : Signature} {ι : Type} {C : ι → Type} [∀ k, SmallCategory (C k)]
variable (A : ∀ k, Premodel Sig (C k))

def selector : Selector (baseArrows A) A where
  sel ρ _ := {X | ∃ t : Term Sig [] (.rel ρ), ∀ k,
    rootTransport X (dist A k) = (A k).sem (𝟙 _) t .nil}
  shift_mem _ _ m X := by
    rintro ⟨t, ht⟩
    exact ⟨t, fun k => (rootTransport_shift m X (dist A k)).trans (ht k)⟩

abbrev names (σ : Ty) := {c : Sig.Const // Sig.typeOf c = σ}

def nameAtom (σ : Ty) : AtomAction (baseArrows A) A σ :=
  pointAtom A σ (names (Sig := Sig) σ) fun k c =>
    castD (D := (A k).Dom (A k).W₀) c.2 ((A k).I c.1)

/-- Each public name has a root representative. Several root individuals can carry
the same name as their descriptor at the distinguished entrances. -/
structure Representatives (Sig : Signature) where
  carrier : Type
  read : carrier → names (Sig := Sig) .e
  named : names (Sig := Sig) .e → carrier
  read_named (n) : read (named n) = n

namespace Representatives

variable (R : Representatives Sig)

def atom : AtomAction (baseArrows A) A .e :=
  pointAtom A .e R.carrier fun k x =>
    castD (D := (A k).Dom (A k).W₀) (R.read x).2 ((A k).I (R.read x).1)

noncomputable abbrev action :=
  selAction (atom A R) (fun i => nameAtom A (.var i)) (selector A)

noncomputable abbrev inclusion :=
  selIncl (atom A R) (fun i => nameAtom A (.var i)) (selector A)

noncomputable def descriptor : ∀ σ : Ty, (action A R).D σ → Term Sig [] σ
  | .e, x => constAt (R.read x).1 (R.read x).2
  | .var _, x => constAt x.1 x.2
  | .rel _, x => Classical.choose x.2.2

theorem descriptor_at : ∀ (σ : Ty) (x : (action A R).D σ) (k : ι),
    (A k).sem (𝟙 _) (descriptor A R σ x) .nil =
    (A k).Incl σ _ ((action A R).tr σ (dist A k) x)
  | .e, x, k => by
    rw [descriptor, sem_constAt]
    simp [action, atom, nameAtom, pointAtom, selAction, dist]
  | .var _, x, k => by
    rw [descriptor, sem_constAt]
    simp [action, atom, nameAtom, pointAtom, selAction, dist]
  | .rel ρ, x, k =>
    (Classical.choose_spec x.2.2 k).symm.trans
      (incl_relLevel_tr (selector A) ρ _ (dist A k) x).symm

noncomputable def valueAt (c : Sig.Const) : ∀ (σ : Ty), Sig.typeOf c = σ → (action A R).D σ
  | .e, h => R.named ⟨c,h⟩
  | .var _, h => ⟨c, h⟩
  | .rel ρ, h =>
    let y := fun k => castD (D := (A k).Dom (A k).W₀) h ((A k).I c)
    ⟨unionTuples A y, fun j => ⟨_, (rootTransport_unionTuples A y j).symm⟩,
      constAt c h, fun k => by
        rw [rootTransport_unionTuples, sem_constAt]
        simp only [Functor.map_id_apply]
        rfl⟩

noncomputable abbrev value (c : Sig.Const) := valueAt A R c _ rfl

theorem cast_value (c : Sig.Const) {σ : Ty} (h : Sig.typeOf c = σ) :
    castD (D := (action A R).D) h (value A R c) = valueAt A R c σ h := by
  cases h
  rfl

theorem transportsAt (c : Sig.Const) (k : ι) : ∀ (σ : Ty) (h : Sig.typeOf c = σ),
    (action A R).tr σ (dist A k) (valueAt A R c σ h) =
    castD (D := (A k).Dom (A k).W₀) h ((A k).I c)
  | .e, h => by
    let val (n : names (Sig := Sig) .e) :=
      castD (D := (A k).Dom (A k).W₀) n.2 ((A k).I n.1)
    change ((A k).inner .e).map (𝟙 _) (val (R.read (R.named ⟨c,h⟩))) = val ⟨c,h⟩
    rw [R.read_named, Functor.map_id_apply]
  | .var _, h => (A k).inner _ |>.map_id_apply _ _
  | .rel ρ, h => by
    apply (A k).incl_injective ρ _
    refine (incl_relLevel_tr (selector A) ρ _ (dist A k) _).trans ?_
    let y := fun j => castD (D := (A j).Dom (A j).W₀) h ((A j).I c)
    exact (rootTransport_unionTuples A y _).trans
      (congrArg ((A k).incl ρ _) (((A k).inner (.rel ρ)).map_id_apply _ (y k)))

theorem transports : TransportsConstants (action A R) (value A R) :=
  fun c k => transportsAt A R c k _ rfl

variable (ne : Nonempty R.carrier)

noncomputable abbrev model :=
  (action A R).coalescedSum (inclusion A R) ne (value A R)

private theorem transport_of_root {ρ : RTy}
    (Y : Intension (action A R).inner ρ (CoalescedSum.base _)) (k : ι) :
    rootTransport {q | ofRT (atom A R) (fun i => nameAtom A (.var i)) (selector A) q ∈ Y}
      (dist A k) = (action A R).transport (k := k) (V := (A k).W₀) (dist A k) Y := by
  ext ⟨U, a, j⟩
  rfl

theorem isModel (M : ∀ k, (A k).IsModel) : (model A R ne).IsModel := by
  have hQ : (action A R).ComponentsAreModels (value A R) := componentsAreModels (transports A R) M
  apply ((action A R).isModel_iff (inclusion A R) ne (value A R)).2
  refine ⟨hQ, (rootClosed_iff_selected _ _ _ ne (value A R) hQ).2 ?_⟩
  intro m Γ ρ t g
  let sub : Sub Sig Γ [] := fun σ v => descriptor A R σ (g.get v)
  refine ⟨t.subst sub, fun k => ?_⟩
  refine (transport_of_root A R _ k).trans ?_
  have hp := (model A R ne).sem_push (CoalescedSum.endo (baseArrows A) m) t g
    (CoalescedSum.arr (baseArrows A) (dist A k))
  refine (congrArg (action A R).compI hp.symm).trans ?_
  refine ((action A R).sem_arr (inclusion A R) ne (value A R) (dist A k) t _).trans ?_
  refine ((A k).rebase_sem_congr (funext fun c => transports A R c k) (𝟙 _) t _).trans ?_
  rw [(A k).sem_subst (M k)]
  congr 1
  apply IEnv.ext
  intro σ v
  apply (A k).Incl_injective σ _
  refine Eq.trans ?_ (((A k).Incl_subEnv_get (M k) _ _ _ v).trans (descriptor_at A R σ (g.get v) k)).symm
  exact congrArg ((A k).Incl σ _) (IEnv.get_map _ v g)

end Representatives

/-- The ordinary descriptor root represents every individual by its own name. -/
def ordinary (Sig : Signature) : Representatives Sig := ⟨names (Sig := Sig) .e, id, id, fun _ => rfl⟩

noncomputable abbrev action := Representatives.action A (ordinary Sig)
noncomputable abbrev inclusion := Representatives.inclusion A (ordinary Sig)
noncomputable abbrev descriptor := Representatives.descriptor A (ordinary Sig)
abbrev descriptor_at := Representatives.descriptor_at A (ordinary Sig)
noncomputable abbrev valueAt := Representatives.valueAt A (ordinary Sig)
noncomputable abbrev value := Representatives.value A (ordinary Sig)
abbrev transportsAt := Representatives.transportsAt A (ordinary Sig)
abbrev transports := Representatives.transports A (ordinary Sig)
noncomputable abbrev model (ne : Nonempty (names (Sig := Sig) .e)) :=
  Representatives.model A (ordinary Sig) ne
theorem isModel (ne : Nonempty (names (Sig := Sig) .e)) (M : ∀ k, (A k).IsModel) :
    (model A ne).IsModel :=
  Representatives.isModel A (ordinary Sig) ne M

end Classicism.Meta.Coalesced.DistinguishedDefinable
