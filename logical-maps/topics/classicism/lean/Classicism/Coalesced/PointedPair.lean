import Classicism.Coalesced.Distinguished
import Classicism.Coalesced.Interpretations
import Classicism.Semantics.IntensionalFull

/-! A test object with a prescribed individual domain and two exits. Relational
names have their given old and private values. The root row may be empty. -/

namespace Classicism.Meta.Coalesced.PointedPair

open CategoryTheory Classicism.Meta.Intensional

variable {Sig : Signature} {C D : Type} [SmallCategory C] [SmallCategory D]

def Space (C D : Type) : Bool → Type
  | false => C
  | true => D

instance : ∀ b, SmallCategory (Space C D b)
  | false => inferInstanceAs (SmallCategory C)
  | true => inferInstanceAs (SmallCategory D)

def components (O : Premodel Sig C) (P : Premodel Sig D) : ∀ b, Premodel Sig (Space C D b)
  | false => O
  | true => P

variable (O : Premodel Sig C) (P : Premodel Sig D)
variable {X : Type} (l : X → O.Dom O.W₀ .e) (r : X → P.Dom P.W₀ .e)

def images : ∀ b, X → ((components O P) b).Dom ((components O P) b).W₀ .e
  | false => l
  | true => r

abbrev individuals := pointAtom (components O P) .e X (images O P l r)
abbrev varAction (n : Nat) := productAtom (components O P) (.var n)
noncomputable abbrev action := fullAction (individuals O P l r) (varAction O P)
noncomputable abbrev incl := fullRootIncl (individuals O P l r) (varAction O P)

/-- Individual names have a chosen lift through both projections. -/
structure Names where
  lift (c : Sig.Const) (h : Sig.typeOf c = Ty.e) : X
  old (c : Sig.Const) (h : Sig.typeOf c = Ty.e) :
    l (lift c h) = castD (D := O.Dom O.W₀) h (O.I c)
  priv (c : Sig.Const) (h : Sig.typeOf c = Ty.e) :
    r (lift c h) = castD (D := P.Dom P.W₀) h (P.I c)

variable (N : Names O P l r)

noncomputable def valueAt (c : Sig.Const) : ∀ (σ : Ty), Sig.typeOf c = σ → (action O P l r).D σ
  | .e, h => N.lift c h
  | .var _, h => fun b => castD (D := ((components O P) b).Dom _) h (((components O P) b).I c)
  | .rel _, h =>
    let A := components O P
    let y := fun b => castD (D := (A b).Dom _) h ((A b).I c)
    ⟨unionTuples A y, fun j => ⟨_, (rootTransport_unionTuples A y j).symm⟩, trivial⟩

noncomputable abbrev value (c : Sig.Const) := valueAt O P l r N c _ rfl

theorem transportsAt (c : Sig.Const) (b : Bool) : ∀ (σ : Ty) (h : Sig.typeOf c = σ),
    (action O P l r).tr σ (dist (components O P) b) (valueAt O P l r N c σ h) =
    castD (D := ((components O P) b).Dom _) h (((components O P) b).I c)
  | .e, h => by
    cases b
    · exact (((O.inner _).map_id_apply _ _).trans (N.old c h))
    · exact (((P.inner _).map_id_apply _ _).trans (N.priv c h))
  | .var _, h => (((components O P) b).inner _).map_id_apply _ _
  | .rel ρ, h => by
    let A := components O P
    let y := fun i => castD (D := (A i).Dom _) h ((A i).I c)
    apply (A b).incl_injective ρ _
    refine (incl_relLevel_tr Selector.all ρ _ (dist A b) _).trans ?_
    exact (rootTransport_unionTuples A y _).trans
      (congrArg ((A b).incl ρ _) (((A b).inner (.rel ρ)).map_id_apply _ (y b)))

theorem transports : TransportsConstants (action O P l r) (value O P l r N) :=
  fun c b => transportsAt O P l r N c b _ rfl

variable (ne : Nonempty X)

noncomputable abbrev model :=
  (action O P l r).coalescedSum (incl O P l r) ne (value O P l r N)

theorem isModel (o : O.IsModel) (p : P.IsModel) : (model O P l r N ne).IsModel :=
  isModel_distinguished _ _ _ _ _ (transports O P l r N) (fun
    | false => o
    | true => p)

end Classicism.Meta.Coalesced.PointedPair
