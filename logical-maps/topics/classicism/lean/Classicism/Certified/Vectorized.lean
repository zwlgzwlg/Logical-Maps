import Classicism.Certified.Entailed
import Classicism.Syntax.VectorizeDerivable

/-!
# Checks: the map's principles at lists of types

The vectorization of `Syntax/Vectorize.lean` on three principles of different shapes
(Barcan, with a Ty-parameter only; Functionality, with a relational codomain; Relational
Choice, vectorized in its input, its output a single type), at the empty list, at
one-element lists and at a two-element list, each checked by `rfl` against the sentence
written out by hand; and the vectorization theorem of `Syntax/VectorizeDerivable.lean`
applied to a certified derivation, `barcan_r_implies_functionality_r`, to give the arrow
between the list forms. The list forms proper, generated for every principle, are Phase 5
of `VECTORIZATION-PLAN.md`.

The checks are stated outside the namespace `Classicism`, so that the object language's
`imp` and the rest can be used unqualified without meeting the shallow layer's.
-/

namespace Classicism.Meta.VectorizeChecks

/-- A pure sentence at the type variable `var 0`, vectorized along `0 ↦ σs`. -/
noncomputable abbrev listAt (σs : List Ty) (p : Sentence Signature.pure) : Sentence Signature.pure :=
  p.vec1 (Assign.single 0 σs) (Signature.pure_vecFixed _)

/-- Two more short names for variables. -/
abbrev v3 {Sig : Signature} {Γ : Ctx} {σ τ υ ω : Ty} : Term Sig (ω :: υ :: τ :: σ :: Γ) σ :=
  .var (.succ (.succ (.succ .zero)))
@[inherit_doc v3] abbrev v4 {Sig : Signature} {Γ : Ctx} {σ τ υ ω ψ : Ty} :
    Term Sig (ψ :: ω :: υ :: τ :: σ :: Γ) σ :=
  .var (.succ (.succ (.succ (.succ .zero))))

/-- BF over a list implies Functionality over it, into any relational type: the vectorization
theorem applied to the certified derivation of `barcan_r_implies_functionality_r` at `var 0`
(the checks below). -/
theorem barcan_r_implies_functionality_r_list (σs : List Ty) (τ : RTy) :
    C.TheoremMinus (Term.imp (listAt σs (P.Barcan.quoted (.var 0)))
      (listAt σs (P.Functionality.quoted (.var 0) τ))) :=
  C.TheoremMinus.vec (Assign.single 0 σs) (Signature.pure_vecFixed _)
    (Proofs.barcan_r_implies_functionality_r.derivable (.var 0) τ)

end Classicism.Meta.VectorizeChecks

section
open Classicism hiding imp iff
open Classicism.Meta Classicism.Meta.Term Classicism.Meta.VectorizeChecks

/-! ### A one-element list is the type itself, on the nose -/

example (σ : Ty) : listAt [σ] (P.Barcan.quoted (.var 0)) = P.Barcan.quoted σ := rfl
example (σ : Ty) : listAt [σ] (P.Functionality.quoted (.var 0) .t) = P.Functionality.quoted σ .t :=
  rfl
example (σ : Ty) :
    listAt [σ] (P.RelationalChoice.quoted (.var 0) .e) = P.RelationalChoice.quoted σ .e := rfl

/-! ### The empty list -/

/-- BF over no variables: `∀X:t. □X → □X`. -/
example : listAt [] (P.Barcan.quoted (.var 0)) = forall' (σ := Ty.t) (imp (box v0) (box v0)) := rfl

/-- Functionality over no variables, into `t`: `∀X Y:t. X = Y → X = Y`. -/
example : listAt [] (P.Functionality.quoted (.var 0) .t)
    = forall' (σ := Ty.t) (forall' (σ := Ty.t) (imp (eq' v1 v0) (eq' v1 v0))) := rfl

/-- Relational Choice from no inputs, into `e`: every instantiated property of individuals
has a subproperty with exactly one instance. -/
example : listAt [] (P.RelationalChoice.quoted (.var 0) .e)
    = forall' (σ := Ty.rel (Ty.e ⇒ .t)) (imp (exists' (σ := Ty.e) (app v1 v0))
        (exists' (σ := Ty.rel (Ty.e ⇒ .t)) (conj
          (exists' (σ := Ty.e) (conj (app v1 v0)
            (forall' (σ := Ty.e) (imp (app v2 v0) (eq' v1 v0)))))
          (forall' (σ := Ty.e) (imp (app v1 v0) (app v2 v0)))))) := rfl

/-! ### A two-element list -/

/-- BF over `x₁:e, x₂:t`: `∀X. (∀x₁ x₂. □X x₁ x₂) → □∀x₁ x₂. X x₁ x₂`. -/
example : listAt [.e, .t] (P.Barcan.quoted (.var 0))
    = forall' (σ := Ty.rel (Ty.e ⇒ Ty.t ⇒ .t)) (imp
        (forall' (σ := Ty.e) (forall' (σ := Ty.t) (box (app (app v2 v1) v0))))
        (box (forall' (σ := Ty.e) (forall' (σ := Ty.t) (app (app v2 v1) v0))))) := rfl

/-- Functionality over `x₁:e, x₂:t`, into `t`: `∀X Y. (∀z₁ z₂. X z₁ z₂ = Y z₁ z₂) → X = Y`. -/
example : listAt [.e, .t] (P.Functionality.quoted (.var 0) .t)
    = forall' (σ := Ty.rel (Ty.e ⇒ Ty.t ⇒ .t)) (forall' (σ := Ty.rel (Ty.e ⇒ Ty.t ⇒ .t)) (imp
        (forall' (σ := Ty.e) (forall' (σ := Ty.t) (eq' (app (app v3 v1) v0) (app (app v2 v1) v0))))
        (eq' v1 v0))) := rfl

/-- Relational Choice from `x₁:e, x₂:t`, into `e`. -/
example : listAt [.e, .t] (P.RelationalChoice.quoted (.var 0) .e)
    = forall' (σ := Ty.rel (Ty.e ⇒ Ty.t ⇒ Ty.e ⇒ .t)) (imp
        (forall' (σ := Ty.e) (forall' (σ := Ty.t)
          (exists' (σ := Ty.e) (app (app (app v3 v2) v1) v0))))
        (exists' (σ := Ty.rel (Ty.e ⇒ Ty.t ⇒ Ty.e ⇒ .t)) (conj
          (forall' (σ := Ty.e) (forall' (σ := Ty.t) (exists' (σ := Ty.e) (conj
            (app (app (app v3 v2) v1) v0)
            (forall' (σ := Ty.e) (imp (app (app (app v4 v3) v2) v0) (eq' v1 v0)))))))
          (forall' (σ := Ty.e) (forall' (σ := Ty.t) (forall' (σ := Ty.e)
            (imp (app (app (app v3 v2) v1) v0) (app (app (app v4 v2) v1) v0)))))))) := rfl

/-! ### The vectorization theorem on a certified derivation

`barcan_r_implies_functionality_r` is derived in `C⁻` at every pair of types, so at
`var 0`, and vectorizing that derivation gives the arrow between the list forms at every
list, `barcan_r_implies_functionality_r_list`. -/

/-- At the empty list. -/
example : C.TheoremMinus (Sig := Signature.pure) (imp
    (forall' (σ := Ty.t) (imp (box v0) (box v0)))
    (forall' (σ := Ty.t) (forall' (σ := Ty.t) (imp (eq' v1 v0) (eq' v1 v0))))) :=
  barcan_r_implies_functionality_r_list [] .t

/-- At `[e, t]`. -/
example : C.TheoremMinus (Sig := Signature.pure) (imp
    (forall' (σ := Ty.rel (Ty.e ⇒ Ty.t ⇒ .t)) (imp
      (forall' (σ := Ty.e) (forall' (σ := Ty.t) (box (app (app v2 v1) v0))))
      (box (forall' (σ := Ty.e) (forall' (σ := Ty.t) (app (app v2 v1) v0))))))
    (forall' (σ := Ty.rel (Ty.e ⇒ Ty.t ⇒ .t)) (forall' (σ := Ty.rel (Ty.e ⇒ Ty.t ⇒ .t)) (imp
      (forall' (σ := Ty.e) (forall' (σ := Ty.t) (eq' (app (app v3 v1) v0) (app (app v2 v1) v0))))
      (eq' v1 v0))))) :=
  barcan_r_implies_functionality_r_list [.e, .t] .t

/-- At a one-element list, the restricted arrow itself. -/
example (σ : Ty) : C.TheoremMinus (imp (P.Barcan.quoted σ) (P.Functionality.quoted σ .t)) :=
  barcan_r_implies_functionality_r_list [σ] .t

end
