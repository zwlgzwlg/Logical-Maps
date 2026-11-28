import Classicism.Coalesced.StoneCoordinates
import Classicism.Semantics.FullModels

/-!
# Unboxed quantification and mixed graphs at the Stone root

The selected root has every current relational extension at every arity. This
allows a quantifier over an admitted predicate to range over the ordinary powerset
when the body depends only on its current extension. Binary relations between
different native domains, including ordinary graphs of maps between subcarriers,
are witnessed by actual native entities and satisfy the deep application formula.
-/

namespace Classicism.Meta.Coalesced.StoneFan

open CategoryTheory Classicism.Meta.Intensional

variable {Sig : Signature} {ι : Type} {C : ι → Type} [∀ k, SmallCategory (C k)]
  (A : ∀ k, Premodel Sig (C k)) (L : ι → Type) (leaf : ι) [TopologicalSpace (L leaf)]
  (M : ∀ k, (A k).IsModel)

include M

local notation "P" => model A L leaf
local notation "W" => CoalescedSum.base (arrows A L)

/-- Every set of current argument tuples is the current extension of an admitted
root entity. The components can all use the values of the closed bottom relation;
these profiles vary constantly across their labels. -/
theorem current_ext_full (ρ : RTy) (E : Set (Args (P).inner ρ W)) :
    ∃ f : (P).Dom W (.rel ρ), ((P).incl ρ W f).ext' (P).inner = E := by
  let y (k : ι) := Classical.choose (M k (𝟙 (A k).W₀) (Term.botR ρ) .nil)
  let ae := atom A L .e
  let av := fun i => atom A L (.var i)
  let s := sel A L leaf
  let R := {a : args A L leaf ρ | argsRootIn ae av s ρ a ∈ E}
  refine ⟨glue A L leaf R (fun k _ => y k) (IsLocallyConstant.const _), ?_⟩
  ext a
  change argsRootIn ae av s ρ (argsRootOut ae av s ρ a) ∈ E ↔ a ∈ E
  rw [argsRootIn_argsRootOut]

/-- Unboxed universal quantification over an extensional body has the full current
powerset semantics. The hypothesis identifies the meaning of the particular body. -/
theorem forall_current_iff {Γ : Ctx} {ρ : RTy}
    (t : Formula Sig (.rel ρ :: Γ)) (g : IEnv ((P).Dom W) Γ)
    (Q : Set (Args (P).inner ρ W) → Prop)
    (body : ∀ f, (P).Holds (𝟙 W) t (.cons f g) ↔ Q (((P).incl ρ W f).ext' (P).inner)) :
    (P).Holds (𝟙 W) (Term.forall' t) g ↔ ∀ E, Q E := by
  rw [(P).holds_forall (isModel A L leaf M)]
  constructor
  · intro h E
    obtain ⟨f, rfl⟩ := current_ext_full A L leaf M ρ E
    exact (body f).1 (h f)
  · intro h f
    exact (body f).2 (h _)

/-- Every externally specified mixed binary relation has an internal graph with
the required truth values at the root, including on arguments of individual type. -/
theorem realizes_mixed_graph {σ τ : Ty} (F : (P).Dom W σ → (P).Dom W τ → Prop) :
    ∃ G : (P).Dom W (.rel (.arr σ (.arr τ .t))), ∀ a b,
      (P).Holds (𝟙 W) (.app (.app (.var (.succ (.succ .zero))) (.var (.succ .zero))) (.var .zero))
        (.cons b (.cons a (.cons G .nil))) ↔ F a b := by
  let E : Set (Args (P).inner (.arr σ (.arr τ .t)) W) := {u | F u.1 u.2.1}
  obtain ⟨G, hG⟩ := current_ext_full A L leaf M _ E
  refine ⟨G, fun a b => ?_⟩
  rw [Premodel.holds_app_var2]
  change (a,b,PUnit.unit) ∈ ((P).incl _ W G).ext' (P).inner ↔ F a b
  rw [hG]
  rfl

#print axioms current_ext_full
#print axioms forall_current_iff
#print axioms realizes_mixed_graph

end Classicism.Meta.Coalesced.StoneFan
