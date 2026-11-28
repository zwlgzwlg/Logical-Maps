import Mathlib.Data.Finite.Sum
import Classicism.Completeness.ReserveConservativity

/-! A finite set of public names, supplemented with one distinguished individual.
The public signature need not have an individual name. -/

namespace Classicism.Meta.FiniteMaxSupport

open Term

variable {Sig : Signature}

/-- The original names in U, together with a new individual marker. -/
def marked (U : Set Sig.Const) : Signature where
  Const := U ⊕ Unit
  typeOf := Sum.elim (fun c => Sig.typeOf c.1) (fun _ => .e)

theorem marked_finite {U : Set Sig.Const} (hU : U.Finite) : Finite (marked U).Const := by
  let _ : Finite U := hU.to_subtype
  exact inferInstanceAs (Finite (U ⊕ Unit))

theorem marked_closed (hS : Sig.Closed) (U : Set Sig.Const) : (marked U).Closed := by
  rintro (c | u)
  · exact hS c.1
  · trivial

theorem marked_admitted (hS : Sig.Closed) {U : Set Sig.Const} {c : Sig.Const}
    (hc : c ∈ U) (ht : Sig.typeOf c ≠ Ty.e) : (marked U).Admitted :=
  ⟨marked_closed hS U, .inl ⟨c, hc⟩, ht⟩

/-- Read a term using only its named constants from U. -/
def narrow (U : Set Sig.Const) : ∀ {Γ : Ctx} {σ : Ty} (t : Term Sig Γ σ),
    t.consts ⊆ U → Term (marked U) Γ σ
  | _, _, .const c, h => .const (Sig := marked U) (.inl ⟨c, h rfl⟩)
  | _, _, .var v, _ => .var v
  | _, _, .app f a, h => .app (narrow U f (fun _ hc => h (Or.inl hc)))
      (narrow U a (fun _ hc => h (Or.inr hc)))
  | _, _, .lam b, h => .lam (narrow U b h)
  | _, _, .and, _ => .and
  | _, _, .or, _ => .or
  | _, _, .not, _ => .not
  | _, _, .all σ, _ => .all σ
  | _, _, .ex σ, _ => .ex σ
  | _, _, .eq σ, _ => .eq σ
  | _, _, .constR ρ, _ => .constR ρ
  | _, _, .negR ρ, _ => .negR ρ
  | _, _, .andR ρ, _ => .andR ρ
  | _, _, .orR ρ, _ => .orR ρ
  | _, _, .coextR ρ, _ => .coextR ρ
  | _, _, .boxR ρ, _ => .boxR ρ
  | _, _, .inclR ρ, _ => .inclR ρ

theorem narrow_ofPure (U : Set Sig.Const) {Γ : Ctx} {σ : Ty}
    (t : Term Signature.pure Γ σ) (h : (ofPure (Sig := Sig) t).consts ⊆ U) :
    narrow U (ofPure t) h = ofPure t := by
  induction t with
  | const c => exact nomatch c
  | app f a hf ha => exact congrArg₂ Term.app (hf _) (ha _)
  | lam b hb => exact congrArg Term.lam (hb _)
  | _ => rfl

theorem closedTypes_narrow (U : Set Sig.Const) {Γ : Ctx} {σ : Ty} (t : Term Sig Γ σ)
    (h : t.consts ⊆ U) : (narrow U t h).closedTypes = t.closedTypes := by
  induction t with
  | app f a hf ha => exact congrArg₂ (· && ·) (hf _) (ha _)
  | lam b hb => exact congrArg (fun z => _ && z) (hb h)
  | _ => rfl

private theorem project (U : Set Sig.Const) {Γ : Ctx} {σ : Ty} (t : Term Sig Γ σ)
    (ht : t.consts ⊆ U) {Δ : Ctx} (r : Ren Γ Δ) (θ : OMap Sig (marked U) Δ)
    (hθ : ∀ c (h : c ∈ U), θ c = some (.const (Sig := marked U) (.inl ⟨c,h⟩))) :
    t.omap r θ = some ((narrow U t ht).rename r) := by
  induction t generalizing Δ with
  | const c => exact hθ c (ht rfl)
  | app f a hf ha =>
    exact omap_app_of r θ (hf _ r θ hθ) (ha _ r θ hθ)
  | lam b hb =>
    apply omap_lam_of
    apply hb ht
    intro c hc
    simp only [OMap.weaken, OMap.rename, hθ c hc]; rfl
  | _ => rfl

private theorem include_narrow (U : Set Sig.Const) {Γ : Ctx} {σ : Ty} (t : Term Sig Γ σ)
    (ht : t.consts ⊆ U) {Δ : Ctx} (r : Ren Γ Δ) (θ : OMap (marked U) Sig Δ)
    (hθ : ∀ c : U, θ (.inl c) = some (.const c.1)) :
    (narrow U t ht).omap r θ = some (t.rename r) := by
  induction t generalizing Δ with
  | const c => exact hθ ⟨c, ht rfl⟩
  | app f a hf ha =>
    exact omap_app_of r θ (hf _ r θ hθ) (ha _ r θ hθ)
  | lam b hb =>
    apply omap_lam_of
    apply hb ht
    intro c
    simp only [OMap.weaken, OMap.rename, hθ c]; rfl
  | _ => rfl

/-- All names outside the support can be interpreted in the marked signature.
There is no fallback at a type variable, which is excluded by signature closure. -/
private def fallback (U : Set Sig.Const) {Γ : Ctx} :
    (σ : Ty) → (∀ i, σ ≠ .var i) → Term (marked U) Γ σ
  | .e, _ => .const (Sig := marked U) (.inr ())
  | .rel ρ, _ => topR ρ
  | .var i, h => (h i rfl).elim

private noncomputable def down (hS : Sig.Closed) (U : Set Sig.Const) (Γ : Ctx) :
    OMap Sig (marked U) Γ := by
  classical
  exact fun c => some (if hc : c ∈ U then .const (Sig := marked U) (.inl ⟨c,hc⟩)
    else fallback U _ (hS.not_var c))

private def up (U : Set Sig.Const) : OMap (marked U) Sig [.e]
  | .inl c => some (.const c.1)
  | .inr _ => some (.var .zero)

/-- Reinsert all the public names, and interpret the sole additional name by a
free individual. Existence at e discharges that individual from the proof. -/
theorem theorem_of_narrow (U : Set Sig.Const) (p : Sentence Sig) (hp : p.consts ⊆ U)
    (d : C.Theorem (narrow U p hp)) : C.Theorem p := by
  obtain ⟨F, _, hd⟩ := Derivable.omap_support (Sig₂ := Sig) d (fun _ ha => ha)
  have hcov : (up U).Covers F := by rintro (c|u) _ <;> rfl
  have dh : C.Derivable ([] : List (Formula Sig [.e])) p.close :=
    hd Ren.ofEmpty (up U) hcov .nil (include_narrow U p hp Ren.ofEmpty (up U) (fun _ => rfl))
  have hw : (p.close : Formula Sig [.e]) = p.weaken := by
    rw [Completeness.close_cons, Term.close_nil]
  rw [hw] at dh
  exact Derivable.exE (Derivable.axiom (show C.axioms existence_e from rfl))
    (Derivable.weaken dh (List.nil_subset _))


/-- Every cited maximality axiom remains a maximality axiom in the marked
finite sublanguage; its nonderivable equality is reflected by reinsertion. -/
theorem maximalist_narrow (U : Set Sig.Const) {p : Sentence Sig} (h : AxiomSet.maximalist p)
    (hp : p.consts ⊆ U) : AxiomSet.maximalist (narrow U p hp) := by
  rcases h with h | ⟨cl, σ, x, y, hn, rfl⟩
  · exact h.elim
  · have hx : x.consts ⊆ U := fun c hc => hp (Or.inr (Or.inl (Or.inr hc)))
    have hy : y.consts ⊆ U := fun c hc => hp (Or.inr (Or.inr hc))
    refine Or.inr ⟨(closedTypes_narrow U _ hp).trans cl, σ, narrow U x hx, narrow U y hy, ?_, rfl⟩
    intro d
    apply hn
    apply Derivable.mono (fun a ha => Or.inl ha)
    apply theorem_of_narrow U (eq' x y) (fun c hc => hp (Or.inr hc))
    exact Derivable.mono (fun a ha => ha.elim id False.elim) d

/-- All public names cited by a finite list of hypotheses. -/
def listSupport : List (Sentence Sig) → Set Sig.Const
  | [] => ∅
  | a :: L => a.consts ∪ listSupport L

theorem finite_listSupport (L : List (Sentence Sig)) : (listSupport L).Finite := by
  induction L with
  | nil => exact Set.finite_empty
  | cons a L ih => exact a.consts_finite.union ih

private theorem image_hyps (hS : Sig.Closed) (U : Set Sig.Const)
    (Ax : AxiomSet Sig) (Ax' : AxiomSet (marked U))
    (good : ∀ a, Ax a → ∀ h : a.consts ⊆ U, Ax' (narrow U a h))
    (L : List (Sentence Sig)) (hL : ∀ a ∈ L, Ax a) (cover : listSupport L ⊆ U) :
    ∃ L', (∀ a' ∈ L', Ax' a') ∧ OMap.Hyps Ren.id (down hS U []) L L' := by
  induction L with
  | nil => exact ⟨[], by simp, .nil⟩
  | cons a L ih =>
    have ha : a.consts ⊆ U := Set.subset_union_left.trans cover
    obtain ⟨L', hL', hmap⟩ := ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))
      (Set.subset_union_right.trans cover)
    refine ⟨narrow U a ha :: L', fun q hq => ?_, .cons ?_ hmap⟩
    · rcases List.mem_cons.1 hq with rfl | hq
      · exact good _ (hL _ List.mem_cons_self) ha
      · exact hL' q hq
    · simpa only [Term.rename_id] using
        project U a ha Ren.id (down hS U []) (fun c hc => by simp [down, hc])

/-- A C proof from a set of axioms transfers to a finite marked sublanguage.
The finite bounds include all names in the goal and all hypotheses cited
in a compact C derivation. The proof may use any further names internally. -/
theorem finite_derivation (hS : Sig.Closed) {Ax : AxiomSet Sig} {p : Sentence Sig}
    (d : Theorem (C.axioms ∪ Ax) p) (K : Set Sig.Const) (hK : K.Finite) :
    ∃ U : Set Sig.Const, U.Finite ∧ K ⊆ U ∧ ∃ hp : p.consts ⊆ U,
      ∀ Ax' : AxiomSet (marked U),
        (∀ a, Ax a → ∀ ha : a.consts ⊆ U, Ax' (narrow U a ha)) →
        Theorem (C.axioms ∪ Ax') (narrow U p hp) := by
  obtain ⟨L, hL, d⟩ := Completeness.Theorem.exists_hyps d
  let U := K ∪ p.consts ∪ listSupport L
  have hp : p.consts ⊆ U := Set.subset_union_right.trans Set.subset_union_left
  refine ⟨U, (hK.union p.consts_finite).union (finite_listSupport L),
    Set.subset_union_left.trans Set.subset_union_left, hp, ?_⟩
  intro Ax' good
  obtain ⟨L', hL', hmap⟩ := image_hyps hS U Ax Ax' good L hL Set.subset_union_right
  obtain ⟨F, _, hd⟩ := Derivable.omap_support (Sig₂ := marked U) d (fun _ ha => ha)
  apply Completeness.Theorem.of_hyps hL'
  refine hd Ren.id (down hS U []) (fun _ _ => rfl) hmap ?_
  simpa only [Term.rename_id] using project U p hp Ren.id (down hS U [])
    (fun c hc => by simp [down, hc])

/-- Ordinary maximality plus any single sentence is consistent whenever
it is consistent in each finite marked sublanguage containing that sentence
and an optional prescribed finite set of public names. -/
theorem consistent_max_of_finite (hS : Sig.Closed) (p : Sentence Sig)
    (K : Set Sig.Const) (hK : K.Finite)
    (localCon : ∀ (U : Set Sig.Const), U.Finite → K ⊆ U → ∀ hp : p.consts ⊆ U,
      AxiomSet.Consistent (AxiomSet.maximalist ∪ AxiomSet.single (narrow U p hp))) :
    AxiomSet.Consistent (AxiomSet.maximalist ∪ AxiomSet.single p) := by
  intro d
  obtain ⟨U,hU,hK',_,hd⟩ := finite_derivation hS d (K ∪ p.consts) (hK.union p.consts_finite)
  have hp : p.consts ⊆ U := Set.subset_union_right.trans hK'
  apply localCon U hU (Set.subset_union_left.trans hK') hp
  apply hd
  intro a ha h
  rcases ha with hmax | rfl
  · exact Or.inl (maximalist_narrow U hmax h)
  · exact Or.inr rfl

end Classicism.Meta.FiniteMaxSupport
