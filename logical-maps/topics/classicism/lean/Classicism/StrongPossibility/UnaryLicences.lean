import Classicism.StrongPossibility.UnaryReading
import Classicism.Coalesced.DistinguishedDefinable
import Classicism.Coalesced.Complete
import Classicism.Syntax.Russell

/-! The guarded return at a descriptor root. Each root tester has a closed descriptor,
and separation on the canonical family controls its entire cone after each exit. -/

noncomputable section
namespace Classicism.Meta.UnarySP

open CategoryTheory Intensional Coalesced DistinguishedDefinable Term
open Classicism.Proofs.UnarySP

abbrev unaryTy : RTy := Ty.e ⇒ RTy.t
abbrev testerTy : RTy := Ty.rel unaryTy ⇒ RTy.t
abbrev params := [Ty.rel testerTy, Ty.e]

/-- Partially apply the unary operator to its transported individual marker. -/
noncomputable def atMarker {Sig : Signature} {Γ : Ctx} (b : Term Sig Γ .e) :
    Term Sig Γ (Ty.rel testerTy ⇒ unaryTy) :=
  Term.app (StrongPossibility.UnaryReading.op (Sig := Sig)).close b

def diagAt {Sig : Signature} {Γ : Ctx} (b : Term Sig Γ .e) : Term Sig Γ (.rel unaryTy) :=
  let q := atMarker b
  .app q (.lam (exists' (conj (eq' (.app q.weaken.weaken v0) v1) (neg (.app v0 v1)))))

def sameOutput (Sig : Signature) : Formula Sig params :=
  eq' (.app (atMarker v1) v0) (diagAt v1)

def acceptsDiagonal (Sig : Signature) : Formula Sig params := .app v0 (diagAt v1)

def guardedAt {Sig : Signature} (g : Sentence Sig) : Sentence Sig :=
  .app (ofPure guardedLaw.term) g

theorem guardedAt_closed {Sig : Signature} {g : Sentence Sig} (hg : g.closedTypes = true) :
    (guardedAt g).closedTypes = true := by
  change (true && g.closedTypes) = true
  simp only [hg, Bool.and_self]

def expandedGuard {Sig : Signature} (g : Sentence Sig) : Sentence Sig :=
  forall' (forall' (Term.imp (sameOutput Sig) (box (Term.imp g.close (acceptsDiagonal Sig)))))

private theorem weaken_twice {Sig : Signature} {σ τ υ : Ty} (t : Term Sig [] σ) :
    (t.weaken (τ := τ)).weaken (τ := υ) = t.close := by
  calc _ = ((t.close (Γ := [])).weaken (τ := τ)).weaken := by rw [close_nil]
       _ = _ := by rw [close_weaken, close_weaken]

theorem guardedAt_conv {Sig : Signature} (g : Sentence Sig) :
    guardedAt g ≡ expandedGuard g := by
  unfold expandedGuard
  rw [← weaken_twice]
  exact Conv.beta _ g

def plug {Sig : Signature} (b : Term Sig [] .e) (f : Term Sig [] (.rel testerTy)) :
    Sub Sig params [] := Sub.cons f (Sub.cons b Sub.id)

private theorem diag_plug {Sig : Signature} (b : Term Sig [] .e) (f : Term Sig [] (.rel testerTy)) :
    (diagAt (Γ := params) v1).subst (plug b f) =
      let q := Term.app (StrongPossibility.UnaryReading.op (Sig := Sig)) b
      .app q (Diagonal.russell q) := by
  let q := Term.app (StrongPossibility.UnaryReading.op (Sig := Sig)) b
  change Term.app q (.lam (exists' (conj
    (eq' (.app (.app (StrongPossibility.UnaryReading.op (Sig := Sig)).close b.weaken.weaken) v0) v1)
    (neg (.app v0 v1))))) = _
  rw [weaken_twice]
  rfl

private theorem accepts_plug {Sig : Signature} (b : Term Sig [] .e) (f : Term Sig [] (.rel testerTy)) :
    (acceptsDiagonal Sig).subst (plug b f) =
      let q := Term.app (StrongPossibility.UnaryReading.op (Sig := Sig)) b
      Term.app f (.app q (Diagonal.russell q)) :=
  congrArg (Term.app f) (diag_plug b f)

/-- Separation for the public names denoting individuals and the closed tester descriptors. -/
def NamedSeparation (Sig : Signature) [Countable Sig.Const] : Prop :=
  ∀ (b : names (Sig := Sig) .e) (f : Term Sig [] (.rel testerTy)),
    let q := Term.app (StrongPossibility.UnaryReading.op (Sig := Sig)) (constAt b.1 b.2)
    let d := Term.app q (Diagonal.russell q)
    (∀ k, (canonicalFamily Sig k).HoldsSentence (eq' (.app q f) d)) →
    ∀ k, (canonicalFamily Sig k).HoldsSentence (box (.app f d))

section DescriptorRoot

variable {Sig : Signature} [Countable Sig.Const]
local notation "A" => canonicalFamily Sig
variable (R : Representatives Sig) (ne : Nonempty R.carrier)
local notation "RA" => Representatives.action (canonicalFamily Sig) R
local notation "desc" => Representatives.descriptor (canonicalFamily Sig) R
local notation "V" => Representatives.model (canonicalFamily Sig) R ne
local notation "mV" => Representatives.isModel (canonicalFamily Sig) R ne canonicalFamily_isModel

private theorem desc_after (σ : Ty) (x : (RA).D σ)
    {k} {z} (h : (A k).W₀ ⟶ z) :
    (A k).Incl σ z ((RA).tr σ (k := k) h x) =
    (A k).sem h (desc σ x) .nil := by
  have H := (RA).tr_map σ h (dist A k) x
  change (RA).tr σ (k := k) (𝟙 _ ≫ h) x = _ at H
  rw [Category.id_comp] at H
  rw [H, (A k).Incl_map, ← Representatives.descriptor_at]
  simpa only [Category.id_comp, Premodel.push, IEnv.map] using
    ((A k).sem_push (𝟙 _) (desc σ x) .nil h).symm

/-- At every exit, substituting both closed descriptors gives the transported formula. -/
private theorem descriptor_exit (p : Formula Sig params)
    (b : (RA).D .e) (f : (RA).D (.rel testerTy))
    {k} {z} (h : (A k).W₀ ⟶ z) :
    (V).Holds (CoalescedSum.arr (baseArrows A) (x := ⟨k,z⟩) h) p
      (.cons ((RA).tr _ (k := k) h f)
        (.cons ((RA).tr _ (k := k) h b) .nil)) ↔
    (A k).Holds h (p.subst (plug (desc .e b) (desc _ f))) .nil := by
  let K := A k
  let G : IEnv (K.Dom z) params := .cons ((RA).tr _ (k := k) h f)
    (.cons ((RA).tr _ (k := k) h b) .nil)
  refine ((RA).holds_arr (Representatives.inclusion A R) ne
    (Representatives.value A R) (k := k) h p G).trans ?_
  have E := K.rebase_sem_congr (funext fun c =>
    tr_eq_map (Representatives.transports A R) c h) (𝟙 z) p G
  refine (Set.ext_iff.mp E ⟨z, PUnit.unit, 𝟙 z⟩).trans ?_
  have base := K.holds_truncate h (𝟙 z) p G
  rw [Category.comp_id] at base
  refine base.trans ?_
  have env : G = K.subEnv (canonicalFamily_isModel k) h
      (plug (desc .e b) (desc _ f)) .nil := by
    apply IEnv.ext
    intro σ v
    apply K.Incl_injective σ _
    rw [K.Incl_subEnv_get]
    cases v with
    | zero => exact desc_after R _ f h
    | succ v =>
      cases v with
      | zero => exact desc_after R _ b h
      | succ v => cases v
  unfold Premodel.Holds
  rw [K.sem_subst (canonicalFamily_isModel k), ← env]

omit [Countable Sig.Const] in
private theorem persist_eq {C : Type} [SmallCategory C]
    (K : Premodel Sig C) (m : K.IsModel) {Γ : Ctx} {τ : Ty} {u v : Term Sig Γ τ}
    (g : IEnv (K.Dom K.W₀) Γ) (H : K.Holds (𝟙 _) (eq' u v) g)
    {z} (h : K.W₀ ⟶ z) : K.Holds h (eq' u v) (K.push h g) := by
  have eq := congrArg (Outer.map K.inner τ h) ((K.holds_eq m _ _ _ _).1 H)
  rw [← K.sem_push (𝟙 _) u g h, ← K.sem_push (𝟙 _) v g h, Category.id_comp] at eq
  exact (K.holds_eq m _ _ _ _).2 eq

private theorem descriptor_endpoint (sep : NamedSeparation Sig) (guard : Sentence Sig)
    (off : ¬ (V).HoldsSentence guard) : (V).HoldsSentence (expandedGuard guard) := by
  unfold Premodel.HoldsSentence
  rw [expandedGuard, (V).holds_forall mV]
  intro b
  rw [(V).holds_forall mV]
  intro f
  rw [(V).holds_imp mV, (V).holds_box mV]
  intro pos
  let g : IEnv ((V).Dom (V).W₀) params := .cons f (.cons b .nil)
  have hp : ∀ k, (A k).HoldsSentence
      ((sameOutput Sig).subst (plug (desc .e b) (desc _ f))) := by
    intro k
    let h := CoalescedSum.arr (baseArrows A) (x := ⟨k,(A k).W₀⟩) (dist A k)
    exact (descriptor_exit R ne (sameOutput Sig) b f (dist A k)).mp
      (persist_eq (V) mV g pos h)
  intro site h
  rw [(V).holds_imp mV]
  intro hm
  cases site with
  | root =>
    cases h
    exact False.elim (off (((V).holds_close _ _ _).1 hm))
  | of site =>
    rcases site with ⟨k,z⟩
    rw [Category.id_comp]
    apply (descriptor_exit R ne (acceptsDiagonal Sig) b f h).mpr
    let accepted := (acceptsDiagonal Sig).subst (plug (desc .e b) (desc _ f))
    apply ((A k).holdsSentence_truncate (show (A k).W₀ ⟶ z from h) accepted).mp
    have e := diag_plug (desc .e b) (desc _ f)
    have pos' := fun i => hp i
    simp only [sameOutput, eq', subst_app, e] at pos'
    have boxed := sep (R.read b) (desc _ f) pos' k
    apply ((A k).box_iff_truncate (canonicalFamily_isModel k) accepted).mp _ z h
    exact (congrArg (fun p => (A k).HoldsSentence (box p))
      (accepts_plug (constAt (R.read b).1 (R.read b).2) (desc _ f))).mpr boxed

/-- A root where the scalar guard fails satisfies the guarded law. On exits its
tester is evaluated by the same closed descriptor in the original public signature. -/
theorem guard_of_descriptors (sep : NamedSeparation Sig) (guard : Sentence Sig)
    (off : ¬ (V).HoldsSentence guard) : (V).HoldsSentence (guardedAt guard) := by
  unfold Premodel.HoldsSentence Premodel.Holds
  rw [(V).sem_conv mV (guardedAt_conv guard)]
  exact descriptor_endpoint R ne sep guard off

end DescriptorRoot

/-- The public signature's consistent sentences occur at the canonical entrances
for every choice of individual representatives. -/
theorem representatives_complete {Sig : Signature} [Countable Sig.Const] (hS : Sig.Closed)
    (R : Representatives Sig) : (Representatives.action (canonicalFamily Sig) R).CompleteComponentsSig
      (Representatives.value (canonicalFamily Sig) R) := by
  intro p hp cons
  obtain ⟨w, hw⟩ := canonicalFamily_complete hS p hp cons
  refine ⟨w, (canonicalFamily Sig w).W₀, dist (canonicalFamily Sig) w, ?_⟩
  rwa [component_dist (Representatives.transports (canonicalFamily Sig) R) w]

theorem representatives_licence {Sig : Signature} [Countable Sig.Const] (hS : Sig.Closed)
    (R : Representatives Sig) (ne : Nonempty R.carrier) {p : Sentence Sig}
    (hp : (Representatives.model (canonicalFamily Sig) R ne).HoldsSentence p) :
    AxiomSet.Consistent (AxiomSet.maximalist ∪ AxiomSet.single p) := by
  let A := canonicalFamily Sig
  let B := Representatives.model A R ne
  have M : B.IsModel := Representatives.isModel A R ne canonicalFamily_isModel
  apply AxiomSet.Consistent.of_model B M
  apply B.holdsAx_union _ (B.holdsAx_single hp)
  exact B.holdsAx_union B.holdsAx_empty
    ((Representatives.action A R).holdsAx_distinctnessC_of_complete _ _ _ M (representatives_complete hS R))

end Classicism.Meta.UnarySP
