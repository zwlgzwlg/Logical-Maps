import Classicism.Statements
import Classicism.Results.Arity
import Classicism.Results.Forms
import Classicism.Results.SentenceSchemas.Incompatibilities

/-!
# The map's results, certified

One theorem per map result proved in Lean, named by the result's id, whose type is the
statement the map generates for it (`Classicism/Statements.lean`, written by the map's own
generator from its YAML: `map/generate.py`); and one per equivalent form of a principle,
named `<principle id>.<form id>`. These are the map's `lean_ref`s: what `pmap lean-check`
checks, against the generated statement and the map's list of allowed axioms.

Each principle is a schema at every signature (`Certified/Signatures.lean`). A result's
statement reads: for every signature and every schema `Ax` over it, if `Ax` entails each
premise then it entails the conclusion; for an incompatibility, `Ax` is inconsistent. That
is equivalent to the entailment between the schemas, or to their inconsistency. A form's
statement reads: `Ax` entails the principle iff it entails the form.

Each certificate is one line citing the result's proof. That proof is found, for a reader,
by name: `Proofs.<id>` in `Results/Records.lean` (the shallow proof, at one argument type
where the result is at every arity), `<id>` or `Meta.<id>` in `Results/Arity.lean` (a shallow
core, the result at every arity); otherwise the theorem the certificate cites, in
`Results/SentenceSchemas/`; for a form, the two directions in `Results/Forms.lean`.
`#classicism_map_index` (`Tools/MapIndex.lean`) writes these locations out for the map
(`map/index.json`).
-/

namespace Classicism.Meta.AxiomSet

variable {Sig : Signature}

/-! ## Glue: from the entailments as proved to the statements as generated -/

/-- The logical axioms with a pure schema, read in a signature, are among the logical
axioms with the schema read there. -/
theorem ofPure_union_subset (A : AxiomSet Signature.pure) :
    ∀ a, AxiomSet.ofPure (Sig := Sig) (C.axioms ∪ A) a → (C.axioms ∪ AxiomSet.ofPure A) a
  | _, ⟨p, Or.inl h, e⟩ => Or.inl (logical_ofPure_subset _ ⟨p, h, e⟩)
  | _, ⟨p, Or.inr h, e⟩ => Or.inr ⟨p, h, e⟩

/-- **A pure entailment holds in every signature**, its schemas read there. -/
theorem Entails.ofPure {A B : AxiomSet Signature.pure} (h : A ⟹ B) :
    AxiomSet.ofPure (Sig := Sig) A ⟹ AxiomSet.ofPure B := by
  rintro a ⟨p, hp, rfl⟩
  exact Derivable.mono (ofPure_union_subset A) (Theorem.ofPure (h p hp))

theorem Entails.ofPure_union {Ax : AxiomSet Sig} {A B : AxiomSet Signature.pure}
    (h₁ : Ax ⟹ AxiomSet.ofPure A) (h₂ : Ax ⟹ AxiomSet.ofPure B) :
    Ax ⟹ AxiomSet.ofPure (A ∪ B) := by
  rintro a ⟨p, hp | hp, rfl⟩
  · exact h₁ _ ⟨p, hp, rfl⟩
  · exact h₂ _ ⟨p, hp, rfl⟩

theorem Entails.ofPure_empty {Ax : AxiomSet Sig} : Ax ⟹ AxiomSet.ofPure empty := by
  rintro a ⟨p, hp, rfl⟩
  exact hp.elim

theorem Entails.to_empty {Ax : AxiomSet Sig} : Ax ⟹ empty := fun _ h => h.elim

/-- An inconsistency of the pure language is one in every signature. -/
theorem not_consistent_ofPure {A : AxiomSet Signature.pure} (h : ¬ Consistent A) :
    ¬ Consistent (AxiomSet.ofPure (Sig := Sig) A) := fun hc =>
  h fun hb => hc (Derivable.mono (ofPure_union_subset A) (Theorem.ofPure hb))

/-- What is inconsistent stays so when enlarged. -/
theorem not_consistent_mono {A B : AxiomSet Sig} (hs : A ⊆ B) (h : ¬ Consistent A) :
    ¬ Consistent B := fun hc => h (Consistent.mono hs hc)

/-- `C⁻ ⊢ A → ¬B` makes `A` and `B` together inconsistent: the form in which the
translator derives a record concluding `False`. -/
theorem not_consistent_of_imp_neg {A B : Sentence Sig}
    (h : C.TheoremMinus (Term.imp A (Term.neg B))) : ¬ Consistent (single A ∪ single B) :=
  fun hc => hc (Derivable.notE (Theorem.ax (Or.inr rfl))
    (Theorem.mp (Theorem.ofCMinus h) (Theorem.ax (Or.inl rfl))))

/-- `A ∪ B ⊆ A ∪ B'` from `B ⊆ B'`. -/
theorem union_subset_union_right {A B B' : AxiomSet Sig} (h : B ⊆ B') : A ∪ B ⊆ A ∪ B' :=
  fun a => Or.imp_right (h a)

/-- A term of the pure language, read in a signature, is pure there. -/
theorem _root_.Classicism.Meta.Term.pure_ofPure :
    ∀ {Γ : Ctx} {σ : Ty} (t : Term Signature.pure Γ σ), (Term.ofPure (Sig := Sig) t).pure = true
  | _, _, .var _ | _, _, .and | _, _, .or | _, _, .not | _, _, .all _ | _, _, .ex _ | _, _, .eq _
  | _, _, .constR _ | _, _, .negR _ | _, _, .andR _ | _, _, .orR _ | _, _, .coextR _
  | _, _, .boxR _ | _, _, .boxImpR _ => rfl
  | _, _, .const c => nomatch c
  | _, _, .app f a => by simp [Term.ofPure_app, Term.pure, Term.pure_ofPure f, Term.pure_ofPure a]
  | _, _, .lam b => by simpa [Term.ofPure_lam, Term.pure] using Term.pure_ofPure b

/-- No Pure Contingency of the pure language, read in a signature, is part of No Pure
Contingency there. -/
theorem npc_ofPure_subset : AxiomSet.ofPure (npc Signature.pure) ⊆ npc Sig := by
  rintro a ⟨_, ⟨p, -, rfl⟩, rfl⟩
  exact ⟨Term.ofPure p, Term.pure_ofPure p, rfl⟩

/-- B for the pure sentences, likewise. -/
theorem pureB_ofPure_subset : AxiomSet.ofPure (pureB Signature.pure) ⊆ pureB Sig := by
  rintro a ⟨_, ⟨p, -, rfl⟩, rfl⟩
  exact ⟨Term.ofPure p, Term.pure_ofPure p, rfl⟩

/-- An entailment of No Pure Contingency in the form `Results/SentenceSchemas/` proves it, as
the pure version of No Contingency. -/
theorem Entails.to_pureVersion_noContingency {X : AxiomSet Sig}
    (h : X ⟹ AxiomSet.ofPure (npc Signature.pure)) : X ⟹ pureVersion noContingency := by
  rw [pureVersion_noContingency]
  exact h

/-- Likewise for Pure B, as the pure version of Signature B. -/
theorem Entails.to_pureVersion_signatureB {X : AxiomSet Sig}
    (h : X ⟹ AxiomSet.ofPure (pureB Signature.pure)) : X ⟹ pureVersion signatureB := by
  rw [pureVersion_signatureB]
  exact h

end Classicism.Meta.AxiomSet

namespace Classicism.Map

open Meta Meta.AxiomSet

/-- Assemble `Ax ⟹ S`, for `S` a union of the statement's premises, from the hypotheses
`Ax ⟹ Aᵢ`, in any order and nesting, read in the signature or not. -/
syntax "map_premises" : tactic
macro_rules
  | `(tactic| map_premises) => `(tactic| first
      | assumption
      | (rw [← AxiomSet.pureVersion_noContingency]; assumption)
      | (rw [← AxiomSet.pureVersion_signatureB]; assumption)
      | exact AxiomSet.Entails.ofPure_empty
      | exact AxiomSet.Entails.to_empty
      | (apply AxiomSet.Entails.ofPure_union <;> map_premises)
      | (apply AxiomSet.Entails.union <;> map_premises))

/-- A certificate from a pure entailment `h : S ⟹ C`, `S` a union of the premises. -/
macro "map_cert " h:term : tactic => `(tactic| (
  intro _ _
  intros
  exact AxiomSet.Entails.trans (by map_premises) (AxiomSet.Entails.ofPure $h)))

/-- A certificate from an entailment at every signature. -/
macro "map_cert_sig " h:term : tactic => `(tactic| (
  intro _ _
  intros
  exact AxiomSet.Entails.trans (by map_premises) $h))

/-- A certificate for an incompatibility, from a pure inconsistency `h : ¬ Consistent S`. -/
macro "map_cert_incompatible " h:term : tactic => `(tactic| (
  intro _ _
  intros
  intro hc
  exact AxiomSet.not_consistent_ofPure $h (AxiomSet.Consistent.of_entails (by map_premises) hc)))

/-- A certificate for an equivalent form, from the two pure entailments between the
official form and it. -/
macro "map_form " h₁:term:max h₂:term:max : tactic => `(tactic| (
  intro _ _
  exact ⟨fun h => AxiomSet.Entails.trans h (AxiomSet.Entails.ofPure $h₁),
    fun h => AxiomSet.Entails.trans h (AxiomSet.Entails.ofPure $h₂)⟩))

/-- `N ⊆ box A` or `box A ⊆ N`, for `N` the schema of the boxed principle of `A`: their
instances are the same sentences. (`cases` rather than `rintro … rfl`: inside a macro the
pattern `rfl` is renamed by hygiene and no longer substitutes.) -/
syntax "map_box" : tactic
macro_rules
  | `(tactic| map_box) => `(tactic| first
      | (intro _ h; cases h; exact AxiomSet.mem_box rfl)
      | (intro _ h; obtain ⟨_, hc, he⟩ := h; cases he; exact AxiomSet.mem_box ⟨_, hc, rfl⟩)
      | (intro _ h; obtain ⟨_, _, hc₁, hc₂, he⟩ := h; cases he
         exact AxiomSet.mem_box ⟨_, _, hc₁, hc₂, rfl⟩)
      | (intro _ h; obtain ⟨_, hp, he⟩ := h; cases hp; cases he; rfl)
      | (intro _ h; obtain ⟨_, ⟨_, hc, hp⟩, he⟩ := h; cases hp; cases he; exact ⟨_, hc, rfl⟩)
      | (intro _ h; obtain ⟨_, ⟨_, _, hc₁, hc₂, hp⟩, he⟩ := h; cases hp; cases he
         exact ⟨_, _, hc₁, hc₂, rfl⟩))

/-! ## The certificates -/


/-- `actual-profile-r-implies-actuality` -/
theorem actual_profile_r_implies_actuality : Statements.actual_profile_r_implies_actuality := by
  map_cert Meta.actual_profile_r_implies_actuality

/-- `actuality-and-bf-imply-inextensible-comprehension` -/
theorem actuality_and_bf_imply_inextensible_comprehension : Statements.actuality_and_bf_imply_inextensible_comprehension := by
  map_cert Meta.actuality_and_bf_imply_inextensible_comprehension

/-- `actuality-and-distinctness-preserving-collapse-imply-inextensible-comprehension` -/
theorem actuality_and_distinctness_preserving_collapse_imply_inextensible_comprehension : Statements.actuality_and_distinctness_preserving_collapse_imply_inextensible_comprehension := by
  map_cert Meta.actuality_and_distinctness_preserving_collapse_imply_inextensible_comprehension

/-- `actuality-implies-actual-profile-r` -/
theorem actuality_implies_actual_profile_r : Statements.actuality_implies_actual_profile_r := by
  map_cert Proofs.actuality_implies_actual_profile_r.listEntails

/-- `actuality-implies-persistent-comprehension-r` -/
theorem actuality_implies_persistent_comprehension_r : Statements.actuality_implies_persistent_comprehension_r := by
  map_cert Meta.actuality_implies_persistent_comprehension_r

/-- `actuality-implies-transversal` -/
theorem actuality_implies_transversal : Statements.actuality_implies_transversal := by
  map_cert Proofs.actuality_implies_transversal.entails

/-- `actuality-implies-vicinity` -/
theorem actuality_implies_vicinity : Statements.actuality_implies_vicinity := by
  map_cert Proofs.actuality_implies_vicinity.entails

/-- `actuality-implies-weakly-inextensible-comprehension-r` -/
theorem actuality_implies_weakly_inextensible_comprehension_r : Statements.actuality_implies_weakly_inextensible_comprehension_r := by
  map_cert Meta.actuality_implies_weakly_inextensible_comprehension_r

/-- `actuality-incompatible-with-atomlessness` -/
theorem actuality_incompatible_with_atomlessness : Statements.actuality_incompatible_with_atomlessness := by
  map_cert_incompatible (not_consistent_of_imp_neg Proofs.actuality_incompatible_with_atomlessness.derivable)

/-- `atomicity-and-bf-imply-necessary-actuality` -/
theorem atomicity_and_bf_imply_necessary_actuality : Statements.atomicity_and_bf_imply_necessary_actuality := by
  map_cert Proofs.atomicity_and_bf_imply_necessary_actuality.entails

/-- `atomicity-and-bf-imply-strong-leibniz` -/
theorem atomicity_and_bf_imply_strong_leibniz : Statements.atomicity_and_bf_imply_strong_leibniz := by
  map_cert Meta.atomicity_and_bf_imply_strong_leibniz

/-- `atomicity-r-implies-atomicity-t` -/
theorem atomicity_r_implies_atomicity_t : Statements.atomicity_r_implies_atomicity_t := by
  map_cert Proofs.atomicity_r_implies_atomicity_t.entails

/-- `atomicity-t-and-bf-imply-atomicity` -/
theorem atomicity_t_and_bf_imply_atomicity : Statements.atomicity_t_and_bf_imply_atomicity := by
  map_cert Meta.atomicity_t_and_bf_imply_atomicity

/-- `atomicity-t-and-bf-imply-necessary-actuality` -/
theorem atomicity_t_and_bf_imply_necessary_actuality : Statements.atomicity_t_and_bf_imply_necessary_actuality := by
  map_cert Proofs.atomicity_t_and_bf_imply_necessary_actuality.entails

/-- `atomicity-t-and-bf-t-imply-strong-leibniz-t` -/
theorem atomicity_t_and_bf_t_imply_strong_leibniz_t : Statements.atomicity_t_and_bf_t_imply_strong_leibniz_t := by
  map_cert Proofs.atomicity_t_and_bf_t_imply_strong_leibniz_t.entails

/-- `atomicity-t-incompatible-with-atomlessness` -/
theorem atomicity_t_incompatible_with_atomlessness : Statements.atomicity_t_incompatible_with_atomlessness := by
  map_cert_incompatible (not_consistent_of_imp_neg Proofs.atomicity_t_incompatible_with_atomlessness.derivable)

/-- `barcan-r-implies-barcan-t` -/
theorem barcan_r_implies_barcan_t : Statements.barcan_r_implies_barcan_t := by
  map_cert Proofs.barcan_r_implies_barcan_t.entails

/-- `barcan-r-implies-functionality-r` -/
theorem barcan_r_implies_functionality_r : Statements.barcan_r_implies_functionality_r := by
  map_cert Proofs.barcan_r_implies_functionality_r.entails

/-- `boolean-completeness-r-implies-boolean-completeness-t` -/
theorem boolean_completeness_r_implies_boolean_completeness_t : Statements.boolean_completeness_r_implies_boolean_completeness_t := by
  map_cert Proofs.boolean_completeness_r_implies_boolean_completeness_t.entails

/-- `boolean-completeness-r-implies-weakly-inextensible-comprehension-r` -/
theorem boolean_completeness_r_implies_weakly_inextensible_comprehension_r : Statements.boolean_completeness_r_implies_weakly_inextensible_comprehension_r := by
  map_cert Meta.boolean_completeness_r_implies_weakly_inextensible_comprehension_r

/-- `c5-and-actuality-imply-completeness` -/
theorem c5_and_actuality_imply_completeness : Statements.c5_and_actuality_imply_completeness := by
  map_cert Meta.c5_and_actuality_imply_completeness

/-- `c5-and-actuality-imply-rigid-comprehension` -/
theorem c5_and_actuality_imply_rigid_comprehension : Statements.c5_and_actuality_imply_rigid_comprehension := by
  map_cert Meta.c5_and_actuality_imply_rigid_comprehension

/-- `c5-and-atomicity-imply-necessary-atomicity` -/
theorem c5_and_atomicity_imply_necessary_atomicity : Statements.c5_and_atomicity_imply_necessary_atomicity := by
  map_cert Meta.c5_and_atomicity_imply_necessary_atomicity

/-- `c5-and-atomicity-imply-necessary-completeness` -/
theorem c5_and_atomicity_imply_necessary_completeness : Statements.c5_and_atomicity_imply_necessary_completeness := by
  map_cert Meta.c5_and_atomicity_imply_necessary_completeness

/-- `c5-and-atomicity-imply-necessary-plenitude` -/
theorem c5_and_atomicity_imply_necessary_plenitude : Statements.c5_and_atomicity_imply_necessary_plenitude := by
  map_cert Meta.c5_and_atomicity_imply_necessary_plenitude

/-- `c5-and-atomicity-imply-necessary-rigid-comprehension` -/
theorem c5_and_atomicity_imply_necessary_rigid_comprehension : Statements.c5_and_atomicity_imply_necessary_rigid_comprehension := by
  map_cert Meta.c5_and_atomicity_imply_necessary_rigid_comprehension

/-- `c5-and-completeness-imply-actuality` -/
theorem c5_and_completeness_imply_actuality : Statements.c5_and_completeness_imply_actuality := by
  map_cert Proofs.c5_and_completeness_imply_actuality.entails

/-- `c5-and-completeness-imply-plenitude` -/
theorem c5_and_completeness_imply_plenitude : Statements.c5_and_completeness_imply_plenitude := by
  map_cert Meta.c5_and_completeness_imply_plenitude

/-- `c5-and-necessary-actuality-imply-atomicity` -/
theorem c5_and_necessary_actuality_imply_atomicity : Statements.c5_and_necessary_actuality_imply_atomicity := by
  map_cert Meta.c5_and_necessary_actuality_imply_atomicity

/-- `c5-and-necessary-completeness-imply-atomicity` -/
theorem c5_and_necessary_completeness_imply_atomicity : Statements.c5_and_necessary_completeness_imply_atomicity := by
  map_cert Meta.c5_and_necessary_completeness_imply_atomicity

/-- `c5-and-necessary-rigid-comprehension-imply-necessary-gallin-comprehension` -/
theorem c5_and_necessary_rigid_comprehension_imply_necessary_gallin_comprehension : Statements.c5_and_necessary_rigid_comprehension_imply_necessary_gallin_comprehension := by
  map_cert _root_.Classicism.c5_and_necessary_rigid_comprehension_imply_necessary_gallin_comprehension.entails

/-- `c5-and-persistent-comprehension-imply-gallin` -/
theorem c5_and_persistent_comprehension_imply_gallin : Statements.c5_and_persistent_comprehension_imply_gallin := by
  map_cert _root_.Classicism.c5_and_persistent_comprehension_imply_gallin.entails

/-- `classicism-implies-broad-necessitism-r` -/
theorem classicism_implies_broad_necessitism_r : Statements.classicism_implies_broad_necessitism_r := by
  map_cert Proofs.classicism_implies_broad_necessitism_r.entails

/-- `classicism-implies-converse-barcan-r` -/
theorem classicism_implies_converse_barcan_r : Statements.classicism_implies_converse_barcan_r := by
  map_cert Proofs.classicism_implies_converse_barcan_r.entails

/-- `classicism-implies-existence-r` -/
theorem classicism_implies_existence_r : Statements.classicism_implies_existence_r := by
  map_cert Meta.classicism_implies_existence_r

/-- `classicism-implies-identity-necessary-r` -/
theorem classicism_implies_identity_necessary_r : Statements.classicism_implies_identity_necessary_r := by
  map_cert Proofs.classicism_implies_identity_necessary_r.entails

/-- `classicism-implies-intensionality-r` -/
theorem classicism_implies_intensionality_r : Statements.classicism_implies_intensionality_r := by
  map_cert Proofs.classicism_implies_intensionality_r.entails

/-- `classicism-implies-modal-four` -/
theorem classicism_implies_modal_four : Statements.classicism_implies_modal_four := by
  map_cert Proofs.classicism_implies_modal_four.entails

/-- `classicism-implies-modal-k` -/
theorem classicism_implies_modal_k : Statements.classicism_implies_modal_k := by
  map_cert Proofs.classicism_implies_modal_k.entails

/-- `classicism-implies-modal-t` -/
theorem classicism_implies_modal_t : Statements.classicism_implies_modal_t := by
  map_cert Proofs.classicism_implies_modal_t.entails

/-- `classicism-implies-modalized-fregean` -/
theorem classicism_implies_modalized_fregean : Statements.classicism_implies_modalized_fregean := by
  map_cert Proofs.classicism_implies_modalized_fregean.entails

/-- `classicism-implies-modalized-functionality-r` -/
theorem classicism_implies_modalized_functionality_r : Statements.classicism_implies_modalized_functionality_r := by
  map_cert Proofs.classicism_implies_modalized_functionality_r.entails

/-- `classicism-implies-modalized-plenitude-r` -/
theorem classicism_implies_modalized_plenitude_r : Statements.classicism_implies_modalized_plenitude_r := by
  map_cert Meta.classicism_implies_modalized_plenitude_r

/-- `completeness-and-actuality-imply-weak-rigid-comprehension` -/
theorem completeness_and_actuality_imply_weak_rigid_comprehension : Statements.completeness_and_actuality_imply_weak_rigid_comprehension := by
  map_cert Meta.completeness_and_actuality_imply_weak_rigid_comprehension

/-- `distinctness-necessary-r-implies-distinctness-necessary-t` -/
theorem distinctness_necessary_r_implies_distinctness_necessary_t : Statements.distinctness_necessary_r_implies_distinctness_necessary_t := by
  map_cert Proofs.distinctness_necessary_r_implies_distinctness_necessary_t.entails

/-- `distinctness-necessary-t-implies-modal-five` -/
theorem distinctness_necessary_t_implies_modal_five : Statements.distinctness_necessary_t_implies_modal_five := by
  map_cert Proofs.distinctness_necessary_t_implies_modal_five.entails

/-- `distinctness-necessary-t-implies-vicinity` -/
theorem distinctness_necessary_t_implies_vicinity : Statements.distinctness_necessary_t_implies_vicinity := by
  map_cert Proofs.distinctness_necessary_t_implies_vicinity.entails

/-- `distinctness-preserving-collapse-and-nd-imply-fregean-axiom` -/
theorem distinctness_preserving_collapse_and_nd_imply_fregean_axiom : Statements.distinctness_preserving_collapse_and_nd_imply_fregean_axiom := by
  map_cert Proofs.distinctness_preserving_collapse_and_nd_imply_fregean_axiom.entails

/-- `distinctness-schema-r-implies-possibility-schema-r` -/
theorem distinctness_schema_r_implies_possibility_schema_r : Statements.distinctness_schema_r_implies_possibility_schema_r := by
  map_cert Meta.distinctness_schema_r_implies_possibility_schema_r

/-- `distinctness-signature-r-implies-possibility-signature-r` -/
theorem distinctness_signature_r_implies_possibility_signature_r : Statements.distinctness_signature_r_implies_possibility_signature_r := by
  map_cert_sig Meta.distinctness_signature_r_implies_possibility_signature_r

/-- `extensionality-r-implies-actuality` -/
theorem extensionality_r_implies_actuality : Statements.extensionality_r_implies_actuality := by
  map_cert Proofs.extensionality_r_implies_actuality.entails

/-- `extensionality-r-implies-atomicity-r` -/
theorem extensionality_r_implies_atomicity_r : Statements.extensionality_r_implies_atomicity_r := by
  map_cert Meta.extensionality_r_implies_atomicity_r

/-- `extensionality-r-implies-boolean-completeness-r` -/
theorem extensionality_r_implies_boolean_completeness_r : Statements.extensionality_r_implies_boolean_completeness_r := by
  map_cert Meta.extensionality_r_implies_boolean_completeness_r

/-- `extensionality-r-implies-fregean-axiom` -/
theorem extensionality_r_implies_fregean_axiom : Statements.extensionality_r_implies_fregean_axiom := by
  map_cert Proofs.extensionality_r_implies_fregean_axiom.entails

/-- `extensionality-r-implies-functionality-r` -/
theorem extensionality_r_implies_functionality_r : Statements.extensionality_r_implies_functionality_r := by
  map_cert Proofs.extensionality_r_implies_functionality_r.entails

/-- `extensionality-r-implies-necessary-extensionality-r` -/
theorem extensionality_r_implies_necessary_extensionality_r : Statements.extensionality_r_implies_necessary_extensionality_r := by
  map_cert Proofs.extensionality_r_implies_necessary_extensionality_r.entails

/-- `extensionality-r-implies-plenitude-r` -/
theorem extensionality_r_implies_plenitude_r : Statements.extensionality_r_implies_plenitude_r := by
  map_cert Meta.extensionality_r_implies_plenitude_r

/-- `extensionality-r-implies-rigid-comprehension-r` -/
theorem extensionality_r_implies_rigid_comprehension_r : Statements.extensionality_r_implies_rigid_comprehension_r := by
  map_cert _root_.Classicism.extensionality_r_implies_rigid_comprehension_r.entails

/-- `fregean-axiom-implies-distinctness-preserving-collapse` -/
theorem fregean_axiom_implies_distinctness_preserving_collapse : Statements.fregean_axiom_implies_distinctness_preserving_collapse := by
  map_cert Proofs.fregean_axiom_implies_distinctness_preserving_collapse.entails

/-- `fregean-axiom-implies-extensionality-r` -/
theorem fregean_axiom_implies_extensionality_r : Statements.fregean_axiom_implies_extensionality_r := by
  map_cert Proofs.fregean_axiom_implies_extensionality_r.entails

/-- `fregean-axiom-implies-necessary-distinctness-necessary-r` -/
theorem fregean_axiom_implies_necessary_distinctness_necessary_r : Statements.fregean_axiom_implies_necessary_distinctness_necessary_r := by
  map_cert Proofs.fregean_axiom_implies_necessary_distinctness_necessary_r.entails

/-- `fregean-axiom-implies-necessary-fregean-axiom` -/
theorem fregean_axiom_implies_necessary_fregean_axiom : Statements.fregean_axiom_implies_necessary_fregean_axiom := by
  map_cert Proofs.fregean_axiom_implies_necessary_fregean_axiom.entails

/-- `fregean-axiom-implies-no-contingency-signature-r` -/
theorem fregean_axiom_implies_no_contingency_signature_r : Statements.fregean_axiom_implies_no_contingency_signature_r := by
  map_cert_sig fregean_entails_noContingency

/-- `fregean-axiom-implies-no-pure-contingency-r` -/
theorem fregean_axiom_implies_no_pure_contingency_r : Statements.fregean_axiom_implies_no_pure_contingency_r := by
  map_cert_sig (Entails.to_pureVersion_noContingency (Entails.ofPure fregean_entails_npc_pure))

/-- `functional-choice-r-implies-plenitude-r` -/
theorem functional_choice_r_implies_plenitude_r : Statements.functional_choice_r_implies_plenitude_r := by
  map_cert Proofs.functional_choice_r_implies_plenitude_r.entails

/-- `functional-choice-r-implies-relational-choice-r` -/
theorem functional_choice_r_implies_relational_choice_r : Statements.functional_choice_r_implies_relational_choice_r := by
  map_cert Proofs.functional_choice_r_implies_relational_choice_r.entails

/-- `functionality-r-implies-tractarianism-r` -/
theorem functionality_r_implies_tractarianism_r : Statements.functionality_r_implies_tractarianism_r := by
  map_cert Proofs.functionality_r_implies_tractarianism_r.entails

/-- `gallin-comprehension-and-bf-imply-rigid-comprehension` -/
theorem gallin_comprehension_and_bf_imply_rigid_comprehension : Statements.gallin_comprehension_and_bf_imply_rigid_comprehension := by
  map_cert Meta.gallin_comprehension_and_bf_imply_rigid_comprehension

/-- `gallin-comprehension-and-bf-imply-weak-rigid-comprehension` -/
theorem gallin_comprehension_and_bf_imply_weak_rigid_comprehension : Statements.gallin_comprehension_and_bf_imply_weak_rigid_comprehension := by
  map_cert Meta.gallin_comprehension_and_bf_imply_weak_rigid_comprehension

/-- `gallin-comprehension-implies-nd` -/
theorem gallin_comprehension_implies_nd : Statements.gallin_comprehension_implies_nd := by
  map_cert Proofs.gallin_comprehension_implies_nd.entails

/-- `inextensible-comprehension-r-implies-weakly-inextensible-comprehension-r` -/
theorem inextensible_comprehension_r_implies_weakly_inextensible_comprehension_r : Statements.inextensible_comprehension_r_implies_weakly_inextensible_comprehension_r := by
  map_cert Proofs.inextensible_comprehension_r_implies_weakly_inextensible_comprehension_r.entails

/-- `maximalist-distinctness-incompatible-with-nd` -/
theorem maximalist_distinctness_incompatible_with_nd : Statements.maximalist_distinctness_incompatible_with_nd := by
  map_cert_incompatible maximalist_nd_inconsistent

/-- `maximalist-distinctness-incompatible-with-necessary-actuality` -/
theorem maximalist_distinctness_incompatible_with_necessary_actuality : Statements.maximalist_distinctness_incompatible_with_necessary_actuality := by
  map_cert_incompatible maximalist_necActuality_inconsistent

/-- `maximalist-distinctness-incompatible-with-necessary-atomicity-r` -/
theorem maximalist_distinctness_incompatible_with_necessary_atomicity_r : Statements.maximalist_distinctness_incompatible_with_necessary_atomicity_r := by
  map_cert_incompatible
    (not_consistent_mono (B := maximalist ∪ P.NecAtomicity.schema)
      (union_subset_union_right (A := maximalist) (B := AxiomSet.box P.Atomicity.schema)
        (B' := P.NecAtomicity.schema) (by map_box)) maximalist_necAtomicity_inconsistent)

/-- `maximalist-distinctness-incompatible-with-necessary-barcan-r` -/
theorem maximalist_distinctness_incompatible_with_necessary_barcan_r : Statements.maximalist_distinctness_incompatible_with_necessary_barcan_r := by
  map_cert_incompatible
    (not_consistent_mono (B := maximalist ∪ P.NecBarcan.schema)
      (union_subset_union_right (A := maximalist) (B := AxiomSet.box P.Barcan.schema)
        (B' := P.NecBarcan.schema) (by map_box)) maximalist_necBarcan_inconsistent)

/-- `maximalist-distinctness-incompatible-with-necessary-boolean-completeness-r` -/
theorem maximalist_distinctness_incompatible_with_necessary_boolean_completeness_r : Statements.maximalist_distinctness_incompatible_with_necessary_boolean_completeness_r := by
  map_cert_incompatible maximalist_necBooleanCompleteness_inconsistent'

/-- `maximalist-distinctness-incompatible-with-necessary-tractarianism-r` -/
theorem maximalist_distinctness_incompatible_with_necessary_tractarianism_r : Statements.maximalist_distinctness_incompatible_with_necessary_tractarianism_r := by
  map_cert_incompatible
    (not_consistent_mono (B := maximalist ∪ P.NecTractarianism.schema)
      (union_subset_union_right (A := maximalist) (B := AxiomSet.box P.Tractarianism.schema)
        (B' := P.NecTractarianism.schema) (by map_box)) maximalist_necTractarianism_inconsistent)

/-- `modal-b-implies-distinctness-necessary-r` -/
theorem modal_b_implies_distinctness_necessary_r : Statements.modal_b_implies_distinctness_necessary_r := by
  map_cert Proofs.modal_b_implies_distinctness_necessary_r.entails

/-- `modal-b-implies-signature-b-r` -/
theorem modal_b_implies_signature_b_r : Statements.modal_b_implies_signature_b_r := by
  map_cert_sig modalB_entails_signatureB

/-- `modal-five-implies-modal-b` -/
theorem modal_five_implies_modal_b : Statements.modal_five_implies_modal_b := by
  map_cert Proofs.modal_five_implies_modal_b.entails

/-- `nd-and-bf-imply-necessary-nd` -/
theorem nd_and_bf_imply_necessary_nd : Statements.nd_and_bf_imply_necessary_nd := by
  map_cert Proofs.nd_and_bf_imply_necessary_nd.entails

/-- `necessary-actuality-implies-actuality` -/
theorem necessary_actuality_implies_actuality : Statements.necessary_actuality_implies_actuality := by
  map_cert Proofs.necessary_actuality_implies_actuality.entails

/-- `necessary-actuality-implies-necessary-transversal` -/
theorem necessary_actuality_implies_necessary_transversal : Statements.necessary_actuality_implies_necessary_transversal := by
  map_cert Proofs.necessary_actuality_implies_necessary_transversal.entails

/-- `necessary-actuality-implies-necessary-vicinity` -/
theorem necessary_actuality_implies_necessary_vicinity : Statements.necessary_actuality_implies_necessary_vicinity := by
  map_cert Proofs.necessary_actuality_implies_necessary_vicinity.entails

/-- `necessary-actuality-implies-necessary-weakly-inextensible-comprehension-r` -/
theorem necessary_actuality_implies_necessary_weakly_inextensible_comprehension_r : Statements.necessary_actuality_implies_necessary_weakly_inextensible_comprehension_r := by
  map_cert Meta.necessary_actuality_implies_necessary_weakly_inextensible_comprehension_r

/-- `necessary-atomicity-and-necessary-bf-imply-necessary-strong-leibniz` -/
theorem necessary_atomicity_and_necessary_bf_imply_necessary_strong_leibniz : Statements.necessary_atomicity_and_necessary_bf_imply_necessary_strong_leibniz := by
  map_cert Meta.necessary_atomicity_and_necessary_bf_imply_necessary_strong_leibniz

/-- `necessary-atomicity-and-necessary-bf-t-imply-necessary-strong-leibniz-t` -/
theorem necessary_atomicity_and_necessary_bf_t_imply_necessary_strong_leibniz_t : Statements.necessary_atomicity_and_necessary_bf_t_imply_necessary_strong_leibniz_t := by
  map_cert Proofs.necessary_atomicity_and_necessary_bf_t_imply_necessary_strong_leibniz_t.entails

/-- `necessary-atomicity-r-implies-atomicity-r` -/
theorem necessary_atomicity_r_implies_atomicity_r : Statements.necessary_atomicity_r_implies_atomicity_r := by
  map_cert Proofs.necessary_atomicity_r_implies_atomicity_r.entails

/-- `necessary-barcan-r-implies-barcan-r` -/
theorem necessary_barcan_r_implies_barcan_r : Statements.necessary_barcan_r_implies_barcan_r := by
  map_cert Proofs.necessary_barcan_r_implies_barcan_r.entails

/-- `necessary-barcan-r-implies-necessary-barcan-t` -/
theorem necessary_barcan_r_implies_necessary_barcan_t : Statements.necessary_barcan_r_implies_necessary_barcan_t := by
  map_cert Proofs.necessary_barcan_r_implies_necessary_barcan_t.entails

/-- `necessary-barcan-r-implies-necessary-functionality-r` -/
theorem necessary_barcan_r_implies_necessary_functionality_r : Statements.necessary_barcan_r_implies_necessary_functionality_r := by
  map_cert Proofs.necessary_barcan_r_implies_necessary_functionality_r.entails

/-- `necessary-barcan-t-implies-barcan-t` -/
theorem necessary_barcan_t_implies_barcan_t : Statements.necessary_barcan_t_implies_barcan_t := by
  map_cert Proofs.necessary_barcan_t_implies_barcan_t.entails

/-- `necessary-bf-and-actuality-imply-inextensible-comprehension` -/
theorem necessary_bf_and_actuality_imply_inextensible_comprehension : Statements.necessary_bf_and_actuality_imply_inextensible_comprehension := by
  map_cert Meta.necessary_bf_and_actuality_imply_inextensible_comprehension

/-- `necessary-boolean-completeness-r-implies-boolean-completeness-r` -/
theorem necessary_boolean_completeness_r_implies_boolean_completeness_r : Statements.necessary_boolean_completeness_r_implies_boolean_completeness_r := by
  map_cert Proofs.necessary_boolean_completeness_r_implies_boolean_completeness_r.entails

/-- `necessary-distinctness-necessary-r-implies-distinctness-necessary-r` -/
theorem necessary_distinctness_necessary_r_implies_distinctness_necessary_r : Statements.necessary_distinctness_necessary_r_implies_distinctness_necessary_r := by
  map_cert Proofs.necessary_distinctness_necessary_r_implies_distinctness_necessary_r.entails

/-- `necessary-distinctness-necessary-r-implies-necessary-barcan-r` -/
theorem necessary_distinctness_necessary_r_implies_necessary_barcan_r : Statements.necessary_distinctness_necessary_r_implies_necessary_barcan_r := by
  map_cert Proofs.necessary_distinctness_necessary_r_implies_necessary_barcan_r.entails

/-- `necessary-distinctness-necessary-r-implies-necessary-distinctness-necessary-t` -/
theorem necessary_distinctness_necessary_r_implies_necessary_distinctness_necessary_t : Statements.necessary_distinctness_necessary_r_implies_necessary_distinctness_necessary_t := by
  map_cert Proofs.necessary_distinctness_necessary_r_implies_necessary_distinctness_necessary_t.entails

/-- `necessary-distinctness-necessary-r-implies-necessary-modal-five` -/
theorem necessary_distinctness_necessary_r_implies_necessary_modal_five : Statements.necessary_distinctness_necessary_r_implies_necessary_modal_five := by
  map_cert Proofs.necessary_distinctness_necessary_r_implies_necessary_modal_five.entails

/-- `necessary-distinctness-necessary-t-implies-distinctness-necessary-t` -/
theorem necessary_distinctness_necessary_t_implies_distinctness_necessary_t : Statements.necessary_distinctness_necessary_t_implies_distinctness_necessary_t := by
  map_cert Proofs.necessary_distinctness_necessary_t_implies_distinctness_necessary_t.entails

/-- `necessary-distinctness-necessary-t-implies-necessary-distinctness-necessary-r` -/
theorem necessary_distinctness_necessary_t_implies_necessary_distinctness_necessary_r : Statements.necessary_distinctness_necessary_t_implies_necessary_distinctness_necessary_r := by
  map_cert Proofs.necessary_distinctness_necessary_t_implies_necessary_distinctness_necessary_r.entails

/-- `necessary-distinctness-necessary-t-implies-necessary-vicinity` -/
theorem necessary_distinctness_necessary_t_implies_necessary_vicinity : Statements.necessary_distinctness_necessary_t_implies_necessary_vicinity := by
  map_cert Proofs.necessary_distinctness_necessary_t_implies_necessary_vicinity.entails

/-- `necessary-extensionality-r-implies-extensionality-r` -/
theorem necessary_extensionality_r_implies_extensionality_r : Statements.necessary_extensionality_r_implies_extensionality_r := by
  map_cert Proofs.necessary_extensionality_r_implies_extensionality_r.entails

/-- `necessary-fregean-axiom-implies-fregean-axiom` -/
theorem necessary_fregean_axiom_implies_fregean_axiom : Statements.necessary_fregean_axiom_implies_fregean_axiom := by
  map_cert Proofs.necessary_fregean_axiom_implies_fregean_axiom.entails

/-- `necessary-functional-choice-r-implies-functional-choice-r` -/
theorem necessary_functional_choice_r_implies_functional_choice_r : Statements.necessary_functional_choice_r_implies_functional_choice_r := by
  map_cert Proofs.necessary_functional_choice_r_implies_functional_choice_r.entails

/-- `necessary-functional-choice-r-implies-necessary-plenitude-r` -/
theorem necessary_functional_choice_r_implies_necessary_plenitude_r : Statements.necessary_functional_choice_r_implies_necessary_plenitude_r := by
  map_cert Proofs.necessary_functional_choice_r_implies_necessary_plenitude_r.entails

/-- `necessary-functional-choice-r-implies-necessary-relational-choice-r` -/
theorem necessary_functional_choice_r_implies_necessary_relational_choice_r : Statements.necessary_functional_choice_r_implies_necessary_relational_choice_r := by
  map_cert Proofs.necessary_functional_choice_r_implies_necessary_relational_choice_r.entails

/-- `necessary-functionality-r-implies-functionality-r` -/
theorem necessary_functionality_r_implies_functionality_r : Statements.necessary_functionality_r_implies_functionality_r := by
  map_cert Proofs.necessary_functionality_r_implies_functionality_r.entails

/-- `necessary-functionality-r-implies-necessary-tractarianism-r` -/
theorem necessary_functionality_r_implies_necessary_tractarianism_r : Statements.necessary_functionality_r_implies_necessary_tractarianism_r := by
  map_cert Proofs.necessary_functionality_r_implies_necessary_tractarianism_r.entails

/-- `necessary-gallin-comprehension-implies-gallin-comprehension` -/
theorem necessary_gallin_comprehension_implies_gallin_comprehension : Statements.necessary_gallin_comprehension_implies_gallin_comprehension := by
  map_cert Proofs.necessary_gallin_comprehension_implies_gallin_comprehension.entails

/-- `necessary-gallin-comprehension-implies-necessary-nd` -/
theorem necessary_gallin_comprehension_implies_necessary_nd : Statements.necessary_gallin_comprehension_implies_necessary_nd := by
  map_cert Proofs.necessary_gallin_comprehension_implies_necessary_nd.entails

/-- `necessary-gallin-comprehension-implies-necessary-rigid-comprehension` -/
theorem necessary_gallin_comprehension_implies_necessary_rigid_comprehension : Statements.necessary_gallin_comprehension_implies_necessary_rigid_comprehension := by
  map_cert Meta.necessary_gallin_comprehension_implies_necessary_rigid_comprehension

/-- `necessary-modal-b-implies-modal-b` -/
theorem necessary_modal_b_implies_modal_b : Statements.necessary_modal_b_implies_modal_b := by
  map_cert Proofs.necessary_modal_b_implies_modal_b.entails

/-- `necessary-modal-b-implies-necessary-distinctness-necessary-r` -/
theorem necessary_modal_b_implies_necessary_distinctness_necessary_r : Statements.necessary_modal_b_implies_necessary_distinctness_necessary_r := by
  map_cert Proofs.necessary_modal_b_implies_necessary_distinctness_necessary_r.entails

/-- `necessary-modal-five-implies-modal-five` -/
theorem necessary_modal_five_implies_modal_five : Statements.necessary_modal_five_implies_modal_five := by
  map_cert Proofs.necessary_modal_five_implies_modal_five.entails

/-- `necessary-modal-five-implies-necessary-modal-b` -/
theorem necessary_modal_five_implies_necessary_modal_b : Statements.necessary_modal_five_implies_necessary_modal_b := by
  map_cert Proofs.necessary_modal_five_implies_necessary_modal_b.entails

/-- `necessary-nd-implies-bf` -/
theorem necessary_nd_implies_bf : Statements.necessary_nd_implies_bf := by
  map_cert Proofs.necessary_nd_implies_bf.entails

/-- `necessary-plenitude-r-implies-atomicity-r` -/
theorem necessary_plenitude_r_implies_atomicity_r : Statements.necessary_plenitude_r_implies_atomicity_r := by
  map_cert Meta.necessary_plenitude_r_implies_atomicity_r

/-- `necessary-plenitude-r-implies-necessary-actuality` -/
theorem necessary_plenitude_r_implies_necessary_actuality : Statements.necessary_plenitude_r_implies_necessary_actuality := by
  map_cert Proofs.necessary_plenitude_r_implies_necessary_actuality.entails

/-- `necessary-plenitude-r-implies-necessary-atomicity-r` -/
theorem necessary_plenitude_r_implies_necessary_atomicity_r : Statements.necessary_plenitude_r_implies_necessary_atomicity_r := by
  map_cert Meta.necessary_plenitude_r_implies_necessary_atomicity_r

/-- `necessary-plenitude-r-implies-necessary-distinctness-necessary-r` -/
theorem necessary_plenitude_r_implies_necessary_distinctness_necessary_r : Statements.necessary_plenitude_r_implies_necessary_distinctness_necessary_r := by
  map_cert Proofs.necessary_plenitude_r_implies_necessary_distinctness_necessary_r.entails

/-- `necessary-plenitude-r-implies-plenitude-r` -/
theorem necessary_plenitude_r_implies_plenitude_r : Statements.necessary_plenitude_r_implies_plenitude_r := by
  map_cert Proofs.necessary_plenitude_r_implies_plenitude_r.entails

/-- `necessary-relational-choice-and-necessary-plenitude-imply-necessary-functional-choice` -/
theorem necessary_relational_choice_and_necessary_plenitude_imply_necessary_functional_choice : Statements.necessary_relational_choice_and_necessary_plenitude_imply_necessary_functional_choice := by
  map_cert Proofs.necessary_relational_choice_and_necessary_plenitude_imply_necessary_functional_choice.entails

/-- `necessary-relational-choice-r-implies-relational-choice-r` -/
theorem necessary_relational_choice_r_implies_relational_choice_r : Statements.necessary_relational_choice_r_implies_relational_choice_r := by
  map_cert Proofs.necessary_relational_choice_r_implies_relational_choice_r.entails

/-- `necessary-rigid-comprehension-r-implies-necessary-actuality` -/
theorem necessary_rigid_comprehension_r_implies_necessary_actuality : Statements.necessary_rigid_comprehension_r_implies_necessary_actuality := by
  map_cert Proofs.necessary_rigid_comprehension_r_implies_necessary_actuality.entails

/-- `necessary-rigid-comprehension-r-implies-necessary-boolean-completeness-r` -/
theorem necessary_rigid_comprehension_r_implies_necessary_boolean_completeness_r : Statements.necessary_rigid_comprehension_r_implies_necessary_boolean_completeness_r := by
  map_cert Meta.necessary_rigid_comprehension_r_implies_necessary_boolean_completeness_r

/-- `necessary-rigid-comprehension-r-implies-rigid-comprehension-r` -/
theorem necessary_rigid_comprehension_r_implies_rigid_comprehension_r : Statements.necessary_rigid_comprehension_r_implies_rigid_comprehension_r := by
  map_cert Proofs.necessary_rigid_comprehension_r_implies_rigid_comprehension_r.entails

/-- `necessary-strong-leibniz-implies-necessary-atomicity` -/
theorem necessary_strong_leibniz_implies_necessary_atomicity : Statements.necessary_strong_leibniz_implies_necessary_atomicity := by
  map_cert Meta.necessary_strong_leibniz_implies_necessary_atomicity

/-- `necessary-strong-leibniz-r-implies-necessary-strong-leibniz-t` -/
theorem necessary_strong_leibniz_r_implies_necessary_strong_leibniz_t : Statements.necessary_strong_leibniz_r_implies_necessary_strong_leibniz_t := by
  map_cert Proofs.necessary_strong_leibniz_r_implies_necessary_strong_leibniz_t.entails

/-- `necessary-strong-leibniz-r-implies-strong-leibniz-r` -/
theorem necessary_strong_leibniz_r_implies_strong_leibniz_r : Statements.necessary_strong_leibniz_r_implies_strong_leibniz_r := by
  map_cert Proofs.necessary_strong_leibniz_r_implies_strong_leibniz_r.entails

/-- `necessary-strong-leibniz-t-and-necessary-bf-imply-necessary-strong-leibniz` -/
theorem necessary_strong_leibniz_t_and_necessary_bf_imply_necessary_strong_leibniz : Statements.necessary_strong_leibniz_t_and_necessary_bf_imply_necessary_strong_leibniz := by
  map_cert Meta.necessary_strong_leibniz_t_and_necessary_bf_imply_necessary_strong_leibniz

/-- `necessary-strong-leibniz-t-implies-strong-leibniz-t` -/
theorem necessary_strong_leibniz_t_implies_strong_leibniz_t : Statements.necessary_strong_leibniz_t_implies_strong_leibniz_t := by
  map_cert Proofs.necessary_strong_leibniz_t_implies_strong_leibniz_t.entails

/-- `necessary-tractarianism-r-implies-necessary-barcan-r` -/
theorem necessary_tractarianism_r_implies_necessary_barcan_r : Statements.necessary_tractarianism_r_implies_necessary_barcan_r := by
  map_cert Proofs.necessary_tractarianism_r_implies_necessary_barcan_r.entails

/-- `necessary-tractarianism-r-implies-tractarianism-r` -/
theorem necessary_tractarianism_r_implies_tractarianism_r : Statements.necessary_tractarianism_r_implies_tractarianism_r := by
  map_cert Proofs.necessary_tractarianism_r_implies_tractarianism_r.entails

/-- `necessary-transversal-and-necessary-relational-choice-imply-necessary-transversal-choice` -/
theorem necessary_transversal_and_necessary_relational_choice_imply_necessary_transversal_choice : Statements.necessary_transversal_and_necessary_relational_choice_imply_necessary_transversal_choice := by
  map_cert Proofs.necessary_transversal_and_necessary_relational_choice_imply_necessary_transversal_choice.entails

/-- `necessary-transversal-choice-r-implies-necessary-relational-choice-r` -/
theorem necessary_transversal_choice_r_implies_necessary_relational_choice_r : Statements.necessary_transversal_choice_r_implies_necessary_relational_choice_r := by
  map_cert Proofs.necessary_transversal_choice_r_implies_necessary_relational_choice_r.entails

/-- `necessary-transversal-choice-r-implies-necessary-transversal-r` -/
theorem necessary_transversal_choice_r_implies_necessary_transversal_r : Statements.necessary_transversal_choice_r_implies_necessary_transversal_r := by
  map_cert Proofs.necessary_transversal_choice_r_implies_necessary_transversal_r.entails

/-- `necessary-transversal-choice-r-implies-transversal-choice-r` -/
theorem necessary_transversal_choice_r_implies_transversal_choice_r : Statements.necessary_transversal_choice_r_implies_transversal_choice_r := by
  map_cert Proofs.necessary_transversal_choice_r_implies_transversal_choice_r.entails

/-- `necessary-transversal-r-implies-transversal-r` -/
theorem necessary_transversal_r_implies_transversal_r : Statements.necessary_transversal_r_implies_transversal_r := by
  map_cert Proofs.necessary_transversal_r_implies_transversal_r.entails

/-- `necessary-vicinity-and-necessary-weakly-inextensible-comprehension-imply-necessary-actuality` -/
theorem necessary_vicinity_and_necessary_weakly_inextensible_comprehension_imply_necessary_actuality : Statements.necessary_vicinity_and_necessary_weakly_inextensible_comprehension_imply_necessary_actuality := by
  map_cert Proofs.necessary_vicinity_and_necessary_weakly_inextensible_comprehension_imply_necessary_actuality.entails

/-- `necessary-vicinity-implies-vicinity` -/
theorem necessary_vicinity_implies_vicinity : Statements.necessary_vicinity_implies_vicinity := by
  map_cert Proofs.necessary_vicinity_implies_vicinity.entails

/-- `necessary-weakly-inextensible-comprehension-r-implies-weakly-inextensible-comprehension-r` -/
theorem necessary_weakly_inextensible_comprehension_r_implies_weakly_inextensible_comprehension_r : Statements.necessary_weakly_inextensible_comprehension_r_implies_weakly_inextensible_comprehension_r := by
  map_cert Proofs.necessary_weakly_inextensible_comprehension_r_implies_weakly_inextensible_comprehension_r.entails

/-- `no-contingency-signature-r-implies-no-pure-contingency-r` -/
theorem no_contingency_signature_r_implies_no_pure_contingency_r : Statements.no_contingency_signature_r_implies_no_pure_contingency_r := by
  map_cert_sig (Entails.to_pureVersion_noContingency
    (Entails.mono_right npc_ofPure_subset noContingency_entails_npc))

/-- `no-contingency-signature-r-implies-signature-b-r` -/
theorem no_contingency_signature_r_implies_signature_b_r : Statements.no_contingency_signature_r_implies_signature_b_r := by
  map_cert_sig noContingency_entails_signatureB

/-- `no-pure-contingency-and-actuality-imply-necessary-actuality` -/
theorem no_pure_contingency_and_actuality_imply_necessary_actuality : Statements.no_pure_contingency_and_actuality_imply_necessary_actuality := by
  map_cert npc_actuality_entails_necActuality

/-- `no-pure-contingency-and-atomicity-imply-necessary-atomicity` -/
theorem no_pure_contingency_and_atomicity_imply_necessary_atomicity : Statements.no_pure_contingency_and_atomicity_imply_necessary_atomicity := by
  map_cert (Entails.mono_right (Ax₃ := P.NecAtomicity.schema) (by map_box) npc_atomicity_entails_box)

/-- `no-pure-contingency-and-b-imply-necessary-b` -/
theorem no_pure_contingency_and_b_imply_necessary_b : Statements.no_pure_contingency_and_b_imply_necessary_b := by
  map_cert (Entails.mono_right (Ax₃ := P.NecModalB.schema) (by map_box) (npc_union_entails_box_pure P.ModalB.schema))

/-- `no-pure-contingency-and-bf-imply-necessary-bf` -/
theorem no_pure_contingency_and_bf_imply_necessary_bf : Statements.no_pure_contingency_and_bf_imply_necessary_bf := by
  map_cert (Entails.mono_right (Ax₃ := P.NecBarcan.schema) (by map_box) npc_barcan_entails_box)

/-- `no-pure-contingency-and-bf-t-imply-necessary-bf-t` -/
theorem no_pure_contingency_and_bf_t_imply_necessary_bf_t : Statements.no_pure_contingency_and_bf_t_imply_necessary_bf_t := by
  map_cert npc_barcanT_entails_necBarcanT

/-- `no-pure-contingency-and-completeness-imply-necessary-completeness` -/
theorem no_pure_contingency_and_completeness_imply_necessary_completeness : Statements.no_pure_contingency_and_completeness_imply_necessary_completeness := by
  map_cert (Entails.mono_right (Ax₃ := P.NecBooleanCompleteness.schema) (by map_box) npc_booleanCompleteness_entails_box)

/-- `no-pure-contingency-and-extensionality-imply-necessary-extensionality` -/
theorem no_pure_contingency_and_extensionality_imply_necessary_extensionality : Statements.no_pure_contingency_and_extensionality_imply_necessary_extensionality := by
  map_cert (Entails.mono_right (Ax₃ := P.NecExtensionality.schema) (by map_box) (npc_union_entails_box_pure P.Extensionality.schema))

/-- `no-pure-contingency-and-five-imply-necessary-five` -/
theorem no_pure_contingency_and_five_imply_necessary_five : Statements.no_pure_contingency_and_five_imply_necessary_five := by
  map_cert (Entails.mono_right (Ax₃ := P.NecModalFive.schema) (by map_box) (npc_union_entails_box_pure P.ModalFive.schema))

/-- `no-pure-contingency-and-fregean-imply-necessary-fregean` -/
theorem no_pure_contingency_and_fregean_imply_necessary_fregean : Statements.no_pure_contingency_and_fregean_imply_necessary_fregean := by
  map_cert (Entails.mono_right (Ax₃ := P.NecFregeanAxiom.schema) (by map_box) npc_fregean_entails_box)

/-- `no-pure-contingency-and-functional-choice-imply-necessary-functional-choice` -/
theorem no_pure_contingency_and_functional_choice_imply_necessary_functional_choice : Statements.no_pure_contingency_and_functional_choice_imply_necessary_functional_choice := by
  map_cert (Entails.mono_right (Ax₃ := P.NecFunctionalChoice.schema) (by map_box) (npc_union_entails_box_pure P.FunctionalChoice.schema))

/-- `no-pure-contingency-and-functionality-imply-necessary-functionality` -/
theorem no_pure_contingency_and_functionality_imply_necessary_functionality : Statements.no_pure_contingency_and_functionality_imply_necessary_functionality := by
  map_cert (Entails.mono_right (Ax₃ := P.NecFunctionality.schema) (by map_box) (npc_union_entails_box_pure P.Functionality.schema))

/-- `no-pure-contingency-and-gallin-comprehension-imply-necessary-gallin-comprehension` -/
theorem no_pure_contingency_and_gallin_comprehension_imply_necessary_gallin_comprehension : Statements.no_pure_contingency_and_gallin_comprehension_imply_necessary_gallin_comprehension := by
  map_cert (Entails.mono_right (Ax₃ := P.NecGallinExtensionalComprehension.schema) (by map_box) (npc_union_entails_box_pure P.GallinExtensionalComprehension.schema))

/-- `no-pure-contingency-and-nd-imply-necessary-nd` -/
theorem no_pure_contingency_and_nd_imply_necessary_nd : Statements.no_pure_contingency_and_nd_imply_necessary_nd := by
  map_cert (Entails.mono_right (Ax₃ := P.NecNecessityOfDistinctness.schema) (by map_box) npc_nd_entails_box)

/-- `no-pure-contingency-and-nd-t-imply-necessary-nd-t` -/
theorem no_pure_contingency_and_nd_t_imply_necessary_nd_t : Statements.no_pure_contingency_and_nd_t_imply_necessary_nd_t := by
  map_cert npc_ndT_entails_necNdT

/-- `no-pure-contingency-and-plenitude-imply-necessary-plenitude` -/
theorem no_pure_contingency_and_plenitude_imply_necessary_plenitude : Statements.no_pure_contingency_and_plenitude_imply_necessary_plenitude := by
  map_cert (Entails.mono_right (Ax₃ := P.NecPlenitude.schema) (by map_box) (npc_union_entails_box_pure P.Plenitude.schema))

/-- `no-pure-contingency-and-relational-choice-imply-necessaryelational-choice` -/
theorem no_pure_contingency_and_relational_choice_imply_necessaryelational_choice : Statements.no_pure_contingency_and_relational_choice_imply_necessaryelational_choice := by
  map_cert (Entails.mono_right (Ax₃ := P.NecRelationalChoice.schema) (by map_box) (npc_union_entails_box_pure P.RelationalChoice.schema))

/-- `no-pure-contingency-and-rigid-comprehension-imply-necessary-rigid-comprehension` -/
theorem no_pure_contingency_and_rigid_comprehension_imply_necessary_rigid_comprehension : Statements.no_pure_contingency_and_rigid_comprehension_imply_necessary_rigid_comprehension := by
  map_cert (Entails.mono_right (Ax₃ := P.NecRigidComprehension.schema) (by map_box) (npc_union_entails_box_pure P.RigidComprehension.schema))

/-- `no-pure-contingency-and-strong-leibniz-imply-necessary-strong-leibniz` -/
theorem no_pure_contingency_and_strong_leibniz_imply_necessary_strong_leibniz : Statements.no_pure_contingency_and_strong_leibniz_imply_necessary_strong_leibniz := by
  map_cert (Entails.mono_right (Ax₃ := P.NecStrongLeibniz.schema) (by map_box) (npc_union_entails_box_pure P.StrongLeibniz.schema))

/-- `no-pure-contingency-and-strong-leibniz-t-imply-necessary-strong-leibniz-t` -/
theorem no_pure_contingency_and_strong_leibniz_t_imply_necessary_strong_leibniz_t : Statements.no_pure_contingency_and_strong_leibniz_t_imply_necessary_strong_leibniz_t := by
  map_cert (Entails.mono_right (Ax₃ := P.NecStrongLeibnizT.schema) (by map_box) (npc_union_entails_box_pure P.StrongLeibnizT.schema))

/-- `no-pure-contingency-and-tractarianism-imply-necessary-tractarianism` -/
theorem no_pure_contingency_and_tractarianism_imply_necessary_tractarianism : Statements.no_pure_contingency_and_tractarianism_imply_necessary_tractarianism := by
  map_cert (Entails.mono_right (Ax₃ := P.NecTractarianism.schema) (by map_box) (npc_union_entails_box_pure P.Tractarianism.schema))

/-- `no-pure-contingency-and-transversal-choice-imply-necessary-transversal-choice` -/
theorem no_pure_contingency_and_transversal_choice_imply_necessary_transversal_choice : Statements.no_pure_contingency_and_transversal_choice_imply_necessary_transversal_choice := by
  map_cert npc_transversalChoice_entails_necTransversalChoice

/-- `no-pure-contingency-and-transversal-imply-necessary-transversal` -/
theorem no_pure_contingency_and_transversal_imply_necessary_transversal : Statements.no_pure_contingency_and_transversal_imply_necessary_transversal := by
  map_cert npc_transversal_entails_necTransversal

/-- `no-pure-contingency-and-vicinity-imply-necessary-vicinity` -/
theorem no_pure_contingency_and_vicinity_imply_necessary_vicinity : Statements.no_pure_contingency_and_vicinity_imply_necessary_vicinity := by
  map_cert npc_vicinity_entails_necVicinity

/-- `no-pure-contingency-and-weakly-inextensible-comprehension-imply-necessary-weakly-inextensible-comprehension` -/
theorem no_pure_contingency_and_weakly_inextensible_comprehension_imply_necessary_weakly_inextensible_comprehension : Statements.no_pure_contingency_and_weakly_inextensible_comprehension_imply_necessary_weakly_inextensible_comprehension := by
  map_cert npc_weaklyInextensibleComprehension_entails_box

/-- `no-pure-contingency-r-implies-pure-b-r` -/
theorem no_pure_contingency_r_implies_pure_b_r : Statements.no_pure_contingency_r_implies_pure_b_r := by
  map_cert_sig (Entails.to_pureVersion_signatureB
    (Entails.ofPure (npc_entails_pureB (Sig := Signature.pure))))

/-- `persistent-comprehension-r-implies-actuality` -/
theorem persistent_comprehension_r_implies_actuality : Statements.persistent_comprehension_r_implies_actuality := by
  map_cert Proofs.persistent_comprehension_r_implies_actuality.entails

/-- `plenitude-r-implies-actuality` -/
theorem plenitude_r_implies_actuality : Statements.plenitude_r_implies_actuality := by
  map_cert Proofs.plenitude_r_implies_actuality.entails

/-- `plenitude-r-implies-distinctness-necessary-r` -/
theorem plenitude_r_implies_distinctness_necessary_r : Statements.plenitude_r_implies_distinctness_necessary_r := by
  map_cert Proofs.plenitude_r_implies_distinctness_necessary_r.entails

/-- `possibility-and-necessary-barcan-t-incompatible` -/
theorem possibility_and_necessary_barcan_t_incompatible : Statements.possibility_and_necessary_barcan_t_incompatible := by
  map_cert_incompatible possibility_necBarcanT_inconsistent

/-- `possibility-and-no-pure-contingency-incompatible` -/
theorem possibility_and_no_pure_contingency_incompatible : Statements.possibility_and_no_pure_contingency_incompatible := by
  map_cert_incompatible possibility_schema_npc_inconsistent

/-- `possibility-schema-r-implies-distinctness-schema-r` -/
theorem possibility_schema_r_implies_distinctness_schema_r : Statements.possibility_schema_r_implies_distinctness_schema_r := by
  map_cert Meta.possibility_schema_r_implies_distinctness_schema_r

/-- `possibility-signature-r-implies-distinctness-signature-r` -/
theorem possibility_signature_r_implies_distinctness_signature_r : Statements.possibility_signature_r_implies_distinctness_signature_r := by
  map_cert_sig Meta.possibility_signature_r_implies_distinctness_signature_r

/-- `pure-b-and-pure-possibility-incompatible` -/
theorem pure_b_and_pure_possibility_incompatible : Statements.pure_b_and_pure_possibility_incompatible := by
  map_cert_incompatible possibility_pureB_inconsistent

/-- `relational-choice-and-extensionality-imply-transversal-choice` -/
theorem relational_choice_and_extensionality_imply_transversal_choice : Statements.relational_choice_and_extensionality_imply_transversal_choice := by
  map_cert Proofs.relational_choice_and_extensionality_imply_transversal_choice.entails

/-- `relational-choice-and-plenitude-imply-functional-choice-r` -/
theorem relational_choice_and_plenitude_imply_functional_choice_r : Statements.relational_choice_and_plenitude_imply_functional_choice_r := by
  map_cert Proofs.relational_choice_and_plenitude_imply_functional_choice_r.entails

/-- `relational-choice-and-very-weak-rigid-comprehension-imply-transversal-choice` -/
theorem relational_choice_and_very_weak_rigid_comprehension_imply_transversal_choice : Statements.relational_choice_and_very_weak_rigid_comprehension_imply_transversal_choice := by
  map_cert Proofs.relational_choice_and_very_weak_rigid_comprehension_imply_transversal_choice.entails

/-- `rigid-comprehension-and-bf-imply-necessary-bf` -/
theorem rigid_comprehension_and_bf_imply_necessary_bf : Statements.rigid_comprehension_and_bf_imply_necessary_bf := by
  map_cert Proofs.rigid_comprehension_and_bf_imply_necessary_bf.entails

/-- `rigid-comprehension-and-nd-imply-plenitude` -/
theorem rigid_comprehension_and_nd_imply_plenitude : Statements.rigid_comprehension_and_nd_imply_plenitude := by
  map_cert Meta.rigid_comprehension_and_nd_imply_plenitude

/-- `rigid-comprehension-r-implies-actuality` -/
theorem rigid_comprehension_r_implies_actuality : Statements.rigid_comprehension_r_implies_actuality := by
  map_cert Proofs.rigid_comprehension_r_implies_actuality.entails

/-- `rigid-comprehension-r-implies-boolean-completeness-r` -/
theorem rigid_comprehension_r_implies_boolean_completeness_r : Statements.rigid_comprehension_r_implies_boolean_completeness_r := by
  map_cert Meta.rigid_comprehension_r_implies_boolean_completeness_r

/-- `rigid-comprehension-r-implies-inextensible-comprehension-r` -/
theorem rigid_comprehension_r_implies_inextensible_comprehension_r : Statements.rigid_comprehension_r_implies_inextensible_comprehension_r := by
  map_cert Proofs.rigid_comprehension_r_implies_inextensible_comprehension_r.entails

/-- `rigid-comprehension-r-implies-persistent-comprehension-r` -/
theorem rigid_comprehension_r_implies_persistent_comprehension_r : Statements.rigid_comprehension_r_implies_persistent_comprehension_r := by
  map_cert Proofs.rigid_comprehension_r_implies_persistent_comprehension_r.entails

/-- `rigid-comprehension-r-implies-weak-rigid-comprehension-r` -/
theorem rigid_comprehension_r_implies_weak_rigid_comprehension_r : Statements.rigid_comprehension_r_implies_weak_rigid_comprehension_r := by
  map_cert Proofs.rigid_comprehension_r_implies_weak_rigid_comprehension_r.entails

/-- `signature-b-r-implies-pure-b-r` -/
theorem signature_b_r_implies_pure_b_r : Statements.signature_b_r_implies_pure_b_r := by
  map_cert_sig (Entails.to_pureVersion_signatureB
    (Entails.mono_right pureB_ofPure_subset signatureB_entails_pureB))

/-- `strong-leibniz-r-implies-atomicity-r` -/
theorem strong_leibniz_r_implies_atomicity_r : Statements.strong_leibniz_r_implies_atomicity_r := by
  map_cert Meta.strong_leibniz_r_implies_atomicity_r

/-- `strong-leibniz-r-implies-strong-leibniz-t` -/
theorem strong_leibniz_r_implies_strong_leibniz_t : Statements.strong_leibniz_r_implies_strong_leibniz_t := by
  map_cert Proofs.strong_leibniz_r_implies_strong_leibniz_t.entails

/-- `strong-leibniz-t-implies-atomicity-t` -/
theorem strong_leibniz_t_implies_atomicity_t : Statements.strong_leibniz_t_implies_atomicity_t := by
  map_cert Proofs.strong_leibniz_t_implies_atomicity_t.entails

/-- `strong-leibniz-t-implies-necessary-actuality` -/
theorem strong_leibniz_t_implies_necessary_actuality : Statements.strong_leibniz_t_implies_necessary_actuality := by
  map_cert Proofs.strong_leibniz_t_implies_necessary_actuality.entails

/-- `tractarianism-r-implies-barcan-r` -/
theorem tractarianism_r_implies_barcan_r : Statements.tractarianism_r_implies_barcan_r := by
  map_cert Proofs.tractarianism_r_implies_barcan_r.entails

/-- `transversal-and-relational-choice-imply-transversal-choice` -/
theorem transversal_and_relational_choice_imply_transversal_choice : Statements.transversal_and_relational_choice_imply_transversal_choice := by
  map_cert Proofs.transversal_and_relational_choice_imply_transversal_choice.entails

/-- `transversal-choice-r-implies-relational-choice-r` -/
theorem transversal_choice_r_implies_relational_choice_r : Statements.transversal_choice_r_implies_relational_choice_r := by
  map_cert Proofs.transversal_choice_r_implies_relational_choice_r.entails

/-- `transversal-choice-r-implies-transversal-r` -/
theorem transversal_choice_r_implies_transversal_r : Statements.transversal_choice_r_implies_transversal_r := by
  map_cert Proofs.transversal_choice_r_implies_transversal_r.entails

/-- `very-weak-rigid-comprehension-r-implies-weak-rigid-comprehension-r` -/
theorem very_weak_rigid_comprehension_r_implies_weak_rigid_comprehension_r : Statements.very_weak_rigid_comprehension_r_implies_weak_rigid_comprehension_r := by
  map_cert _root_.Classicism.very_weak_rigid_comprehension_r_implies_weak_rigid_comprehension_r.entails

/-- `vicinity-and-distinctness-preserving-collapse-imply-actuality` -/
theorem vicinity_and_distinctness_preserving_collapse_imply_actuality : Statements.vicinity_and_distinctness_preserving_collapse_imply_actuality := by
  map_cert Proofs.vicinity_and_distinctness_preserving_collapse_imply_actuality.entails

/-- `vicinity-and-weakly-inextensible-comprehension-imply-actuality` -/
theorem vicinity_and_weakly_inextensible_comprehension_imply_actuality : Statements.vicinity_and_weakly_inextensible_comprehension_imply_actuality := by
  map_cert Proofs.vicinity_and_weakly_inextensible_comprehension_imply_actuality.entails

/-- `weak-rigid-comprehension-r-implies-boolean-completeness-r` -/
theorem weak_rigid_comprehension_r_implies_boolean_completeness_r : Statements.weak_rigid_comprehension_r_implies_boolean_completeness_r := by
  map_cert Meta.weak_rigid_comprehension_r_implies_boolean_completeness_r

/-- `weak-rigid-comprehension-r-implies-persistent-comprehension-r` -/
theorem weak_rigid_comprehension_r_implies_persistent_comprehension_r : Statements.weak_rigid_comprehension_r_implies_persistent_comprehension_r := by
  map_cert Proofs.weak_rigid_comprehension_r_implies_persistent_comprehension_r.entails

/-- `weak-rigid-comprehension-r-implies-very-weak-rigid-comprehension-r` -/
theorem weak_rigid_comprehension_r_implies_very_weak_rigid_comprehension_r : Statements.weak_rigid_comprehension_r_implies_very_weak_rigid_comprehension_r := by
  map_cert Proofs.weak_rigid_comprehension_r_implies_very_weak_rigid_comprehension_r.entails

/-- `weak-rigid-comprehension-r-implies-weakly-inextensible-comprehension-r` -/
theorem weak_rigid_comprehension_r_implies_weakly_inextensible_comprehension_r : Statements.weak_rigid_comprehension_r_implies_weakly_inextensible_comprehension_r := by
  map_cert Proofs.weak_rigid_comprehension_r_implies_weakly_inextensible_comprehension_r.entails

/-! ## Equivalent forms -/

/-- `boolean-completeness-r`, form `lub`: Boolean Completeness and its LUB form. -/
theorem boolean_completeness_r.lub : Statements.boolean_completeness_r.lub := by
  map_form Proofs.boolean_completeness_implies_lub_form.entails
    Proofs.lub_form_implies_boolean_completeness.entails

end Classicism.Map
