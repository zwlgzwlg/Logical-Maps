import Classicism.Certified.Schemas
import Classicism.Certified.Entailed
import Classicism.Semantics.IntensionalExamples
import Classicism.Semantics.IntensionalProperties
import Classicism.Models.Permutations
import Classicism.Syntax.SentenceSchemas

/-!
# Consistency facts, from the models

The side conditions of Possibility and Distinctness — "`P` is consistent with `C`",
"`A = B` is not a theorem of `C`" — are met by exhibiting a model. This file collects,
from the models the semantics provides, every such fact the results in this folder use,
each as `Consistent Ax` or `¬ Theorem (C ∪ Ax) p` for the axiom sets and quoted
sentences the results are stated in. Two models do all the work:

- **`Prop`, the full Henkin model on `e`** (`Interp.ofDomain e`, the reading that the
  reflection theorems `P.reflect` are stated for): the Fregean Axiom holds, by `propext`;
  and, since there is one world, everything true is necessary, so No Contingency holds —
  for any signature, the constants interpreted anyhow (`Interp.trivial`). The map's
  `full-henkin-singleton-base`.
- **The full M-set models on the two two-element monoids** (`Semantics/IntensionalExamples.lean`,
  intensional action models):
  on the idempotent monoid `ND_t`, `BF_t` and the Fregean Axiom fail, so their
  negations are consistent and they are not theorems; Tractarianism at `t` fails there
  too, since it implies `BF_t` — the record `tractarianism-r-implies-barcan-r`, certified,
  carried into the model by soundness. On the two-element group `□ND_σ` and `□BF_σ` hold
  at every type while the Fregean Axiom fails, so `¬FA` and `¬□FA` are consistent with
  `□ND ∪ □BF`. The map's `full-idempotent-monoid` and `full-involution-group`.

- **The permutation model of Appendix D, Part 1** (`Models/Permutations.lean`): ideally
  full over the permutations of `ℕ`. `□ND_σ` and `□BF_σ` hold at every type and
  Atomlessness holds, while Actuality and Atomicity at `t` fail; so `¬`Actuality and
  `¬`Atomicity (`t`) are consistent with `□ND`, `□BF` and Atomlessness, and neither is a
  theorem of `C` with them.

The model verdicts themselves stay in `Semantics/IntensionalExamples.lean` and
`Models/Permutations.lean`; this file turns
them into facts about the theory with `Consistent.of_model`, `not_theorem_of_model`,
`Consistent.of_interp` and `not_theorem_of_interp`.
-/

namespace Classicism.Meta

open AxiomSet CategoryTheory Intensional

/-! ### `Prop`: the full Henkin model on `e` -/

instance : Nonempty Classicism.e := ⟨Classicism.e_exists.choose⟩

/-- The full Henkin model on `e`, the reading the reflection theorems are stated for. -/
abbrev henkin : Interp Signature.pure := Interp.ofDomain Classicism.e

instance : Nonempty henkin.D := inferInstanceAs (Nonempty Classicism.e)

/-- In a one-world model what is true is necessary. -/
theorem Sentence.box_holds_of_holds {Sig : Signature} (I : Interp Sig) {p : Sentence Sig}
    (h : Sentence.holds I p) : Sentence.holds I (Term.box p) :=
  propext ⟨fun _ => Or.inr (fun h => h False), fun _ => h⟩

/-- **No Contingency holds in `Prop`**, for any signature and any interpretation of its
constants: the map's note that it "holds in every one-world model whatever the constants
denote". -/
theorem noContingency_holds_interp {Sig : Signature} (I : Interp Sig) : (noContingency Sig).holds I := by
  rintro a ⟨p, rfl⟩
  exact (Classical.em (Sentence.holds I p)).elim (fun h => Or.inr (Sentence.box_holds_of_holds I h)) Or.inl

theorem npc_holds_interp {Sig : Signature} (I : Interp Sig) : (npc Sig).holds I :=
  fun a ha => noContingency_holds_interp I a (npc_subset_noContingency a ha)

/-- No Contingency for any signature is consistent: `no-contingency-signature-r`. -/
theorem noContingency_consistent (Sig : Signature) : Consistent (noContingency Sig) :=
  Consistent.of_interp (Interp.trivial Sig Classicism.e) (noContingency_holds_interp _)

/-- The Fregean Axiom holds in `Prop`: it is `propext`. -/
theorem fregean_holds_henkin : Sentence.holds henkin P.FregeanAxiom.quoted :=
  P.FregeanAxiom.reflect.mpr (fun p q (h : p ↔ q) => propext h : ∀ p q : Prop, (p ↔ q) → p = q)

theorem box_fregean_holds_henkin : Sentence.holds henkin (Term.box P.FregeanAxiom.quoted) :=
  Sentence.box_holds_of_holds henkin fregean_holds_henkin

/-- The Fregean Axiom is consistent with Classicism. -/
theorem fregean_consistent : Consistent (single P.FregeanAxiom.quoted) :=
  Consistent.of_interp henkin fun _ h => h ▸ fregean_holds_henkin

/-- So is its necessitation, `FA = ⊤`. -/
theorem box_fregean_consistent : Consistent (single (Term.box P.FregeanAxiom.quoted)) :=
  Consistent.of_interp henkin fun _ h => h ▸ box_fregean_holds_henkin

/-- No Pure Contingency and the Fregean Axiom are jointly consistent: `Prop` is a model
of both. -/
theorem npc_fregean_consistent : Consistent (npc Signature.pure ∪ P.FregeanAxiom.schema) :=
  Consistent.of_interp henkin fun a ha =>
    ha.elim (npc_holds_interp henkin a) (fun h => h ▸ fregean_holds_henkin)

/-! ### The model on the idempotent monoid: `ND_t`, `BF_t`, `FA`, Tractarianism at `t` fail -/

/-- The quoted principles are the sentences the model facts are stated for. -/
theorem nd_quoted_eq (σ : Ty) : P.NecessityOfDistinctness.quoted σ = Sentence.nd σ := rfl
theorem ndT_quoted_eq : P.NecessityOfDistinctnessT.quoted = Sentence.nd Ty.t := rfl
theorem bf_quoted_eq (σ : Ty) : P.Barcan.quoted σ = Sentence.bf σ := rfl
theorem bfT_quoted_eq : P.BarcanT.quoted = Sentence.bf Ty.t := rfl
theorem fregean_quoted_eq : P.FregeanAxiom.quoted = Sentence.fregean := rfl
theorem necBfT_quoted_eq : P.NecBarcanT.quoted = Term.box P.BarcanT.quoted := rfl
theorem necNdT_quoted_eq : P.NecNecessityOfDistinctnessT.quoted = Term.box P.NecessityOfDistinctnessT.quoted := rfl

-- The record `tractarianism-r-implies-barcan-r` as a rule of `C`, for the model to use.
#classicism_rule Classicism.Proofs.tractarianism_r_implies_barcan_r

namespace Idem

open Intensional.Premodel Intensional.Idem

/-- The model, with its model proof. -/
local notation "A" => MSet.model Idem
local notation "M" => MSet.model_isModel Idem

theorem not_nd_t_consistent : Consistent (single (Term.neg P.NecessityOfDistinctnessT.quoted)) :=
  Consistent.of_model A M (holdsAx_single A ((holdsSentence_neg A M _).2 not_nd_t))

theorem nd_t_not_theorem : ¬ Theorem (C.axioms ∪ empty) P.NecessityOfDistinctnessT.quoted :=
  not_theorem_of_model A M (holdsAx_empty A) not_nd_t

theorem not_bf_t_consistent : Consistent (single (Term.neg P.BarcanT.quoted)) :=
  Consistent.of_model A M (holdsAx_single A ((holdsSentence_neg A M _).2 not_bf_t))

theorem bf_t_not_theorem : ¬ Theorem (C.axioms ∪ empty) P.BarcanT.quoted :=
  not_theorem_of_model A M (holdsAx_empty A) not_bf_t

theorem not_fregean_consistent : Consistent (single (Term.neg P.FregeanAxiom.quoted)) :=
  Consistent.of_model A M (holdsAx_single A ((holdsSentence_neg A M _).2 not_fregean))

/-- **Tractarianism at `t` fails in the model**: it implies `BF_t`, by the certified
record `tractarianism-r-implies-barcan-r`, a theorem of `C` and so true in the model. -/
theorem not_tractarianism_t : ¬ (A).HoldsSentence (P.Tractarianism.quoted Ty.t) := fun h =>
  not_bf_t (((A).holds_imp M (𝟙 _) IEnv.nil _ _).1
    ((A).theorem_holds M (Proofs.tractarianism_r_implies_barcan_r.rule Ty.t)) h)

theorem not_tractarianism_t_consistent : Consistent (single (Term.neg (P.Tractarianism.quoted Ty.t))) :=
  Consistent.of_model A M (holdsAx_single A ((holdsSentence_neg A M _).2 not_tractarianism_t))

end Idem

/-! ### The model on the two-element group: `□ND_σ`, `□BF_σ` hold, `FA` and `□FA` fail -/

namespace Invol

open Intensional.Premodel Intensional.Invol

local notation "A" => MSet.model Invol
local notation "M" => MSet.model_isModel Invol

/-- `□ND`, `□BF`, and so `ND` and `BF`, at every type, hold in the model. -/
theorem holdsAx_nd_bf :
    (A).HoldsAx (AxiomSet.box P.NecessityOfDistinctness.schema ∪ AxiomSet.box P.Barcan.schema ∪
      (P.NecessityOfDistinctness.schema ∪ P.Barcan.schema)) := by
  rintro a ((⟨_, ⟨σ, rfl⟩, rfl⟩ | ⟨_, ⟨σ, rfl⟩, rfl⟩) | (⟨σ, rfl⟩ | ⟨σ, rfl⟩))
  · exact box_nd σ
  · exact box_bf σ
  · exact holdsSentence_of_box A M (box_nd σ)
  · exact holdsSentence_of_box A M (box_bf σ)

/-- `□ND` and `□BF` are jointly consistent, with `ND` and `BF`. -/
theorem nd_bf_consistent :
    Consistent (AxiomSet.box P.NecessityOfDistinctness.schema ∪ AxiomSet.box P.Barcan.schema ∪
      (P.NecessityOfDistinctness.schema ∪ P.Barcan.schema)) :=
  Consistent.of_model A M holdsAx_nd_bf

theorem not_box_fregean : ¬ (A).HoldsSentence (Term.box P.FregeanAxiom.quoted) :=
  fun h => not_fregean (holdsSentence_of_box A M h)

/-- `¬FA` is consistent with `□ND` and `□BF`. -/
theorem not_fregean_nd_bf_consistent :
    Consistent (single (Term.neg P.FregeanAxiom.quoted) ∪
      (AxiomSet.box P.NecessityOfDistinctness.schema ∪ AxiomSet.box P.Barcan.schema ∪
        (P.NecessityOfDistinctness.schema ∪ P.Barcan.schema))) :=
  Consistent.of_model A M
    (holdsAx_union A (holdsAx_single A ((holdsSentence_neg A M _).2 not_fregean)) holdsAx_nd_bf)

/-- `FA = ⊤` is not a theorem of `C`. -/
theorem box_fregean_not_theorem : ¬ Theorem (C.axioms ∪ empty) (Term.box P.FregeanAxiom.quoted) :=
  not_theorem_of_model A M (holdsAx_empty A) not_box_fregean

theorem not_box_fregean_consistent : Consistent (single (Term.neg (Term.box P.FregeanAxiom.quoted))) :=
  Consistent.of_model A M (holdsAx_single A ((holdsSentence_neg A M _).2 not_box_fregean))

theorem fregean_not_theorem : ¬ Theorem (C.axioms ∪ empty) P.FregeanAxiom.quoted :=
  not_theorem_of_model A M (holdsAx_empty A) not_fregean

end Invol

/-! ### The permutation model: `□ND`, `□BF`, Atomlessness hold, Actuality and Atomicity (`t`) fail -/

namespace Perms

open Intensional.Premodel Intensional.Perms

local notation "A" => Intensional.Perms.model
local notation "M" => Intensional.Perms.model_isModel

theorem necActuality_quoted_eq : P.NecActuality.quoted = Term.box P.Actuality.quoted := rfl

/-- `□ND`, `□BF` at every type and Atomlessness hold in the model. -/
theorem holdsAx_nd_bf_atomless :
    (A).HoldsAx (AxiomSet.box P.NecessityOfDistinctness.schema ∪ AxiomSet.box P.Barcan.schema ∪
      P.Atomlessness.schema) := by
  rintro a ((⟨_, ⟨σ, rfl⟩, rfl⟩ | ⟨_, ⟨σ, rfl⟩, rfl⟩) | rfl)
  · exact box_nd σ
  · exact box_bf σ
  · exact atomlessness

/-- `□ND`, `□BF` and Atomlessness are jointly consistent. -/
theorem nd_bf_atomless_consistent :
    Consistent (AxiomSet.box P.NecessityOfDistinctness.schema ∪ AxiomSet.box P.Barcan.schema ∪
      P.Atomlessness.schema) :=
  Consistent.of_model A M holdsAx_nd_bf_atomless

/-- `¬`Actuality is consistent, on its own and with `□ND`, `□BF` and Atomlessness. -/
theorem not_actuality_consistent : Consistent (single (Term.neg P.Actuality.quoted)) :=
  Consistent.of_model A M (holdsAx_single A ((holdsSentence_neg A M _).2 not_actuality))

theorem not_actuality_nd_bf_atomless_consistent :
    Consistent (single (Term.neg P.Actuality.quoted) ∪
      (AxiomSet.box P.NecessityOfDistinctness.schema ∪ AxiomSet.box P.Barcan.schema ∪
        P.Atomlessness.schema)) :=
  Consistent.of_model A M
    (holdsAx_union A (holdsAx_single A ((holdsSentence_neg A M _).2 not_actuality)) holdsAx_nd_bf_atomless)

/-- Actuality is not a theorem of `C` with `□ND`, `□BF` and Atomlessness. -/
theorem actuality_not_theorem :
    ¬ Theorem (C.axioms ∪ (AxiomSet.box P.NecessityOfDistinctness.schema ∪ AxiomSet.box P.Barcan.schema ∪
      P.Atomlessness.schema)) P.Actuality.quoted :=
  not_theorem_of_model A M holdsAx_nd_bf_atomless not_actuality

/-- `¬`Atomicity at `t` likewise. -/
theorem not_atomicityT_consistent : Consistent (single (Term.neg P.AtomicityT.quoted)) :=
  Consistent.of_model A M (holdsAx_single A ((holdsSentence_neg A M _).2 not_atomicityT))

theorem not_atomicity_t_consistent : Consistent (single (Term.neg (P.Atomicity.quoted RTy.t))) :=
  Consistent.of_model A M (holdsAx_single A ((holdsSentence_neg A M _).2 not_atomicity_t))

theorem atomicityT_not_theorem :
    ¬ Theorem (C.axioms ∪ (AxiomSet.box P.NecessityOfDistinctness.schema ∪ AxiomSet.box P.Barcan.schema ∪
      P.Atomlessness.schema)) P.AtomicityT.quoted :=
  not_theorem_of_model A M holdsAx_nd_bf_atomless not_atomicityT

end Perms

end Classicism.Meta
