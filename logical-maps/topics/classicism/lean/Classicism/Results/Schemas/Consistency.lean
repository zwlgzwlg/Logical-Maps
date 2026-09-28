import Classicism.Certified.Schemas
import Classicism.Certified.Entailed
import Classicism.Semantics.IntensionalExamples
import Classicism.Semantics.IntensionalProperties
import Classicism.Models.Permutations
import Classicism.Models.Monoids
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
  Atomlessness holds, while Actuality, Atomicity at `t` and Boolean Completeness at
  `e → t` fail; so the negation of each is consistent with `□ND`, `□BF` and Atomlessness,
  and none is a theorem of `C` with them.

- **The monoid models of Appendix D, Parts 2 to 8** (`Models/Monoids.lean`, each an
  ideally full model over a submonoid of the functions on `ℕ`, built by
  `Models/MonoidModel.lean`): one section per part. Each has `holdsAx_pos`, the principles
  that hold there (No Pure Contingency, which holds in every model on a monoid, and
  `BF`, Actuality, Atomlessness, Atomicity at `t` as the part has them), `holdsAx_neg`,
  the negations of those that fail (`ND_e` and Boolean Completeness at `e → t` in every
  part, `BF_e`, Actuality, Atomicity at `t`), `consistent`, their union consistent — the
  row of the paper's Proposition D.5 for that part — and, for each principle that fails,
  that it is not a theorem of `C` with the ones that hold: `BF_e` is not a theorem of `C`
  with Actuality and Atomicity (Part 7), Actuality not of `C` with Atomicity (Part 6),
  Atomicity not of `C` with `BF` and Actuality (Part 5), `ND_e` and Boolean Completeness
  not of `C` with all three (Part 8). The necessitations follow from No Pure Contingency
  (`Contingency.lean`, `npc_union_entails_box`) and are not restated.

The model verdicts themselves stay in `Semantics/IntensionalExamples.lean`,
`Models/Permutations.lean` and `Models/Monoids.lean`; this file turns
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

/-- `¬`Boolean Completeness at `e → t` likewise: the paper's Proposition D.5, part 1. -/
theorem not_bc_consistent : Consistent (single (Term.neg (P.BooleanCompleteness.quoted (.arr .e .t)))) :=
  Consistent.of_model A M (holdsAx_single A ((holdsSentence_neg A M _).2 not_bc))

theorem not_bc_nd_bf_atomless_consistent :
    Consistent (single (Term.neg (P.BooleanCompleteness.quoted (.arr .e .t))) ∪
      (AxiomSet.box P.NecessityOfDistinctness.schema ∪ AxiomSet.box P.Barcan.schema ∪
        P.Atomlessness.schema)) :=
  Consistent.of_model A M
    (holdsAx_union A (holdsAx_single A ((holdsSentence_neg A M _).2 not_bc)) holdsAx_nd_bf_atomless)

theorem bc_not_theorem :
    ¬ Theorem (C.axioms ∪ (AxiomSet.box P.NecessityOfDistinctness.schema ∪ AxiomSet.box P.Barcan.schema ∪
      P.Atomlessness.schema)) (P.BooleanCompleteness.quoted (.arr .e .t)) :=
  not_theorem_of_model A M holdsAx_nd_bf_atomless not_bc

end Perms

/-! ### Appendix D, Part 2: the monotone surjections -/

namespace MonoSurj

open Intensional.Premodel Intensional.MonoidModel Intensional.Monoids.MonoSurj

local notation "A" => Intensional.MonoidModel.model Intensional.Monoids.monoSurj
local notation "M" => Intensional.MonoidModel.model_isModel Intensional.Monoids.monoSurj

/-- What holds: No Pure Contingency, `BF`, Atomlessness. -/
theorem holdsAx_pos : (A).HoldsAx (npc Signature.pure ∪ P.Barcan.schema ∪ P.Atomlessness.schema) :=
  holdsAx_union A (holdsAx_union A (holdsAx_npc A M)
      (by rintro _ ⟨σ, rfl⟩; exact bf σ))
      (by rintro _ rfl; exact atomlessness)

/-- What fails: `ND_e`, Actuality, Atomicity at `t`, Boolean Completeness at `e → t`. -/
theorem holdsAx_neg : (A).HoldsAx (single (Term.neg (Sentence.nd .e)) ∪ single (Term.neg P.Actuality.quoted) ∪ single (Term.neg P.AtomicityT.quoted) ∪ single (Term.neg (P.BooleanCompleteness.quoted (.arr .e .t)))) :=
  holdsAx_union A (holdsAx_union A (holdsAx_union A (holdsAx_single A ((holdsSentence_neg A M _).2 not_nd_e))
      (holdsAx_single A ((holdsSentence_neg A M _).2 not_actuality)))
      (holdsAx_single A ((holdsSentence_neg A M _).2 not_atomicityT)))
      (holdsAx_single A ((holdsSentence_neg A M _).2 not_bc))

/-- The verdicts of Part 2, jointly consistent. -/
theorem consistent :
    Consistent (npc Signature.pure ∪ P.Barcan.schema ∪ P.Atomlessness.schema ∪
      (single (Term.neg (Sentence.nd .e)) ∪ single (Term.neg P.Actuality.quoted) ∪ single (Term.neg P.AtomicityT.quoted) ∪ single (Term.neg (P.BooleanCompleteness.quoted (.arr .e .t))))) :=
  Consistent.of_model A M (holdsAx_union A holdsAx_pos holdsAx_neg)

theorem nd_e_not_theorem :
    ¬ Theorem (C.axioms ∪ (npc Signature.pure ∪ P.Barcan.schema ∪ P.Atomlessness.schema)) (Sentence.nd .e) :=
  not_theorem_of_model A M holdsAx_pos not_nd_e

theorem actuality_not_theorem :
    ¬ Theorem (C.axioms ∪ (npc Signature.pure ∪ P.Barcan.schema ∪ P.Atomlessness.schema)) (P.Actuality.quoted) :=
  not_theorem_of_model A M holdsAx_pos not_actuality

theorem atomicityT_not_theorem :
    ¬ Theorem (C.axioms ∪ (npc Signature.pure ∪ P.Barcan.schema ∪ P.Atomlessness.schema)) (P.AtomicityT.quoted) :=
  not_theorem_of_model A M holdsAx_pos not_atomicityT

theorem bc_not_theorem :
    ¬ Theorem (C.axioms ∪ (npc Signature.pure ∪ P.Barcan.schema ∪ P.Atomlessness.schema)) (P.BooleanCompleteness.quoted (.arr .e .t)) :=
  not_theorem_of_model A M holdsAx_pos not_bc

end MonoSurj

/-! ### Appendix D, Part 3: the monotone functions -/

namespace Mono

open Intensional.Premodel Intensional.MonoidModel Intensional.Monoids.Mono

local notation "A" => Intensional.MonoidModel.model Intensional.Monoids.mono
local notation "M" => Intensional.MonoidModel.model_isModel Intensional.Monoids.mono

/-- What holds: No Pure Contingency, Atomlessness. -/
theorem holdsAx_pos : (A).HoldsAx (npc Signature.pure ∪ P.Atomlessness.schema) :=
  holdsAx_union A (holdsAx_npc A M)
      (by rintro _ rfl; exact atomlessness)

/-- What fails: `ND_e`, `BF_e`, Actuality, Atomicity at `t`, Boolean Completeness at `e → t`. -/
theorem holdsAx_neg : (A).HoldsAx (single (Term.neg (Sentence.nd .e)) ∪ single (Term.neg (Sentence.bf .e)) ∪ single (Term.neg P.Actuality.quoted) ∪ single (Term.neg P.AtomicityT.quoted) ∪ single (Term.neg (P.BooleanCompleteness.quoted (.arr .e .t)))) :=
  holdsAx_union A (holdsAx_union A (holdsAx_union A (holdsAx_union A (holdsAx_single A ((holdsSentence_neg A M _).2 not_nd_e))
      (holdsAx_single A ((holdsSentence_neg A M _).2 not_bf_e)))
      (holdsAx_single A ((holdsSentence_neg A M _).2 not_actuality)))
      (holdsAx_single A ((holdsSentence_neg A M _).2 not_atomicityT)))
      (holdsAx_single A ((holdsSentence_neg A M _).2 not_bc))

/-- The verdicts of Part 3, jointly consistent. -/
theorem consistent :
    Consistent (npc Signature.pure ∪ P.Atomlessness.schema ∪
      (single (Term.neg (Sentence.nd .e)) ∪ single (Term.neg (Sentence.bf .e)) ∪ single (Term.neg P.Actuality.quoted) ∪ single (Term.neg P.AtomicityT.quoted) ∪ single (Term.neg (P.BooleanCompleteness.quoted (.arr .e .t))))) :=
  Consistent.of_model A M (holdsAx_union A holdsAx_pos holdsAx_neg)

theorem nd_e_not_theorem :
    ¬ Theorem (C.axioms ∪ (npc Signature.pure ∪ P.Atomlessness.schema)) (Sentence.nd .e) :=
  not_theorem_of_model A M holdsAx_pos not_nd_e

theorem bf_e_not_theorem :
    ¬ Theorem (C.axioms ∪ (npc Signature.pure ∪ P.Atomlessness.schema)) (Sentence.bf .e) :=
  not_theorem_of_model A M holdsAx_pos not_bf_e

theorem actuality_not_theorem :
    ¬ Theorem (C.axioms ∪ (npc Signature.pure ∪ P.Atomlessness.schema)) (P.Actuality.quoted) :=
  not_theorem_of_model A M holdsAx_pos not_actuality

theorem atomicityT_not_theorem :
    ¬ Theorem (C.axioms ∪ (npc Signature.pure ∪ P.Atomlessness.schema)) (P.AtomicityT.quoted) :=
  not_theorem_of_model A M holdsAx_pos not_atomicityT

theorem bc_not_theorem :
    ¬ Theorem (C.axioms ∪ (npc Signature.pure ∪ P.Atomlessness.schema)) (P.BooleanCompleteness.quoted (.arr .e .t)) :=
  not_theorem_of_model A M holdsAx_pos not_bc

end Mono

/-! ### Appendix D, Part 4: the monotone functions collapsing `0` and `1`, and the identity -/

namespace Mono01

open Intensional.Premodel Intensional.MonoidModel Intensional.Monoids.Mono01

local notation "A" => Intensional.MonoidModel.model Intensional.Monoids.mono01
local notation "M" => Intensional.MonoidModel.model_isModel Intensional.Monoids.mono01

/-- What holds: No Pure Contingency, Actuality. -/
theorem holdsAx_pos : (A).HoldsAx (npc Signature.pure ∪ P.Actuality.schema) :=
  holdsAx_union A (holdsAx_npc A M)
      (by rintro _ rfl; exact actuality)

/-- What fails: `ND_e`, `BF_e`, Atomicity at `t`, Boolean Completeness at `e → t`. -/
theorem holdsAx_neg : (A).HoldsAx (single (Term.neg (Sentence.nd .e)) ∪ single (Term.neg (Sentence.bf .e)) ∪ single (Term.neg P.AtomicityT.quoted) ∪ single (Term.neg (P.BooleanCompleteness.quoted (.arr .e .t)))) :=
  holdsAx_union A (holdsAx_union A (holdsAx_union A (holdsAx_single A ((holdsSentence_neg A M _).2 not_nd_e))
      (holdsAx_single A ((holdsSentence_neg A M _).2 not_bf_e)))
      (holdsAx_single A ((holdsSentence_neg A M _).2 not_atomicityT)))
      (holdsAx_single A ((holdsSentence_neg A M _).2 not_bc))

/-- The verdicts of Part 4, jointly consistent. -/
theorem consistent :
    Consistent (npc Signature.pure ∪ P.Actuality.schema ∪
      (single (Term.neg (Sentence.nd .e)) ∪ single (Term.neg (Sentence.bf .e)) ∪ single (Term.neg P.AtomicityT.quoted) ∪ single (Term.neg (P.BooleanCompleteness.quoted (.arr .e .t))))) :=
  Consistent.of_model A M (holdsAx_union A holdsAx_pos holdsAx_neg)

theorem nd_e_not_theorem :
    ¬ Theorem (C.axioms ∪ (npc Signature.pure ∪ P.Actuality.schema)) (Sentence.nd .e) :=
  not_theorem_of_model A M holdsAx_pos not_nd_e

theorem bf_e_not_theorem :
    ¬ Theorem (C.axioms ∪ (npc Signature.pure ∪ P.Actuality.schema)) (Sentence.bf .e) :=
  not_theorem_of_model A M holdsAx_pos not_bf_e

theorem atomicityT_not_theorem :
    ¬ Theorem (C.axioms ∪ (npc Signature.pure ∪ P.Actuality.schema)) (P.AtomicityT.quoted) :=
  not_theorem_of_model A M holdsAx_pos not_atomicityT

theorem bc_not_theorem :
    ¬ Theorem (C.axioms ∪ (npc Signature.pure ∪ P.Actuality.schema)) (P.BooleanCompleteness.quoted (.arr .e .t)) :=
  not_theorem_of_model A M holdsAx_pos not_bc

end Mono01

/-! ### Appendix D, Part 5: the surjective ones among those -/

namespace MonoSurj01

open Intensional.Premodel Intensional.MonoidModel Intensional.Monoids.MonoSurj01

local notation "A" => Intensional.MonoidModel.model Intensional.Monoids.monoSurj01
local notation "M" => Intensional.MonoidModel.model_isModel Intensional.Monoids.monoSurj01

/-- What holds: No Pure Contingency, `BF`, Actuality. -/
theorem holdsAx_pos : (A).HoldsAx (npc Signature.pure ∪ P.Barcan.schema ∪ P.Actuality.schema) :=
  holdsAx_union A (holdsAx_union A (holdsAx_npc A M)
      (by rintro _ ⟨σ, rfl⟩; exact bf σ))
      (by rintro _ rfl; exact actuality)

/-- What fails: `ND_e`, Atomicity at `t`, Boolean Completeness at `e → t`. -/
theorem holdsAx_neg : (A).HoldsAx (single (Term.neg (Sentence.nd .e)) ∪ single (Term.neg P.AtomicityT.quoted) ∪ single (Term.neg (P.BooleanCompleteness.quoted (.arr .e .t)))) :=
  holdsAx_union A (holdsAx_union A (holdsAx_single A ((holdsSentence_neg A M _).2 not_nd_e))
      (holdsAx_single A ((holdsSentence_neg A M _).2 not_atomicityT)))
      (holdsAx_single A ((holdsSentence_neg A M _).2 not_bc))

/-- The verdicts of Part 5, jointly consistent. -/
theorem consistent :
    Consistent (npc Signature.pure ∪ P.Barcan.schema ∪ P.Actuality.schema ∪
      (single (Term.neg (Sentence.nd .e)) ∪ single (Term.neg P.AtomicityT.quoted) ∪ single (Term.neg (P.BooleanCompleteness.quoted (.arr .e .t))))) :=
  Consistent.of_model A M (holdsAx_union A holdsAx_pos holdsAx_neg)

theorem nd_e_not_theorem :
    ¬ Theorem (C.axioms ∪ (npc Signature.pure ∪ P.Barcan.schema ∪ P.Actuality.schema)) (Sentence.nd .e) :=
  not_theorem_of_model A M holdsAx_pos not_nd_e

theorem atomicityT_not_theorem :
    ¬ Theorem (C.axioms ∪ (npc Signature.pure ∪ P.Barcan.schema ∪ P.Actuality.schema)) (P.AtomicityT.quoted) :=
  not_theorem_of_model A M holdsAx_pos not_atomicityT

theorem bc_not_theorem :
    ¬ Theorem (C.axioms ∪ (npc Signature.pure ∪ P.Barcan.schema ∪ P.Actuality.schema)) (P.BooleanCompleteness.quoted (.arr .e .t)) :=
  not_theorem_of_model A M holdsAx_pos not_bc

end MonoSurj01

/-! ### Appendix D, Part 6: the identity and the truncations -/

namespace Truncs

open Intensional.Premodel Intensional.MonoidModel Intensional.Monoids.Truncs

local notation "A" => Intensional.MonoidModel.model Intensional.Monoids.truncs
local notation "M" => Intensional.MonoidModel.model_isModel Intensional.Monoids.truncs

/-- What holds: No Pure Contingency, Atomicity at `t`. -/
theorem holdsAx_pos : (A).HoldsAx (npc Signature.pure ∪ P.AtomicityT.schema) :=
  holdsAx_union A (holdsAx_npc A M)
      (by rintro _ rfl; exact atomicityT)

/-- What fails: `ND_e`, `BF_e`, Actuality, Boolean Completeness at `e → t`. -/
theorem holdsAx_neg : (A).HoldsAx (single (Term.neg (Sentence.nd .e)) ∪ single (Term.neg (Sentence.bf .e)) ∪ single (Term.neg P.Actuality.quoted) ∪ single (Term.neg (P.BooleanCompleteness.quoted (.arr .e .t)))) :=
  holdsAx_union A (holdsAx_union A (holdsAx_union A (holdsAx_single A ((holdsSentence_neg A M _).2 not_nd_e))
      (holdsAx_single A ((holdsSentence_neg A M _).2 not_bf_e)))
      (holdsAx_single A ((holdsSentence_neg A M _).2 not_actuality)))
      (holdsAx_single A ((holdsSentence_neg A M _).2 not_bc))

/-- The verdicts of Part 6, jointly consistent. -/
theorem consistent :
    Consistent (npc Signature.pure ∪ P.AtomicityT.schema ∪
      (single (Term.neg (Sentence.nd .e)) ∪ single (Term.neg (Sentence.bf .e)) ∪ single (Term.neg P.Actuality.quoted) ∪ single (Term.neg (P.BooleanCompleteness.quoted (.arr .e .t))))) :=
  Consistent.of_model A M (holdsAx_union A holdsAx_pos holdsAx_neg)

theorem nd_e_not_theorem :
    ¬ Theorem (C.axioms ∪ (npc Signature.pure ∪ P.AtomicityT.schema)) (Sentence.nd .e) :=
  not_theorem_of_model A M holdsAx_pos not_nd_e

theorem bf_e_not_theorem :
    ¬ Theorem (C.axioms ∪ (npc Signature.pure ∪ P.AtomicityT.schema)) (Sentence.bf .e) :=
  not_theorem_of_model A M holdsAx_pos not_bf_e

theorem actuality_not_theorem :
    ¬ Theorem (C.axioms ∪ (npc Signature.pure ∪ P.AtomicityT.schema)) (P.Actuality.quoted) :=
  not_theorem_of_model A M holdsAx_pos not_actuality

theorem bc_not_theorem :
    ¬ Theorem (C.axioms ∪ (npc Signature.pure ∪ P.AtomicityT.schema)) (P.BooleanCompleteness.quoted (.arr .e .t)) :=
  not_theorem_of_model A M holdsAx_pos not_bc

end Truncs

/-! ### Appendix D, Part 7: the roundings to multiples of powers of `2` -/

namespace Pow2

open Intensional.Premodel Intensional.MonoidModel Intensional.Monoids.Pow2

local notation "A" => Intensional.MonoidModel.model Intensional.Monoids.pow2
local notation "M" => Intensional.MonoidModel.model_isModel Intensional.Monoids.pow2

/-- What holds: No Pure Contingency, Actuality, Atomicity at `t`. -/
theorem holdsAx_pos : (A).HoldsAx (npc Signature.pure ∪ P.Actuality.schema ∪ P.AtomicityT.schema) :=
  holdsAx_union A (holdsAx_union A (holdsAx_npc A M)
      (by rintro _ rfl; exact actuality))
      (by rintro _ rfl; exact atomicityT)

/-- What fails: `ND_e`, `BF_e`, Boolean Completeness at `e → t`. -/
theorem holdsAx_neg : (A).HoldsAx (single (Term.neg (Sentence.nd .e)) ∪ single (Term.neg (Sentence.bf .e)) ∪ single (Term.neg (P.BooleanCompleteness.quoted (.arr .e .t)))) :=
  holdsAx_union A (holdsAx_union A (holdsAx_single A ((holdsSentence_neg A M _).2 not_nd_e))
      (holdsAx_single A ((holdsSentence_neg A M _).2 not_bf_e)))
      (holdsAx_single A ((holdsSentence_neg A M _).2 not_bc))

/-- The verdicts of Part 7, jointly consistent. -/
theorem consistent :
    Consistent (npc Signature.pure ∪ P.Actuality.schema ∪ P.AtomicityT.schema ∪
      (single (Term.neg (Sentence.nd .e)) ∪ single (Term.neg (Sentence.bf .e)) ∪ single (Term.neg (P.BooleanCompleteness.quoted (.arr .e .t))))) :=
  Consistent.of_model A M (holdsAx_union A holdsAx_pos holdsAx_neg)

theorem nd_e_not_theorem :
    ¬ Theorem (C.axioms ∪ (npc Signature.pure ∪ P.Actuality.schema ∪ P.AtomicityT.schema)) (Sentence.nd .e) :=
  not_theorem_of_model A M holdsAx_pos not_nd_e

theorem bf_e_not_theorem :
    ¬ Theorem (C.axioms ∪ (npc Signature.pure ∪ P.Actuality.schema ∪ P.AtomicityT.schema)) (Sentence.bf .e) :=
  not_theorem_of_model A M holdsAx_pos not_bf_e

theorem bc_not_theorem :
    ¬ Theorem (C.axioms ∪ (npc Signature.pure ∪ P.Actuality.schema ∪ P.AtomicityT.schema)) (P.BooleanCompleteness.quoted (.arr .e .t)) :=
  not_theorem_of_model A M holdsAx_pos not_bc

end Pow2

/-! ### Appendix D, Part 8: the shifts -/

namespace Shifts

open Intensional.Premodel Intensional.MonoidModel Intensional.Monoids.Shifts

local notation "A" => Intensional.MonoidModel.model Intensional.Monoids.shifts
local notation "M" => Intensional.MonoidModel.model_isModel Intensional.Monoids.shifts

/-- What holds: No Pure Contingency, `BF`, Actuality, Atomicity at `t`. -/
theorem holdsAx_pos : (A).HoldsAx (npc Signature.pure ∪ P.Barcan.schema ∪ P.Actuality.schema ∪ P.AtomicityT.schema) :=
  holdsAx_union A (holdsAx_union A (holdsAx_union A (holdsAx_npc A M)
      (by rintro _ ⟨σ, rfl⟩; exact bf σ))
      (by rintro _ rfl; exact actuality))
      (by rintro _ rfl; exact atomicityT)

/-- What fails: `ND_e`, Boolean Completeness at `e → t`. -/
theorem holdsAx_neg : (A).HoldsAx (single (Term.neg (Sentence.nd .e)) ∪ single (Term.neg (P.BooleanCompleteness.quoted (.arr .e .t)))) :=
  holdsAx_union A (holdsAx_single A ((holdsSentence_neg A M _).2 not_nd_e))
      (holdsAx_single A ((holdsSentence_neg A M _).2 not_bc))

/-- The verdicts of Part 8, jointly consistent. -/
theorem consistent :
    Consistent (npc Signature.pure ∪ P.Barcan.schema ∪ P.Actuality.schema ∪ P.AtomicityT.schema ∪
      (single (Term.neg (Sentence.nd .e)) ∪ single (Term.neg (P.BooleanCompleteness.quoted (.arr .e .t))))) :=
  Consistent.of_model A M (holdsAx_union A holdsAx_pos holdsAx_neg)

theorem nd_e_not_theorem :
    ¬ Theorem (C.axioms ∪ (npc Signature.pure ∪ P.Barcan.schema ∪ P.Actuality.schema ∪ P.AtomicityT.schema)) (Sentence.nd .e) :=
  not_theorem_of_model A M holdsAx_pos not_nd_e

theorem bc_not_theorem :
    ¬ Theorem (C.axioms ∪ (npc Signature.pure ∪ P.Barcan.schema ∪ P.Actuality.schema ∪ P.AtomicityT.schema)) (P.BooleanCompleteness.quoted (.arr .e .t)) :=
  not_theorem_of_model A M holdsAx_pos not_bc

end Shifts

end Classicism.Meta
