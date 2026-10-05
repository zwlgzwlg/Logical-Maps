import Classicism.Results.SentenceSchemas.Contingency
import Classicism.Syntax.WitnessedPossibility

/-!
# Witnessed Possibility, Logical Necessity and Modal Freedom

The map's arrows among the schemas with constants put for variables
(`Syntax/WitnessedPossibility.lean`) and No (Pure) Contingency. Each instance needs one
object-level step, a shallow lemma about propositions certified once and instantiated at
the sentences the instance mentions (`allEβ`, `allE₂β`):

- `logical-necessity-r-implies-no-pure-contingency-r`,
  `converse-witnessed-possibility-r-implies-no-pure-contingency-r`,
  `modal-freedom-signature-r-implies-no-pure-contingency-r`: the instances with no
  constants, at a pure sentence `P` (and, for Modal Freedom, `¬P`).
- `no-pure-contingency-r-implies-converse-witnessed-possibility-r`: No Pure Contingency at
  `¬∃x̄. P`; with `P[c̄/x̄] → ∃x̄. P` necessitated (`C.Theorem.nec`), `◇P[c̄/x̄]` gives `∃x̄. P`.
- `no-contingency-signature-r-implies-modal-freedom-signature-r`: No Contingency at
  `¬P[c̄/x̄]` and `¬Q[d̄/ȳ]`.
- `witnessed-possibility-and-npc-imply-possibly-witnessed-possibility`: No Pure Contingency
  makes the possible pure sentence `∃x̄. P` true (`npc_dia_imp`).
- `possibly-witnessed-possibility-r-implies-witnessed-possibility-r`: `p → ◇p`.
- `logical-necessity-r-implies-witnessed-possibility-r`: Logical Necessity at `¬P`, with
  `∃x̄. P → ¬∀x̄. ¬P` (a block De Morgan law, `Syntax/Blocks.lean`).
- `witnessed-possibility-and-no-pure-contingency-imply-logical-necessity`: left to right,
  Witnessed Possibility at `¬P` with `¬∀x̄. P → ∃x̄. ¬P`; right to left, No Pure
  Contingency at `∀x̄. P` and `∀x̄. P → P[c̄/x̄]` necessitated.

The incompatibilities of Witnessed Possibility with No Contingency for the signature,
with Signature B and with ND are not here: they need a constant, and at a signature with
none Witnessed Possibility says only `P → ◇P`.
-/

namespace Classicism

/-- From `□p ↔ p`, with `p` true, `□p`: the left-to-right half of nothing more than the
biconditional. -/
theorem iff_box_imp_box (p : Prop) : (□ p ↔ p) → p → □ p := fun h => h.2

/-- If `◇¬p` would make `p` false, a true `p` is necessary. -/
theorem cwp_box (p : Prop) : (◇ ¬ p → ¬ p) → p → □ p :=
  fun h hp => (em (□ p)).elim id fun hn => absurd hp (h (dia_not_of_not_box p hn))

/-- No Pure Contingency at `¬a`, with `□(b → a)`: `◇b` gives `a`. -/
theorem npc_cwp (a b : Prop) : (¬ a → □ ¬ a) → □ (b → a) → ◇ b → a :=
  fun h₁ h₂ h₃ => (em a).elim id fun hna =>
    absurd h₃ (not_dia_of_box_not b (modal_K _ _ (modal_K _ _
      (nec% (fun (hba : b → a) (hna' : ¬ a) (hb : b) => hna' (hba hb))) h₂) (h₁ hna)))

/-- If `p` and `¬p` jointly possible whenever each is, a true `p` is necessary. -/
theorem mf_box (p : Prop) : (◇ p ∧ ◇ ¬ p → ◇ (p ∧ ¬ p)) → p → □ p :=
  fun h hp => (em (□ p)).elim id fun hn =>
    absurd (h ⟨dia_intro p hp, dia_not_of_not_box p hn⟩)
      (not_dia_of_box_not (p ∧ ¬ p) (nec% (fun (h' : p ∧ ¬ p) => h'.2 h'.1)))

/-- No Contingency at `¬a` and `¬b` makes what is possible true, so `a ∧ b` follows from
`◇a ∧ ◇b`, and is possible. -/
theorem nc_mf (a b : Prop) : (¬ a → □ ¬ a) → (¬ b → □ ¬ b) → ◇ a ∧ ◇ b → ◇ (a ∧ b) :=
  fun h₁ h₂ h => dia_intro (a ∧ b) ⟨npc_dia_imp a h₁ h.1, npc_dia_imp b h₂ h.2⟩

/-- No Pure Contingency at `¬a`, with `a → ◇b`: `◇a` gives `◇b`. -/
theorem npc_wp_pwp (a b : Prop) : (¬ a → □ ¬ a) → (a → ◇ b) → ◇ a → ◇ b :=
  fun h₁ h₂ h₃ => h₂ (npc_dia_imp a h₁ h₃)

/-- From `◇a → ◇b`, `a → ◇b`. -/
theorem pwp_wp (a b : Prop) : (◇ a → ◇ b) → a → ◇ b := fun h ha => h (dia_intro a ha)

/-- Logical Necessity at `¬b`, `□¬b ↔ f`, with `e → ¬f`: `e` gives `◇b`. -/
theorem ln_wp (b e f : Prop) : (□ ¬ b ↔ f) → (e → ¬ f) → e → ◇ b :=
  fun h₁ h₂ he => by rw [dia_eq_not_box_not]; exact fun hb => h₂ he (h₁.1 hb)

/-- Witnessed Possibility at `¬b` (`e → ◇¬b`, with `¬a → e`), No Pure Contingency at `a`,
and `□(a → b)`: `□b ↔ a`. -/
theorem wp_npc_ln (b a e : Prop) : (e → ◇ ¬ b) → (¬ a → e) → (a → □ a) → □ (a → b) → (□ b ↔ a) :=
  fun h₁ h₂ h₃ h₄ =>
    ⟨fun hb => (em a).elim id fun hna => absurd (h₁ (h₂ hna)) (by rw [hb]; exact fun h => h not_true_eq),
     fun ha => modal_K _ _ h₄ (h₃ ha)⟩

#classicism_derive Classicism.iff_box_imp_box Classicism.cwp_box Classicism.npc_cwp
  Classicism.mf_box Classicism.nc_mf Classicism.npc_wp_pwp Classicism.pwp_wp
  Classicism.ln_wp Classicism.wp_npc_ln

namespace Meta

open AxiomSet

variable {Sig : Signature}

/-- The instances built below are in the paper's language when those they are built from
are: the side condition of every sentence schema (`Syntax/ClosedTypes.lean`). -/
local macro "split_closed " h:ident : tactic => `(tactic| simp only [Term.closedTypes_imp,
  Term.closedTypes_iff, Term.closedTypes_dia, Term.closedTypes_box, Term.closedTypes_conj,
  Term.closedTypes_neg, Term.closedTypes_ofPure, Term.closedTypes_atConsts,
  Term.closedTypes_forallBlock_eq_existsBlock, Term.closedTypes_eq', Term.closedTypes_bot,
  Term.closedTypes_top, Term.closedTypes_forall', Term.closedTypes_var, Ty.closed_rel,
  RTy.closed_t, decide_true, Bool.and_true, Bool.and_eq_true, and_true] at $h:ident)

/-- `logical-necessity-r-implies-no-pure-contingency-r`: Logical Necessity with no
constants, at a pure sentence `P`, is `□P ↔ P`. -/
theorem logicalNecessity_entails_npc :
    logicalNecessity Sig ⟹ AxiomSet.ofPure (npc Signature.pure) := by
  rintro a ⟨_, ⟨hq, q, -, rfl⟩, rfl⟩
  split_closed hq
  have h : Theorem (C.axioms ∪ logicalNecessity Sig)
      (Term.iff (Term.box (Term.atConsts [] q)) (Term.ofPure (Term.forallBlock [] q))) :=
    Theorem.ax (logicalNecessity_mem List.nodup_nil hq.1)
  rw [Term.atConsts_nil] at h
  exact Theorem.mp (Derivable.allEβ
    (Theorem.ofCMinus (C.TheoremMinus.ofPure iff_box_imp_box.derivable)) _) h

/-- `converse-witnessed-possibility-r-implies-no-pure-contingency-r`: the instance with no
constants at `¬P` is `◇¬P → ¬P`. -/
theorem converseWitnessedPossibility_entails_npc :
    converseWitnessedPossibility Sig ⟹ AxiomSet.ofPure (npc Signature.pure) := by
  rintro a ⟨_, ⟨hq, q, -, rfl⟩, rfl⟩
  split_closed hq
  have h : Theorem (C.axioms ∪ converseWitnessedPossibility Sig)
      (Term.imp (Term.dia (Term.atConsts [] (Term.neg q))) (Term.ofPure (Term.existsBlock [] (Term.neg q)))) :=
    Theorem.ax (converseWitnessedPossibility_mem List.nodup_nil
      (by rw [closedTypes_existsBlock_neg]; exact hq.1))
  rw [Term.atConsts_nil] at h
  exact Theorem.mp (Derivable.allEβ
    (Theorem.ofCMinus (C.TheoremMinus.ofPure cwp_box.derivable)) _) h

/-- `no-pure-contingency-r-implies-converse-witnessed-possibility-r`: No Pure Contingency at
the pure `¬∃x̄. P`, and `P[c̄/x̄] → ∃x̄. P` necessitated. -/
theorem npc_entails_converseWitnessedPossibility :
    AxiomSet.ofPure (npc Signature.pure) ⟹ converseWitnessedPossibility Sig := by
  rintro a ⟨hc, cs, P, -, rfl⟩
  split_closed hc
  have hBA : C.Theorem (Term.imp (Term.atConsts cs P) (Term.ofPure (Term.existsBlock _ P))) := by
    rw [Term.ofPure_existsBlock]
    exact Derivable.impI (Derivable.exIBlock _ (Terms.consts cs) Derivable.hyp₀)
  have hnpc : Theorem (C.axioms ∪ AxiomSet.ofPure (Sig := Sig) (npc Signature.pure))
      (Term.imp (Term.neg (Term.ofPure (Term.existsBlock _ P)))
        (Term.box (Term.neg (Term.ofPure (Term.existsBlock _ P))))) :=
    Theorem.ax ⟨_, npc_mem (p := Term.neg (Term.existsBlock _ P)) (Term.pure_of_pureSig _)
      (by rw [Term.closedTypes_neg]; exact hc.2), rfl⟩
  exact Theorem.mp₂ (Derivable.allE₂β
    (Theorem.ofCMinus (C.TheoremMinus.ofPure npc_cwp.derivable)) _ _) hnpc
    (Theorem.ofC (C.Theorem.nec hBA))

/-- `modal-freedom-signature-r-implies-no-pure-contingency-r`: the instance with no
constants, at a pure sentence `P` and at `¬P`. -/
theorem modalFreedom_entails_npc :
    modalFreedom Sig ⟹ AxiomSet.ofPure (npc Signature.pure) := by
  rintro a ⟨_, ⟨hq, q, -, rfl⟩, rfl⟩
  split_closed hq
  have h : Theorem (C.axioms ∪ modalFreedom Sig)
      (Term.imp (Term.conj (Term.dia (Term.atConsts [] q)) (Term.dia (Term.atConsts [] (Term.neg q))))
        (Term.dia (Term.conj (Term.atConsts [] q) (Term.atConsts [] (Term.neg q))))) :=
    Theorem.ax (modalFreedom_mem List.nodup_nil hq.1 (by rw [Term.closedTypes_neg]; exact hq.1))
  rw [Term.atConsts_nil, Term.atConsts_nil] at h
  exact Theorem.mp (Derivable.allEβ
    (Theorem.ofCMinus (C.TheoremMinus.ofPure mf_box.derivable)) _) h

/-- `no-contingency-signature-r-implies-modal-freedom-signature-r`: No Contingency at
`¬P[c̄/x̄]` and at `¬Q[d̄/ȳ]`. -/
theorem noContingency_entails_modalFreedom : noContingency Sig ⟹ modalFreedom Sig := by
  rintro a ⟨hc, cs, ds, P, Q, -, rfl⟩
  split_closed hc
  exact Theorem.mp₂ (Derivable.allE₂β
    (Theorem.ofCMinus (C.TheoremMinus.ofPure nc_mf.derivable)) _ _)
    (Theorem.ax (noContingency_mem (p := Term.neg (Term.atConsts cs P))
      (by rw [Term.closedTypes_neg, Term.closedTypes_atConsts]; exact hc.1.1)))
    (Theorem.ax (noContingency_mem (p := Term.neg (Term.atConsts ds Q))
      (by rw [Term.closedTypes_neg, Term.closedTypes_atConsts]; exact hc.1.2)))

/-- `witnessed-possibility-and-npc-imply-possibly-witnessed-possibility`: No Pure
Contingency makes the possible pure sentence `∃x̄. P` true, and Witnessed Possibility
then gives `◇P[c̄/x̄]`. -/
theorem npc_witnessedPossibility_entails_possiblyWitnessedPossibility :
    AxiomSet.ofPure (npc Signature.pure) ∪ witnessedPossibility Sig ⟹
      possiblyWitnessedPossibility Sig := by
  rintro a ⟨hc, cs, P, hcs, rfl⟩
  split_closed hc
  exact Theorem.mp₂ (Derivable.allE₂β
    (Theorem.ofCMinus (C.TheoremMinus.ofPure npc_wp_pwp.derivable)) _ _)
    (Theorem.ax (Or.inl ⟨_, npc_mem (p := Term.neg (Term.existsBlock _ P)) (Term.pure_of_pureSig _)
      (by rw [Term.closedTypes_neg]; exact hc.1), rfl⟩))
    (Theorem.ax (Or.inr (witnessedPossibility_mem hcs hc.1)))

/-- `possibly-witnessed-possibility-r-implies-witnessed-possibility-r`: `∃x̄. P` gives
`◇∃x̄. P`. -/
theorem possiblyWitnessedPossibility_entails_witnessedPossibility :
    possiblyWitnessedPossibility Sig ⟹ witnessedPossibility Sig := by
  rintro a ⟨hc, cs, P, hcs, rfl⟩
  split_closed hc
  exact Theorem.mp (Derivable.allE₂β
    (Theorem.ofCMinus (C.TheoremMinus.ofPure pwp_wp.derivable)) _ _)
    (Theorem.ax (possiblyWitnessedPossibility_mem hcs hc.1))

/-- `logical-necessity-r-implies-witnessed-possibility-r`: Logical Necessity at `¬P` is
`□¬P[c̄/x̄] ↔ ∀x̄. ¬P`, and `∃x̄. P` refutes the right side. -/
theorem logicalNecessity_entails_witnessedPossibility :
    logicalNecessity Sig ⟹ witnessedPossibility Sig := by
  rintro a ⟨hc, cs, P, hcs, rfl⟩
  split_closed hc
  have hln : Theorem (C.axioms ∪ logicalNecessity Sig)
      (Term.iff (Term.box (Term.atConsts cs (Term.neg P))) (Term.ofPure (Term.forallBlock _ (Term.neg P)))) :=
    Theorem.ax (logicalNecessity_mem hcs (by rw [closedTypes_existsBlock_neg]; exact hc.1))
  have hef : C.Theorem (Term.imp (Term.ofPure (Sig := Sig) (Term.existsBlock _ P))
      (Term.neg (Term.ofPure (Term.forallBlock _ (Term.neg P))))) := by
    rw [Term.ofPure_existsBlock, Term.ofPure_forallBlock]
    exact Derivable.impI (Derivable.notI (q := Term.top)
      (Derivable.existsBlock_forallBlock_neg _ (Derivable.weaken₁ Derivable.hyp₀) Derivable.hyp₀)
      (Derivable.existsBlock_forallBlock_neg _ (Derivable.weaken₁ Derivable.hyp₀) Derivable.hyp₀))
  exact Theorem.mp₂ (Derivable.allE₃β
    (Theorem.ofCMinus (C.TheoremMinus.ofPure ln_wp.derivable)) _ _ _) hln (Theorem.ofC hef)

/-- `witnessed-possibility-and-no-pure-contingency-imply-logical-necessity`. -/
theorem npc_witnessedPossibility_entails_logicalNecessity :
    AxiomSet.ofPure (npc Signature.pure) ∪ witnessedPossibility Sig ⟹ logicalNecessity Sig := by
  rintro a ⟨hc, cs, P, hcs, rfl⟩
  split_closed hc
  have hwp : Theorem (C.axioms ∪ (AxiomSet.ofPure (Sig := Sig) (npc Signature.pure) ∪ witnessedPossibility Sig))
      (Term.imp (Term.ofPure (Term.existsBlock _ (Term.neg P))) (Term.dia (Term.atConsts cs (Term.neg P)))) :=
    Theorem.ax (Or.inr (witnessedPossibility_mem hcs (by rw [closedTypes_existsBlock_neg]; exact hc.2.1)))
  have hae : C.Theorem (Term.imp (Term.neg (Term.ofPure (Sig := Sig) (Term.forallBlock _ P)))
      (Term.ofPure (Term.existsBlock _ (Term.neg P)))) := by
    rw [Term.ofPure_existsBlock, Term.ofPure_forallBlock]
    exact Derivable.impI (Derivable.existsBlock_neg_of_not_forallBlock _ Derivable.hyp₀)
  have hnpc : Theorem (C.axioms ∪ (AxiomSet.ofPure (Sig := Sig) (npc Signature.pure) ∪ witnessedPossibility Sig))
      (Term.imp (Term.ofPure (Term.forallBlock _ P)) (Term.box (Term.ofPure (Term.forallBlock _ P)))) :=
    Theorem.ax (Or.inl ⟨_, npc_mem (p := Term.forallBlock _ P) (Term.pure_of_pureSig _)
      (by rw [Term.closedTypes_forallBlock_eq_existsBlock]; exact hc.2.1), rfl⟩)
  have hab : C.Theorem (Term.imp (Term.ofPure (Sig := Sig) (Term.forallBlock _ P)) (Term.atConsts cs P)) := by
    rw [Term.ofPure_forallBlock]
    exact Derivable.impI (Derivable.allEBlock _ Derivable.hyp₀ (Terms.consts cs))
  exact Theorem.mp (Theorem.mp (Theorem.mp₂ (Derivable.allE₃β
    (Theorem.ofCMinus (C.TheoremMinus.ofPure wp_npc_ln.derivable)) _ _ _)
    hwp (Theorem.ofC hae)) hnpc) (Theorem.ofC (C.Theorem.nec hab))

end Meta

end Classicism
