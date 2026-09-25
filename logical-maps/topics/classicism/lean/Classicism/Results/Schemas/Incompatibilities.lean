import Classicism.Results.Schemas.Consistency
import Classicism.Results.Schemas.PossibilityDistinctness
import Classicism.Results.Schemas.Contingency

/-!
# What Possibility and Distinctness exclude

The map's incompatibilities whose proof is "a model of `C` refutes `Y`, so Possibility
makes `¬Y` possible, which `□Y` forbids" — the pattern the map states at
`possibility-and-necessary-barcan-t-incompatible` — and its relatives. Each needs a
consistency fact, from `Consistency.lean`, and one object-level step, a shallow lemma
certified once:

- **Possibility refutes every necessitation of a refutable sentence**:
  `possibility_box_inconsistent`, for any theory and signature; through the equivalence
  with Distinctness, so does Distinctness, and so does the maximalization
  (`max_box_inconsistent`). The instances the models give:
  `possibility-and-necessary-barcan-t-incompatible` (`¬BF_t` consistent),
  `maximalist-distinctness-incompatible-with-necessary-barcan-r`,
  `maximalist-distinctness-incompatible-with-necessary-tractarianism-r` (`¬Tract_t`
  consistent, by the certified record that Tractarianism implies BF), and the
  necessitation of `ND_t`, which the map reaches through `maximalist-distinctness-incompatible-with-nd`.
- `maximalist-distinctness-incompatible-with-nd` itself: `FA = ⊤` is neither a theorem
  nor refutable, so Distinctness has `FA ≠ ⊤` and Possibility `◇(FA = ⊤)`; `ND_t` at
  `FA, ⊤` makes the first necessary. Two binders instantiated at once (`allE₂β`).
- `possibility-and-no-pure-contingency-incompatible`: the Fregean Axiom and its negation
  are both consistent, so both are possible, and whichever is true, No Pure Contingency
  makes it necessary. General form `possibility_npc_inconsistent`, for any such `Y`.
- `pure-b-and-pure-possibility-incompatible`: the same two possibilities, with B for the
  pure sentence `¬FA` in place of No Pure Contingency; the object-level reasoning is the
  shallow lemma `pureB_fregean_contra`.

Not here, for want of the models: the incompatibilities with `□`Strong Leibniz (`t`),
`□`Relational Choice, Countable Boolean Completeness and the Necessity of Arithmetic
(coalesced sums, a Henkin model without choice, Gödel), and the maximalist ones with
`□`Actuality, `□`Atomicity, `□`Boolean Completeness, `□`Functionality and Rigid
Comprehension.
-/

namespace Classicism

/-- `□p` and `◇¬p` are contradictory. -/
theorem box_dia_neg_contra (p : Prop) : □ p → ◇ (¬ p) → False :=
  fun hb hd => hd (by rw [hb]; exact not_true_eq)

theorem eq_false_of_not_eq_true (p : Prop) : (¬ p) = True → p = False :=
  fun h => by rw [← not_not_eq p, h, not_true_eq]

/-- `□¬p` and `◇p` are contradictory. -/
theorem box_not_dia_contra (p : Prop) : □ (¬ p) → ◇ p → False :=
  fun hb hd => hd (eq_false_of_not_eq_true p hb)

/-- No Pure Contingency at `p` and at `¬p` is contradicted by `◇p` and `◇¬p`: by excluded
middle one of them is true, hence necessary. -/
theorem npc_possibility_contra (p : Prop) : (p → □ p) → (¬ p → □ ¬ p) → ◇ p → ◇ ¬ p → False :=
  fun h₁ h₂ hd₁ hd₂ => (em p).elim (fun hp => box_dia_neg_contra p (h₁ hp) hd₂)
    (fun hn => box_not_dia_contra p (h₂ hn) hd₁)

/-- Where the Fregean Axiom is possible it is necessary, so it is not possibly false. -/
theorem not_fregean_of_dia_neg : ◇ ¬ P.FregeanAxiom → ¬ P.FregeanAxiom :=
  fun hd hF => box_dia_neg_contra _ (fregean_box _ hF hF) hd

/-- B for `¬FA` is contradicted by `◇FA` and `◇¬FA`: if `FA`, it is necessary, against
`◇¬FA`; if `¬FA`, B gives `□◇¬FA`, and necessarily `◇¬FA → ¬FA`, so `□¬FA`, against
`◇FA`. -/
theorem pureB_fregean_contra :
    (¬ P.FregeanAxiom → □ ◇ ¬ P.FregeanAxiom) → ◇ P.FregeanAxiom → ◇ ¬ P.FregeanAxiom → False :=
  fun hB hd₁ hd₂ => (em P.FregeanAxiom).elim
    (fun hF => box_dia_neg_contra _ (fregean_box _ hF hF) hd₂)
    (fun hn => box_not_dia_contra _ (modal_K _ _ (nec% not_fregean_of_dia_neg) (hB hn)) hd₁)

#classicism_derive Classicism.box_dia_neg_contra Classicism.box_not_dia_contra
  Classicism.npc_possibility_contra Classicism.pureB_fregean_contra

namespace Meta

open AxiomSet

variable {Sig : Signature}

/-! ### Possibility refutes the necessitation of anything refutable -/

/-- **Possibility relative to `T` is inconsistent with `□Y` whenever `¬Y` is consistent
with `T`**: Possibility has `◇¬Y`. -/
theorem possibility_box_inconsistent {Ax : AxiomSet Sig} {Y : Sentence Sig}
    (h : Consistent (Ax ∪ single (Term.neg Y))) :
    ¬ Consistent (possibility Ax ∪ single (Term.box Y)) := fun hc => hc <|
  have hd : Theorem (C.axioms ∪ (possibility Ax ∪ single (Term.box Y))) (Term.dia (Term.neg Y)) :=
    Theorem.ax (Or.inl ⟨Term.neg Y, h, rfl⟩)
  have hb : Theorem (C.axioms ∪ (possibility Ax ∪ single (Term.box Y))) (Term.box Y) :=
    Theorem.ax (Or.inr rfl)
  Derivable.notE hd (Theorem.mp (Derivable.allEβ
    (Theorem.ofCMinus (C.TheoremMinus.ofPure box_dia_neg_contra.derivable)) Y) hb)

/-- Distinctness is Possibility, so it excludes the same. -/
theorem distinctness_box_inconsistent {Ax : AxiomSet Sig} {Y : Sentence Sig}
    (h : Consistent (Ax ∪ single (Term.neg Y))) :
    ¬ Consistent (distinctness Ax ∪ single (Term.box Y)) := fun hc =>
  possibility_box_inconsistent h (Consistent.of_entails
    (Entails.union (Entails.mono_left (subset_union_left _ _) (distinctness_entails_possibility Ax))
      (Entails.union_right _ _)) hc)

/-- And so does the maximalization of the theory. -/
theorem max_box_inconsistent {Ax : AxiomSet Sig} {Y : Sentence Sig}
    (h : Consistent (Ax ∪ single (Term.neg Y))) :
    ¬ Consistent (max Ax ∪ single (Term.box Y)) := fun hc =>
  distinctness_box_inconsistent h
    (Consistent.mono (fun _ ha => ha.elim (fun h => Or.inl (Or.inr h)) Or.inr) hc)

/-- `possibility-and-necessary-barcan-t-incompatible`. -/
theorem possibility_necBarcanT_inconsistent :
    ¬ Consistent (possibility (empty : AxiomSet Signature.pure) ∪ P.NecBarcanT.schema) :=
  possibility_box_inconsistent (Consistent.empty_union Idem.not_bf_t_consistent)

/-- `maximalist-distinctness-incompatible-with-necessary-barcan-r`, through the `t`
instance. -/
theorem maximalist_necBarcanT_inconsistent :
    ¬ Consistent (maximalist (Sig := Signature.pure) ∪ P.NecBarcanT.schema) :=
  max_box_inconsistent (Consistent.empty_union Idem.not_bf_t_consistent)

theorem maximalist_necBarcan_inconsistent :
    ¬ Consistent (maximalist (Sig := Signature.pure) ∪ AxiomSet.box P.Barcan.schema) := fun hc =>
  maximalist_necBarcanT_inconsistent (Consistent.mono
    (fun a ha => ha.elim Or.inl (fun h => Or.inr (by
      subst (h : a = P.NecBarcanT.quoted); exact AxiomSet.mem_box ⟨Ty.t, rfl⟩))) hc)

/-- `maximalist-distinctness-incompatible-with-necessary-tractarianism-r`, through the
`t` instance, which fails in the idempotent-monoid model because it implies `BF_t`. -/
theorem maximalist_necTractarianism_inconsistent :
    ¬ Consistent (maximalist (Sig := Signature.pure) ∪ AxiomSet.box P.Tractarianism.schema) := fun hc =>
  max_box_inconsistent (Y := P.Tractarianism.quoted Ty.t)
    (Consistent.empty_union Idem.not_tractarianism_t_consistent)
    (Consistent.mono (fun a ha => ha.elim Or.inl (fun h => Or.inr (by
      subst (h : a = Term.box (P.Tractarianism.quoted Ty.t)); exact AxiomSet.mem_box ⟨Ty.t, rfl⟩))) hc)

/-- Possibility (pure) is inconsistent with `□ND_t` (the map has this through
`maximalist-distinctness-incompatible-with-nd`). -/
theorem possibility_necNdT_inconsistent :
    ¬ Consistent (possibility (empty : AxiomSet Signature.pure) ∪ P.NecNecessityOfDistinctnessT.schema) :=
  possibility_box_inconsistent (Consistent.empty_union Idem.not_nd_t_consistent)

/-! ### Maximalist Classicism and `ND` -/

/-- **`maximalist-distinctness-incompatible-with-nd`**: `FA = ⊤` is not a theorem (the
group model) and is consistent (`Prop`), so Distinctness has `FA ≠ ⊤` and Possibility
`◇(FA = ⊤)`; `ND_t` at `FA` and `⊤` makes `FA ≠ ⊤` necessary, against `◇(FA = ⊤)`. -/
theorem maximalist_ndT_inconsistent :
    ¬ Consistent (maximalist (Sig := Signature.pure) ∪ P.NecessityOfDistinctnessT.schema) := fun hc => hc <|
  let FA := P.FregeanAxiom.quoted
  have h₁ : Theorem (C.axioms ∪ (maximalist ∪ P.NecessityOfDistinctnessT.schema))
      (Term.neg (Term.eq' FA Term.top)) :=
    Theorem.ax (Or.inl (Or.inr ⟨Ty.t, FA, Term.top, Invol.box_fregean_not_theorem, rfl⟩))
  have h₂ : Theorem (C.axioms ∪ (maximalist ∪ P.NecessityOfDistinctnessT.schema))
      (Term.dia (Term.eq' FA Term.top)) :=
    Entails.mono_left (subset_union_left _ _) (maximalist_entails_possibility) _
      ⟨Term.eq' FA Term.top, Consistent.empty_union box_fregean_consistent, rfl⟩
  have h₃ : Theorem (C.axioms ∪ (maximalist ∪ P.NecessityOfDistinctnessT.schema))
      (Term.box (Term.neg (Term.eq' FA Term.top))) :=
    Theorem.mp (Derivable.allE₂β
      (Theorem.ax (Ax := maximalist ∪ P.NecessityOfDistinctnessT.schema)
        (a := P.NecessityOfDistinctnessT.quoted) (Or.inr rfl)) FA Term.top) h₁
  Derivable.notE h₂ (Theorem.mp (Derivable.allEβ (Theorem.ofCMinus box_not_dia_contra.derivable)
    (Term.eq' FA Term.top)) h₃)

/-- The record's own premise, `ND` at every type. -/
theorem maximalist_nd_inconsistent :
    ¬ Consistent (maximalist (Sig := Signature.pure) ∪ P.NecessityOfDistinctness.schema) := fun hc =>
  maximalist_ndT_inconsistent
    (Consistent.mono (fun _ ha => ha.elim Or.inl (fun h => Or.inr (h ▸ ⟨Ty.t, rfl⟩))) hc)

/-! ### Possibility and No Pure Contingency -/

/-- **Possibility is inconsistent with No Pure Contingency** whenever some pure `Y` and
its negation are both consistent with the theory. -/
theorem possibility_npc_inconsistent {Ax : AxiomSet Sig} {Y : Sentence Sig} (hY : Y.pure = true)
    (h₁ : Consistent (Ax ∪ single Y)) (h₂ : Consistent (Ax ∪ single (Term.neg Y))) :
    ¬ Consistent (possibility Ax ∪ npc Sig) := fun hc => hc <|
  have hd₁ : Theorem (C.axioms ∪ (possibility Ax ∪ npc Sig)) (Term.dia Y) :=
    Theorem.ax (Or.inl ⟨Y, h₁, rfl⟩)
  have hd₂ : Theorem (C.axioms ∪ (possibility Ax ∪ npc Sig)) (Term.dia (Term.neg Y)) :=
    Theorem.ax (Or.inl ⟨Term.neg Y, h₂, rfl⟩)
  have hn₁ : Theorem (C.axioms ∪ (possibility Ax ∪ npc Sig)) (Term.imp Y (Term.box Y)) :=
    Theorem.ax (Or.inr ⟨Y, hY, rfl⟩)
  have hn₂ : Theorem (C.axioms ∪ (possibility Ax ∪ npc Sig))
      (Term.imp (Term.neg Y) (Term.box (Term.neg Y))) :=
    Theorem.ax (Or.inr ⟨Term.neg Y, by simp [Term.pure, hY], rfl⟩)
  Derivable.notE hd₂ (Theorem.mp (Theorem.mp (Theorem.mp (Derivable.allEβ
    (Theorem.ofCMinus (C.TheoremMinus.ofPure npc_possibility_contra.derivable)) Y) hn₁) hn₂) hd₁)

/-- `possibility-and-no-pure-contingency-incompatible`: the Fregean Axiom is the pure
sentence, consistent by `Prop` and refutable by the M-set models. -/
theorem possibility_schema_npc_inconsistent :
    ¬ Consistent (possibility (empty : AxiomSet Signature.pure) ∪ npc Signature.pure) :=
  possibility_npc_inconsistent P.FregeanAxiom.quoted.pure_of_pureSig
    (Consistent.empty_union fregean_consistent) (Consistent.empty_union Idem.not_fregean_consistent)

/-- `pure-b-and-pure-possibility-incompatible`. -/
theorem possibility_pureB_inconsistent :
    ¬ Consistent (possibility (empty : AxiomSet Signature.pure) ∪ pureB Signature.pure) := fun hc => hc <|
  let FA := P.FregeanAxiom.quoted
  have hB : Theorem (C.axioms ∪ (possibility empty ∪ pureB Signature.pure))
      (Term.imp (Term.neg FA) (Term.box (Term.dia (Term.neg FA)))) :=
    Theorem.ax (Or.inr ⟨Term.neg FA, (Term.neg FA).pure_of_pureSig, rfl⟩)
  have hd₁ : Theorem (C.axioms ∪ (possibility empty ∪ pureB Signature.pure)) (Term.dia FA) :=
    Theorem.ax (Or.inl ⟨FA, Consistent.empty_union fregean_consistent, rfl⟩)
  have hd₂ : Theorem (C.axioms ∪ (possibility empty ∪ pureB Signature.pure)) (Term.dia (Term.neg FA)) :=
    Theorem.ax (Or.inl ⟨Term.neg FA, Consistent.empty_union Idem.not_fregean_consistent, rfl⟩)
  Derivable.notE hd₂ ((Theorem.ofCMinus pureB_fregean_contra.derivable).mp₂ hB hd₁)

end Meta

end Classicism
