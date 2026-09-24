import Classicism.Meta.Entailment

/-!
# Schemas over the syntax

The map's principles that are schemas over *sentences* rather than over types: No Pure
Contingency, No Contingency and B for a signature, Distinctness, Possibility, and the
maximalization of a theory. None is the reading of a shallow definition — the shallow
layer cannot quantify over syntax, which was purpose one of this layer — so none can come
from `#classicism_schema`, and this module is their home, as `Schemas.lean` is the home
of the type-indexed ones. Each is an `AxiomSet`, so that the entailments of
`Entailment.lean` and the model facts of `Action*.lean` apply to them as to the others.

Two conventions. A schema "for a signature `Σ`" is the schema at `Sig := Σ`; at
`Signature.pure`, where every term is pure, it is the map's "(pure)" version, so one
definition serves both. And a schema relative to a theory `T` is relative to
`C.axioms ∪ Ax`, as entailment is.

Map ids: `no-pure-contingency-r` (`npc`), `no-contingency-signature-r` (`noContingency`),
`signature-b-r` (`signatureB`), `distinctness-schema-r` / `distinctness-signature-r`
(`distinctness`), `possibility-schema-r` / `possibility-signature-r` (`possibility`).
Not yet here: the schemas with substitution of constants for variables (Witnessed
Possibility and its kin), Possibility+, and Strong Possibility, which needs `◇_≠`.
-/

namespace Classicism.Meta

namespace AxiomSet

variable (Sig : Signature)

/-- No Pure Contingency: `P → □P` for every pure sentence `P`. -/
def npc : AxiomSet Sig :=
  fun a => ∃ p : Sentence Sig, p.pure = true ∧ a = Term.imp p (Term.box p)

/-- No Contingency for the signature: `P → □P` for every sentence `P`. -/
def noContingency : AxiomSet Sig :=
  fun a => ∃ p : Sentence Sig, a = Term.imp p (Term.box p)

/-- B for the sentences of the signature: `P → □◇P`. -/
def signatureB : AxiomSet Sig :=
  fun a => ∃ p : Sentence Sig, a = Term.imp p (Term.box (Term.dia p))

variable {Sig}

/-- **Distinctness**, relative to `C ∪ Ax`: `A ≠ B` for every closed `A = B` that is not a
theorem (Classicism, §"Finer-grained strengthenings"). -/
def distinctness (Ax : AxiomSet Sig) : AxiomSet Sig :=
  fun a => ∃ (σ : Ty) (x y : Term Sig [] σ),
    ¬ Theorem (C.axioms ∪ Ax) (Term.eq' x y) ∧ a = Term.neg (Term.eq' x y)

/-- **Possibility**, relative to `C ∪ Ax`: `◇P` for every sentence `P` consistent with the
theory. -/
def possibility (Ax : AxiomSet Sig) : AxiomSet Sig :=
  fun a => ∃ p : Sentence Sig, Consistent (Ax ∪ single p) ∧ a = Term.dia p

/-- The **maximalization** of a theory: its axioms together with every closed distinctness
claim consistent with it (Classicism, §"Finer-grained strengthenings"). The paper's
`Max T` is the theory these generate — everything derivable from them — which here is
`Theorem (C.axioms ∪ max Ax)`; as an axiom set it is the generators. **Maximalist
Classicism** is `max empty`. -/
def max (Ax : AxiomSet Sig) : AxiomSet Sig := Ax ∪ distinctness Ax

theorem subset_max (Ax : AxiomSet Sig) : Ax ⊆ max Ax := subset_union_left _ _

theorem distinctness_subset_max (Ax : AxiomSet Sig) : distinctness Ax ⊆ max Ax :=
  subset_union_right _ _

/-- Maximalist Classicism. -/
def maximalist : AxiomSet Sig := max empty

end AxiomSet

end Classicism.Meta
