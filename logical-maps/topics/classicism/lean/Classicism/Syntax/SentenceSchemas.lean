import Classicism.Syntax.Entailment

/-!
# Sentence schemas

The map's principles that are schematic in a *sentence* rather than a type: No Pure
Contingency, No Contingency and B for a signature, Distinctness, Possibility, and the
maximalization of a theory. Each is a schema (an `AxiomSet`), defined by a condition on
sentences. None is the schema of a principle — the shallow layer cannot quantify over
syntax, which was purpose one of this layer — so none can come from `#classicism_schema`,
and this module is their home, as `Certified/Schemas.lean` is the home of the principles'
schemas. The entailments of `Entailment.lean` and the model facts of `Action*.lean` apply
to them as to the others.

Two conventions. A sentence schema "for a signature `Σ`" is the schema at `Sig := Σ`; at
`Signature.pure`, where every term is pure, it is the map's "(pure)" version, so one
definition serves both. And a schema relative to a theory `T` is relative to
`C.axioms ∪ Ax`, as entailment is.

Map ids: `no-pure-contingency-r` (`npc`), `no-contingency-signature-r` (`noContingency`),
`signature-b-r` (`signatureB`), `pure-b-r` (`pureB`), `distinctness-schema-r` /
`distinctness-signature-r` (`distinctness`), `possibility-schema-r` /
`possibility-signature-r` (`possibility`). The necessitation of a schema, `Ax.box`, is
how the map's boxed principles are formed from the unboxed ones (`□BF` is
`P.Barcan.schema.box`). Not yet here: the schemas with substitution of constants for
variables (Witnessed Possibility and its kin), Possibility+, and Strong Possibility, which
needs `◇_≠`. What follows from these schemas is in `Results/SentenceSchemas/`.
-/

namespace Classicism.Meta

/-- In the pure signature every term is pure: there are no constants. -/
theorem Term.pure_of_pureSig : ∀ {Γ : Ctx} {σ : Ty} (t : Term Signature.pure Γ σ), t.pure = true
  | _, _, .var _ | _, _, .and | _, _, .or | _, _, .not | _, _, .all _ | _, _, .ex _ | _, _, .eq _
  | _, _, .constR _ | _, _, .negR _ | _, _, .andR _ | _, _, .orR _ | _, _, .coextR _
  | _, _, .boxR _ | _, _, .boxImpR _ => rfl
  | _, _, .const c => nomatch c
  | _, _, .app f a => by simp [Term.pure, pure_of_pureSig f, pure_of_pureSig a]
  | _, _, .lam b => pure_of_pureSig b

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

/-- B for the pure sentences: `P → □◇P` for every pure `P`. -/
def pureB : AxiomSet Sig :=
  fun a => ∃ p : Sentence Sig, p.pure = true ∧ a = Term.imp p (Term.box (Term.dia p))

variable {Sig}

/-- The necessitation of a schema: `□P` for each of its sentences `P`. A boxed principle
of the map says exactly that each closed instance of the base is necessary, so `□P` is
`P.schema.box`. -/
def box (Ax : AxiomSet Sig) : AxiomSet Sig := fun a => ∃ p, Ax p ∧ a = Term.box p

theorem mem_box {Ax : AxiomSet Sig} {p : Sentence Sig} (h : Ax p) : Ax.box (Term.box p) := ⟨p, h, rfl⟩

/-- A schema of pure sentences. -/
def Pure (Ax : AxiomSet Sig) : Prop := ∀ a, Ax a → a.pure = true

/-- In the pure signature every schema is pure. -/
theorem Pure.of_pureSig (Ax : AxiomSet Signature.pure) : Pure Ax := fun a _ => a.pure_of_pureSig

theorem npc_subset_noContingency : npc Sig ⊆ noContingency Sig := fun _ ⟨p, _, h⟩ => ⟨p, h⟩
theorem pureB_subset_signatureB : pureB Sig ⊆ signatureB Sig := fun _ ⟨p, _, h⟩ => ⟨p, h⟩

/-- In the pure signature, No Contingency is No Pure Contingency, and B for the signature
is B for pure sentences. -/
theorem noContingency_subset_npc : noContingency Signature.pure ⊆ npc Signature.pure :=
  fun _ ⟨p, h⟩ => ⟨p, p.pure_of_pureSig, h⟩
theorem signatureB_subset_pureB : signatureB Signature.pure ⊆ pureB Signature.pure :=
  fun _ ⟨p, h⟩ => ⟨p, p.pure_of_pureSig, h⟩

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
