# Results about the schemas over sentences

The map's principles that are schemas over *sentences* — No Pure Contingency, No
Contingency and B for a signature, Distinctness, Possibility, Maximalist Classicism — are
axiom sets of the metalogical layer (`Syntax/SentenceSchemas.lean`), and the side
conditions of Distinctness and Possibility, "not a theorem of `C`", "consistent with
`C`", are met by exhibiting a model. This folder holds the map's results about them: what
they entail, what they exclude, and the consistency facts from the models that the
exclusions rest on. It is the first use of the semantics to prove arrows of the map.

Every theorem is over any signature `Sig` where it can be — the pure and the signature
versions of a record are then one theorem — and at `Signature.pure`, where the map's
type-indexed principles live as `P.schema`, where a principle is involved. A certified
lemma of the shallow layer is carried into a signature by `Term.ofPure`
(`Syntax/Pure.lean`), and instantiated at the sentences of the proof by `allEβ` and
`allE₂β`.

| file | contents |
| --- | --- |
| `Consistency.lean` | The facts the side conditions need, from three models: `Prop` (the full Henkin model on `e`) makes the Fregean Axiom, `□FA` and No Contingency for any signature consistent; the M-set models make `¬ND_t`, `¬BF_t`, `¬FA`, `¬□FA` and `¬`Tractarianism at `t` consistent (the last through the certified record that Tractarianism implies BF), and `□ND`, `□BF` at every type consistent with `¬FA`; the permutation model of Appendix D makes `¬`Actuality and `¬`Atomicity (`t`) consistent with `□ND`, `□BF` and Atomlessness. |
| `PossibilityDistinctness.lean` | Distinctness and Possibility are equivalent, relative to any theory over any signature; `Max T` entails both. The one object-level step, `◇(x ≠ y) → x ≠ y`, is a shallow lemma certified once. |
| `Contingency.lean` | No Pure Contingency necessitates every schema of pure sentences, `NPC ∪ Ax ⟹ Ax.box` — the map's twenty `no-pure-contingency-and-X-imply-necessary-X` records as one theorem; the arrows among No Contingency, No Pure Contingency, B for the signature and B for pure sentences; B and the Fregean Axiom as sources. |
| `Incompatibilities.lean` | Possibility, Distinctness and `Max T` refute the necessitation of anything refutable in a model (`possibility_box_inconsistent`); Maximalist Classicism against `ND`; Possibility against No Pure Contingency and against B for pure sentences. |

## The map's records covered

| record | theorem |
| --- | --- |
| `distinctness-schema-r-implies-possibility-schema-r` | `distinctness_entails_possibility` (at `Signature.pure`, `empty`) |
| `possibility-schema-r-implies-distinctness-schema-r` | `possibility_entails_distinctness` |
| `distinctness-signature-r-implies-possibility-signature-r` | `distinctness_entails_possibility` (any `Sig`) |
| `possibility-signature-r-implies-distinctness-signature-r` | `possibility_entails_distinctness` |
| `no-pure-contingency-and-X-imply-necessary-X` (twenty records) | `npc_union_entails_box_pure`; named: `npc_barcanT_entails_necBarcanT`, `npc_ndT_entails_necNdT`, `npc_barcan_entails_box`, `npc_nd_entails_box`, `npc_fregean_entails_box`, `npc_actuality_entails_necActuality`, `npc_booleanCompleteness_entails_box`, `npc_atomicity_entails_box` |
| `no-contingency-signature-r-implies-no-pure-contingency-r` | `noContingency_entails_npc` |
| `no-contingency-signature-r-implies-signature-b-r` | `noContingency_entails_signatureB` |
| `no-pure-contingency-r-implies-pure-b-r` | `npc_entails_pureB` |
| `signature-b-r-implies-pure-b-r` | `signatureB_entails_pureB` |
| `modal-b-implies-signature-b-r` | `modalB_entails_signatureB` |
| `fregean-axiom-implies-no-contingency-signature-r` | `fregean_entails_noContingency` |
| `fregean-axiom-implies-no-pure-contingency-r` | `fregean_entails_npc` |
| `possibility-and-necessary-barcan-t-incompatible` | `possibility_necBarcanT_inconsistent` |
| `possibility-and-no-pure-contingency-incompatible` | `possibility_schema_npc_inconsistent` |
| `pure-b-and-pure-possibility-incompatible` | `possibility_pureB_inconsistent` |
| `maximalist-distinctness-incompatible-with-nd` | `maximalist_nd_inconsistent` (through `ND_t`) |
| `maximalist-distinctness-incompatible-with-necessary-barcan-r` | `maximalist_necBarcan_inconsistent` (through `□BF_t`) |
| `maximalist-distinctness-incompatible-with-necessary-tractarianism-r` | `maximalist_necTractarianism_inconsistent` (through `t`) |
| `maximalist-distinctness-incompatible-with-necessary-actuality` | `maximalist_necActuality_inconsistent` (the permutation model) |
| `maximalist-distinctness-incompatible-with-necessary-atomicity-r` | `maximalist_necAtomicity_inconsistent` (through `t`, the permutation model) |
| consistency of `no-contingency-signature-r` (its notes) | `noContingency_consistent` |

The necessitation of a principle is `AxiomSet.box P.schema`; the two boxed principles the
shallow layer states, `□BF_t` and `□ND_t`, are the schemas `P.NecBarcanT.schema` and
`P.NecNecessityOfDistinctnessT.schema`, and the theorems are stated for them where the
record is about them.

## Not yet here, and why

- **Cross-signature arrows**: `possibility-signature-r-implies-possibility-schema-r` and
  `distinctness-signature-r-implies-distinctness-schema-r` need the conservativity of
  `C(Σ)` over `C` for pure sentences, which the map proves through completeness. The
  direction this folder has, `ofPure`, is the other one. A syntactic proof would replace
  the constants of a derivation by fresh variables and discharge them by Existence.
- **Principles not in the shallow layer**: Witnessed Possibility and its kin (substitution
  of constants for variables), Possibility+, Strong Possibility (`◇_≠`), Separated
  Structure, Independence, Modal Freedom, Logical Necessity, the Infinity principles, the
  Necessity of Arithmetic. (Actuality, Boolean Completeness, Atomlessness and Plenitude
  are now in `Principles.lean`, with their shallow records in `Results/Records.lean`.)
- **Models not yet built**: the incompatibilities of Possibility with `□`Strong Leibniz
  (`t`) and `□`Relational Choice need the coalesced sums and a Henkin model without
  choice; with Countable Boolean Completeness, Gödel. The maximalist incompatibilities with
  `□`Actuality, `□`Atomicity, `□`Boolean Completeness, `□`Functionality and Rigid
  Comprehension need models refuting those principles, which the two M-set models do not
  (every proposition of a finite full M-set model has an atom below it); the ideally full
  models of Appendix D are where they come from, and the first of them
  (`Models/Permutations.lean`) supplies `□`Actuality and `□`Atomicity; `□`Boolean
  Completeness waits on Proposition 2.5 or a direct argument, `□`Functionality and Rigid
  Comprehension on further models.
- **`c5-and-atomicity(-t)-imply-no-pure-contingency`**: the automorphism exchanging two
  atoms, extended by conjugation to every type, is a substantial metalogical proof by
  induction on terms; a candidate for the next experiment of the Atomicity kind.

## What the results depend on

The entailments rest on `propext` and `Quot.sound`, like every certified derivation. The
consistency facts from `Prop` rest also on `Classicism.e` and `e_exists` — the Henkin
model on `e` needs an individual — and on `Classical.choice`; those from the M-set models
on `Classical.choice` alone (the full models are noncomputable). `#print axioms` on any
theorem reports which.
