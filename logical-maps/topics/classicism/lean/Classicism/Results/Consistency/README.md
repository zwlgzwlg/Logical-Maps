# Consistency facts from the models

What the models show about the object language: that a schema is consistent with `C`, or
that one schema does not entail another. The side conditions of Distinctness and
Possibility ("not a theorem of `C`", "consistent with `C`") and the incompatibilities in
`../SentenceSchemas/` rest on these; so do the map's non-entailments that the models
witness.

| file | contents |
| --- | --- |
| `Consistency.lean` | The facts the side conditions need, from three models: `Prop` (the full Henkin model on `e`) makes the Fregean Axiom, `□FA` and No Contingency for any signature consistent; the M-set models make `¬ND_t`, `¬BF_t`, `¬FA`, `¬□FA` and `¬`Tractarianism at `t` consistent (the last through the certified record that Tractarianism implies BF), and `□ND`, `□BF` at every type consistent with `¬FA`; the permutation model of Appendix D makes `¬`Actuality, `¬`Atomicity (`t`) and `¬`Boolean Completeness (`e → t`) consistent with `□ND`, `□BF` and Atomlessness; Parts 2 to 8 give Proposition D.5 row by row, Boolean Completeness column included; the two-object model after Part 8 makes `¬□BF_e` consistent with `BF` at every type, so `BF` does not entail `□BF`. |
| `ConsistencyPointed.lean` | The packages of the eight monoid models with a point adjoined (Appendix D, after Part 8): in each, `ND_e` and Boolean Completeness contingently false, Atomlessness false, `◇(□ND_e ∧ Atomicity)`, and `BF`, Actuality, Atomicity at `t` each necessary or contingently false as the part has them. |

## The map's records covered

| record | theorem |
| --- | --- |
| `BF` does not entail `□BF` (Appendix D, after Part 8) | `ContingentBarcan.bf_not_entails_box_bf` |
| consistency of `no-contingency-signature-r` (its notes) | `noContingency_consistent` |

## What the results depend on

The consistency facts from `Prop` rest on `Classicism.e` and `e_exists` — the Henkin
model on `e` needs an individual — and on `Classical.choice`; those from the M-set models
on `Classical.choice` alone (the full models are noncomputable). `#print axioms` on any
theorem reports which.
