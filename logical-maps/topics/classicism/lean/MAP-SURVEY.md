# Survey of the Logical Map results by kind of proof

Made 28 September 2026 from `ciandorr/Logical-Maps` at commit 7c928c4 ("first trawl"), which had 230 Classicism results; refreshed 1 October against `zwlgzwlg/Logical-Maps` at commit 8edffb3 (30 September), which has 270 (264 proved, 6 conjectured). Each result was read (premises, conclusion, recorded proof) and put in one of four classes. The judgement is about what formalizing the recorded proof would need, not about how hard the mathematics is.

| class | count | what it means |
| --- | --- | --- |
| Per-type routine | 139 | The object-level proof is uniform in the type parameters (pointwise reasoning at a relational type goes through the `Rel`/`Pointwise` classes), so each conclusion instance follows from finitely many premise instances. Includes specializations to `t`, stripping a box with T, and boxing a proved implication with necessitation, K and 4. Lifting is routine: a shallow theorem certified as an entailment. |
| Per-instance routine over sentences | 52 | The principles are sentence schemas, over closed (pure or Σ-) sentences with only syntactic side conditions (purity, closedness, fresh constants). Each instance has a short object-level proof; lifting is checking that the side conditions carry over. `npc_union_entails_box` in `Results/SentenceSchemas/Contingency.lean` does the "No Pure Contingency and X imply □X" results at once (twenty-four). |
| Sweet spot | 47 | A real shallow core plus a real metalogical step: an induction on the arity of a relational type (tuple haecceities, BF one argument at a time, a pointwise meet or join over a property), an induction on n for a schema indexed by numbers, an induction over arithmetical formulas, or reasoning about theoremhood, consistency or substitution of constants in the side conditions. |
| Metalogic-dominated | 26 | The work is a model, soundness or completeness, conservativity of C(Σ) over C, or Gödel incompleteness; the object-level part is a line or two. |
| Conjectured | 6 | No proof recorded. |

## Lean coverage (1 October)

Since 2 October each result counted as proved has a certificate in `Classicism/Map.lean`: a
theorem named by its id whose type is the statement the map's own generator writes for it
(`map/README.md`). The 202 certificates agree with the table below; `map/index.json` gives,
for each, the file and lines of its proof.

A record theorem in `Results/Records.lean` named exactly by a map id proves the map's claim, and its certificate is the entailment between the map's schemas. One named by a map id plus `_at_t` proves only the instances at type `t` (or with output `t`); its certificate is from the map's premise schemas to those instances. Where a full version exists too, the `_at_t` one is the instance at `t` that other proofs at `t` cite. A record with a Ty-parameter is proved at every list of types too, by its list form (`foo.listEntails`, the vectorized derivation); where the map's principle is over argument tuples, as Actual Profile is, or the record is proved at `σ → t` for a principle over relational types, that list form is the map's claim (`Results/Lists.lean`, `Results/Arity.lean`). `classicism_implies_existence_r_at_e` and `_relational` together cover their record, composed in `Results/Arity.lean`. Results proved by the metalogical theorems of `Results/SentenceSchemas/` are counted as proved too: those whose docstrings name the record, and the twenty-four "No Pure Contingency and X imply □X" results, all instances of `npc_union_entails_box`.

| class | results | proved in Lean | in part only | not yet |
| --- | --- | --- | --- | --- |
| Per-type routine | 139 | 130 | 0 | 9 |
| Per-instance routine over sentences | 52 | 31 | 0 | 21 |
| Sweet spot | 47 | 32 | 0 | 15 |
| Metalogic-dominated | 26 | 9 | 0 | 17 |
| Conjectured | 6 | 0 | 0 | 6 |
| total | 270 | 202 | 0 | 68 |

## Sweet spot (47)

- `actuality-and-bf-imply-inextensible-comprehension` — **Lean: at every arity, `Results/Arity.lean`**
- `actuality-implies-actual-profile-r` — **Lean: full, its list form**
- `atomicity-t-and-bf-imply-atomicity` — **Lean: at every arity, `Results/Arity.lean`**
- `atomlessness-implies-infinity-t`
- `axiom-of-infinity-e-implies-infinity-e`
- `axiom-of-infinity-t-implies-infinity-t`
- `boolean-completeness-r-implies-weakly-inextensible-comprehension-r` — **Lean: at every arity, `Results/Arity.lean`**
- `c5-and-actuality-imply-completeness` — **Lean: at every arity, `Results/Arity.lean`**
- `c5-and-actuality-imply-rigid-comprehension` — **Lean: at every arity, `Results/Arity.lean`**
- `c5-and-atomicity-imply-necessary-atomicity` — **Lean: at every arity, `Results/Arity.lean`**
- `c5-and-atomicity-imply-necessary-completeness` — **Lean: at every arity, `Results/Arity.lean`**
- `c5-and-atomicity-imply-necessary-plenitude` — **Lean: at every arity, `Results/Arity.lean`**
- `c5-and-atomicity-imply-necessary-rigid-comprehension` — **Lean: at every arity, `Results/Arity.lean`**
- `c5-and-atomicity-imply-no-pure-contingency`
- `c5-and-atomicity-t-imply-no-pure-contingency`
- `c5-and-completeness-imply-plenitude` — **Lean: at every arity, `Results/Arity.lean`**
- `c5-and-necessary-actuality-imply-atomicity` — **Lean: at every arity, `Results/Arity.lean`**
- `c5-and-necessary-completeness-imply-atomicity` — **Lean: at every arity, `Results/Arity.lean`**
- `classicism-implies-modalized-plenitude-r` — **Lean: at every arity, `Results/Arity.lean`**
- `completeness-and-actuality-imply-weak-rigid-comprehension` — **Lean: at every arity, `Results/Arity.lean`**
- `countable-boolean-completeness-implies-necessity-of-arithmetic`
- `distinctness-schema-r-implies-possibility-schema-r` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `distinctness-signature-r-implies-possibility-signature-r` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `distinctness-signature-r-implies-separated-structure-r`
- `extensionality-r-implies-atomicity-r` — **Lean: at every arity, `Results/Arity.lean`**
- `extensionality-r-implies-boolean-completeness-r` — **Lean: at every arity, `Results/Arity.lean`**
- `extensionality-r-implies-plenitude-r` — **Lean: at every arity, `Results/Arity.lean`**
- `gallin-comprehension-and-bf-imply-rigid-comprehension` — **Lean: at every arity, `Results/Arity.lean`**
- `gallin-comprehension-and-bf-imply-weak-rigid-comprehension` — **Lean: at every arity, `Results/Arity.lean`**
- `logical-necessity-r-implies-separated-structure-r`
- `necessary-bf-and-actuality-imply-inextensible-comprehension` — **Lean: at every arity, `Results/Arity.lean`**
- `necessary-gallin-comprehension-implies-necessary-rigid-comprehension` — **Lean: at every arity, `Results/Arity.lean`**
- `necessary-plenitude-r-implies-atomicity-r` — **Lean: at every arity, `Results/Arity.lean`**
- `necessary-plenitude-r-implies-necessary-atomicity-r` — **Lean: at every arity, `Results/Arity.lean`**
- `necessary-strong-leibniz-t-and-necessary-bf-imply-necessary-strong-leibniz` — **Lean: at every arity, `Results/Arity.lean`**
- `possibility-schema-r-implies-distinctness-schema-r` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `possibility-signature-r-implies-distinctness-signature-r` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `possibly-witnessed-possibility-r-implies-separated-structure-r`
- `pure-distinctness-and-separated-structure-imply-signature-distinctness`
- `rigid-comprehension-and-nd-imply-plenitude` — **Lean: at every arity, `Results/Arity.lean`**
- `rigid-comprehension-r-implies-boolean-completeness-r` — **Lean: at every arity, `Results/Arity.lean`**
- `separated-structure-r-implies-general-separated-structure-r`
- `separated-structure-r-implies-independence-signature-r`
- `separated-structure-r-implies-possibly-witnessed-possibility-r`
- `strong-possibility-r-implies-possibility-schema-r`
- `strong-possibility-signature-r-implies-possibility-signature-r`
- `weak-rigid-comprehension-r-implies-boolean-completeness-r` — **Lean: at every arity, `Results/Arity.lean`**

## Metalogic-dominated (26)

- `distinctness-signature-r-implies-distinctness-schema-r`
- `maximalist-distinctness-incompatible-with-nd` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `maximalist-distinctness-incompatible-with-necessary-actuality` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `maximalist-distinctness-incompatible-with-necessary-atomicity-r` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `maximalist-distinctness-incompatible-with-necessary-barcan-r` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `maximalist-distinctness-incompatible-with-necessary-boolean-completeness-r` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `maximalist-distinctness-incompatible-with-necessary-functionality-r`
- `maximalist-distinctness-incompatible-with-necessary-rigid-comprehension-r`
- `maximalist-distinctness-incompatible-with-necessary-tractarianism-r` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `maximalist-distinctness-incompatible-with-rigid-comprehension`
- `possibility-and-countable-boolean-completeness-incompatible`
- `possibility-and-necessary-barcan-t-incompatible` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `possibility-and-necessary-relational-choice-incompatible`
- `possibility-and-necessary-strong-leibniz-t-incompatible`
- `possibility-and-necessity-of-arithmetic-incompatible`
- `possibility-and-no-pure-contingency-incompatible` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `possibility-plus-signature-r-implies-possibility-plus-r`
- `possibility-schema-r-implies-possible-infinity-e`
- `possibility-schema-r-implies-possible-infinity-t`
- `possibility-signature-r-implies-possibility-schema-r`
- `possibility-signature-r-implies-witnessed-possibility-r`
- `pure-b-and-pure-possibility-incompatible` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `pure-distinctness-implies-infinity-t`
- `pure-possibility-implies-axiom-of-infinity-t`
- `strong-possibility-and-distinctness-preserving-collapse-incompatible`
- `strong-possibility-signature-and-distinctness-preserving-collapse-incompatible`

## Per-instance routine over sentences (52)

- `converse-witnessed-possibility-r-implies-no-pure-contingency-r`
- `fregean-axiom-implies-no-contingency-signature-r` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `fregean-axiom-implies-no-pure-contingency-r` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `general-separated-structure-r-implies-separated-structure-r`
- `logical-necessity-r-implies-modal-freedom-signature-r`
- `logical-necessity-r-implies-no-pure-contingency-r`
- `logical-necessity-r-implies-witnessed-possibility-r`
- `modal-b-implies-pure-b-r`
- `modal-b-implies-signature-b-r` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `modal-freedom-signature-r-implies-no-pure-contingency-r`
- `no-contingency-signature-incompatible-with-witnessed-possibility`
- `no-contingency-signature-r-implies-modal-freedom-signature-r`
- `no-contingency-signature-r-implies-no-pure-contingency-r` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-contingency-signature-r-implies-signature-b-r` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-pure-contingency-and-actuality-imply-necessary-actuality` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-pure-contingency-and-atomicity-imply-necessary-atomicity` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-pure-contingency-and-b-imply-necessary-b` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-pure-contingency-and-bf-imply-necessary-bf` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-pure-contingency-and-bf-t-imply-necessary-bf-t` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-pure-contingency-and-completeness-imply-necessary-completeness` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-pure-contingency-and-extensionality-imply-necessary-extensionality` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-pure-contingency-and-five-imply-necessary-five` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-pure-contingency-and-fregean-imply-necessary-fregean` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-pure-contingency-and-functional-choice-imply-necessary-functional-choice` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-pure-contingency-and-functionality-imply-necessary-functionality` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-pure-contingency-and-gallin-comprehension-imply-necessary-gallin-comprehension` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-pure-contingency-and-nd-imply-necessary-nd` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-pure-contingency-and-nd-t-imply-necessary-nd-t` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-pure-contingency-and-plenitude-imply-necessary-plenitude` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-pure-contingency-and-relational-choice-imply-necessaryelational-choice` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-pure-contingency-and-rigid-comprehension-imply-necessary-rigid-comprehension` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-pure-contingency-and-strong-leibniz-imply-necessary-strong-leibniz` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-pure-contingency-and-strong-leibniz-t-imply-necessary-strong-leibniz-t` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-pure-contingency-and-tractarianism-imply-necessary-tractarianism` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-pure-contingency-and-transversal-choice-imply-necessary-transversal-choice` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-pure-contingency-and-transversal-imply-necessary-transversal` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-pure-contingency-and-vicinity-imply-necessary-vicinity` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-pure-contingency-and-weakly-inextensible-comprehension-imply-necessary-weakly-inextensible-comprehension` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `no-pure-contingency-implies-necessity-of-arithmetic`
- `no-pure-contingency-r-implies-converse-witnessed-possibility-r`
- `no-pure-contingency-r-implies-pure-b-r` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `possibility-plus-r-implies-possibility-schema-r`
- `possibility-plus-signature-r-implies-possibility-signature-r`
- `possible-infinity-e-and-no-pure-contingency-imply-axiom-of-infinity-e`
- `possible-infinity-t-and-no-pure-contingency-imply-axiom-of-infinity-t`
- `possibly-witnessed-possibility-r-implies-witnessed-possibility-r`
- `separated-structure-incompatible-with-nd`
- `signature-b-and-witnessed-possibility-incompatible`
- `signature-b-r-implies-pure-b-r` — **Lean: metalogical theorem in `Results/SentenceSchemas/`**
- `witnessed-possibility-and-no-pure-contingency-imply-logical-necessity`
- `witnessed-possibility-and-npc-imply-possibly-witnessed-possibility`
- `witnessed-possibility-incompatible-with-nd`

## Per-type routine (139)

- `actual-profile-r-implies-actuality` — **Lean: full, `Results/Arity.lean`**
- `actuality-and-distinctness-preserving-collapse-imply-inextensible-comprehension` — **Lean: at every arity, `Results/Arity.lean`**
- `actuality-implies-persistent-comprehension-r` — **Lean: at every arity, `Results/Arity.lean`**
- `actuality-implies-transversal` — **Lean: full**
- `actuality-implies-vicinity` — **Lean: full**
- `actuality-implies-weakly-inextensible-comprehension-r` — **Lean: at every arity, `Results/Arity.lean`**
- `actuality-incompatible-with-atomlessness` — **Lean: full**
- `atomicity-and-bf-imply-necessary-actuality` — **Lean: full**
- `atomicity-and-bf-imply-strong-leibniz` — **Lean: at every arity, `Results/Arity.lean`**
- `atomicity-r-implies-atomicity-t` — **Lean: full**
- `atomicity-t-and-bf-imply-necessary-actuality` — **Lean: full**
- `atomicity-t-and-bf-t-imply-strong-leibniz-t` — **Lean: full**
- `atomicity-t-incompatible-with-atomlessness` — **Lean: full**
- `atomlessness-implies-axiom-of-infinity-t`
- `axiom-of-infinity-e-implies-possible-infinity-e`
- `axiom-of-infinity-t-implies-possible-infinity-t`
- `barcan-r-implies-barcan-t` — **Lean: full**
- `barcan-r-implies-functionality-r` — **Lean: full**
- `boolean-completeness-r-implies-boolean-completeness-t` — **Lean: full**
- `boolean-completeness-r-implies-countable-boolean-completeness-r`
- `c5-and-completeness-imply-actuality` — **Lean: full**
- `c5-and-necessary-rigid-comprehension-imply-necessary-gallin-comprehension` — **Lean: at every arity, `Results/Arity.lean`**
- `c5-and-persistent-comprehension-imply-gallin` — **Lean: at every arity, `Results/Arity.lean`**
- `classicism-implies-broad-necessitism-r` — **Lean: full**
- `classicism-implies-converse-barcan-r` — **Lean: full**
- `classicism-implies-existence-r` — **Lean: full, `Results/Arity.lean`**
- `classicism-implies-identity-necessary-r` — **Lean: full**
- `classicism-implies-intensionality-r` — **Lean: full**
- `classicism-implies-modal-four` — **Lean: full**
- `classicism-implies-modal-k` — **Lean: full**
- `classicism-implies-modal-t` — **Lean: full**
- `classicism-implies-modalized-fregean` — **Lean: full**
- `classicism-implies-modalized-functionality-r` — **Lean: full**
- `classicism-implies-ordinary-comprehension-r`
- `distinctness-necessary-r-implies-distinctness-necessary-t` — **Lean: full**
- `distinctness-necessary-t-implies-modal-five` — **Lean: full**
- `distinctness-necessary-t-implies-vicinity` — **Lean: full**
- `distinctness-preserving-collapse-and-nd-imply-fregean-axiom` — **Lean: full**
- `extensionality-r-implies-actuality` — **Lean: full**
- `extensionality-r-implies-fregean-axiom` — **Lean: full**
- `extensionality-r-implies-functionality-r` — **Lean: full**
- `extensionality-r-implies-necessary-extensionality-r` — **Lean: full**
- `extensionality-r-implies-rigid-comprehension-r` — **Lean: at every arity, `Results/Arity.lean`**
- `fregean-axiom-implies-distinctness-preserving-collapse` — **Lean: full**
- `fregean-axiom-implies-extensionality-r` — **Lean: full**
- `fregean-axiom-implies-necessary-distinctness-necessary-r` — **Lean: full**
- `fregean-axiom-implies-necessary-fregean-axiom` — **Lean: full**
- `fregean-incompatible-with-infinity-t`
- `functional-choice-r-implies-plenitude-r` — **Lean: full**
- `functional-choice-r-implies-relational-choice-r` — **Lean: full**
- `functionality-r-implies-tractarianism-r` — **Lean: full**
- `gallin-comprehension-implies-nd` — **Lean: full**
- `inextensible-comprehension-r-implies-weakly-inextensible-comprehension-r` — **Lean: full**
- `modal-b-implies-distinctness-necessary-r` — **Lean: full**
- `modal-five-implies-modal-b` — **Lean: full**
- `nd-and-bf-imply-necessary-nd` — **Lean: full**
- `necessary-actuality-implies-actuality` — **Lean: full**
- `necessary-actuality-implies-necessary-transversal` — **Lean: full**
- `necessary-actuality-implies-necessary-vicinity` — **Lean: full**
- `necessary-actuality-implies-necessary-weakly-inextensible-comprehension-r` — **Lean: at every arity, `Results/Arity.lean`**
- `necessary-atomicity-and-necessary-bf-imply-necessary-strong-leibniz` — **Lean: at every arity, `Results/Arity.lean`**
- `necessary-atomicity-and-necessary-bf-t-imply-necessary-strong-leibniz-t` — **Lean: full**
- `necessary-atomicity-r-implies-atomicity-r` — **Lean: full**
- `necessary-barcan-r-implies-barcan-r` — **Lean: full**
- `necessary-barcan-r-implies-necessary-barcan-t` — **Lean: full**
- `necessary-barcan-r-implies-necessary-functionality-r` — **Lean: full**
- `necessary-barcan-t-implies-barcan-t` — **Lean: full**
- `necessary-boolean-completeness-r-implies-boolean-completeness-r` — **Lean: full**
- `necessary-distinctness-necessary-r-implies-distinctness-necessary-r` — **Lean: full**
- `necessary-distinctness-necessary-r-implies-necessary-barcan-r` — **Lean: full**
- `necessary-distinctness-necessary-r-implies-necessary-distinctness-necessary-t` — **Lean: full**
- `necessary-distinctness-necessary-r-implies-necessary-modal-five` — **Lean: full**
- `necessary-distinctness-necessary-t-implies-distinctness-necessary-t` — **Lean: full**
- `necessary-distinctness-necessary-t-implies-necessary-distinctness-necessary-r` — **Lean: full**
- `necessary-distinctness-necessary-t-implies-necessary-vicinity` — **Lean: full**
- `necessary-extensionality-r-implies-extensionality-r` — **Lean: full**
- `necessary-fregean-axiom-implies-fregean-axiom` — **Lean: full**
- `necessary-functional-choice-r-implies-functional-choice-r` — **Lean: full**
- `necessary-functional-choice-r-implies-necessary-plenitude-r` — **Lean: full**
- `necessary-functional-choice-r-implies-necessary-relational-choice-r` — **Lean: full**
- `necessary-functionality-r-implies-functionality-r` — **Lean: full**
- `necessary-functionality-r-implies-necessary-tractarianism-r` — **Lean: full**
- `necessary-gallin-comprehension-implies-gallin-comprehension` — **Lean: full**
- `necessary-gallin-comprehension-implies-necessary-nd` — **Lean: full**
- `necessary-modal-b-implies-modal-b` — **Lean: full**
- `necessary-modal-b-implies-necessary-distinctness-necessary-r` — **Lean: full**
- `necessary-modal-five-implies-modal-five` — **Lean: full**
- `necessary-modal-five-implies-necessary-modal-b` — **Lean: full**
- `necessary-nd-implies-bf` — **Lean: full**
- `necessary-plenitude-r-implies-necessary-actuality` — **Lean: full**
- `necessary-plenitude-r-implies-necessary-distinctness-necessary-r` — **Lean: full**
- `necessary-plenitude-r-implies-plenitude-r` — **Lean: full**
- `necessary-relational-choice-and-necessary-plenitude-imply-necessary-functional-choice` — **Lean: full**
- `necessary-relational-choice-r-implies-relational-choice-r` — **Lean: full**
- `necessary-rigid-comprehension-r-implies-necessary-actuality` — **Lean: full**
- `necessary-rigid-comprehension-r-implies-necessary-boolean-completeness-r` — **Lean: at every arity, `Results/Arity.lean`**
- `necessary-rigid-comprehension-r-implies-rigid-comprehension-r` — **Lean: full**
- `necessary-strong-leibniz-and-rigid-comprehension-imply-necessary-bf-t`
- `necessary-strong-leibniz-implies-necessary-atomicity` — **Lean: at every arity, `Results/Arity.lean`**
- `necessary-strong-leibniz-r-implies-necessary-strong-leibniz-t` — **Lean: full**
- `necessary-strong-leibniz-r-implies-strong-leibniz-r` — **Lean: full**
- `necessary-strong-leibniz-t-implies-strong-leibniz-t` — **Lean: full**
- `necessary-tractarianism-r-implies-necessary-barcan-r` — **Lean: full**
- `necessary-tractarianism-r-implies-tractarianism-r` — **Lean: full**
- `necessary-transversal-and-necessary-relational-choice-imply-necessary-transversal-choice` — **Lean: full**
- `necessary-transversal-choice-r-implies-necessary-relational-choice-r` — **Lean: full**
- `necessary-transversal-choice-r-implies-necessary-transversal-r` — **Lean: full**
- `necessary-transversal-choice-r-implies-transversal-choice-r` — **Lean: full**
- `necessary-transversal-r-implies-transversal-r` — **Lean: full**
- `necessary-vicinity-and-necessary-weakly-inextensible-comprehension-imply-necessary-actuality` — **Lean: full**
- `necessary-vicinity-implies-vicinity` — **Lean: full**
- `necessary-weakly-inextensible-comprehension-r-implies-weakly-inextensible-comprehension-r` — **Lean: full**
- `persistent-comprehension-r-implies-actuality` — **Lean: full**
- `plenitude-r-implies-actuality` — **Lean: full**
- `plenitude-r-implies-distinctness-necessary-r` — **Lean: full**
- `possible-infinity-e-and-bf-imply-axiom-of-infinity-e`
- `possible-infinity-t-and-bf-t-imply-axiom-of-infinity-t`
- `relational-choice-and-extensionality-imply-transversal-choice` — **Lean: full**
- `relational-choice-and-plenitude-imply-functional-choice-r` — **Lean: full**
- `relational-choice-and-very-weak-rigid-comprehension-imply-transversal-choice` — **Lean: full**
- `rigid-comprehension-and-bf-imply-necessary-bf` — **Lean: full**
- `rigid-comprehension-r-implies-actuality` — **Lean: full**
- `rigid-comprehension-r-implies-inextensible-comprehension-r` — **Lean: full**
- `rigid-comprehension-r-implies-persistent-comprehension-r` — **Lean: full**
- `rigid-comprehension-r-implies-weak-rigid-comprehension-r` — **Lean: full**
- `strong-leibniz-r-implies-atomicity-r` — **Lean: at every arity, `Results/Arity.lean`**
- `strong-leibniz-r-implies-strong-leibniz-t` — **Lean: full**
- `strong-leibniz-t-implies-atomicity-t` — **Lean: full**
- `strong-leibniz-t-implies-necessary-actuality` — **Lean: full**
- `tractarianism-r-implies-barcan-r` — **Lean: full**
- `transversal-and-relational-choice-imply-transversal-choice` — **Lean: full**
- `transversal-choice-r-implies-relational-choice-r` — **Lean: full**
- `transversal-choice-r-implies-transversal-r` — **Lean: full**
- `very-weak-rigid-comprehension-r-implies-weak-rigid-comprehension-r` — **Lean: at every arity, `Results/Arity.lean`**
- `vicinity-and-distinctness-preserving-collapse-imply-actuality` — **Lean: full**
- `vicinity-and-weakly-inextensible-comprehension-imply-actuality` — **Lean: full**
- `weak-rigid-comprehension-r-implies-persistent-comprehension-r` — **Lean: full**
- `weak-rigid-comprehension-r-implies-very-weak-rigid-comprehension-r` — **Lean: full**
- `weak-rigid-comprehension-r-implies-weakly-inextensible-comprehension-r` — **Lean: full**

## Conjectured (6)

- `necessary-atomicity-completeness-bf-imply-rigid-comprehension` — refuted by a countermodel (Cian, 1 October); the proof in n. 42 has two gaps (`HANDOFF.md`, §4)
- `possible-infinity-e-implies-axiom-of-infinity-e`
- `possible-infinity-t-implies-axiom-of-infinity-t`
- `relational-choice-and-boolean-completeness-imply-transversal-choice`
- `relational-choice-r-implies-transversal-choice-r`
- `strong-possibility-signature-r-implies-strong-possibility-r`

## Lean records that are not map results

Record-shaped theorems in `Results/Records.lean` with no map counterpart: consequences at type `t`, or with the premise `□ND` at `t` alone where the map uses `□ND` at all types, which the map could add as records.

- `very_weak_rigid_comprehension_implies_boolean_completeness_t`
- `necessary_distinctness_necessary_t_implies_distinctness_necessary_r`
- `distinctness_necessary_t_and_barcan_t_imply_necessary_distinctness_necessary_t`
- `atomicity_t_and_necessary_distinctness_necessary_t_imply_necessary_actuality`
- `necessary_actuality_and_necessary_distinctness_necessary_t_imply_necessary_boolean_completeness_r`
- `necessary_boolean_completeness_r_and_necessary_distinctness_necessary_t_imply_necessary_actuality`
- `necessary_rigid_comprehension_r_and_necessary_distinctness_necessary_t_imply_atomicity_t`
- `strong_leibniz_t_and_bf_imply_strong_leibniz`
