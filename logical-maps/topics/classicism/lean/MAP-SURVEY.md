# Survey of the Logical Map results by kind of proof

Made 28 September 2026 from `ciandorr/Logical-Maps` at commit 7c928c4 ("first trawl"), which has 230 Classicism results (226 proved, 4 conjectured). Each result was read (premises, conclusion, recorded proof) and put in one of four classes. The judgement is about what formalizing the recorded proof would need, not about how hard the mathematics is.

| class | count | what it means |
| --- | --- | --- |
| Per-type routine | 112 | The object-level proof is uniform in the type parameters (pointwise reasoning at a relational type goes through the `Rel`/`Pointwise` classes), so each conclusion instance follows from finitely many premise instances. Includes specializations to `t`, stripping a box with T, and boxing a proved implication with necessitation, K and 4. Lifting is routine: a shallow theorem certified as an entailment. |
| Per-instance routine over sentences | 48 | The principles are schemas over closed (pure or Σ-) sentences with only syntactic side conditions (purity, closedness, fresh constants). Each instance has a short object-level proof; lifting is checking that the side conditions carry over. `npc_union_entails_box` in `Results/Schemas/Contingency.lean` does sixteen of these at once. |
| Sweet spot | 40 | A real object-level kernel plus a real metalogical step: an induction on the arity of a relational type (tuple haecceities, BF one argument at a time, a pointwise meet or join over a property), an induction on n for a schema indexed by numbers, an induction over arithmetical formulas, or reasoning about theoremhood, consistency or substitution of constants in the side conditions. |
| Metalogic-dominated | 26 | The work is a model, soundness or completeness, conservativity of C(Σ) over C, or Gödel incompleteness; the object-level part is a line or two. |
| Conjectured | 4 | No proof recorded. |

The record `atomicity-t-and-bf-imply-atomicity`, the model for the sweet spot, is not in this commit of the map.

## Sweet spot (40)

- `actuality-implies-actual-profile-r` — shallow theorem of the same name in `Results/Records.lean`
- `atomlessness-implies-infinity-t`
- `axiom-of-infinity-e-implies-infinity-e`
- `axiom-of-infinity-t-implies-infinity-t`
- `c5-and-actuality-imply-completeness`
- `c5-and-actuality-imply-rigid-comprehension`
- `c5-and-atomicity-imply-necessary-atomicity`
- `c5-and-atomicity-imply-necessary-completeness`
- `c5-and-atomicity-imply-necessary-plenitude`
- `c5-and-atomicity-imply-necessary-rigid-comprehension`
- `c5-and-completeness-imply-plenitude`
- `c5-and-necessary-actuality-imply-atomicity`
- `c5-and-necessary-completeness-imply-atomicity`
- `completeness-and-actuality-imply-weak-rigid-comprehension`
- `countable-boolean-completeness-implies-necessity-of-arithmetic`
- `distinctness-schema-r-implies-possibility-schema-r`
- `distinctness-signature-r-implies-possibility-signature-r`
- `distinctness-signature-r-implies-separated-structure-r`
- `extensionality-r-implies-atomicity-r`
- `extensionality-r-implies-boolean-completeness-r` — shallow theorem of the same name in `Results/Records.lean`
- `extensionality-r-implies-plenitude-r`
- `gallin-comprehension-and-bf-imply-rigid-comprehension`
- `gallin-comprehension-and-bf-imply-weak-rigid-comprehension`
- `logical-necessity-r-implies-separated-structure-r`
- `necessary-atomicity-completeness-bf-imply-rigid-comprehension`
- `necessary-gallin-comprehension-implies-necessary-rigid-comprehension`
- `necessary-plenitude-r-implies-atomicity-r`
- `necessary-plenitude-r-implies-necessary-atomicity-r`
- `possibility-schema-r-implies-distinctness-schema-r`
- `possibility-signature-r-implies-distinctness-signature-r`
- `possibly-witnessed-possibility-r-implies-separated-structure-r`
- `pure-distinctness-and-separated-structure-imply-signature-distinctness`
- `rigid-comprehension-and-nd-imply-plenitude`
- `rigid-comprehension-r-implies-boolean-completeness-r` — shallow theorem of the same name in `Results/Records.lean`
- `separated-structure-r-implies-general-separated-structure-r`
- `separated-structure-r-implies-independence-signature-r`
- `separated-structure-r-implies-possibly-witnessed-possibility-r`
- `strong-possibility-r-implies-possibility-schema-r`
- `strong-possibility-signature-r-implies-possibility-signature-r`
- `weak-rigid-comprehension-r-implies-boolean-completeness-r` — shallow theorem of the same name in `Results/Records.lean`

## Metalogic-dominated (26)

- `distinctness-signature-r-implies-distinctness-schema-r`
- `maximalist-distinctness-incompatible-with-nd`
- `maximalist-distinctness-incompatible-with-necessary-actuality`
- `maximalist-distinctness-incompatible-with-necessary-atomicity-r`
- `maximalist-distinctness-incompatible-with-necessary-barcan-r`
- `maximalist-distinctness-incompatible-with-necessary-boolean-completeness-r`
- `maximalist-distinctness-incompatible-with-necessary-functionality-r`
- `maximalist-distinctness-incompatible-with-necessary-rigid-comprehension-r`
- `maximalist-distinctness-incompatible-with-necessary-tractarianism-r`
- `maximalist-distinctness-incompatible-with-rigid-comprehension`
- `possibility-and-countable-boolean-completeness-incompatible`
- `possibility-and-necessary-barcan-t-incompatible`
- `possibility-and-necessary-relational-choice-incompatible`
- `possibility-and-necessary-strong-leibniz-t-incompatible`
- `possibility-and-necessity-of-arithmetic-incompatible`
- `possibility-and-no-pure-contingency-incompatible`
- `possibility-plus-signature-r-implies-possibility-plus-r`
- `possibility-schema-r-implies-possible-infinity-e`
- `possibility-schema-r-implies-possible-infinity-t`
- `possibility-signature-r-implies-possibility-schema-r`
- `possibility-signature-r-implies-witnessed-possibility-r`
- `pure-b-and-pure-possibility-incompatible`
- `pure-distinctness-implies-infinity-t`
- `pure-possibility-implies-axiom-of-infinity-t`
- `strong-possibility-and-distinctness-preserving-collapse-incompatible`
- `strong-possibility-signature-and-distinctness-preserving-collapse-incompatible`

## Per-instance routine over sentences (48)

- `converse-witnessed-possibility-r-implies-no-pure-contingency-r`
- `fregean-axiom-implies-no-contingency-signature-r`
- `fregean-axiom-implies-no-pure-contingency-r`
- `general-separated-structure-r-implies-separated-structure-r`
- `logical-necessity-r-implies-modal-freedom-signature-r`
- `logical-necessity-r-implies-no-pure-contingency-r`
- `logical-necessity-r-implies-witnessed-possibility-r`
- `modal-b-implies-pure-b-r`
- `modal-b-implies-signature-b-r`
- `modal-freedom-signature-r-implies-no-pure-contingency-r`
- `no-contingency-signature-incompatible-with-witnessed-possibility`
- `no-contingency-signature-r-implies-modal-freedom-signature-r`
- `no-contingency-signature-r-implies-no-pure-contingency-r`
- `no-contingency-signature-r-implies-signature-b-r`
- `no-pure-contingency-and-actuality-imply-necessary-actuality`
- `no-pure-contingency-and-atomicity-imply-necessary-atomicity`
- `no-pure-contingency-and-b-imply-necessary-b`
- `no-pure-contingency-and-bf-imply-necessary-bf`
- `no-pure-contingency-and-bf-t-imply-necessary-bf-t`
- `no-pure-contingency-and-completeness-imply-necessary-completeness`
- `no-pure-contingency-and-extensionality-imply-necessary-extensionality`
- `no-pure-contingency-and-five-imply-necessary-five`
- `no-pure-contingency-and-fregean-imply-necessary-fregean`
- `no-pure-contingency-and-functional-choice-imply-necessary-functional-choice`
- `no-pure-contingency-and-functionality-imply-necessary-functionality`
- `no-pure-contingency-and-gallin-comprehension-imply-necessary-gallin-comprehension`
- `no-pure-contingency-and-nd-imply-necessary-nd`
- `no-pure-contingency-and-nd-t-imply-necessary-nd-t`
- `no-pure-contingency-and-plenitude-imply-necessary-plenitude`
- `no-pure-contingency-and-relational-choice-imply-necessaryelational-choice`
- `no-pure-contingency-and-rigid-comprehension-imply-necessary-rigid-comprehension`
- `no-pure-contingency-and-strong-leibniz-imply-necessary-strong-leibniz`
- `no-pure-contingency-and-strong-leibniz-t-imply-necessary-strong-leibniz-t`
- `no-pure-contingency-and-tractarianism-imply-necessary-tractarianism`
- `no-pure-contingency-implies-necessity-of-arithmetic`
- `no-pure-contingency-r-implies-converse-witnessed-possibility-r`
- `no-pure-contingency-r-implies-pure-b-r`
- `possibility-plus-r-implies-possibility-schema-r`
- `possibility-plus-signature-r-implies-possibility-signature-r`
- `possible-infinity-e-and-no-pure-contingency-imply-axiom-of-infinity-e`
- `possible-infinity-t-and-no-pure-contingency-imply-axiom-of-infinity-t`
- `possibly-witnessed-possibility-r-implies-witnessed-possibility-r`
- `separated-structure-incompatible-with-nd`
- `signature-b-and-witnessed-possibility-incompatible`
- `signature-b-r-implies-pure-b-r`
- `witnessed-possibility-and-no-pure-contingency-imply-logical-necessity`
- `witnessed-possibility-and-npc-imply-possibly-witnessed-possibility`
- `witnessed-possibility-incompatible-with-nd`

## Per-type routine (112)

- `actual-profile-r-implies-actuality`
- `actuality-implies-inextensible-comprehension-r`
- `actuality-implies-persistent-comprehension-r` — shallow theorem of the same name in `Results/Records.lean`
- `actuality-incompatible-with-atomlessness` — shallow theorem of the same name in `Results/Records.lean`
- `atomicity-and-bf-imply-necessary-actuality` — shallow theorem of the same name in `Results/Records.lean`
- `atomicity-and-bf-imply-strong-leibniz`
- `atomicity-r-implies-atomicity-t`
- `atomicity-t-and-bf-imply-necessary-actuality` — shallow theorem of the same name in `Results/Records.lean`
- `atomicity-t-and-bf-t-imply-strong-leibniz-t`
- `atomicity-t-incompatible-with-atomlessness`
- `atomlessness-implies-axiom-of-infinity-t`
- `axiom-of-infinity-e-implies-possible-infinity-e`
- `axiom-of-infinity-t-implies-possible-infinity-t`
- `barcan-r-implies-barcan-t` — shallow theorem of the same name in `Results/Records.lean`
- `barcan-r-implies-functionality-r` — shallow theorem of the same name in `Results/Records.lean`
- `boolean-completeness-r-implies-boolean-completeness-t` — shallow theorem of the same name in `Results/Records.lean`
- `boolean-completeness-r-implies-countable-boolean-completeness-r`
- `c5-and-completeness-imply-actuality`
- `c5-and-necessary-rigid-comprehension-imply-necessary-gallin-comprehension`
- `c5-and-persistent-comprehension-imply-gallin`
- `classicism-implies-broad-necessitism-r`
- `classicism-implies-converse-barcan-r` — shallow theorem of the same name in `Results/Records.lean`
- `classicism-implies-existence-r`
- `classicism-implies-identity-necessary-r` — shallow theorem of the same name in `Results/Records.lean`
- `classicism-implies-intensionality-r` — shallow theorem of the same name in `Results/Records.lean`
- `classicism-implies-modal-four` — shallow theorem of the same name in `Results/Records.lean`
- `classicism-implies-modal-k` — shallow theorem of the same name in `Results/Records.lean`
- `classicism-implies-modal-t` — shallow theorem of the same name in `Results/Records.lean`
- `classicism-implies-modalized-fregean` — shallow theorem of the same name in `Results/Records.lean`
- `classicism-implies-modalized-functionality-r` — shallow theorem of the same name in `Results/Records.lean`
- `classicism-implies-ordinary-comprehension-r`
- `distinctness-necessary-r-implies-distinctness-necessary-t`
- `distinctness-necessary-t-implies-modal-five` — shallow theorem of the same name in `Results/Records.lean`
- `distinctness-preserving-collapse-and-nd-imply-fregean-axiom`
- `extensionality-r-implies-actuality` — shallow theorem of the same name in `Results/Records.lean`
- `extensionality-r-implies-fregean-axiom` — shallow theorem of the same name in `Results/Records.lean`
- `extensionality-r-implies-functionality-r`
- `extensionality-r-implies-necessary-extensionality-r`
- `extensionality-r-implies-rigid-comprehension-r`
- `fregean-axiom-implies-distinctness-preserving-collapse`
- `fregean-axiom-implies-extensionality-r` — shallow theorem of the same name in `Results/Records.lean`
- `fregean-axiom-implies-necessary-distinctness-necessary-r`
- `fregean-axiom-implies-necessary-fregean-axiom`
- `fregean-incompatible-with-infinity-t`
- `functional-choice-r-implies-plenitude-r` — shallow theorem of the same name in `Results/Records.lean`
- `functional-choice-r-implies-relational-choice-r` — shallow theorem of the same name in `Results/Records.lean`
- `functionality-r-implies-tractarianism-r` — shallow theorem of the same name in `Results/Records.lean`
- `gallin-comprehension-implies-nd` — shallow theorem of the same name in `Results/Records.lean`
- `modal-b-implies-distinctness-necessary-r` — shallow theorem of the same name in `Results/Records.lean`
- `modal-five-implies-modal-b` — shallow theorem of the same name in `Results/Records.lean`
- `nd-and-bf-imply-necessary-nd`
- `necessary-actuality-implies-actuality` — shallow theorem of the same name in `Results/Records.lean`
- `necessary-atomicity-and-necessary-bf-imply-necessary-strong-leibniz`
- `necessary-atomicity-and-necessary-bf-t-imply-necessary-strong-leibniz-t`
- `necessary-atomicity-r-implies-atomicity-r`
- `necessary-barcan-r-implies-barcan-r`
- `necessary-barcan-r-implies-necessary-barcan-t`
- `necessary-barcan-r-implies-necessary-functionality-r`
- `necessary-barcan-t-implies-barcan-t` — shallow theorem of the same name in `Results/Records.lean`
- `necessary-boolean-completeness-r-implies-boolean-completeness-r` — shallow theorem of the same name in `Results/Records.lean`
- `necessary-distinctness-necessary-r-implies-distinctness-necessary-r`
- `necessary-distinctness-necessary-r-implies-necessary-barcan-r`
- `necessary-distinctness-necessary-r-implies-necessary-distinctness-necessary-t`
- `necessary-distinctness-necessary-r-implies-necessary-modal-five`
- `necessary-distinctness-necessary-t-implies-distinctness-necessary-t` — shallow theorem of the same name in `Results/Records.lean`
- `necessary-distinctness-necessary-t-implies-necessary-distinctness-necessary-r` — shallow theorem of the same name in `Results/Records.lean`
- `necessary-extensionality-r-implies-extensionality-r`
- `necessary-fregean-axiom-implies-fregean-axiom`
- `necessary-functional-choice-r-implies-functional-choice-r`
- `necessary-functional-choice-r-implies-necessary-plenitude-r`
- `necessary-functional-choice-r-implies-necessary-relational-choice-r`
- `necessary-functionality-r-implies-functionality-r`
- `necessary-functionality-r-implies-necessary-tractarianism-r`
- `necessary-gallin-comprehension-implies-gallin-comprehension`
- `necessary-gallin-comprehension-implies-necessary-nd`
- `necessary-modal-b-implies-modal-b`
- `necessary-modal-b-implies-necessary-distinctness-necessary-r`
- `necessary-modal-five-implies-modal-five`
- `necessary-modal-five-implies-necessary-modal-b`
- `necessary-nd-implies-bf`
- `necessary-plenitude-r-implies-necessary-actuality`
- `necessary-plenitude-r-implies-necessary-distinctness-necessary-r`
- `necessary-plenitude-r-implies-plenitude-r`
- `necessary-relational-choice-and-necessary-plenitude-imply-necessary-functional-choice`
- `necessary-relational-choice-r-implies-relational-choice-r`
- `necessary-rigid-comprehension-r-implies-necessary-actuality` — shallow theorem of the same name in `Results/Records.lean`
- `necessary-rigid-comprehension-r-implies-necessary-boolean-completeness-r` — shallow theorem of the same name in `Results/Records.lean`
- `necessary-rigid-comprehension-r-implies-rigid-comprehension-r`
- `necessary-strong-leibniz-and-rigid-comprehension-imply-necessary-bf-t`
- `necessary-strong-leibniz-implies-necessary-atomicity`
- `necessary-strong-leibniz-r-implies-necessary-strong-leibniz-t`
- `necessary-strong-leibniz-t-implies-strong-leibniz-t`
- `necessary-tractarianism-r-implies-necessary-barcan-r`
- `necessary-tractarianism-r-implies-tractarianism-r`
- `persistent-comprehension-r-implies-actuality` — shallow theorem of the same name in `Results/Records.lean`
- `plenitude-r-implies-actuality` — shallow theorem of the same name in `Results/Records.lean`
- `plenitude-r-implies-distinctness-necessary-r` — shallow theorem of the same name in `Results/Records.lean`
- `possible-infinity-e-and-bf-imply-axiom-of-infinity-e`
- `possible-infinity-t-and-bf-t-imply-axiom-of-infinity-t`
- `relational-choice-and-plenitude-imply-functional-choice-r`
- `rigid-comprehension-and-bf-imply-necessary-bf`
- `rigid-comprehension-r-implies-actuality` — shallow theorem of the same name in `Results/Records.lean`
- `rigid-comprehension-r-implies-inextensible-comprehension-r` — shallow theorem of the same name in `Results/Records.lean`
- `rigid-comprehension-r-implies-persistent-comprehension-r` — shallow theorem of the same name in `Results/Records.lean`
- `rigid-comprehension-r-implies-weak-rigid-comprehension-r` — shallow theorem of the same name in `Results/Records.lean`
- `strong-leibniz-r-implies-atomicity-r`
- `strong-leibniz-r-implies-strong-leibniz-t`
- `strong-leibniz-t-implies-atomicity-t`
- `tractarianism-r-implies-barcan-r` — shallow theorem of the same name in `Results/Records.lean`
- `very-weak-rigid-comprehension-r-implies-weak-rigid-comprehension-r`
- `weak-rigid-comprehension-r-implies-persistent-comprehension-r` — shallow theorem of the same name in `Results/Records.lean`
- `weak-rigid-comprehension-r-implies-very-weak-rigid-comprehension-r` — shallow theorem of the same name in `Results/Records.lean`

## Conjectured (4)

- `c5-and-atomicity-imply-no-pure-contingency`
- `possible-infinity-e-implies-axiom-of-infinity-e`
- `possible-infinity-t-implies-axiom-of-infinity-t`
- `strong-possibility-signature-r-implies-strong-possibility-r`

## Lean record names that match no map id

These theorems in `Results/Records.lean` were named by guessing the map's ids (mostly the `C5` section of 28 September); they should be renamed to the ids above.

- `actuality-and-necessary-distinctness-necessary-t-imply-boolean-completeness-r`
- `actuality-and-necessary-distinctness-necessary-t-imply-rigid-comprehension-r`
- `actuality-implies-weakly-inextensible-comprehension`
- `atomicity-t-and-necessary-distinctness-necessary-t-imply-necessary-actuality`
- `atomicity-t-and-necessary-distinctness-necessary-t-imply-necessary-boolean-completeness-r`
- `atomicity-t-and-necessary-distinctness-necessary-t-imply-necessary-rigid-comprehension-r`
- `boolean-completeness-r-and-necessary-distinctness-necessary-t-imply-actuality`
- `boolean-completeness-r-and-necessary-distinctness-necessary-t-imply-plenitude-r`
- `classicism-implies-existence-e`
- `classicism-implies-existence-rel`
- `distinctness-necessary-r-and-barcan-r-imply-necessary-distinctness-necessary-r`
- `distinctness-necessary-t-and-barcan-t-imply-necessary-distinctness-necessary-t`
- `necessary-actuality-and-necessary-distinctness-necessary-t-imply-atomicity-t`
- `necessary-actuality-and-necessary-distinctness-necessary-t-imply-necessary-boolean-completeness-r`
- `necessary-boolean-completeness-r-and-necessary-distinctness-necessary-t-imply-atomicity-t`
- `necessary-boolean-completeness-r-and-necessary-distinctness-necessary-t-imply-necessary-actuality`
- `necessary-distinctness-necessary-t-implies-barcan-r`
- `necessary-distinctness-necessary-t-implies-distinctness-necessary-r`
- `necessary-distinctness-necessary-t-implies-necessary-barcan-r`
- `necessary-rigid-comprehension-r-and-necessary-distinctness-necessary-t-imply-atomicity-t`
- `rigid-comprehension-r-and-barcan-r-imply-necessary-barcan-r`
- `rigid-comprehension-r-and-distinctness-necessary-r-imply-plenitude-r`
- `very-weak-rigid-comprehension-implies-boolean-completeness-t`
