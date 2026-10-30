# Full Boolean-valued model with a second Cohen forcing

<p class='cert'>Model — Source: Misc.; produced by Daniel Kodsi, with ChatGPT assistance, using Andrew Bacon's Boolean-valued construction and the earlier forcing-transfer arguments; recorded by GPT-6 Astra (OpenAI), prompted by Daniel Kodsi.</p>

## Package

- **□ND.** Necessarily, distinct things of any type are necessarily distinct.
- **□Relational Choice.** Necessarily, every serial binary relation has a functional subrelation.
- **Necessity of Second-Order Analysis.** Every second-order analytical sentence is either true in every real number structure in every possible world or false in every real number structure in every possible world. One sentence for each type $\sigma$ and each second-order analytical sentence.
- **¬ Analytic Necessitism.** If there could be a real number structure, there is a rigid one that is necessarily a real number structure: a rigid property with necessarily distinct instances, with rigid order, addition, multiplication and natural numbers, which necessarily form a complete ordered field. One sentence for each type $\sigma$.

## Definition

Choose a countable model N of ZFC, with no external well-foundedness assumption. Let Q=Fn(omega,2,<omega), take an N-generic G, and put M=N[G]. Inside M form the fresh regular-open completion A=RO^M(Q) of a second Cohen forcing, and B=2 times A. Use the internally full relational hierarchy with D_e=omega^M, D_t=B and all internal functions at every admitted function type. Externalize the domains at standard finite types and evaluate at the isolated first coordinate. Quantifiers are internal meets and joins; defined necessity is the global top test. The preparation of M is part of this model definition.

## Arguments

### Holds □ND, □Relational Choice.

Singleton characteristic predicates make identity crisp and necessity the top test, giving C5. Well-order each output domain internally and disjointify every relation row. The selecting graph has the same totality value as the original row, is single-valued and lies below it. Thus Relational Choice and its box hold at every admitted input/output type, including individual outputs. Necessary BF also follows directly from the top-test calculation and is derived by the map from C5.

*Write-up: [full-boolean-valued-repeated-forcing](full-boolean-valued-repeated-forcing.html). Address: `full-boolean-valued-second-cohen-forcing#boolean-core`. By Daniel Kodsi, with ChatGPT assistance, applying the Bacon and Kodsi Boolean construction, 2026-10-30.*

### Holds Necessity of Second-Order Analysis.

Cohen forcing is weakly homogeneous, its set and order are unchanged after its first application, and its square is isomorphic to itself. For every fixed standard parameter-free set-theoretic sentence, the sign decided over N is therefore also forced by the second Q over M. Translate each native second-order analytical sentence into set theory. Full extensional forcing transfer and complete-field categoricity, below each candidate field's Boolean support, give the same analytical truth at every carrier and in both coordinates. The appropriate boxed universal real-structure assertion has value top. This is the complete native schema.

*Write-up: [full-boolean-valued-repeated-forcing](full-boolean-valued-repeated-forcing.html). Address: `full-boolean-valued-second-cohen-forcing#fixed-second-order-analytical-theory`. By Daniel Kodsi, with ChatGPT assistance, 2026-10-29.*

### Fails Analytic Necessitism.

At et, endpoint sequences contain a ground real-field carrier, so possible Real has value top. Any rigid necessarily-real witness must have endpoint-valued field relations and hence be one ground complete ordered field. A second Cohen real yields a new rational cut without an old supremum, so no such field remains complete in the forcing coordinate. Every candidate contributes bottom to the existential consequent. Thus the actual et instance of AN fails; SOAN failure is derived.

*Write-up: [full-boolean-valued-repeated-forcing](full-boolean-valued-repeated-forcing.html). Address: `full-boolean-valued-second-cohen-forcing#new-real-refutes-analytic-necessitism`. By Daniel Kodsi, with ChatGPT assistance, applying the earlier new-cut obstruction, 2026-10-29.*


## Notes

Relative existence follows from Con(ZFC) using an arbitrary countable model, not a countable transitive model. The forcing completion is formed in M after preparation. Theory preservation is an external schema for standard finite parameter-free formulas; it asserts neither a truth predicate nor elementarity with parameters from M. No No Pure Contingency or finite-type necessitism verdict is added. The analytical verdicts use the existing unboxed schema nodes. Mathematical review was carried out with ChatGPT assistance; no independent human check or Lean proof is recorded.

## Sources

- **Repeated forcing 29 Oct** — Daniel Kodsi, with ChatGPT assistance, Fixed analytical theory with changing analytical objects, 29 October 2026, repeated Cohen forcing argument; proof reproduced in the companion write-up, Sections 1–5 and 7.
- **Bacon Boolean hierarchy** — Andrew Bacon, Could the truths of mathematics have been different?, draft of 9 October 2025, online Appendix B.2, pp. 7–9 (PDF pp. 41–43), Boolean-valued construction and Lemmas B.1–B.4.
- **Kodsi Boolean transfer** — OpenAI Codex, prompted by Daniel Kodsi, Full Boolean-valued carrier and premise audit, 25 October 2026, Sections 5 and 7; Generic-point Boolean models, 25 October 2026, Sections 2–3 and 6, internal soundness, endpoint rigidity and extensional forcing transfer.
- **New-cut obstruction** — Claude Fable 5.1 (Anthropic), prompted by Zachary Goodsell, 23 October 2026, revised 24 October at Cian Dorr's direction, rigid-ground-field and new-rational-cut obstruction, as recorded in full-boolean-valued-atom-and-atomless.

<p class='cert'>Record: <code>topics/classicism/models/full-boolean-valued-second-cohen-forcing.yaml</code></p>

## Paper references

- **Background: [Could the truths of mathematics have been different?](https://andrew-bacon.github.io/papers/Could%20mathematics%20have%20been%20different.pdf).** Bacon, Andrew (2025). Could the truths of mathematics have been different? Draft dated 9 October 2025, with online appendix; published in Philosophical Review 135(3), 2026, pp. 221–285, as cited by Barton and Goodsell. Locators refer to the draft. The full Boolean-valued construction is in appendix §B.2, pp. 7–9 of the separately paginated appendix (PDF pp. 41–43); Theorem 4.4 and its proof (Appendix C.1) and Lemma C.6 (Appendix C.2) were read directly on 19 October 2026. — Online Appendix B.2, pp. 7–9 (PDF pp. 41–43), Lemmas B.1–B.4
