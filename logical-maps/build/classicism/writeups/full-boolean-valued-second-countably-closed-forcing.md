# Full Boolean-valued model with a second countably closed forcing

<p class='cert'>Model — Source: Misc.; produced by Daniel Kodsi, with ChatGPT assistance, using Andrew Bacon's Boolean-valued construction and the earlier no-new-reals and represented-power arguments; recorded by GPT-6 Astra (OpenAI), prompted by Daniel Kodsi.</p>

## Package

- **□ND.** Necessarily, distinct things of any type are necessarily distinct.
- **□Relational Choice.** Necessarily, every serial binary relation has a functional subrelation.
- **Necessity of Second-Order Analysis.** Every second-order analytical sentence is either true in every real number structure in every possible world or false in every real number structure in every possible world. One sentence for each type $\sigma$ and each second-order analytical sentence.
- **Analytic Necessitism.** If there could be a real number structure, there is a rigid one that is necessarily a real number structure: a rigid property with necessarily distinct instances, with rigid order, addition, multiplication and natural numbers, which necessarily form a complete ordered field. One sentence for each type $\sigma$.
- **¬ Second-Order Analytic Necessitism.** If there could be a real number structure, there is a rigid one, necessarily a real number structure, together with represented powers of every arity up to $n$: rigid properties of rigid relations among the structure's elements that necessarily represent every relation on them. One sentence for each type $\sigma$ and each $n\ge1$.

## Definition

Choose a countable model N of ZFC+CH, with no external well-foundedness assumption. Let Q=Fn(omega_1,2,<omega_1), the countable partial binary functions, take an N-generic G, and put M=N[G]. Inside M form the fresh regular-open completion A=RO^M(Q) of a second application of this forcing, and B=2 times A. Use D_e=omega^M, D_t=B and the internally full function domains at every admitted relational type. Externalize standard finite types and evaluate at the isolated first coordinate. Quantifiers are internal meets and joins; necessity is the global top test. All countability assertions about the forcing and its conditions are internal to the indicated ground.

## Arguments

### Holds □ND, □Relational Choice.

Crisp identity and top-test necessity give C5. Internal well-orders disjointify arbitrary relation rows into selecting graphs with the same totality values; Relational Choice and its box hold at all admitted input/output types. The direct top-test calculation also gives necessary BF, which the map derives from C5.

*Write-up: [full-boolean-valued-repeated-forcing](full-boolean-valued-repeated-forcing.html). Address: `full-boolean-valued-second-countably-closed-forcing#boolean-core`. By Daniel Kodsi, with ChatGPT assistance, applying the Bacon and Kodsi Boolean construction, 2026-10-30.*

### Holds Necessity of Second-Order Analysis.

Countable closure preserves all countable sequences of ordinals and omega_1, so after the first forcing every countable partial binary condition is old: the recomputed Q has exactly the old set and order. It is weakly homogeneous and Q times Q is isomorphic to Q. The product/iteration calculation makes the second forcing preserve every standard finite parameter-free set-theoretic sentence over M. Extensional transfer and complete-field categoricity give the full native second-order analytical schema at every carrier, including vacuous instances.

*Write-up: [full-boolean-valued-repeated-forcing](full-boolean-valued-repeated-forcing.html). Address: `full-boolean-valued-second-countably-closed-forcing#fixed-second-order-analytical-theory`. By Daniel Kodsi, with ChatGPT assistance, 2026-10-29.*

### Holds Analytic Necessitism.

The second forcing adds no reals. The old complete real field stays complete for every new bounded subset because its supremum is determined by an old rational cut. Conditions with domain omega give a ground-continuum antichain in A, so every nonindividual type admits an endpoint-valued copy of the field. Endpoint rigidity and full extensional transfer make it a rigid necessarily-real witness. At e, a complete field on a subset of omega is impossible in either coordinate, making the antecedent false. This proves every current AN instance with its native guard.

*Write-up: [full-boolean-valued-repeated-forcing](full-boolean-valued-repeated-forcing.html). Address: `full-boolean-valued-second-countably-closed-forcing#no-new-reals-give-all-carrier-an`. By Daniel Kodsi, with ChatGPT assistance, 2026-10-29.*

### Fails Second-Order Analytic Necessitism.

A fresh-coordinate dense argument makes the second generic subset of omega_1 unequal to every old subset with Boolean equality value zero. CH survives the first forcing, so transfer this name to every prospective ground real carrier. Rigid supported relations are old endpoint-valued subsets. The join of their agreement values with the new subset has forcing coordinate zero, so no rigid family can satisfy the boxed representation clause. This defeats every field tuple and every unary represented power, not just a chosen canonical one. The et, arity-one SOAN antecedent is true and its consequent is bottom.

*Write-up: [full-boolean-valued-repeated-forcing](full-boolean-valued-repeated-forcing.html). Address: `full-boolean-valued-second-countably-closed-forcing#new-subset-refutes-every-unary-power`. By Daniel Kodsi, with ChatGPT assistance, 2026-10-29.*


## Notes

Relative existence follows from Con(ZFC), using the relative consistency of CH and arbitrary countable models. This strengthens the analytical truth profile of the one-stage countably closed subset model by a different prescribed ground; it does not change that earlier record. Necessary BF is derived. AN and SOAN use their existing unboxed nodes; no additional outer-box or finite-type necessitism verdict is asserted. The Boolean completion must be taken freshly inside M. Mathematical review was carried out with ChatGPT assistance; no independent human check or Lean proof is recorded.

## Sources

- **Repeated forcing 29 Oct** — Daniel Kodsi, with ChatGPT assistance, Fixed analytical theory with changing analytical objects, 29 October 2026, repeated countably closed forcing argument; proof reproduced in the companion write-up, Sections 1–4 and 6–7.
- **Bacon Boolean hierarchy** — Andrew Bacon, Could the truths of mathematics have been different?, draft of 9 October 2025, online Appendix B.2, pp. 7–9 (PDF pp. 41–43), Boolean-valued construction and Lemmas B.1–B.4.
- **Kodsi Boolean transfer** — OpenAI Codex, prompted by Daniel Kodsi, Full Boolean-valued carrier and premise audit, 25 October 2026, Sections 5 and 7; Generic-point Boolean models, 25 October 2026, Sections 2–3, 6 and 7.2, internal soundness, endpoint rigidity and extensional forcing transfer.
- **AN and represented powers** — Daniel Kodsi, with ChatGPT assistance, Analytic Necessitism and no-new-reals forcing, and represented powers in an internally full Boolean hierarchy, 29 October 2026; the all-carrier and uniform unary-power proofs are reproduced in the companion write-up, Sections 4 and 6.

<p class='cert'>Record: <code>topics/classicism/models/full-boolean-valued-second-countably-closed-forcing.yaml</code></p>

## Paper references

- **Background: [Could the truths of mathematics have been different?](https://andrew-bacon.github.io/papers/Could%20mathematics%20have%20been%20different.pdf).** Bacon, Andrew (2025). Could the truths of mathematics have been different? Draft dated 9 October 2025, with online appendix; published in Philosophical Review 135(3), 2026, pp. 221–285, as cited by Barton and Goodsell. Locators refer to the draft. The full Boolean-valued construction is in appendix §B.2, pp. 7–9 of the separately paginated appendix (PDF pp. 41–43); Theorem 4.4 and its proof (Appendix C.1) and Lemma C.6 (Appendix C.2) were read directly on 19 October 2026. — Online Appendix B.2, pp. 7–9 (PDF pp. 41–43), Lemmas B.1–B.4
