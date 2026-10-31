# Cofinite-germ model: Functional Choice without Boolean Completeness

<p class='cert'>Model — Source: Misc.; produced by Daniel Kodsi, with ChatGPT assistance; recorded by ChatGPT, prompted by Daniel Kodsi.</p>

## Package

- **Functional Choice.** Every serial binary relation admits a selecting operation. Its output type is relational, as required by the type system.
- **¬ Boolean Completeness (type t).** Every property of propositions has a greatest lower bound.

## Definition

At r in the cofinite-neighborhood germ model over {r} union N, all relational domains are germs of arbitrary pointwise relation tables. D_e is a singleton; application and lambda abstraction are table slicing and tabulation; quantifiers use full point domains. The proposition algebra at r is 2 x (P(N)/Fin). See complete accompanying proof note.

## Arguments

### Holds Functional Choice. Fails Boolean Completeness (type t).

Sections 3–4 construct every admitted type and prove term locality, whole-object substitution, beta, eta, and the H-restricted Logical Equivalence schema. Section 5 represents every set function between the domains at r with relational output, giving all-type Functional Choice. Section 6 gives an admitted family of propositions with no supremum in 2 x (P(N)/Fin). The failure of full Boolean Completeness and Rigid Comprehension follows through the existing implications.

*Write-up: [functional-choice-countermodel](functional-choice-countermodel.html). Address: `cofinite-germ-functional-choice-incomplete#functional-choice-and-failed-join`. By Daniel Kodsi, with ChatGPT assistance, 2026-10-30.*


## Notes

Functional Choice is unboxed. Boolean Completeness fails at proposition type t. Section 9 separately shows why the construction does not satisfy necessary Functional Choice.

## Sources

- **Kodsi / ChatGPT germ construction** — Daniel Kodsi, with ChatGPT assistance, Functional Choice without Boolean Completeness, 30 October 2026, Sections 3–7; the substitution argument is expanded in Section 4.5.

<p class='cert'>Record: <code>topics/classicism/models/cofinite-germ-functional-choice-incomplete.yaml</code></p>
