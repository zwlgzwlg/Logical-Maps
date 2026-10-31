# Necessary arithmetic infinity

[Paper (PDF)](../papers/finite-type-necessitism.pdf) · [LaTeX source](../papers/finite-type-necessitism.tex) · [Finite-type guide](finite-type-non-contingency-guide.md)

## Map node

$$\Box I^*_{\rho}.$$

This is the entire statement of the node. It asserts necessary zero-exclusion and successor injectivity for the canonical numbers at source type $\rho$. The type letter indexes the finite-type schema; it is not quantified in the object language. The map's canonical zero, successor and least inductive number property are those defined in Section 3, equation (3.1), of the paper.

The node is an optional assumption. There is no empty-premise result deriving it from Classicism, and it is not automatically assigned to every model. It is neither Arithmetic Necessitism nor a substitute for the separately formulated quantified individual Infinity principle. The entry makes the existing canonical-arithmetic assumption selectable; it does not claim a new formulation of infinity.

## Supporting transfer lemma — not a map node

Section 3, pp. 4–5, states, over Classicism,

$$\Box I^*_{\rho}\longrightarrow\Box I^*_{et}.$$

This conditional is retained here as a supporting lemma, not as the node and not as an unconditional proof of either boxed assumption. The target $et$ is the type of properties of individuals.

Fix a finite type $\rho$ and assume $\Box I^*_\rho$. Section 3 of the paper uses the rigid finite initial segments of the necessarily Peano $\mathbb N_\rho$ as size standards. Failure of $I^*_{et}$ gives a successor collision and a necessarily empty predicate for a positive finite cardinality, hence a necessary finite bound on $et$. The necessary injections $a\mapsto\lambda x(x=a)$ and $p\mapsto\lambda x\,p$ transfer that bound to $e$ and $t$. Counting profiles over the finitely many Boolean atoms of $t$ propagates necessary finite bounds through finite type formation, contradicting $\Box I^*_\rho$. This proves the conditional with unboxed consequent. Necessitate that proved conditional, not the temporary hypothesis, and use axiom 4 and distribution to obtain $\Box I^*_\rho\to\Box I^*_{et}$. No FTN instance or additional infinity premise is used.

This records the argument supplied in the paper; it is not a new independent proof verification. No new graph implication or model verdict is inferred merely from adding the assumption node. The paper PDF and original LaTeX remain unchanged.
