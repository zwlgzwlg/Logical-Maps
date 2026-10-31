# ND (type t) ∧ 5-necessities are ND-necessary ⇒ □ND

<p class='cert'>Result — Source: Misc.; produced by GPT-6 Astra, prompted by Daniel Kodsi; recorded by OpenAI Codex, prompted by Daniel Kodsi.</p>

## Premises

- **ND (type t).** Distinct propositions are necessarily distinct.
- **5-necessities are ND-necessary.** Whatever is 5-necessary is ND-necessary.

## Conclusion

- **□ND.** Necessarily, distinct things of any type are necessarily distinct.

## Proof

Write $D=\Box_{\ne}$ and $S=\Box_5$. Current ND at $t$ gives $Dp\to\Box p$: a witness $q$ to $Dp$ is true and satisfies $\Box(\Diamond q\to p)$; hence $q\ne\bot$, and ND gives $\Box(q\ne\bot)$, equivalently $\Box\Diamond q$. Normal modal reasoning yields $\Box p$. The assumed $Sp\to Dp$ therefore gives current $Sp\to\Box p$. The unconditional implications $\Box p\to Sp$ and [[box5-barcan]] now yield, at every admitted type, $\forall x\,\Box Rx\to\forall x\,S Rx\to S\forall x\,Rx\to\Box\forall x\,Rx$. Thus ordinary BF holds, in particular at $t$. Apply [[nd-t-and-bf-t-imply-necessary-nd-t]], then [[necessary-distinctness-necessary-t-implies-necessary-distinctness-necessary-r]]. All applications of the local-collapse premise are current; no optional hypothesis is necessitated or substituted underneath a box.

## Notes

Only the type-t instance of current ND is needed. The converse follows from existing results, so no reverse arrow is added. This is a short consequence of the credited 5-necessity Barcan theorem.

## Sources

- **Local collapse derivation** — GPT-6 Astra, prompted by Daniel Kodsi, Local 5-to-ND collapse is Barcan for ND-necessity, research note of 29 October 2026, section Consequence: the ND propagation question (unpaginated).
- **Dorr–Astra Barcan for 5-necessity** — Cian Dorr, with help from GPT-6 Astra (OpenAI), 29 October 2026, Background varieties, proposition box5-barcan (unpaginated).
- **Classicism** — Andrew Bacon and Cian Dorr, Classicism, draft of 16 May 2023, Proposition 2.4, p. 23.

<p class='cert'>Record: <code>topics/classicism/results/nd-t-and-five-to-nd-collapse-imply-necessary-nd.yaml</code></p>

## Paper references

- **Proof: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — Proposition 2.4, p. 23. The current ND plus BF propagation step.
