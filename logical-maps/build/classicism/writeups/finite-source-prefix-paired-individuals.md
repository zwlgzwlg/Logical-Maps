# Paired-individuals model with a singleton-source prefix

Proof by OpenAI Codex, prompted by Daniel Kodsi, 30 October 2026, from GPT-6 Astra, prompted by Daniel Kodsi, *Finite-source prefix and the boxed two-hat question* (29 October 2026, §§1–3). The paired tail and its two-hat separation are due to Cian Dorr and Claude Fable 5.1 (Anthropic), prompted by Cian Dorr, 14 October 2026, with the retained argument clarified on 29 October. The earlier entrance construction is due to GPT-6 Astra (OpenAI), prompted by Daniel Kodsi, *A fixed-point entrance model, Tame Rigidity without □Tame Rigidity*, 22 October 2026, §§1–6 (unpaginated), as credited in [the qualitative-links entrance model](symmetric-entrance-qualitative-links.html). The present corollary uses all constant entrance arrows and the paired tail; it is not a new general model family.

## 1. Category, domains, and the unchanged tail

Take the unsymmetric ideally-full category of [paired-individuals-two-object](paired-individuals-two-object.html): its objects are $W=\mathbb N$ in two-element blocks and $V=\mathbb N\sqcup\{\star\}$, with $\star$ a singleton block, and its arrows are all block-respecting maps. Retain all these arrows. Adjoin $A=\{*\}$ with only its identity endomorphism, all constants $c_b:A\to W,V$, and no arrows from $W$ or $V$ to $A$. Composition is composition of maps: $h c_b=c_{h(b)}$. Use finite pins and trivial symmetry groups throughout, with each base as its individual domain. Relational signature constants can be top.

Finite pins have finite images, so the hypotheses of the ideally-full construction in *Classicism*, Appendix D, Definitions D.1–D.3 and Proposition D.4, pp. 73–74, hold. In particular, if a root profile is transported along $c_b$, its transport is pinned by $\{b\}$: parallel $k,l$ agreeing at $b$ satisfy $k c_b=l c_b$. This verifies the additional transport obligation. The cited construction theorem supplies typed term and quantifier closure and C soundness.

The old worlds have exactly the same outgoing categories. Induction on types therefore leaves their domains, application, transport, quantifiers and truth values unchanged. New incoming maps do not add operators to the old domains. The old two-hat counterexample continues to quantify over every old operator, not merely transported source operators.

## 2. The complete atomic source

At a relational type $\tau=\bar\sigma t$, a root profile assigns a subset of the appropriate target tuple-domain to each arrow out of $A$. Every such profile is pinned by $\{*\}$, since parallel arrows agreeing on the singleton source are equal. With trivial symmetries there is no further restriction. The root Boolean algebra is therefore the full powerset of the disjoint union of arrow/target-tuple coordinates. Its arbitrary intersections and unions are admitted meets and joins; its singleton coordinates are atoms. This proves Boolean Completeness and Atomicity at every relational type, including the null tuple $t$.

The proposition containing just $1_A$ is true and contained in every true proposition, so it witnesses Actuality. Given a currently serial relation, choose a functional subrelation of its identity-row extension in the external ZFC metatheory. Give this graph empty extensions at all nonidentity arrows. It is an admitted root profile, so it proves full current Relational Choice, including individual outputs. No operation-valued choice follows from this construction.

## 3. Failure of the boxed collapse

At the old $W$, let $p_0$ be the proposition consisting of the arrows $W\to W$. The current `two-hat-not-five` argument of the paired-tail record proves

$$\Box_5p_0\quad\text{and}\quad\neg\hat{\hat\Box}p_0.$$

Use its corrected support reading: the relevant predicate $Y$ accepts every proposition at $W$, and at $V$ accepts exactly those propositions pinned by a finite set of **old individuals**. Do not use the literally broader phrase “in the range of some arrow from $W$”. The inclusion $W\to V$ survives the second-hat return game at every finite old pin, preventing two-hat necessity of $p_0$. Along the restricted arrows injective on a finite union of old blocks, transported pins remain old; the $Y$ argument and the unconditional Barcan law for $\Box_5$ then establish $\Box_5p_0$. The source's 29 October withdrawal concerns its different, unrestricted ordinary-BF argument; it expressly preserves this two-hat argument. The present proof does not depend on any AN/SOAN argument.

The constant $c_0:A\to W$ makes that world accessible. Hence the closed sentence $\forall p(\Box_5p\to\hat{\hat\Box}p)$ is false at an accessible evaluation, and its necessity is false at $A$. The source itself satisfies the current collapse by Actuality; only the boxed conclusion is refuted.

Thus the model satisfies current full Boolean Completeness, full Atomicity, Actuality and full Relational Choice, while failing necessary five-to-two-hat collapse. This combines familiar complete-source reasoning with the recorded tail separation. It asserts neither necessary completeness nor a new analysis verdict.

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — Appendix D, Definitions D.1–D.3 and Proposition D.4, pp. 73–74. Ideally-full action-model soundness.
