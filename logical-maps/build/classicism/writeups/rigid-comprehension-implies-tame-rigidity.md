# Rigid Comprehension ⇒ Tame Rigidity

<p class='cert'>Result — Source: Possible Worlds Without Atomicity (draft), Lean `Classicism.Map.rigid_comprehension_implies_tame_rigidity`; produced by Christopher Sun; recorded by Claude Opus 5.5 (Anthropic), 2 October 2026.</p>

## Premises

- **Rigid Comprehension.** Every relation, including a proposition, is coextensive with a rigid one.

## Conclusion

- **Tame Rigidity.** Every weakly rigid relation, including a proposition, is rigid.

## Proof

Lemma: coextensive weakly rigid relations are identical. Let $F$ and $G$ be weakly rigid with $\forall\bar x\, .\,F[\bar x]\leftrightarrow G[\bar x]$. If $F[\bar x]$ then $G[\bar x]$, and T applied to $\operatorname{Persistent}(G)$ gives $\Box G[\bar x]$. So $\forall\bar x\, .\,F[\bar x]\to\Box G[\bar x]$, and the weak inextensibility of $F$, instantiated at $G$, gives $F\le G$. Symmetrically $G\le F$. Together these say $\Box\forall\bar x\, .\,F[\bar x]\leftrightarrow G[\bar x]$, and necessarily coextensive relations are identical in C (Intensionality), so $F=G$. Now let $F$ be weakly rigid. Rigid Comprehension at the same type supplies a rigid $G$ coextensive with $F$. A rigid relation is weakly rigid, since T strips the leading box from $\operatorname{Inextensible}(G)$. By the lemma $F=G$, so $F$ is rigid.

## Notes

The lemma uses only the unboxed persistence of $F$ and $G$, so Rigid Comprehension makes every very weakly rigid relation rigid as well. With Rigid Comprehension ⇒ Weak Rigid Comprehension, this gives Sun's equivalence of Rigid Comprehension with Tame Rigidity plus Weak Rigid Comprehension.

## Sources

- **Possible Worlds Without Atomicity** — Christopher Sun, Possible Worlds Without Atomicity, draft of September 2026.

<p class='cert'>Record: <code>topics/classicism/results/rigid-comprehension-implies-tame-rigidity.yaml</code></p>

## Paper references

- **Origin: Possible Worlds Without Atomicity.** Sun, Christopher. Possible Worlds Without Atomicity. Unpublished draft, September 2026.
- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — §1.5, pp. 16–17. Intensionality and T.
