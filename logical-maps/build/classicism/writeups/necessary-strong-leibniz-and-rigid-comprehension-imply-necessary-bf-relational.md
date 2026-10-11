# □Strong Leibniz Biconditionals ∧ Rigid Comprehension ⇒ □BF (relational types)

<p class='cert'>Result — Source: Philosophical Introduction to HOL (2024); produced by Andrew Bacon; recorded by Claude Fable 5.1 (Anthropic), 22 September 2026.</p>

## Premises

- **□Strong Leibniz Biconditionals.** Necessarily, at each relational type, every possible entity (one distinct from bottom) is entailed by a strong world: a possible entity that necessarily entails every entity of the type or its negation.
- **Rigid Comprehension.** Every relation, including a proposition, is coextensive with a rigid one.

## Conclusion

- **□BF (relational types).** Necessarily, BF holds at every relational type.

## Proof

Theorem 8.2 of the book: given Rigid Comprehension, $\Box\mathrm{SL}_\sigma$ at all relational types implies $\Box\mathrm{BF}_\sigma$ for every relational $\sigma\ne e$. Its proof for $\sigma=t$ (pp. 170–171): from $\Diamond\exists p\, .\,Xp$, $X$ is a possible property, so by $\mathrm{SL}_{tt}$ it is entailed by a strong world property $W$; let $H$ be the rigid collection, supplied by Rigid Comprehension, of world properties accessible to $W$, and let $r:=\exists V\, .\,\exists p\, .\,HV\land Vp\land p$. Bacon shows $\Box\forall p\, .\,Wp\to p=r$, using $\Box\mathrm{SL}_t$ for the step that every world proposition entails $\exists V\, .\,HV\land Vp$ and the rigidity of $H$ for the converse; since $W$ entails $X$, $\Diamond Xr$, which gives $\exists p\, .\,\Diamond Xp$, the contrapositive of $\mathrm{BF}_t$. The argument is carried out under necessary assumptions, so it yields $\Box\mathrm{BF}_t$. The book proves the same for every relational type other than $e$, and the map records it at all of them.

## Notes

The right-to-left half of Theorem 8.2 is the recorded implication from □Atomicity and □BF (relational types) to □SL, which needs no Rigid Comprehension. The type-$t$ case, which the book proves in full, is derived through □BF (relational types) ⇒ □BF (type t).

## Revisions

- **2026-10-11** (Claude Opus 5.5 (Anthropic), at Cian Dorr's direction) — The conclusion is now □BF (relational types), as Theorem 8.2 states it, in place of □BF (type t), recorded until then for want of a node; the record's id changed with it (formerly necessary-strong-leibniz-and-rigid-comprehension-imply-necessary-bf-t). The proof text is unchanged except for its last sentence.

## Sources

- **Philosophical Introduction to HOL** — Andrew Bacon, A Philosophical Introduction to Higher-Order Logics, Routledge, 2024, §8.2, Theorem 8.2, pp. 169–171.

<p class='cert'>Record: <code>topics/classicism/results/necessary-strong-leibniz-and-rigid-comprehension-imply-necessary-bf-relational.yaml</code></p>

## Paper references

- **Proof: A Philosophical Introduction to Higher-Order Logics.** Bacon, Andrew (2024). A Philosophical Introduction to Higher-Order Logics. Routledge. DOI 10.4324/9781003039181. Chapter 8, Application: Consequences and strengthenings of Classicism, pp. 155–182, and Chapter 18, The model theory of classicism, pp. 389–413, were read directly on 22 September 2026; locators give the book's own page numbers. The book works in the full simple type hierarchy with Modalized Functionality at all types; its results are taken in the map's relational type system, of which its models are models. — §8.2, Theorem 8.2, pp. 169–171
