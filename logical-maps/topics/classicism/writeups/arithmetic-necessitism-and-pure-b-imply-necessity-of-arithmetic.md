# Arithmetic Necessitism and pure B imply Necessity of Arithmetic

Fix a type $\sigma$. Write $N$ for its Frege numbers, $I^*$ for their
Peano condition, and $I$ for $\Diamond I^*$. We use B only for the closed
pure sentence $I$.

By the [equivalent forms of Potential Infinity](../index.html#background/arithmetic),
C proves $I\leftrightarrow I^*$. C also proves $\Diamond I\leftrightarrow I$,
since $I$ is a possibility and the accessibility relation is reflexive
and transitive. The B instance $I\to\Box\Diamond I$ now shows
$I\to\Box I$, hence $I\to\Box I^*$. If $I$ has no possible instance,
$\Box(I\to A)$ holds for every sentence $A$. Otherwise $I$ holds now
and $I^*$ holds necessarily.

In the second case Arithmetic Necessitism makes $N$ rigid. In particular,
if each current number necessarily satisfies an admitted property $X$, then
necessarily every number satisfies $X$. This is precisely the conclusion of
Goodsell's Lemma 8, the only place his argument uses Countable Boolean
Completeness. Substituting this instance of weak inextensibility in his
proof of Theorem 9 gives $\Box(I\to A)\lor\Box(I\to\neg A)$ for each
arithmetical sentence $A$. This also holds in the first case, since its guard
is impossible. [Goodsell's Lemma 8 and Theorem 9](countable-boolean-completeness-implies-necessity-of-arithmetic.html)

OpenAI Codex (GPT-6), prompted by Daniel Kodsi, obtained this combination
of the pure B instance with Arithmetic Necessitism's restricted
quantification on 26 November 2026, using Zachary Goodsell's arithmetic
persistence and formula induction. Two additional GPT-6 research agents
independently reviewed the argument.
