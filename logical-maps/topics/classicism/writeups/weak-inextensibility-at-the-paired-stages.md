# A current family with no weakly inextensible coextension

The [integer stages with unrestricted pinned rows](integer-stages-paired-individuals-glued-constants.html) and their [fixed-or-collapsed pair restriction](fixed-or-collapsed-pairs.html) fail even local Weakly Inextensible Comprehension at the type of unary predicates on propositions. The same witness works with [isolated zero coefficients](paired-stages-with-zero-arrows.html), where the paired sites are external. It therefore applies to both the glued-name and constant-name interpretations.

Fix a stage $n$. In one coordinate choose a seat $a_i$ from each of $\aleph_1$ different ordinary pairs. There are at least continuum many subsets of the nonempty words. Choose distinct such subsets $S_i$ for these indices. Define the scalar $p_i$ at $n$ by the following rows.

- On an ordinary empty-word arrow it is true exactly if the target is $n$ and the coefficient fixes $a_i$.
- On an ordinary arrow with nonempty word $w$ it is true exactly if $w\in S_i$.
- If there are zero coefficients, use false there.

Each $p_i$ has the singleton pin $\{a_i\}$ and is true at $n$. For any ordinary empty-word endomorphism $g:n\to n$ and $j\ne i$, the propositions $gp_j$ and $p_i$ differ: continue by the identity coefficient labelled with any nonempty word in the symmetric difference of $S_i$ and $S_j$. If $g$ moves $a_i$, then $gp_i$ is currently false, distinguishing it from $p_i$ as well.

The family $E=\{p_i:i<\omega_1\}$ is an admitted current extension because a row at each target can be chosen independently of the ordinary coefficient. Suppose $Y$ is a coextensive weakly inextensible predicate and let $N$ pin its rows. Choose $a_i$ in a pair disjoint from $N$. There is an ordinary empty-word endomorphism $f$ of $n$ that fixes $N$ and moves $a_i$, by collapsing that pair onto its other seat and fixing the rest. Thus $Y_f=Y_{1_n}=E$ as rows on the same target, so $p_i\in Y_f$.

Define a tester with full rows except at ordinary empty-word endomorphisms $g$ of $n$ moving $a_i$, where it excludes the single whole proposition $p_i$. Its pin is $\{a_i\}$. Every current member of $Y$ necessarily satisfies it, since at each restricted row all transported $gp_j$ differ from $p_i$ by the word or current-bit test above. But the tester excludes $p_i$ at $f$, contradicting weak inextensibility of $Y$. The argument works at every stage.

The earlier two-object paired-individuals model uses a different support argument for a related failure. Here the word profiles distinguish the source members even where the only allowed change to the selected pair is a collapse. OpenAI Codex (GPT-6), prompted by Daniel Kodsi, 27 November 2026.
