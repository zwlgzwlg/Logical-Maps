# Rigid Power with one individual name and infinitely many unary predicates

*OpenAI Codex (GPT-6), prompted by Daniel Kodsi. Independent mathematical review. The underlying signature-definable root is due to Cian Dorr with GPT-6 Astra and Claude Fable 5.2, prompted by Cian Dorr.*

Fix one individual name and countably many unary predicate names in the public signature $\Sigma$. Let $W$ be the coalesced definable root over any family of pointed components complete for $C(\Sigma)$. For every rigid property $F:t\to t$ at $W$, its canonical power

$$
P_F(X)\;\equiv\;\mathrm{Rigid}(X)\land X\le F
$$

is rigid there. In fact the argument proves Rigid Power at every finite arity. At type $t\to t$ it also proves that the current extension of $F$ is externally finite.

## How full rigidity constrains the descriptor

Write $u$ for the closed descriptor of $F$. At every component entrance the transported $F$ is the interpretation of $u$. Rigidity persists. If $C(\Sigma)$ did not prove $\mathrm{Rigid}(u)$, some designated component would therefore contradict rigidity of the transported $F$. Similarly, let $\bar a$ be any actual member of $F$ with descriptor tuple $\bar s$. Persistence of membership in the rigid $F$ shows that $u(\bar s)$ holds at every entrance. Hence

$$
C(\Sigma)\vdash\mathrm{Rigid}(u),\qquad
C(\Sigma)\vdash u(\bar s)\quad\text{for every represented }\bar s.
$$

This is where the assumption of **full** rigidity enters. The sole assertion that $F$ is weakly rigid at $W$ does not force the first theorem.

## Use a second root to bound the number of descriptors

Work in the auxiliary signature-Maximalist model $R$ of the [finite-support construction](coalesced-finite-support-rigid-root.md). Its private language adds fresh predicate names. Its old component theory $T$ requires those predicates to miss every tuple of closed terms necessarily. The cited construction proves that every weakly rigid relation at $R$ has only finitely many distinct old descriptor tuples among its current members, modulo $T$-provable identity.

Interpret the **public term** $u$ at $R$. By the two theorems above it is rigid there and contains the interpretation at $R$ of every represented public tuple $\bar s$. That interpretation has old descriptor $\bar s$. Furthermore, if two public descriptors are distinct modulo $C(\Sigma)$, they remain distinct modulo $T$. Indeed, take a pointed $C(\Sigma)$-model separating a coordinate of the two. Interpreting all the private predicates by constant bottom gives a $T$-expansion on the same model, preserving the public disequality. Thus all the distinct public descriptors represented in $F$ inject into the finite descriptor support of the single relation $u$ at $R$. Their number is finite.

This argument compares interpretations of **closed terms**. The actual membership row of $F$ at $W$ need not be the actual membership row of $u$ at either root. The two roots may have different domains and different component families.

## The power at the original root and throughout its cone

Back at $W$, choose one actual member $\bar a_i$ of $F$ for each of its finitely many descriptor tuples. A root tester is available whose current row is full and whose descriptor is the finite union of the tuple-haecceities of the corresponding $\bar s_i$. It necessarily accepts every actual member of $F$. Weak inextensibility yields containment of $F$ in this tester. Conversely persistence ensures every transported $\bar a_i$ remains in $F$. Consequently at each proper exit, including its continuations, the entire transported $F$ is the finite union of the haecceities of the images of the $\bar a_i$.

At any proper target the canonical power of this finite union is rigid by the [finite-bound lemma](https://github.com/dkodsi/Logical-Maps/blob/308cd0abb0684dcc6de1d52d521801fd6bb6fc94/logical-maps/topics/classicism/background/rigidity.md#internally-finite-bounds). At the original root $P_F$ is persistent because its defining conditions persist. Every rigid subrelation of the transported bound at any proper target is the union of finitely many tuple-haecceities there: its current extension is finite, and weak inextensibility and persistence identify it with the union of the haecceities of its current members. Choose a source representative $\bar a_i$ for each selected target tuple. Their source haecceity union is rigid and lies below $F$ by persistence. It transports to the required subrelation as a whole entity. Thus any tester necessary on all current $P_F$-members covers all its members at every future, proving weak inextensibility at the root. Combined with the proper-target result this proves full rigidity.

For the particular input type $t$, a root proposition consists of its descriptor and one current bit. Hence finitely many descriptors give at most twice that many root members, and the finite-bound lemma also applies at the original root itself. At other types descriptor fibres can be infinite, which is why the lift of a finite union through each proper exit is useful.

## Consequences

The proof used only an arbitrary complete family of components and the availability of all current rows with a single closed descriptor per relation. It applies to all such families for the specified signature and to every allowed choice of the interpretations of its predicate names at the root.

For this signature [Barcan at propositional type](coalesced-definable-root-signature.md) holds at the root. The universal property of propositions is therefore weakly rigid. A component where Barcan fails makes its transport cease to be weakly rigid, so it is not rigid at the root. Thus Tame Rigidity fails. Weakly Rigid Power would imply Tame Rigidity and fails as well. Since $W$ satisfies signature Maximalism and Rigid Power together, it refutes both implications. The specified signature meets the map’s [requirement of a nonindividual constant](https://github.com/dkodsi/Logical-Maps/blob/308cd0abb0684dcc6de1d52d521801fd6bb6fc94/logical-maps/topics/classicism/background/signatures.md). The two negative verdicts concern implications with an unrestricted signature parameter. The construction does not need these conclusions to fail for every finite signature.
