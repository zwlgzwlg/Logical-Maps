# A propositional atom can stay strong while a unary atom splits

For every set-sized signature, Logical Necessity is consistent with necessary Strong Atomicity at type $t$ and necessary ordinary Atomicity at every relational type, while a unary relation is an ordinary atom and fails to be a self-atom. The splitting occurs at a point where the unary relation is instantiated. Countable Boolean Completeness holds necessarily, and Boolean Completeness fails at the binary individual relation type.

## The action on individuals and relations

Let $I=\mathbb N\times\omega_1$. There is one raw pair of labels $(k,i,b)$, $b\in\mathbf F_2$, for each $(k,i)\in I$. The group $G=\mathbf F_2^I$ acts on these pairs by addition to the last coordinate. Choose an ultrafilter on $I$ extending the cocountable filter. Put $\chi(g)=\lim_{\mathcal U}g(k,i)$. Since the range is the finite discrete group $\mathbf F_2$, $\chi$ is a homomorphism. For every countable $P\subseteq I$, the element which is zero on $P$ and one on its complement has $\chi(g)=1$.

There is one object. Its arrows form the free monoid $M$ on a letter $h$ and an infinite set of additional letters, large enough for the chosen signature. Write $vk$ for the composite that follows $k$ and then $v$. Associate to $h$ the endomorphism of $G$ given by

$$\beta_h(g)_{0,i}=\chi(g),\qquad \beta_h(g)_{m+1,i}=g_{m,i}.$$

Associate the identity to every other letter, and put $\beta_{vk}=\beta_v\beta_k$. Write $K_P$ for the permutations which are zero on the countable pin $P\subseteq I$.

An individual is an array $a$ assigning a raw label to every word. Set $(ga)(v)=\beta_v(g)a(v)$ and $(T_k a)(v)=a(vk)$. Admit exactly the arrays for which **every** $T_k a$, including $a$ itself, is fixed by some $K_P$. The pin may depend on $k$.

Inductively at a relational type admit profiles $F$ with one tuple row $F_v$ at each word, with the same requirement on all their suffix restrictions. The group action on the rows is

$$(gF)_v=\beta_v(g)[F_v],\qquad (T_kF)_v=F_{vk},$$

using the already constructed action on the input tuple. At type $t$ there is no tuple input and the carrier is all of $\mathcal P(M)$. Transport in the action model is $T_k$ and application reads the current row at the empty word.

These domains are closed under transport by their definition. On all entities $T_k(gF)=\beta_k(g)T_kF$ by composition of the $\beta$ maps. Since $G$ is abelian, acting by $\beta_k(g)$ preserves support by any $K_P$. Hence the domains are closed under the group action as well. The logical operations commute with the action: at each word the transported parameters and the tuple are transformed by the same group element, which permutes the entire domain of bound variables. Boolean operations, equality, modal evaluation and quantification consequently preserve this equivariance. For a lambda, the union of the pins of its parameters supports its profile; at any suffix use the pins of the transported parameters there. This gives a hereditarily admitted profile for the lambda and the usual commutation with transport. Equality of relation profiles is equivalent to equality of all rows at all words.

## Gluing the signature

The pure theory is constant because there is one object. For each realized pure matrix and finite variable-type list choose one actual witnessing tuple. There are countably many matrices and type lists. For each matching tuple of distinct names assign its occurrence of the matrix a separate letter $j\ne h$. For a participating constant prescribe its row or individual value at $vj$ by the value of its designated witness at $v$. Give it bottom rows elsewhere at relational types. At individual type use a fixed default array $a(v)=(\#_h(v),i_0,0)$ on all remaining words, where $\#_h$ counts occurrences of $h$. Its pin is the single coordinate $(0,i_0)$; its suffixes have the corresponding shifted single-coordinate pins.

For a fixed name only countably many distinct witness entities enter these prescriptions, even if the signature has uncountably many names. Their pins and the default pin have countable union. This supports the prescribed profile at the empty word since $\beta_{vj}=\beta_v$. At a nonempty suffix the final letter is already fixed: the suffix restriction is a transported witness or a transported default. Hence the interpretation of every constant is admitted, including individual constants. At its designated letter a named tuple transports to the entire witness. This proves Logical Necessity for the chosen signature. [Free-word gluing in an action model](free-words-supported-pair-flips.html)

## The unary atom

For $i<\omega_1$ and $b\in\mathbf F_2$ put $x_{i,b}(v)=(\#_h(v),i,b)$. These are admitted individuals. The ordinary group action sends $x_{i,b}$ to $x_{i,b+g_{0,i}}$. Fix $i_0$ and let $Q$ have precisely the pair $\{x_{i_0,0},x_{i_0,1}\}$ at the one-letter word $h$, and empty rows elsewhere. The pair is invariant under every group element. All suffixes are admitted, so $Q$ belongs to the domain.

A nonzero part of $Q$ must contain at least one of these two individuals in its $h$-row. If it contained exactly one, an element $g$ fixing its entire source pin with $\chi(g)=1$ would exchange the two individuals at that row: $\beta_h(g)_{0,i_0}=\chi(g)$. Thus no such part is admitted and $Q$ is an atom. Its transport $T_hQ$ has the whole pair at the identity and is empty at the proper words. There the identity-only singleton of either individual is admitted using the one-coordinate pin $(0,i_0)$. Hence $T_hQ$ is instantiated and is not an atom. This refutes the all-type principle that atoms are self-atoms.

At type $t$, the singleton word propositions are all admitted. Right cancellation makes each transport of one of them either another singleton word or bottom. They are strong atoms and cover every nonzero proposition. The identity-word singleton also gives Strong Actuality. These verdicts hold at every point of the one-object model.

## Ordinary atomicity at all types

Take any $\bar a\in F_w$ and let $T$ be a countable pin fixing its tuple. For every factorization $w=vk$ choose a countable $P_k$ pinning the whole transported relation $T_kF$. Enlarge it by the pairs $(m-\#_h(v),i)$ for $(m,i)\in T$ with $m\ge\#_h(v)$. Each subgroup $\beta_v(K_{P_k})$ preserves $F_w$. On the previously specified tuple pin $T$, its permutations are zero on the levels $m\ge\#_h(v)$; at each lower level the flip is a single bit shared by all labels $i$. This follows by iterating the definition of $\beta_h$.

There are only finitely many factorizations of $w$. The subgroup generated by all these subgroups therefore has only finitely many possible restrictions to $T$. Since agreement on $T$ gives the same image of $\bar a$, the orbit $O$ of $\bar a$ is finite and contained in $F_w$. Take the profile assigning just $O$ at $w$ and nothing elsewhere. For $w=vk$ its $k$-restriction is fixed by $K_{P_k}$, since the generating subgroup contains $\beta_v(K_{P_k})$. Other suffix restrictions are bottom. Thus the profile is admitted. Its nonempty admitted subprofiles form a nonempty finite set under inclusion, so one of them is a minimal nonzero subrelation of $F$. This proves ordinary Atomicity at each relational type.

## Joins

The standard numeral denotations at any sort form an available current inductive set: the identity-only profile for this set is fixed by $G$, since all standard numeral terms are pure. Thus an internally countable family is externally at most countable. Its rowwise union is admitted, since at every suffix the countably many constituent profiles have a countable union of their pins. This gives necessary Countable Boolean Completeness. At type $t$ every external union is a proposition.

For each $i\ne i_0$ take the binary property $F_i$ whose only row is at $h$, consisting of $(x_{i_0,b},x_{i,b})$ for the two equal bits $b$. Define $B_i$ at the same word by taking opposite bits. Every $F_i$ and $B_i$ is invariant as a whole at the source: at $h$ the new-level bit added to both entries is $\chi(g)$. After transport to the identity row the two coordinates $(0,i_0),(0,i)$ pin each relation. The current-only family with extension $\{F_i:i\ne i_0\}$ is therefore admitted. Every $\neg B_i$ bounds this family. A least upper bound $L$ would have to include every equal-bit pair at $h$ and omit every corresponding opposite-bit pair there. Choose $i\ne i_0$ outside a countable pin for $T_hL$ at level zero. Flipping only $(0,i)$ preserves this pin but exchanges the required truth values at the identity row of $T_hL$. Hence the family has no join at type $eet$.

## The propositional and relational Barcan formulas

At type $t$, every suffix transport $T_k$ is onto. For any set $A$ of words, take the proposition $\{vk:v\in A\}$; right cancellation gives exactly $A$ after transport along $k$. Thus any tester necessarily holding of every current proposition holds of every proposition at every continuation. This proves Barcan at $t$. The proposition domain is infinite, and every finite collection of propositions is represented by a current predicate, since the group acts trivially on propositions. The inductive test for precisely the standard numeral values described above shows that no current Frege number counts the whole proposition domain. This gives the Axiom of Infinity at $t$. Both statements hold necessarily because there is one object and they are pure.

Barcan fails for the input type $et$. Let $I_b$ be the unary property with just $x_{i_0,b}$ in its identity row and empty rows elsewhere. Both $I_b$ are admitted. If $F$ is any source unary property pinned by $P$, then $T_hF$ is fixed by every $\beta_h(g)$ with $g\in K_P$. One such $g$ has $\chi(g)=1$, so $\beta_h(g)$ exchanges $I_0$ and $I_1$. Consequently neither can be $T_h F$. Define a tester on unary properties by using the full row at every word except $h$, where its row excludes precisely $I_0$ and $I_1$. The pair is invariant as a set, so the tester and all its suffixes are admitted. Every current unary property necessarily passes, but $I_0$ fails the test at $h$. These arguments were independently checked by two other OpenAI Codex (GPT-6) research agents, prompted by Daniel Kodsi, on 27 November 2026.
