# Necessary Countable Boolean Completeness implies Arithmetic Necessitism

Fix any type $\sigma$, including $e$. Write $N$ for the property of being a
finite Frege cardinality at $\sigma$, $\nu=(\sigma t)t$ for its argument
type, and $s$ for numerical successor. Necessary Countable Boolean
Completeness makes $N$ rigid. If $\Box I^*_\sigma$ also holds, distinct
current numbers are necessarily distinct. Together these are the map's
Arithmetic Necessitism at $\sigma$.

The three ingredients are Lemmas 3, 4 and 8 of Zachary Goodsell,
*Arithmetic is Necessary*, draft of 5 June 2024. The map's existing
[proof of his Theorem 9](countable-boolean-completeness-implies-necessity-of-arithmetic.html)
includes the relevant lemmas. This record applies them to the map's
entity-level principle.

1. By Lemma 3, $\forall n\,(Nn\to\Box Nn)$ is a theorem of C, by induction
   using $\lambda n\,\Box Nn$. Its necessitation gives persistence of $N$.
2. At the evaluation point, the family of singleton predicates
   $H_n=\lambda k\,(k=n)$ for current numbers $n$ is countable at $\sigma$.
   The graph of $H_n\mapsto n$ is a typed relation. Countable Boolean
   Completeness supplies their join $Z$ in the entailment order at $\nu t$.
   Thus $\Box Z0$ and $\Box Z(sn)$ for every current number $n$.
   The latter makes $\lambda k\,Z(sk)$ an upper bound of the same family,
   so $\Box\forall k\,(Zk\to Z(sk))$. Induction inside the box gives
   $\Box\forall k\,(Nk\to Zk)$. Every tester $X$ necessarily had by each
   current number is another upper bound, so $Z\le X$ and
   $\Box\forall k\,(Nk\to Xk)$. This is weak inextensibility of $N$
   (Lemma 8). Necessitate the implication from the fixed countable
   completeness instance at $(\sigma,\nu t)$ and apply K. Its boxed
   premise therefore gives full inextensibility of $N$.
3. By Lemma 4, distinct current numbers satisfy
   $\Box(I^*_\sigma\to m\ne n)$. The definition of Arithmetic Necessitism
   supplies the antecedent $\Box I^*_\sigma$, so K yields
   $\Box(m\ne n)$.

The rigidity conclusion holds even when $\Box I^*_\sigma$ fails. Only
the distinctness assertion uses that antecedent. The stronger premise of
necessary Boolean completeness immediately suffices by restriction to the
countable instances.
