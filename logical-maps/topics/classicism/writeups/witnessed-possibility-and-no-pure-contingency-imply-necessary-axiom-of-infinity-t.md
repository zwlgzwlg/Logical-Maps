# Witnessed Possibility and No Pure Contingency imply the necessary Axiom of Infinity at type $t$

For every internal finite number $n$, there is a current proposition with exactly $n$ possible truth-value alternations, with either initial truth value prescribed. This holds necessarily. It implies the necessary Axiom of Infinity at type $t$, which excludes a finite count of all propositions at every accessible point. This also answers the question whether Converse Witnessed Possibility and Possibly Witnessed Possibility entail necessary Potential Infinity at type $t$. Work in C, with the map's standing assumption of at least one relational signature constant. The proof is by OpenAI Codex (GPT-6), prompted by Daniel Kodsi, 26 November 2026.

For a proposition $p$, consider how many times its truth value can alternate along a sequence of accessible points. The proof uses a property of propositions that detects an exact number of alternations. The number can be nonstandard. Two facts make this possible. First, bounded initial segments of the realized internal numbers are weakly inextensible. Second, a single higher-order formula iterates the two modal tests for one further alternation, with a value that can be tracked under transport. All inductions below are applications of the native impredicative definition of finite cardinality.

## 1. Bounded initial segments

Write $N(n)$ for $n\in\mathbb N_t$, $S$ for the Frege successor, and $R(n)$ for $\exists X\, .\,nX$. Say $a$ *fits* $b$, written $a\preceq b$, when $\exists X,Y\, .\,bX\land aY\land Y\subseteq X$, using inclusion of current extensions. We use the arithmetic facts in Background [Cardinality, arithmetic and analysis](https://github.com/zwlgzwlg/Logical-Maps/blob/4bb9287187ed7cb09567eb3a6302cb896c986ec4/logical-maps/topics/classicism/background/arithmetic.md#L229). Finite cardinalities respect current coextension. A finite count persists as a number. A member can be added to or removed from a finite property according to the successor equations. No proper subproperty of a finite property has its count. Two finite numbers that could count the same property are identical.

For $N(n)$ put $C_n(k):=N(k)\land R(k)\land\neg(n\preceq k)$. Then

$$C_0(k)\leftrightarrow\bot,\qquad C_{Sn}(k)\leftrightarrow C_n(k)\lor(k=n\land R(n)).$$

The empty subproperty fits every realized $k$. If $Sn$ fits $k$, removing one member makes $n$ fit $k$. Conversely suppose $nY$, $kX$ and $Y\subseteq X$. A member of $X$ outside $Y$ makes $Sn$ fit $k$ by addition. If there is none, $n$ and $k$ count the same property and are identical. Finally $Sn$ cannot fit $n$. Removing a member from its witnessing subproperty would give a proper $n$-counted subproperty of an $n$-counted property. These recursions hold wherever $n$ is finite, hence throughout the cone of a point where $n$ is finite.

**Lemma 1.** If $N(n)$ and $R(n)$, $C_n$ is weakly inextensible. If each of its current members necessarily satisfies a tester $Y$, then necessarily every member satisfies $Y$.

*Proof.* Induct on $n$ with the conditional $R(n)$ in the induction predicate. The empty predicate satisfies the claim. Realization of $Sn$ gives realization of $n$, so the induction hypothesis applies. The predicate $k=n\land R(n)$ is weakly inextensible here. A tester necessary on its current members is necessary of $n$ and therefore covers every later member, even if $n$ ceases to have instances. Taking the union of two weakly inextensible predicates preserves weak inextensibility by applying their two clauses to the same tester. Use the successor recursion. $\square$

Let $H$ be any definable predicate of realized finite numbers. If some $H$-number exists here, then the following pure sentence is possible whenever $H$ is pure and parameter-free:

$$M_H:=\exists h\, .\,H(h)\land\Box\forall m\, .\,\bigl(H(m)\to h\preceq m\bigr).$$

To see this, put $P(k)=\Diamond H(k)$. If $R(n)$ and a predicate meets $C_n\cup\{n\}$, it has a member $m$ there, with $R(m)$ and no member in $C_m$. This follows by induction on finite $n$. At zero take zero. At a realized successor use the induction hypothesis if the predicate meets its cut $C_{Sn}=C_n\cup\{n\}$, and otherwise use $Sn$. Start with a current $H(n)$ and apply this argument to $P$. Then $\Diamond H(m)$ and each current member of $C_m$ necessarily fails $H$. Lemma 1 gives $\Box\forall k\, .\,\bigl(C_m(k)\to\neg H(k)\bigr)$. That box persists at the point witnessing $H(m)$. Each later $H$-number is finite and realized, so it admits $m$ as a subcount, as asserted.

## 2. Iterating the modal tests

Use bits $b\in\{0,1\}$, with $p_0=\neg p$ and $p_1=p$. Code a pair of propositions $z$ at type $tt$ by giving it the desired entries $z_0,z_1$ at the necessarily distinct inputs $\bot,\top$, using equality tests and value $\bot$ otherwise. Use this fixed constructor for every pair. Set

$$z^0(p)=(p_0,p_1),\qquad f_p(z)_b=p_b\land\Diamond z_{1-b}.$$

Let $O_p(n,z)$ say that every relation on pairs of a cardinality and a $tt$ entity which contains $(0,z^0(p))$ and is closed under $(k,y)\mapsto(Sk,f_p(y))$ contains $(n,z)$. This is an impredicative formula at one fixed type. It has the indicated base and step laws, and $O_p(n,z)$ entails $N(n)$. Every pair in $O_p$ is the base or the image of a pair in $O_p$. Indeed the collection of those base and image pairs is contained in $O_p$, contains the base and is itself closed under the step. Use it in the definition of $O_p$.

**Lemma 2.** For each finite $n$ there is $z$ with $\Box O_p(n,z)$. Whenever $R(n)$ holds, the value of $z$ satisfying $O_p(n,z)$ is unique.

*Proof.* For existence take the base pair and apply the necessitated step law to its persistent witnesses, by induction on $n$. Both boxed laws are necessitations of theorems of C, with their parameters universally closed. For uniqueness induct on $n$ conditionally on $R(n)$. Zero is never a successor. For a realized $Sn$ any predecessor index $k$ coming from an $O_p$ pair is finite and satisfies $Sk=Sn$. Remove a member from a common instance of these successors. Then $k$ and $n$ have a common instance, whence $k=n$. Also $n$ is realized. The induction hypothesis identifies the predecessor pair, so its image is unique. $\square$

For a realized finite $n$ write $A_n^b(p)$ for the entries of this unique pair and put $L_n=A_n^0\lor A_n^1$. Define $A_{n+1},A_{n+2}$ at the same object by one and two applications of $f_p$ to that pair, even before proving realization of the successor indices. When they are realized these entries agree with their unique pairs by Lemma 2. Set $E_n^b=A_n^b\land\neg A_{n+1}^b$ and $E_n=E_n^0\lor E_n^1$. Under these conventions $E_n$ is a proposition at the current object. To express the truth of $E_n$ in a formula, existentially quantify $z$ with $O_p(n,z)$ and evaluate the indicated Boolean expression at $z$. For statements about its transport we choose the persistent witness in Lemma 2, whose transported value is uniquely determined wherever the transported $n$ is realized.

## 3. Exact alternation layers in the proposition algebra

The following inequalities hold in the Boolean algebra of propositions at an object for any realized finite indices in the statements.

1. $A_n^b\le p_b$ and $A_{n+1}^b\le A_n^b$. At zero the latter inclusion follows from the bit conjunct of $f_p(z^0)_b$. The operation $f_p$ is monotone in the entries, giving the induction step. In particular $E_n=L_n\land\neg L_{n+1}$.
2. $\Diamond L_n=L_n$, also for $L_{n+1}$. At zero $L_0=\top$. A point seeing $A_{n+1}^b$ sees $A_n^{1-b}$ by transitivity and sees $A_n^b$ by part 1. Its present bit gives the corresponding disjunct of $L_{n+1}$. The reverse inclusion is T.
3. $E_{n+1}^b\le\Diamond E_n^{1-b}$. The positive conjunct in $E_{n+1}^b$ gives $\Diamond A_n^{1-b}$. The negative conjunct and the present bit $b$ give $\neg\Diamond A_{n+1}^{1-b}$. Thus an accessible point witnessing the former is in $E_n^{1-b}$. This argument uses the two extra applications of $f_p$ just defined.
4. If $h\preceq m$, then $L_m\le L_h$ and $E_m\le\Diamond E_h$. Induct on $m$, with $h$ arbitrary. A finite number fitting zero itself counts the empty property, so is zero. For $m=h$ use equality and T. If $m=Sk\ne h$, a subproperty of count $h$ inside an $Sk$-counted property is proper. Remove an outside member, obtaining $h\preceq k$. Apply induction, parts 1 and 3, and transitivity of possibility. In addition, when $h\preceq m$ and $h\ne m$, adding an outside member gives $Sh\preceq m$, so $L_m\le L_{h+1}$.
5. If $E_n\ne\bot$, then $R(Sn)$. More precisely, some property counted by $Sn$ consists of propositions all above $L_n$. At zero take $\{L_0\}$. For the step, $E_{n+1}\ne\bot$ implies $E_n\ne\bot$ by part 3. By part 1, $L_{n+1}<L_n$. The property obtained by induction omits $L_{n+1}$, so adjoin it and apply finite cardinal addition. Every member is now above $L_{n+1}$.

## 4. A recoloring that adds one alternation

Fix a current proposition $c$ and a realized finite $h$. Put $q=L_{h+1}(c)$. Suppose $q$ is true and $\Diamond E_h^d(c)$ for a bit $d$. Give $q$ the constant color $1-d$ and keep $c$ unchanged on $\neg q$, producing a current proposition $p'$. Then $p'$ has actual exact rank $Sh$ and $Sh$ is realized.

Indeed $\Diamond q=q$ gives $\neg q\le\Box\neg q$. Two entries which agree on $\neg q$ have possibilities agreeing there. The seed pairs for $p'$ and $c$ agree there, and applying their respective $f$ operations preserves that agreement. Induction on the realized index, with $q$ fixed, gives agreement of their $h$-pairs on $\neg q$. One and two more applications give it for the two further pairs. These are equalities of the restricted propositional entities at the source object.

On $q$ the bit $d$ never holds for $p'$. Outside $q$ its $A_{h+1}^d(p')$ implies $A_{h+1}^d(c)$, hence $q$. Therefore $A_{h+1}^d(p')=\bot$ and $A_{h+2}^{1-d}(p')=\bot$. By part 1, $E_h^d(c)\le\neg q$, so its possibility gives $\Diamond A_h^d(p')$. Since $q$ is true now, the present bit of $p'$ is $1-d$. We have proved that $A_{h+1}^{1-d}(p')$ is true and $A_{h+2}^{1-d}(p')$ is false. In particular $E_{h+1}(p')\ne\bot$, so $E_h(p')\ne\bot$ by part 3. Part 5 gives $R(Sh)$, and the pair computed for $h+1$ really is the unique one at that realized number.

## 5. Witnessing opposite colors at a terminal rank

Let $P(n)$ mean $N(n)\land R(n)\land\exists p\, .\,E_n(p)$ with $E_n(p)$ true at the evaluation point. Put $H(n)=P(n)\land\neg P(Sn)$. Suppose for a contradiction that there is a number $h$ satisfying $H$.

Section 1 gives $\Diamond M_H$. This is a fixed pure sentence, so No Pure Contingency, applied to its negation, gives $M_H$ now. Fix its witness $h$. Whenever a later $m$ satisfies $H$, the transported $h$ fits $m$ there.

For each bit $b$ let $F_b(p)$ say $\exists m\, .\,H(m)\land E_m^b(p)$. Since $P(h)$ holds, some current proposition has exact rank $h$. Complementation reverses its bit and preserves exact rank, as is seen by interchanging the entries in the seed pair, the iteration and its last step. Thus both $F_b$ have current witnesses. Choose a nonindividual signature constant $C$ and put $c=\forall\bar u\, .\,C(\bar u)$, with $c=C$ at arity zero. Each current proposition $p$ is the corresponding universal closure of the constant relation $\lambda\bar u\, .\,p$, since the argument domains are nonempty. Apply ordinary Witnessed Possibility to the two pure formulas $F_b(\forall\bar u\, .\,x(\bar u))$, with just $x$ free. It gives both $\Diamond F_0(c)$ and $\Diamond F_1(c)$ for the **same** $c$.

At either witnessing point take $m$ with $H(m)$ and $E_m^b(c)$. There $h\preceq m$, so the transported $h$ is realized and its persistent pair from the source is the unique local $h$-pair. All computations of $L_{h+1}(c)$ and $E_h^d(c)$ there therefore use the transported source propositions.

* If $m\ne h$ at either witness, part 4 gives $L_m\le L_{h+1}=q$ and $E_m\le\Diamond E_h$ at that witness. Back at the source, $\Diamond q$ gives $q$ by part 2. Transitivity gives $\Diamond E_h$, hence $\Diamond E_h^d$ for some bit $d$.
* If $m=h$ at both, the source has both $\Diamond E_h^0$ and $\Diamond E_h^1$. Choose $d$ opposite to the source bit of $c$. Then $\Diamond A_h^d$ and that source bit give $A_{h+1}^{1-d}(c)$, so again $q$ and $\Diamond E_h^d$.

Section 4 now supplies a current witness to $P(Sh)$, contrary to $H(h)$. We have excluded $\exists h\, .\,H(h)$. Thus $P$ is closed under successor. A constant coloring witnesses $P(0)$, so induction gives $P(n)$ for every internal finite $n$. Complementation again gives exact rank $n$ with either initial bit. The universal assertion is pure, so No Pure Contingency makes it necessary.

There is also a single represented injection $n\mapsto\lambda p.E_n(p)$ from the internal numbers into $tt$. Indeed all numbers are realized, so the Peano conditions and induction give the usual comparison by addition; if $m=n+Sk$, induction on $k$ gives $L_m(p)\le L_{n+1}(p)$, whence $E_m$ and $E_n$ are disjoint as current properties of $p$, and each has an instance.

At any point satisfying the rank assertion, no finite cardinality $a$ can count the universal property of propositions. The finite number $Sa$ has an instance by $P(Sa)$, and removing one member from it would leave a proper $a$-counted subproperty of the universal property. This proves the stated necessary Axiom of Infinity. In total the argument uses two fixed Witnessed Possibility instances and two pure-sentence instances of No Pure Contingency.

## Relational types and the individual type

The infinity conclusion also holds necessarily at every relational type $\tau=\bar\sigma t$. Fix any tuple $\bar a$ of arguments at an object. Evaluation $Y\mapsto Y(\bar a)$ maps the $\tau$-entities onto the propositions there, since $\lambda\bar x.p$ maps to $p$. A property of $\tau$-entities with a finite $\tau$-count has an evaluation image with a finite $t$-count. To prove this, induct on its $\tau$-count. At a successor remove one member. The image of the remainder has a finite count by induction. If the removed member's value is already in the image the count is unchanged, and otherwise the addition lemma gives its successor. The image is an admitted predicate defined by existential quantification and equality. Applied to the universal property at $\tau$, this would give a finite count of all propositions, which the theorem excludes at every accessible object. At type $e$ there is a recorded counterexample: the [full free-monoid model with one individual](full-free-monoid-glued-constants-singleton.html) satisfies Logical Necessity, hence both premises, and has a single individual.
