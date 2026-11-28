# Signature Strong Possibility excludes relational Barcan

For every first-order signature, finite or infinite, signature Strong Possibility refutes one explicit Barcan instance at input type $tt$. Hence signature Strong Possibility and BF at relational types are incompatible in every signature: a signature with a higher-order constant already falls under [Dorr and Fable's Russell–Myhill argument](strong-possibility-signature-r-inconsistent.html). For propositional Barcan, the [general inconsistency theorem](strong-possibility-signature-r-inconsistent.html) settles the full-schema incompatibility. The following construction identifies a particular failed Barcan test at the higher input type.

## A pure test on operators

Let $L(f)$ say that $f^{tt}$ is necessarily a Boolean involution. Explicitly, box the universal closure of preservation of complement and binary meet and of $f(fp)=p$. Write
$$
 B(f)=L(f)\land \forall p^t(fp=p)\land\Box\mathrm{BF}_e.
$$
The middle condition asserts the indicated identities of all currently available propositions. It leaves open whether the same holds for a new proposition at a future point.

Define conjugation at each fixed type by $S_e x=x$, $S_t p=fp$ and
$$
 S_{\sigma\tau}X=\lambda y^\sigma.\,S_\tau\bigl(X(S_\sigma y)\bigr).
$$
These abbreviate native terms; at $e$ this notation simply leaves the argument unchanged. Necessarily under $L(f)$ every $S_\tau$ is an involution. This follows inductively by beta reduction and equality from necessary coextension.

For clarity, this lift preserves the logical constants even when ordinary Barcan fails at higher types. A Boolean involution preserves top and material implication and is its own modal dual. It therefore satisfies N and K, and B is $p\to f(fp)$. Under $L(f)$ these hold necessarily. Prior's Barcan argument for an NKB operator gives $\forall x\, f(Rx)\to f(\forall x\,Rx)$ at every input type. The reverse implication follows from the necessary individual instances of universal elimination and preservation of order. Applied at each future point this is equality of the corresponding scalar terms. [Prior's argument and Corollary D6](../index.html#background/varieties/box5-barcan)

The operator fixes the identity proposition $x=y$ at every type. If the entities are equal, the identity is necessary and N applies. For the other sign, B and the necessary implication $fp\to\Diamond p$ give $p\to f(\Diamond p)$; the latter implication follows by contraposing $\Box\neg p\to f(\neg p)$. With $p=(x\ne y)$, necessity of identity gives $\Box(\Diamond p\to p)$, so N and K yield $p\to fp$. The complement law now gives both signs at every point. The necessarily bijective lift also preserves and reflects identity of its input entities. Thus $f(x=y)$ and $S_\sigma x=S_\sigma y$ are identical propositions.

Consequently conjugation commutes with all terms when any free arguments and names are conjugated along with them. At application use involutivity on the input; at abstraction compare rows at all future points and all their arguments. Boolean connectives commute by the definition of $L$. At $\forall$ use the preceding quantifier equality and rename via the bijection on its input type. This term induction uses the persistent hypothesis $L(f)$ and the necessary fixing of any particular named entities; it does not assume that the unboxed middle conjunct of $B(f)$ persists.

At a $B(f)$-point each currently interpreted first-order symbol is fixed by its lift. Individuals are unchanged and current scalar entities are fixed by hypothesis. For a predicate $c$ of $k$ individuals, each current tuple $\bar x$ satisfies the identity $f(c[\bar x])=c[\bar x]$. Each such identity is necessary. Iterating the necessarily available ordinary Barcan formula at $e$ gives
$$
 \Box\forall\bar x\,\bigl(f(c[\bar x])=c[\bar x]\bigr).
$$
This proves $S(c)=c$ as an entity, and that identity persists. The argument works for any number of first-order symbols and extra individual markers. In particular every closed first-order-signature term $u:tt$ is fixed at **every** $B(f)$-point. Define the closed pure tester
$$
 C(Y)=\forall f^{tt}\,\bigl(B(f)\to S_{tt}Y=Y\bigr).
$$

## A finite point where the test fails

Take an old full S5 clique on four worlds $W=\{1,2,3,4\}$ with singleton individuals. Whole entities transport identically between the old worlds. Old propositions are subsets of $W$. At every relational type all operations on old inputs with proposition values are available. The permutation $(12)(34)$ of $W$ acts by conjugation on the higher types and is an external automorphism of the full old structure. Let $H$ be the group it generates.

Adjoin a point $v$ with one entrance into the old clique and all its old postcomposites. Its individual is the old singleton. Its relational entities have an arbitrary current row and an old trace equal to an $H$-fixed old entity. Invariance under the external group is preserved by old abstraction on invariant parameters, including quantification over all old arguments; take its current row by ordinary evaluation. An inequality between old traces is detected in the full old clique. These profiles therefore form an action model of C. The singleton individual domain throughout gives $\Box\mathrm{BF}_e$.

An old scalar trace at $v$ is a union of the two $H$-orbits $\{1,2\}$ and $\{3,4\}$. The permutation $a=(12)$ fixes each such union. Its action on old subsets is a Boolean involution commuting with $H$, so is an allowed old trace for $f^{tt}$. Give $f$ the current row which reads the input's current truth. For every current scalar the old trace is unchanged as well as the current bit. Hence $fp=p$ as an entity for each current $p$, and $f$ is a Boolean involution at the identity and throughout the old clique. This gives $B(f)$ at $v$.

For $Y^{tt}$ use the old operation induced by $b=(13)(24)$. It too commutes with $H$. The old trace of $S_{tt}Y$ acts by $aba$. This sends $\{1\}$ to $\{4\}$, whereas $b$ sends it to $\{3\}$. Hence $S_{tt}Y\ne Y$ at $v$, so $\exists Y\,\neg C(Y)$ is C-consistent. Public first-order names can be given any available values in this example. The permutation calculation can also be checked on the sixteen old scalars directly. The two compositions disagree on twelve of them.

## The Maximalist witness and reflection

Use the [signature-definable coalesced root](coalesced-definable-root-signature.html) for the specified first-order signature, including its auxiliary individual marker if needed. Adjoin the above old pointed model to the complete component family. At the root $\Box\mathrm{BF}_e$ fails by ordinary Maximalism: a two-site action with an additional individual at the second point refutes the local formula. Thus all current operators pass $C$ at the identity. At every proper arrow each current operator is given by a single closed descriptor $u$ in the first-order signature with the extra individual names. The term induction proves $C(u)$ there, including at every further old evaluation. The exit to $v$ supplies a new operator that fails $C$. Therefore this one signature-Maximalist point satisfies the closed pure sentence
$$
 D=\bigl(\forall Y^{tt}\, C(Y)=\top\bigr)\land
       \bigl((\lambda Y^{tt}.C(Y))\ne\top_{(tt)t}\bigr).
$$

Signature Strong Possibility supplies $\Diamond_{\ne}D$ for this same signature. The two conjuncts are universal Boolean combinations of typed identities, so their [ND reflection](strong-possibility-signature-and-finite-rigid-bounds.html) yields $D$ at the starting point. Concretely, a current counterexample to $C(Y)=\top$ would be a true disequality; testing with that disequality forces it to remain possible at the intermediate point, contradicting necessity of the displayed identity there. If the tester itself were top, that identity would persist and immediately rule out the second conjunct at the intermediate point.

Thus $C$ holds necessarily of each current $Y$, but the tester is not the top property. This is the failure of the unboxed Barcan formula at input type $tt$. For a signature with any non-first-order constant use the already established inconsistency cited above. This completes the uniform claim.

The failure extends to each individual input type $\tau=\beta_1\ldots\beta_n t$ with at least one relational argument $\beta_i=\bar\gamma t$. Indeed $tt$ is a definable retract of $\tau$. Encode $Y^{tt}$ by the relation with value $Y(\forall\bar z\,X_i[\bar z])$ on its arguments. To decode $Z^\tau$ at $p^t$, take its $i$th argument to be $\lambda\bar z.p$ and universally bind the other arguments. The decoder composed with the encoder is the identity on operators because all domains are nonempty. This also covers empty $\bar\gamma$. Pull $C$ back along the decoder. Every current input then passes necessarily, and encoding the failing operator at the future point still fails the new tester. No such retract is asserted at scalar input.

## Distinctness-preserving possibility of scalar Barcan failure

In the definition of $B(f)$ above, replace $\Box\mathrm{BF}_e$ by local $\mathrm{BF}_e$. With this weaker guard put $M(Y)=\exists f\,(B(f)\land S_{tt}Y\ne Y)$ and $m=\exists Y^{tt}M(Y)$. At any pure Strong Possibility point, or any signature Strong Possibility point for an arbitrary first-order signature, each old $Y$ has $M(Y)=\bot$ while $\Diamond_{\ne}m$ holds. In particular $\Diamond_{\ne}\neg\mathrm{BF}_t$ holds. The movement in this assertion concerns a later operator. It does not refute scalar Barcan at the source.

### The unboxed individual guard

For a public predicate $c$ of individuals the scalar fixing clause gives
$\forall x_1\cdots x_k\,\Box(f(c[\bar x])=c[\bar x])$. Holding
$x_1,\ldots,x_{k-1}$ fixed, apply local individual Barcan to the last
variable. Repeat at the same point, using successively the matrices
with the later variables universally bound. The result is
$\Box\forall\bar x(f(c[\bar x])=c[\bar x])$. It identifies $S_fc$
with $c$ as an entity. The identity persists under every transport.
This is the only step of the term induction that uses individual Barcan.

At the signature descriptor root a guarding $f$ fixes every interpreted
closed descriptor as a whole. To see why it also fixes a root entity
whose current row differs from its descriptor's, induct on type.
Individuals are unchanged, and propositions are fixed by the guard.
For a relation $Y$ pick its closed descriptor $u$. Along every proper
arrow $Y$ and $u$ have identical transports, so the necessary identity
$S_fu=u$ gives agreement there. At the identity arrow, apply the
induction hypothesis to every current argument and to the resulting
lower-type value of $Y$. This gives agreement of the current rows,
hence $S_fY=Y$. The argument on proper exits in the earlier proof
uses the same term induction with the transported descriptors. Thus
the descriptor root satisfies $\forall Y(M(Y)=\bot)$. Its universal
identity form transfers to the corresponding Strong Possibility point.

### A Maximalist point with a moved operator

Let $K$ be a pointed signature Maximalist model with local individual
Barcan, for example the pinned-interpretations root. Use its entire
cone as one component and a full four-world S5 clique with singleton
individuals as a second. At a new root use the individual carrier of
$K$, mapping identically into $K$ and constantly to the private
clique. At each relational type allow an arbitrary current row, a
whole entity from $K$, and a whole entity in the clique invariant
under $H=\langle(12)(34)\rangle$. Give each public symbol its
interpretation in the $K$ coordinate. An arbitrary invariant choice
is available in the clique. Lambda closure in each coordinate follows
from ordinary evaluation in $K$ and equivariance of clique evaluation
under the external action of $H$.

The new root reaches $K$ and so has signature Maximalism. If every
current individual satisfies a tester necessarily, its transport to
$K$ necessarily holds of each individual of $K$. Local individual
Barcan at $K$ gives the result over that cone. Every individual in
the private component is already an image. This establishes local
individual Barcan at the new root.

Let $f$ read the current bit at the root, be the identity at $K$ and
act by $(12)$ on the clique. It necessarily is a Boolean involution
and fixes every current scalar as a whole, since every current clique
coordinate is a union of $H$-orbits. Take for $Y$ any operation with
private coordinate $(13)(24)$. Its conjugate by $f$ differs on the
private clique, so $m$ holds at this Maximalist root. Thus Strong
Possibility gives $\Diamond_{\ne}m$ at the original point. At every
$m$-point local scalar Barcan fails. Otherwise $\forall p(fp=p)$
would give $\Box\forall p(fp=p)$ by scalar Barcan and necessary
identity, making $f$ the identity and $S_fY=Y$.

## Intensional Choice

Dorr’s October result already excludes local Intensional Choice under ordinary pure Maximalism, using an individual parameter. The same construction here supplies a single closed pure property of operators under either pure or signature Strong Possibility. [Dorr’s individual-type argument](../index.html#result/maximalism-incompatible-with-intensional-choice) For each fixed relational type $\tau$, abbreviate the tester $\forall f(B(f)\to S_\tau Z=Z)$ by $C_\tau(Z)$. At the corresponding descriptor Maximalist root every current $Z$ satisfies $C_\tau(Z)=\top$. This universally quantified identity reflects as above, so every actual $Z$ at the Strong Possibility source passes its typed test necessarily. Only the first conjunct of the preceding reflection is needed here. For pure Strong Possibility use the pure signature and its single auxiliary individual marker. For a higher-order public signature the established inconsistency applies.

For $Y:tt$, let $M(Y)=\exists f(B(f)\land S_{tt}Y\ne Y)$ and put
$$
 T(Y)=M(Y)\lor\neg\exists Z^{tt}\,M(Z).
$$
This pure property is necessarily instantiated by classical logic and nonemptiness of the type. Suppose some current $G\le T$ selects exactly one member necessarily. Pure Maximalism gives a point with $\exists Z\,M(Z)$ since the finite four-world construction realizes this sentence at $v$. Let $y$ be the transported $G$'s unique member there. Since $G\le T$, some guarded $f$ moves $y$. On the other hand the transferred property $G$ passes $C_{(tt)t}$ at this point. Hence $S_{(tt)t}G=G$, which gives $G(S_{tt}y)=f(Gy)$ by application and involutivity. The guard fixes every current scalar as an entity, including $Gy$. Thus $S_{tt}y$ is a second selected member, a contradiction. This excludes just one fixed instance with the parameter-free property $T$.

OpenAI Codex (GPT-6), prompted by Daniel Kodsi, 27 November 2026. Independent GPT-6 researchers reviewed the finite action, the conjugation argument and the uniqueness obstruction. Lean also checks the Boolean involution, typed quantifier and identity facts, unique selection, and the derivation from the reflected tester to the failure of Barcan at input type $tt$. The construction of the witness to the consistency side condition and the structural induction on descriptors are ordinary mathematical arguments. [Lean proofs](../lean/Classicism/Results/Research/FixedOperatorBarcan.lean) · [Object-language derivations](../lean/Classicism/Results/Research/FixedOperatorBarcanCertificates.lean)
