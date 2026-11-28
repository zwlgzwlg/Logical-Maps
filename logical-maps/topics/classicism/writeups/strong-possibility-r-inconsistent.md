# Strong Possibility (pure) ⇒ ⊥

<a id="unary-proof" name="unary-proof"></a>

## A unary diagonal

[Four-page typeset proof](../sources/strong-possibility-inconsistency.pdf)

**Theorem.** There are two closed pure sentences $K$ and $H(K)$ such that, in the pure language and in every admitted signature $\Sigma$,

$$
\begin{aligned}
&\mathrm{Max}(C_\Sigma)+K \text{ is consistent},\\
&\mathrm{Max}(C_\Sigma)+H(K) \text{ is consistent},\\
&C_\Sigma\vdash\neg\bigl(DK\land D H(K)\bigr).
\end{aligned}
$$

Write $C_\Sigma$ for Classicism in the language $\Sigma$. Its ordinary Maximalist theory $\mathrm{Max}(C_\Sigma)$ adds every $C_\Sigma$-consistent closed disequality. Strong Possibility (SP) asserts $DP$ for each closed sentence $P$ consistent with that theory. The first two claims therefore give the two instances of SP contradicted by the third.

### The contradiction

Write $D=\Diamond_{\ne}$. Its return condition is

$$
DP\ \longleftrightarrow\ \forall q^t\thinspace \bigl(q\to\Diamond(P\land\Diamond q)\bigr).
$$

For any proposition $q$ true at $w$, this gives arrows $w\to v\to u$ with $P$ true at $v$ and $q$ true at $u$. Parameters in $q$ travel along those same arrows. Equality persists along every arrow.

**First sentence.** Put $K=\forall x^e y^e\thinspace (x\ne y\to\Diamond\Box(x\ne y))$. We claim $DK\to K$. Fix $x\ne y$ at $w$ and use $q=(x\ne y)$ in the return condition. The pair is distinct at $u$, hence at $v$, since equality at $v$ would persist to $u$. Apply $K$ at $v$ to this pair. There is an arrow $v\to z$ with $\Box(x\ne y)$ at $z$. Composing $w\to v\to z$ gives the required $\Diamond\Box(x\ne y)$ at $w$.

**Second sentence.** Let $S=e\to t$ and $T=S\to t$. Thus $p:S$ is a unary predicate and $F:T$ tests a unary predicate. For now take any pure term $Q:e\to T\to S$ and write $Q_bF=(Q(b))(F)$. Define

$$
\begin{aligned}
\rho_b(p)&\equiv\exists F^T\thinspace (Q_bF=p\land\neg F(p)), &d_b&=Q_b\rho_b,\\
H(g)&\equiv\forall b^e\thinspace \forall F^T\thinspace
\bigl(Q_bF=d_b\to\Box(g\to F(d_b))\bigr).
\end{aligned}
$$

At every world and for every $b$, $\rho_b(d_b)$ is true. Indeed, assuming $\neg\rho_b(d_b)$ supplies a witness to $\rho_b(d_b)$, namely $F=\rho_b$. Unfolding its truth now gives a tester $F$ with $Q_bF=d_b$ and $\neg F(d_b)$. This is the Russell–Myhill step. [Earlier signature argument](strong-possibility-signature-r-inconsistent.md)

**Claim.** $D H(g)\to\neg g$. Suppose $w\models D H(g)\land g$. Choose an individual $b$ and a rejecting witness $F$ as above. Use the single guard $q=g\land\neg F(d_b)$ in the return condition. Along the resulting arrows the same parameters give

$$
\begin{array}{c|l}
w & Q_bF=d_b,\qquad g\land\neg F(d_b)\\
v & H(g),\quad Q_bF=d_b,\quad\text{hence }\Box(g\to F(d_b))\\
u & g\land\neg F(d_b),\quad g\to F(d_b).
\end{array}
$$

The identity at $v$ is the transported identity from $w$. The last line is contradictory. Taking $g=K$ proves $DK\land D H(K)\to\bot$. It remains to choose $Q$ and establish the two consistency claims.

### Two ordinary Maximalist models

First work in a finite signature with an individual name $m$ and constants of closed types. Take a complete family of pointed canonical $C_\Sigma$-models $(A_i,w_i)$. Adjoin a root $o$ and one entrance $\varepsilon_i:o\to w_i$ into each component. A *proper exit* is $\varepsilon_i$ followed by any component arrow. The identity and these exits are all the arrows out of $o$.

Use the definable-root construction. An individual $b$ at $o$ has a name $n$ as descriptor. A relation $F$ at $o$ has an arbitrary current extension and a closed term $f$ of its type as descriptor. Writing $(\varepsilon_i)\mathstrut_{\ast}$ for transport and $\lbrack\negthinspace\lbrack  f\rbrack\negthinspace\rbrack\mathstrut_{w_i}$ for the denotation of $f$ at $w_i$, the defining condition is

$$
(\varepsilon_i)\mathstrut_{\ast}b=\lbrack\negthinspace\lbrack  n\rbrack\negthinspace\rbrack\mathstrut_{w_i},
\qquad
(\varepsilon_i)\mathstrut_{\ast}F=\lbrack\negthinspace\lbrack  f\rbrack\negthinspace\rbrack\mathstrut_{w_i}
\qquad\text{for every }i.
$$

In particular, the *same* $f$ determines $F$ on every proper exit. Equality of two unary predicates means agreement along every future arrow on every individual at its target. For an abstraction with parameters, substituting their descriptors gives one descriptor for the abstraction. The definable-root construction therefore gives models of $C_\Sigma$. For each consistent closed disequality $s\ne t$, completeness gives some $w_i\models s\ne t$. If $o\models s=t$, transporting along $\varepsilon_i$ would give $w_i\models s=t$. Thus both roots below satisfy ordinary Maximalism. [Definable-root construction](coalesced-definable-root.md) · [Signature version](coalesced-definable-root-signature.md)

**A root satisfying $K$.** Give each individual name exactly one representative. Distinct root individuals have different names $i,j$. A one-world classical model can interpret them differently and hence satisfies $\Box(i\ne j)$. By completeness there is an entrance witnessing $\Box(i\ne j)$ for this pair. Thus $o\models K$. For the pure theorem we can use just the auxiliary name $m$. In that case the root has one individual and $K$ holds vacuously.

**A root satisfying $H(K)$.** Give each name $n$ two representatives $n_0,n_1$ with the same descriptor $n$. The pair $m_0,m_1$ is distinct at $o$ and equal at every proper exit. No reachable world makes it permanently distinct, so $o\models\neg K$. The remaining property of $Q$ we need is the following.

**Separation lemma.** For every individual name $n$ and closed tester $f$,

$$
\bigl(\exists i\thickspace \exists (w_i\to z)\thickspace  z\models\neg f(d_n)\bigr)
\quad\Longrightarrow\quad
\bigl(\exists j\thickspace  w_j\models Q_nf\ne d_n\bigr).
$$

The two components $i,j$ may differ. The rejecting world $z$ supplies the input for the construction of the world that distinguishes the outputs.

To see why this suffices, take any $b,F$ at the doubled root with $Q_bF=d_b$ and let $n,f$ be their descriptors. Transport gives the first line below. Separation, by contraposition, gives the second.

$$
\begin{aligned}
&\forall j\quad w_j\models Q_nf=d_n,\\
&\forall i\quad w_i\models\Box f(d_n).
\end{aligned}
$$

Thus at every proper exit $F(d_b)$ is true, and at the identity exit $K$ is false. These exhaust the arrows out of $o$, proving $o\models\Box(K\to F(d_b))$ for the chosen $b,F$. This proves $o\models H(K)$ once separation is established.

<a id="unary-reading" name="unary-reading"></a>

### The operator and its two-layer model

To distinguish the two unary outputs $Q_nf$ and $d_n=Q_n\rho_n$, it suffices to find one individual $a$ on which they disagree. We build a world where evaluating either output at $a$ asks whether its tester can reject the old predicate $d_n$. The construction records that predicate in the sizes of the fibres over the old individuals.

For individual parameters $a,b$ define the following pure terms. The variable $x$ ranges over individuals and $r$ over unary predicates.

$$
\begin{gathered}
B \equiv (a=b),\\
L_{a,b}(x)\equiv \exists y^e\thinspace \bigl(x\ne y\land\Box(B\to x=y)\bigr),\\
\mathrm{Code}_{a,b}(r)\equiv
(r=\lambda x.\Diamond r(x))\\
\qquad{}\land\Box\bigl(\neg B\to\forall x^e\thinspace
(\neg L_{a,b}(x)\leftrightarrow\Diamond(B\land r(x)))\bigr),\\
(Q_bF)(a)\equiv\Diamond\bigl(\neg B\land\exists r^S\thinspace
(\mathrm{Code}_{a,b}(r)\land\Diamond(B\land\neg F(r)))\bigr).
\end{gathered}
$$

The first possibility in $Q$ chooses a world with distinct markers and a predicate $r$ there. The second chooses a later world with equal markers and tests the transported $r$. Every output $p=Q_bF$ satisfies $p=\lambda x.\Diamond p(x)$, since $\Diamond\Diamond A\leftrightarrow\Diamond A$ everywhere. Also $\neg p(b)$ holds everywhere, since equal markers stay equal. In particular both facts hold for $p=d_b$.

**Reading lemma.** Fix an old pointed model $(A,w)$ with individual name $n$. There is an extended model with a new world $\widehat w$ and a single individual $a$ there such that for **every** closed tester $f$,

$$
\widehat w\models (Q_nf)(a)
\quad\Longleftrightarrow\quad
w\models\Diamond\neg f(d_n). \tag{1}
$$

**Construction.** Set $p=\lbrack\negthinspace\lbrack  d_n\rbrack\negthinspace\rbrack\mathstrut_w$. An old arrow $h:w\to z$ indexes an upper world $\widehat h$ over $z$. Write $p_h(u)$ for the value of $h_{\ast}p$ at $u\in A_e(z)$. The individuals over $u$ at $\widehat h$ are

$$
\begin{cases}
u_0 &\text{if }p_h(u),\\
u_0,\ u_1 &\text{if }\neg p_h(u).
\end{cases}
$$

Each $k:z\to z'$ induces an upper arrow $\widehat h\to\widehat{kh}$ and an exit $\widehat h\to z'$, where $kh=k\circ h$. Upper arrows send $u_j$ to ${(k_{\ast}u)}\mathstrut_{j}$. This is well defined: $p_{kh}(k_{\ast}u)$ would imply $p_h(u)$ by possibility-fixity, so a second copy, once present, persists upstairs. Exits send both copies to $k_{\ast}u$. Lower worlds retain their original domains and arrows. At $\widehat w=\widehat{1_w}$ interpret $n$ by the first copy of its old denotation and take $a$ to be the second. It exists because $p(n)$ is false. Thus $B=(a=n)$ is false upstairs and true on every exit downstairs.

At relational type $\bar\sigma\to t$, an upper entity at $\widehat h$ consists of arbitrary rows on upper arrows, with arguments from the target domains, and one admitted old entity at $z$ giving all its exit rows. This defines the carriers recursively on type. Upper transport restricts the rows by composition and transports the old entity. The immediate exit to $z$ recovers that entity. Interpret other individual names by first copies and relation names by empty upper rows with their old entity downstairs. At a schematic type variable retain the old carrier and transport. For term closure, an abstraction has arbitrary permitted upper rows, and downstairs its value is the old abstraction on the projected parameters. This gives the required values also on arguments first appearing at a later world. Two unequal upper entities are distinguished by an upper row or by an old observation after an exit.

### Reading the predicate and proving separation

Let $\pi(u_j)=u$. Upstairs $\Box(B\to x=y)$ holds exactly when $\pi(x)=\pi(y)$: the immediate exit tests the two projections, and equal projections stay equal on every further exit. Hence $L_{a,n}(x)$ says that $x$ has a distinct copy over the same individual. The construction gives, for every upper world and every individual there,

$$
\widehat h\models\neg L_{a,n}(u_j)\quad\Longleftrightarrow\quad p_h(u).
$$

Suppose $\widehat h\models\mathrm{Code}_{a,n}(r)$ and let $r^\downarrow$ be its old component at $z$. Take **any** $k:z\to z'$ and **any** $u\in A_e(z')$. Evaluate the boxed conjunct of $\mathrm{Code}$ on the first copy $u_0$ at $\widehat{kh}$. It gives

$$
\begin{aligned}
p_{kh}(u)
&\ \Longleftrightarrow\ \widehat{kh}\models\Diamond(B\land r(u_0))\\
&\ \Longleftrightarrow\ z'\models\Diamond\bigl((k_{\ast}r^\downarrow)(u)\bigr)\\
&\ \Longleftrightarrow\ z'\models(k_{\ast}r^\downarrow)(u).
\end{aligned}
$$

The middle equivalence uses the description of exits. The last uses $r=\lambda x.\Diamond r(x)$ transported downstairs. Equality for every $k,u$ is precisely equality of the two old unary intensions, so $r^\downarrow=h_{\ast}p$. Conversely, the upper interpretation of the term $d_n$ has old component $h_{\ast}p$ by term closure and is possibility-fixed because it is an output of $Q_n$. The same equivalences verify its boxed code condition. Thus a passing code exists at every upper world.

This proves (1) in both directions. A witness to $(Q_nf)(a)$ must choose a passing $r$ upstairs and then cross to an old world. There $f$ rejects the transported $p$, giving the right-hand side. Conversely, given an old rejection reachable from $w$, take $r=d_n$ at $\widehat w$ and cross along that very arrow.

To finish separation, take a rejecting old world as $w$. Apply (1) twice at the **same** $\widehat w,a$:

$$
\begin{aligned}
w\models\neg f(d_n) &\ \Longrightarrow\ \widehat w\models(Q_nf)(a),\\
w\models\Box\rho_n(d_n) &\ \Longrightarrow\ \widehat w\models\neg(Q_n\rho_n)(a).
\end{aligned}
$$

The first line uses the identity arrow. The second uses the Russell argument, valid at every old world. Since $d_n=Q_n\rho_n$, the two outputs differ at $a$. Hence $Q_nf\ne d_n$ is consistent, and completeness puts this disequality at a canonical entrance. If $f$ uses schematic type variables, the canonical components supply the required witnesses at those sorts and the upper construction retains their carriers. This proves the lemma. The action semantics and completeness used here are those of Bacon and Dorr, *Classicism*, §§3.5–3.6 and Appendix E in the draft numbering.

<a id="unary-signatures" name="unary-signatures"></a>

### Pure and signature Strong Possibility

Both $K$ and $H(K)$ are closed and pure: $b$ is bound in $H$, and the definitions of $Q,\rho,d$ use no names. For the pure case one auxiliary individual name suffices to construct the two models. Forgetting that name preserves the two sentences and every pure Maximalist axiom.

For any admitted free signature $\Sigma$, suppose a derivation refuted either sentence over $\mathrm{Max}(C_\Sigma)$. It uses finitely many names and finitely many Maximalist disequalities. Retain these names and add a fresh individual name $m$. Each cited disequality is still consistent with $C$ in this finite language: a proof of its opposite equality could be returned to $\Sigma$ by replacing $m$ with a fresh individual variable and using existence at type $e$. The same finite derivation would therefore refute the sentence in a language in which we have constructed its Maximalist model. This proves both consistency claims for $\Sigma$. Applying SP now yields $DK$ and $D H(K)$, and the contradiction above concludes the proof. $\square$

<a id="uniform-pair" name="uniform-pair"></a>

## Earlier proof using atomlessness and a six-place diagonal

**Theorem.** In Classicism there are two closed pure sentences $A_0$ and $\Psi$, each consistent with ordinary pure Maximalism, for which

$$
C\vdash\neg(\Diamond_{\ne} A_0\land\Diamond_{\ne}\Psi).
$$

Consequently pure Strong Possibility is inconsistent. The same two sentences witness the inconsistency of Strong Possibility for every free signature admitted by the map, with both consistency tests taken in that signature.

Here $A_0$ says that the Boolean algebra of propositions is atomless. Write $D=\Diamond_{\ne}$. At a $DP$-point, each currently true proposition can still be made true after reaching a $P$-point. Applying this to a true strong atom shows that $DA_0$ rules out Strong Actuality. To define $\Psi$, the proof uses the Russell–Myhill diagonal at the type of six-place relations on individuals. An auxiliary world for each old arrow and individual tuple tests the entire interpretation of such a relation. This produces a sentence true at a definable Maximalist root whose distinctness-preserving possibility contradicts the diagonal whenever Strong Actuality fails.

OpenAI Codex (GPT-6), prompted by Daniel Kodsi, found the construction and completed the proof on 27 November 2026. Independent GPT-6 researchers checked the native types, full action-model extension, descriptor argument, and the two licences in each signature. The diagonal adapts the earlier [higher-order-signature proof](strong-possibility-signature-r-inconsistent.md) of Cian Dorr and Claude Fable 5.2 (Anthropic), prompted by Cian Dorr. Lean verifies both map statements. The [unary proof](#unary-proof) gives another choice of incompatible possibilities.

## The closed terms

Let $S=e^6t$ denote the type of six-place relations on individuals. Write a tuple of six individuals as $\bar a=(a_0,a_1,b_0,b_1,c_0,c_1)$. With this tuple as parameter define

$$
A=(a_0\ne a_1),\quad B=(b_0=b_1),\quad
T=\neg A\land\neg B\land c_0\ne c_1,\quad
U=\neg A\land\neg B\land c_0=c_1.
$$

Put $x\sim y$ for $\Box(U\to x=y)$. Let $C_i(x)$ say that exactly $i$ current individuals $y$ satisfy $x\sim y$, using the usual finite first-order formula, for $1\le i\le7$. Set $J=\exists x\thinspace C_7(x)$. These formulas all use the same six transported parameters. For $p:S$ put

$$
\begin{split}
\mathrm{Code}(p;\bar a)={}&(p=\lambda\bar v.\Diamond p(\bar v))\\
&{}\land\Box\bigl(T\to\forall v_1\ldots v_6\thinspace [(\bigwedge_{i=1}^6 C_i(v_i))
\to(J\leftrightarrow\Diamond(B\land p(\bar v))) ]\bigr).
\end{split}
$$

Define

$$
\begin{split}
(QF)(\bar a)&=\Diamond\left(A\land\exists p^S\thinspace [\mathrm{Code}(p;\bar a)
\land\Diamond(B\land\neg Fp)]\right),\\
\rho(x)&=\exists F^{St}\thinspace [QF=x\land\neg Fx],\qquad d=Q\rho.
\end{split}
$$

Here $QF$ abbreviates the six-individual lambda abstraction displayed above. Equivalently its uncurried relation takes one input of type $St$ followed by six inputs of type $e$. In particular $d=Q\rho$ is a relation of type $S$. All its output rows are fixed by ordinary possibility: $QF=\lambda\bar v.\Diamond((QF)(\bar v))$ by S4 and intensionality. The Russell–Myhill argument gives $\rho d=\top$. If $\rho d$ were false, $F=\rho$ would make it true. Unfolding the resulting theorem gives

$$
C\vdash\exists F^{St}\thinspace [QF=d\land Fd\ne\top]. \tag{1}
$$

## Testing a marked term

Let $f:St$ be any term closed apart from one freely interpreted individual marker. Suppose $f(d)=\top$ is not provable in marked C. By completeness a countermodel to the identity has an ordinary continuation where the proposition is false. Repointing there, with the transported marker, gives a marked C action model $w$ with $\neg f(d)$. Keep its generated cone unchanged. At $w$ fix the marker's original individual as an anchor.

Adjoin a new root $o$ and an arrow $l:o\to w$. For every old arrow $h:w\to z$, including the identity, and every tuple $\bar u\in D_e(z)^6$, add a fresh object $t=t_{h,\bar u}$, with arrows $i_t:o\to t$ and $k_t:t\to z$. Impose $k_t i_t=h l$. Also add one fresh classical terminal $v_t$ and an arrow $j_t:t\to v_t$. These generators and the old compositions impose all the identifications. In particular every path from $o$ into the old cone factors through $l$, and every path from $t$ into the old cone factors through $k_t$.

Choose a root tuple $\bar a$ with the three pairs distinct at $o$. All six entries go to the anchor under $l$. At each $t$ merge the first pair and keep the other two pairs distinct. At $v_t$ keep only the $b$-pair distinct. Under $k_t$ all six transported root entries map to $h$ of the anchor. Thus $A$ holds only at $o$, $B$ holds precisely in the old cone, $T$ holds at the test objects $t$, and $U$ holds at the private terminals $v_t$, for this choice of $\bar a$.

At $t$ the relation $x\sim y$ is exactly $j_tx=j_ty$. Implement its fibres as follows. For each $i=1,\ldots,6$ create one fibre of size $i$ and send *every* member of that fibre to $u_i$ under $k_t$. Add one fibre of size seven precisely when $d(\bar u)$ is true at the old point $z$. Its elements can go to the transported anchor. Use two further fibres of size eight for the incoming root controls and any fillers. For example take distinct local control representatives except for the already merged $a$-pair. Place the two $b$-representatives in opposite size-eight fibres, the two $c$-representatives in the same one, and send all control representatives to the transported anchor under $k_t$. Use the fibres themselves as distinct terminal individuals, and let $j_t$ send each element to its fibre. This realizes the cardinalities and both required individual compositions. The colour of the optional fibre uses the value of an already defined closed term in the **original** component. Adding predecessors does not enter its interpretation there.

For clarity, the new relations form an action model at every standard type. At a test object $t$ admit an arbitrary current row, one entire $z$-entity, and one entire $v_t$-entity. At $o$ admit an arbitrary current row, an arbitrary current row at each $i_t$, one whole $v_t$-entity per $t$, and one whole $w$-entity. Its value transported to $t$ has the prescribed test row, prescribed private entity, and old entity transported along $h$ from $w$. The terminal hierarchies are full. These descriptions are inductive on types since rows use only lower-type arguments. Distinct entities are separated at their differing row or in a continuation of their differing old or terminal component. Lambda abstraction takes the body row on *all* target arguments at each new row, and takes the native abstraction in the original or terminal cone on transported parameters. Hence every abstract has the prescribed form, including those with new higher-type parameters. The test objects consequently preserve the equation $k_t i_t=h l$ also on higher-type parameters. The marked individual of the new pointed test can be any root individual transported to the original anchor.

## What the code determines

If $p$ satisfies $\mathrm{Code}(p;\bar a)$ at $o$, its old projection equals $d$ as a **whole** $S$-entity at $w$. To check an arbitrary old row choose $h:w\to z$ and any six current individuals $\bar u$ at $z$. At its test object choose a member of the fibre of size $i$ as $v_i$, independently at each coordinate. The antecedent in the code holds. Possibility of $B\land p(\bar v)$ there is precisely possibility of the projected row of $p$ on $\bar u$ at $z$, since the old continuations are exactly those through $k_t$. The first code condition makes that row possibility-fixed. Its possibility therefore equals its current truth at $z$. The colour $J$ is exactly the previously recorded truth of $d(\bar u)$ there. Every old row on every old tuple agrees, proving equality by intensionality.

Conversely $p=d$ passes the code at $o$. Its rows are possibility-fixed by construction. At a test site *every* member of the fibre of size $i$ has the stipulated old image, so the comparison holds for every tuple satisfying the antecedent. The transported selected root parameters disable the comparison everywhere else.

It follows that $(Qf)(\bar a)$ is true at $o$, using $d$ as code and the old $w$ itself for $B\land\neg f(d)$. But $(Q\rho)(\bar a)$ is false. The only possible site satisfying $A$ is $o$ itself. Every passing code equals $d$ throughout the old cone, and $\rho(d)=\top$ throughout that cone. Thus $Qf=d$ is not a theorem of marked C.

Consequently no standard marked term solves (1): whenever a marked term satisfies the required identity, it fails the required disequality in the term algebra.

## The contradiction at a proposed Strong Possibility point

Let $V$ be the standard coalesced definable ordinary pure Maximalist root. Its sole individual supplies the construction's auxiliary marker. Every relational entity there has a closed one-marker term descriptor, evaluated on its marked target at every proper exit. An abstraction with root parameters has as descriptor the same abstraction with their descriptors substituted. Root identities imply provable identities between these descriptors: the components and their possible marker interpretations are complete for marked C. The scalar true only at the identity of the root is a true strong atom. It decides every root proposition there and transports to bottom at each proper exit, so Strong Actuality ($\mathrm{SA}$) holds at $V$. [Descriptor root](coalesced-definable-root.md)

If $QF=d$ holds at $V$, the descriptor $f$ of $F$ satisfies $Qf=d$ provably in marked C. The test just proved gives provable $f(d)=\top$. Consequently $Fd=\top$ holds at every proper exit of $V$. The identity of $V$ satisfies $\mathrm{SA}$, so the following **one pure sentence** is true at this ordinary Maximalist point:

$$
\Psi=\mathrm{SA}\land\forall F^{St}\thinspace
[QF=d\to\Box(\neg\mathrm{SA}\to Fd=\top)].
$$

Pure Strong Possibility excludes Strong Actuality. Indeed there is an ordinary pure Maximalist point with an atomless scalar algebra. If a Strong Possibility point had a true strong atom, use that atom as the true guard in distinctness-preserving possibility of atomlessness. At the intermediate atomless point the transported atom is nonzero since it is true at a continuation. Its necessary decision of every scalar persists, which makes it an atom and gives a contradiction. [Strong-atom obstruction](https://github.com/zwlgzwlg/Logical-Maps/blob/4bb9287187ed7cb09567eb3a6302cb896c986ec4/logical-maps/build/classicism/writeups/strong-possibility-and-strong-actuality-incompatible.md)

At a putative pure Strong Possibility point choose $F$ from (1). The scalar $\neg\mathrm{SA}\land Fd\ne\top$ is true. Apply $\Diamond_{\ne}\Psi$ with that scalar as guard. This gives an intermediate site satisfying $\Psi$ and a subsequent site restoring the guard on the transported parameter. Since identity persists, $QF=d$ still holds at the intermediate site. Its boxed conditional gives $Fd=\top$ at the subsequent site, contrary to the restored guard. This proves inconsistency of pure Strong Possibility.

Explicitly, let $A_0$ be propositional Atomlessness. The strong-atom argument gives $\Diamond_{\ne} A_0\to\neg\mathrm{SA}$ already in C. Hence (1) and the guard above give the pure failed disjunction

$$
C\vdash \Box_{\ne}\neg A_0\ \lor\ \Box_{\ne}\neg\Psi.
$$

Neither $\neg A_0$ nor $\neg\Psi$ is provable in ordinary pure Maximalism. Only these two Strong Possibility instances are needed.

## Extension to an arbitrary free signature

Let $\Sigma$ be any set-sized free signature admitted by the map. Use $\Sigma^+=\Sigma$ when it already has an individual constant, and otherwise add one individual marker. The terms $Q,\rho,d$ and the sentence $\Psi$ remain pure.

The test of a closed $\Sigma^+$-term $f$ works with its constants retained. Start with a marked old point where $\neg f(d)$. Give each relational constant its prescribed old value at $w$, empty new current rows and bottom values at private terminals. At each test object its old component is the transport along $h$ of its value at $w$. For each individual constant add a distinct individual at $o$ with its specified image at $w$. At each $t_{h,\bar u}$ give its image a fresh fibre of size eight, distinct from the control and size-one-through-seven fibres. Send that entire fibre to $h$ of the constant's old value. The image at the private terminal is its fibre. These choices commute with the imposed square and make no new size-seven classes. The control individuals themselves remain separate from the added individuals. The construction works for arbitrarily many constants since the fibres are disjoint and all eight-element fibres are ignored by the six selectors and the colour. The same proof gives

$$
C(\Sigma^+)\vdash Qf=d\quad\Longrightarrow\quad
C(\Sigma^+)\vdash f(d)=\top .
$$

The ordinary signature-Maximalist coalesced descriptor root gives every entity a closed $\Sigma^+$-descriptor and is strongly actual. It therefore satisfies the same pure $\Psi$. The atomless ordinary signature-Maximalist point exists in this same signature, so signature Strong Possibility excludes Strong Actuality and also gives $\Diamond_{\ne}\Psi$. Applying the same single return guard to (1) gives the contradiction for signature Strong Possibility, including first-order signatures and infinite sets of names. [Signature descriptor root](coalesced-definable-root-signature.md) · [Atomless model in the given signature](#an-atomless-ordinary-maximalist-point)

## An atomless ordinary Maximalist point

Fix a pointed ordinary Maximalist model $K,w$ for the given signature, for example the [signature descriptor root](coalesced-definable-root-signature.md). Take two copies $G,X$ of the Cantor space $2^{\mathbb N}$, with $G$ acting as a group by coordinatewise addition modulo two. Add a new root with the individuals of $w$, loops indexed by $G$ fixing all individuals, and an entrance to an independent copy of $K,w$ for each $x\in X$. Each entrance absorbs every loop and acts identically on individuals. Include all old postcomposites.

At each relational type $\tau$ a root entity consists of a locally constant table on $G$ of current rows and an independent locally constant function $X\to D_\tau(w)$ of whole old entities. Both ranges have the discrete topology. Loops right-translate the table and fix the old section. An entrance evaluates the section at its index. Give each relational name a constant table and the constant section of its prescribed old value. Individual names keep their old interpretations. Compactness of Cantor space gives a common finite prefix on which every entry of a finite list of tables depends. Thus the transported parameters of an abstraction are locally constant as whole entities along the loops, and evaluating its body on all current tuples gives another locally constant table. At the entrances the native abstraction on the transported old parameters is likewise locally constant as a whole old entity. This includes quantification over new target arguments. Differences of entities are witnessed on a loop or in a continuation of an old copy. The action therefore validates C, and the entrances retain every ordinary Maximalist possibility in the given signature.

At scalar type every nonzero loop row or old value occurs on a nonempty clopen patch. Split that patch into two nonempty clopen pieces. Restrict the scalar to the appropriate coordinate and one piece, setting it to bottom elsewhere. This gives a nonzero proper part, since the other piece retains a nonzero value witnessed on a loop or an old continuation. Thus the scalar algebra at this ordinary Maximalist root is atomless.

## Lean verification

Both exported proofs apply the same theorem for signatures whose constants have closed types. The first licence realizes $K$ at the ordinary named root. The second realizes $H(K)$ at the root with two copies of each individual name. In the unary reading lemma, the upper term $d_b$ itself supplies the passing code. [Permanence and reflection](../lean/Classicism/StrongPossibility/Permanent.lean) · [First licence](../lean/Classicism/StrongPossibility/UnaryUniformPositive.lean) · [Second licence](../lean/Classicism/StrongPossibility/UnaryUniformNegative.lean) · [Diagonal reading](../lean/Classicism/StrongPossibility/UnarySeparation.lean) · [Uniform signature theorem](../lean/Classicism/StrongPossibility/UnaryArbitrarySignature.lean)

The exports are `Classicism.Map.strong_possibility_r_inconsistent` and `Classicism.Map.strong_possibility_signature_r_inconsistent`. The registry verifies both. The proof-body audit traces each to the two licences, the reflection arguments, the Russell witness, and the unary reading. Each uses exactly `propext`, `Classical.choice`, and `Quot.sound`. From `logical-maps/`, run `python scripts/pmap.py lean-check classicism` to check the generated statements and audit their Lean axioms. From `topics/classicism/lean/`, run `lake env lean scripts/StrongPossibility.lean` to trace both proof bodies to the unary reading theorem. [Proof dependency check](../lean/scripts/StrongPossibility.lean)
