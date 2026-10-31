# Supported-product action model: external coordinate symmetry

GPT-6 Astra, prompted by Daniel Kodsi, 30 October 2026.

Logical Necessity together with necessary propositional Boolean Completeness
does not imply full Boolean Completeness, Weakly Inextensible Comprehension,
or Rigid Power. One construction supplies all three separations. It also has
necessary all-type Barcan, Countable Boolean Completeness and Tame Rigidity,
and current Atomlessness.

The change to the [free-monoid supported product](supported-product-free-monoids-glued-constants.md)
is a second support condition on higher relations. It restricts represented
families sufficiently to give propositional joins while preserving the higher-type
obstructions. Its three joint separations use existing principles; the simpler
separations from Logical Necessity alone already have the original product as
a witness.

## 1. The two support conditions

Work in external ZFC. For a prescribed set-sized finitary signature choose an
infinite cardinal $\kappa$ bounding its syntax. Let $|I|=\kappa^+$ and let $L$
be the free monoid on $\kappa$ letters. The single object's arrows are
$M=L^I$, with coordinatewise concatenation. Write $1$ for the empty-word arrow.
Individuals form a singleton. The external group $G=\operatorname{Sym}(I)$ acts
by $(gm)_i=m_{g^{-1}i}$; its elements are not extra accessibility arrows.

At each relational type $\tau=\sigma_1\cdots\sigma_nt$, admit all profiles
$F:M\to\mathcal P(\prod_iD_{\sigma_i})$ with both:

* an arrow support $S\subseteq I$, $|S|\le\kappa$, such that $F_m=F_{m'}$
  whenever $m|_S=m'|_S$;
* a permutation support $T\subseteq I$, $|T|\le\kappa$, such that every $g$
  fixing $T$ pointwise fixes the whole profile under
  $(gF)_m=g[F_{g^{-1}m}]$.

These domains and group actions are defined recursively. Transport is
$(hF)_k=F_{kh}$; equality at the object is literal whole-profile identity.
Truth of a scalar means membership of $1$. Every scalar depending on at most
$\kappa$ coordinates satisfies both conditions, so the original scalar
algebra is unchanged.

The action is covariant: $g(hF)=(gh)(gF)$, where $gh$ on the right denotes
the permuted arrow. Transport $hF$ retains arrow support $S$ and has
permutation support $S\cup T$: if $g$ fixes that union, $gh$ agrees with $h$
on $S$. This works for arbitrary arrows, without restricting their supports.

For a term with finitely many parameters, take the unions of their two kinds
of support. Arrows agreeing on the first union transport all parameters to
identical whole entities. Evaluation of a formula, including its quantified
subformulas over the full admitted domains, is then identical. Equivariance
under $G$ follows by induction, since it bijects both arrows and every domain.
Thus abstraction has the two supports. Application, with
$(Fa)_m(\bar b)=F_m(ma,\bar b)$, does too. Constant singleton predicates
have empty arrow support and the permutation support of their parameter,
and distinguish unequal whole entities. Transported haecceities are admitted
as well.

The ordinary action semantics therefore validates the lambda rules and H.
An H-theorem-level equivalence agrees at every arrow and tuple and identifies
the corresponding abstraction profiles. This verifies C with its theoremhood
restriction. Pure closed sentences have constant truth across this one-object
model; a verified pure closed instance consequently holds necessarily.

## 2. Scalar joins by a support hull

Two scalar support facts will be useful. If $S,R$ both support $p$, then
$S\cap R$ supports it: patch an arrow taking the required values on $S$ and
$R$. If $p$ is invariant under all permutations fixing $T$, move $S\setminus T$
to fresh coordinates disjoint from $S\cup T$. The moved support and $S$
intersect inside $T$. Thus such a $p$ depends only on $T$.

For an admitted $X:tt$, put $E=X_1$. A permutation support $T$ of $X$
makes $E$ invariant under $\operatorname{Fix}(T)$. Define the scalar

$$
J=\{m:\exists n\in\bigcup E\ (n|_T=m|_T)\}.
$$

It has support $T$ and contains each member of $E$. To prove leastness, let
$b$ be any admitted upper bound, with arrow support $R$. For $m\in J$ choose
$p\in E$ and $n\in p$ agreeing with $m$ on $T$. If $S$ supports $p$, choose
$g$ fixing $T$ and moving $S\setminus T$ off $R\cup T$. Then $gp\in E$,
and its support $gS$ meets $R$ only inside $T$. Patch an arrow $k$ agreeing
with $gn$ on $gS$ and $m$ on $R$. It belongs to $gp$, hence $b$, so $m\in b$.
The empty-family case gives $J=\varnothing$.

This is the least upper bound among all admitted scalars. The union $\bigcup E$
need not itself be admitted. Every represented scalar family has a join,
proving $\Box\mathrm{BC}_t$.

## 3. Necessary Barcan and countable completeness

Let $F$ have arrow support $S$ and permutation support $T$. To lift $F$
through an arbitrary $h$, define $G_m=F_{r(m)}$ if every $m_i$, $i\in S$,
ends in $h_i$, where $r(m)_i$ removes that suffix on $S$ and is empty elsewhere.
Set $G_m=\varnothing$ if a suffix test fails. Free-word cancellation gives
$hG=F$. The new profile has arrow support $S$ and permutation support
$S\cup T$. Every transport is therefore onto at every type, yielding
$\Box\mathrm{BF}$.

The pointwise union of at most $\kappa$ profiles retains both supports.
For any counting type $\sigma$, the external orbit of the closed terms
$\operatorname{Suc}_\sigma^n(\mathbf0_\sigma)$ has an admitted constant
characteristic profile with both supports empty. It is currently inductive.
Finite induction gives the converse, so native numberhood has exactly this
countable orbit as its actual extension. No distinctness of its iterates
is assumed. A native countability witness assigns each actual family member
a nonempty set of numeral labels, with disjoint label sets for distinct members.
Assigning externally the least iteration index of a label injects the family
into $\mathbb N$. Its pointwise union is admitted and is its whole-profile
least upper bound. This proves $\Box\mathrm{CBC}$ at every counting type
and relational output type, without requiring an admitted choice operation.

## 4. Higher weak inextensibility and completeness fail

Let $q_i=\{m:m_i=\varepsilon\}$. The constant profile with extension
$E=\{q_i:i\in I\}$ has both supports empty. Suppose $Y:tt$ has current
extension $E$, and choose $j$ outside an arrow support of $Y$. Let $h$
have a nonempty word only at $j$. Then $Y_h=E$. The admitted test

$$
Z_m=\begin{cases}D_t,&m_j=\varepsilon,\\
D_t\setminus\{q_j\},&m_j\ne\varepsilon
\end{cases}
$$

has both supports $\{j\}$. Every transported current member $q_i$ satisfies
$Z$: it remains $q_i$ or becomes bottom. Yet the fresh $q_j\in Y_h$ fails
$Z_h$. Thus every current coextension of $E$ fails weak inextensibility.
This refutes WIC at $tt$.

The existing same-type proof of BC implying WIC takes a represented family
of haecceities at the output type. Applied here at output $tt$, a least upper
bound would give the impossible weakly inextensible coextension (intersect
with the original relation). Hence BC fails at $tt$, although BC at $t$
holds necessarily.

## 5. Exact images and Tame Rigidity

For $E$ a set of tuples write $(H_E)_m=mE$. If this profile is admitted,
it and all its transports are weakly persistent and weakly inextensible:
all target instances are precisely transported current ones. Thus it is rigid.
Conversely let $Y$ be weakly rigid, $E=Y_1$. Persistence gives $mE\subseteq Y_m$.
If $T_0$ supports $E$ under permutations, then for each small $Q$ the profile

$$
B_Q(E)_m=\bigcup\{nE:n|_Q=m|_Q\}
$$

has arrow support $Q$ and permutation support $Q\cup T_0$. Each current
$E$-member necessarily satisfies it, so $Y\le B_Q(E)$. For $b\in Y_m$ choose
$Q$ containing the arrow supports of $Y$ and the entries of $b$. Find
$n,a$ with $n|_Q=m|_Q$, $a\in E$ and $na=b$. Set $r_i=u_i=\varepsilon$
on $Q$ and $r_i=n_i,u_i=m_i$ elsewhere. Then $mr=un$; $Y_r=E$,
weak persistence puts $ra\in E$, and $u$ fixes $b$. Therefore
$b=u(na)=m(ra)\in mE$. Thus $Y=H_E$.

Weakly rigid admitted profiles are therefore rigid, and the closed pure
schema holds necessarily. This is $\Box$Tame Rigidity. It does not assert
that every external exact-image profile is admitted.

## 6. Rigid Power fails

Fix $o\in I$. For $j\ne o$, let $y_j:tt$ be the constant profile $\{q_j\}$.
For $z\in\mathbb Z$, define $e_{z,j}:tt$ with $r=|m_o|$, $n=|m_j|$ by

$$
(e_{z,j})_m=\begin{cases}
\{q_j\}\cup\{\bot:\chi(n+z)=1\},&r=0,\\
\{q_j\},&r=1,\ n+z\ge0,\\
\varnothing,&r=1,\ n+z<0,\\
\{q_j\},&r\ge2,
\end{cases}
$$

where $\chi(k)=1$ exactly at nonnegative squares. Its two supports are
$\{o,j\}$. Square tails distinguish $z$, and $q_j$ distinguishes $j$.
For one-letter arrows $a$ at $o$ and $b_j$ at $j$,

$$
b_je_{z,j}=e_{z+1,j},\qquad a^2e_{z,j}=y_j,\qquad
ae_{z,j}=y_j\ \Longleftrightarrow\ z\ge0.
$$

Set $E=\{e_{z,j}:z\in\mathbb Z,j\ne o\}$ and $B_0=\{y_j:j\ne o\}$.
The exact images $F=H_E$ and $X=H_{B_0}$ are admitted with support $\{o\}$
of both kinds; arbitrary shifts in the other coordinates permute the integer
indices. Both are rigid and $X\le aF$.

If a rigid $Y\le F$ satisfied $aY=X$, the exact-image lemma gives $Y=H_A$
for $A\subseteq E$ and $aA=B_0$. Choose $j$ outside its arrow support.
Then $b_jA=A$. The nonempty $j$-section of $A$, needed to supply $y_j$,
is invariant under the bilateral shift of $\mathbb Z$, so contains every
integer, including $-1$. But $ae_{-1,j}\notin B_0$, contradiction.
The canonical rigid-power property of $F$ has the fresh member $X$ at $a$
and is not an exact image. It is not rigid. The failed bound type is $(tt)t$.

## 7. Gluing the fixed signature

Fix these pure domains before choosing interpretations. Select one
interpretation $J_\alpha$ for every signature sentence satisfiable over them.
There are at most $\kappa$ sentence/constant pairs. Choose $j$ outside the
union of both supports of every selected constant denotation. Interpret each
relational constant $c$ by the profile whose row at $m$ is $J_\alpha(c)_m$
when $m_j$ ends in the letter for $\alpha$, and empty when no such letter
occurs. Its supports are the corresponding unions together with $\{j\}$.
A one-letter arrow $h_\alpha$ at $j$ recovers the whole interpretation
$J_\alpha$ simultaneously; transporting any interpretation still gives an
interpretation on the fixed pure domains.

A signature sentence is consequently possible exactly when it is satisfiable
by an interpretation on these domains. For pure $P$ and distinct matching
constant symbols $\bar c$, this gives
$\Diamond P[\bar c/\bar x]\leftrightarrow\exists\bar x P$, and by negation
$\Box P[\bar c/\bar x]\leftrightarrow\forall\bar x P$. This is current
Logical Necessity, including the empty tuple. It is not a claim of necessary
Logical Necessity or of Maximalism.

## 8. Atomlessness and the choice obstructions

A nonzero scalar with arrow support $S$ splits by $q_j$ for fresh $j$.
For any current true $p$ with support $S$, an arrow nonempty only at fresh
$j$ still satisfies $p$ but fails the current truth $q_j$. This refutes
Actuality. Since $\Diamond q_j=q_j$, the same example refutes Vicinity.

For Relational Choice at input/output $(t,t)$ consider the admitted serial
relation

$$
D(p,q)=(\neg p\land\neg q\land\neg(q\le p))\lor(p\land q=\bot).
$$

At a false $p$, use $q=\neg q_j$ for $j$ outside its support. At a true
$p$, use bottom. Suppose a functional subrelation has permutation support
$T$. Put $b_T=\neg\{m:\forall i\in T\ m_i=\varepsilon\}$. It is false
and fixed by $\operatorname{Fix}(T)$. Uniqueness forces its selected output
$q$ to be fixed by that group, hence $T$-coordinate-supported by §2. Since
$q$ is false, it cannot contain an arrow empty on $T$; thus $q\le b_T$,
contradicting $D(b_T,q)$.

For Zorn at carrier $t$, let $P(p)=\neg p$ and put
$R(p,q)=\neg P(p)\lor(P(q)\land p\le q)$. True scalars lie below all
false scalars; false scalars are ordered by inclusion. Fresh-coordinate
escape shows there is no maximal element. If $X$ is an admitted $R$-chain
with permutation support $T$, every involution fixing $T$ fixes each false
member: applying it to a strict comparison with its image would reverse
that comparison. Every permutation fixing $T$ is a product of two such
involutions, by reflecting each finite cyclic or bilateral infinite orbit.
Thus every false member depends only on $T$ and lies below $b_T$. This
false scalar bounds the chain, including the empty chain. Zorn's native
represented-chain hypothesis holds but its conclusion fails.

The construction uses the original supported-product witnesses and signature
gluing, the support-moving hull method, and the support obstruction to selectors.
The added permutation condition is responsible for the new joint
Logical-Necessity/scalar-completeness separations. No all-type completeness,
positive choice, current ND or analytical verdict is inferred.
