# Symmetric Cohen model: arithmetic growth

GPT-6 Astra, prompted by Daniel Kodsi. Original construction and proof dated 29 October 2026. Here SANA denotes the map’s Second-Order Analytic Necessitism (SOAN).

The construction gives a model of

$$
C+\mathrm{SANA}+\neg\mathrm{Arithmetic\ Necessitism}.
$$

SANA, and consequently Analytic Necessitism, holds because there is necessarily no genuine real structure at any admitted type. Arithmetic Necessitism fails at the canonical individual-counting instance despite $\Box I_e^*$. Its failure is inextensibility of the number property; standard numerals remain necessarily distinct.

The metatheory is ZFC. Generic extensions establish Boolean values, and a Boolean-Henkin reduction separately produces an actual countable classical Henkin model. No countable transitive model of ZFC is assumed. The nonstandard component A is constructed inside the ground universe before the final auxiliary generic evaluation and has trivial group action.

## 1. Fixed conventions

Types are generated from $e,t$, allowing an arrow only when its output is not $e$. Every relational type can consequently be written
$\sigma_1\cdots\sigma_k t$, including $k=0$.

Native necessity is the term $\Box p=(p=\top)$, and possibility is $p\ne\bot$. Equality at an evaluated classical point must be actual object identity. Distinct propositions with the same current truth value must **not** be identified.

A genuine $\operatorname{Real}_\tau$ structure uses literal equality, an antisymmetric linear order, functional field operations, and completeness for **all admitted subproperties** of its carrier. A quotient presentation with a separate equivalence relation is not enough.

Let $\nu=(et)t$. Write $N$ for the canonical Frege number property, $\bar n$ for the standard numeral terms, and $<$ for the definable strict natural-number order.

## 2. The finite-support Boolean hierarchy

Work in the metatheoretic universe $V$. Let

$$
\Omega=(2^\omega)^\omega,
\qquad B=\operatorname{RO}(\Omega).
$$

Thus $B$ is the complete regular-open Boolean algebra of a countable product of Cohen-real coordinates. For finite $J\subseteq\omega$, let $B_J$ be the embedded complete regular-open algebra depending only on coordinates in $J$. Put

$$
B_{\mathrm{fs}}=\bigcup_{J\subseteq\omega\text{ finite}}B_J.
$$

At each coordinate, a finite-prefix permutation permutes all binary strings of some fixed finite length and leaves their tails unchanged. Let $G$ be the group of products of these permutations at finitely many coordinates. Let $G_J$ be its subgroup acting trivially on the coordinates in $J$.

An object has support $J$ when it is fixed by every member of $G_J$. The action on function spaces is conjugation:

$$
(g\cdot f)(x)=g\cdot f(g^{-1}\cdot x).
$$

Define the base hierarchy recursively:

$$
D_e=\omega\quad\text{with trivial action},\qquad
D_t=B_{\mathrm{fs}},
$$

and $D_{\sigma\tau}$ consists of all finitely supported functions $D_\sigma\to D_\tau$, for admitted arrow types.

Application is actual function evaluation. Equality is crisp:

$$
\llbracket x=y\rrbracket=
\begin{cases}1&x=y,\\0&x\ne y.\end{cases}
$$

Connectives are Boolean operations. Quantification uses the meet or join in the complete ambient algebra $B$:

$$
\llbracket\forall x\,F x\rrbracket
 =\bigwedge_{x\in D_\sigma}F(x).
$$

### 2.1 Why quantifiers stay in the domain

The fixed-point algebra of $G_J$ acting on $B$ is exactly $B_J$. To see this, an invariant open set has, at each fixed $J$-coordinate value, an outside-coordinate section invariant under all finite-prefix permutations. Any nonempty such open section is the whole outside space: translates of any basic cylinder cover it. Regular openness then gives the asserted embedded regular-open algebra.

If $F$ has support $J$, then

$$
g\Bigl(\bigwedge_xF(x)\Bigr)
=\bigwedge_xF(gx)=\bigwedge_xF(x)
\quad(g\in G_J).
$$

Its meet therefore belongs to $B_J$. The same holds for joins. Lambda denotations have support contained in the union of the supports of their finitely many parameters: all logical operations, including these quantifiers, are equivariant. Thus unrestricted syntactic lambda comprehension is retained.

### 2.2 Soundness for C and C5

The usual induction gives Boolean soundness for H. If H proves two lambda bodies equivalent, their Boolean values agree at every assignment. Their function denotations are literally identical. This validates C's Logical Equivalence schema with its theoremhood side condition intact.

Native necessity in this base hierarchy is

$$
\Box b=\delta[b=1].
$$

Crisp equality makes all instances of necessary distinctness valid; hence this base validates C5. These observations establish validity of the relevant axioms at Boolean value 1, not just truth in one arbitrarily chosen filter.

### 2.3 Canonical arithmetic is standard in the base

Let $K=\{\bar n:n\in\omega\}$ be the ground set of standard numeral objects. Each numeral is fixed by $G$. The characteristic predicate of $K$ is an admitted support-empty predicate on $D_\nu$.

It contains zero and is successor closed. In the impredicative definition of $N$, this predicate excludes every object outside $K$. Conversely, finite induction establishes $N\bar n=1$ for every standard $n$. Hence $N$ is exactly the crisp characteristic predicate of $K$.

The numerals are distinct: evaluate them on crisp finite subsets of $D_e=\omega$ of the appropriate sizes. Successor is injective on $K$. Therefore $I_e^*=1$, and $\Box I_e^*=1$.

## 3. Generic evaluation and the strong symmetry lemma

For the next argument work in a forcing extension with a $V$-generic Cohen point $u\in\Omega$, or equivalently argue with the forcing theorem. Let $U$ be its Boolean generic ultrafilter. Interpret a proposition $b$ as true iff $b\in U$. Domains remain the **ground** $D_\sigma$'s.

Genericity supplies the quantifier truth clauses. For any ground predicate $F$, the conditions deciding its existential join by going below one of its values form a dense set. Thus if $\bigvee_x F(x)\in U$, some ground $x$ satisfies $F(x)\in U$. The witness comes from an admitted ground predicate.

### 3.1 Moving an object while fixing the evaluation point

**Lemma.** Let $x$ be any ground object of a ground $G$-set. If $x$ is not fixed by $G_J$, then there is a single-coordinate finite-prefix transposition $h\in G_J$ such that

$$
h^2=1,\qquad h(u)=u,\qquad h(x)\ne x.
$$

**Proof.** Let $O_x$ be the union of the fixed-point regions $\operatorname{Fix}(h)$ of all such transpositions $h\in G_J$ that move $x$. It is a ground open set. Suppose a basic cylinder $p$ missed $O_x$.

Fix any coordinate $i\notin J$. At a sufficiently large finite prefix depth, the restrictions imposed by $p$ leave at least three possible prefixes at coordinate $i$. Every transposition at that depth swaps only two prefixes, and therefore has a fixed-point cylinder meeting $p$. Since $p\cap O_x$ is empty, every such transposition must fix $x$. These transpositions generate the entire prefix-permutation group at that depth. Taking arbitrarily large depths shows that every finite-prefix permutation at coordinate $i$ fixes $x$. Doing this at every $i\notin J$ shows that all of $G_J$ fixes $x$, a contradiction.

Thus $O_x$ is dense. Genericity gives $u\in O_x$, yielding the required transposition. $\square$

Only actual finite transpositions are used. There is no appeal to the external finite order of an element of a nonstandard model's internally finite group.

### 3.2 Why this is an ordinary order automorphism

Suppose an admitted structure $\mathfrak R$ at type $\tau$ is a genuine real field at $U$. Choose a finite support $J$ for its entire finite tuple of data, including its distinguished elements.

A permutation fixing $J$ need not preserve truth at $U$. **We use only permutations that also fix $U$.** Such an $h$ is an automorphism of the evaluated classical Henkin structure, because

$$
b\in U\iff h(b)\in U.
$$

Since it fixes the field data, it induces an ordinary order automorphism of this particular evaluated field. An involution preserving a linear order fixes every element: either $x<hx$ or $hx<x$ would reverse after applying $h$.

By the lemma, every element of the field carrier must therefore be fixed by all of $G_J$. This is the precise reason a field's carrier is forced into its finite support; invariance of the Boolean-valued data alone would not suffice.

## 4. No genuine real field at any type

Put

$$
F_{\tau,J}=\{x\in D_\tau:g x=x\text{ for all }g\in G_J\}.
$$

The alleged field carrier lies in this ground set. When its arguments lie in $F_{\tau,J}$, every Boolean coefficient of its structure lies in $B_J$. Thus its carrier and ordinary field operations belong to the intermediate extension $V[U_J]$, and agree there with their interpretations in $V[U]$.

### 4.1 All intermediate subproperties are represented

Let $S$ be any subset of this carrier belonging to $V[U_J]$. Choose a $B_J$-name for $S$. For each ground $x\in F_{\tau,J}$, let $b_x\in B_J$ be its Boolean membership coefficient. Define a ground predicate on $D_\tau$ by

$$
P(x)=b_x\quad(x\in F_{\tau,J}),\qquad
P(x)=0\quad(x\notin F_{\tau,J}).
$$

This predicate has support $J$: the fixed points are pointwise fixed, their membership coefficients lie in $B_J$, and their complement is invariant. Therefore $P$ is an admitted predicate, and its current extension is exactly $S$.

The field's internal completeness consequently implies ordinary Dedekind completeness for every subset of its carrier in $V[U_J]$. It is a complete ordered field in that intermediate universe.

### 4.2 A fresh cut is also admitted

Choose $k\notin J$. Coordinate $k$ supplies a new real over $V[U_J]$, hence a new bounded rational Dedekind cut. For example, inject the new binary sequence into the Cantor subset of $[0,1]$.

Inside $V[U_{J\cup\{k\}}]$, form the subset of the alleged field consisting of the rational elements in this cut. It has a ground Boolean name on $F_{\tau,J}$ with coefficients in $B_{J\cup\{k\}}$. The same zero-extension construction represents it by an admitted predicate with support $J\cup\{k\}$.

This is an admitted bounded subproperty **at the very same evaluation point** as the field. Any supremum in the field would determine the new rational cut, but every field element lies in $V[U_J]$, where that cut is absent. Contradiction.

Therefore no genuine real field exists at any admitted type in any generic evaluation. By the forcing theorem and the quantifier truth lemma,

$$
\llbracket\exists\mathfrak R\,\operatorname{Real}_\tau(\mathfrak R)\rrbracket=0
\quad\text{for every admitted }\tau.
$$

Its negation has value 1, and native necessity of its negation has value 1 as well.

The argument does not infer noReal from external countability. Countable Henkin structures can be internally complete fields. It instead constructs an admitted bad cut for every alleged field.

## 5. Boolean-Henkin reduction without an actual generic over V

Here is the reduction used twice below.

Take the set-sized, many-sorted semantic structure containing:

- the complete ambient Boolean algebra $B$;
- each admitted domain $D_\sigma$;
- application, logical constants, and quantifier operations;
- the Boolean value map $v_0:D_t\to B$;
- the operations interpreting every lambda term with its finite parameter tuple.

There are countably many types and syntactic lambda operations. Name any countably many special witnesses that should be retained. Take a countable elementary substructure $K$.

For $F\in D_{\sigma t}^K$, write
$j(F)=v_0(\exists_\sigma F)$. Elementarity retains the density property

$$
0<b\le j(F)\quad\Longrightarrow\quad
\exists x\in D_\sigma^K\ [b\wedge v_0(Fx)\ne0].
$$

It holds in the full structure because $j(F)$ is the complete ambient join of the values $v_0(Fx)$.

On the countable Boolean algebra $B^K$, meet the dense set

$$
\Delta_F=
\{b>0:b\le\neg j(F)\}
\ \cup\
\{b>0:\exists x\in D_\sigma^K\ b\le v_0(Fx)\}
$$

for every admitted $F$, as well as the Boolean decision requirements. A descending construction gives an ultrafilter $u$ meeting all these countably many requirements.

Declare a proposition $p\in D_t^K$ true iff $v_0(p)\in u$. The dense sets give precisely

$$
\exists_\sigma F\text{ is true}
\iff
Fx\text{ is true for some }x\in D_\sigma^K.
$$

Lambda closure handles every formula with parameters in $K$, so induction gives the full classical Henkin truth lemma. Crisp first-coordinate equality makes truth of equality exactly literal object identity.

**Do not quotient proposition objects by agreement of their current truth values.** The ultrafilter is used only to define truth. Distinct true propositions remain different objects, preserving the native definition of necessity.

All closed axioms whose Boolean value was 1 remain true. In particular the base construction gives an actual countable model $A_0$ of

$$
T=C5+\Box I_e^*
 +\{\Box\neg\exists\operatorname{Real}_\tau:\tau\text{ admitted}\}.
$$

The canonical naturals of $A_0$ are externally standard: the full Boolean number predicate was exactly the characteristic predicate of the standard numeral objects, all of which are retained as term values.

## 6. The nonstandard C5 component

Take the elementary diagram of the countable Henkin structure $A_0$, in its countable expanded algebraic signature. Add a constant $c$ of number type with

$$
N(c)=\top,
\qquad (\bar n<c)=\top
\quad(n\in\omega).
$$

These are object equations, equivalently the corresponding boxed assertions. Every finite subset is realized by a sufficiently large standard numeral of $A_0$. Compactness and countable Löwenheim-Skolem give a countable elementary extension $A$ with such a $c$.

Both steps take place in $V$: first the ground Boolean-value calculation and Boolean-Henkin reduction construct $A_0$ in $V$; then ordinary compactness constructs $A$ in $V$. For the final hybrid, every domain and operation of $A$ is a ground set and its $G$-action is trivial. Only after this construction do we use a fresh $V$-generic Cohen evaluation as an auxiliary proof device. This ordering is essential: an arbitrary component selected in $V[U]$ could encode the supposedly fresh coordinates and would invalidate the intermediate-extension argument.

Use the original admitted application, lambda, and quantifier operations of $A$. Do not replace its higher-type domains by arbitrary external function spaces.

Its proposition objects form a Boolean algebra $B_A$. C5 makes its equality propositions crisp, and its native necessity is $a\mapsto\delta[a=\top_A]$. In particular, from the axioms of $T$,

$$
(I_e^*)_A=\top_A,
\qquad (\exists\operatorname{Real}_\tau)_A=\bot_A.
$$

These exact object equalities matter for the gluing; mere current falsity of real existence would not suffice.

An elementary extension of standard-arithmetic $A_0$ suffices. The separation does not require a contingent first-order arithmetical sentence.

## 7. The hybrid root hierarchy

Reuse the Cohen algebra, finite-support group, and support convention. Let

$$
D_e^r=\omega\times D_e^A,
\qquad \pi_e(n,a)=a,
$$

with trivial $G$-action.

For a relational type $\tau=\sigma_1\cdots\sigma_k t$, define

$$
D_\tau^r=
\{(f_0,a):
 f_0:D_{\sigma_1}^r\times\cdots\times D_{\sigma_k}^r
       \to B_{\mathrm{fs}}\text{ is finitely supported},
\ a\in D_\tau^A\}.
$$

For $k=0$, this says $D_t^r=B_{\mathrm{fs}}\times B_A$. Put $\pi(f_0,a)=a$. The group acts on the current profile and trivially on its $A$-component.

Application is

$$
(f_0,a)\cdot x=(f_0(x,-),\ a\cdot_A\pi x).
$$

Boolean operations are componentwise. Equality at any type is

$$
\operatorname{Eq}_r(x,y)=
(\delta[x=y],\operatorname{Eq}_A(\pi x,\pi y)).
$$

For $F=(f_0,a)\in D_{\sigma t}^r$,

$$
\forall_r F=
\left(\bigwedge_{x\in D_\sigma^r}f_0(x),\ \forall_A a\right).
$$

The current meet lies in $B_{\mathrm{fs}}$ by support invariance. Lambda abstraction uses the current Boolean body profile and the component's original lambda operation with projected parameters. A term induction proves that $\pi$ commutes with every term operation.

Every $\pi_\sigma$ is surjective: this is explicit at $e$, and a relational component $a$ has the root lift $(0,a)$.

### 7.1 Soundness for C

The current coordinate is a Boolean interpretation of H with literal current equality and all required lambda denotations. The second coordinate interprets the same terms in $A$. An H-theorem has current Boolean value 1, and its component is $\top_A$.

For an instance of Logical Equivalence, H-equivalent bodies have identical current profiles; their component lambda denotations are identical because $A$ is a C model. Therefore the corresponding root lambda objects are literally identical. This validates C without replacing actual coextensionality by identity.

Native root necessity is

$$
\Box(b,a)=
\bigl(\delta[b=1\text{ and }a=\top_A],\ \delta[a=\top_A]\bigr).
$$

Equivalently, its second coordinate is $\Box_A a$. The first coordinate is 1 exactly when **both** coordinates of the original proposition object are top. This formula follows from the displayed equality clause; it is not an independently imposed modal operator.

### 7.2 NoReal is retained

The generic-symmetry proof applies unchanged to the hybrid domains. A $U$-fixing transposition fixing the support of the field tuple is an automorphism of the evaluated current field. Its elements are therefore $J$-fixed. Every required current subproperty is still available: its finite-support current profile may be paired with any admitted $A$-component, for example bottom.

Consequently the current Boolean coordinate of every existential Real statement is 0. Its component is $\bot_A$ by $T$. Thus the **entire proposition object** is bottom:

$$
(\exists\operatorname{Real}_\tau)_r=(0,\bot_A).
$$

Therefore $\Box\neg\exists\operatorname{Real}_\tau$ holds for every type. Every antecedent of SANA is false. SANA, and hence ordinary Analytic Necessitism, holds vacuously.

### 7.3 Canonical numbers grow

Let $K=\{\bar n^r:n\in\omega\}$. Each standard root numeral is fixed by $G$. Use explicitly the admitted predicate

$$
W=(\chi_K,\top_{\nu t}^A).
$$

Its current profile is inductive and excludes every nonstandard root number object; its component is the constantly true predicate and is inductive as well. Finite induction supplies the converse inclusion. Hence

$$
N_r=(\chi_K,N_A).
$$

The current canonical numbers are exactly the standard numerals, whereas the projected number property contains the nonstandard $c$.

Both coordinates of $I_e^*$ are top: current successor is injective on the standard numerals, and the component is $\top_A$. Thus $\Box I_e^*$ holds at the root.

### 7.4 Explicit failure of inextensibility

Let

$$
X_A:=\lambda n\,[N_A(n)\land n<c],
\qquad X_r:=(\chi_K,X_A).
$$

For every current root number $\bar n^r$, its current $X_r$-value is 1 and its component is $\top_A$, by the boxed constraints on $c$. Therefore

$$
\forall n\,[N_r n\to\Box X_r n]
$$

has current Boolean value 1.

But $N_A\not\le X_A$, since $c$ is a number and is not below itself. Hence the root relation objects do not satisfy $N_r\le X_r$: their current profiles agree, but the component prevents the required algebraic identity. So the unboxed inextensibility condition already fails, and therefore the boxed inextensibility condition fails.

This witnesses

$$
\Box I_e^*\land\neg\operatorname{Rigid}(N_e).
$$

Standard natural numbers remain necessarily distinct. The Arithmetic Necessitism failure is specifically the inextensibility failure just exhibited.

Apply the Boolean-Henkin reduction again, naming $X_r$ and the countable component as needed. The closed target statements retain their Boolean values. The result is an actual countable classical Henkin model of C, SANA, and failure of Arithmetic Necessitism.

## 8. Verdicts justified by this construction

| Assertion | Status in the constructed root model |
|---|---|
| C | Holds by the interpretation and Logical Equivalence argument |
| $\Box I_e^*$ | Holds |
| $\Box\neg\exists\operatorname{Real}_\tau$, every admitted $\tau$ | Holds |
| SANA | Holds, because every possible-Real guard is false |
| Analytic Necessitism | Holds for the same reason |
| Arithmetic Necessitism at $e$ | Fails |
| Inextensibility of canonical $N_e$ | Fails, with the explicit $X_r$ above |
| Necessary distinctness restricted to current $N_e$ | Holds |
| Contingency of a first-order arithmetic sentence | Not claimed; unnecessary for this countermodel |


## Sources and attribution

- [Bacon and Dorr, Classicism (earlier draft, 1 July 2022)](https://andrew-bacon.github.io/papers/Classicism.pdf), for the framework and Henkin semantics. Exact map conventions are given in Background, Framework and Analysis.
- [Karagila, Lecture Notes: Forcing & Symmetric Extensions](https://karagila.org/files/Forcing-2023.pdf), for forcing and finite-support background, not this construction.
- The Boolean hierarchy, truth-preserving involution lemma, no-real argument, ground nonstandard component and hybrid arithmetic-growth construction above are given in this construction.

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering.. C and its Henkin/action semantics. This hybrid construction and its no-real proof are new, not asserted as a source theorem.
