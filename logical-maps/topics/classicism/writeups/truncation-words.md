# Logical Necessity with necessary Atomicity and no true atom

For every set-sized signature there is a model of Logical Necessity and necessary Atomicity at every relational type in which Actuality fails. The same point has Mathematical Possibilism, necessary Countable Boolean Completeness and both necessary rigid powers. The construction enlarges the pin bound of the [Bacon–Dorr truncation model](finite-support-truncations.html) so that the profiles witnessing an entire signature can be assigned simultaneously.

## Truncations and word shifts

Work in ZFC. Put $\kappa=\max(\aleph_0,|\Sigma|)$, choose a regular cardinal $\lambda>\kappa$, and use $\lambda$ as an auxiliary ordinal index. Let $T$ consist of the identity of $\lambda$ and the truncations $g_\alpha(\beta)=\min(\alpha,\beta)$ for $\alpha<\lambda$. Thus $g_\alpha g_\beta=g_{\min(\alpha,\beta)}$. The arrow monoid of one object is $T\times W$, where $W$ is the free monoid on $\kappa$ letters and has unit $\epsilon$. Multiplication is componentwise, and we write the rightmost arrow first in a composite. Individuals form a singleton fixed by the entire monoid. The ordinal index set defines the support condition on rows.

At a relational type take the profiles $F$ assigning to each $(f,w)$ a subset of the tuples from the previously constructed argument carriers. Require some set $P\subseteq\lambda$ of size less than $\lambda$ such that
$$
  f|P=f'|P\quad\Longrightarrow\quad F_{(f,w)}=F_{(f',w)}
  \qquad\text{for all }w\in W.
$$
This tests equality of whole rows. The identity row is the extension, and transport precomposes the arrow index. If $P$ pins $F$, then $f[P]$ pins its transport by $(f,w)$. If two arrows at the same word agree on $P$, their transports of $F$ agree as entire entities, since every further composite agrees on $P$. Arbitrary constant rows are available, so every external subset of the current tuple domain is an admitted current extension.

For a term abstraction use the usual row at an arrow: evaluate the body at the single object on the transported parameters and all newly supplied arguments. The union of pins of the finitely many parameters suffices, since agreeing on this union at a fixed word gives the same *whole* transported parameters and hence the same row on all the new arguments. Application, Boolean operations and quantified formulas have the same closure, and all these operations commute with transport. Different relational profiles have different rows on some arrow and tuple, giving the required intensional identity condition. This verifies the ordinary action model.

## Interpreting the whole signature

There are at most $\kappa$ instances with a pure formula and a finite list of distinct matching constants. For each for which a witnessing tuple exists in the pure reduct, choose one tuple and a private letter $l$. Interpret each relational constant $c$ independently on the disjoint word cylinders with distinct last letters. On a cylinder reserved for an instance using $c$, set
$$
 (c)_{(f,wl)}=(v_c)_{(f,w)},
$$
where $v_c$ is the selected value for its position in the tuple. Use empty rows on the remaining cylinders, and at the empty word. The union of the pins of all the chosen values for any one $c$ still has size less than $\lambda$ by regularity. Thus this is an admitted profile; its transport by $(1,l)$ equals exactly $v_c$. The only individual value is automatically the required witness for each individual position. The number of letters was fixed from the signature, before witnesses in this very pure reduct were chosen.

Witnessed Possibility follows. A pure existential sentence has the same truth value at every arrow of a one-object action model. Thus a possibly realized assignment is already locally realized, and every possible named instance has its existential closure locally true. This gives Possibly Witnessed Possibility and its converse direction as required for Logical Necessity. The construction works also when individual names are present; the output is an interpretation for the specified signature.

## Atomicity and the failure of Actuality

For each $\alpha<\lambda$, its successor ordinal $\alpha+1$ distinguishes $g_\alpha$ from all other truncations and from the identity by its value there. Therefore a profile supported on just $(g_\alpha,w)$ and one given tuple is an admitted atom. Every nonzero profile contains such an atom. If already instantiated at $(g_\alpha,w)$ take such a tuple there. If instantiated at $(1,w)$, choose $\alpha$ above the bound of its pin; the same tuple occurs at $(g_\alpha,w)$. This applies at every relational type and throughout the model.

Every true proposition contains $(1,\epsilon)$ and all $(g_\alpha,\epsilon)$ for sufficiently large $\alpha$. Two such distinct truncation addresses give disjoint nonzero proper parts. Hence no true proposition is an atom, and Actuality fails. The atom supported on a single $(g_\alpha,\epsilon)$ becomes, at $(g_\alpha,\epsilon)$, a true proposition containing all $(g_\beta,\epsilon)$ with $\beta\ge\alpha$. It is no longer an atom there and fails self-atomhood. The distinction between Atomicity and strong or self-atomicity is needed here.

## Completeness and Mathematical Possibilism

Every externally countable family has a join at every relational type: take the rowwise union of its members. Countably many pins still have a union of size less than $\lambda$. Internal countability implies external countability at the designated object: the externally countable set of denotations of the standard Frege numerals is inductive and is a current predicate extension by fullness of current rows. Thus the range of an internal injection into the canonical numbers is externally countable. This proves Countable Boolean Completeness and, by homogeneity, its necessitation.

Full Boolean Completeness at $t$ fails. Partition $\lambda$ into two cofinal subsets $C,D$. Take the current family of singleton propositions supported on $(g_\alpha,\epsilon)$ for $\alpha\in C$. Every upper bound contains all sufficiently high $(g_\beta,\epsilon)$, since its pin is bounded and $C$ is cofinal. Removing the singleton at any such $\beta\in D$ produces a strictly smaller upper bound. The family is admitted by current fullness.

The one individual at all arrows bounds the inexact ordinal carrier by the three closed thresholds (well-ordered, nonempty well-ordered field, impossible). Their currently instantiated finite subfamilies, when rigid, equal the corresponding finite disjunction of haecceities; their limits are again thresholds. The finite set of thresholds is an admissible current induction predicate. Full current subsets and graphs imply that every infinite carrier contains a countably infinite power-closed subset larger than the benchmark, since all its strictly smaller subsets have finite powers, coded by finite subsets. Thus every revised-small Boolean algebra is finite. Every finite set of isolated truncation addresses is itself a proposition, with every subset present. Its principal ideal realizes the Boolean algebra with that many atoms. This proves Mathematical Possibilism. [The map's bounded-individual ordinal argument](https://github.com/zwlgzwlg/Logical-Maps/blob/4bb9287187ed7cb09567eb3a6302cb896c986ec4/logical-maps/topics/classicism/arguments/forcing-possibilism-countably-many-arrows.yaml)

## Inextensibility and the two powers

If a relation $Y$ has full current row on the proposition sort, then $Y_{(g_\gamma,\epsilon)}$ is still full for $\gamma$ above the bound of its pin. At this one isolated address put a tester whose row is the image of the proposition carrier under $g_\gamma$, and let every other row of the tester be full. It necessarily holds of every old proposition. But the singleton at $(g_{\gamma+1},\epsilon)$ is not in that image: every image is fixed by the idempotent $g_\gamma$, whereas this singleton transports to bottom there. Hence $Y$ is not weakly inextensible. This refutes Weakly Inextensible Comprehension.

For a weakly rigid $F$ write $E$ for its current row. Weak persistence gives $a[E]\subseteq F_a$ at each arrow. At any isolated $a=(g_\alpha,w)$ use a tester full elsewhere and equal to $a[E]$ there. It necessarily accepts all of $E$, so weak inextensibility gives the reverse inclusion there. In particular $E=g_\gamma[E]$ for any $\gamma$ above the bound of the pin of $F$. Every tuple in $E$ is fixed by that idempotent, and therefore by all larger truncations. At $(1,w)$ the pin of $F$ now gives $F_{(1,w)}=F_{(g_\beta,w)}=(1,w)[E]$ for $\beta$ sufficiently large. Thus $F_a=a[E]$ at every arrow.

Conversely, when one truncation $g_\gamma$ fixes every tuple in $E$, the profile with rows $a[E]$ is admitted: the initial segment through $\gamma$ pins the truncation action on all the tuples at once. Exact-image rows prove hereditary rigidity, since every member after any further arrow is the image of a current one. This gives Tame Rigidity. For a rigid or weakly rigid subrelation $X$ below $aF$, let $E'=E\cap a^{-1}[X_{(1,\epsilon)}]$. Its members share the old bound and $a[E']=X_{(1,\epsilon)}$. The exact-image relation on $E'$ lies below $F$ and transports to $X$. Consequently the current members of either canonical power transport onto its actual members at each future, and the converse inclusion follows by persistence. Exact-image rows again prove rigidity. Both powers hold necessarily.

OpenAI Codex (GPT-6), prompted by Daniel Kodsi, developed the extension on 26 November 2026. Two additional GPT-6 research agents independently checked the ordinal pinning, signature and Atomicity arguments; the power classification and completeness consequences received separate review.
