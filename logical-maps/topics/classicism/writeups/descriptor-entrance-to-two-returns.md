# Self-atoms and two distinct returns

Self-Atomicity at every relational type and necessary Actuality can hold at a point with a successor where a two-hat necessity fails to be ND-necessary. The same successor witnesses the failure of the implication from 5-necessity to ND-necessity. Self-Atomicity is required at the original point.

## A point with two returns

Use the finite category with objects $w,v$, an arrow $f:w\to v$ and distinct arrows $l_0,l_1:v\to w$ such that $l_i f=1_w$. The endomorphisms of $w$ consist of its identity. The endomorphisms of $v$ are $1_v,fl_0,fl_1$. These equations specify composition. Concretely one can take $f$ as the inclusion of a two-element set into a three-element set and use the two retractions assigning the third element to different members. These sets specify the arrows only. The actual individual domain is a singleton at both objects. Use the full action model, so a relation has an independent tuple row for every outgoing arrow.

At either object, concentrating one tuple at the identity arrow gives an atom instantiated by that tuple. At type $t$ this gives a true atom. In particular Actuality holds everywhere. At $w$ the unique true atom is the proposition supported at $1_w$. Transport along $f$ sends this proposition to one true at both return arrows $l_0,l_1$. The target proposition supported just at $l_0$ splits it. Thus the true atom at $w$ is not strong. Strong Actuality fails at $w$.

The map proves that Actuality together with the implication from two-hat necessity to ND-necessity gives Strong Actuality. By contraposition that implication fails at $w$. Any two-hat necessity is 5-necessary, so the implication from 5-necessity to ND-necessity fails there as well. [Actuality and the two-hat implication](../#result/actuality-and-two-hat-implies-nd-imply-strong-actuality)

## Adding the entrance

Choose a countable auxiliary language $\Theta$ containing infinitely many constants of each relational type, and one marker for the unique individual. For each old object $b$ and **every** assignment of these symbols there, take a separate copy of the component rooted at $b$. The assignment at a future history is its transport from the initial point. This can be implemented with objects the arrows from $b$ and continuations the old composable arrows, with each object using the original typed domains at its endpoint. Quantification and modal evaluation in each copy agree with those of the original model, including at $w$. The copies form a set.

Prepend a point $r$ with just its identity loop and an independent entrance to each copy. The individual at $r$ is the sole individual. A root relation consists of an arbitrary current tuple row and the old traces given by **one** closed $\Theta$-term across all copies. Terms that give identical rows at every arrow specify the same entity. Transport into a copy evaluates the descriptor under its own assignment. The auxiliary symbols define which traces the model admits. The original language may interpret any relational names as top.

These domains are closed under lambda abstraction. Given finitely many root parameters, choose their descriptors and substitute them into the old body of the lambda. The resulting single term evaluates its correct row at every old history and every old argument tuple. At $r$ the lambda’s actual extension is admitted by the unrestricted current row. The same term induction handles quantifiers and modal truth. Equality agrees with agreement at every arrow and argument tuple. [Definable roots and term descriptors](coalesced-definable-root.html)

## Every nonzero root relation contains a self-atom

Let $P$ be nonzero. If its current row contains a tuple, keep that tuple just at the identity of $r$ and take the bottom old descriptor. This gives a strong atom below $P$. It includes the propositional case, where the tuple is empty.

Otherwise some old continuation instantiates a descriptor $T$ of $P$ at a tuple $\bar a$. At the target of that continuation record the transported values of the finitely many symbols in $T$. Among the copies there is a fresh entrance directly to this old object with the same values for those symbols. Choose a symbol $C$ of the same type as $P$ absent from $T$. In this copy give $C$ the identity-row atom of $\bar a$. These requirements are compatible, so $T$ and $C$ hold of $\bar a$ at the entry to this copy, and $C$ is an atom there.

Give $Q$ an empty root row and the following single descriptor across **all** copies:

$$Q(\bar x)=T(\bar x)\land C(\bar x)\land\operatorname{Atom}(C).$$

It satisfies $Q\le P$ and is nonzero by the chosen copy. At any future at which $Q$ is instantiated, $C$ is an atom there and $Q\le C$. The transported $Q$ is nonzero there and must equal that atom. Thus $Q$ is a self-atom. This argument works independently at every finite relational type, with no persistence assumption on the assertion that $C$ is an atom.

The entrance’s identity-only proposition is a true strong atom. Every old object has a true atom, giving necessary Actuality at $r$. Nevertheless the old $w$-copy still has the two distinct returns and still refutes both modal implications.

The root proposition supported throughout the old components contains no ordinary root atom. Indeed, any nonzero part of it has an old descriptor true at some old history; at a fresh initial copy of that same targeted object one can vary a fresh propositional symbol while preserving all the descriptor’s parameters. Intersecting with that symbol and with its complement produces two nonzero parts. Thus ordinary Atomicity at $t$ fails here.
