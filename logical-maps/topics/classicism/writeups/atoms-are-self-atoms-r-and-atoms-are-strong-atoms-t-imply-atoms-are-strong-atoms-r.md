# The interval below a self-atom

For a self-atom $X$ at any relational type, write $p=\exists\bar x\,X[\bar x]$. The Boolean interval below $X$ is canonically order-isomorphic to the interval below $p$ at propositional type. The two maps are

$$
 Y\longmapsto\exists\bar x\,Y[\bar x],
 \qquad q\longmapsto \lambda\bar x.\,q\land X[\bar x].
$$

If $q\le p$, taking the instance proposition of the restriction gives $q\land p=q$. Conversely fix $Y\le X$. At every point where $Y$ is instantiated, $X$ is instantiated, hence an atom by self-atomhood. There $Y$ is a nonzero subrelation of $X$, so $Y=X$. At other points both $Y$ and the restriction of $X$ by $\exists Y$ have empty extension. Necessary coextension gives their identity. Both maps preserve order. Each calculation is valid also at every successor where the transport of $X$ is nonbottom, since the boxed clause in self-atomhood persists by 4. This localizes the argument in the map's [30 October scalar-to-relational bridge](../index.html#result/self-atoms-are-strong-atoms-t-implies-self-atoms-are-strong-atoms-r).

In particular a self-atom whose instance proposition is a strong atom is itself strong. At each future point where $X$ is nonzero, $p$ is nonzero too, so $p$ is an atom there. The interval isomorphism makes $X$ an atom there. At all other points $X$ is bottom.

Now suppose atoms are self-atoms at all relational types and scalar atoms are strong. For any atom $X$, its instance proposition is an atom by the map's instance-proposition lemma. The scalar premise makes that proposition strong, the other premise makes $X$ a self-atom, and the local argument proves $X$ strong.

The same calculation gives the density version. Suppose Self-Atomicity at all relational types and Strong Atomicity at propositional type. Below any nonzero relation pick a self-atom $X$ and a strong scalar atom $w\le p$. The restriction of $X$ by $w$ has instance proposition $w$. Wherever it is instantiated it is a nonzero subrelation of the atom $X$ there and must equal it. Thus this restriction is itself a self-atom, and its strong instance proposition makes it strong. This proves Strong Atomicity at the original relation type. Each implication gives its boxed counterpart by necessitation and K.

The two mixed-premise implications are by OpenAI Codex (GPT-6), prompted by Daniel Kodsi, 27 November 2026. Two further GPT-6 researchers independently reviewed the arguments.
