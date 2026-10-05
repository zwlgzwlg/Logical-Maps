# □BF, □Atomicity and □Rigid Comprehension imply □Rigid Power

Original argument of Claude Opus 5.5 (Anthropic), 3 October 2026. Informal, not Lean-verified.

Let $F$ be rigid and $P:=\lambda X\, .\,\operatorname{Rigid}(X)\land X\le F$. Persistence of $P$ holds in
C, since both conjuncts are necessitated and 4 holds. Since $F$ is rigid, it is necessarily rigid. So it
suffices to show that at any world $v$, given BF, Atomicity (type $t$) and Rigid Comprehension at $v$, and
$F$ rigid at $v$, the property $P$ is weakly inextensible at $v$. The boxed premises supply this at every
world.

## Two facts, at $v$

1. *Atoms decide.* If $a$ is an atom and $\Diamond(a\land p)$, then $a\le p$. By BF this extends to
   existential propositions, as in the Intensional Choice write-up.
2. *No new instances below an atom.* If $R$ is weakly rigid, $a$ is an atom and $a\le Rz$, then $a\le z=z_1$
   for some actual instance $z_1$ of $R$. (Apply weak inextensibility to
   $\lambda z'\, .\,\neg(a\land z'=z)$.) In C, coextensive weakly rigid relations are identical, at every
   world.

## The argument

Let $\forall X\, .\,PX\to\Box\mathcal XX$, and suppose $\Diamond\exists X\, .\,PX\land\neg\mathcal XX$. By BF
and Atomicity there are an $X$ and an atom $a$ with $a\le PX\land\neg\mathcal XX$. Let $X'$ be a rigid
relation coextensive with $Q:=\lambda z\, .\,Fz\land\Diamond(a\land Xz)$, which Rigid Comprehension
supplies.

*$X'\le F$.* Every actual instance of $X'$ is an instance of $F$, and so necessarily an instance of $F$ by
persistence. Weak inextensibility of $X'$ gives $X'\le F$. So $PX'$, and therefore $\Box\mathcal XX'$.

*$a$ entails that $X$ and $X'$ are coextensive.* Suppose instead that $a$ entails $Xz\land\neg X'z$ for
some $z$; such a $z$ exists by facts 1 and BF. Since $a\le X\le F$, we have $a\le Fz$. By fact 2 for $F$,
$a\le z=z_1$ for some actual instance $z_1$ of $F$. Then $a\le Xz_1$, so $Qz_1$ holds, hence $X'z_1$, hence
$\Box X'z_1$, and so $a\le X'z$. Contradiction. Conversely, suppose $a$ entails $X'z\land\neg Xz$. By fact
2 for $X'$, $a\le z=z_1$ for an actual instance $z_1$ of $X'$. So $Qz_1$, so $\Diamond(a\land Xz_1)$, so
$a\le Xz_1$ by fact 1, and $a\le Xz$. Contradiction.

*Conclusion.* At the worlds where $a$ holds, $X$ is rigid, since $a\le PX$. $X'$ is rigid there too,
being necessarily rigid. Coextensive weakly rigid relations are identical, so $a\le X=X'$. Hence
$a\le\mathcal XX'=\mathcal XX$, which contradicts $a\le\neg\mathcal XX$ and $\Diamond a$.

The argument uses BF at the type of the arguments of $F$ and at the type of $F$, Atomicity at type $t$, and
Rigid Comprehension at the type of $F$. It makes no use of B or 5.

## Paper references

- **Background: Classicism.** Bacon, Andrew, and Cian Dorr (2024). Classicism. In Peter Fritz and Nicholas K. Jones (eds), Higher-Order Metaphysics, Oxford University Press, pp. 109–190. The map was built from the draft dated 16 May 2023, 87 pages, which does not differ materially from the published version; all page, proposition and footnote locators in this map refer to that draft's numbering. — §2.3, pp. 28–33. Rigidity and Rigid Comprehension.
