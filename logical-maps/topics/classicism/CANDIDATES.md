# Classicism: candidate principles

Principles that may be added to the map later. None of them is recorded yet.
Each needs a decision before it is added, usually because it opens a family of
variants or connections. Notation follows `background.md`. Remove an entry
once it has been recorded or rejected.

## Weak variants of Rigid Power

*Added 3 October 2026.* Rigid Power (`rigid-power-r`, Goodsell 2019) says:
if $F$ is rigid, so is $P_F:=\lambda X\, .\,\operatorname{Rigid}(X)\land X\le F$.
"Rigid" can be replaced by "weakly rigid" in three places:

- **H**: the hypothesis on $F$;
- **I**: the condition inside the power property, $\lambda X\, .\,\underline{\ \ }(X)\land X\le F$;
- **C**: the conclusion about that property.

Write a variant as a triple over $\{R,W\}$, so that Rigid Power is
$(R,R,R)$. Cian Dorr's "natural" reading of "Weak Rigid Power" is $(W,W,W)$.

### Logical relationships

- *H and C.* Weakening the hypothesis or strengthening the conclusion gives a
  stronger principle. With I fixed, $(W,I,R)$ is the strongest variant and
  $(R,I,W)$ the weakest; $(R,I,R)$ and $(W,I,W)$ lie between them.
- *I.* Changing I changes the property concerned, so there is no direct
  ordering. The two properties are necessarily coextensive, and hence
  identical, wherever weak rigidity and rigidity necessarily coincide, that is,
  under □Tame Rigidity.
- *Persistence.* Every variant's conclusion includes the persistence of the
  power property. With $I=R$ this is a theorem of C: rigidity and entailment are
  necessitated conditions, and 4 holds. With $I=W$ it is not, because
  $\operatorname{WeaklyRigid}(X)$ has an unboxed weak-inextensibility conjunct.
  Persistence then needs $\operatorname{WeaklyRigid}(X)\to\Box
  \operatorname{WeaklyRigid}(X)$ at every world, which □Tame Rigidity supplies.
- *Collapse.* Under □Tame Rigidity all eight variants are equivalent. A weakly
  rigid $F$ is then rigid, and the two power properties are identical. □Rigid
  Comprehension gives □Tame Rigidity, and so does C5 (both recorded). So all eight follow from □BF + □Atomicity + □RC, and from C5,
  by the recorded results for Rigid Power. Under unboxed Rigid Comprehension
  alone, Tame Rigidity holds at the evaluation point, so the hypotheses R and W
  are equivalent there.

### What the unboxed premises give

The recorded result `necessary-bf-atomicity-and-rigid-comprehension-imply-necessary-rigid-power`
derives □Rigid Power, the full $(R,R,R)$, from boxed premises. Its argument at a
single world $v$ uses BF, Atomicity and Rigid Comprehension at $v$, and it
establishes the weak inextensibility of $P_F$ at $v$. Run once at the evaluation
point, from unboxed premises, it gives:

> **BF + Atomicity + Rigid Comprehension ⇒ $(W,R,W)$**: if $F$ is weakly rigid,
> then $\lambda X\, .\,\operatorname{Rigid}(X)\land X\le F$ is weakly rigid.

- *Hypothesis W suffices.* The argument uses $F$ only at the evaluation point,
  in two places. One is the atom lemma for $F$: below an atom, every instance of
  $F$ is identified with an actual instance. It uses only the unboxed weak
  inextensibility of $F$. The other is $X'\le F$, which uses only the persistence
  of $F$. Very weak rigidity of $F$ would also do.
- *Inside R is needed.* The conclusion's persistence clause is free for $I=R$.
  For $I=W$ it would need □Tame Rigidity, but unboxed Rigid Comprehension gives
  Tame Rigidity only at the evaluation point.
- *Conclusion W only.* $\operatorname{Rigid}(P_F)$ needs weak inextensibility at
  every accessible world $v$. The argument would need an atom below the failure
  at $v$ that is possible relative to $v$, and a pull-back by Rigid Comprehension
  at $v$. Actual-world atoms and an actual rigid pull-back do not suffice without
  B, because expressing "accessible from $v$" needs a backward modality. RC + BF ⇒
  □BF is recorded, so BF at $v$ is available; Atomicity and Rigid Comprehension
  at $v$ are not.

*Open question:* do unboxed BF + Atomicity + Rigid Comprehension give Rigid Power
itself? No countermodel is known.

## Finiteness of rigid extensions

*Added 3 October 2026.* "Everything rigid has a finite extension":
$\forall F\, .\,\operatorname{Rigid}(F)\to\operatorname{Finite}(F)$, where $F$ has
a finite extension when some finite cardinality (`background.md`, Infinity) holds
of it. Variants replace Rigid by Weakly Rigid, Inextensible or Weakly
Inextensible, and perhaps Persistent.

Points to settle first:
- In the finite-support truncation model, every rigid property of individuals
  has finite extension.
- $\operatorname{Inextensible}(\top_{\sigma t})$ is equivalent to □BF at
  $\sigma$. So with infinitely many entities, □BF refutes the Inextensible and
  Rigid variants at that type, and Rigid Comprehension refutes the rigid variant
  given the Axiom of Infinity.
- The variants interact with the Axiom of Infinity and Possible Infinity, and
  with which types are allowed. Decide the type range before recording.

## Maximalizations of extensions of C

*Added 3 October 2026.* Bacon, *A Philosophical Introduction to Higher-Order
Logics* (2024), Corollary 18.2, shows the maximalizations of C + BF, C + □BF,
C + Actuality, C + □Actuality, C + Atomicity and C + □Atomicity consistent.
`extraction.md` notes these, with Proposition 18.8, Corollaries 18.3–18.4 and
Propositions 18.9–18.11, as awaiting a decision. Recording them would need
relativized Possibility and Distinctness Maximalism principles, one for each base
theory, and it is not yet decided how to present them.

## Further modal principles

*Added 3 October 2026.* Propositional modal axioms not yet on the map, each
closed over $p$ (and $q$):

- **McKinsey (M):** $\forall p\, .\,\Box\Diamond p\to\Diamond\Box p$.
- **Grz:** $\forall p\, .\,\Box(\Box(p\to\Box p)\to p)\to p$.
- **.2 (G):** $\forall p\, .\,\Diamond\Box p\to\Box\Diamond p$.
- **.3:** $\forall p\,q\, .\,\Box(\Box p\to q)\lor\Box(\Box q\to p)$.

Expected connections, to be checked before recording:
- 5 implies .2 and .3.
- M with 5 yields $\Diamond p\to\Box p$, which collapses the modality and conflicts
  with any contingency. 4 is a theorem of C, so B already gives S5, and M with B
  (equivalently ND) collapses too.
- Grz with B likewise collapses, since Grz over S5 forces $p\to\Box p$.
- Their relations to NPC, Atomicity and the existence of worlds need working out,
  as do their boxed forms. With $\Box$ the broadest necessity, boxed and unboxed
  forms may differ.
