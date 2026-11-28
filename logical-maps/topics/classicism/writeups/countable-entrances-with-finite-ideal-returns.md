# Functional Choice without Tame Rigidity

The universal individual property can be weakly rigid at a Functional Choice point and fail weak inextensibility at the next point. Use two different ideals in the [countable-ideal retraction](countable-ideal-retraction.html). The first step preserves all individuals. The second introduces a new individual while sending parameters from the original root by an elementary embedding.

## The two sets of domains

Start with a countable elementary substructure $M$ of $H_{(\beth_\omega)^+}$, with the sets and choice functions for the finite types used below. All powersets, sequence spaces, ideals, and equivalences at a stage are computed inside its own set-theoretic structure. Set $I=\omega_1$, and write $=_{\rm ct}$ for agreement off a countable subset of $I$, $=_{\rm fin}$ for agreement off a finite subset of $\omega$. There are two kinds of stage, $R$ and $S$. At both the individual carrier is $\omega$. For $\tau=\bar\sigma t$, write $A_R,A_S$ for the respective products of argument domains and put

$$
 R_\tau=\mathcal P(A_R)\times\big(\mathcal P(A_S)^I/{=_{\rm ct}}\big),
 \qquad
 S_\tau=\mathcal P(A_S)\times\big(R_\tau^\omega/{=_{\rm fin}}\big).
$$

Construct $R_\tau$ using the lower argument types, then $S_\tau$ at that same type. The first coordinate gives the current row. For each $R$-entity $x$ choose a representative $f_x$ of its second coordinate. At $S$ choose representatives $v_z$ of the low-index sequences, using literally constant representatives for the classes of constant sequences. For $y\in I$ and $i\in\omega$ put

$$
 H_y(x)=(f_x(y),[\operatorname{const} x]),\qquad L_i(z)=v_z(i).
$$

These are virtual maps. On individuals they are the identity, and $L_iH_yx=x$ at every type. Choices for any fixed finite list of types can be made together inside the structure and transported by elementary embeddings. Equivalently choose one internal section per external finite type in the initial countable structure and carry these sections through its tree of embeddings. Interpret individual names by zero and relational names by top.

## Actual arrows and term transport

At $R(M)$ take a successor for each $M$-generic ultrafilter on $\mathcal P(I)/[I]^{\le\aleph_0}$. For its elementary ultrapower $j:M\to N$ and $k=[\mathrm{id}_I]$, the arrow to $S(N)$ sends $x$ to $H_k^N(jx)$. At $S(N)$ take a successor for each $N$-generic ultrafilter on $\mathcal P(\omega)/\mathrm{Fin}$. For the elementary ultrapower $\ell:N\to N'$ and $l=[\mathrm{id}_\omega]$, the arrow to $R(N')$ sends $z$ to $L_l^{N'}(\ell z)$. Individual maps are $j$ and $\ell$. Objects are finite histories, with paths as arrows. All these structures are externally countable. A generic containing a prescribed internally positive condition exists by meeting their dense sets in sequence. Each two-step composite on an $R$-entity is exactly the elementary image $\ell jx$ because its low return is constant.

The high-index arrow maps individuals onto all individuals at its target. For a function $I\to\omega$ in its source, the conditions contained in a single fiber are dense among the positive conditions. Otherwise a positive condition would be a countable union of countable sets. The generic decides a fiber, so each target natural equals the image of a source one. This argument remains internal at later stages, even if their higher ordinals or natural numbers are externally nonstandard. At a low-index step $[\mathrm{id}_\omega]$ differs from the image of every individual of the preceding structure, since its singleton fibers are null.

For a lambda abstract on $R$-parameters give it its set of current satisfying tuples and the germ of the $S$-rows computed on the corresponding $H_y$-images. At $S$ give it its current row and the low germ of whole $R$-abstracts on the $L_i$-images of its parameters. For each term, form the $R$ case first using the truth of its proper subterms; the $S$ case then uses this already defined $R$ case. Partial application restricts the indicated rows to the supplied arguments. At a high arrow the current $S$ row agrees with the transported $R$ abstract's row because the possible changes of representatives for its finitely many parameters occur in a null set. Its low return is the constant germ of the $R$ abstract on the elementary images of the initial arguments, by $L_iH_y=1$. At a low arrow the whole transported $R$ abstract agrees by the definition of the low germ and Łoś's theorem. Finite intersections suffice for each application. The calculations use equality of entire rows and of whole entities, so the new quantifiers range over all target arguments.

A difference invisible at the current $R$ row is visible along a high generic containing the positive set of differing rows. At $S$ a difference in return germs is visible after a low generic containing its infinite difference set, followed by the preceding $R$ calculation if needed. Thus distinct relations are extensionally separated by the available arrows. These verifications give the action semantics for C. In particular every fixed formula's current truth at an $R$ stage is an internal first-order assertion in its set-theoretic structure with the chosen sections as parameters. Its assertion on transported parameters survives every complete pair of steps by elementarity.

## Choice and the two Barcan verdicts

For a serial relation on current root inputs choose an allowed relational output $D_x$ for each input, internally by Choice. Give the selector the prescribed current rows and at high index $y$ prescribe on $H_yx$ the row of $H_yD_x$. The constant return tag makes $H_y$ injective. For each fixed input the current data and high germ give exactly $D_x$ as a whole output entity. Thus Functional Choice holds at the root.

For a root property $F$ suppose $\forall x^e\,\Box Fx$ there. At any later $R$ stage the same assertion holds on the elementary image of $F$, for all individuals of that stage. Into the next $S$ stage every individual lifts along the high arrow. Thus every individual at every reachable point satisfies the transported $F$. This gives Barcan at input type $e$ at the root. In particular the universal individual property $U$ is weakly inextensible there. Its persistence gives weak rigidity.

At the first $S(N)$ stage take a tester with full current row and low return germ

$$
       [\,i\longmapsto(\lambda x^e.\ x\ne i)_{R(N)}\,] .
$$

Every current individual passes it necessarily. At any low return the tester becomes the whole property of differing from $l=[\mathrm{id}_\omega]$. Every original individual differs from $l$ and all later individual maps are injective. But $l$ itself fails the tester at that return. Hence the universal individual property fails weak inextensibility at $S(N)$. The very same $U$ that was weakly rigid at the designated root is not rigid there. In particular Functional Choice fails to entail Tame Rigidity.

## Rigid bounds at the root

Root Rigid Power nevertheless holds. At each argument tuple type take the tester with full current root row and, at each high index, the $S$-tuples whose relational components have constant low return germs. Individuals need no restriction. Every root tuple necessarily passes this tester. At an even stage the tester and tuple are elementary images, and at each following high entrance the transported tuple has constant returns. Any weakly inextensible root relation lies below this tester.

Suppose a rigid root relation $F$ has infinite current extension $E$. The initial elementary substructure has standard $\omega$ and internally supplies a sequence of distinct tuples $x_i\in E$. At a high successor, every tuple in the current extension of the transported $F$ has a constant low return, say $y$. Form there a tester with full current row and low return sequence of whole $R$-predicates of differing from $jx_i$. For any low generic the excluded tuple $[i\mapsto jx_i]$ differs from the elementary image of $y$ since the sequence is injective. Distinct $R$-entities remain distinct along every continuation: even-stage composites are elementary and each high entrance keeps the whole elementary image as a constant return. Thus the tester necessarily accepts every current member of the transported $F$. But at a low return the excluded tuple itself belongs to the further transport of $F$, whose current row is $\ell jE$. This violates weak inextensibility at the intervening stage. Every rigid root bound must therefore have a finite current extension. The [finite-bound theorem](../index.html#background/rigidity/internally-finite-rigid-power) gives Rigid Power there.

The same proof used only weak inextensibility at the root and at the high successor. Every inextensible relation at the root therefore has finite current extension. In particular the universal individual property has no inextensible coextension.

## Arithmetic and analysis

Inside the initial $\omega$-standard $M$, both modes admit a current predicate for the set of the Frege numeral denotations at each fixed counting type. This set is obtained by iterating the single typed successor operation. It is inductive and all its members are in every inductive current predicate. Every type is internally infinite: individuals are $\omega$, the scalar germ has infinitely many distinct elements, and nonempty higher arities have all internal subsets of their infinite tuple domain as current rows. Hence every finite size is represented and distinct numeral denotations have distinct finite counting behavior. This proves the Peano guards and Axioms of Infinity at $e,t$ in both initial base modes. Each fixed closed assertion transfers at its mode to all later structures by elementarity, including after a low step adds nonstandard individuals. At the designated point the infinite canonical number property at $e$ cannot be rigid by the preceding finite bound. This refutes Arithmetic Necessitism.

The root scalar sort supports a real-number structure. Partition the index set $I$ inside $M$ into countably many uncountable sets. The unions selected by different internal subsets of $\omega$ give distinct scalar germs. These supply labels for the numbers and reals, and the current graphs of their successor and membership are available. Every real-number structure has infinitely many current number labels. Thus there can be no real-number structure of this type whose number property is rigid, refuting Analytic Necessitism.

At either base mode, full internal current rows give each real-number structure precisely the internal subsets of its number sequence as its reals, by extensionality and comprehension. Every internal relation on finite tuples of its number and real labels is available. Thus those structures evaluate any fixed analytical sentence, including its second-order quantifiers, as in $M$. The same applies to arithmetic sentences at Peano types. The two modes agree on these guarded evaluations, and each fixed verdict transfers by the same elementary maps at every finite history. This proves Necessity of Arithmetic and Necessity of Second-Order Analysis.

## Atoms and the two-hat modality

At each kind of stage the order on relations is the product of the current-row order and the germ order. Every nonzero germ splits by dividing its support into two disjoint positive parts. At $R$ split an internally uncountable set into two uncountable subsets; at $S$ split an internally infinite set into two infinite subsets. Thus every atom at either stage is a current-only singleton. At $S$ these atoms die at the next arrow. At $R$ such an atom has empty current row at each odd continuation, and each even image is again a current-only singleton by elementarity. This proves necessary selfhood of atoms at every type. Furthermore, a root entity with nonzero germ becomes instantiated at some high generic and there has a nonzero low return as well as an inhabited current row. It cannot be a self-atom. Every self-atom at $R$ is therefore an atom.

The true root scalar atom $a$ has only its current bit. At a high successor its return is the constant germ of a nonzero atom, which splits by even and odd indices. The transported $a$ stays a self-atom and fails to be an atom there. Thus at the root selfhood need not give strength, the root has no true strong atom, and necessary selfhood-to-atomhood fails even for propositions. These conclusions concern the low-ideal returns; the deterministic-return construction treats this germ differently.

At $R$, the scalar $a$ holds at every even continuation and fails at every odd one. At an odd site its own true current-only atom $v$ becomes impossible after any proper continuation. Hence at that site $\neg\Diamond_{\ne}a$, since it cannot reach a point satisfying $a\land\Diamond v$. Every current $R$ truth holds at every even continuation by elementarity. Consequently $a$ guards the two-hat necessity of every $R$ truth. At an odd site its current-only $v$ itself guards the two-hat necessity of every current truth. This holds at every stage. But $a$ is not ND-necessary at $R$. For each true root guard, after any odd entrance its truth is still possible at the following even stage, and $a$ is false at that odd site.
