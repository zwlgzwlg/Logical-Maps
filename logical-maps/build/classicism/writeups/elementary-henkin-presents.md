# Subset-closed elementary Henkin presents

GPT-6 Astra, prompted by Daniel Kodsi, 30 October 2026. The full-present construction and its product-order criterion are due to Daniel Kodsi, using the earlier classical-present machinery of Cian Dorr. The construction below chooses elementary leaves with controlled subset closure. The two sizes serve different purposes.

Over external ZFC, the countably closed model satisfies necessary Countable Boolean Completeness, necessary Actuality and necessary Inextensible Comprehension, together with Analytic Necessitism and Necessity of Second-Order Analysis, but fails full Boolean Completeness and Second-Order Analytic Necessitism. The continuum-closed model satisfies Second-Order Analytic Necessitism, necessary Countable Boolean Completeness and necessary Strong Atomicity, while still failing full Boolean Completeness.

All types use the fixed relational type system of C. Completeness at a Henkin leaf concerns admitted families. Completeness at its full present must also handle families whose projections are external subsets of the leaf algebra. This difference supplies the missing joins.

## 1. Elementary leaves with exact subset codes

Let \(\mathfrak c=2^{\aleph_0}\), and let \(F\) be the full standard extensional typed hierarchy over \(F_e=\omega\), with \(F_t=2\) and terminal modality. Present it as a countable many-sorted first-order structure, with application, logical operations, and all finite parameterized-lambda templates. Each finite type is a set; all these sorts together form a set-sized structure. Elementary substructures retain every parameter instance of comprehension.

For each infinite relational sort \(\tau\), choose an ordinary real-field copy \(X_\tau\subseteq F_\tau\). Include every point of this copy and its carrier, order, addition, multiplication and natural-part relations, together with zero and one, in the seed. Such a copy exists: an infinite relational sort is a full power set of an infinite argument product, so has at least \(\mathfrak c\) members. Include every individual as well. There are countably many types.

For the **countable closure**, start with an elementary hull of this seed of size \(\mathfrak c\). Build a continuous elementary chain of length \(\omega_1\). At each successor stage, for each sort, add the actual \(F\)-characteristic predicate \(\chi_T\) of every external countable subset \(T\) of that stage's domain; then take an elementary hull. The number of additions is at most \(\mathfrak c^{\aleph_0}=\mathfrak c\). The union \(H\) has size \(\mathfrak c\) and is elementary in \(F\). Every countable subset of a final sort is contained in one earlier stage, by regularity of \(\omega_1\), so its exact characteristic predicate belongs to \(H\).

For the **continuum closure**, put \(\lambda=2^{\mathfrak c}\), add every member of \(F_{(et)t}\) to the seed, and take an elementary chain of length \(\mathfrak c^+\). At each successor stage add exact characteristic predicates for every subset of each stage domain of size at most \(\mathfrak c\). Every stage and the union have size \(\lambda\), since

\[
\lambda^{\mathfrak c}=\lambda,\qquad \mathfrak c^+\leq\lambda.
\]

Regularity of \(\mathfrak c^+\) ensures that every final subset of size at most \(\mathfrak c\) is contained in one stage. Thus the union has precisely the required closure. Neither construction assumes CH or regularity of \(\mathfrak c\).

The word *exact* matters: \(\chi_T\) has extension \(T\) on the entire ambient \(F\)-domain, not merely on one stage. This ensures that existential unions computed in \(F\) introduce no extra members later.

Restriction to \(H\) argument domains is faithful. Distinct relations in \(H\) have a distinguishing tuple in \(F\), and elementarity supplies such a tuple in \(H\). Consequently \(H\), with these restricted applications and terminal modality, is an extensional Henkin model of C. Parameterized lambda terms and quantifiers have their inherited interpretations.

Both leaves have \(H_e=\omega\) and \(H_{et}=\mathcal P(\omega)\): every subset of \(\omega\) receives an exact countable code. Every finite \(F\)-sort is wholly retained by elementarity. Every infinite relational \(H\)-sort contains its seeded \(\mathfrak c\) real points. In the smaller leaf every such sort therefore has size exactly \(\mathfrak c\). In the larger leaf the sort sizes are at most \(\lambda\), and \(H_{(et)t}=F_{(et)t}\) has size exactly \(\lambda\).

## 2. The full present and its order

Add a root \(R\) with identity individual transport and, recursively at relational types \(\tau=\alpha_1\cdots\alpha_k t\), domains

\[
R_e=\omega,\qquad
R_\tau=\mathcal P\!\left(\prod_iR_{\alpha_i}\right)\times H_\tau,
\qquad q_\tau(S,h)=h.
\]

The empty argument product handles \(\tau=t\). There are just the root and its terminal future \(H\). A relation's first coordinate is its arbitrary current extension; its second is its whole future entity. Application has the specified current truth value and the application of the transported entities as its future coordinate. Connectives, equality, quantifiers and abstractions have the corresponding two coordinates; identity is literal at each point. Modality at the root tests both the current and terminal evaluations.

Every projection is onto: \((\varnothing,h)\) lifts an arbitrary relational \(h\), and individual transport is the identity. Hence quantified terms project to the original \(H\)-quantifiers, including their entire future domains. Abstraction of an arbitrary formula has an admitted first-coordinate extension and its admitted \(H\)-abstraction as second coordinate. These observations verify the application, lambda, quantifier and transport clauses of the full-present construction. The classical and modal rules hold at both evaluations. H-equivalent abstractions have the same current extension and the same \(H\)-component, so are literally equal; the theoremhood restriction on Logical Equivalence is preserved. Thus this is a C model.

Native order is necessary inclusion. For \(A=(S,a),B=(T,b)\), it is precisely

\[
 A\leq B\quad\Longleftrightarrow\quad S\subseteq T\text{ and }a\leq_H b.
\tag{1}
\]

This compares whole profiles; current-row inclusion alone would be insufficient.

## 3. Countable completeness and a missing larger join

Let \(T\subseteq H_\tau\) be an external family within the leaf's closure bound. Its exact family code \(W=\chi_T\) belongs to \(H_{\tau t}\). Parameter comprehension gives

\[
u_T=\lambda\bar x\,\exists Y^\tau(WY\land Y[\bar x]).
\]

In \(F\) this is the genuine union of the full rows in \(T\); hence in \(H\) it is their union and their LUB against every admitted upper bound. Independently, terminal \(H\) satisfies **internal full BC**, since every admitted family has its lambda union. External subset closure is needed only for families not already admitted there.

At the root, for each counting type \(\sigma\), the current canonical numbers are exactly the external successor orbit

\[
 O_\sigma=\{\operatorname{Suc}_\sigma^n(\mathbf0_\sigma):n\in\omega\}.
\]

The root admits a predicate with exactly that current extension and an arbitrary leaf component. It is currently inductive, so leastness gives \(\mathbb N_\sigma\subseteq O_\sigma\); ordinary external finite induction gives the reverse inclusion. The orbit may repeat when \(\sigma\) is finite, which does not affect countability.

If a current family is natively countable at \(\sigma\), its shared-code witness assigns each member a code from \(O_\sigma\), with the same code only for equal members. Assign each member the least external index of an assigned successor iterate. This is an external injection into \(\omega\); it requires no object-language operation choosing codes. Thus the current family \(S\subseteq R_\tau\) is externally countable, at every counting type.

Its projection \(q[S]\) has a leaf union \(u_{q[S]}\). Equation (1) proves that

\[
 J=\left(\bigcup_{Y\in S}\operatorname{row}_R(Y),u_{q[S]}\right)
\]

is a root LUB against every test. This proves every current CBC instance, for every relational output type. Every instance also holds at \(H\) by its internal full BC. Hence **necessary CBC** holds in both models. In fact the larger root has external joins for all families of size at most \(\mathfrak c\), by the same argument.

Full BC nevertheless fails. In the smaller leaf put \(\delta=et\), \(\kappa=\mathfrak c\); in the larger put \(\delta=(et)t\), \(\kappa=\lambda\). In each case \(|H_\delta|=\kappa\), while \(|H_{\delta t}|\leq\kappa\). Choose an external \(A\subseteq H_\delta\) not represented by any leaf predicate. Each singleton \(a_x=\lambda y(y=x)\) and its complement belong to \(H_{\delta t}\).

The external family \(\{a_x:x\in A\}\) has **no** leaf LUB. Any upper bound contains \(A\), and the complement of each omitted singleton is an upper bound. A least upper bound would therefore exclude every point outside \(A\) and represent \(A\), a contradiction. This rules out alternative upper bounds as well as the missing literal union.

Lift the singletons as \(b_x=(\varnothing,a_x)\), and admit at the root a family whose current members are exactly the \(b_x\), with leaf component bottom. If \((J_0,j_H)\) were its LUB, comparison with every \((\varnothing,z_H)\) for a leaf upper bound \(z_H\) would make \(j_H\) a leaf LUB. This is impossible. Thus BC fails at \((et)t\) in the smaller model and at \(((et)t)t\) in the larger. No failure at type \(t\) is involved.

## 4. Actuality, inextensible coextensions and strong atoms

At \(R\), the true proposition \((1,0)\) entails every current truth \((1,b)\). At \(H\), top witnesses Actuality. Therefore Actuality holds necessarily.

Any root relation with current row \(S\) has coextensive representative \((S,\bot_H)\). If a test is necessarily true of each current member, it contains the whole row now and faces no members in the terminal image. This proves current weak inextensibility. At the terminal point weak inextensibility is automatic, giving the required leading box. Thus the representative is inextensible. Terminal relations supply their own coextensions, so IC holds necessarily at every relational type.

For completeness, singleton comprehension makes every nonzero leaf relation contain a singleton atom. Such an atom decides every admitted leaf relation and is therefore strong. The product algebra (1) has exactly two kinds of atoms:

\[
 (\{\bar a\},\bot_H),\qquad (\varnothing,s_{\bar b}),
\]

where \(s_{\bar b}\) is a leaf singleton. Every nonzero root relation contains one. Each atom decides every root relation according to its nonzero coordinate. At \(H\), its image is respectively bottom or a singleton, each of which decides every future relation. Hence each root atom satisfies the native boxed decision clause. A strong atom may become bottom; its nonzero clause is current. This proves necessary Strong Atomicity at every relational type, including \(t\), in both constructions. The displayed root truth atom and terminal top also witness necessary Strong Actuality. These are consequences of the full-present geometry with an extensional terminal leaf.

## 5. Rigid real fields at the same carrier

Fix an infinite relational host \(\tau\). Its seed contains the entire ordinary real copy \(X_\tau=\{a_s:s\in\mathbb R\}\), together with every field graph. Lift its points to \(x_s=(\varnothing,a_s)\), and lift each graph with its graph on the \(x_s\) as current row and its seeded graph as leaf component. The future extension of each graph is exactly the image of its current extension.

An exact-image relation is rigid. Membership persists. If an arbitrary root test is necessarily true of its current tuples, it is true at \(H\) of every image tuple, hence of the whole leaf graph. This is weak inextensibility against **every** test. At terminal \(H\), weak persistence and weak inextensibility hold automatically, so both native leading boxes are verified. Transport is injective on the chosen points, giving necessary distinctness.

The same field is Real at both points. At the root it is the ordinary real field with all current subproperties available. At the leaf all its ordinary points and graphs remain present, so every admitted bounded nonempty subproperty has its external real supremum among the seed points. Its natural part is the standard one. Thus this tuple witnesses the consequent of AN at its original host.

The finite/infinite status of each relational root sort agrees with its \(F\)-sort, by induction through the pair definition. Finite carriers cannot support a real field. At the root \(e=\omega\) cannot either, because full current predicates give Real its external meaning. At the leaf, the typed sentence asserting no real field on \(e\), and the corresponding sentences for finite sorts, transfer from \(F\) by elementarity. Countability alone would not justify this claim about an arbitrary Henkin field. These cases exhaust the types. Full same-carrier AN holds in both models.

## 6. Necessary second-order analytical truth

Fix a host and a standard finite sentence in the map's analytical grammar. Relation variables there are used extensionally on field points, without modal tests or literal identity tests on the relation entities. Let \(\varepsilon\) be its usual truth value in the ordinary real field with full finite-arity relation quantification.

The typed first-order presentation of \(F\) satisfies the sentence saying that **every** Real tuple at this host has sign \(\varepsilon\). Elementarity transfers that universal sentence to \(H\). This treats every admitted leaf field, not only the seeded copy, and does not assert that every leaf field is externally complete. At the root, full current rows make each Real tuple an ordinary real field and realize every finite-arity relation on it. The same universally signed sentence therefore holds there. Both points agree, proving the exact Necessity of Second-Order Analysis schema. Duplicate intensions do not affect the stipulated grammar.

## 7. Why the smaller leaf cannot represent a real power

Consider any proposed root SOAN witness with current field carrier \(X\). Root fullness makes \(X\) an ordinary real carrier of cardinality \(\mathfrak c\). Its necessarily distinct points have injective transport.

For every external \(A\subseteq X\), root fullness provides a relation with precisely that extension. The current instance of the boxed representation clause supplies a member \(U_A\) of the proposed power family agreeing with it on \(X\). This member is rigid and supported on \(X\), so has exactly extension \(A\).

If \(x\in A\setminus B\), persistence gives \(\Box U_Ax\). Every current member \(y\) of \(U_B\) differs necessarily from \(x\), by necessary distinctness of \(X\). Weak inextensibility of \(U_B\), applied to the complement of the haecceity of \(x\), therefore gives \(\Box\neg U_Bx\). Their projections to \(H\) differ. Choosing one representative per subset externally, or using uniqueness of coextensive weakly rigid representatives, yields an injection

\[
 \mathcal P(X)\hookrightarrow H_{\tau t}.
\]

Its source has cardinality \(2^{\mathfrak c}\), while every smaller-leaf sort has size at most \(\mathfrak c\), contradiction. The argument defeats every field and power-family candidate. At host \(et\) the field constructed in section 5 makes the possible-Real antecedent true, so SOAN fails already at unary power.

## 8. Why the larger leaf admits whole finite-arity powers

Fix a seeded field \(X\) at host \(\tau\) and a finite \(k\geq1\). Every external \(T\subseteq X^k\) has size at most \(\mathfrak c\). For each tuple in \(T\), parameter comprehension gives its tuple-haecceity relation. The family of these has size at most \(\mathfrak c\), hence an exact admitted family code. Its existential union gives an \(H\)-relation \(h_T\) whose extension on the entire \(F\)-domain is exactly \(T\).

The **whole family** is admitted separately by comprehension:

\[
 P_H^k=\lambda S^{\tau\cdots\tau t}\,
       \forall\bar x(S[\bar x]\to X^k[\bar x]).
\]

Its extension is exactly \(\{h_T:T\subseteq X^k\}\). Every supported relation has some such external extension and is identified with its code by faithful extensionality. This family may have size \(2^{\mathfrak c}\); we did not apply the smaller-subset closure bound to it.

Use the common exact-image field lift \(X_R\) from section 5. For each \(T\), form \(U_T=(T^R,h_T)\), where \(T^R\) is its inverse image under the carrier bijection. These relations are rigid and supported on \(X_R^k\). The root family

\[
 P_R^k=(\{U_T:T\subseteq X^k\},P_H^k)
\]

is admitted by full current rows and has exactly its current image as its entire leaf extension. The same arbitrary-test proof shows that this **family entity** is rigid, as well as each member.

At the root an arbitrary relation has a restriction to \(X_R^k\), and the corresponding \(U_T\) represents it. At \(H\), the restriction of every admitted relation is represented by its \(h_T\). These two local verifications prove the boxed universal-existential representation clause, with its full future quantifier domain. They do not require a uniform witness or an exchange of box and existence.

For each fixed finite bound, the families for all smaller arities coexist over the same field. The finite and individual-carrier vacuity cases are those of section 5. Thus the larger model satisfies full SOAN while retaining the missing higher Boolean join of section 3.
