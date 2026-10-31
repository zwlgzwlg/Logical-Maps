# Current countable completeness connects analytic and arithmetic necessitism

GPT-6 Astra, prompted by Daniel Kodsi, 30 October 2026. The numerical-haecceity join method and parameterized arithmetic stability are from Zachary Goodsell's *Arithmetic is Necessary*, Lemmas 3–4, 8 and Theorem 9. The current cut-field and fixed-reference constructions are proved in [[analytic-necessitism-and-transversal-imply-arithmetic-necessitism]].

Over C,

\[
 \mathrm{AN}+\mathrm{CBC}\ \longrightarrow\ \mathrm{Arithmetic\ Necessitism}.
\]

CBC is current. For each source type \(\sigma\), only the CBC instance counting at \(\sigma\) and joining relations of type \(\rho=((\sigma t)t)t\) is needed, together with AN at that same real host \(\rho\). Propositional CBC is not a substitute.

## 1. Canonical representatives from countable joins

Fix \(\sigma\), put \(\nu=(\sigma t)t\), \(\rho=\nu t\), and assume the Arithmetic Necessitism guard \(\Box I^*_\sigma\). Write \(N=\mathbb N_\sigma\). For a current subproperty \(C\subseteq N\), let

\[
 H_n=\lambda z^\nu(n=z),\qquad
 W_C=\lambda Y^\rho\,\exists n(Nn\land Cn\land Y=H_n).
\]

This is natively countable at \(\sigma\). The same displayed relation with \(n\) free supplies the shared-code witness: shared codes imply equal members, and equal members share any code witnessing membership. No choice of codes or operation is extracted.

CBC supplies a LUB \(J_C\) at \(\rho\), with respect to necessary inclusion. The LUB is literally unique by antisymmetry. Its current extension is exactly \(C\):

* Every current \(Cn\) gives \(H_n\leq J_C\), hence \(J_Cn\).
* Goodsell's number-persistence lemma makes \(N\) an algebraic upper bound of every selected \(H_n\). Thus \(J_C\leq N\), excluding all current nonnumbers.
* If a current number \(m\) is outside \(C\), necessary distinctness under \(\Box I^*_\sigma\) gives \(H_n\leq\neg H_m\) for every selected \(n\). Thus \(J_C\leq\neg H_m\), excluding \(m\).

Only current membership in \(W_C\) is used. No claim about persistence of \(C\), future members of its family, or preservation of current truth by arbitrary joins is required.

If \(C,C'\) are currently coextensive, their displayed families have exactly the same current members, hence the same upper bounds. Their joins lie below each other and are literally identical. Conversely identical joins give coextensive inputs by the preceding paragraph.

## 2. A current real field and the arithmetic bridge

Use the internally coded rational field \(Q\subseteq N\) and its cut predicate from sections 1–3 of [[analytic-necessitism-and-transversal-imply-arithmetic-necessitism]]. All its operations are relational graphs, and the small-gap calculation uses induction with arbitrary cut parameters; it assumes no external standardness of the canonical numbers.

Define the admitted family

\[
 F(J)\ \longleftrightarrow\
 \exists C\bigl(\operatorname{Cut}(C)\land
                    \operatorname{LUB}_\rho(J,W_C)\bigr).
\]

It contains exactly one literal representative of every current cut extension. This is a single lambda-defined family. It is not assembled from scalar values and does not require an operation choosing joins.

The cut-field construction needs representatives only for cuts: the zero and one cuts, every raw operation output, and the union cut of each admitted nonempty bounded family. Therefore \(F\) supplies every representative it uses. Literal uniqueness gives equality, functionality of the relational graphs and antisymmetry. For a bounded nonempty admitted family of represented cuts, its lambda-defined union is a cut, and its representative is the LUB. The family's size is unrestricted: it is the numerical code family of the **union cut** to which CBC is applied. The resulting field is natively complete for all admitted bounded families. The least-inductive predicate gives its natural part. Hence

\[
 \Box I^*_\sigma+\mathrm{CBC}_{\sigma,\rho}
 \ \longrightarrow\ \exists\mathfrak R\,\operatorname{Real}_\rho(\mathfrak R).
\tag{1}
\]

Current AN at \(\rho\) now supplies a rigid necessarily-real reference field. The fixed Peano reference theorem, proved in section 4 of the linked write-up, transfers rigidity and necessary distinctness to the canonical \(\sigma\)-numbers. Discharging \(\Box I^*_\sigma\) yields Arithmetic Necessitism at \(\sigma\). No optional premise was necessitated.

## 3. The field-existence lemma needs only current infinity

For completeness, the stronger local existence statement is

\[
 I^*_\sigma+\mathrm{CBC}_{\sigma,\rho}
 \ \longrightarrow\ \exists\mathfrak R\,\operatorname{Real}_\rho(\mathfrak R).
\tag{2}
\]

Goodsell's Theorem 9 gives guarded stability for every arithmetic formula with current numerical parameters. Its only completeness use is Lemma 8 at the displayed CBC instance. Rational validity, least-code normalization and rational order expand into such arithmetic formulas. Under current \(I^*_\sigma\), the current \(I_\sigma=\Diamond I^*_\sigma\) holds, so a currently true arithmetic formula has its positive guarded necessary sign.

For current rational \(q<r\), apply this to the **whole** formula

\[
 Qq\land Qr\land
 \forall x\in N\bigl((Qx\land x<q)\to x<r\bigr).
\]

Put \(L_q=\lambda x(I_\sigma\land Qx\land x<q)\). The boxed quantified comparison gives \(L_q\leq L_r\): at future points satisfying \(I_\sigma\) it compares every numerical argument, and elsewhere both guarded predicates are empty. This does not exchange box and quantification or box the CBC premise. All these predicates are below \(G=\lambda x(I_\sigma\land Qx)\).

For a current rational cut \(C\), the family of \(L_q\) with \(q\in C\) is countable by the same shared-code construction. Its unique join \(J\) lies below \(G\), excluding nonrationals now. Roundedness puts every \(x\in C\) in some \(L_q\) with \(q\in C\), hence in \(J\). If \(r\notin C\) is rational, every \(q\in C\) has \(q<r\), making \(L_r\) an algebraic upper bound. Therefore \(Jr\) is false by irreflexivity. Thus the join has exactly the current cut extension.

Equal current cuts again give the same literal join. The lambda-defined range of this join relation supplies the same restricted cut representatives and field construction, proving (2). The arithmetic-object implication already follows from the shorter proof (1); (2) records the precise strength of its field-existence step.

## 4. Necessary CBC and the existing arithmetic-truth consequence

Separately, [[necessary-countable-completeness-implies-arithmetic-necessitism]] is a recovered source composition. Necessitate Goodsell's **discharged** conditional from CBC to weak inextensibility of the numbers, then apply K. Necessary CBC gives native inextensibility with its leading box; unconditional persistence and guarded distinctness supply the other clauses.

Current CBC already implies Necessity of Arithmetic by Goodsell's recorded theorem. The new connection here concerns **Arithmetic Necessitism**, the rigidity of the number objects. These proofs leave current CBC alone implying that object principle unresolved, and do not imply full Transversal or a necessarily correct cut selector.
