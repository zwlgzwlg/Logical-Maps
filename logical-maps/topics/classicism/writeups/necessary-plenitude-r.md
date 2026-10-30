# Necessary worlds and persistent atoms are boxed Plenitude

OpenAI Codex, prompted by Daniel Kodsi. 28 October 2026.

The intuitive statement is: **necessarily, some true proposition remains an atom at every accessible evaluation**. The proof below identifies this with □Plenitude and with atomic coverage by propositions that are necessarily worlds. The inner atom condition includes nonzeroness. It differs from Strong Atomicity, whose strong atoms may become bottom.

For any **one fixed relational type** \(\rho\), let
\[
 P_\rho:\quad\forall R^\rho\bigl(R\ne0_\rho\to
          \exists a^\rho(\Box\operatorname{Atom}_\rho(a)\land a\le R)\bigr).
                                                               \tag{1}
\]
Over C, (1) is equivalent to boxed Plenitude. In particular the full
relational schema adds nothing beyond any one such instance. In words,
every nonzero relation contains a part which remains an atom. Necessary
nonzeroness is included in \(\Box\operatorname{Atom}\); it must not be
dropped or replaced by the usual strong-world condition alone.

This is a structural presentation of \(C5+\operatorname{Atomicity}\).
It requires no observer, uniform selector, extra BF or Choice premise.

## 1. Existential projection carries atoms to atoms

Suppose \(K:A\to B\) is a Boolean homomorphism and \(L:B\to A\) its
left order adjoint. If \(b\) is an atom, then \(Lb\ne0\): otherwise
adjunction gives \(b\le K0=0\). For any \(a\in A\), atomhood decides
\(Ka\); complement preservation and adjunction give
\(Lb\le a\) or \(Lb\le\neg a\). Thus \(Lb\) is an atom.

For \(\rho=\sigma_1\cdots\sigma_n t\), C supplies admitted canonical
operations
\[
 K(p)=\lambda\bar x.p,\qquad L(R)=\exists\bar x\,R[\bar x],
 \qquad L(R)\le p\ \longleftrightarrow\ R\le K(p).          \tag{2}
\]
The orders are whole relational Boolean orders, not current pointwise
orders. The boxed formulas defining (2) contain H-equivalent quantifier
formulas, so C's strict Logical Equivalence rule proves the adjunction
unconditionally. \(K\) is Boolean and injective, by applying an equality
to one tuple of the standing nonempty domains. The empty tuple case is
identity. No tuple-choosing operation is needed.

The atom-projection implication for these canonical terms is therefore
a C theorem. Necessitating that discharged theorem yields
\(\Box\operatorname{Atom}_\rho(a)\to
\Box\operatorname{Atom}_t(La)\). If \(p\ne0\), injectivity makes
\(Kp\ne0\). Apply (1) to \(Kp\), then (2), to obtain a necessarily
atomic proposition below \(p\). Thus any \(P_\rho\) gives \(P_t\),
with no BF and without requiring the relation atom to have a current instance.

## 2. Coverage makes a true persistent atom necessarily available

Let \(\chi:=\exists w^t(w\land\Box\operatorname{Atom}_t(w))\).
If \(\neg\chi\ne0\), \(P_t\) supplies necessarily atomic
\(w\le\neg\chi\). Modal 4 makes its necessary atomhood itself
necessary; existential introduction therefore gives
\(\Box(w\to\chi)\), or \(w\le\chi\). This forces \(w=0\),
contradicting atomhood and T. Hence \(\neg\chi=0\), namely \(\Box\chi\).
Only unconditional logical implications and modal 4 were necessitated.

## 3. A true persistent atom supplies ND and Actuality

C proves the unconditional implication
\[
                    \chi\longrightarrow ND_t\land\operatorname{Actuality}.
                                                               \tag{3}
\]
For a true necessarily atomic \(w\), its current atomhood puts it below
every current truth, so it is an Actuality witness. Let \(d=(p=q)\)
be a currently false identity. Atomhood and truth of \(w\) force
\(w\le\neg d\). This literal order identity persists by NI. If \(d\)
became true, NI would make its value Top there; then the persistent bound
would force \(w=0\), contrary to necessary atomhood. Thus
\(\Box\neg d\), proving current \(ND_t\).

Necessitate the discharged (3), and apply \(\Box\chi\). We obtain
\(\Box ND_t\) and necessary Actuality. The native recorded type-transfer
theorem gives all-type boxed ND, or C5. The native theorem C5 plus
necessary Actuality gives Atomicity, and C5 plus Atomicity gives boxed
Plenitude. Their source attribution remains Bacon–Dorr; the new proof
does not replace or reattribute those lemmas.

## 4. Boxed Plenitude supplies the same atom witnesses

Native results give C5 and all-type Atomicity from boxed Plenitude.
Over C5 each current atom remains atomic: every Boolean decision
\(a\le B\) or \(a\le\neg B\) is a disjunction of literal identities,
so persists; BF collects the deciding argument quantifier, and necessary
ND keeps \(a\ne0\). Thus \(\operatorname{Atom}(a)\to
\Box\operatorname{Atom}(a)\). Apply Atomicity to each nonzero \(R\)
and retain its atom to prove (1). No uniform selection of atoms is made.

The same reasoning gives the useful equivalent world statement
\(\Box\exists w(w\land\Box\operatorname{Atom}(w))\).
The atomic-coverage formulation can therefore be displayed as its own
principle with equivalence arrows, without changing this theory. The
already native Dorr route from 5 plus Strong Leibniz to this theory
is not counted as a newly solved connection.

## Sources and verification scope

Direct original research source: OpenAI Codex, prompted by Daniel Kodsi,
*Adjunctions, atom projection, and persistent worlds*,
28 October 2026, §§1–5, unpaginated;
*Pure uniformity and one necessary atom*,
§§3–4. The general Boolean-adjunction lemma is elementary; no historical
priority is claimed for it.

Native bridges used without changing their proofs:

- `necessary-distinctness-necessary-t-implies-necessary-distinctness-necessary-r`:
  Bacon–Dorr, *Classicism*, Proposition 2.2, p. 22 (16 May 2023 draft).
- `c5-and-necessary-actuality-imply-atomicity`:
  Proposition 2.6, pp. 25–26.
- `c5-and-atomicity-imply-necessary-plenitude`, and the two native
  boxed-Plenitude-to-C5/Atomicity directions.

The witness order is \(\exists a\,\Box\operatorname{Atom}(a)\).
