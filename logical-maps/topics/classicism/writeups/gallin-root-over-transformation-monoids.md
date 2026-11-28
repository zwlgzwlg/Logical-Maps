# Gallin Extensional Comprehension with an accessible self-atom that splits

Use one root $r$ and countably many sites $s_i$. At each site the ordinary arrows are the monoid of all maps $\mathbb N\to\mathbb N$, with the permutations $G$ acting as its designated symmetries. The integers here label arrows. The individual domain in the logic is a singleton throughout.

Adjoin $h_i:r\to s_i$ and $j_i:s_i\to r$, with $j_i h_i=1_r$. Each ordinary map $m$ at $s_i$ satisfies $mh_i=h_i$ and $j_i m=j_i$. Include all resets $h_kj_i$ as distinct from the ordinary arrows, and compose any path through $r$ by these rules. The root has no further loops.

At each relational type use the [split Functional Choice construction](functional-choice-over-supported-stages.html). A root entity consists of any current tuple row $R$ and a $G$-invariant row $V_i$ at each site. An entity at $s_i$ consists of a profile on the ordinary arrows satisfying $U_{gm}=g[U_m]$ for $g\in G$, together with an independent whole root entity $x$ for its return coordinate. No finite pin is required. Ordinary $m$ transports the profile by right translation and fixes $x$. The map $j_i$ projects to $x$. The value of $h_i$ on a root entity has the constant ordinary row $V_i$ and the original entity as return coordinate. The invariance of $V_i$ gives the required equivariance. These definitions proceed by recursion on type. Evaluate an abstract from its current tuples at each arrow; the old group symmetries preserve satisfaction, giving ordinary equivariance and invariance of the rows on the $h_i$-images. Its return is the root abstract on the returned parameters. This is the term-closure calculation for the split construction. At a site the order is separate inclusion on ordinary profiles and on the entire return coordinate. Take top for relational names.

## The root choice, comprehension and power principles

Given a root row $R$, choose $V_i=j_i^{-1}[R]$ on argument tuples. This is invariant because $j_i g=j_i$. Membership is preserved in both directions by every arrow. The root-to-site step uses $j_i h_i=1$, ordinary steps use $j_i m=j_i$, and a return uses the definition of $V_i$. This gives the Gallin coextension of $R$.

All current choice graphs are admitted. To realize a selector by an operation, prescribe its output on a root input $x$ and prescribe the transported output on $h_i x$ at each site. Each $h_i$ is injective and the $h_i$-images are fixed by all ordinary arrows, so these prescriptions are consistent and invariant. The operation agrees as a whole entity on every root input, which proves Functional Choice.

For any current tuple set $E$, use $E$ and the exact images $h_i[E]$ as its rows. These define a rigid relation $H_E$. Every weakly rigid relation with row $E$ equals $H_E$ by persistence and the weak-inextensibility tester $H_E$. This gives Rigid Comprehension and Tame Rigidity. At $s_i$ each member of the transported bound lies in $h_i[E]$. The current row of any weakly rigid subrelation there is consequently $h_i[E']$ for some $E'\subseteq E$. Its weak rigidity makes it identical to the rigid $h_iH_{E'}$ with that row. This lifts every eligible subrelation, at all proper arrows from the root as well as at its identity. Each power predicate hence has exact images, and composing arrows preserves those images. This proves both rigid power principles at the root. The root algebra is a powerset at each type, with independent current tuples and site-orbits of tuples, so it is complete and atomic.

For revised Mathematical Possibilism apply the singleton-individual argument in the [same construction](functional-choice-over-supported-stages.html). The finitely many uniform extensional order-and-field tables contain zero and are closed under successor. A rigid family of them is bounded by the finite union of the haecceities of its current members, so its limit is again uniform. Thus the inexact ordinal benchmark is finite. Full current graphs make every countably infinite set power-closed, and every infinite carrier contains one. Each finite Boolean algebra occurs as the interval under a sum of finitely many isolated site scalars.

## The two boxed failures

Fix a site. At scalar type its ordinary coordinate consists of all postpermutation-invariant sets of endomaps. Let $f(n)=n+1$ and

$$
    P=\{m:mf\in G\}.
$$

Give the scalar with ordinary profile $P$ the bottom root return. Whenever it is true at an ordinary arrow $k$, $kf$ is a permutation, so the transported ordinary profile is precisely $G$. The return remains bottom. Since $G$ is one postpermutation orbit, $(G,0)$ is an atom in the site's product order. Every reset or return takes the original scalar to bottom. This proves its self-atomhood.

The two maps $m_i(n+1)=n$, $m_i(0)=i$ for $i=0,1$ are both in $P$. Their postpermutation orbits differ, since only the first satisfies $m_i(0)=m_i(1)$. Intersecting $P$ with this equality test splits the scalar. Thus an accessible self-atom of propositional type is neither an atom nor strong. The same argument also shows that the site's true atom $(G,0)$ fails to be strong, since its transport along $f$ is the scalar just split. The root satisfies Gallin Extensional Comprehension with failure of both boxed self-atom principles. Compare the corrected argument for [the second unpinned object](symmetric-two-object-unpinned.html).
