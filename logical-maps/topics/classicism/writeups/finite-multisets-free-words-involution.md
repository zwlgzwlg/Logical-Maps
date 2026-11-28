# Finite multisets with free words and an involution

For every set-sized signature, Logical Necessity is consistent with necessary
Strong Atomicity at every relational type and a true proposition that fails
to be 5-necessary. Hence even the additional necessary Strong Actuality,
Barcan Formula and Countable Boolean Completeness below do not make every
truth 5-necessary.

## Adding the involution

Take the [finite-multiset model](finite-multisets-free-words.html), with its
one individual and one object, and replace its arrow monoid $M$ by
$M\times C_2$. Write $1$ for the identity and $s$ for the unit with zero
multiset, empty word, and bit one. Thus $s^2=1$. Retain the same type
recursion, comparing two profile rows on a pin when their multiset sizes,
words, and *bits* are the same. Postcomposition preserves these comparisons,
so the original parameter-pin argument gives closure under all terms.

Each single arrow is still isolated by its multiset size, the multiplicities
on its finite support, its word, and its bit. Each nonzero relational entity
therefore contains a single-arrow, single-tuple atom. Every arrow remains
right-cancellable, so a transport of this atom is either bottom or another
singleton. This proves necessary Strong Atomicity at all relational types;
the proposition supported at $1$ is a true strong atom.

For the Barcan Formula, use the original lift by subtracting the incoming
multiset and stripping the incoming word suffix. For the input bit of
the lifted row subtract the incoming bit in $C_2$. This adds no pins and
gives surjectivity at all types. To obtain Logical Necessity, glue the
realizing assignments on their designated final letters exactly as in the
original model, retaining the bit coordinate of each assigned profile.
The resolving one-letter arrows have zero multiset and bit zero. Necessary
Countable Boolean Completeness follows by the same proof as before: all
current sets of standard numeral values are admitted inductive rows, so each
internally countable family is externally at most countable and the union
of its profiles is pinned. Propositional Boolean Completeness still fails.
Use the original family of size-one, empty-word atoms with the additional
bit fixed at zero. A join must distinguish the two unbounded sets of indices
outside its pin.

## A true proposition with a failing S5 test

Let $X^{tt}$ have at every arrow the constant row
\[
   \{p\in D_t:p(1)\ \text{and}\ p(s)\}.
\]
This entity has empty pin and all arrows transport it to itself. By the
application rule, at any arrow $h$ one has
\[
   (Xp)(h)\quad\Longleftrightarrow\quad p(h)\land p(sh).
\]
The operator satisfies each of the map's three S5 conditions at every
arrow. For N, a necessarily true proposition holds in particular at both
$h$ and $sh$. For K, pointwise modus ponens works at both. For B, if $p(h)$
holds, then $\neg X\neg p$ holds at $h$ and at $sh$: each two-point test
includes $h$, since $s^2=1$. Thus $X\neg X\neg p$ holds at $h$.
These checks apply to every current proposition at the sole object,
including each new assignment at an arrow. Hence $\operatorname{S5}(X)$.

Now take $p$ true just at $1$. It is actually true but false at $s$, so
$Xp$ fails. As $\Box_5 p$ requires every S5 operator to accept $p$, it
too fails. The pure counterexample repeats at the sole object. By the
ordering $\Box_{\ne}\le\hat{\hat\Box}\le\Box_5$, the same $p$ also fails
the two-hat and distinctness-preserving necessity tests.

OpenAI Codex (GPT-6), prompted by Daniel Kodsi, produced this variation on
26 November 2026. Two additional OpenAI Codex agents independently checked the construction
and the modal separation.
