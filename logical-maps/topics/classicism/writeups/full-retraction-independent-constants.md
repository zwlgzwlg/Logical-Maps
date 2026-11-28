# Full retraction with independently movable constants

For every admitted set-sized signature, Independence and Functional Choice
hold at a point where the Barcan Formula fails at individual type. At the
same point distinctness at every type is necessary.

Start with [the full two-object retraction](full-two-object-retract.html).
Its arrows are the identities, $h:r\to s$, $j:s\to r$ and the idempotent
$hj$, with $jh=1_r$. Take its product with the one-object group
$G=\bigoplus_{c\in\Sigma}C_2$. Arrows carry a group element and
composition adds the labels. The individuals at $r$ are a fixed base
element and two partners for each individual name. At $s$ add one new
individual $*$, let $h$ include the old ones and let $j$ send $*$ to the
base element. A generator for an individual name exchanges the two partners
of that name and fixes everything else. All generators fix the base and
$*$. These permutations commute with the entrance and retraction.

Use full typed action domains. At a relational type an entity has an
arbitrary extension row at each outgoing arrow, on the tuples at that
arrow's target. Transport takes sections by composition. Interpret an
individual name by its first partner at $r$. For a relational name $c$,
take the profile with full row exactly at arrows whose label has $c$-bit
one, and empty row elsewhere. For a proposition the tuple is empty.
Evaluate named formulas from this root assignment, transporting names
along the evaluation arrow. Equivalently, unfold at the root, taking an
object for each arrow from $r$ and morphisms given by its continuations.

The $c$-generator fixes the values of all other names. It moves the value
of $c$ by exchanging partners or complementing its rows. Closed pure
operations commute with transport. Thus every pure term applied to other
names is fixed by this loop, and cannot equal $c$. This proves Independence
for the signature.

Every arrow $u$ out of $r$ has a left inverse. Functoriality gives a left
inverse to its transport at every type, so it preserves distinctions.
For Functional Choice, take any serial current relation and select an
output $Y_a$ of its relational output type for each current input $a$.
At each $u$, define the row of an operation at the tuple $(u a,\bar z)$
to be true exactly when $\bar z$ is in the current extension of $uY_a$.
Injectivity makes this prescription single-valued. Fill the row with
false on other inputs. Fullness admits the resulting operation. At every
continuation its value on $a$ has exactly the extension of $Y_a$ there,
so its value is $Y_a$ as an entity. This proves Functional Choice at $r$.

Finally take the property with row $u[D_e(r)]$ at every arrow $u$ from
$r$. It necessarily contains each individual at $r$. Its row at the
entrance $(h,0)$ omits the new individual $*$. This refutes the ordinary
Barcan Formula and gives the stated separation.
