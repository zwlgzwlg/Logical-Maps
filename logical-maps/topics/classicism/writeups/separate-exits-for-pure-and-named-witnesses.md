# Pure Possibility+ and signature Maximalism without signature Possibility+

For every set-sized signature containing a relational name, pure Possibility+, Possibly Witnessed Possibility and signature Maximalism can all hold while signature Possibility+ fails. The failed instance has just two free individual variables and one relational name.

## The pure model

Let $\kappa=\max(\aleph_0,|\Sigma|)$. The designated object $r$ has an individual domain $I$ of size $\kappa$. Reserve distinct elements to interpret its individual names, leaving two further elements $a\ne b$. Give $r$ a free monoid of words as loops. For every finite prescription of values in $I$ to individual-name labels, include $\kappa$ generators whose individual maps extend that prescription and send $a$ and $b$ to the same value. All nonempty words therefore identify $a,b$.

For each consistent pure formula $P(\bar x)$ with only individual free variables, choose a pointed action model of C and a tuple witnessing $P$. Include the empty tuple. The action presentations used in the [map's coalesced root construction](coalesced-definable-root.html) suffice. Take disjoint copies of the chosen components. For every pairwise distinct root tuple $\bar u$ matching $P$, add a direct entrance to its chosen point, sending $\bar u$ to the witnessing tuple. Distinct input elements can be given these values even when the witness repeats an element. Extend to a total individual map in any way. Call these entrances $U$.

Add a second set of direct entrances $V$ to every object of every chosen component. For every finite prescription from root individual-name labels to individuals of that object, include $\kappa$ such entrances extending the prescription and identifying $a$ and $b$. All component domains are inhabited.

Keep each entrance as a separate generator. A path from $r$ either is a root word or consists of a root word, a single entrance, and an arrow of its old component, in that order. Equality of paths in the latter case requires the same word, entrance and old arrow. There are no arrows back from old components. At a type $\bar\sigma t$, take an arbitrary root tuple row for each root word and an independently chosen whole old entity at each pair consisting of a word and an entrance. The root identity row is the current extension. Word transport restricts to its continuations; entrance transport reads the corresponding whole entity. Subsequent old transport takes place in the component. This prescription is recursive in the argument types. It leaves the pure domains fixed before interpreting relational names.

A difference of word rows is observed there on a tuple. A difference of stored old entities is observed in their component, by its own intensional identity criterion. For a lambda abstract, compute its row at each word from its body with transported parameters, and store at each entrance its old denotation on the transported parameters. Old term closure and arbitrary root rows admit exactly this profile. Application and the Boolean and quantified terms obey the same transport calculation. This gives a model of C.

Every instance of pure Possibility+ holds by its direct $U$ entrance.

## Naming possible witnesses

List the pure matrices with a matching list of distinct names which have a witness anywhere accessible from $r$. For each of the at most $\kappa$ requirements choose one witnessing site and tuple. A witness at the target of a word is a tuple at the root object. Give it a distinct first-letter sector whose generator maps the finitely many individual-name labels as required. On that sector copy each requested relational name's entire witness profile, including its whole old entities at all future entrances. If the witness is at an old object, instead choose a fresh direct $V$ entrance to that object implementing the finite individual prescription. Give each requested relational name its whole old witness there. The individual prescriptions never concern the reserved $a,b$. Distinct first-letter sectors and distinct direct entrances use disjoint coordinates. These assignments establish Possibly Witnessed Possibility.

Signature Maximalism follows as well. In any C-consistent closed signature sentence replace its finitely many distinct names by matching variables and existentially quantify them. The resulting pure sentence is C-consistent, hence possible by pure Possibility+. Possibly Witnessed Possibility then realizes the original sentence with its names.

## The missing joint possibility

Fix a relational name $C$ of any admitted relational type. Write $T(C)=\forall\bar z\,C[\bar z]$, taking $T(C)=C$ at propositional type. Set its root identity row full and set its whole old interpretation to top at **each direct $U$ entrance after the empty word**. These coordinates were all free in the naming argument. In particular a $U$ entrance after a nonempty word can still carry any whole value prescribed by copying a witness.

The matrix $x\ne y\land\neg T(C)$ is C-consistent, as shown by a two-individual extensional model with $C$ bottom. At the designated point its side condition is satisfied by $a,b$, since they are distinct and the matrix contains no individual names. At the identity $T(C)$ is true. Any path beginning with a root letter or a direct $V$ entrance identifies $a$ and $b$, permanently. On every path beginning with a direct $U$ entrance, $C$ is top throughout the old component cone. This exhausts the paths from $r$. The required matrix is consequently impossible for this particular pair.

OpenAI Codex (GPT-6), prompted by Daniel Kodsi, 27 November 2026. Independent GPT-6 researchers checked the signatures, the path decomposition and the whole-entity assignments.
