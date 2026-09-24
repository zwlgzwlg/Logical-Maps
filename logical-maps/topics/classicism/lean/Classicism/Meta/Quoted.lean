import Classicism.Meta.Quote
import Classicism.Proofs

/-!
# The record theorems, quoted

Every record theorem of `Classicism/Proofs.lean`, quoted into the object language and
checked by reflection: for each `foo : p` that the quoter reaches, `foo.quoted` is the
sentence and `foo.reflect` the kernel-checked proof that reading it back gives `p`, by
`rfl` where the reading is definitional and by rewriting where a relational operation
sits at a type variable or the shallow connectives are read (`Meta/Relational.lean`).
This is the one home of those declarations.
-/

#classicism_quote_audit Classicism.Proofs
