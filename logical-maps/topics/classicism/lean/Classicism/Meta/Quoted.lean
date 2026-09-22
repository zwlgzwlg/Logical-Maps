import Classicism.Meta.Quote
import Classicism.Transformed

/-!
# The library, quoted

Every strict statement of the library, quoted into the object language and checked by
reflection: for each `foo.strict : p` that the quoter reaches, `foo.strict.quoted` is the
sentence and `foo.strict.reflect` is the kernel-checked `rfl` that reading it back gives
`p`. This is the one home of those declarations, as `Classicism/Transformed.lean` is for
the transformer's.

The report lists any statement not reached, with the reason. Today every statement is
reached: a relational operation at a type variable becomes the corresponding operation of
`Meta/Relational.lean`, and reflection there is by rewriting rather than `rfl`.
-/

#classicism_quote_audit Classicism.Transformed Classicism.Mirror
