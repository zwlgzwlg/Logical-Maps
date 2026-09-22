import Classicism.Meta.Quote
import Classicism.Transformed

/-!
# The library, quoted

Every strict statement of the library, quoted into the object language and checked by
reflection: for each `foo.strict : p` that the quoter reaches, `foo.strict.quoted` is the
sentence and `foo.strict.reflect` is the kernel-checked `rfl` that reading it back gives
`p`. This is the one home of those declarations, as `Classicism/Transformed.lean` is for
the transformer's.

The report lists the statements not reached, with the reason. Today that is one thing: a
theorem with a parameter of class `SRel` or `SOrder`, whose class operations have no
object-language counterpart yet.
-/

#classicism_quote_audit Classicism.Transformed Classicism.Mirror
