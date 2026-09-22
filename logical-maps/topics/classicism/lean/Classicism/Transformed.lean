import Classicism.Mirror
import Classicism.Proofs
import Classicism.Identities

/-!
# The library, transformed

This module runs the Appendix A transformer over every theorem of the shallow layer, once.
For each theorem `foo : S` that it reaches it declares `foo.nec : S' = ⊤` and
`foo.strict : S'`, from the eleven identities and no `propext` or `funext`; for each
definition whose reading changes, such as `Persistent`, it declares the strict twin. The
kernel checks every one, and `Classicism/Audit.lean` then holds them to the strict check and
the type check.

This is the one home of those declarations. Anything that wants `modal_K.strict` imports
this module; running `#classicism_transform` elsewhere only reports, since the transformer
does not redeclare what exists.

The report lists any theorem not reached, with the reason, and says how many were done in
the outer mode. Today every theorem is reached.
-/

#classicism_transform_audit Classicism.Booleanism Classicism.Identities Classicism.Modal
#classicism_transform_audit Classicism.Order Classicism.Comprehension Classicism.Proofs
