import Classicism.Check
import Classicism.TypeSystem
import Classicism.Proofs
import Classicism.Identities
import Classicism.Strict
import Classicism.Quantifier
import Classicism.Transform

/-!
# Audit

Runs the checker over every record proof and every prelude theorem at build time, so
that `lake build` fails if a proof strays outside Classicism. The `Axiomatic`
namespace is not audited: it holds the alternative axioms and nothing proves from them.
-/

-- Every theorem of the library: the prelude, the eleven identities, the record proofs.
#classicism_audit Classicism.Booleanism Classicism.Identities Classicism.Modal
#classicism_audit Classicism.Order Classicism.Comprehension Classicism.Proofs

-- The type-class instances carry the Logical-Equivalence instances that Intensionality
-- uses. They are definitions, not theorems, so the audit names them.
#classicism_check Classicism.instTyE Classicism.instRelProp Classicism.instRelArrow
#classicism_check Classicism.instOrderProp Classicism.instOrderArrow

-- The negative and positive controls for the checker are in `Classicism/Tests.lean`.

/-! ### The term-level type-system check

Every theorem of the library must also stay inside the relational type system: no
quantification over Lean types that a `Ty`, `Rel` or `Order` instance does not guard, no
type outside `R`, and no constant beyond the logical inductives, the `Eq` plumbing and
the formalisation's own metalanguage. -/

#classicism_types_audit Classicism.Booleanism Classicism.Identities Classicism.Modal
#classicism_types_audit Classicism.Order Classicism.Comprehension Classicism.Proofs
#classicism_types_audit Classicism.Algebra Classicism.Strict Classicism.Tautology
#classicism_types_audit Classicism.Quantifier Classicism.Rules Classicism.Primitives

/-! ### The strict layer

The strict modules use no Logical Equivalence at all: `propext` and `funext` are banned
there, and the eleven closed identities stand in their place. This covers the abstract
Boolean algebra, the rule lemmas of the transformer, and the necessitations of the
primitive proof constants. -/

#classicism_strict_audit Classicism.Algebra Classicism.Strict Classicism.Tautology
#classicism_strict_audit Classicism.Quantifier Classicism.Rules Classicism.Primitives

/-! ### The transformer, over the whole library

Every theorem of the shallow layer is run through the Appendix A transformer, which
declares its necessitation and its strict restatement; the kernel checks each, and the
report says which rest on the eleven identities alone. The theorems it does not yet reach
are listed with the reason, which today is one of two things: a law field of the classes
`Rel` and `Order`, which have no strict mirror yet, or a record whose hypothesis is a
schema over types, which needs the outer mode. -/

#classicism_transform_audit Classicism.Booleanism Classicism.Identities Classicism.Modal
#classicism_transform_audit Classicism.Order Classicism.Comprehension Classicism.Proofs
