import Classicism.Tools.Check
import Classicism.Tools.TypeSystem
import Classicism.Strict.Transformed

/-!
# Audit of the strict layer

The strict modules use no Logical Equivalence at all: `propext` and `funext` are banned
there, and the eleven closed identities stand in their place. This covers the abstract
Boolean algebra, the rule lemmas of the transformer, the necessitations of the primitive
proof constants, the mirrors, and what the transformer declares over the library, which
is held to the same checks as anything written by hand.
-/

#classicism_types_audit Classicism.Strict.Algebra Classicism.Strict.Vocabulary Classicism.Strict.Tautology
#classicism_types_audit Classicism.Strict.Quantifier Classicism.Strict.Rules Classicism.Strict.Primitives
#classicism_types_audit Classicism.Strict.Mirror

#classicism_strict_audit Classicism.Strict.Algebra Classicism.Strict.Vocabulary Classicism.Strict.Tautology
#classicism_strict_audit Classicism.Strict.Quantifier Classicism.Strict.Rules Classicism.Strict.Primitives
#classicism_strict_audit Classicism.Strict.Mirror

#classicism_strict_audit Classicism.Strict.Transformed
#classicism_types_audit Classicism.Strict.Transformed
