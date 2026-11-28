import Classicism.StrongPossibility.UnaryArbitrarySignature

namespace Classicism.Meta.UnarySP

/-- The pure language is one instance of the uniform closed-signature proof. -/
theorem pure_inconsistent : ¬ AxiomSet.Consistent (AxiomSet.strongPossibility Signature.pure) :=
  inconsistent_in_closed_signature (by intro name; exact nomatch name)

end Classicism.Meta.UnarySP
