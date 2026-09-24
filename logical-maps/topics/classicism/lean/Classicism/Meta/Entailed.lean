import Classicism.Meta.Schemas
import Classicism.Meta.Derivations

/-!
# The map's arrows as entailments

Every record theorem of `Classicism/Proofs.lean` — a shallow proof of `P … → Q …`, derived
in the object language as `foo.derivable` — read as an entailment between schemas,
`foo.entails : P.schema ⟹ Q.schema`. This is the one home of those declarations; the derivations they
cite are in `Derivations.lean`.
-/

#classicism_entails_audit Classicism.Proofs
