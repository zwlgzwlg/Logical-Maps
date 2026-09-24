import Classicism.Meta.Schemas
import Classicism.Meta.Derivations

/-!
# The map's arrows as entailments

Every record theorem of `Classicism/Proofs.lean` — a shallow proof of `P … → Q …`, re-proved
from the eleven identities as `foo.strict` and derived in the object language as
`foo.strict.derivable` — read as an entailment between schemas, `foo.entails :
P.schema ⟹ Q.schema`. This is the one home of those declarations; the derivations they
cite are in `Derivations.lean`.
-/

#classicism_entails_audit Classicism.Proofs
