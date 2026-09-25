import Classicism.Tools.Translate
import Classicism.Results.Records

/-!
# The record theorems, derived

Every theorem of `Classicism/Results/Records.lean`, derived in the object language by the
translator from its shallow proof: the home of every `foo.derivable` that the entailments
of `Entailed.lean` cite. Kept apart from them because the derivations are the expensive
part of the build and change only when the proofs do.
-/

set_option maxHeartbeats 0 in
#classicism_derive_audit Classicism.Results.Records
