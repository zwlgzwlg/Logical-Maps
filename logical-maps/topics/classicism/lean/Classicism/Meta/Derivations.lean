import Classicism.Meta.Translate
import Classicism.Meta.Quoted

/-!
# The record theorems, derived

Every theorem of `Classicism/Proofs.lean` with a strict twin, derived in the object
language by the translator: the home of every `foo.strict.derivable` that the entailments
of `Entailed.lean` cite. Kept apart from them because the derivations are the expensive
part of the build and change only when the proofs do.
-/

set_option maxHeartbeats 0 in
#classicism_derive_audit Classicism.Proofs
