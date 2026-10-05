import Classicism.Certified.Schemas
import Classicism.Syntax.Infinity

/-!
# The Infinity schemas

`fregean-incompatible-with-infinity-t`: under the Fregean Axiom there are at most two
propositions, `⊤` and `⊥`, while the Infinity schema at `t` has three distinct ones at
`n = 3`. The object-level step is the shallow lemma `fregean_not_three`, certified once; the
instance of the schema at `n = 3` is the sentence it refutes.

Not here: the arrows into the Infinity schemas from the Axioms of Infinity, Atomlessness
and Distinctness (pure), each an induction on `n`.
-/

namespace Classicism

/-- Under the Fregean Axiom there are no three distinct propositions: two of any three
have the same truth value, and so are identical. -/
theorem fregean_not_three : P.FregeanAxiom →
    ¬ ∃ p q r : Prop, (¬ p = q ∧ ¬ p = r ∧ True) ∧ (¬ q = r ∧ True) ∧ True ∧ True :=
  fun fa h => h.elim fun p h => h.elim fun q h => h.elim fun r h =>
    (em p).elim
      (fun hp => (em q).elim (fun hq => h.1.1 (fa p q ⟨fun _ => hq, fun _ => hp⟩))
        (fun hq => (em r).elim (fun hr => h.1.2.1 (fa p r ⟨fun _ => hr, fun _ => hp⟩))
          (fun hr => h.2.1.1 (fa q r ⟨fun h' => absurd h' hq, fun h' => absurd h' hr⟩))))
      (fun hp => (em q).elim
        (fun hq => (em r).elim (fun hr => h.2.1.1 (fa q r ⟨fun _ => hr, fun _ => hq⟩))
          (fun hr => h.1.2.1 (fa p r ⟨fun h' => absurd h' hp, fun h' => absurd h' hr⟩)))
        (fun hq => h.1.1 (fa p q ⟨fun h' => absurd h' hp, fun h' => absurd h' hq⟩)))

#classicism_derive Classicism.fregean_not_three

namespace Meta

open AxiomSet

/-- `fregean-incompatible-with-infinity-t`, through the instance of the Infinity schema at
`n = 3`. -/
theorem fregean_infinityT_inconsistent :
    ¬ Consistent (P.FregeanAxiom.schema ∪ infinityT Signature.pure) := fun hc =>
  not_consistent_of_imp_neg fregean_not_three.derivable
    (Consistent.mono (fun a ha => ha.elim Or.inl (fun h => Or.inr ⟨3, by decide, h⟩)) hc)

end Meta

end Classicism
