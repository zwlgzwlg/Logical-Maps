import Classicism.StrongPossibility.UnaryArbitrarySignature
import Classicism.StrongPossibility.FiniteProxyGuards
import Classicism.StrongPossibility.Predecessor
import Classicism.StrongPossibility.ProxyCanonical

/-! The two incompatible return visits in any admitted public signature. -/

namespace Classicism.Meta.ProxyDiagonal

open Term Coalesced DescriptorColours StrongPossibilityReturn StrongPossibilityLicences FiniteMaxSupport

variable {Sig : Signature} {ρ : RTy}

/-- Every finite fragment of ordinary Maximalism and one guard uses a finite
marked language. Its Max licences reflect to the public language, including
when the public language contains no individual name. -/
theorem arbitrary_licence (hS : Sig.Closed) (c : Sig.Const)
    (hc : Sig.typeOf c = .rel ρ) (s : Bool) :
    AxiomSet.Consistent (AxiomSet.maximalist ∪ AxiomSet.single (endpoint s c hc)) := by
  apply consistent_max_of_finite hS _ {c} (Set.finite_singleton c)
  intro U hU K hp
  have m : c ∈ U := K (Set.mem_singleton c)
  rw [narrow_endpoint U s c hc m hp]
  let _ : Finite (marked U).Const := marked_finite hU
  have ne : Nonempty (DistinguishedDefinable.names (Sig := marked U) .e) :=
    ⟨⟨Sum.inr (), rfl⟩⟩
  have both := named_licences (marked_closed hS U) ne Q
    (canonical_proxy_separation (predecessors (marked U))) (Sum.inl ⟨c,m⟩) hc
  cases s
  · exact both.2
  · exact both.1

/-- Strong Possibility is inconsistent in every signature admitted by the map. -/
theorem inconsistent_in_admitted_signature (hs : Sig.Admitted) :
    ¬ AxiomSet.Consistent (AxiomSet.strongPossibility Sig) :=
  UnarySP.inconsistent_in_admitted_signature hs

end Classicism.Meta.ProxyDiagonal
