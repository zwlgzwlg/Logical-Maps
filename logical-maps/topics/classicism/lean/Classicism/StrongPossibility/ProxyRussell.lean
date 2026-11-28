import Classicism.StrongPossibility.ProxyTerms

namespace Classicism.Meta.ProxyDiagonal
variable {Sig : Signature}

export Diagonal (russell_self)

theorem rho_d {Ax : AxiomSet Sig} {Δ : List (Sentence Sig)} : Derivable Ax Δ (.app rho d) :=
  russell_self Q

end Classicism.Meta.ProxyDiagonal
