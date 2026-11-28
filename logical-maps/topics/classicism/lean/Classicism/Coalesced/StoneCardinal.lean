import Classicism.Coalesced.StoneOrdinalBound
import Mathlib.SetTheory.Cardinal.Aleph

/-! A ZFC strong-limit cut above all actual inexact ordinal carriers of the
canonical family. Both the cut and its strictness are independent of X. -/

namespace Classicism.Meta.Coalesced.StoneFan.Canonical

open Cardinal Ordinal
open scoped Cardinal

noncomputable section

variable (Sig : Signature) [Countable Sig.Const]

def ordinalCut : Cardinal := beth ((#(OrdinalBound Sig)).ord + omega0)

theorem bound_lt_cut : #(OrdinalBound Sig) < ordinalCut Sig :=
  (le_beth_ord _).trans_lt (beth_strictMono (lt_add_of_pos_right _ omega0_pos))

theorem cut_strong_limit : IsStrongLimit (ordinalCut Sig) :=
  isStrongLimit_beth.2 (isSuccLimit_add _ isSuccLimit_omega0).isSuccPrelimit

theorem actual_ordinal_lt_cut (X : Type) [TopologicalSpace X] :
    #(ActualOrdinal Sig X) < ordinalCut Sig :=
  (Cardinal.mk_le_of_injective (ordinalEmbedding Sig X).injective).trans_lt (bound_lt_cut Sig)

#print axioms actual_ordinal_lt_cut
#print axioms cut_strong_limit

end
end Classicism.Meta.Coalesced.StoneFan.Canonical
