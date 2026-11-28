import Classicism.Certified.Arithmetic
import Classicism.Certified.Box5
import Classicism.Results.Records.C5

/-! One scalar countable join yields a guarded Barcan inference for the Frege numbers.
The pure recurrent labels and the incompleteness argument are given in the accompanying proof. -/

namespace Classicism.Proofs.RecurrentCells
open Classicism.P Classicism.Paper

variable {σ : Type} [Ty σ]
abbrev Num (σ : Type) := (σ → Prop) → Prop

def cell (G : Prop) (J : Num σ → Prop) (n : Num σ) := G ∧ J n

def family (G : Prop) (J : Num σ → Prop) (p : Prop) :=
  ∃ n, FiniteCardinality n ∧ p = cell G J n

/-- The precise native countability predicate holds for this family at its counting sort. -/
theorem countable_family (G : Prop) (J : Num σ → Prop) : Ctbl σ (family G J) :=
  ⟨fun p n => p = cell G J n, fun _ _ hpq =>
    ⟨fun h => h.elim fun _ ⟨_, hp, hq⟩ => hp.trans hq.symm,
     fun hpq' => hpq.1.elim fun n ⟨hn, hp⟩ => ⟨n, hn, hp, hpq'.symm.trans hp⟩⟩⟩

def uniqueLabel (J : Num σ → Prop) := ∀ n k, FiniteCardinality n → FiniteCardinality k →
  J n → J k → k = n

def recurrent (G : Prop) (J : Num σ → Prop) := ModalB ∧
  (∀ n, FiniteCardinality n → ◇ (cell G J n)) ∧ □ (G → uniqueLabel J)

def reader (J X : Num σ → Prop) := ∃ n, FiniteCardinality n ∧ J n ∧ X n

theorem below_join (G s : Prop) (J : Num σ → Prop) (hs : LUB s (family G J))
    (n : Num σ) (hn : FiniteCardinality n) : cell G J n ≤ s :=
  (hs s).2 (le_refl_prop s) _ ⟨n, hn, rfl⟩

theorem introduce_reader (G : Prop) (J X : Num σ → Prop) (n : Num σ) :
    FiniteCardinality n → X n → cell G J n → reader J X := fun hn hx hc =>
  ⟨n, hn, hc.2, hx⟩

theorem join_below_reader (G s : Prop) (J X : Num σ → Prop) (hs : LUB s (family G J))
    (hx : ∀ n, FiniteCardinality n → □ (X n)) : s ≤ reader J X :=
  (hs _).1 (fun _ he => he.elim fun n ⟨hn, hp⟩ => hp.symm ▸
    (le_iff_prop _ _).2 (modal_K _ _ (modal_K _ _ (nec% (introduce_reader G J X n))
      (finiteCardinality_box n hn)) (hx n hn)))

theorem read_label (G s : Prop) (J X : Num σ → Prop) (n : Num σ)
    (hu : G → uniqueLabel J) (hn : FiniteCardinality n) (hd : cell G J n ≤ s)
    (hr : s ≤ reader J X) (hc : cell G J n) : X n :=
  have ht := imp_of_le_prop _ _ hr (imp_of_le_prop _ _ hd hc)
  ht.elim fun k ⟨hk, hj, hx⟩ => (hu hc.1 n k hn hk hc.2 hj) ▸ hx

theorem possible_reading (G s : Prop) (J X : Num σ → Prop) (n : Num σ)
    (hrec : recurrent G J) (hn : FiniteCardinality n) (hd : cell G J n ≤ s)
    (hr : s ≤ reader J X) : ◇ (X n) :=
  dia_mono _ _ (modal_K _ _ (modal_K _ _ (modal_K _ _ (modal_K _ _
    (nec% (read_label G s J X n)) hrec.2.2) (finiteCardinality_box n hn))
    (box_le_prop _ _ hd)) (box_le_prop _ _ hr)) (hrec.2.1 n hn)

def nextCovered (G s : Prop) (J : Num σ → Prop) (n : Num σ) :=
  cell G J (SucCard n) ≤ s

theorem local_coverage (G s : Prop) (J : Num σ → Prop) (hrec : recurrent G J)
    (h0 : cell G J (ZeroCard σ) ≤ s) (hr : s ≤ reader J (nextCovered G s J)) :
    ∀ n, FiniteCardinality n → cell G J n ≤ s := fun _ hn =>
  (hn (fun k => FiniteCardinality k ∧ cell G J k ≤ s)
    ⟨⟨finiteCardinality_zero, h0⟩, fun k ⟨hk, hd⟩ =>
      ⟨finiteCardinality_suc k hk, b_dia_box_imp hrec.1 _
        (dia_mono _ _ (nec% (box_le_prop (cell G J (SucCard k)) s))
          (possible_reading G s J (nextCovered G s J) k hrec hk hd hr))⟩⟩).2

theorem local_conclusion (G s : Prop) (J X : Num σ → Prop)
    (hrec : G → recurrent G J) (h0 : cell G J (ZeroCard σ) ≤ s)
    (hnext : s ≤ reader J (nextCovered G s J))
    (hx : s ≤ reader J (fun k => □ (G → X k))) (hg : G) :
    ∀ n, FiniteCardinality n → X n := fun n hn =>
  b_dia_box_imp (hrec hg).1 _ (possible_reading G s J _ n (hrec hg) hn
    (local_coverage G s J (hrec hg) h0 hnext n hn) hx) hg

/-- Frege induction takes place under the guard and covers all new local numbers there. -/
theorem guarded_numerical_barcan (G s : Prop) (J X : Num σ → Prop)
    (hs : LUB s (family G J)) (hrec : □ (G → recurrent G J))
    (hx : ∀ n, FiniteCardinality n → □ (G → X n)) :
    □ (G → ∀ n, FiniteCardinality n → X n) :=
  have hnext := join_below_reader G s J (nextCovered G s J) hs fun n hn =>
    box_le_prop _ _ (below_join G s J hs (SucCard n) (finiteCardinality_suc n hn))
  have hread := join_below_reader G s J (fun k => □ (G → X k)) hs fun n hn =>
    modal_four _ (hx n hn)
  modal_K _ _ (modal_K _ _ (modal_K _ _ (modal_K _ _
    (nec% (local_conclusion G s J X)) hrec)
    (box_le_prop _ _ (below_join G s J hs (ZeroCard σ) finiteCardinality_zero)))
    (box_le_prop _ _ hnext)) (box_le_prop _ _ hread)

/-- An explicit persistent guard. Its extra condition A can include the Peano axioms. -/
def guard (A : Prop) (J : Num σ → Prop) := □ (A ∧ ModalB ∧ uniqueLabel J ∧
  ∀ n, FiniteCardinality n → ◇ (J n))

theorem guard_is_recurrent (A : Prop) (J : Num σ → Prop) (hg : guard A J) :
    recurrent (guard A J) J :=
  have hb : □ (guard A J) := modal_four _ hg
  have hU : □ (uniqueLabel J) := modal_K _ _
    (nec% (fun (h : A ∧ ModalB ∧ uniqueLabel J ∧ ∀ n, FiniteCardinality n → ◇ (J n)) =>
      h.2.2.1)) hg
  ⟨(box_elim hg).2.1, fun n hn => dia_mono _ _
     (nec% (fun (h : J n ∧ guard A J) => (⟨h.2, h.1⟩ : cell (guard A J) J n)))
     (dia_and_of_dia_box _ _ ((box_elim hg).2.2.2 n hn) hb),
   box_imp_of_box _ _ hU⟩

theorem guarded_numerical_barcan_of_join (A s : Prop) (J X : Num σ → Prop)
    (hs : LUB s (family (guard A J) J))
    (hx : ∀ n, FiniteCardinality n → □ (guard A J → X n)) :
    □ (guard A J → ∀ n, FiniteCardinality n → X n) :=
  guarded_numerical_barcan _ s J X hs (nec% (guard_is_recurrent A J)) hx

end Classicism.Proofs.RecurrentCells

#classicism_derive Classicism.Proofs.RecurrentCells.guarded_numerical_barcan
#classicism_derive Classicism.Proofs.RecurrentCells.guarded_numerical_barcan_of_join
#classicism_derive Classicism.Proofs.RecurrentCells.countable_family
