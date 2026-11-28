import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Order.BooleanSubalgebra
import Mathlib.Order.Atoms

/-! Periodic subsets in an arbitrary integer action. The Boolean row algebra
consists of sets fixed by some nonzero period. Singletons are its only possible
atoms, even when the row contains points of infinite orbit. -/

namespace Classicism.Meta.PeriodicIntegerRows

variable {α : Type*} [AddAction ℤ α]

def Periodic (U : Set α) : Prop :=
  ∃ n : ℤ, n ≠ 0 ∧ ∀ (k : ℤ) (x : α), (n * k) +ᵥ x ∈ U ↔ x ∈ U

theorem inter {U V : Set α} (hU : Periodic U) (hV : Periodic V) :
    Periodic (U ∩ V) := by
  obtain ⟨n, hn, hU⟩ := hU
  obtain ⟨m, hm, hV⟩ := hV
  refine ⟨n*m, mul_ne_zero hn hm, fun k x => ?_⟩
  exact (by simpa [mul_assoc] using hU (m*k) x : ((n*m)*k) +ᵥ x ∈ U ↔ x ∈ U).and
    (by simpa [mul_assoc, mul_left_comm, mul_comm] using hV (n*k) x)

private def suborbit (x : α) (n : ℤ) : Set α := Set.range fun k : ℤ => (n*k) +ᵥ x

private theorem mem_suborbit (x : α) (n : ℤ) : x ∈ suborbit x n := by
  exact ⟨0, by simp⟩

private theorem periodic_suborbit (x : α) {n : ℤ} (hn : n ≠ 0) : Periodic (suborbit x n) := by
  refine ⟨n,hn,?_⟩
  intro k a
  constructor
  · rintro ⟨j,hj⟩
    refine ⟨j-k, ?_⟩
    have e := congrArg (fun z : α => (-(n*k)) +ᵥ z) hj
    rw [← add_vadd, ← add_vadd, neg_add_cancel, zero_vadd] at e
    change (n*(j-k)) +ᵥ x = a
    rw [mul_sub]
    simpa only [sub_eq_add_neg, add_comm] using e
  · rintro ⟨j,rfl⟩
    refine ⟨k+j, ?_⟩
    change (n*(k+j)) +ᵥ x = _
    rw [mul_add, add_vadd]

/-- Distinct tuples can be separated by one periodic test. No finite-orbit
hypothesis on the tuple or on the original action is used. -/
theorem exists_separating {x y : α} (hxy : x ≠ y) :
    ∃ V : Set α, Periodic V ∧ x ∈ V ∧ y ∉ V := by
  classical
  by_cases fixed : ∃ n : ℤ, n ≠ 0 ∧ n +ᵥ x = x
  · obtain ⟨n,hn,hx⟩ := fixed
    refine ⟨suborbit x n, periodic_suborbit x hn, mem_suborbit x n, ?_⟩
    rintro ⟨k,rfl⟩
    have hmem : n ∈ AddAction.stabilizer ℤ x := hx
    have hsum := (AddAction.stabilizer ℤ x).zsmul_mem hmem k
    exact hxy (by simpa [zsmul_eq_mul, mul_comm, AddAction.mem_stabilizer_iff] using hsum.symm)
  have faithful : Function.Injective (fun i : ℤ => i +ᵥ x) := by
    intro a b hab
    by_contra neq
    apply fixed
    refine ⟨a-b, sub_ne_zero.mpr neq, ?_⟩
    have same := congrArg (fun z : α => (-b) +ᵥ z) hab
    rw [← add_vadd, ← add_vadd, neg_add_cancel, zero_vadd] at same
    simpa [sub_eq_add_neg, add_comm] using same
  by_cases inOrbit : y ∈ suborbit x 1
  · obtain ⟨k,hk⟩ := inOrbit
    change (1*k) +ᵥ x = y at hk
    rw [one_mul] at hk
    have nonzero : k ≠ 0 := by
      rintro rfl
      exact hxy (by simpa using hk)
    let n : ℤ := (k.natAbs + 1 : ℕ)
    have hn : n ≠ 0 := Int.natCast_ne_zero.mpr (Nat.succ_ne_zero _)
    refine ⟨suborbit x n, periodic_suborbit x hn, mem_suborbit x n, ?_⟩
    rintro ⟨i,hi⟩
    have eq := faithful (hi.trans hk.symm)
    apply nonzero
    exact Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (show n ∣ k from ⟨i,eq.symm⟩) (show k.natAbs < (k.natAbs + 1 : ℕ) from Nat.lt_succ_self _)
  · exact ⟨suborbit x 1, periodic_suborbit x one_ne_zero, mem_suborbit x 1, inOrbit⟩

def Atom (U : Set α) : Prop :=
  U.Nonempty ∧ ∀ V : Set α, Periodic V → V ⊆ U → V.Nonempty → V = U

theorem atom_iff_singleton (U : Set α) (hU : Periodic U) :
    Atom U ↔ ∃ x : α, U = {x} := by
  constructor
  · rintro ⟨⟨x,hx⟩,minimal⟩
    refine ⟨x, Set.eq_singleton_iff_unique_mem.mpr ⟨hx, ?_⟩⟩
    intro y hy
    by_contra neq
    obtain ⟨V,hV,hxV,hyV⟩ := exists_separating (Ne.symm neq)
    have eq := minimal (U ∩ V) (inter hU hV) Set.inter_subset_left ⟨x,hx,hxV⟩
    exact hyV ((eq.symm ▸ hy : y ∈ U ∩ V).2)
  · rintro ⟨x,rfl⟩
    refine ⟨⟨x,rfl⟩, ?_⟩
    rintro V _ hs ⟨v,hv⟩
    apply Set.Subset.antisymm hs
    intro y hy
    have ev : v = x := hs hv
    have ey : y = x := hy
    exact (ey.trans ev.symm).symm ▸ hv


/-- The admitted Boolean algebra of rows, ordered by ordinary inclusion. -/
def algebra (α : Type*) [AddAction ℤ α] : BooleanSubalgebra (Set α) where
  carrier := {U | Periodic U}
  infClosed' _ hU _ hV := inter hU hV
  supClosed' := by
    rintro U ⟨n,hn,hU⟩ V ⟨m,hm,hV⟩
    refine ⟨n*m, mul_ne_zero hn hm, fun k x => ?_⟩
    exact (by simpa [mul_assoc] using hU (m*k) x : ((n*m)*k) +ᵥ x ∈ U ↔ x ∈ U).or
      (by simpa [mul_assoc, mul_left_comm, mul_comm] using hV (n*k) x)
  compl_mem' := by
    rintro U ⟨n,hn,hU⟩
    exact ⟨n,hn, fun k x => (hU k x).not⟩
  bot_mem' := ⟨1,one_ne_zero, fun _ _ => Iff.rfl⟩

private theorem ne_bot_iff (U : algebra α) : U ≠ ⊥ ↔ U.1.Nonempty := by
  rw [Set.nonempty_iff_ne_empty]
  exact not_congr ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem isAtom_iff_singleton (U : algebra α) :
    IsAtom U ↔ ∃ x : α, U.1 = {x} := by
  rw [← atom_iff_singleton U.1 U.2, isAtom_iff_le_of_ge]
  constructor
  · rintro ⟨hne, hmin⟩
    refine ⟨(ne_bot_iff U).mp hne, fun V hV sub hv => ?_⟩
    exact Set.Subset.antisymm sub (hmin ⟨V,hV⟩ ((ne_bot_iff ⟨V,hV⟩).mpr hv) sub)
  · rintro ⟨hne,hmin⟩
    exact ⟨(ne_bot_iff U).mpr hne, fun V hv sub =>
      (hmin V.1 V.2 sub ((ne_bot_iff V).mp hv)).ge⟩

/-- A periodic translation-invariant row of integers can never be a singleton.
Thus the terminal-only all-integers property admits no subrow which becomes
an atom in the full powerset algebra of the terminal. -/
theorem integers_no_singleton {U : Set ℤ} (hU : Periodic U) : ¬∃ x, U = {x} := by
  rintro ⟨x,rfl⟩
  obtain ⟨n,hn,h⟩ := hU
  have e : n + x = x := by simpa using (h 1 x).2 rfl
  apply hn
  omega


private theorem product_atom_cases {A B : Type*} [PartialOrder A] [OrderBot A]
    [PartialOrder B] [OrderBot B] {u : A} {v : B} (atom : IsAtom (u,v)) :
    (IsAtom u ∧ v = ⊥) ∨ (u = ⊥ ∧ IsAtom v) := by
  have min := isAtom_iff_le_of_ge.mp atom
  by_cases root : u = ⊥
  · refine Or.inr ⟨root, isAtom_iff_le_of_ge.mpr ⟨?_, ?_⟩⟩
    · intro empty
      exact min.1 (Prod.ext root empty)
    · intro w hw wv
      exact (min.2 (⊥,w) (fun e => hw (congrArg Prod.snd e)) ⟨bot_le,wv⟩).2
  · refine Or.inl ⟨isAtom_iff_le_of_ge.mpr ⟨root, ?_⟩, ?_⟩
    · intro w hw wu
      exact (min.2 (w,⊥) (fun e => hw (congrArg Prod.fst e)) ⟨wu,bot_le⟩).1
    · exact le_bot_iff.mp (min.2 (u,⊥) (fun e => root (congrArg Prod.fst e)) ⟨le_rfl,bot_le⟩).2

/-- At a two-sector root an atom has one occupied tuple in exactly one sector.
In particular its image under projection to the full terminal powerset is
bottom or an atom of that unrestricted powerset. -/
theorem two_sector_atom {β : Type*} [AddAction ℤ β]
    {U : algebra α} {V : algebra β} (atom : IsAtom (U,V)) :
    ((∃ x, U.1 = {x}) ∧ V.1 = ∅) ∨ (U.1 = ∅ ∧ ∃ y, V.1 = {y}) := by
  obtain ⟨hu, hv⟩ | ⟨hu, hv⟩ := product_atom_cases atom
  · exact Or.inl ⟨(isAtom_iff_singleton U).mp hu, congrArg Subtype.val hv⟩
  · exact Or.inr ⟨congrArg Subtype.val hu, (isAtom_iff_singleton V).mp hv⟩

/-- If shifting a member by each multiple of a common period preserves a
family as a set, its union is an admitted row. Individual members can have
different periods. This is the Boolean-completeness step at the root. -/
theorem union_periodic {E : Set (Set α)} {n : ℤ} (hn : n ≠ 0)
    (permutes : ∀ (k : ℤ) (U : Set α), U ∈ E → {x | (n*k) +ᵥ x ∈ U} ∈ E) :
    Periodic (⋃₀ E) := by
  refine ⟨n, hn, fun k x => ?_⟩
  constructor
  · rintro ⟨U,hU,hx⟩
    exact ⟨_, permutes k U hU, hx⟩
  · rintro ⟨U,hU,hx⟩
    refine ⟨_, permutes (-k) U hU, ?_⟩
    change (n*(-k)) +ᵥ ((n*k) +ᵥ x) ∈ U
    simpa [← add_vadd] using hx

#print axioms two_sector_atom
#print axioms union_periodic

#print axioms isAtom_iff_singleton
#print axioms integers_no_singleton

end Classicism.Meta.PeriodicIntegerRows
