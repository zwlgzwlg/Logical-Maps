import Classicism.Results.SentenceSchemas.Arithmetic
import Classicism.Results.Records.Arithmetic

/-!
# Arithmetic atoms over guarded Peano points

Goodsell's impredicative sum and product graphs are total on the source numbers and
functional at Peano points. Hence a guarded Peano hypothesis suffices to decide
their values uniformly across the guard.
-/

namespace Classicism.GuardedArithmetic
variable {σ : Type} [Ty σ]

local notation "N" => Arith.N σ
local notation "Z" => Arith.zero σ
local notation "S" => Arith.suc σ
local notation "Sum" => Arith.Sum σ
local notation "Prod" => Arith.Prod σ
local notation "ν" => Arith.ν σ

theorem sum_total (m n : ν) (hm : N m) (hn : N n) : ∃ o, N o ∧ Sum m n o :=
  (hn (fun i => N i ∧ ∃ o, N o ∧ Sum m i o)
    ⟨⟨arith_N_zero, m, hm, arith_Sum_zero m⟩, fun i h =>
      ⟨arith_N_suc i h.1, h.2.elim fun j hj =>
        ⟨S j, arith_N_suc j hj.1, arith_Sum_step m i j h.1 hj.1 hj.2⟩⟩⟩).2

theorem prod_total (m n : ν) (hm : N m) (hn : N n) : ∃ o, N o ∧ Prod m n o :=
  (hn (fun i => N i ∧ ∃ o, N o ∧ Prod m i o)
    ⟨⟨arith_N_zero, Z, arith_N_zero, arith_Prod_zero m⟩, fun i h =>
      ⟨arith_N_suc i h.1, h.2.elim fun j hj => (sum_total m j hm hj.1).elim fun k hk =>
        ⟨k, hk.1, arith_Prod_step m i j k h.1 hj.1 hk.1 hj.2 hk.2⟩⟩⟩).2

def sumCases (m n o : ν) :=
  (n = Z ∧ o = m) ∨ ∃ i j, N i ∧ N j ∧ Sum m i j ∧ n = S i ∧ o = S j

theorem sum_cases (m n o : ν) (h : Sum m n o) : sumCases m n o :=
  (h (fun i j => Sum m i j ∧ sumCases m i j)
    ⟨arith_Sum_zero m, Or.inl ⟨rfl, rfl⟩⟩ fun i j hi hj a =>
      ⟨arith_Sum_step m i j hi hj a.1, Or.inr ⟨i, j, hi, hj, a.1, rfl, rfl⟩⟩).2

theorem sum_at_zero (hI : IStar σ) (m o : ν) (h : Sum m Z o) : o = m :=
  (sum_cases m Z o h).elim And.right fun h => h.elim fun i h => h.elim fun _j h =>
    ((hI i i h.1 h.1).1 h.2.2.2.1).elim

theorem sum_at_succ (hI : IStar σ) (m i o : ν) (hi : N i) (h : Sum m (S i) o) :
    ∃ j, Sum m i j ∧ o = S j :=
  (sum_cases m (S i) o h).elim (fun a => ((hI i i hi hi).1 a.1.symm).elim)
    fun h => h.elim fun k h => h.elim fun j h =>
      ⟨j, ((hI i k hi h.1).2 h.2.2.2.1).symm ▸ h.2.2.1, h.2.2.2.2⟩

theorem sum_functional (hI : IStar σ) (m n : ν) (hn : N n) :
    ∀ j k, Sum m n j → Sum m n k → j = k :=
  (hn (fun i => N i ∧ ∀ j k, Sum m i j → Sum m i k → j = k)
    ⟨⟨arith_N_zero, fun j k hj hk => (sum_at_zero hI m j hj).trans (sum_at_zero hI m k hk).symm⟩,
      fun i ih => ⟨arith_N_suc i ih.1, fun j k hj hk =>
        (sum_at_succ hI m i j ih.1 hj).elim fun a ha =>
        (sum_at_succ hI m i k ih.1 hk).elim fun b hb =>
          ha.2.trans ((congrArg S (ih.2 a b ha.1 hb.1)).trans hb.2.symm)⟩⟩).2

def prodCases (m n o : ν) :=
  (n = Z ∧ o = Z) ∨ ∃ i j, N i ∧ N j ∧ Prod m i j ∧ n = S i ∧ Sum m j o

theorem prod_cases (m n o : ν) (h : Prod m n o) : prodCases m n o :=
  (h (fun i j => Prod m i j ∧ prodCases m i j)
    ⟨arith_Prod_zero m, Or.inl ⟨rfl, rfl⟩⟩ fun i j k hi hj hk a b =>
      ⟨arith_Prod_step m i j k hi hj hk a.1 b, Or.inr ⟨i, j, hi, hj, a.1, rfl, b⟩⟩).2

theorem prod_at_zero (hI : IStar σ) (m o : ν) (h : Prod m Z o) : o = Z :=
  (prod_cases m Z o h).elim And.right fun h => h.elim fun i h => h.elim fun _j h =>
    ((hI i i h.1 h.1).1 h.2.2.2.1).elim

theorem prod_at_succ (hI : IStar σ) (m i o : ν) (hi : N i) (h : Prod m (S i) o) :
    ∃ j, N j ∧ Prod m i j ∧ Sum m j o :=
  (prod_cases m (S i) o h).elim (fun a => ((hI i i hi hi).1 a.1.symm).elim)
    fun h => h.elim fun k h => h.elim fun j h =>
      ⟨j, h.2.1, ((hI i k hi h.1).2 h.2.2.2.1).symm ▸ h.2.2.1, h.2.2.2.2⟩

theorem prod_functional (hI : IStar σ) (m n : ν) (hn : N n) :
    ∀ j k, Prod m n j → Prod m n k → j = k :=
  (hn (fun i => N i ∧ ∀ j k, Prod m i j → Prod m i k → j = k)
    ⟨⟨arith_N_zero, fun j k hj hk => (prod_at_zero hI m j hj).trans (prod_at_zero hI m k hk).symm⟩,
      fun i ih => ⟨arith_N_suc i ih.1, fun j k hj hk =>
        (prod_at_succ hI m i j ih.1 hj).elim fun a ha =>
        (prod_at_succ hI m i k ih.1 hk).elim fun b hb =>
          sum_functional hI m a ha.1 j k ha.2.2
            ((ih.2 a b ha.2.1 hb.2.1).symm ▸ hb.2.2)⟩⟩).2

theorem guard_box (G p : Prop) (hp : □ p) : □ (G → p) :=
  modal_K _ _ (nec% (fun (h : p) (_ : G) => h)) hp

theorem guarded_zero_ne_succ (G : Prop) (hI : □ (G → IStar σ)) (k : ν) (hk : N k) :
    □ (G → Z ≠ S k) :=
  modal_K _ _ (modal_K _ _
    (nec% (fun (f : G → IStar σ) (n : N k) (g : G) => ((f g) k k n n).1))
    hI) (arith_N_box k hk)

theorem guarded_succ_inj (G : Prop) (hI : □ (G → IStar σ)) (i k : ν) (hi : N i) (hk : N k) :
    □ (G → S i = S k → i = k) :=
  modal_K _ _ (modal_K _ _ (modal_K _ _
    (nec% (fun (f : G → IStar σ) (a : N i) (b : N k) (g : G) => ((f g) i k a b).2))
    hI) (arith_N_box i hi)) (arith_N_box k hk)

theorem guarded_distinct (G : Prop) (hI : □ (G → IStar σ)) (m : ν) (hm : N m) :
    ∀ n, N n → m ≠ n → □ (G → m ≠ n) :=
  (hm (fun i => N i ∧ ∀ n, N n → i ≠ n → □ (G → i ≠ n))
    ⟨⟨arith_N_zero, fun n hn ne =>
      (finiteCardinality_zero_or_suc n hn).elim (fun e => (ne e.symm).elim)
        fun ex => ex.elim fun k hk => hk.2 ▸ guarded_zero_ne_succ G hI k hk.1⟩,
     fun i hi => ⟨arith_N_suc i hi.1, fun n hn ne =>
       (finiteCardinality_zero_or_suc n hn).elim
         (fun e => e ▸ modal_K _ _
           (nec% (fun (f : G → Z ≠ S i) (g : G) (e : S i = Z) => f g e.symm))
           (guarded_zero_ne_succ G hI i hi.1))
         fun ex => ex.elim fun k hk => hk.2 ▸ modal_K _ _ (modal_K _ _
           (nec% (fun (f : G → i ≠ k) (h : G → S i = S k → i = k) (g : G)
             (e : S i = S k) => f g (h g e)))
           (hi.2 k hk.1 fun e => ne (hk.2 ▸ congrArg S e))) (guarded_succ_inj G hI i k hi.1 hk.1)⟩⟩).2

theorem graph_agreement (G : Prop) (R : ν → Prop) (o : ν) (ho : N o)
    (hI : □ (G → IStar σ)) (ht : ∃ j, N j ∧ R j) (hp : ∀ j, R j → □ (R j))
    (hu : □ (G → ∀ j k, R j → R k → j = k)) :
    (□ (G → R o)) ∨ (□ (G → ¬ R o)) :=
  (em (R o)).elim (fun h => Or.inl (guard_box G _ (hp o h))) fun no =>
    ht.elim fun j hj => Or.inr (modal_K _ _ (modal_K _ _ (modal_K _ _
      (nec% (fun (u : G → ∀ j k, R j → R k → j = k) (r : R j) (d : G → j ≠ o)
        (g : G) (z : R o) => d g (u g j o r z))) hu) (hp j hj.2))
      (guarded_distinct G hI j hj.1 o ho (fun e => no (e ▸ hj.2))))

theorem number_agreement (G : Prop) (N' : ν → Prop) (n : ν)
    (he : N' = N) (hn : N' n) : (□ (G → N' n)) ∨ (□ (G → ¬ N' n)) :=
  he ▸ Or.inl (guard_box G _ (arith_N_box n (he ▸ hn)))

theorem equality_agreement (G : Prop) (m n : ν) (hI : □ (G → IStar σ)) (hm : N m) (hn : N n) :
    (□ (G → m = n)) ∨ (□ (G → m ≠ n)) :=
  (em (m = n)).elim (fun e => Or.inl (guard_box G _ (necessity_of_identity m n e)))
    (fun ne => Or.inr (guarded_distinct G hI m hm n hn ne))

theorem sum_agreement (G : Prop) (m n o : ν) (hI : □ (G → IStar σ)) (hm : N m) (hn : N n)
    (ho : N o) : (□ (G → Sum m n o)) ∨ (□ (G → ¬ Sum m n o)) :=
  graph_agreement G (Sum m n) o ho hI (sum_total m n hm hn) (arith_Sum_box m n)
    (modal_K _ _ (modal_K _ _
      (nec% (fun (f : G → IStar σ) (a : N n) (g : G) => sum_functional (f g) m n a))
      hI) (arith_N_box n hn))

theorem prod_agreement (G : Prop) (m n o : ν) (hI : □ (G → IStar σ)) (hm : N m) (hn : N n)
    (ho : N o) : (□ (G → Prod m n o)) ∨ (□ (G → ¬ Prod m n o)) :=
  graph_agreement G (Prod m n) o ho hI (prod_total m n hm hn) (arith_Prod_box m n)
    (modal_K _ _ (modal_K _ _
      (nec% (fun (f : G → IStar σ) (a : N n) (g : G) => prod_functional (f g) m n a))
      hI) (arith_N_box n hn))

/- The vocabulary arguments make the certified rules usable directly on the deep
   translation, where applications of closed vocabulary terms are left unreduced. -/
theorem persistence_rel (N' : ν → Prop) (hN : N' = N) : ∀ n, N' n → □ (N' n) :=
  hN ▸ (arith_N_box (σ := σ))

theorem equality_rel (G I : Prop) (N' : ν → Prop) (m n : ν) (eI : I = IStar σ)
    (eN : N' = N) (hI : □ (G → I)) (hm : N' m) (hn : N' n) :
    (□ (G → m = n)) ∨ (□ (G → m ≠ n)) :=
  equality_agreement G m n (eI ▸ hI) (eN ▸ hm) (eN ▸ hn)

theorem sum_rel (G I : Prop) (N' : ν → Prop) (R : ν → ν → ν → Prop)
    (m n o : ν) (eI : I = IStar σ) (eN : N' = N) (eR : R = Sum)
    (hI : □ (G → I)) (hm : N' m) (hn : N' n) (ho : N' o) :
    (□ (G → R m n o)) ∨ (□ (G → ¬ R m n o)) :=
  eR ▸ sum_agreement G m n o (eI ▸ hI) (eN ▸ hm) (eN ▸ hn) (eN ▸ ho)

theorem prod_rel (G I : Prop) (N' : ν → Prop) (R : ν → ν → ν → Prop)
    (m n o : ν) (eI : I = IStar σ) (eN : N' = N) (eR : R = Prod)
    (hI : □ (G → I)) (hm : N' m) (hn : N' n) (ho : N' o) :
    (□ (G → R m n o)) ∨ (□ (G → ¬ R m n o)) :=
  eR ▸ prod_agreement G m n o (eI ▸ hI) (eN ▸ hm) (eN ▸ hn) (eN ▸ ho)

end Classicism.GuardedArithmetic

#classicism_derive Classicism.GuardedArithmetic.persistence_rel Classicism.GuardedArithmetic.number_agreement
  Classicism.GuardedArithmetic.equality_rel Classicism.GuardedArithmetic.sum_rel Classicism.GuardedArithmetic.prod_rel
