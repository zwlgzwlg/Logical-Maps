import Classicism.Coalesced.StoneOrder
import Classicism.Semantics.FullModels

/-! Rigidity of unary families, including families of ordinal candidates. -/

namespace Classicism.Meta.Coalesced.StoneFan

open CategoryTheory CategoryTheory.Sigma Classicism.Meta.Intensional

private abbrev Unary (σ : Ty) : RTy := .arr σ .t

namespace UnaryRigid

variable {Sig : Signature} {σ : Ty}

/-- The native unary comparison, written using the same relational primitives as
the map's generic rigidity definitions. -/
def incl {Γ : Ctx} (a b : Term Sig Γ (Unary σ)) : Formula Sig Γ :=
  .app (.app (.inclR (Unary σ)) a) b

def test {Γ : Ctx} (a b : Term Sig Γ (Unary σ)) : Formula Sig Γ :=
  incl a (.app (.boxR (Unary σ)) b)

def persistent : Formula Sig [.rel (Unary σ)] :=
  Term.box (test (.var .zero) (.var .zero))

def inextensible : Formula Sig [.rel (Unary σ)] :=
  Term.box (Term.forall' (Term.imp (test (.var (.succ .zero)) (.var .zero))
    (Term.box (incl (.var (.succ .zero)) (.var .zero)))))

def rigid : Formula Sig [.rel (Unary σ)] := Term.conj persistent inextensible

variable {K : Type} [SmallCategory K] (B : Premodel Sig K) (M : B.IsModel)
  {Γ : Ctx} {W : K} (h : B.W₀ ⟶ W) (g : IEnv (B.Dom W) Γ)

abbrev atArrow (Y : B.Dom W (Unary σ)) {U : K} (j : W ⟶ U) (b : B.Dom U σ) :=
  (⟨U, (b, PUnit.unit), j⟩ : Tuple B.inner (Unary σ) W) ∈ B.incl _ W Y

include M

theorem holds_test (s t : Term Sig Γ (Unary σ)) (Y Z : B.Dom W (Unary σ))
    (hs : B.sem h s g = B.incl _ W Y) (ht : B.sem h t g = B.incl _ W Z) :
    B.Holds h (test s t) g ↔
      ∀ b, atArrow B Y (𝟙 W) b → ∀ (U : K) (j : W ⟶ U),
        atArrow B Z j ((B.inner σ).map j b) := by
  simp only [test, incl, Premodel.holds_inclR M, Premodel.sem_boxR M, hs, ht,
    Set.mem_ofPred_eq, Category.id_comp]
  constructor
  · intro H b hb
    exact H (b, PUnit.unit) hb
  · rintro H ⟨b, ⟨⟩⟩
    exact H b

theorem holds_le (s t : Term Sig Γ (Unary σ)) (Y Z : B.Dom W (Unary σ))
    (hs : B.sem h s g = B.incl _ W Y) (ht : B.sem h t g = B.incl _ W Z) :
    B.Holds h (Term.box (incl s t)) g ↔ B.incl _ W Y ⊆ B.incl _ W Z := by
  simp only [incl, B.holds_box M, Premodel.holds_inclR M, B.sem_push, hs, ht,
    Outer.map_rel, Intension.mem_map, Category.comp_id]
  constructor
  · rintro H ⟨U, a, j⟩ hp
    exact H j a hp
  · intro H U j a ha
    exact H ha

theorem weak_clauses (Y : B.Dom W (Unary σ))
    (hy : B.Holds h rigid (.cons Y .nil)) :
    (∀ b, atArrow B Y (𝟙 W) b → ∀ (U : K) (j : W ⟶ U), atArrow B Y j ((B.inner σ).map j b)) ∧
      ∀ Z : B.Dom W (Unary σ),
        (∀ b, atArrow B Y (𝟙 W) b → ∀ (U : K) (j : W ⟶ U), atArrow B Z j ((B.inner σ).map j b)) →
        B.incl _ W Y ⊆ B.incl _ W Z := by
  obtain ⟨p,i⟩ := (B.holds_conj M _ _ _ _).1 hy
  have drop {Γ' : Ctx} (q : Formula Sig Γ') (g' : IEnv (B.Dom W) Γ') (hbox : B.Holds h (Term.box q) g') :
      B.Holds h q g' := by
    simpa only [Category.comp_id, B.push_id] using ((B.holds_box M _ _ _).1 hbox (𝟙 W))
  have wp := drop _ _ p
  have wi := drop _ _ i
  refine ⟨(holds_test B M h _ _ _ Y Y rfl rfl).1 wp, ?_⟩
  intro Z hz
  have hi := (B.holds_forall M _ _ _).1 wi Z
  apply (holds_le B M h (.cons Z (.cons Y .nil)) (.var (.succ .zero)) (.var .zero) Y Z rfl rfl).1
  apply (B.holds_imp M _ _ _ _).1 hi
  exact (holds_test B M h (.cons Z (.cons Y .nil)) (.var (.succ .zero)) (.var .zero) Y Z rfl rfl).2 hz

end UnaryRigid

variable {Sig : Signature} {ι : Type} {C : ι → Type} [∀ k, SmallCategory (C k)]
  (A : ∀ k, Premodel Sig (C k)) (L : ι → Type) (leaf : ι) [TopologicalSpace (L leaf)]
  {σ : Ty}

local notation "S" => arrows A L
local notation "R" => action A L leaf
local notation "P" => model A L leaf

/-- All native transports along a tagged arrow are determined by the value at its base. -/
theorem tr_factor (b : (R).D σ) {k : ι} {U : C k}
    (x : L k) (j : (A k).W₀ ⟶ U) :
    (R).tr σ (k := k) (V := U) (x,j) b =
      ((A k).inner σ).map j ((R).tr σ (baseArrow A L k x) b) := by
  have h := (R).tr_map σ j (baseArrow A L k x) b
  change (R).tr σ (k := k) (V := U) (x, 𝟙 _ ≫ j) b = _ at h
  rwa [Category.id_comp] at h

theorem at_component (Y : (R).D (.rel (Unary σ))) {k : ι} {U : C k}
    (x : L k) (j : (A k).W₀ ⟶ U) (b : (A k).Dom U σ) :
    UnaryRigid.atArrow (W := CoalescedSum.base S) P Y
      (CoalescedSum.arr S (x := ⟨k,U⟩) (x,j)) b ↔
      UnaryRigid.atArrow (A k) (profile A L leaf Y k x) j b := by
  have h := congrArg (fun X : Set (RootTuple S A (Unary σ) (args A L leaf (Unary σ))) =>
    Sum.inr ⟨k,U,(b,PUnit.unit),x,j⟩ ∈ X) (congrArg Subtype.val (glue_profile A L leaf Y))
  exact Iff.of_eq h.symm

private noncomputable def chosenLabel (z : L leaf) (k : ι) (x : L k) : L k := by
  classical
  exact if h : k = leaf then h.symm ▸ z else x

omit [TopologicalSpace (L leaf)] in
private theorem chosen_leaf (z x : L leaf) : chosenLabel L leaf z leaf x = z := by
  classical
  simp [chosenLabel]

/-- A rigid native unary family whose actual members each have a constant
distinguished profile has *one and the same full predicate intension* at every
distinguished leaf. This applies to the uniformity step for ordinal limits. -/
theorem rigid_uniform_family (M : ∀ k, (A k).IsModel) (Y : (R).D (.rel (Unary σ)))
    (hy : (P).Holds (𝟙 (CoalescedSum.base S)) UnaryRigid.rigid (.cons Y .nil))
    (hu : ∀ b : (R).D σ,
      UnaryRigid.atArrow (W := CoalescedSum.base S) P Y (𝟙 _) b →
      ∀ x z : L leaf, (R).tr σ (baseArrow A L leaf x) b = (R).tr σ (baseArrow A L leaf z) b) :
    ∀ x z : L leaf, profile A L leaf Y leaf x = profile A L leaf Y leaf z := by
  have ⟨hp, hi⟩ := UnaryRigid.weak_clauses P (isModel A L leaf M) (𝟙 (CoalescedSum.base S)) Y hy
  have compare (x z : L leaf) :
      (A leaf).incl _ _ (profile A L leaf Y leaf x) ⊆ (A leaf).incl _ _ (profile A L leaf Y leaf z) := by
    let y := fun k (l : L k) => profile A L leaf Y k (chosenLabel L leaf z k l)
    have hloc : IsLocallyConstant (y leaf) := by
      apply IsLocallyConstant.of_constant
      intro a b
      simp [y, chosen_leaf]
    let Q := glue A L leaf (row A L leaf Y) y hloc
    have eq_tr (b : (R).D σ) (hb : UnaryRigid.atArrow (W := CoalescedSum.base S) P Y (𝟙 _) b)
        (k : ι) (l : L k) :
        (R).tr σ (baseArrow A L k (chosenLabel L leaf z k l)) b = (R).tr σ (baseArrow A L k l) b := by
      classical
      by_cases e : k = leaf
      · subst k
        exact hu b hb _ _
      · simp [chosenLabel, e]
    have below := hi Q (by
      intro b hb U j
      cases U with
      | root =>
        cases j
        change UnaryRigid.atArrow (W := CoalescedSum.base S) (σ := σ) P Q (𝟙 (CoalescedSum.base S)) (((P).inner σ).map (𝟙 _) b)
        rw [Functor.map_id_apply]
        exact hb
      | of kv =>
        obtain ⟨k,U⟩ := kv
        change L k × ((A k).W₀ ⟶ U) at j
        obtain ⟨l,j⟩ := j
        have hz := hp b hb (.of ⟨k,U⟩)
          (CoalescedSum.arr S (x := ⟨k,U⟩) (chosenLabel L leaf z k l, j))
        have hz' := (at_component A L leaf Y (chosenLabel L leaf z k l) j _).1 hz
        apply (at_component A L leaf Q l j _).2
        change UnaryRigid.atArrow (A k) (profile A L leaf Q k l) j
          ((R).tr σ (k := k) (V := U) (l,j) b)
        change UnaryRigid.atArrow (A k) (profile A L leaf Y k (chosenLabel L leaf z k l)) j
          ((R).tr σ (k := k) (V := U) (chosenLabel L leaf z k l,j) b) at hz'
        have eqval := (tr_factor A L leaf b (chosenLabel L leaf z k l) j).trans
          ((congrArg (fun v => ((A k).inner σ).map j v) (eq_tr b hb k l)).trans
            (tr_factor A L leaf b l j).symm)
        have e : profile A L leaf Q k l = y k l := tr_glue A L leaf _ _ _ k l
        exact (congrArg₂ (fun Z v => UnaryRigid.atArrow (A k) Z j v) e.symm eqval).mp hz')
    have H := ((incl_iff_coordinates A L leaf Y Q).1 below).2 leaf x
    have e : profile A L leaf Q leaf x = profile A L leaf Y leaf z :=
      (tr_glue A L leaf _ _ _ leaf x).trans (congrArg (profile A L leaf Y leaf) (chosen_leaf L leaf z x))
    rwa [e] at H
  intro x z
  exact (A leaf).incl_injective _ _ (Set.Subset.antisymm (compare x z) (compare z x))

/-- In particular any relational term taking the rigid family as its sole free
parameter has uniform transported denotation, including a term defining an ordinal
limit. The family parameter may vary throughout the old component. -/
theorem rigid_uniform_term (M : ∀ k, (A k).IsModel) (Y : (R).D (.rel (Unary σ)))
    (hy : (P).Holds (𝟙 (CoalescedSum.base S)) UnaryRigid.rigid (.cons Y .nil))
    (hu : ∀ b : (R).D σ, UnaryRigid.atArrow (W := CoalescedSum.base S) P Y (𝟙 _) b →
      ∀ x z : L leaf, (R).tr σ (baseArrow A L leaf x) b = (R).tr σ (baseArrow A L leaf z) b)
    {ρ : RTy} (t : Term Sig [.rel (Unary σ)] (.rel ρ)) (x z : L leaf) :
    (R).transport (baseArrow A L leaf x) ((P).sem (𝟙 (CoalescedSum.base S)) t (.cons Y .nil)) =
      (R).transport (baseArrow A L leaf z) ((P).sem (𝟙 (CoalescedSum.base S)) t (.cons Y .nil)) := by
  have readAt (l : L leaf) :
      (R).transport (baseArrow A L leaf l) ((P).sem (𝟙 (CoalescedSum.base S)) t (.cons Y .nil)) =
        (A leaf).sem (𝟙 _) t (.cons (profile A L leaf Y leaf l) .nil) :=
    (StoneLeaves.transport_sem (baseArrow A L leaf) (fun _ _ => rfl) _ _ _ _
      PUnit.unit t (.cons Y .nil) l).trans ((A leaf).rebase_sem_congr
        (funext fun c => tr_lift A L leaf _ (fun k => (A k).I c) leaf l) (𝟙 _) t _)
  exact (readAt x).trans ((congrArg (fun a => (A leaf).sem (𝟙 _) t (.cons a .nil))
    (rigid_uniform_family A L leaf M Y hy hu x z)).trans (readAt z).symm)

#print axioms rigid_uniform_family
#print axioms rigid_uniform_term

end Classicism.Meta.Coalesced.StoneFan
