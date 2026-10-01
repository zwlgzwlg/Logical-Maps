import Classicism.Tools.Schema
import Classicism.Certified.Schemas
import Classicism.Certified.Entailed
import Classicism.Results.Atomicity
import Classicism.Principles
import Classicism.Pointwise
import Classicism.Paper

-- goals and hover print `fun y ↦ …`, matching the source
set_option pp.unicode.fun true

/-!
# Results at every arity

The map states comprehension, Boolean Completeness, Atomicity and their kin for relations
of every arity, `∀^Ty σ̄`, and several of the paper's proofs reason about an argument tuple
`x̄`: "BF, one argument at a time", "the persistent coextension `λȳ. w ≤ X[ȳ]`". Two kinds
of shallow proof reach every arity:

- **pointwise reasoning at a relational type**: a theorem at a Rel-parameter `τ`, its
  pointwise steps through the laws of `Pointwise`, which the translator derives for every
  object type by induction on the type. It is at every arity already;
- **a unary proof**, at `σ → t`, for a result that uses BF over the tuple: vectorized in
  `σ` (its list rule), it holds at `σs ⇒* t` for every list, which is every relational
  type (`schema_subset_args`). BF at `σ` in such a proof becomes BF over the list, which
  BF gives (`P.Barcan.schema_entails_listSchema`); in `C5`, `□`BF at `σ` comes from `□ND`
  at `t` inside the proof, and the vectorized result has no list premise at all.

The file has three parts, as `Results/Atomicity.lean` does:

1. **The shallow layer**: the shallow cores at `τ`, the unary ones at `σ → t`, and the
   boxed step of Atomicity.
2. **Certification.** The certification command makes each a rule between schema
   instances, and, with a Ty-parameter, a list rule; the entailment command an entailment
   between schemas, and a list entailment.
3. **The metalogic**: the compositions of certified entailments, among them the ones in
   `Certified/Entailed.lean`, into the map's arrows. Each theorem here named by a map id
   is that record, for every arity.
-/

namespace Classicism
open Paper

/-! ## 1. The shallow layer -/

section shallowCores
variable {τ : Type} [Rel τ] [Pointwise τ]

/-- `w` an actual world gives `q ↔ □(¬w ∨ q)` for every `q`. -/
theorem actual_iff (w : Prop) (hw : ActualWorld w) : ∀ q : Prop, q ↔ □ (¬ w ∨ q) := fun q =>
  ⟨fun hq => modal_K _ _ (nec% (not_or_of_imp w q)) ((le_iff_prop w q).1 (hw.2 q hq)),
   fun h => Or.elim (box_elim h) (fun hn => absurd hw.1 hn) (fun hq => hq)⟩

/-- With `w` the actual world, `λx̄. □(¬w ∨ X[x̄])`, that is `λx̄. w ≤ X[x̄]`, is a persistent
coextension of `X` (Classicism, n. 38). -/
theorem persistent_coext_of_actual (X : τ) (w : Prop) (hw : ActualWorld w) :
    Persistent (boxAt (Rel.or (Rel.neg (constP w)) X)) ∧
      X ≡ boxAt (Rel.or (Rel.neg (constP w)) X) :=
  ⟨nec% (boxAt_four (Rel.or (Rel.neg (constP w)) X)), coext_boxAt_actual X w (actual_iff w hw)⟩

/-- `actuality-implies-persistent-comprehension-r`, at every relational type. -/
theorem actuality_implies_persistent_comprehension_r :
    P.Actuality → P.PersistentComprehension τ := fun act X =>
  act.elim fun w (hw : ActualWorld w) => ⟨_, persistent_coext_of_actual X w hw⟩

/-- `very-weak-rigid-comprehension-r-implies-weak-rigid-comprehension-r`, at every
arity: for `Y` very weakly rigid, `λz̄. □Y[z̄]` is a weakly rigid coextension. -/
theorem very_weak_rigid_comprehension_r_implies_weak_rigid_comprehension_r :
    P.VeryWeakRigidComprehension τ → P.WeakRigidComprehension τ := fun vw X =>
  (vw X).elim fun Y hY =>
    ⟨boxAt Y,
      ⟨nec% (boxAt_four Y), fun Z hZ =>
        modal_K _ _ (nec% (boxImp_trans (boxAt Y) Y Z (boxAt_T Y)))
          (hY.1.2 Z (boxImp_trans Y (boxAt Y) (boxAt Z) hY.1.1 hZ))⟩,
      coext_of_boxImp X (boxAt Y)
        (boxImp_trans X Y (boxAt Y) (boxImp_of_coext X Y hY.2) hY.1.1)
        (boxImp_trans (boxAt Y) Y X (boxAt_T Y) (boxImp_of_coext' X Y hY.2))⟩

/-- If every truth is necessary, every relation is weakly inextensible. -/
theorem weaklyInextensible_of_all (X : τ) : (∀ p : Prop, p → □ p) → WeaklyInextensible X :=
  fun h Z hZ => h _ (boxImp_trans X (boxAt Z) Z hZ (boxAt_T Z))

/-- `extensionality-r-implies-rigid-comprehension-r`, at every arity: under the Fregean
Axiom (the nullary instance) every truth is necessary, and necessarily so; so every
relation is persistent and inextensible, and is its own rigid coextension. -/
theorem extensionality_r_implies_rigid_comprehension_r :
    P.Extensionality Prop → P.RigidComprehension τ := fun extP X =>
  have fa := Proofs.extensionality_r_implies_fregean_axiom extP
  have hall : □ (∀ p : Prop, p → □ p) := Proofs.box_of_fregean fa _ (Proofs.box_of_fregean fa)
  ⟨X, ⟨modal_K _ _ (nec% (boxImp_boxAt_of_all X)) hall,
      modal_K _ _ (nec% (weaklyInextensible_of_all X)) hall⟩, Rel.coext_refl X⟩

/-- In `C5` the negation of a persistent relation is persistent: where `Y` fails, `B` and
the persistence of `Y` make it fail necessarily, at every world. -/
theorem persistent_neg_of_c5 (Y : τ) :
    P.NecNecessityOfDistinctness Prop → Persistent Y → Persistent (Rel.neg Y) := fun hnd hP =>
  modal_K _ _ (modal_K _ _ (nec% (neg_boxImp_boxAt_of_b Y)) (Proofs.box_b_of_box_nd_t hnd))
    (modal_K _ _ (nec% (top_boxAt_of_box Y (boxAt Y))) (modal_four _ hP))

/-- `c5-and-persistent-comprehension-imply-gallin`, at every arity. -/
theorem c5_and_persistent_comprehension_imply_gallin :
    P.NecNecessityOfDistinctness Prop → P.PersistentComprehension τ →
      P.GallinExtensionalComprehension τ := fun hnd pc X =>
  (pc X).elim fun Y hY => ⟨Y, hY.1, persistent_neg_of_c5 Y hnd hY.1, hY.2⟩

/-- Rigid Comprehension gives Gallin's, in `C5`. -/
theorem c5_rigid_gallin :
    P.NecNecessityOfDistinctness Prop → P.RigidComprehension τ →
      P.GallinExtensionalComprehension τ := fun hnd rc =>
  c5_and_persistent_comprehension_imply_gallin hnd fun X => (rc X).elim fun Y hY => ⟨Y, hY.1.1, hY.2⟩

/-- `c5-and-necessary-rigid-comprehension-imply-necessary-gallin-comprehension`, at every
arity: the last lemma necessitated, `□ND` boxed by `4`. -/
theorem c5_and_necessary_rigid_comprehension_imply_necessary_gallin_comprehension :
    P.NecNecessityOfDistinctness Prop → P.NecRigidComprehension τ →
      P.NecGallinExtensionalComprehension τ := fun hnd hrc =>
  modal_K _ _ (modal_K _ _ (nec% (c5_rigid_gallin (τ := τ))) (modal_four _ hnd)) hrc

end shallowCores

section unary
variable {σ : Type} [Ty σ]

/-- With BF at `σ`, a property whose negation is weakly persistent is weakly inextensible:
where `Y` fails it fails necessarily, so `Y ⊆ □Z` gives `□(Y z → Z z)` at each `z`, and BF
boxes the quantifier. -/
theorem weaklyInextensible_of_neg_bf (Y : σ → Prop) :
    P.Barcan σ → WeaklyPersistent (¬ Y) → WeaklyInextensible Y := fun bf hn Z hZ =>
  bf (λ z ↦ Y z → Z z) fun z =>
    (em (Y z)).elim (fun hy => Proofs.box_imp_of_box (Y z) (Z z) (hZ z hy))
      (fun hny => Proofs.box_imp_of_box_not (Y z) (Z z) (hn z hny))

/-- Gallin Extensional Comprehension and BF give Weak Rigid Comprehension, at `σ → t`:
the Gallin-rigid coextension is persistent and, its negation being persistent, weakly
inextensible. -/
theorem gallin_bf_weak_rigid_comprehension :
    P.GallinExtensionalComprehension (σ → Prop) → P.Barcan σ →
      P.WeakRigidComprehension (σ → Prop) :=
  fun g bf X => (g X).elim fun Y hY =>
    ⟨Y, ⟨hY.1, weaklyInextensible_of_neg_bf Y bf (box_elim hY.2.1)⟩, hY.2.2⟩

/-- And in `C5`, Rigid Comprehension: the argument above under the box, with `□`BF at `σ`
from `□ND` at `t` (Proposition 2.3), the persistence of the negation being boxed
already. -/
theorem gallin_c5_rigid_comprehension :
    P.GallinExtensionalComprehension (σ → Prop) → P.NecNecessityOfDistinctness Prop →
      P.RigidComprehension (σ → Prop) :=
  fun g hnd X => (g X).elim fun Y hY =>
    ⟨Y, ⟨hY.1, modal_K _ _ (modal_K _ _ (nec% (weaklyInextensible_of_neg_bf Y))
      (Proofs.necessary_distinctness_necessary_r_implies_necessary_barcan_r hnd)) hY.2.1⟩,
     hY.2.2⟩

/-- Boxed Gallin Extensional Comprehension gives `□`Rigid Comprehension in `C5`, at
`σ → t`: the last lemma necessitated, `□ND` boxed by `4`. -/
theorem nec_gallin_c5_nec_rigid_comprehension :
    P.NecGallinExtensionalComprehension (σ → Prop) → P.NecNecessityOfDistinctness Prop →
      P.NecRigidComprehension (σ → Prop) := fun hg hnd =>
  modal_K _ _ (modal_K _ _ (nec% (gallin_c5_rigid_comprehension (σ := σ))) hg)
    (modal_four _ hnd)

end unary

/-- In `C5`, `□`Boolean Completeness gives `□`Plenitude, for relations `σ → (σ' → t) → t`:
Proposition 2.14 necessitated, `□ND` boxed by `4`. -/
theorem necessary_completeness_c5_necessary_plenitude {σ' σ : Type} [Ty σ'] [Ty σ] :
    P.NecBooleanCompleteness (σ → σ' → Prop) → P.NecNecessityOfDistinctness Prop →
      P.NecPlenitude σ (σ' → Prop) := fun hbc hnd =>
  modal_K _ _ (modal_K _ _ (nec% (Proofs.c5_and_completeness_imply_plenitude (σ' := σ') (σ := σ)))
    hbc) (modal_four _ hnd)

section atomicity
variable {σ τ : Type} [Ty σ] [Rel τ] [Order τ] [Pointwise τ]

/-- The boxed step of Atomicity: `□`Atomicity at `τ` and `□`BF at `σ` give `□`Atomicity at
`σ → τ`, the step of `Results/Atomicity.lean` necessitated. -/
theorem necAtomicity_step : P.NecAtomicity τ → P.NecBarcan σ → P.NecAtomicity (σ → τ) :=
  fun h₁ h₂ => modal_K _ _ (modal_K _ _ (nec% (atomicity_step (σ := σ) (τ := τ))) h₁) h₂

end atomicity

/-- In `C5`, `□`Actuality gives `□`Atomicity at `t`: Proposition 2.6 at `t`, necessitated. -/
theorem c5_necessary_atomicity_t :
    P.NecActuality → P.NecNecessityOfDistinctness Prop → P.NecAtomicity Prop := fun hna hnd =>
  modal_K _ _ (modal_K _ _ (nec% Proofs.c5_and_necessary_actuality_imply_atomicity_at_t)
    (modal_four _ hna)) (modal_four _ hnd)

/-- Under the Fregean Axiom a truth is necessary, Actuality among them. -/
theorem fregean_actuality_necessary_actuality : P.FregeanAxiom → P.Actuality → P.NecActuality :=
  fun fa act => fa _ True ⟨fun _ => trivial, fun _ => act⟩

/-! ## 2. Certification -/

#classicism_certify Classicism.actuality_implies_persistent_comprehension_r
  Classicism.gallin_bf_weak_rigid_comprehension Classicism.gallin_c5_rigid_comprehension
  Classicism.nec_gallin_c5_nec_rigid_comprehension
  Classicism.necAtomicity_step Classicism.c5_necessary_atomicity_t
  Classicism.fregean_actuality_necessary_actuality
  Classicism.very_weak_rigid_comprehension_r_implies_weak_rigid_comprehension_r
  Classicism.extensionality_r_implies_rigid_comprehension_r
  Classicism.c5_and_persistent_comprehension_imply_gallin
  Classicism.c5_and_necessary_rigid_comprehension_imply_necessary_gallin_comprehension
  Classicism.necessary_completeness_c5_necessary_plenitude

#classicism_entails Classicism.actuality_implies_persistent_comprehension_r
  Classicism.gallin_bf_weak_rigid_comprehension Classicism.gallin_c5_rigid_comprehension
  Classicism.nec_gallin_c5_nec_rigid_comprehension
  Classicism.c5_necessary_atomicity_t Classicism.fregean_actuality_necessary_actuality
  Classicism.very_weak_rigid_comprehension_r_implies_weak_rigid_comprehension_r
  Classicism.extensionality_r_implies_rigid_comprehension_r
  Classicism.c5_and_persistent_comprehension_imply_gallin
  Classicism.c5_and_necessary_rigid_comprehension_imply_necessary_gallin_comprehension
  Classicism.necessary_completeness_c5_necessary_plenitude

/-! ## 3. The metalogic -/

namespace Meta
open AxiomSet

/-- `actuality-implies-persistent-comprehension-r`, the map's record, at every arity. -/
theorem actuality_implies_persistent_comprehension_r :
    P.Actuality.schema ⟹ P.PersistentComprehension.schema :=
  Classicism.actuality_implies_persistent_comprehension_r.entails

/-- `c5-and-actuality-imply-rigid-comprehension` (Proposition 2.10), at every arity: the
record at `σ → t`, vectorized. -/
theorem c5_and_actuality_imply_rigid_comprehension :
    P.NecNecessityOfDistinctness.schema ∪ P.Actuality.schema ⟹ P.RigidComprehension.schema :=
  Entails.mono_right (schema_subset_args _)
    (Entails.trans (Entails.union (Entails.union_right _ _) (Entails.union_left _ _))
      Proofs.c5_and_actuality_imply_rigid_comprehension.listEntails)

/-- `gallin-comprehension-and-bf-imply-weak-rigid-comprehension`, at every arity: the core
at `σ → t`, vectorized, with BF over every list from BF. -/
theorem gallin_comprehension_and_bf_imply_weak_rigid_comprehension :
    P.GallinExtensionalComprehension.schema ∪ P.Barcan.schema ⟹
      P.WeakRigidComprehension.schema :=
  Entails.mono_right (schema_subset_args _)
    (Entails.trans
      (Entails.union (Entails.union_left _ _)
        (Entails.trans (Entails.union_right _ _) P.Barcan.schema_entails_listSchema))
      gallin_bf_weak_rigid_comprehension.listEntails)

/-- `gallin-comprehension-and-bf-imply-rigid-comprehension`, at every arity: Gallin gives
ND, ND and BF give `□ND`, and the core at `σ → t`, vectorized. -/
theorem gallin_comprehension_and_bf_imply_rigid_comprehension :
    P.GallinExtensionalComprehension.schema ∪ P.Barcan.schema ⟹ P.RigidComprehension.schema :=
  have nd : P.GallinExtensionalComprehension.schema ∪ P.Barcan.schema ⟹
      P.NecessityOfDistinctness.schema :=
    Entails.trans (Entails.union_left _ _) Proofs.gallin_comprehension_implies_nd.entails
  have nnd : P.GallinExtensionalComprehension.schema ∪ P.Barcan.schema ⟹
      P.NecNecessityOfDistinctness.schema :=
    Entails.trans (Entails.union nd (Entails.union_right _ _))
      Proofs.nd_and_bf_imply_necessary_nd.entails
  Entails.mono_right (schema_subset_args _)
    (Entails.trans (Entails.union (Entails.union_left _ _) nnd)
      gallin_c5_rigid_comprehension.listEntails)

/-- `c5-and-atomicity-imply-necessary-rigid-comprehension`, at every arity: the record at
`σ → t`, from Atomicity at `t`, vectorized. -/
theorem c5_and_atomicity_imply_necessary_rigid_comprehension :
    P.NecNecessityOfDistinctness.schema ∪ P.Atomicity.schema ⟹
      P.NecRigidComprehension.schema :=
  Entails.mono_right (schema_subset_args _)
    (Entails.trans (Entails.union (Entails.union_right _ _) (Entails.union_left _ _))
      Proofs.c5_and_atomicity_imply_necessary_rigid_comprehension.listEntails)

/-- `c5-and-necessary-actuality-imply-atomicity` (Proposition 2.6, right to left), at every
arity: Atomicity at `t` from the `t` record, BF from `□ND`, and the induction. -/
theorem c5_and_necessary_actuality_imply_atomicity :
    P.NecNecessityOfDistinctness.schema ∪ P.NecActuality.schema ⟹ P.Atomicity.schema :=
  Entails.trans
    (Entails.union
      (Entails.trans (Entails.union (Entails.union_right _ _) (Entails.union_left _ _))
        Proofs.c5_and_necessary_actuality_imply_atomicity_at_t.entails)
      (Entails.trans (Entails.union_left _ _) Proofs.necessary_nd_implies_bf.entails))
    atomicity_of_atomicity_at_t_barcan

/-- `c5-and-necessary-completeness-imply-atomicity` (Proposition 2.6), at every arity. -/
theorem c5_and_necessary_completeness_imply_atomicity :
    P.NecNecessityOfDistinctness.schema ∪ P.NecBooleanCompleteness.schema ⟹
      P.Atomicity.schema :=
  Entails.trans
    (Entails.union
      (Entails.trans (Entails.union (Entails.union_right _ _) (Entails.union_left _ _))
        Proofs.c5_and_necessary_completeness_imply_atomicity_at_t.entails)
      (Entails.trans (Entails.union_left _ _) Proofs.necessary_nd_implies_bf.entails))
    atomicity_of_atomicity_at_t_barcan

/-- **`□`Atomicity at `t` and `□`BF entail `□`Atomicity**: the boxed step, vectorized, as
for `atomicity_of_atomicity_at_t_barcan`. -/
theorem necAtomicity_of_at_t_necBarcan :
    single (P.NecAtomicity.quoted RTy.t) ∪ P.NecBarcan.schema ⟹ P.NecAtomicity.schema := by
  refine Entails.mono_right (schema_subset_args _) ?_
  rintro a ⟨σs, hσs, rfl⟩
  exact (Theorem.ofC (necAtomicity_step.listRule σs .t trivial)).mp₂ (Theorem.ax (Or.inl rfl))
    (Entails.mono_left (fun _ => Or.inr) P.NecBarcan.schema_entails_listSchema _ ⟨σs, hσs, rfl⟩)

/-- `c5-and-atomicity-imply-necessary-atomicity` (Proposition 2.6 with 2.7), at every
arity: Atomicity and BF give `□`Actuality, which with `□ND` gives `□`Atomicity at `t`,
and `□`BF, from `□ND`, carries it to every type. -/
theorem c5_and_atomicity_imply_necessary_atomicity :
    P.NecNecessityOfDistinctness.schema ∪ P.Atomicity.schema ⟹ P.NecAtomicity.schema :=
  have bf : P.NecNecessityOfDistinctness.schema ∪ P.Atomicity.schema ⟹ P.Barcan.schema :=
    Entails.trans (Entails.union_left _ _) Proofs.necessary_nd_implies_bf.entails
  have na : P.NecNecessityOfDistinctness.schema ∪ P.Atomicity.schema ⟹
      single P.NecActuality.quoted :=
    Entails.trans (Entails.union (Entails.union_right _ _) bf)
      Proofs.atomicity_and_bf_imply_necessary_actuality.entails
  Entails.trans
    (Entails.union
      (Entails.trans (Entails.union na (Entails.union_left _ _)) c5_necessary_atomicity_t.entails)
      (Entails.trans (Entails.union_left _ _)
        Proofs.necessary_distinctness_necessary_r_implies_necessary_barcan_r.entails))
    necAtomicity_of_at_t_necBarcan

/-- `extensionality-r-implies-atomicity-r`, at every arity: Extensionality gives the
Fregean Axiom and Actuality; the Fregean Axiom gives `□ND` and makes Actuality necessary;
and in `C5` `□`Actuality gives Atomicity. -/
theorem extensionality_r_implies_atomicity_r :
    P.Extensionality.schema ⟹ P.Atomicity.schema :=
  have fa : P.Extensionality.schema ⟹ single P.FregeanAxiom.quoted :=
    Proofs.extensionality_r_implies_fregean_axiom.entails
  have act : P.Extensionality.schema ⟹ single P.Actuality.quoted :=
    Proofs.extensionality_r_implies_actuality.entails
  Entails.trans
    (Entails.union (Entails.trans fa Proofs.fregean_axiom_implies_necessary_distinctness_necessary_r.entails)
      (Entails.trans (Entails.union fa act) fregean_actuality_necessary_actuality.entails))
    c5_and_necessary_actuality_imply_atomicity

/-- `necessary-gallin-comprehension-implies-necessary-rigid-comprehension`, at every arity:
`□`Gallin gives `□ND`, and the boxed core at `σ → t`, vectorized. -/
theorem necessary_gallin_comprehension_implies_necessary_rigid_comprehension :
    P.NecGallinExtensionalComprehension.schema ⟹ P.NecRigidComprehension.schema :=
  Entails.mono_right (schema_subset_args _)
    (Entails.trans
      (Entails.union (Entails.refl _)
        Proofs.necessary_gallin_comprehension_implies_necessary_nd.entails)
      nec_gallin_c5_nec_rigid_comprehension.listEntails)

/-- `necessary-plenitude-r-implies-atomicity-r` (Propositions 2.13, 2.15 and 2.6 boxed),
at every arity: `□`Plenitude gives `□ND` and `□`Actuality, and in `C5` `□`Actuality gives
Atomicity. -/
theorem necessary_plenitude_r_implies_atomicity_r :
    P.NecPlenitude.schema ⟹ P.Atomicity.schema :=
  Entails.trans
    (Entails.union Proofs.necessary_plenitude_r_implies_necessary_distinctness_necessary_r.entails
      Proofs.necessary_plenitude_r_implies_necessary_actuality.entails)
    c5_and_necessary_actuality_imply_atomicity

/-- `necessary-plenitude-r-implies-necessary-atomicity-r`, at every arity. -/
theorem necessary_plenitude_r_implies_necessary_atomicity_r :
    P.NecPlenitude.schema ⟹ P.NecAtomicity.schema :=
  Entails.trans
    (Entails.union Proofs.necessary_plenitude_r_implies_necessary_distinctness_necessary_r.entails
      necessary_plenitude_r_implies_atomicity_r)
    c5_and_atomicity_imply_necessary_atomicity

/-! ### Boolean Completeness, Plenitude and the haecceities

The records at `σ → t` in `Results/Records.lean` whose greatest lower bounds are pointwise
meets `λz. ∀Y. X*Y → Yz`, or whose witnesses are haecceities `λx. u = x`, vectorized; and
the Plenitude records for output `σ' → t`, vectorized in `σ'`, every output type being
`σs ⇒* t`. -/

/-- `weak-rigid-comprehension-r-implies-boolean-completeness-r`, at every arity. -/
theorem weak_rigid_comprehension_r_implies_boolean_completeness_r :
    P.WeakRigidComprehension.schema ⟹ P.BooleanCompleteness.schema :=
  Entails.mono_right (schema_subset_args _)
    Proofs.weak_rigid_comprehension_r_implies_boolean_completeness_r.listEntails

/-- `rigid-comprehension-r-implies-boolean-completeness-r` (Proposition 2.8), at every
arity. -/
theorem rigid_comprehension_r_implies_boolean_completeness_r :
    P.RigidComprehension.schema ⟹ P.BooleanCompleteness.schema :=
  Entails.mono_right (schema_subset_args _)
    Proofs.rigid_comprehension_r_implies_boolean_completeness_r.listEntails

/-- `extensionality-r-implies-boolean-completeness-r`, at every arity. -/
theorem extensionality_r_implies_boolean_completeness_r :
    P.Extensionality.schema ⟹ P.BooleanCompleteness.schema :=
  Entails.mono_right (schema_subset_args _)
    Proofs.extensionality_r_implies_boolean_completeness_r.listEntails

/-- `necessary-rigid-comprehension-r-implies-necessary-boolean-completeness-r`, at every
arity. -/
theorem necessary_rigid_comprehension_r_implies_necessary_boolean_completeness_r :
    P.NecRigidComprehension.schema ⟹ P.NecBooleanCompleteness.schema :=
  Entails.mono_right (schema_subset_args _)
    Proofs.necessary_rigid_comprehension_r_implies_necessary_boolean_completeness_r.listEntails

/-- `c5-and-actuality-imply-completeness` (Proposition 2.5, right to left), at every arity:
Rigid Comprehension (Proposition 2.10), then Proposition 2.8. -/
theorem c5_and_actuality_imply_completeness :
    P.NecNecessityOfDistinctness.schema ∪ P.Actuality.schema ⟹ P.BooleanCompleteness.schema :=
  Entails.trans c5_and_actuality_imply_rigid_comprehension
    rigid_comprehension_r_implies_boolean_completeness_r

/-- `c5-and-atomicity-imply-necessary-completeness` (Proposition 2.6), at every arity:
`□`Rigid Comprehension, then Proposition 2.8 boxed. -/
theorem c5_and_atomicity_imply_necessary_completeness :
    P.NecNecessityOfDistinctness.schema ∪ P.Atomicity.schema ⟹
      P.NecBooleanCompleteness.schema :=
  Entails.trans c5_and_atomicity_imply_necessary_rigid_comprehension
    necessary_rigid_comprehension_r_implies_necessary_boolean_completeness_r

/-- `completeness-and-actuality-imply-weak-rigid-comprehension`, at every arity: the least
upper bound of the haecceities. -/
theorem completeness_and_actuality_imply_weak_rigid_comprehension :
    P.BooleanCompleteness.schema ∪ P.Actuality.schema ⟹ P.WeakRigidComprehension.schema :=
  Entails.mono_right (schema_subset_args _)
    Proofs.completeness_and_actuality_imply_weak_rigid_comprehension.listEntails

/-- `c5-and-completeness-imply-plenitude` (Proposition 2.14), at every output type. -/
theorem c5_and_completeness_imply_plenitude :
    P.NecNecessityOfDistinctness.schema ∪ P.BooleanCompleteness.schema ⟹ P.Plenitude.schema :=
  Entails.mono_right (schema_subset_args₂ _)
    (Entails.trans (Entails.union (Entails.union_right _ _) (Entails.union_left _ _))
      Proofs.c5_and_completeness_imply_plenitude.listEntails)

/-- `rigid-comprehension-and-nd-imply-plenitude` (Proposition 2.16), at every output
type. -/
theorem rigid_comprehension_and_nd_imply_plenitude :
    P.RigidComprehension.schema ∪ P.NecessityOfDistinctness.schema ⟹ P.Plenitude.schema :=
  Entails.mono_right (schema_subset_args₂ _)
    Proofs.rigid_comprehension_and_nd_imply_plenitude.listEntails

/-- `extensionality-r-implies-plenitude-r`, at every output type: Extensionality gives the
Fregean Axiom, hence `□ND`, and Boolean Completeness, and Proposition 2.14. -/
theorem extensionality_r_implies_plenitude_r :
    P.Extensionality.schema ⟹ P.Plenitude.schema :=
  Entails.trans
    (Entails.union
      (Entails.trans Proofs.extensionality_r_implies_fregean_axiom.entails
        Proofs.fregean_axiom_implies_necessary_distinctness_necessary_r.entails)
      extensionality_r_implies_boolean_completeness_r)
    c5_and_completeness_imply_plenitude

/-- `c5-and-atomicity-imply-necessary-plenitude`, at every output type: `□`Boolean
Completeness (Proposition 2.6) and Proposition 2.14 boxed. -/
theorem c5_and_atomicity_imply_necessary_plenitude :
    P.NecNecessityOfDistinctness.schema ∪ P.Atomicity.schema ⟹ P.NecPlenitude.schema :=
  Entails.mono_right (schema_subset_args₂ _)
    (Entails.trans
      (Entails.union c5_and_atomicity_imply_necessary_completeness (Entails.union_left _ _))
      necessary_completeness_c5_necessary_plenitude.listEntails)

/-- `actual-profile-r-implies-actuality`: Actual Profile over the empty list of argument
types is Actuality, on the nose. -/
theorem actual_profile_r_implies_actuality :
    P.ActualProfile.listSchema ⟹ P.Actuality.schema := by
  rintro a rfl
  exact Theorem.ax ⟨[], by simp [Ty.AllClosed], rfl⟩

end Meta

end Classicism
