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
`x̄`: "BF, one argument at a time", "the persistent coextension `λȳ. w ≤ X[ȳ]`". The
shallow layer has no tuples; a relational type is a type parameter `τ` with `Rel τ`, and
pointwise reasoning at `τ` goes through the laws of `Pointwise`, which the translator
derives for every object type by induction on the type. This file does the arity results
that need nothing more than that, in three parts, as `Results/Atomicity.lean` does:

1. **The shallow layer.** BF over a whole argument tuple, `P.BarcanArgs τ`, is an auxiliary
   principle (not one of the map's): at `t` a theorem, and at `σ → τ` a consequence of
   BF at `σ` and itself at `τ`; likewise its necessitation. Then the shallow cores of the
   results, each a theorem at a Rel-parameter `τ`, from the map's premises
   and `P.BarcanArgs τ` or its box.
2. **Certification.** `#classicism_certify` makes each a rule between schema instances,
   `#classicism_entails` an entailment between schemas.
3. **The metalogic.** The inductions on the type giving BF over tuples from BF, and the
   compositions of certified entailments, among them the ones already in
   `Certified/Entailed.lean`, into the map's arrows. Each theorem here named by a map id
   is that record, for every arity.
-/

namespace Classicism
open Paper

/-! ## 1. The shallow layer -/

section barcanArgs
variable {σ τ : Type} [Ty σ] [Rel τ]

/-- BF over the empty tuple: `(⊤ → □X) → □(⊤ → X)`. -/
theorem barcanArgs_t : P.BarcanArgs Prop := fun X h =>
  modal_K _ _ (nec% (fun (hx : X) (_ : True) => hx)) (h trivial)

/-- **The step**: BF at `σ` and BF over the tuple of `τ` give BF over the tuple of `σ → τ`.
For `∀z ȳ. □X z ȳ`, BF over `τ` gives `∀z. □∀ȳ. X z ȳ`, and BF at `σ` boxes the `∀z`. -/
theorem barcanArgs_step : P.Barcan σ → P.BarcanArgs τ → P.BarcanArgs (σ → τ) :=
  fun bf ba X h => bf (λ z ↦ Rel.top τ ⊆ X z) fun z => ba (X z) (h z)

/-- `□`BF over the empty tuple: the necessitation of the theorem at `t`. -/
theorem necBarcanArgs_t : P.NecBarcanArgs Prop := nec% barcanArgs_t

/-- The boxed step, by `K`. -/
theorem necBarcanArgs_step : P.NecBarcan σ → P.NecBarcanArgs τ → P.NecBarcanArgs (σ → τ) :=
  fun h₁ h₂ => modal_K _ _ (modal_K _ _ (nec% (barcanArgs_step (σ := σ) (τ := τ))) h₁) h₂

end barcanArgs

section shallowCores
variable {τ : Type} [Rel τ] [Pointwise τ]

/-- With `B` and BF over the tuple, a persistent relation is weakly inextensible (the
argument of Classicism, n. 41, at every arity): if `Y ⊆ □Z`, then pointwise
`□(¬Y ∨ Z)`, by `B` where `Y` fails, and BF over the tuple boxes the tuple quantifier. -/
theorem weaklyInextensible_of_b_barcanArgs (Y : τ) :
    (∀ p : Prop, p → □ ◇ p) → P.BarcanArgs τ → Persistent Y → WeaklyInextensible Y :=
  fun b ba hP Z hZ =>
    modal_K _ _ (nec% (boxImp_of_top_or Y Z))
      (ba _ (top_boxAt_of_b Y Z b hZ (top_boxAt_of_box Y (boxAt Y) hP)))

/-- In `C5`, with `□`BF over the tuple, a persistent relation is inextensible. -/
theorem inextensible_of_persistent_c5 (Y : τ) :
    □ (∀ p : Prop, p → □ ◇ p) → P.NecBarcanArgs τ → Persistent Y → Inextensible Y :=
  fun hb hba hP =>
    modal_K _ _ (modal_K _ _ (modal_K _ _ (nec% (weaklyInextensible_of_b_barcanArgs Y)) hb) hba)
      (modal_four _ hP)

/-- A relation whose negation is weakly persistent is weakly inextensible, given BF over
the tuple: where `Y` fails it fails necessarily. -/
theorem weaklyInextensible_of_neg (Y : τ) :
    P.BarcanArgs τ → WeaklyPersistent (¬ Y) → WeaklyInextensible Y :=
  fun ba hn Z hZ =>
    modal_K _ _ (nec% (boxImp_of_top_or Y Z)) (ba _ (top_boxAt_of_neg Y Z hZ hn))

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

/-- The shallow core of Proposition 2.10 at every arity: Actuality, `□ND` and `□`BF over the
tuple give Rigid Comprehension at `τ`. The persistent coextension is inextensible in
`C5`. -/
theorem c5_actuality_rigid_comprehension :
    P.Actuality → P.NecNecessityOfDistinctness Prop → P.NecBarcanArgs τ →
      P.RigidComprehension τ := fun act hnd hba X =>
  act.elim fun w (hw : ActualWorld w) =>
    ⟨_, ⟨(persistent_coext_of_actual X w hw).1,
      inextensible_of_persistent_c5 _ (Proofs.box_b_of_box_nd_t hnd) hba
        (persistent_coext_of_actual X w hw).1⟩,
     (persistent_coext_of_actual X w hw).2⟩

/-- The same, boxed: `□`Actuality, `□ND` and `□`BF over the tuple give `□`Rigid
Comprehension at `τ`. -/
theorem c5_necessary_actuality_necessary_rigid_comprehension :
    P.NecActuality → P.NecNecessityOfDistinctness Prop → P.NecBarcanArgs τ →
      P.NecRigidComprehension τ := fun hna hnd hba =>
  modal_K _ _ (modal_K _ _ (modal_K _ _ (nec% (c5_actuality_rigid_comprehension (τ := τ))) hna)
    (modal_four _ hnd)) (modal_four _ hba)

/-- Gallin Extensional Comprehension and BF over the tuple give Weak Rigid Comprehension:
the Gallin-rigid coextension is persistent and, its negation being persistent, weakly
inextensible. -/
theorem gallin_barcanArgs_weak_rigid_comprehension :
    P.GallinExtensionalComprehension τ → P.BarcanArgs τ → P.WeakRigidComprehension τ :=
  fun g ba X => (g X).elim fun Y hY =>
    ⟨Y, ⟨hY.1, weaklyInextensible_of_neg Y ba (box_elim hY.2.1)⟩, hY.2.2⟩

/-- And with `□`BF over the tuple, Rigid Comprehension: the argument above under the box,
the persistence of the negation being boxed already. -/
theorem gallin_necBarcanArgs_rigid_comprehension :
    P.GallinExtensionalComprehension τ → P.NecBarcanArgs τ → P.RigidComprehension τ :=
  fun g hba X => (g X).elim fun Y hY =>
    ⟨Y, ⟨hY.1, modal_K _ _ (modal_K _ _ (nec% (weaklyInextensible_of_neg Y)) hba) hY.2.1⟩, hY.2.2⟩

/-- Boxed Gallin Extensional Comprehension and `□`BF over the tuple give `□`Rigid
Comprehension. -/
theorem nec_gallin_necBarcanArgs_nec_rigid_comprehension :
    P.NecGallinExtensionalComprehension τ → P.NecBarcanArgs τ → P.NecRigidComprehension τ :=
  fun hg hba => modal_K _ _ (modal_K _ _ (nec% (gallin_necBarcanArgs_rigid_comprehension (τ := τ))) hg)
    (modal_four _ hba)

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

#classicism_certify Classicism.barcanArgs_t Classicism.barcanArgs_step
  Classicism.necBarcanArgs_t Classicism.necBarcanArgs_step
  Classicism.actuality_implies_persistent_comprehension_r
  Classicism.c5_actuality_rigid_comprehension
  Classicism.c5_necessary_actuality_necessary_rigid_comprehension
  Classicism.gallin_barcanArgs_weak_rigid_comprehension
  Classicism.gallin_necBarcanArgs_rigid_comprehension
  Classicism.nec_gallin_necBarcanArgs_nec_rigid_comprehension
  Classicism.necAtomicity_step Classicism.c5_necessary_atomicity_t
  Classicism.fregean_actuality_necessary_actuality
  Classicism.very_weak_rigid_comprehension_r_implies_weak_rigid_comprehension_r
  Classicism.extensionality_r_implies_rigid_comprehension_r
  Classicism.c5_and_persistent_comprehension_imply_gallin
  Classicism.c5_and_necessary_rigid_comprehension_imply_necessary_gallin_comprehension

#classicism_entails Classicism.actuality_implies_persistent_comprehension_r
  Classicism.c5_actuality_rigid_comprehension
  Classicism.c5_necessary_actuality_necessary_rigid_comprehension
  Classicism.gallin_barcanArgs_weak_rigid_comprehension
  Classicism.gallin_necBarcanArgs_rigid_comprehension
  Classicism.nec_gallin_necBarcanArgs_nec_rigid_comprehension
  Classicism.c5_necessary_atomicity_t Classicism.fregean_actuality_necessary_actuality
  Classicism.very_weak_rigid_comprehension_r_implies_weak_rigid_comprehension_r
  Classicism.extensionality_r_implies_rigid_comprehension_r
  Classicism.c5_and_persistent_comprehension_imply_gallin
  Classicism.c5_and_necessary_rigid_comprehension_imply_necessary_gallin_comprehension

/-! ## 3. The metalogic -/

namespace Meta
open AxiomSet

/-- **BF entails BF over every argument tuple**, by induction on the type. -/
theorem barcanArgs_of_barcan : P.Barcan.schema ⟹ P.BarcanArgs.schema := by
  rintro a ⟨ρ, hρ, rfl⟩
  induction ρ using RTy.induction with
  | t => exact Theorem.ofC barcanArgs_t.rule
  | arr σ ρ ih =>
    exact (Theorem.ofC (barcanArgs_step.rule σ ρ)).mp₂ (Theorem.ax ⟨σ, hρ.1, rfl⟩) (ih hρ.2)

/-- **`□`BF entails `□`BF over every argument tuple.** -/
theorem necBarcanArgs_of_necBarcan : P.NecBarcan.schema ⟹ P.NecBarcanArgs.schema := by
  rintro a ⟨ρ, hρ, rfl⟩
  induction ρ using RTy.induction with
  | t => exact Theorem.ofC necBarcanArgs_t.rule
  | arr σ ρ ih =>
    exact (Theorem.ofC (necBarcanArgs_step.rule σ ρ)).mp₂ (Theorem.ax ⟨σ, hρ.1, rfl⟩) (ih hρ.2)

/-- **Atomicity at `t` and BF entail Atomicity**, with Atomicity at `t` read as the
`t`-instance of Atomicity (the form the `C5` records conclude with): the induction of
`Results/Atomicity.lean`, from the instance. -/
theorem atomicity_of_atomicity_at_t_barcan :
    single (P.Atomicity.quoted RTy.t) ∪ P.Barcan.schema ⟹ P.Atomicity.schema := by
  rintro a ⟨ρ, hρ, rfl⟩
  induction ρ using RTy.induction with
  | t => exact Theorem.ax (Or.inl rfl)
  | arr σ ρ ih =>
    exact (Theorem.ofC (atomicity_step.rule σ ρ)).mp₂ (ih hρ.2) (Theorem.ax (Or.inr ⟨σ, hρ.1, rfl⟩))

/-- `□ND` entails `□`BF over every tuple. -/
theorem necBarcanArgs_of_c5 : P.NecNecessityOfDistinctness.schema ⟹ P.NecBarcanArgs.schema :=
  Entails.trans Proofs.necessary_distinctness_necessary_r_implies_necessary_barcan_r.entails
    necBarcanArgs_of_necBarcan

/-- `actuality-implies-persistent-comprehension-r`, the map's record, at every arity. -/
theorem actuality_implies_persistent_comprehension_r :
    P.Actuality.schema ⟹ P.PersistentComprehension.schema :=
  Classicism.actuality_implies_persistent_comprehension_r.entails

/-- `c5-and-actuality-imply-rigid-comprehension` (Proposition 2.10), at every arity. -/
theorem c5_and_actuality_imply_rigid_comprehension :
    P.NecNecessityOfDistinctness.schema ∪ P.Actuality.schema ⟹ P.RigidComprehension.schema :=
  Entails.trans
    (Entails.union (Entails.union (Entails.union_right _ _) (Entails.union_left _ _))
      (Entails.trans (Entails.union_left _ _) necBarcanArgs_of_c5))
    c5_actuality_rigid_comprehension.entails

/-- `gallin-comprehension-and-bf-imply-weak-rigid-comprehension`, at every arity. -/
theorem gallin_comprehension_and_bf_imply_weak_rigid_comprehension :
    P.GallinExtensionalComprehension.schema ∪ P.Barcan.schema ⟹
      P.WeakRigidComprehension.schema :=
  Entails.trans
    (Entails.union (Entails.union_left _ _)
      (Entails.trans (Entails.union_right _ _) barcanArgs_of_barcan))
    gallin_barcanArgs_weak_rigid_comprehension.entails

/-- `gallin-comprehension-and-bf-imply-rigid-comprehension`, at every arity: Gallin gives
ND, ND and BF give `□ND`, which gives `□`BF over every tuple. -/
theorem gallin_comprehension_and_bf_imply_rigid_comprehension :
    P.GallinExtensionalComprehension.schema ∪ P.Barcan.schema ⟹ P.RigidComprehension.schema :=
  have nd : P.GallinExtensionalComprehension.schema ∪ P.Barcan.schema ⟹
      P.NecessityOfDistinctness.schema :=
    Entails.trans (Entails.union_left _ _) Proofs.gallin_comprehension_implies_nd.entails
  have nnd : P.GallinExtensionalComprehension.schema ∪ P.Barcan.schema ⟹
      P.NecNecessityOfDistinctness.schema :=
    Entails.trans (Entails.union nd (Entails.union_right _ _))
      Proofs.nd_and_bf_imply_necessary_nd.entails
  Entails.trans
    (Entails.union (Entails.union_left _ _) (Entails.trans nnd necBarcanArgs_of_c5))
    gallin_necBarcanArgs_rigid_comprehension.entails

/-- `c5-and-atomicity-imply-necessary-rigid-comprehension`, at every arity: Atomicity and
BF (from `□ND`) give `□`Actuality (Proposition 2.7), and the boxed shallow core. -/
theorem c5_and_atomicity_imply_necessary_rigid_comprehension :
    P.NecNecessityOfDistinctness.schema ∪ P.Atomicity.schema ⟹
      P.NecRigidComprehension.schema :=
  have bf : P.NecNecessityOfDistinctness.schema ∪ P.Atomicity.schema ⟹ P.Barcan.schema :=
    Entails.trans (Entails.union_left _ _) Proofs.necessary_nd_implies_bf.entails
  have na : P.NecNecessityOfDistinctness.schema ∪ P.Atomicity.schema ⟹
      single P.NecActuality.quoted :=
    Entails.trans (Entails.union (Entails.union_right _ _) bf)
      Proofs.atomicity_and_bf_imply_necessary_actuality.entails
  Entails.trans
    (Entails.union (Entails.union na (Entails.union_left _ _))
      (Entails.trans (Entails.union_left _ _) necBarcanArgs_of_c5))
    c5_necessary_actuality_necessary_rigid_comprehension.entails

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

/-- **`□`Atomicity at `t` and `□`BF entail `□`Atomicity**, by induction on the type. -/
theorem necAtomicity_of_at_t_necBarcan :
    single (P.NecAtomicity.quoted RTy.t) ∪ P.NecBarcan.schema ⟹ P.NecAtomicity.schema := by
  rintro a ⟨ρ, hρ, rfl⟩
  induction ρ using RTy.induction with
  | t => exact Theorem.ax (Or.inl rfl)
  | arr σ ρ ih =>
    exact (Theorem.ofC (necAtomicity_step.rule σ ρ)).mp₂ (ih hρ.2) (Theorem.ax (Or.inr ⟨σ, hρ.1, rfl⟩))

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
`□`Gallin gives `□ND`, hence `□`BF over every tuple, and the boxed shallow core. -/
theorem necessary_gallin_comprehension_implies_necessary_rigid_comprehension :
    P.NecGallinExtensionalComprehension.schema ⟹ P.NecRigidComprehension.schema :=
  Entails.trans
    (Entails.union (Entails.refl _)
      (Entails.trans Proofs.necessary_gallin_comprehension_implies_necessary_nd.entails
        necBarcanArgs_of_c5))
    nec_gallin_necBarcanArgs_nec_rigid_comprehension.entails

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

end Meta

end Classicism
