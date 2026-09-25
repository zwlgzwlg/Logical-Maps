import Classicism.Tools.Schema
import Classicism.Certified.Schemas
import Classicism.Principles
import Classicism.Pointwise

/-!
# Atomicity at type `t` and BF imply Atomicity

The map's record `atomicity-t-and-bf-imply-atomicity` (Cian Dorr, 23 September 2026):
given Atomicity at type `t` and BF at every type, every non-bottom relation of every
relational type has an atom below it.

The informal proof runs, for `X` of type `σ₁ → ⋯ → σₙ → t`: `X ≠ ⊥` gives `◇∃ȳ. Xȳ`; BF at
`σ₁, …, σₙ` gives `x̄` with `Xx̄ ≠ ⊥`; Atomicity at `t` gives an atom `w ≤ Xx̄`; and
`λȳ. w ∧ ȳ = x̄` is an atom below `X`. It is a metatheorem, "for every `n`", with a chunk
of object-level reasoning inside. Here it is an induction on the relational type, one
argument type at a time:

1. **The step**, in the shallow layer: `Atomicity τ → BF σ → Atomicity (σ → τ)`, a
   theorem of Classicism at the type variables `σ`, `τ`, proved with Lean's own tactics.
   The pointwise reasoning at `τ` ("by Leibniz's law", "under the box") is the class
   `Pointwise`; the passage from `X ≠ ⊥` to an instance `Xz ≠ ⊥` is BF at `σ`; and each
   fact carried under the box is a closed lemma necessitated with `nec%` and pushed
   through with `K`, as the paper does.
2. **Its certification**: `#classicism_certify` runs Appendix A on the proof, derives the
   result in the object language, and states it as a rule between the instances of the
   schemas, `atomicity_step.rule σ' τ' : C ⊢ Atomicity_τ' → BF_σ' → Atomicity_{σ'→τ'}`.
3. **The theorem**, in the metalogical layer: induction on the type, the base case an
   axiom and the step the rule, giving the entailment between axiom sets that is the
   map's arrow.

Only the type-`t` instance of Atomicity is used, and BF only at the argument types of
the conclusion's type, exactly as the write-up says.

**Build status.** Certified by the direct route (evening of 24 September): the module
builds in eleven seconds, the rules resting on `propext` and `Quot.sound`. Through the
strict route earlier that day the same file elaborated in twelve minutes and its `.olean`
never finished writing; that is what led to the change of route (see `Meta/README.md`).
-/

namespace Classicism

/-! ## 1. The step -/

section pointwise
variable {σ τ : Type} [Ty σ] [Rel τ] [Pointwise τ]

/-! The relation `λy. w ∧ y = z` — `w` at `z`, empty elsewhere — and three facts about it,
each a closed lemma so that it can be carried under the box. In the paper each is "by
Leibniz's law"; here Leibniz's law is the case split on `y = z` and a rewrite. -/

/-- `w ⊑ Xz` gives `(λy. w ∧ y = z) ⊑ X`. -/
theorem pin_boxImp (X : σ → τ) (w : τ) (z : σ) :
    boxImp w (X z) → boxImp (fun y => Rel.and w (constP (y = z))) X := fun h y =>
  (em (y = z)).elim
    (fun hyz => by
      show boxImp (Rel.and w (constP (y = z))) (X y)
      rw [hyz]
      exact boxImp_trans _ w _ (boxImp_and_left w _) h)
    (fun hyz => boxImp_of_and_constP w (X y) (y = z) hyz)

/-- `Z ⊑ (λy. w ∧ y = z)` and `Zz = w` give `Z ≡ (λy. w ∧ y = z)`. -/
theorem pin_coext (Z : σ → τ) (w : τ) (z : σ) :
    boxImp Z (fun y => Rel.and w (constP (y = z))) → Z z = w →
      coext Z (fun y => Rel.and w (constP (y = z))) := fun h₁ h₂ y =>
  (em (y = z)).elim
    (fun hyz => by
      show coext (Z y) (Rel.and w (constP (y = z)))
      rw [hyz, h₂]
      exact coext_of_boxImp _ _ (boxImp_and_constP_self w _ rfl) (boxImp_and_left w _))
    (fun hyz => coext_of_boxImp _ _ (h₁ y) (boxImp_of_and_constP w (Z y) (y = z) hyz))

/-- `Z ⊑ (λy. w ∧ y = z)` and `Zz ⊑ ¬Zz` give `Z ⊑ ¬Z`. -/
theorem pin_bot (Z : σ → τ) (w : τ) (z : σ) :
    boxImp Z (fun y => Rel.and w (constP (y = z))) → boxImp (Z z) (Rel.neg (Z z)) →
      boxImp Z (Rel.neg Z) := fun h₁ h₂ y =>
  (em (y = z)).elim
    (fun hyz => by
      show boxImp (Z y) (Rel.neg (Z y))
      rw [hyz]
      exact h₂)
    (fun hyz => boxImp_trans _ _ _ (boxImp_and_elim_right w _ _ (h₁ y))
      (boxImp_of_constP (Rel.neg (Z y)) _ hyz))

end pointwise

section step
variable {σ τ : Type} [Ty σ] [Rel τ] [Order τ] [Pointwise τ]

/-! The step itself, in the pieces the paper's argument has. Each is a closed lemma of
its own, since the translator derives a cited lemma once and cites it, and a derivation is
checked piece by piece rather than as one proof. -/

omit [Pointwise τ] in
/-- A possible instance: `X ≠ ⊥` gives some `Xz ≠ ⊥`, for were every `Xz ≤ ¬Xz`, BF would
make `X ≤ ¬X`. -/
theorem instance_of_ne_bot (X : σ → τ) :
    P.Barcan σ → ¬ Rel.le X (Rel.neg X) → ∃ z, ¬ Rel.le (X z) (Rel.neg (X z)) := fun hBF hX =>
  (em (∃ z, ¬ Rel.le (X z) (Rel.neg (X z)))).elim id fun hno =>
    absurd ((le_iff X (Rel.neg X)).2 (hBF (fun z => boxImp (X z) (Rel.neg (X z))) fun z =>
      (em (Rel.le (X z) (Rel.neg (X z)))).elim (fun h => (le_iff _ _).1 h)
        (fun h => absurd ⟨z, h⟩ hno))) hX

/-- `w ≤ Xz` gives `(λy. w ∧ y = z) ≤ X`: `w ⊑ Xz` under the box. -/
theorem pin_le (X : σ → τ) (w : τ) (z : σ) :
    Rel.le w (X z) → Rel.le (fun y => Rel.and w (constP (y = z))) X := fun hwX =>
  (le_iff _ _).2 (modal_K _ _ (nec% (pin_boxImp X w z)) ((le_iff _ _).1 hwX))

/-- `Z ≤ (λy. w ∧ y = z)` gives `Zz ≤ w`. -/
theorem pin_le_apply (Z : σ → τ) (w : τ) (z : σ) :
    Rel.le Z (fun y => Rel.and w (constP (y = z))) → Rel.le (Z z) w := fun hZA =>
  (le_iff _ _).2 (modal_K _ _ (nec% (boxImp_and_elim_left w (constP (z = z)) (Z z)))
    (converse_barcan (fun y => boxImp (Z y) (Rel.and w (constP (y = z))))
      ((le_iff _ _).1 hZA) z))

/-- `Z ≤ (λy. w ∧ y = z)` and `Zz = w` give `Z = (λy. w ∧ y = z)`, by Intensionality. -/
theorem pin_eq (Z : σ → τ) (w : τ) (z : σ) :
    Rel.le Z (fun y => Rel.and w (constP (y = z))) → Z z = w →
      Z = (fun y => Rel.and w (constP (y = z))) := fun hZA hZw =>
  intensionality Z _ (modal_K _ _ (modal_K _ _ (nec% (pin_coext Z w z))
    ((le_iff _ _).1 hZA)) (necessity_of_identity _ _ hZw))

/-- `Z ≤ (λy. w ∧ y = z)` and `Zz ≤ ¬Zz` give `Z ≤ ¬Z`. -/
theorem pin_le_neg (Z : σ → τ) (w : τ) (z : σ) :
    Rel.le Z (fun y => Rel.and w (constP (y = z))) → Rel.le (Z z) (Rel.neg (Z z)) →
      Rel.le Z (Rel.neg Z) := fun hZA hbot =>
  (le_iff _ _).2 (modal_K _ _ (modal_K _ _ (nec% (pin_bot Z w z))
    ((le_iff _ _).1 hZA)) ((le_iff _ _).1 hbot))

/-- `Z ≤ ¬Z` gives `Z ≤ A` for any `A`. -/
theorem le_of_le_neg (Z A : σ → τ) : Rel.le Z (Rel.neg Z) → Rel.le Z A := fun hZ =>
  (le_iff _ _).2 (modal_K _ _ (nec% (boxImp_of_boxImp_neg Z A)) ((le_iff _ _).1 hZ))

/-- `(λy. w ∧ y = z) ≤ ¬(λy. w ∧ y = z)` gives `w ≤ ¬w`: instantiate at `z`, where the
relation is `w ∧ ⊤`. -/
theorem le_neg_of_pin_le_neg (w : τ) (z : σ) :
    Rel.le (fun y => Rel.and w (constP (y = z))) (Rel.neg (fun y => Rel.and w (constP (y = z)))) →
      Rel.le w (Rel.neg w) := fun hA =>
  (le_iff _ _).2 (modal_K _ _ (modal_K _ _ (nec% (boxImp_neg_of_and_constP w (z = z)))
    (necessity_of_identity z z rfl))
    (converse_barcan
      (fun y => boxImp (Rel.and w (constP (y = z))) (Rel.neg (Rel.and w (constP (y = z)))))
      ((le_iff _ _).1 hA) z))

/-- If `w` is an atom, so is `λy. w ∧ y = z`: what is strictly below it is `⊥`, since its
value at `z` is `w` or `⊥`; and `⊥` is strictly below it, since it is not `⊥`. -/
theorem pin_atom (w : τ) (z : σ) : Atom w → Atom (fun y => Rel.and w (constP (y = z))) :=
  fun hw Z => Iff.intro
    (fun h => (em (Z z = w)).elim
      (fun hZw => absurd (pin_eq Z w z h.1 hZw) h.2)
      (fun hZw => pin_le_neg Z w z h.1 ((hw (Z z)).1 ⟨pin_le_apply Z w z h.1, hZw⟩)))
    (fun hZ => ⟨le_of_le_neg Z _ hZ,
      fun hZA => not_le_neg_of_atom hw (le_neg_of_pin_le_neg w z (hZA ▸ hZ))⟩)

/-- **The step.** Atomicity at `τ` and BF at `σ` give Atomicity at `σ → τ`: for `X ≠ ⊥`,
BF gives `z` with `Xz ≠ ⊥`, Atomicity at `τ` an atom `w ≤ Xz`, and `λy. w ∧ y = z` is an
atom below `X`. -/
theorem atomicity_step : P.Atomicity τ → P.Barcan σ → P.Atomicity (σ → τ) := fun hAt hBF X =>
  (em (Rel.le X (Rel.neg X))).elim Or.inl fun hX => Or.inr <|
    (instance_of_ne_bot X hBF hX).elim fun z hz =>
      ((hAt (X z)).elim (fun h => absurd h hz) id).elim fun w hw =>
        ⟨fun y => Rel.and w (constP (y = z)), pin_atom w z hw.1, pin_le X w z hw.2⟩

end step

/-- Atomicity at `t` is the instance of Atomicity at `t`, in the map's two spellings. -/
theorem atomicityT_step : P.AtomicityT → P.Atomicity Prop := fun h => h

/-! ## 2. Certification

Each theorem of the step becomes a rule of the object language. For a shallow theorem
`foo : P₁ … → … → Q …`, `#classicism_certify foo` quotes into schemas any principle it
mentions that has none yet (here all come from `Certified/Schemas.lean`), translates its
proof into a derivation, and reads the derivation through the schemas, declaring two
kernel-checked theorems, with `foo`'s type parameters as object types (`σ' : Ty` for a
`[Ty σ]`, `τ' : RTy` for a `[Rel τ]`):

* `foo.derivable : ∀ σ' τ', Meta.Theorem C.axiomsMinus ⌜foo σ' τ'⌝`, the derivation of the
  quoted statement of `foo`, in `C⁻` (in `C` when the proof uses Existence at `e`);
* `foo.rule : ∀ σ' τ', C.Theorem (Term.imp (P₁.quoted …) (… (Q.quoted …)))`, the same
  derivation lifted to `C` and stated as a rule between *instances* of the schemas, each
  written through its principle's `quoted` so that it composes with `Theorem.ax` and
  `Theorem.mp`.

So the command below makes available

    atomicityT_step.rule : C.Theorem (Term.imp P.AtomicityT.quoted (P.Atomicity.quoted RTy.t))
    atomicity_step.rule  : ∀ (σ' : Ty) (τ' : RTy), C.Theorem (Term.imp (P.Atomicity.quoted τ')
                             (Term.imp (P.Barcan.quoted σ') (P.Atomicity.quoted (σ' ⇒ τ'))))

which part 3 applies at the types of the induction. The report prints each rule's type and
the Lean axioms it rests on. -/

#classicism_certify Classicism.atomicityT_step Classicism.atomicity_step

/-! ## 3. The theorem -/

open Meta Meta.AxiomSet in
/-- **Atomicity at `t` and BF entail Atomicity**, at every relational type: the map's
arrow. By induction on the type: at `t` the premise, at `σ → τ` the rule. -/
theorem atomicity_of_atomicityT_barcan :
    P.AtomicityT.schema ∪ P.Barcan.schema ⟹ P.Atomicity.schema := by
  rintro a ⟨ρ, rfl⟩
  induction ρ using RTy.induction with
  | t => exact (Theorem.ofC atomicityT_step.rule).mp (Theorem.ax (Or.inl rfl))
  | arr σ ρ ih =>
    exact (Theorem.ofC (atomicity_step.rule σ ρ)).mp₂ ih (Theorem.ax (Or.inr ⟨σ, rfl⟩))

end Classicism
