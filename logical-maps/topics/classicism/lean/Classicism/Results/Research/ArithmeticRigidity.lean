import Classicism.Certified.Entailed

/-!
# Two sufficient conditions for Arithmetic Necessitism

Use Goodsell's countable join of the haecceities of the numbers, as formalized in
`Results/Records/Arithmetic.lean`. Its local conclusion is weak inextensibility.
Necessary Countable Boolean Completeness boxes that conclusion. Tame Rigidity
instead upgrades the weak rigidity supplied by unboxed Countable Boolean Completeness.
-/

namespace Classicism.Proofs
open Classicism.P Classicism.Paper

/-- The boxed join premise supplies inextensibility at every accessible point. -/
theorem necessary_countable_boolean_completeness_implies_arithmetic_necessitism
    {σ : Type} [Ty σ] :
    NecCountableBooleanCompleteness σ (((σ → Prop) → Prop) → Prop) →
      ArithmeticNecessitism σ := fun hcbc hI =>
  ⟨⟨finiteCardinality_persistent,
    modal_K _ _ (nec% (finiteCardinality_weaklyInextensible_of_cbc (σ := σ))) hcbc⟩,
   fun m n hm hn => finiteCardinality_nd hI m hm n hn⟩

/-- Local joins and the promotion of weak to full rigidity at the number-property type suffice. -/
theorem tame_rigidity_and_countable_boolean_completeness_imply_arithmetic_necessitism
    {σ : Type} [Ty σ] :
    TameRigidity (((σ → Prop) → Prop) → Prop) →
      CountableBooleanCompleteness σ (((σ → Prop) → Prop) → Prop) →
      ArithmeticNecessitism σ := fun htame hcbc hI =>
  ⟨htame FiniteCardinality
    ⟨box_elim finiteCardinality_persistent, finiteCardinality_weaklyInextensible_of_cbc hcbc⟩,
   fun m n hm hn => finiteCardinality_nd hI m hm n hn⟩

end Classicism.Proofs

#classicism_derive Classicism.Proofs.necessary_countable_boolean_completeness_implies_arithmetic_necessitism
  Classicism.Proofs.tame_rigidity_and_countable_boolean_completeness_imply_arithmetic_necessitism
#classicism_entails Classicism.Proofs.necessary_countable_boolean_completeness_implies_arithmetic_necessitism
  Classicism.Proofs.tame_rigidity_and_countable_boolean_completeness_imply_arithmetic_necessitism
