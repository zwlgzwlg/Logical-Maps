import Classicism.Models.PointedParts
import Classicism.Results.Consistency.Consistency

/-!
# Consistency facts from the models with a point adjoined

The packages of Classicism, Appendix D, after Part 8: each of the eight monoid models with a
point adjoined (`Models/Pointed.lean`, `Models/PointedParts.lean`), in which No Pure
Contingency fails and principles can be contingently false. For each part, the statuses
at `ℕ` hold together, so their union is consistent with Classicism:

- in every part, `ND_e` and Boolean Completeness at `e → t` are **contingently false**
  (`¬P` and `◇P`), Atomlessness is false, and the paper's `◇(□ND_e ∧ Atomicity)` holds
  (`common`);
- `BF`, Actuality and Atomicity at `t` are **necessary** (`□P`) where the one-object model
  has them, and contingently false where it does not.

| part | `BF` | Actuality | Atomicity (`t`) |
| --- | --- | --- | --- |
| 1⁺, 2⁺ | `□BF_σ` | c. false | c. false |
| 3⁺ | c. false (`e`) | c. false | c. false |
| 4⁺ | c. false | `□` | c. false |
| 5⁺ | `□BF_σ` | `□` | c. false |
| 6⁺ | c. false | c. false | `□` |
| 7⁺ | c. false | `□` | `□` |
| 8⁺ | `□BF_σ` | `□` | `□` |

Every one-object model satisfies No Pure Contingency, so none of these packages, with its
contingently false principles, follows from the one-object models' facts.
-/

namespace Classicism.Meta.ConsistencyPointed

open AxiomSet CategoryTheory Intensional Intensional.Premodel Intensional.Pointed Intensional.Monoids

/-- A sentence contingently false: `¬P` and `◇P`. -/
abbrev cfalse (p : Sentence Signature.pure) : AxiomSet Signature.pure :=
  single (Term.neg p) ∪ single (Term.dia p)

/-- What every part has: `ND_e` and Boolean Completeness at `e → t` contingently false,
Atomlessness false, `◇(□ND_e ∧ Atomicity)`. -/
abbrev common : AxiomSet Signature.pure :=
  cfalse (Sentence.nd .e) ∪ cfalse (P.BooleanCompleteness.quoted (.arr .e .t)) ∪
    single (Term.neg P.Atomlessness.quoted) ∪
    single (Term.dia (Term.conj (Term.box (Sentence.nd .e)) P.AtomicityT.quoted))

/-- Part 1⁺, the bijections. -/
theorem part1_consistent :
    Consistent (common ∪ AxiomSet.box P.Barcan.schema ∪ cfalse P.Actuality.quoted ∪
      cfalse P.AtomicityT.quoted) :=
  Consistent.of_model _ (model_isModel PointedParts.bij)
    (holdsAx_union _ (holdsAx_union _ (holdsAx_union _
      (holdsAx_common _ PointedParts.Bij.not_bc)
      (holdsAx_box_bf _ PointedParts.Bij.bf))
      (holdsAx_cfalse _ actuality_pure PointedParts.Bij.not_actuality fun k => actuality_pt _ k))
      (holdsAx_cfalse _ atomicityT_pure PointedParts.Bij.not_atomicityT fun k => atomicityT_pt _ k))

/-- Part 2⁺, the monotone surjections. -/
theorem part2_consistent :
    Consistent (common ∪ AxiomSet.box P.Barcan.schema ∪ cfalse P.Actuality.quoted ∪
      cfalse P.AtomicityT.quoted) :=
  Consistent.of_model _ (model_isModel monoSurj)
    (holdsAx_union _ (holdsAx_union _ (holdsAx_union _
      (holdsAx_common _ PointedParts.MonoSurj.not_bc)
      (holdsAx_box_bf _ PointedParts.MonoSurj.bf))
      (holdsAx_cfalse _ actuality_pure PointedParts.MonoSurj.not_actuality fun k => actuality_pt _ k))
      (holdsAx_cfalse _ atomicityT_pure PointedParts.MonoSurj.not_atomicityT fun k => atomicityT_pt _ k))

/-- Part 3⁺, the monotone functions. -/
theorem part3_consistent :
    Consistent (common ∪ cfalse (Sentence.bf .e) ∪ cfalse P.Actuality.quoted ∪
      cfalse P.AtomicityT.quoted) :=
  Consistent.of_model _ (model_isModel mono)
    (holdsAx_union _ (holdsAx_union _ (holdsAx_union _
      (holdsAx_common _ PointedParts.Mono.not_bc)
      (holdsAx_cfalse _ (bf_pure .e) PointedParts.Mono.not_bf_e fun k => bf_pt _ k .e))
      (holdsAx_cfalse _ actuality_pure PointedParts.Mono.not_actuality fun k => actuality_pt _ k))
      (holdsAx_cfalse _ atomicityT_pure PointedParts.Mono.not_atomicityT fun k => atomicityT_pt _ k))

/-- Part 4⁺, monotone and collapsing `0, 1` unless the identity. -/
theorem part4_consistent :
    Consistent (common ∪ cfalse (Sentence.bf .e) ∪ single (Term.box P.Actuality.quoted) ∪
      cfalse P.AtomicityT.quoted) :=
  Consistent.of_model _ (model_isModel mono01)
    (holdsAx_union _ (holdsAx_union _ (holdsAx_union _
      (holdsAx_common _ PointedParts.Mono01.not_bc)
      (holdsAx_cfalse _ (bf_pure .e) PointedParts.Mono01.not_bf_e fun k => bf_pt _ k .e))
      (holdsAx_nec _ actuality_pure PointedParts.Mono01.actuality fun k => actuality_pt _ k))
      (holdsAx_cfalse _ atomicityT_pure PointedParts.Mono01.not_atomicityT fun k => atomicityT_pt _ k))

/-- Part 5⁺, the surjective ones among those. -/
theorem part5_consistent :
    Consistent (common ∪ AxiomSet.box P.Barcan.schema ∪ single (Term.box P.Actuality.quoted) ∪
      cfalse P.AtomicityT.quoted) :=
  Consistent.of_model _ (model_isModel monoSurj01)
    (holdsAx_union _ (holdsAx_union _ (holdsAx_union _
      (holdsAx_common _ PointedParts.MonoSurj01.not_bc)
      (holdsAx_box_bf _ PointedParts.MonoSurj01.bf))
      (holdsAx_nec _ actuality_pure PointedParts.MonoSurj01.actuality fun k => actuality_pt _ k))
      (holdsAx_cfalse _ atomicityT_pure PointedParts.MonoSurj01.not_atomicityT fun k => atomicityT_pt _ k))

/-- Part 6⁺, the identity and the truncations. -/
theorem part6_consistent :
    Consistent (common ∪ cfalse (Sentence.bf .e) ∪ cfalse P.Actuality.quoted ∪
      single (Term.box P.AtomicityT.quoted)) :=
  Consistent.of_model _ (model_isModel truncs)
    (holdsAx_union _ (holdsAx_union _ (holdsAx_union _
      (holdsAx_common _ PointedParts.Truncs.not_bc)
      (holdsAx_cfalse _ (bf_pure .e) PointedParts.Truncs.not_bf_e fun k => bf_pt _ k .e))
      (holdsAx_cfalse _ actuality_pure PointedParts.Truncs.not_actuality fun k => actuality_pt _ k))
      (holdsAx_nec _ atomicityT_pure PointedParts.Truncs.atomicityT fun k => atomicityT_pt _ k))

/-- Part 7⁺, the roundings. -/
theorem part7_consistent :
    Consistent (common ∪ cfalse (Sentence.bf .e) ∪ single (Term.box P.Actuality.quoted) ∪
      single (Term.box P.AtomicityT.quoted)) :=
  Consistent.of_model _ (model_isModel pow2)
    (holdsAx_union _ (holdsAx_union _ (holdsAx_union _
      (holdsAx_common _ PointedParts.Pow2.not_bc)
      (holdsAx_cfalse _ (bf_pure .e) PointedParts.Pow2.not_bf_e fun k => bf_pt _ k .e))
      (holdsAx_nec _ actuality_pure PointedParts.Pow2.actuality fun k => actuality_pt _ k))
      (holdsAx_nec _ atomicityT_pure PointedParts.Pow2.atomicityT fun k => atomicityT_pt _ k))

/-- Part 8⁺, the shifts. -/
theorem part8_consistent :
    Consistent (common ∪ AxiomSet.box P.Barcan.schema ∪ single (Term.box P.Actuality.quoted) ∪
      single (Term.box P.AtomicityT.quoted)) :=
  Consistent.of_model _ (model_isModel shifts)
    (holdsAx_union _ (holdsAx_union _ (holdsAx_union _
      (holdsAx_common _ PointedParts.Shifts.not_bc)
      (holdsAx_box_bf _ PointedParts.Shifts.bf))
      (holdsAx_nec _ actuality_pure PointedParts.Shifts.actuality fun k => actuality_pt _ k))
      (holdsAx_nec _ atomicityT_pure PointedParts.Shifts.atomicityT fun k => atomicityT_pt _ k))

/-- **The paper's claim**, `◇(□ND ∧ Atomicity)`, with No Pure Contingency false: in any
of the models, `¬ND_e` is true and possibly false. Stated from Part 1⁺, where moreover
`□ND` fails and Atomicity is false. -/
theorem dia_box_nd_atomicity_consistent :
    Consistent (single (Term.dia (Term.conj (Term.box (Sentence.nd .e)) P.AtomicityT.quoted)) ∪
      single (Term.neg P.AtomicityT.quoted) ∪ single (Term.neg (Sentence.nd .e))) :=
  Consistent.mono (fun a ha => by
      rcases ha with (h | h) | h
      · exact Or.inl (Or.inl (Or.inl (Or.inr h)))
      · exact Or.inr (Or.inl h)
      · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))))
    part1_consistent

end Classicism.Meta.ConsistencyPointed
