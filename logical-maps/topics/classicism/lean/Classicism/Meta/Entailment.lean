import Classicism.Meta.Axioms

/-!
# Entailment between axiom sets

The map's arrows are facts of the form "this schema entails that schema": a relation
between *axiom sets*, each element of the second derivable from the first together with
Classicism. This module defines it and proves its algebra: reflexivity, transitivity (a
cut lemma, replacing axioms by their derivations), monotonicity, unions, and how a family
of implications `∀ σ. P σ → Q σ` proved in `C` gives `{P σ} ⟹ {Q σ}`; and consistency of
an axiom set with `C`. The schemas over the syntax that use these — Distinctness,
Possibility, maximalization — are in `SyntaxSchemas.lean`.

Semantics — that entailment transfers holding, in `Prop` and in an action model — is in
`Denotation.lean` and `ActionSoundness.lean`, with the soundness theorems it rests on.
-/

namespace Classicism.Meta

universe u v w

variable {Sig : Signature}

/-! ### Axiom sets -/

namespace AxiomSet

/-- The empty set. -/
def empty : AxiomSet Sig := fun _ => False

/-- One sentence. -/
def single (a : Sentence Sig) : AxiomSet Sig := fun b => b = a

/-- Union. -/
protected def union (Ax₁ Ax₂ : AxiomSet Sig) : AxiomSet Sig := fun a => Ax₁ a ∨ Ax₂ a

instance : Union (AxiomSet Sig) := ⟨AxiomSet.union⟩

/-- Inclusion. -/
protected def Subset (Ax₁ Ax₂ : AxiomSet Sig) : Prop := ∀ a, Ax₁ a → Ax₂ a

instance : HasSubset (AxiomSet Sig) := ⟨AxiomSet.Subset⟩

/-- The instances of a schema: the sentences `P i` for `i` ranging over the schema's
parameters (its object types, typically). -/
def ofFamily {ι : Sort u} (P : ι → Sentence Sig) : AxiomSet Sig := fun a => ∃ i, a = P i

theorem mem_union_left {Ax₁ Ax₂ : AxiomSet Sig} {a : Sentence Sig} (h : Ax₁ a) : (Ax₁ ∪ Ax₂) a :=
  Or.inl h
theorem mem_union_right {Ax₁ Ax₂ : AxiomSet Sig} {a : Sentence Sig} (h : Ax₂ a) : (Ax₁ ∪ Ax₂) a :=
  Or.inr h
theorem subset_union_left (Ax₁ Ax₂ : AxiomSet Sig) : Ax₁ ⊆ Ax₁ ∪ Ax₂ := fun _ => Or.inl
theorem subset_union_right (Ax₁ Ax₂ : AxiomSet Sig) : Ax₂ ⊆ Ax₁ ∪ Ax₂ := fun _ => Or.inr
theorem mem_ofFamily {ι : Sort u} (P : ι → Sentence Sig) (i : ι) : ofFamily P (P i) := ⟨i, rfl⟩

end AxiomSet

/-! ### Replacing axioms by their derivations -/

namespace Derivable

variable {Ax : AxiomSet Sig}

/-- A derivation from axioms each of which is a theorem of another set is a derivation
from that set: `mono`, with derivations in place of axioms. The closed derivation of an
axiom is renamed into the context and weakened. -/
theorem replaceAx {Ax' : AxiomSet Sig} (hA : ∀ a, Ax a → Theorem Ax' a) :
    ∀ {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ},
      Derivable Ax Δ p → Derivable Ax' Δ p
  | _, _, _, hyp h => hyp h
  | Γ, _, _, ax (a := a) h =>
    weaken (rename (Ren.ofEmpty (Γ := Γ)) (hA a h)) (List.nil_subset _)
  | _, _, _, andI h₁ h₂ => andI (replaceAx hA h₁) (replaceAx hA h₂)
  | _, _, _, andE₁ h => andE₁ (replaceAx hA h)
  | _, _, _, andE₂ h => andE₂ (replaceAx hA h)
  | _, _, _, orI₁ h => orI₁ (replaceAx hA h)
  | _, _, _, orI₂ h => orI₂ (replaceAx hA h)
  | _, _, _, orE h h₁ h₂ => orE (replaceAx hA h) (replaceAx hA h₁) (replaceAx hA h₂)
  | _, _, _, notI h₁ h₂ => notI (replaceAx hA h₁) (replaceAx hA h₂)
  | _, _, _, notE h₁ h₂ => notE (replaceAx hA h₁) (replaceAx hA h₂)
  | _, _, _, em p => em p
  | _, _, _, allE h a => allE (replaceAx hA h) a
  | _, _, _, allI h => allI (replaceAx hA h)
  | _, _, _, exI a h => exI a (replaceAx hA h)
  | _, _, _, exE h h' => exE (replaceAx hA h) (replaceAx hA h')
  | _, _, _, refl a => refl a
  | _, _, _, subst F h₁ h₂ => subst F (replaceAx hA h₁) (replaceAx hA h₂)
  | _, _, _, conv h c => conv (replaceAx hA h) c
/-- Cut for axiom sets: if every sentence of `Ax'` is a theorem of `Ax ∪ Ax₁`, a derivation
from `Ax ∪ Ax'` is one from `Ax ∪ Ax₁`. -/
theorem cut {Ax₁ Ax' : AxiomSet Sig} (hA : ∀ a, Ax' a → Theorem (Ax ∪ Ax₁) a)
    {Γ : Ctx} {Δ : List (Formula Sig Γ)} {p : Formula Sig Γ} (h : Derivable (Ax ∪ Ax') Δ p) :
    Derivable (Ax ∪ Ax₁) Δ p :=
  replaceAx (fun a ha => ha.elim (fun h => Derivable.axiom (Or.inl h)) (hA a)) h

end Derivable

/-! ### Entailment -/

namespace AxiomSet

/-- **Entailment relative to Classicism**: every sentence of `Ax₂` is a theorem of `C`
together with `Ax₁`. The map's arrows. -/
def Entails (Ax₁ Ax₂ : AxiomSet Sig) : Prop := ∀ a, Ax₂ a → Theorem (C.axioms ∪ Ax₁) a

@[inherit_doc] infix:50 " ⟹ " => Entails

namespace Entails

variable {Ax₁ Ax₂ Ax₃ : AxiomSet Sig}

theorem of_subset (h : Ax₂ ⊆ Ax₁) : Ax₁ ⟹ Ax₂ :=
  fun a ha => Derivable.axiom (Or.inr (h a ha))

theorem refl (Ax : AxiomSet Sig) : Ax ⟹ Ax := of_subset fun _ h => h

theorem trans (h₁ : Ax₁ ⟹ Ax₂) (h₂ : Ax₂ ⟹ Ax₃) : Ax₁ ⟹ Ax₃ :=
  fun a ha => Derivable.cut h₁ (h₂ a ha)

theorem mono_left (h : Ax₁ ⊆ Ax₂) (e : Ax₁ ⟹ Ax₃) : Ax₂ ⟹ Ax₃ :=
  fun a ha => Derivable.mono (fun b hb => hb.elim Or.inl (fun hb => Or.inr (h b hb))) (e a ha)

theorem mono_right (h : Ax₃ ⊆ Ax₂) (e : Ax₁ ⟹ Ax₂) : Ax₁ ⟹ Ax₃ :=
  fun a ha => e a (h a ha)

theorem union (h₁ : Ax₁ ⟹ Ax₂) (h₂ : Ax₁ ⟹ Ax₃) : Ax₁ ⟹ Ax₂ ∪ Ax₃ :=
  fun a ha => ha.elim (h₁ a) (h₂ a)

theorem union_left (Ax₁ Ax₂ : AxiomSet Sig) : Ax₁ ∪ Ax₂ ⟹ Ax₁ := of_subset (subset_union_left _ _)
theorem union_right (Ax₁ Ax₂ : AxiomSet Sig) : Ax₁ ∪ Ax₂ ⟹ Ax₂ := of_subset (subset_union_right _ _)

/-- Classicism alone entails what it proves. -/
theorem of_theorem {a : Sentence Sig} (h : C.Theorem a) : (empty : AxiomSet Sig) ⟹ single a :=
  fun _ hb => hb ▸ Derivable.mono (fun _ => Or.inl) h

/-- A family of implications `P (f k) → Q k` proved in `C` entails the schema `Q` from the
schema `P`: the form of the map's arrows between type-indexed principles. -/
theorem of_imp_family {ι : Sort u} {κ : Sort v} (P : ι → Sentence Sig) (Q : κ → Sentence Sig) (f : κ → ι)
    (h : ∀ k, C.Theorem (Term.imp (P (f k)) (Q k))) : ofFamily P ⟹ ofFamily Q := by
  rintro a ⟨k, rfl⟩
  exact Derivable.impE (Derivable.mono (fun _ => Or.inl) (h k)) (Derivable.axiom (Or.inr ⟨f k, rfl⟩))

/-- Two premises. -/
theorem of_imp_family₂ {ι₁ : Sort u} {ι₂ : Sort v} {κ : Sort w} (P₁ : ι₁ → Sentence Sig) (P₂ : ι₂ → Sentence Sig)
    (Q : κ → Sentence Sig) (f₁ : κ → ι₁) (f₂ : κ → ι₂)
    (h : ∀ k, C.Theorem (Term.imp (P₁ (f₁ k)) (Term.imp (P₂ (f₂ k)) (Q k)))) :
    ofFamily P₁ ∪ ofFamily P₂ ⟹ ofFamily Q := by
  rintro a ⟨k, rfl⟩
  exact Derivable.impE
    (Derivable.impE (Derivable.mono (fun _ => Or.inl) (h k))
      (Derivable.axiom (Or.inr (Or.inl ⟨f₁ k, rfl⟩))))
    (Derivable.axiom (Or.inr (Or.inr ⟨f₂ k, rfl⟩)))

end Entails

/-! ### Consistency -/

/-- `Ax` is consistent (with Classicism): `⊥` is not a theorem of `C ∪ Ax`. -/
def Consistent (Ax : AxiomSet Sig) : Prop := ¬ Theorem (C.axioms ∪ Ax) Term.bot

end AxiomSet

end Classicism.Meta
