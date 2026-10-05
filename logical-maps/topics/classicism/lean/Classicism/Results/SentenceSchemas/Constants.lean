import Classicism.Results.SentenceSchemas.WitnessedPossibility
import Classicism.Syntax.Inhabited
import Classicism.Syntax.Conservativity

/-!
# What a constant of the signature excludes

The map's incompatibilities that need a constant `c` of the signature of a relational type
`ρ`, which the Background's standing assumption supplies (`Signature.Admitted`):

- `witnessed-possibility-incompatible-with-nd`,
  `no-contingency-signature-incompatible-with-witnessed-possibility`,
  `signature-b-and-witnessed-possibility-incompatible`: Witnessed Possibility at the pure
  formulas `x = ⊤_ρ` and `x ≠ ⊤_ρ`, whose existential closures `C` proves (witnessed by
  `⊤_ρ` and `⊥_ρ`, `C.topR_ne_botR`), gives `◇(c = ⊤_ρ)` and `◇(c ≠ ⊤_ρ)`; ND at `ρ`, No
  Contingency, or B at `c ≠ ⊤_ρ` then makes one of them impossible.
- `separated-structure-incompatible-with-nd`: Separated Structure at `λx. x` and
  `λx. ⊤_ρ` gives `c ≠ ⊤_ρ`; ND makes it necessary, `(c ≠ ⊤_ρ) = ⊤`; Separated Structure
  at `λx. x ≠ ⊤_ρ` and `λx. ⊤` then identifies them, and at `⊤_ρ` that is `⊥ = ⊤`.

Each object-level argument is a shallow lemma at a relational type, certified once and
instantiated at `c`, read at the type `ρ` through the equation `typeOf c = ρ`
(`Term.castTy`). The pure formulas are put at the constant's type through the same
equation; the lemmas `cast_*` carry the casts out.
-/

namespace Classicism

section shallow

variable {τ : Type} [Rel τ]

/-- Witnessed Possibility at `x = ⊤` and `x ≠ ⊤`, with ND at the type: contradictory. -/
theorem wp_nd_contra (x : τ)
    (h₁ : (∃ y : τ, y = Rel.top τ) → ◇ (x = Rel.top τ))
    (h₂ : (∃ y : τ, ¬ y = Rel.top τ) → ◇ (¬ x = Rel.top τ))
    (htb : ¬ Rel.top τ = Rel.bot τ) (nd : ¬ x = Rel.top τ → □ (¬ x = Rel.top τ)) : False :=
  (em (x = Rel.top τ)).elim
    (fun hx => not_dia_of_box_not (¬ x = Rel.top τ)
      (modal_K _ _ (nec% (fun (h : x = Rel.top τ) (hn : ¬ x = Rel.top τ) => hn h))
        (necessity_of_identity x _ hx))
      (h₂ ⟨Rel.bot τ, fun e => htb e.symm⟩))
    (fun hx => not_dia_of_box_not (x = Rel.top τ) (nd hx) (h₁ ⟨Rel.top τ, rfl⟩))

/-- Witnessed Possibility at `x = ⊤` and `x ≠ ⊤`, with No Contingency at both. -/
theorem nc_wp_contra (x : τ)
    (h₁ : (∃ y : τ, y = Rel.top τ) → ◇ (x = Rel.top τ))
    (h₂ : (∃ y : τ, ¬ y = Rel.top τ) → ◇ (¬ x = Rel.top τ))
    (htb : ¬ Rel.top τ = Rel.bot τ)
    (n₁ : x = Rel.top τ → □ (x = Rel.top τ)) (n₂ : ¬ x = Rel.top τ → □ (¬ x = Rel.top τ)) : False :=
  (em (x = Rel.top τ)).elim
    (fun hx => not_dia_of_box_not (¬ x = Rel.top τ)
      (modal_K _ _ (nec% (fun (h : x = Rel.top τ) (hn : ¬ x = Rel.top τ) => hn h)) (n₁ hx))
      (h₂ ⟨Rel.bot τ, fun e => htb e.symm⟩))
    (fun hx => not_dia_of_box_not (x = Rel.top τ) (n₂ hx) (h₁ ⟨Rel.top τ, rfl⟩))

/-- Where `x = ⊤`, `x ≠ ⊤` is not possible: NI. -/
theorem eq_top_not_dia_ne (x : τ) : x = Rel.top τ → ¬ ◇ (¬ x = Rel.top τ) := fun h =>
  not_dia_of_box_not (¬ x = Rel.top τ)
    (modal_K _ _ (nec% (fun (h' : x = Rel.top τ) (hn : ¬ x = Rel.top τ) => hn h'))
      (necessity_of_identity x _ h))

/-- Witnessed Possibility at `x = ⊤` and `x ≠ ⊤`, with B at `x ≠ ⊤`: where `x = ⊤` is
possible, there `x = ⊤` is necessary, by NI, against the necessary possibility of
`x ≠ ⊤`. -/
theorem b_wp_contra (x : τ)
    (h₁ : (∃ y : τ, y = Rel.top τ) → ◇ (x = Rel.top τ))
    (h₂ : (∃ y : τ, ¬ y = Rel.top τ) → ◇ (¬ x = Rel.top τ))
    (htb : ¬ Rel.top τ = Rel.bot τ) (b : ¬ x = Rel.top τ → □ ◇ (¬ x = Rel.top τ)) : False :=
  (em (x = Rel.top τ)).elim
    (fun hx => not_dia_of_box_not (¬ x = Rel.top τ)
      (modal_K _ _ (nec% (fun (h : x = Rel.top τ) (hn : ¬ x = Rel.top τ) => hn h))
        (necessity_of_identity x _ hx))
      (h₂ ⟨Rel.bot τ, fun e => htb e.symm⟩))
    (fun hx => not_dia_of_box_not (x = Rel.top τ ∧ ◇ (¬ x = Rel.top τ))
      (nec% (fun (h : x = Rel.top τ ∧ ◇ (¬ x = Rel.top τ)) => eq_top_not_dia_ne x h.1 h.2))
      (dia_and_of_dia_box _ _ (h₁ ⟨Rel.top τ, rfl⟩) (b hx)))

/-- Separated Structure at `λy. y`, `λy. ⊤` and at `λy. y ≠ ⊤`, `λy. ⊤`, with ND at the
type: contradictory. -/
theorem ss_nd_contra (x : τ)
    (s₁ : (λ y : τ ↦ y) x = (λ _ : τ ↦ Rel.top τ) x →
      (λ y : τ ↦ y) = (λ _ : τ ↦ Rel.top τ))
    (s₂ : (λ y : τ ↦ ¬ y = Rel.top τ) x = (λ _ : τ ↦ True) x →
      (λ y : τ ↦ ¬ y = Rel.top τ) = (λ _ : τ ↦ True))
    (htb : ¬ Rel.top τ = Rel.bot τ) (nd : ¬ x = Rel.top τ → □ (¬ x = Rel.top τ)) : False :=
  (em (x = Rel.top τ)).elim
    (fun hx => htb (congrFun (s₁ hx) (Rel.bot τ)).symm)
    (fun hx => (congrFun (s₂ (nd hx)) (Rel.top τ)) ▸ trivial |> fun h => h rfl)

end shallow

#classicism_derive Classicism.wp_nd_contra Classicism.nc_wp_contra Classicism.eq_top_not_dia_ne
  Classicism.b_wp_contra
  Classicism.ss_nd_contra

namespace Meta

open AxiomSet

variable {Sig : Signature}

/-- An admitted signature has a constant of a closed relational type. -/
theorem Signature.Admitted.exists_rel (hS : Sig.Admitted) :
    ∃ (c : Sig.Const) (ρ : RTy), Sig.typeOf c = Ty.rel ρ ∧ ρ.Closed := by
  obtain ⟨c, hc⟩ := hS.2
  match h : Sig.typeOf c, hc, hS.1 c with
  | .e, hc, _ => exact absurd rfl hc
  | .rel ρ, _, hcl => exact ⟨c, ρ, h, hcl⟩
  | .var i, _, hcl => exact absurd hcl (Ty.not_closed_var i)

/-! The casts along `typeOf c = ρ`, carried out. Each is by `subst` on an equation between
types, stated for any term in place of the constant. -/

theorem cast_existsBlock {τ τ' : Ty} (h : τ = τ') (P₀ : Formula Signature.pure [τ']) :
    Term.ofPure (Sig := Sig) (Term.existsBlock [τ] (h.symm ▸ P₀)) = Term.exists' (Term.ofPure P₀) := by
  subst h; rfl

theorem cast_subst {τ τ' : Ty} (h : τ = τ') (P₀ : Formula Signature.pure [τ']) (a : Term Sig [] τ) :
    (Term.ofPure (h.symm ▸ P₀)).subst (Sub.cons a Sub.id) =
      (Term.ofPure P₀).subst (Sub.cons (h ▸ a) Sub.id) := by
  subst h; rfl

theorem cast_app {τ τ' : Ty} {ρ : RTy} (h : τ = τ') (F : Term Sig [] (τ' ⇒ ρ)) (a : Term Sig [] τ) :
    Term.app (h.symm ▸ F : Term Sig [] (τ ⇒ ρ)) a = Term.app F (h ▸ a) := by
  subst h; rfl

theorem cast_eq' {τ τ' : Ty} {ρ : RTy} (h : τ = τ') (F G : Term Sig [] (τ' ⇒ ρ)) :
    Term.eq' (h.symm ▸ F : Term Sig [] (τ ⇒ ρ)) (h.symm ▸ G) = Term.eq' F G := by
  subst h; rfl

theorem cast_consts {τ τ' : Ty} {ρ : RTy} (h : τ = τ') (F : Term Sig [] (τ' ⇒ ρ)) :
    (h.symm ▸ F : Term Sig [] (τ ⇒ ρ)).consts = F.consts := by
  subst h; rfl

theorem cast_closedTypes_ctx {τ τ' : Ty} (h : τ = τ') (P₀ : Formula Signature.pure [τ']) :
    (h.symm ▸ P₀ : Formula Signature.pure [τ]).closedTypes = P₀.closedTypes := by
  subst h; rfl

theorem cast_closedTypes_fun {τ τ' : Ty} {ρ : RTy} (h : τ = τ') (F : Term Sig [] (τ' ⇒ ρ)) :
    (h.symm ▸ F : Term Sig [] (τ ⇒ ρ)).closedTypes = F.closedTypes := by
  subst h; rfl

theorem cast_closedTypes_const {Γ : Ctx} (c : Sig.Const) {τ : Ty} (h : Sig.typeOf c = τ) :
    (h ▸ Term.const c : Term Sig Γ τ).closedTypes = decide τ.Closed := by
  subst h; rfl

/-- The instance of Witnessed Possibility at the constant `c`, with the pure formula
`P₀` read at its type: `(∃x. P₀) → ◇P₀[c]`. -/
theorem witnessedPossibility_at {c : Sig.Const} {ρ : RTy} (h : Sig.typeOf c = Ty.rel ρ)
    (hρ : ρ.Closed) (P₀ : Formula Signature.pure [Ty.rel ρ]) (hP : P₀.closedTypes = true)
    {Ax : AxiomSet Sig} (hW : witnessedPossibility Sig ⊆ Ax) :
    Theorem (C.axioms ∪ Ax) (Term.imp (Term.exists' (Term.ofPure P₀))
      (Term.dia ((Term.ofPure P₀).subst (Sub.cons (h ▸ Term.const c) Sub.id)))) := by
  have w := Theorem.ax (Ax := Ax)
    (a := Term.imp (Term.ofPure (Term.existsBlock [Sig.typeOf c] (h.symm ▸ P₀)))
      (Term.dia ((Term.ofPure (h.symm ▸ P₀)).subst (Sub.cons (Term.const c) Sub.id))))
    (hW _ (witnessedPossibility_mem (cs := [c]) (P := (h.symm ▸ P₀ : Formula Signature.pure [Sig.typeOf c]))
      (List.nodup_singleton c) (by
        have hc : (Sig.typeOf c).Closed := h ▸ hρ
        show (Term.exists' (h.symm ▸ P₀ : Formula Signature.pure [Sig.typeOf c])).closedTypes = true
        rw [Term.closedTypes_exists', cast_closedTypes_ctx h P₀, hP]
        simp [hc])))
  rwa [cast_existsBlock h, cast_subst h] at w

/-- The instance of ND at the closed relational type `ρ`, at `x` and `⊤_ρ`. -/
theorem nd_at {ρ : RTy} (hρ : ρ.Closed) {Ax : AxiomSet Sig}
    (hN : AxiomSet.ofPure P.NecessityOfDistinctness.schema ⊆ Ax) (x : Term Sig [] (Ty.rel ρ)) :
    Theorem (C.axioms ∪ Ax) (Term.imp (Term.neg (Term.eq' x (Term.topR ρ)))
      (Term.box (Term.neg (Term.eq' x (Term.topR ρ))))) :=
  Derivable.allE₂β (Theorem.ax (Ax := Ax) (hN _ ⟨_, ⟨Ty.rel ρ, hρ, rfl⟩, rfl⟩)) x (Term.topR ρ)

/-- `witnessed-possibility-incompatible-with-nd`. -/
theorem witnessedPossibility_nd_inconsistent (hS : Sig.Admitted) :
    ¬ Consistent (witnessedPossibility Sig ∪ AxiomSet.ofPure P.NecessityOfDistinctness.schema) :=
  fun hcons => hcons <| by
  obtain ⟨c, ρ, h, hρ⟩ := hS.exists_rel
  let P₁ : Formula Signature.pure [Ty.rel ρ] := Term.eq' (Term.var .zero) (Term.topR ρ)
  let X := witnessedPossibility Sig ∪ AxiomSet.ofPure P.NecessityOfDistinctness.schema
  have w₁ := witnessedPossibility_at h hρ P₁ (by simp [P₁, Term.closedTypes, hρ]) (Ax := X) (subset_union_left _ _)
  have w₂ := witnessedPossibility_at h hρ (Term.neg P₁) (by simp [P₁, Term.closedTypes, hρ]) (Ax := X) (subset_union_left _ _)
  have k := Theorem.mp (Theorem.mp (Theorem.mp (Derivable.allEβ
    (Theorem.ofCMinus (C.TheoremMinus.ofPure (wp_nd_contra.derivable ρ)))
      (h ▸ Term.const c : Term Sig [] (Ty.rel ρ))) w₁) w₂)
    (Theorem.ofC (C.topR_ne_botR ρ hρ))
  exact Derivable.notE (nd_at hρ (Ax := X) (subset_union_right _ _) _) k

/-- `no-contingency-signature-incompatible-with-witnessed-possibility`. -/
theorem noContingency_witnessedPossibility_inconsistent (hS : Sig.Admitted) :
    ¬ Consistent (noContingency Sig ∪ witnessedPossibility Sig) := fun hcons => hcons <| by
  obtain ⟨c, ρ, h, hρ⟩ := hS.exists_rel
  let X := noContingency Sig ∪ witnessedPossibility Sig
  let P₁ : Formula Signature.pure [Ty.rel ρ] := Term.eq' (Term.var .zero) (Term.topR ρ)
  let cR : Term Sig [] (Ty.rel ρ) := h ▸ Term.const c
  have w₁ := witnessedPossibility_at h hρ P₁ (by simp [P₁, Term.closedTypes, hρ]) (Ax := X) (subset_union_right _ _)
  have w₂ := witnessedPossibility_at h hρ (Term.neg P₁) (by simp [P₁, Term.closedTypes, hρ]) (Ax := X) (subset_union_right _ _)
  have n₁ : Theorem (C.axioms ∪ X)
      (Term.imp (Term.eq' cR (Term.topR ρ)) (Term.box (Term.eq' cR (Term.topR ρ)))) :=
    Theorem.ax (Or.inl (noContingency_mem (by simp [cR, cast_closedTypes_const, Term.closedTypes, hρ])))
  have n₂ : Theorem (C.axioms ∪ X) (Term.imp (Term.neg (Term.eq' cR (Term.topR ρ)))
      (Term.box (Term.neg (Term.eq' cR (Term.topR ρ))))) :=
    Theorem.ax (Or.inl (noContingency_mem (by simp [cR, cast_closedTypes_const, Term.closedTypes, hρ])))
  have k := Theorem.mp (Theorem.mp (Theorem.mp (Theorem.mp (Derivable.allEβ
    (Theorem.ofCMinus (C.TheoremMinus.ofPure (nc_wp_contra.derivable ρ))) cR) w₁) w₂)
    (Theorem.ofC (C.topR_ne_botR ρ hρ))) n₁
  exact Derivable.notE n₂ k

/-- `signature-b-and-witnessed-possibility-incompatible`. -/
theorem signatureB_witnessedPossibility_inconsistent (hS : Sig.Admitted) :
    ¬ Consistent (signatureB Sig ∪ witnessedPossibility Sig) := fun hcons => hcons <| by
  obtain ⟨c, ρ, h, hρ⟩ := hS.exists_rel
  let X := signatureB Sig ∪ witnessedPossibility Sig
  let P₁ : Formula Signature.pure [Ty.rel ρ] := Term.eq' (Term.var .zero) (Term.topR ρ)
  let cR : Term Sig [] (Ty.rel ρ) := h ▸ Term.const c
  have w₁ := witnessedPossibility_at h hρ P₁ (by simp [P₁, Term.closedTypes, hρ]) (Ax := X) (subset_union_right _ _)
  have w₂ := witnessedPossibility_at h hρ (Term.neg P₁) (by simp [P₁, Term.closedTypes, hρ]) (Ax := X) (subset_union_right _ _)
  have b : Theorem (C.axioms ∪ X) (Term.imp (Term.neg (Term.eq' cR (Term.topR ρ)))
      (Term.box (Term.dia (Term.neg (Term.eq' cR (Term.topR ρ)))))) :=
    Theorem.ax (Or.inl (signatureB_mem (by simp [cR, cast_closedTypes_const, Term.closedTypes, hρ])))
  have k := Theorem.mp (Theorem.mp (Theorem.mp (Derivable.allEβ
    (Theorem.ofCMinus (C.TheoremMinus.ofPure (b_wp_contra.derivable ρ))) cR) w₁) w₂)
    (Theorem.ofC (C.topR_ne_botR ρ hρ))
  exact Derivable.notE b k

/-- The instance of Separated Structure at the constant `c`, with closed terms `F₀`, `G₀`
of the type `ρ → ρ'` read at the constant's type. -/
theorem separatedStructure_at {c : Sig.Const} {ρ : RTy} (h : Sig.typeOf c = Ty.rel ρ) {ρ' : RTy}
    (F₀ G₀ : Term Sig [] (Ty.rel ρ ⇒ ρ')) (hF : c ∉ F₀.consts) (hG : c ∉ G₀.consts)
    (hFc : F₀.closedTypes = true) (hGc : G₀.closedTypes = true)
    {Ax : AxiomSet Sig} (hW : separatedStructure Sig ⊆ Ax) :
    Theorem (C.axioms ∪ Ax) (Term.imp
      (Term.eq' (Term.app F₀ (h ▸ Term.const c)) (Term.app G₀ (h ▸ Term.const c))) (Term.eq' F₀ G₀)) := by
  have w := Theorem.ax (Ax := Ax)
    (a := Term.imp (Term.eq' (Term.app (h.symm ▸ F₀ : Term Sig [] (Sig.typeOf c ⇒ ρ')) (Term.const c))
        (Term.app (h.symm ▸ G₀ : Term Sig [] (Sig.typeOf c ⇒ ρ')) (Term.const c)))
      (Term.eq' (h.symm ▸ F₀ : Term Sig [] (Sig.typeOf c ⇒ ρ')) (h.symm ▸ G₀)))
    (hW _ ⟨by
        have hc : (Sig.typeOf c).Closed := by
          have := Term.closed_of_closedTypes hFc; rw [h]; exact this.1
        have hρ' : ρ'.Closed := (Term.closed_of_closedTypes hFc).2
        show (Term.imp (Term.eq' (Term.app (h.symm ▸ F₀ : Term Sig [] (Sig.typeOf c ⇒ ρ')) (Term.const c))
            (Term.app (h.symm ▸ G₀ : Term Sig [] (Sig.typeOf c ⇒ ρ')) (Term.const c)))
          (Term.eq' (h.symm ▸ F₀ : Term Sig [] (Sig.typeOf c ⇒ ρ')) (h.symm ▸ G₀))).closedTypes = true
        simp only [Term.closedTypes_eq', Term.closedTypes]
        rw [cast_closedTypes_fun h F₀, cast_closedTypes_fun h G₀]
        simp [hFc, hGc, hc, hρ'],
      c, ρ', _, _, by rw [cast_consts h]; exact hF, by rw [cast_consts h]; exact hG, rfl⟩)
  rwa [cast_app h, cast_app h, cast_eq' h] at w

/-- `separated-structure-incompatible-with-nd`. -/
theorem separatedStructure_nd_inconsistent (hS : Sig.Admitted) :
    ¬ Consistent (separatedStructure Sig ∪ AxiomSet.ofPure P.NecessityOfDistinctness.schema) :=
  fun hcons => hcons <| by
  obtain ⟨c, ρ, h, hρ⟩ := hS.exists_rel
  let X := separatedStructure Sig ∪ AxiomSet.ofPure P.NecessityOfDistinctness.schema
  let cR : Term Sig [] (Ty.rel ρ) := h ▸ Term.const c
  have s₁ := separatedStructure_at h (Ax := X) (Term.lam (Term.var .zero)) (Term.lam (Term.topR ρ))
    (by simp [Term.consts]) (by simp [Term.consts]) (by simp [Term.closedTypes, hρ])
    (by simp [Term.closedTypes, hρ]) (subset_union_left _ _)
  have s₂ := separatedStructure_at h (Ax := X)
    (Term.lam (Term.neg (Term.eq' (Term.var .zero) (Term.topR ρ)))) (Term.lam Term.top)
    (by simp [Term.consts]) (by simp [Term.consts]) (by simp [Term.closedTypes, hρ])
    (by simp [Term.closedTypes, hρ]) (subset_union_left _ _)
  have s₂' : Theorem (C.axioms ∪ X) (Term.imp (Term.eq' (Term.neg (Term.eq' cR (Term.topR ρ))) Term.top)
      (Term.eq' (Term.lam (Term.neg (Term.eq' (Term.var .zero) (Term.topR ρ)))) (Term.lam Term.top))) :=
    Derivable.conv s₂ (Conv.app_congr (Conv.app_congr (Conv.refl _) (Conv.app_congr (Conv.refl _)
      (Conv.app_congr (Conv.app_congr (Conv.refl _) (Conv.beta _ _)) (Conv.beta _ _)))) (Conv.refl _))
  have k := Theorem.mp (Theorem.mp (Theorem.mp (Derivable.allEβ
    (Theorem.ofCMinus (C.TheoremMinus.ofPure (ss_nd_contra.derivable ρ))) cR) s₁) s₂')
    (Theorem.ofC (C.topR_ne_botR ρ hρ))
  exact Derivable.notE (nd_at hρ (Ax := X) (subset_union_right _ _) _) k

end Meta

end Classicism
