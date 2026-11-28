import Classicism.Coalesced.StonePossibilismTerms
import Classicism.Coalesced.StoneCardinal

/-! Current semantics of typed injections and represented powers at a point
admitting all current unary and binary relation rows. -/

namespace Classicism.Meta.Coalesced.StoneFan.PowerClosed

open CategoryTheory Classicism.Meta.Intensional Ordinals
open scoped Cardinal

noncomputable section

local instance nativeTyStonePowerClosed (α : Type) : _root_.Classicism.Ty α := ⟨()⟩

abbrev unaryBody {Sig : Signature} {Γ : Ctx} {σ : Ty} {ρ : RTy} :
    Term Sig Γ (.rel (.arr σ ρ)) → Term Sig (σ :: Γ) (.rel ρ)
  | .lam t => t
  | _ => Term.botR ρ

variable {Sig : Signature} {K : Type} [SmallCategory K] (B : Premodel Sig K)
  (M : B.IsModel) {W : K} (h : B.W₀ ⟶ W)

def CurrentFull : Prop :=
  ∀ (ρ : RTy) (E : Set (Args B.inner ρ W)), ∃ R, (B.incl ρ W R).ext' B.inner = E

def trace₁ {σ : Ty} (F : B.Dom W (.rel (unary σ))) : Set (B.Dom W σ) :=
  fun a => current B F a

theorem unary_surjective (full : CurrentFull (W := W) B) (σ : Ty) :
    Function.Surjective (trace₁ (W := W) (σ := σ) B) := by
  intro E
  obtain ⟨F, hf⟩ := full (unary σ) {a | a.1 ∈ E}
  refine ⟨F, ?_⟩
  ext a
  change (a, PUnit.unit) ∈ (B.incl _ _ F).ext' B.inner ↔ _
  rw [hf]
  rfl

theorem binary_surjective (full : CurrentFull (W := W) B) (σ τ : Ty) :
    Function.Surjective (row₂ (W := W) (η := σ) (δ := τ) B) := by
  intro E
  obtain ⟨G, hg⟩ := full (.arr σ (.arr τ .t)) {a | E a.1 a.2.1}
  refine ⟨G, ?_⟩
  funext a b
  apply propext
  change (a,b,PUnit.unit) ∈ (B.incl _ _ G).ext' B.inner ↔ _
  rw [hg]
  rfl

abbrev embedsTerm {Sig : Signature} (σ τ : Ty) :
    Formula Sig [.rel (unary τ), .rel (unary σ)] :=
  unaryBody (unaryBody (Term.ofPure (Classicism.StoneMP.Embeds.term σ τ)))

include M in
private theorem embeds_iff_graph {σ τ : Ty} (P : B.Dom W (.rel (unary σ)))
    (Q : B.Dom W (.rel (unary τ))) :
    B.Holds h (embedsTerm σ τ) (.cons Q (.cons P .nil)) ↔
      ∃ F : B.Dom W (.rel (.arr σ (.arr τ .t))),
        Classicism.StoneMP.Injects (row₂ B F) (trace₁ B P) (trace₁ B Q) := by
  dsimp only [embedsTerm, Classicism.StoneMP.Embeds.term, Term.ofPure_lam, unaryBody]
  simp only [Term.ofPure_app, Term.ofPure_var, Term.ofPure_lam, Term.ofPure_and, Term.ofPure_not,
    Term.ofPure_or, Term.ofPure_all, Term.ofPure_ex, Term.ofPure_eq, B.holds_conj M,
    B.holds_forall M, B.holds_imp M, B.holds_exists M, Premodel.holds_eq_var M,
    Premodel.holds_app_var1, Premodel.holds_app_var2, IEnv.get]
  rfl

private theorem external_embeds {α β : Type} (P : Set α) (Q : Set β) :
    Classicism.StoneMP.Embeds P Q ↔ Cardinal.mk P ≤ Cardinal.mk Q := by
  rw [Cardinal.le_def]
  constructor
  · rintro ⟨F, hF, hi⟩
    choose f hmem hedge using fun x : P => hF.2.1 x.1 x.2
    refine ⟨⟨fun x => (⟨f x, hmem x⟩ : Q), ?_⟩⟩
    intro x y he
    have heq : f x = f y := congrArg Subtype.val he
    exact Subtype.ext (hi _ _ _ (hedge x) ((congrArg (F y.1) heq).mpr (hedge y)))
  · rintro ⟨f⟩
    refine ⟨fun x y => ∃ hx : x ∈ P, (f ⟨x,hx⟩).1 = y, ⟨?_, ?_, ?_⟩, ?_⟩
    · rintro x _ ⟨hx, rfl⟩
      exact ⟨hx, (f ⟨x,hx⟩).2⟩
    · intro x hx
      exact ⟨_, (f ⟨x,hx⟩).2, hx, rfl⟩
    · rintro x _ _ ⟨hx,rfl⟩ ⟨_,rfl⟩
      rfl
    · rintro x z _ ⟨hx,rfl⟩ ⟨hz,he⟩
      exact congrArg Subtype.val (f.injective (Subtype.ext he.symm))

include M

theorem holds_embeds {σ τ : Ty} (full : CurrentFull (W := W) B)
    (P : B.Dom W (.rel (unary σ))) (Q : B.Dom W (.rel (unary τ))) :
    B.Holds h (embedsTerm σ τ) (.cons Q (.cons P .nil)) ↔
      Cardinal.mk (trace₁ B P) ≤ Cardinal.mk (trace₁ B Q) := by
  rw [embeds_iff_graph B M h P Q, ← external_embeds]
  exact ((binary_surjective B full σ τ).exists
    (p := fun F => Classicism.StoneMP.Injects F (trace₁ B P) (trace₁ B Q))).symm

private def rename₂ {Γ : Ctx} {σ τ : Ty} (x : Var Γ σ) (y : Var Γ τ) : Ren [τ,σ] Γ
  | _, .zero => y
  | _, .succ .zero => x

abbrev at₂ {Γ : Ctx} {σ τ : Ty} (p : Formula Sig [τ,σ]) (x : Var Γ σ) (y : Var Γ τ) := p.rename (rename₂ x y)

omit M in
theorem holds_at₂ {Γ : Ctx} {σ τ : Ty} (p : Formula Sig [τ,σ])
    (g : IEnv (B.Dom W) Γ) (x : Var Γ σ) (y : Var Γ τ) :
    B.Holds h (at₂ p x y) g ↔ B.Holds h p (.cons (g.get y) (.cons (g.get x) .nil)) := by
  unfold at₂ Premodel.Holds
  rw [B.sem_rename]
  rfl

abbrev smallerTerm {Sig : Signature} (σ τ : Ty) : Formula Sig [.rel (unary τ), .rel (unary σ)] :=
  unaryBody (unaryBody (Term.ofPure (Classicism.StoneMP.Smaller.term σ τ)))

theorem holds_smaller {σ τ : Ty} (full : CurrentFull (W := W) B)
    (P : B.Dom W (.rel (unary σ))) (Q : B.Dom W (.rel (unary τ))) :
    B.Holds h (smallerTerm σ τ) (.cons Q (.cons P .nil)) ↔
      Cardinal.mk (trace₁ B P) < Cardinal.mk (trace₁ B Q) := by
  have eq : smallerTerm (Sig := Sig) σ τ = Term.conj
      (at₂ (embedsTerm σ τ) (.succ .zero) .zero)
      (Term.neg (at₂ (embedsTerm τ σ) .zero (.succ .zero))) := rfl
  rw [eq, B.holds_conj M, B.holds_neg M, holds_at₂, holds_at₂, holds_embeds B M h full,
    holds_embeds B M h full]
  exact lt_iff_le_not_ge.symm

abbrev powTerm {Sig : Signature} (γ α : Ty) : Formula Sig [.rel (unary α), .rel (unary γ)] :=
  unaryBody (unaryBody (Term.ofPure (Classicism.StoneMP.Pow.term α γ)))

private theorem pow_graph {γ α : Ty} (C : B.Dom W (.rel (unary γ))) (A : B.Dom W (.rel (unary α))) :
    B.Holds h (powTerm γ α) (.cons A (.cons C .nil)) ↔
      ∃ R : B.Dom W (.rel (.arr γ (.arr α .t))),
        (∀ c a, row₂ B R c a → c ∈ trace₁ B C ∧ a ∈ trace₁ B A) ∧
        (∀ c d, c ∈ trace₁ B C → d ∈ trace₁ B C → (∀ a, row₂ B R c a ↔ row₂ B R d a) → c = d) ∧
        ∀ Z : B.Dom W (.rel (unary α)), trace₁ B Z ⊆ trace₁ B A →
          ∃ c, c ∈ trace₁ B C ∧ ∀ a, row₂ B R c a ↔ a ∈ trace₁ B Z := by
  dsimp only [powTerm, Classicism.StoneMP.Pow.term, Term.ofPure_lam, unaryBody]
  simp only [Term.ofPure_app, Term.ofPure_var, Term.ofPure_lam, Term.ofPure_and, Term.ofPure_not,
    Term.ofPure_or, Term.ofPure_all, Term.ofPure_ex, Term.ofPure_eq, B.holds_conj M,
    B.holds_forall M, B.holds_imp M, B.holds_exists M, Premodel.holds_eq_var M,
    Premodel.holds_app_var1, Premodel.holds_app_var2, IEnv.get]
  simp only [iff_def, Set.subset_def]
  exact ⟨id, id⟩

theorem holds_pow {γ α : Ty} (full : CurrentFull (W := W) B)
    (C : B.Dom W (.rel (unary γ))) (A : B.Dom W (.rel (unary α))) :
    B.Holds h (powTerm γ α) (.cons A (.cons C .nil)) ↔ Classicism.StoneMP.Pow (trace₁ B C) (trace₁ B A) := by
  rw [pow_graph B M h]
  constructor
  · rintro ⟨R, hdom, hi, hs⟩
    refine ⟨row₂ B R, hdom, hi, ?_⟩
    intro Z hZ
    obtain ⟨Z', e⟩ := unary_surjective B full α Z
    exact e ▸ hs Z' (e.symm ▸ hZ)
  · rintro ⟨R, hdom, hi, hs⟩
    obtain ⟨R', hR⟩ := binary_surjective B full γ α R
    refine ⟨R', ?_⟩
    rw [hR]
    exact ⟨hdom, hi, fun Z hZ => hs (trace₁ B Z) (fun a ha => hZ ha)⟩

omit M in
private theorem external_pow {α γ : Type} (C : Set γ) (A : Set α) (e : C ≃ Set A) :
    Classicism.StoneMP.Pow C A := by
  let R (c : γ) (a : α) := ∃ hc : c ∈ C, ∃ ha : a ∈ A, (⟨a, ha⟩ : A) ∈ e ⟨c,hc⟩
  have he (c : C) (a : A) : R c a ↔ a ∈ e c := by
    constructor
    · rintro ⟨_, _, h⟩; exact h
    · exact fun h => ⟨c.2, a.2, h⟩
  refine ⟨R, ?_, ?_, ?_⟩
  · rintro _ _ ⟨hc,ha,_⟩
    exact ⟨hc,ha⟩
  · intro c d hc hd h
    have eq : e ⟨c,hc⟩ = e ⟨d,hd⟩ :=
      Set.ext fun a => (he ⟨c,hc⟩ a).symm.trans ((h a.1).trans (he ⟨d,hd⟩ a))
    exact congrArg Subtype.val (e.injective eq)
  · intro Z hZ
    let S : Set A := fun a => Z a.1
    let c := e.symm S
    refine ⟨c.1, c.2, fun a => ?_⟩
    constructor
    · rintro ⟨_, ha, h⟩
      change (⟨a,ha⟩ : A) ∈ e (e.symm S) at h
      rw [e.apply_symm_apply] at h
      exact h
    · intro ha
      apply (he c ⟨a,hZ a ha⟩).2
      change (⟨a,_⟩ : A) ∈ e (e.symm S)
      rw [e.apply_symm_apply]
      exact ha

abbrev subPair {Γ : Ctx} {σ : Ty} (a b : Var Γ (.rel (unary σ))) : Formula Sig Γ :=
  Term.forall' (Term.imp (.app (.var (.succ a)) (.var .zero)) (.app (.var (.succ b)) (.var .zero)))

theorem holds_subPair {Γ : Ctx} {σ : Ty} (g : IEnv (B.Dom W) Γ) (a b : Var Γ (.rel (unary σ))) :
    B.Holds h (subPair a b) g ↔ trace₁ B (g.get a) ⊆ trace₁ B (g.get b) := by
  simp only [subPair, B.holds_forall M, B.holds_imp M, Premodel.holds_app_var1, IEnv.get]
  rfl

abbrev pcTerm {Sig : Signature} (σ : Ty) : Formula Sig [.rel (unary σ)] :=
  unaryBody (Term.ofPure (Classicism.StoneMP.PowerClosed.term σ))

private theorem holds_powerClosed {σ : Ty} (full : CurrentFull (W := W) B)
    (Y : B.Dom W (.rel (unary σ))) :
    B.Holds h (pcTerm σ) (.cons Y .nil) ↔
      ∀ A : Set (B.Dom W σ), A ⊆ trace₁ B Y → Cardinal.mk A < Cardinal.mk (trace₁ B Y) →
        ∃ C : Set (B.Dom W σ), C ⊆ trace₁ B Y ∧ Cardinal.mk C < Cardinal.mk (trace₁ B Y) ∧ Classicism.StoneMP.Pow C A := by
  have eq : pcTerm (Sig := Sig) σ =
      Term.forall' (Term.imp (subPair .zero (.succ .zero)) (Term.imp
        (at₂ (smallerTerm σ σ) .zero (.succ .zero)) (Term.exists'
          (Term.conj (subPair .zero (.succ (.succ .zero))) (Term.conj
           (at₂ (smallerTerm σ σ) .zero (.succ (.succ .zero)))
           (at₂ (powTerm σ σ) .zero (.succ .zero))))))) := rfl
  rw [eq, B.holds_forall M]
  have all := unary_surjective B full σ
  rw [all.forall (p := fun A => A ⊆ trace₁ B Y → Cardinal.mk A < Cardinal.mk (trace₁ B Y) →
    ∃ C : Set (B.Dom W σ), C ⊆ trace₁ B Y ∧ Cardinal.mk C < Cardinal.mk (trace₁ B Y) ∧ Classicism.StoneMP.Pow C A)]
  apply forall_congr'
  intro A
  rw [B.holds_imp M, holds_subPair B M h, B.holds_imp M, holds_at₂, holds_smaller B M h full, B.holds_exists M]
  apply imp_congr_right
  intro _
  apply imp_congr_right
  intro _
  rw [all.exists (p := fun C => C ⊆ trace₁ B Y ∧ Cardinal.mk C < Cardinal.mk (trace₁ B Y) ∧ Classicism.StoneMP.Pow C (trace₁ B A))]
  apply exists_congr
  intro C
  simp only [B.holds_conj M, holds_subPair B M h, holds_at₂, holds_smaller B M h full, holds_pow B M h full, IEnv.get]


/-- In a full current relation domain, a strong-limit-sized represented family
satisfies the native represented-power closure formula. -/
theorem powerClosed_of_cut {σ : Ty} (full : CurrentFull (W := W) B)
    (Y : B.Dom W (.rel (unary σ))) (cut : Cardinal.IsStrongLimit (#(trace₁ B Y))) :
    B.Holds h (pcTerm σ) (.cons Y .nil) := by
  apply (holds_powerClosed B M h full Y).2
  intro A _ ha
  have hpow : #(Set A) < #(trace₁ B Y) := by
    rw [Cardinal.mk_set]
    exact cut.isStrongPrelimit ha
  obtain ⟨f⟩ := (Cardinal.le_def _ _).mp hpow.le
  let j : Set A → B.Dom W σ := fun s => (f s).1
  have inj : Function.Injective j := Subtype.val_injective.comp f.injective
  refine ⟨Set.range j, ?_, ?_, external_pow _ _ (Equiv.ofInjective j inj).symm⟩
  · rintro _ ⟨s, rfl⟩
    exact (f s).2
  · rwa [Cardinal.mk_range_eq j inj]

#print axioms powerClosed_of_cut

end
end Classicism.Meta.Coalesced.StoneFan.PowerClosed
