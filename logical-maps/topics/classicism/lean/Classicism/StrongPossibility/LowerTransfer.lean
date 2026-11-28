import Classicism.StrongPossibility.Layers

/-! At a lower site every tuple and every continuation is old. Therefore all terms,
including abstractions with higher-type parameters, keep their original interpretations. -/

namespace Classicism.Meta.StrongPossibility.Layers
open CategoryTheory Intensional
noncomputable section
variable {U C : Type} [SmallCategory U] [SmallCategory C] (π : U ⥤ C)
variable {Sig : Signature} (O : Premodel Sig C) (E : Domain π O .e)

def oldRow {ρ : RTy} {z : C} (X : Intension (inner π O E) ρ (.lower z)) : Intension O.inner ρ z :=
  {p | (⟨.lower p.1, (oldArgs π O E ρ (z := p.1)).symm p.2.1, Site.down π p.2.2⟩ :
    Tuple (inner π O E) ρ (.lower z)) ∈ X}

theorem oldRow_eq_lowerRows {ρ : RTy} {z : C} (X : Intension (inner π O E) ρ (.lower z)) :
    oldRow π O E X = lowerRows π O E (𝟙 (Site.lower (π := π) z)) X := by
  ext ⟨w,a,j⟩
  change _ ↔ (⟨.lower w, (oldArgs π O E ρ (z := w)).symm a, Site.down π (𝟙 z ≫ j)⟩ :
    Tuple (inner π O E) ρ (.lower z)) ∈ X
  rw [Category.id_comp]; rfl

def oldOuter : ∀ σ z, Outer (inner π O E) σ (.lower z) → Outer O.inner σ z
  | .e, _, x => x
  | .var _, _, x => x
  | .rel _, _, x => oldRow π O E x

theorem oldOuter_injective : ∀ σ z, Function.Injective (oldOuter π O E σ z)
  | .e, _ => fun _ _ h => h
  | .var _, _ => fun _ _ h => h
  | .rel ρ, z => by
    intro X Y eq; ext ⟨w,a,j⟩; cases w with
    | upper => exact PEmpty.elim j
    | lower w =>
      have H := Set.ext_iff.mp eq ⟨w,oldArgs π O E ρ (z := w) a,j⟩
      change (⟨.lower w, (oldArgs π O E ρ (z := w)).symm ((oldArgs π O E ρ (z := w)) a),j⟩ :
        Tuple (inner π O E) ρ (.lower z)) ∈ X ↔ (⟨.lower w, (oldArgs π O E ρ (z := w)).symm ((oldArgs π O E ρ (z := w)) a),j⟩ : Tuple (inner π O E) ρ (.lower z)) ∈ Y at H
      simpa only [Equiv.symm_apply_apply] using H

theorem oldOuter_map : ∀ σ {z w : C} (j : z ⟶ w) (x : Outer (inner π O E) σ (.lower z)),
    oldOuter π O E σ w (Outer.map (inner π O E) σ (Site.down π j) x) =
      Outer.map O.inner σ j (oldOuter π O E σ z x)
  | .e, _, _, _, _ => rfl
  | .var _, _, _, _, _ => rfl
  | .rel _, _, _, _, _ => rfl

variable (u : U) (base : O.W₀ ⟶ π.obj u) (ne : ∀ v, Nonempty (E.upper.obj v))
  (lift : O.Dom (π.obj u) .e → E.upper.obj u)

local notation "A" => model π O E u base ne lift

theorem old_incl : ∀ σ z (x : O.Dom z σ), oldOuter π O E σ z ((A).Incl σ (.lower z) x) = O.Incl σ z x
  | .e, _, _ => rfl
  | .var _, _, _ => rfl
  | .rel ρ, z, x => (oldRow_eq_lowerRows π O E _).trans (lower_incl π O E ρ z x)

private theorem old_apply {σ : Ty} {ρ : RTy} {z : C}
    (F : Intension (inner π O E) (.arr σ ρ) (.lower z)) (x : Outer (inner π O E) σ (.lower z)) :
    oldRow π O E ((A).apply F x) = O.apply (oldRow π O E F) (oldOuter π O E σ z x) := by
  ext ⟨w,a,j⟩
  change (∃ y : O.Dom w σ, (A).Incl σ (.lower w) y = Outer.map (inner π O E) σ (Site.down π j) x ∧ _) ↔
    (∃ y : O.Dom w σ, O.Incl σ w y = Outer.map O.inner σ j (oldOuter π O E σ z x) ∧ _)
  refine exists_congr fun y => and_congr ?_ Iff.rfl
  rw [← old_incl π O E u base ne lift σ w y, ← oldOuter_map]
  exact (oldOuter_injective π O E σ w).eq_iff.symm

private theorem read_at {ρ : RTy} {w : C} (p : O.Dom w (.rel ρ)) (a : Args O.inner ρ w) :
    (⟨.lower w, (oldArgs π O E ρ (z := w)).symm a, Site.down π (𝟙 w)⟩ :
      Tuple (inner π O E) ρ (.lower w)) ∈ incl π O E ρ (.lower w) p ↔
    (⟨w,a,𝟙 w⟩ : Tuple O.inner ρ w) ∈ O.incl ρ w p :=
  by change (⟨w,(oldArgs π O E ρ (z := w)) ((oldArgs π O E ρ (z := w)).symm a),𝟙 w⟩ : Tuple O.inner ρ w) ∈ O.incl ρ w p ↔ _; simp

private theorem old_args_map : ∀ ρ {z w : C} (j : z ⟶ w) (a : Args O.inner ρ z),
    Args.map (inner π O E) ρ (Site.down π j) ((oldArgs π O E ρ (z := z)).symm a) =
    (oldArgs π O E ρ (z := w)).symm (Args.map O.inner ρ j a)
  | .t, _, _, _, _ => rfl
  | .arr _ ρ, _, _, j, a => Prod.ext rfl (old_args_map ρ j a.2)

private theorem read_box (ρ : RTy) (z : C) :
    oldRow π O E ((A).boxRead ρ (.lower z)) = O.boxRead ρ z := by
  ext ⟨w, ⟨p,a⟩, j⟩
  change (∀ (v : Site π) (k : Site.lower w ⟶ v), _ ) ↔ ∀ (v : C) (k : w ⟶ v), _
  have atLower (v : C) (k : w ⟶ v) :
      (⟨.lower v, Args.map (inner π O E) ρ (Site.down π k) ((oldArgs π O E ρ (z := w)).symm a),
        Site.down π k⟩ : Tuple (inner π O E) ρ (.lower w)) ∈ incl π O E ρ (.lower w) p ↔
      (⟨v, Args.map O.inner ρ k a, k⟩ : Tuple O.inner ρ w) ∈ O.incl ρ w p := by
    rw [old_args_map]
    exact Set.ext_iff.mp (old_incl π O E u base ne lift (.rel ρ) w p) ⟨v,Args.map O.inner ρ k a,k⟩
  constructor
  · exact fun h v k => (atLower v k).1 (h (.lower v) k)
  · rintro h (v|v) k
    · exact PEmpty.elim k
    · exact (atLower v k).2 (h v k)

private theorem lift_projects (section_lift : ∀ x, E.project.app u (lift x) = x) :
    ∀ σ (x : O.Dom (π.obj u) σ), (level π O E σ).project.app u (liftValue π O E u lift σ x) = x
  | .e, x => section_lift x
  | .var _, _ => rfl
  | .rel _, _ => rfl

theorem old_sem (section_lift : ∀ x, E.project.app u (lift x) = x) :
    ∀ {Γ : Ctx} {σ : Ty} {z : C} (j : π.obj u ⟶ z) (t : Term Sig Γ σ) (g : IEnv (O.Dom z) Γ),
    oldOuter π O E σ z ((A).sem (Site.cross π j) t g) = O.sem (base ≫ j) t g
  | _, _, z, _, .var v, g => old_incl π O E u base ne lift _ z (g.get v)
  | _, _, z, j, .const c, g => by
    change oldOuter π O E _ z ((A).Incl _ (.lower z) (((O.inner _).map j)
      ((level π O E _).project.app u (liftValue π O E u lift _ ((O.inner _).map base (O.I c)))))) = _
    rw [old_incl, lift_projects π O E u lift section_lift]
    simp [Premodel.sem, Functor.map_comp]
  | _, _, _, j, .app f x, g =>
    (old_apply π O E u base ne lift _ _).trans
      (congrArg₂ O.apply (old_sem section_lift j f g) (old_sem section_lift j x g))
  | _, _, z, j, .lam (σ := σ) (ρ := ρ) body, g => by
    ext ⟨w,⟨x,a⟩,k⟩
    have H := Set.ext_iff.mp (old_sem section_lift (j ≫ k) body (.cons x (O.push k g))) ⟨w,a,𝟙 w⟩
    change (⟨w,a,𝟙 w⟩ : Tuple O.inner ρ w) ∈ oldRow π O E ((A).sem (Site.cross π (j ≫ k)) body (.cons x (O.push k g))) ↔
      (⟨w,a,𝟙 w⟩ : Tuple O.inner ρ w) ∈ O.sem ((base ≫ j) ≫ k) body (.cons x (O.push k g))
    rwa [Category.assoc]
  | _, _, _, _, .all _, _ => rfl
  | _, _, _, _, .ex _, _ => rfl
  | _, _, _, _, .eq _, _ => rfl
  | _, _, _, _, .constR _, _ => rfl
  | _, _, _, _, .and, _ | _, _, _, _, .andR _, _ => by
    ext ⟨_,⟨_,_,_⟩,_⟩; exact and_congr (read_at π O E _ _) (read_at π O E _ _)
  | _, _, _, _, .or, _ | _, _, _, _, .orR _, _ => by
    ext ⟨_,⟨_,_,_⟩,_⟩; exact or_congr (read_at π O E _ _) (read_at π O E _ _)
  | _, _, _, _, .not, _ | _, _, _, _, .negR _, _ => by
    ext ⟨_,⟨_,_⟩,_⟩; exact not_congr (read_at π O E _ _)
  | _, _, _, _, .boxR ρ, _ => read_box π O E u base ne lift ρ _
  | _, _, _, _, .coextR ρ, _ => by
    ext ⟨w,⟨x,y,⟨⟩⟩,j⟩
    constructor
    · intro h a
      exact (read_at π O E x a).symm.trans ((h ((oldArgs π O E ρ (z := w)).symm a)).trans (read_at π O E y a))
    · intro h a
      obtain ⟨b,rfl⟩ := (oldArgs π O E ρ (z := w)).symm.surjective a
      exact (read_at π O E x b).trans ((h b).trans (read_at π O E y b).symm)
  | _, _, _, _, .inclR ρ, _ => by
    ext ⟨w,⟨x,y,⟨⟩⟩,j⟩
    constructor
    · intro h a ha
      exact (read_at π O E y a).1 (h _ ((read_at π O E x a).2 ha))
    · intro h a
      obtain ⟨b,rfl⟩ := (oldArgs π O E ρ (z := w)).symm.surjective a
      exact fun hb => (read_at π O E y b).2 (h b ((read_at π O E x b).1 hb))

end
end Classicism.Meta.StrongPossibility.Layers
