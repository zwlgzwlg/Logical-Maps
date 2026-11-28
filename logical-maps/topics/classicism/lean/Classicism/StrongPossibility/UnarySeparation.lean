import Classicism.StrongPossibility.UnaryLayerReading
import Classicism.StrongPossibility.LayerValidity
import Classicism.Syntax.Russell
import Classicism.StrongPossibility.UnaryCanonical

/-! An equation between the value of a named tester and the diagonal can be refuted
by observing the two values at the duplicate of the marker. -/
namespace Classicism.Meta.StrongPossibility.UnarySeparation
open CategoryTheory Intensional Coalesced Term DoubleCover UnaryReading
variable {Sig : Signature} {C : Type} [SmallCategory C]

abbrev q (b : Term Sig [] .e) := Term.app (op (Sig := Sig)) b
abbrev rho (b : Term Sig [] .e) := Diagonal.russell (q b)
abbrev diag (b : Term Sig [] .e) := Term.app (q b) (rho b)

variable (A : Premodel Sig C) (M : A.IsModel)
include M

theorem applied {W V : C} (h : A.W₀ ⟶ W) (b : Term Sig [] .e) (f : Term Sig [] Tester)
    (k : W ⟶ V) (x : A.Dom V .e) :
    row A (A.sem h (.app (q b) f) .nil) k x ↔
      CanFind A (A.sem h f .nil) k (mv A k (A.sem h b .nil)) x := by
  obtain ⟨F,hF⟩ := M h f .nil
  change row A (A.apply (A.apply (A.sem h op .nil) (A.sem h b .nil)) (A.sem h f .nil)) k x ↔ _
  rw [A.apply_eq (A.sem h op .nil) (x := A.sem h b .nil) (b := A.sem h b .nil) rfl, A.apply_eq _ hF, ← hF]
  exact row_value A M h _ F k x

/-- Every output rejects the transported marker. Its first search would have
to distinguish that individual from itself. -/
theorem rejects_marker {W V : C} (h : A.W₀ ⟶ W) (b : Term Sig [] .e)
    (f : Term Sig [] Tester) (k : W ⟶ V) :
    ¬ row A (A.sem h (.app (q b) f) .nil) k (mv A k (A.sem h b .nil)) :=
  fun found => not_canFind_self A (A.sem h f .nil) k (mv A k (A.sem h b .nil))
    ((applied A M h b f k (mv A k (A.sem h b .nil))).mp found)

theorem fixed_output {W : C} (h : A.W₀ ⟶ W) (b : Term Sig [] .e) (f : Term Sig [] Tester) :
    Fixed A (A.sem h (.app (q b) f) .nil) := by
  intro V k x
  constructor
  · intro now
    exact ⟨V,𝟙 V,by simpa only [Category.comp_id, Functor.map_id_apply] using now⟩
  · rintro ⟨Y,l,after⟩
    apply (applied A M h b f k x).2
    obtain ⟨Z,j,diff,p,code,T,m,same,miss⟩ := (applied A M h b f _ _).1 after
    refine ⟨Z,l ≫ j,?_,p,?_,T,m,?_,?_⟩
    · simpa only [mv, Functor.map_comp, types_comp_apply] using diff
    · simpa only [mv, Functor.map_comp, types_comp_apply] using code
    · simpa only [mv, Functor.map_comp, types_comp_apply] using same
    · simpa only [Category.assoc] using miss

theorem self {W : C} (h : A.W₀ ⟶ W) (b : Term Sig [] .e) :
    A.Holds h (.app (rho b) (diag b)) .nil :=
  A.sound M (Ax := AxiomSet.empty) h (fun _ H => H.elim) (Δ := [])
    (Diagonal.russell_self (q b)) .nil (by intro p hp; cases hp)

omit M in
/-- Reading the tester on the transported diagonal is evaluating the closed formula
at the target arrow. The row at the target includes its complete transported predicate. -/
theorem tester_at {W Z : C} (h : A.W₀ ⟶ W) (k : W ⟶ Z) (t : Term Sig [] S)
    (y : A.Dom W S) (hy : A.Incl _ W y = A.sem h t .nil) (f : Term Sig [] Tester) :
    A.Holds (h ≫ k) (.app f t) .nil ↔
    (⟨Z, ((A.inner S).map k y, PUnit.unit), k⟩ : Tuple A.inner Tester W) ∈ A.sem h f .nil := by
  have trans (v : Term Sig [] S) : A.sem (h ≫ k) v .nil =
      Intension.map A.inner k (A.sem h v .nil) := A.sem_push h v .nil k
  have ht : A.Incl S Z ((A.inner S).map k y) = A.sem (h ≫ k) t .nil := by
    rw [trans, A.Incl_map, hy]; rfl
  rw [A.holds_app _ _ _ _ ht]
  have hf : A.sem (h ≫ k) f .nil = Intension.map A.inner k (A.sem h f .nil) :=
    A.sem_push h f .nil k
  rw [hf, Intension.mem_map, Category.comp_id]

omit M
section Projection
open UnaryLayerReading
variable (O : Premodel Sig C) (d : Unary O O.W₀) (hd : Fixed O d)
local notation "P" => Doubled O d hd

/-- The old component of an upper denotation is the original term denotation. -/
theorem project_term {τ : RTy} (t : Term Sig [] (.rel τ)) (F : (P).Dom (P).W₀ (.rel τ))
    (ht : (P).Incl _ _ F = (P).sem (𝟙 _) t .nil) :
    O.incl τ O.W₀ F.2 = O.sem (𝟙 _) t .nil := by
  let down : (P).W₀ ⟶ Lo O O.W₀ := Layers.Site.cross (π O) (𝟙 O.W₀)
  have e : (P).Incl _ _ (((P).inner (.rel τ)).map down F) = (P).sem down t .nil := by
    refine ((P).Incl_map (.rel τ) down F).trans ((congrArg (Outer.map (P).inner (.rel τ) down) ht).trans ?_)
    have push := (P).sem_push (𝟙 (P).W₀) t .nil down
    exact push.symm.trans (congrArg (fun l : (P).W₀ ⟶ Lo O O.W₀ => (P).sem l t .nil)
      (Category.id_comp down))
  have old := congrArg (Layers.oldOuter (π O) O (individual O d hd) (.rel τ) O.W₀) e
  have before := Layers.old_incl (π O) O (individual O d hd) (root O) (𝟙 O.W₀)
    (nonemptyUpper O d) (first O d) (.rel τ) O.W₀ (((P).inner (.rel τ)).map down F)
  have after := Layers.old_sem (π O) O (individual O d hd) (root O) (𝟙 O.W₀)
    (nonemptyUpper O d) (first O d) (fun _ => rfl) (𝟙 O.W₀) t .nil
  have result := before.symm.trans (old.trans after)
  change O.incl τ O.W₀ ((O.inner _).map (𝟙 _) F.2) = O.sem (𝟙 _ ≫ 𝟙 _) t .nil at result
  rw [(O.inner (.rel τ)).map_id_apply O.W₀ F.2, Category.id_comp] at result
  exact result

end Projection

section Marker
open UnaryLayerReading DistinguishedDefinable

variable (O : Premodel Sig C) (n : names (Sig := Sig) .e)
variable (d : Unary O O.W₀) (hd : Fixed O d)
local notation "P" => Doubled O d hd

/-- The old individual denoted by a typed name. -/
abbrev anchor (K : Premodel Sig C) (n : names (Sig := Sig) .e) : K.Dom K.W₀ .e :=
  castD (D := K.Dom K.W₀) n.2 (K.I n.1)

private theorem root_constAt (K : Premodel Sig C) (c : names (Sig := Sig) .e) :
    K.sem (𝟙 K.W₀) (constAt (Γ := []) c.1 c.2) .nil = anchor K c := by
  rw [sem_constAt, Functor.map_id_apply]
  rfl

private theorem upper_constAt :
    (P).sem (𝟙 (P).W₀) (constAt (Γ := []) n.1 n.2) .nil = first O d (anchor O n) := by
  rw [root_constAt]
  change castD (D := (P).Dom (P).W₀) n.2
    (Layers.liftValue (π O) O (individual O d hd) (root O) (first O d) _
      ((O.inner _).map (𝟙 O.W₀) (O.I n.1))) = _
  rw [(O.inner _).map_id_apply O.W₀ (O.I n.1)]
  exact (castD_map (D := O.Dom O.W₀) (D' := (P).Dom (P).W₀)
    (Layers.liftValue (π O) O (individual O d hd) (root O) (first O d)) n.2 (O.I n.1)).symm

/-- If the predicate is false at the named individual, its twin records whether
some old continuation rejects that predicate under the given tester. -/
theorem reads_term (M' : (P).IsModel) (hb : ¬ bit O d (root O) (anchor O n))
    (p : Term Sig [] S) (fixed : Fixed P ((P).sem (𝟙 (P).W₀) p .nil))
    (f : Term Sig [] Tester)
    (target : O.sem (𝟙 O.W₀) p .nil = d) :
    row P ((P).sem (𝟙 _) (.app (q (constAt n.1 n.2)) f) .nil) (𝟙 (P).W₀)
        (second O d (z := root O) (anchor O n) hb) ↔
      ∃ (Z : C) (k : O.W₀ ⟶ Z), ¬ O.Holds k (.app f p) .nil := by
  obtain ⟨F,hF⟩ := M' (𝟙 _) f .nil
  -- The diagonal itself supplies the code used in the Russell comparison.
  obtain ⟨w,hw⟩ := M' (𝟙 (P).W₀) p .nil
  let s := w.2
  have hs : O.incl S _ s = O.sem (𝟙 O.W₀) p .nil := project_term O d hd p w hw
  have code := (isCode_iff O d hd (z := root O) (anchor O n) hb w).mpr
    ⟨(congrArg (Fixed P) hw).mpr fixed,
      hs.trans (target.trans (Intension.map_id O.inner d).symm)⟩
  have semF : (P).sem (𝟙 _) (.app (q (constAt n.1 n.2)) f) .nil =
      UnaryReading.value P (𝟙 (P).W₀) (first O d (z := root O) (anchor O n)) F := by
    change (P).apply ((P).apply ((P).sem (𝟙 _) op .nil) ((P).sem (𝟙 _) (constAt n.1 n.2) .nil))
      ((P).sem (𝟙 _) f .nil) = _
    rw [(P).apply_eq ((P).sem (𝟙 _) op .nil)
      (x := (P).sem (𝟙 _) (constAt n.1 n.2) .nil) (b := (P).sem (𝟙 _) (constAt n.1 n.2) .nil) rfl,
      (P).apply_eq _ hF, upper_constAt O n d hd]
  rw [semF, root_row O d hd M' (anchor O n) hb F w code (hs.trans target)]
  unfold OldReject
  apply exists_congr; intro Z
  apply exists_congr; intro k
  have projection := Set.ext_iff.mp (project_term O d hd f F hF)
    (⟨Z, ((O.inner S).map k s, PUnit.unit), k⟩ : Tuple O.inner Tester O.W₀)
  have h := tester_at O (𝟙 _) k p s hs f
  have at_k := congrArg (fun j : O.W₀ ⟶ Z => O.Holds j (.app f p) .nil)
    (Category.id_comp (show O.W₀ ⟶ Z from k))
  exact not_congr (projection.trans (h.symm.trans (Iff.of_eq at_k)))

/-- For an input false at the named individual, identical outputs agree on
whether the old model admits a continuation where their testers reject it. -/
theorem same_observation (M' : (P).IsModel) (hb : ¬ bit O d (root O) (anchor O n))
    (p : Term Sig [] S) (fixed : Fixed P ((P).sem (𝟙 (P).W₀) p .nil))
    (target : O.sem (𝟙 O.W₀) p .nil = d) (f g : Term Sig [] Tester)
    (same : (P).HoldsSentence (eq' (.app (q (constAt n.1 n.2)) f) (.app (q (constAt n.1 n.2)) g))) :
    (∃ (Z : C) (k : O.W₀ ⟶ Z), ¬ O.Holds k (.app f p) .nil) ↔
     ∃ (Z : C) (k : O.W₀ ⟶ Z), ¬ O.Holds k (.app g p) .nil := by
  let duplicate := second O d (z := root O) (anchor O n) hb
  have eq := ((P).holds_eq M' (𝟙 _) .nil _ _).mp same
  have observation := congrArg (fun u : Unary P (P).W₀ => row P u (𝟙 (P).W₀) duplicate) eq
  exact (reads_term O n d hd M' hb p fixed f target).symm.trans <|
    (Iff.of_eq observation).trans (reads_term O n d hd M' hb p fixed g target)

end Marker

open UnaryLayerReading DistinguishedDefinable

/-- The same marker distinguishes the proposed identity's two sides. A failing
tester lights up its duplicate. Russell's own tester can never light it up. -/
theorem predecessors (Sig : Signature) : UnaryCanonical.Predecessors Sig := by
  intro C _ O M₀ vars n f fail
  let b : Term Sig [] .e := constAt n.1 n.2
  let d := O.sem (𝟙 O.W₀) (diag b) .nil
  have hd : Fixed O d := fixed_output O M₀ (𝟙 O.W₀) b (rho b)
  have hb : ¬ bit O d (root O) (anchor O n) := by
    have absent := rejects_marker O M₀ (𝟙 O.W₀) b (rho b) (𝟙 O.W₀)
    have eq : mv O (𝟙 O.W₀) (O.sem (𝟙 O.W₀) b .nil) = anchor O n :=
      ((O.inner .e).map_id_apply O.W₀ _).trans (root_constAt O n)
    exact (congrArg (fun x => ¬ row O d (𝟙 O.W₀) x) eq).mp absent
  let P := Doubled O d hd
  have M' : P.IsModel := Layers.isModel (π O) O (individual O d hd) (root O) (𝟙 _)
    (nonemptyUpper O d) (first O d) (fun _ => rfl) M₀
  refine ⟨_, inferInstance, P, M', Layers.holdsAx_varExistence (π O) O (individual O d hd)
    (root O) (𝟙 _) (nonemptyUpper O d) (first O d) (fun _ => rfl) M₀ vars, ?_⟩
  intro same
  have observation := same_observation O n d hd M' hb (diag b)
    (fixed_output P M' (𝟙 P.W₀) b (rho b)) rfl f (rho b) same
  obtain ⟨Z,k,rejects⟩ := observation.mp ⟨_, 𝟙 _, fail⟩
  exact rejects (self O M₀ k b)

end Classicism.Meta.StrongPossibility.UnarySeparation
