import Classicism.StrongPossibility.ProxyCounting
import Mathlib.Data.Fintype.Card

namespace Classicism.Meta.ProxyDiagonal

/-- The private labels. Each existing individual name may have its own class; that index
type need not be finite or have decidable equality. -/
inductive Label (N : Type) (bit : Bool) where
  | coord (i : Fin 6)
  | mark (on : bit = true)
  | ctrl (side : Bool)
  | name (n : N)

def Label.width {N : Type} {b : Bool} : Label N b → Nat
  | .coord j => j.val + 1
  | .mark _ => 7
  | .ctrl _ | .name _ => 8

abbrev ProxyInd (N : Type) (b : Bool) := Σ l : Label N b, Fin l.width

def privateImage {N : Type} {b : Bool} (x : ProxyInd N b) := x.1

def oldImage {N E : Type} {b : Bool} (u : Fin 6 → E) (a : E) (names : N → E) :
    ProxyInd N b → E
  | ⟨.coord i, _⟩ => u i
  | ⟨.name n, _⟩ => names n
  | _ => a

def picked {N : Type} {b : Bool} (i : Fin 6) : ProxyInd N b :=
  ⟨.coord i, ⟨0, Nat.zero_lt_succ _⟩⟩

def controlInd {N : Type} {b : Bool} (side : Bool) (i : Fin 8) : ProxyInd N b :=
  ⟨.ctrl side, i⟩

def proxyControls {N : Type} {b : Bool} : Six (ProxyInd N b) :=
  ⟨controlInd false 0, controlInd false 0, controlInd false 0,
   controlInd true 0, controlInd false 0, controlInd false 1⟩

theorem size_unique {α : Type} {m n : Nat} {P : α → Prop}
    (hm : Size m P) (hn : Size n P) : m = n := by
  obtain ⟨s, hs, hP⟩ := hm
  obtain ⟨t, ht, hQ⟩ := hn
  have hst : s = t := Finset.ext (fun a => (hP a).trans (hQ a).symm)
  simpa [hst, hs] using hs.symm.trans (hst ▸ ht)

def fiberInclusion {N : Type} {b : Bool} (l : Label N b) :
    Fin l.width ↪ ProxyInd N b where
  toFun i := ⟨l,i⟩
  inj' := fun _ _ h => eq_of_heq (Sigma.mk.inj h).2

theorem size_fibre {N : Type} {b : Bool} (x : ProxyInd N b) :
    Size x.1.width (fun y : ProxyInd N b => privateImage x = privateImage y) := by
  classical
  refine ⟨Finset.univ.map (fiberInclusion x.1), by simp, ?_⟩
  rintro ⟨l,i⟩
  simp only [Finset.mem_map, Finset.mem_univ, true_and, privateImage]
  constructor
  · rintro ⟨j,e⟩
    exact congrArg Sigma.fst e
  · rintro h
    subst l
    exact ⟨i,rfl⟩

theorem tag_iff_width {N : Type} {b : Bool} (x : ProxyInd N b) (n : Nat) :
    Size n (fun y : ProxyInd N b => privateImage x = privateImage y) ↔ x.1.width = n :=
  ⟨fun H => size_unique (size_fibre x) H, fun h => h ▸ size_fibre x⟩

theorem projected_tag {N E : Type} {b : Bool} (u : Fin 6 → E) (a : E) (names : N → E)
    (x : ProxyInd N b) (i : Fin 6)
    (H : Size (i.val+1) (fun y : ProxyInd N b => privateImage x = privateImage y)) :
    oldImage u a names x = u i := by
  have e := (tag_iff_width x _).mp H
  obtain ⟨l,j⟩ := x
  cases l with
  | coord k =>
    change k.val+1 = i.val+1 at e
    have he : k = i := Fin.ext (by omega)
    subst k; rfl
  | mark _ => change 7 = i.val+1 at e; omega
  | ctrl _ => change 8 = i.val+1 at e; omega
  | name _ => change 8 = i.val+1 at e; omega

theorem picked_tag {N : Type} {b : Bool} (i : Fin 6) :
    Size (i.val+1) (fun y : ProxyInd N b => privateImage (picked i) = privateImage y) :=
  size_fibre (picked i)

theorem marker_iff {N : Type} {b : Bool} :
    (∃ x : ProxyInd N b, Size 7 (fun y => privateImage x = privateImage y)) ↔ b = true := by
  constructor
  · rintro ⟨x,h⟩
    have e := (tag_iff_width x _).mp h
    rcases x with ⟨i,j⟩
    cases i with
    | coord k => change k.val + 1 = 7 at e; omega
    | mark hb => exact hb
    | ctrl _ => change 8 = 7 at e; omega
    | name _ => change 8 = 7 at e; omega
  · rintro hb
    let x : ProxyInd N b := ⟨.mark hb, ⟨0,by change 0 < 7; decide⟩⟩
    exact ⟨x,size_fibre x⟩

end Classicism.Meta.ProxyDiagonal
