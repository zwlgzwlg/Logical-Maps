import Classicism.Syntax.Blocks
import Classicism.Syntax.Russell
import Classicism.Semantics.IntensionalFacts

/-! Native syntax for the six-individual proxy diagonal. The signature can be arbitrary.
The terms use only logical constants. -/

namespace Classicism.Meta.ProxyDiagonal

open Term

abbrev roles := [Ty.e, Ty.e, Ty.e, Ty.e, Ty.e, Ty.e]
abbrev S : RTy := roles ⇒* RTy.t
abbrev Tester : RTy := (S : Ty) ⇒ RTy.t

/-- Arguments in the order of the three identity tests. -/
structure Six (α : Type) where
  a0 : α
  a1 : α
  b0 : α
  b1 : α
  c0 : α
  c1 : α

def Six.map {α β : Type} (f : α → β) (x : Six α) : Six β :=
  ⟨f x.a0, f x.a1, f x.b0, f x.b1, f x.c0, f x.c1⟩

variable {Sig : Signature} {Γ : Ctx}
abbrev Names (Sig : Signature) (Γ : Ctx) := Six (Term Sig Γ Ty.e)

def controls : Names Sig (Ctx.block roles Γ) :=
  ⟨.var (.succ (.succ (.succ (.succ (.succ .zero))))),
   .var (.succ (.succ (.succ (.succ .zero)))),
   .var (.succ (.succ (.succ .zero))),
   .var (.succ (.succ .zero)), .var (.succ .zero), .var .zero⟩

def atSix (p : Term Sig Γ S) (c : Names Sig Γ) : Formula Sig Γ :=
  .app (.app (.app (.app (.app (.app p c.a0) c.a1) c.b0) c.b1) c.c0) c.c1

def start (c : Names Sig Γ) : Formula Sig Γ := neg (eq' c.a0 c.a1)
def old (c : Names Sig Γ) : Formula Sig Γ := eq' c.b0 c.b1
def test (c : Names Sig Γ) : Formula Sig Γ :=
  conj (neg (start c)) (conj (neg (old c)) (neg (eq' c.c0 c.c1)))
def priv (c : Names Sig Γ) : Formula Sig Γ :=
  conj (neg (start c)) (conj (neg (old c)) (eq' c.c0 c.c1))

/-- Exactly n current individuals satisfy the predicate. Removing a selected individual
gives an elementary definition using ordinary quantification at e. -/
def exactly : (n : Nat) → {Γ : Ctx} → Term Sig Γ (Ty.e ⇒ RTy.t) → Formula Sig Γ
  | 0, _, p => forall' (neg (.app p.weaken v0))
  | n+1, _, p => exists' (conj (.app p.weaken v0)
      (exactly n (.lam (conj (.app p.weaken.weaken v0) (neg (eq' v0 v1))))))

def tag (n : Nat) (c : Names Sig Γ) (x : Term Sig Γ Ty.e) : Formula Sig Γ :=
  exactly n (.lam (box (imp (priv (c.map (fun u => u.weaken))) (eq' x.weaken v0))))

def bit (c : Names Sig Γ) : Formula Sig Γ :=
  exists' (tag 7 (c.map (fun u => u.weaken)) v0)

def allTags (c v : Names Sig Γ) : Formula Sig Γ :=
  conj (tag 1 c v.a0) (conj (tag 2 c v.a1) (conj (tag 3 c v.b0)
  (conj (tag 4 c v.b1) (conj (tag 5 c v.c0) (tag 6 c v.c1)))))

def diaRows (p : Term Sig Γ S) : Term Sig Γ S :=
  lamBlock roles (dia (atSix (p.rename (Ren.wkBlock roles)) controls))

def code (c : Names Sig Γ) (p : Term Sig Γ S) : Formula Sig Γ :=
  let c' := c.map (fun u => u.rename (Ren.wkBlock roles))
  let p' := p.rename (Ren.wkBlock roles)
  conj (eq' p (diaRows p)) (box (imp (test c) (forallBlock roles
    (imp (allTags c' controls)
      (iff (bit c') (dia (conj (old c') (atSix p' controls))))))))

def search (f : Term Sig Γ Tester) (c : Names Sig Γ) : Formula Sig Γ :=
  let c' := c.map (fun u => u.weaken (τ := S))
  dia (conj (start c) (exists' (conj (code c' v0)
    (dia (conj (old c') (neg (.app f.weaken v0)))))))

/-- Curried spelling of the seven-place relation Q. -/
def Q : Term Sig [] ((Tester : Ty) ⇒ S) :=
  .lam (lamBlock roles (search ((v0 : Term Sig [Tester] Tester).rename (Ren.wkBlock roles))
    controls))

export Diagonal (russell)

def rho : Term Sig [] Tester := russell Q
def d : Term Sig [] S := .app Q rho

def bad (f : Term Sig [] Tester) : Sentence Sig :=
  conj (eq' (.app Q f) d) (neg (eq' (.app f d) top))

end Classicism.Meta.ProxyDiagonal
