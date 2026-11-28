import Classicism.Coalesced.StoneCatalogue
import Classicism.Coalesced.StoneOrdinalBound

/-! The relational, unboxed vocabulary of the revised Mathematical Possibilism
schema from Andrew Bacon's PR 28 verification tree. -/

namespace Classicism.StoneMP

def Maps {σ τ : Type} [Ty σ] [Ty τ] (F : σ → τ → Prop)
    (A : σ → Prop) (B : τ → Prop) : Prop :=
  (∀ x y, F x y → A x ∧ B y) ∧
  (∀ x, A x → ∃ y, B y ∧ F x y) ∧
  (∀ x y z, F x y → F x z → y = z)
def Injects {σ τ : Type} [Ty σ] [Ty τ] (F : σ → τ → Prop)
    (A : σ → Prop) (B : τ → Prop) : Prop :=
  Maps F A B ∧ ∀ x z y, F x y → F z y → x = z
def Surjects {σ τ : Type} [Ty σ] [Ty τ] (F : σ → τ → Prop)
    (A : σ → Prop) (B : τ → Prop) : Prop :=
  Maps F A B ∧ ∀ y, B y → ∃ x, A x ∧ F x y
def Bijects {σ τ : Type} [Ty σ] [Ty τ] (F : σ → τ → Prop)
    (A : σ → Prop) (B : τ → Prop) : Prop := Injects F A B ∧ Surjects F A B
def Embeds {σ τ : Type} [Ty σ] [Ty τ] (A : σ → Prop) (B : τ → Prop) : Prop :=
  ∃ F, Injects F A B
def Smaller {σ τ : Type} [Ty σ] [Ty τ] (A : σ → Prop) (B : τ → Prop) : Prop :=
  Embeds A B ∧ ¬ Embeds B A
def Equinumerous {σ τ : Type} [Ty σ] [Ty τ] (A : σ → Prop) (B : τ → Prop) : Prop :=
  ∃ F, Bijects F A B
def OrderIso {σ τ : Type} [Ty σ] [Ty τ] (F : σ → τ → Prop)
    (A : σ → Prop) (L : σ → σ → Prop) (B : τ → Prop) (M : τ → τ → Prop) : Prop :=
  Bijects F A B ∧ ∀ x y u v, F x u → F y v → (L x y ↔ M u v)
def PartialOrderOn {σ : Type} [Ty σ] (A : σ → Prop) (E : σ → σ → Prop) : Prop :=
  (∀ x y, E x y → A x ∧ A y) ∧ (∀ x, A x → E x x) ∧
  (∀ x y, E x y → E y x → x = y) ∧ (∀ x y z, E x y → E y z → E x z)
def Supremum {σ : Type} [Ty σ] (A : σ → Prop) (E : σ → σ → Prop)
    (X : σ → Prop) (s : σ) : Prop :=
  A s ∧ (∀ x, X x → E x s) ∧ ∀ y, A y → (∀ x, X x → E x y) → E s y
def Infimum {σ : Type} [Ty σ] (A : σ → Prop) (E : σ → σ → Prop)
    (X : σ → Prop) (s : σ) : Prop :=
  A s ∧ (∀ x, X x → E s x) ∧ ∀ y, A y → (∀ x, X x → E y x) → E y s
def Joins {σ : Type} [Ty σ] (A : σ → Prop) (E : σ → σ → Prop) (x y z : σ) : Prop :=
  Supremum A E (fun u => u = x ∨ u = y) z
def Meets {σ : Type} [Ty σ] (A : σ → Prop) (E : σ → σ → Prop) (x y z : σ) : Prop :=
  Infimum A E (fun u => u = x ∨ u = y) z
def Endpoints {σ : Type} [Ty σ] (A : σ → Prop) (E : σ → σ → Prop) (o i : σ) : Prop :=
  A o ∧ A i ∧ ∀ x, A x → E o x ∧ E x i
def DistributiveOn {σ : Type} [Ty σ] (A : σ → Prop) (E : σ → σ → Prop) : Prop :=
  ∀ x y z j l r s, A x → A y → A z → Joins A E y z j → Meets A E x j l →
    Meets A E x y r → Meets A E x z s → Joins A E r s l
def CBA {σ : Type} [Ty σ] (A : σ → Prop) (E : σ → σ → Prop) : Prop :=
  PartialOrderOn A E ∧
  (∀ X : σ → Prop, (∀ x, X x → A x) → ∃ s, Supremum A E X s) ∧
  (∀ X : σ → Prop, (∀ x, X x → A x) → ∃ s, Infimum A E X s) ∧
  DistributiveOn A E ∧ ∃ o i, Endpoints A E o i ∧
    ∀ x, A x → ∃ y, A y ∧ Meets A E x y o ∧ Joins A E x y i
def Below (p q : Prop) : Prop := □ (q → p)
def EntailmentOrder (p q : Prop) : Prop := □ (p → q)

variable {α γ : Type} [Ty α] [Ty γ]
def RepresentsPower (R : γ → α → Prop) (C : γ → Prop) (A : α → Prop) : Prop :=
  (∀ c a, R c a → C c ∧ A a) ∧
  (∀ c d, C c → C d → (∀ a, R c a ↔ R d a) → c = d) ∧
  ∀ Z : α → Prop, (∀ a, Z a → A a) → ∃ c, C c ∧ ∀ a, R c a ↔ Z a

def Pow (C : γ → Prop) (A : α → Prop) : Prop := ∃ R, RepresentsPower R C A

variable {σ η : Type} [Ty σ] [Ty η]
def PowerClosed (Y : σ → Prop) : Prop :=
  ∀ A : σ → Prop, (∀ a, A a → Y a) → Smaller A Y →
    ∃ C : σ → Prop, (∀ c, C c → Y c) ∧ Smaller C Y ∧ Pow C A

def SmallAbove (H : η → Prop) (X : σ → Prop) : Prop :=
  ¬ ∃ Y : σ → Prop, (∀ y, Y y → X y) ∧ Smaller H Y ∧ PowerClosed Y

/-- H is the existing INEXACT inductive carrier over individuals. -/
def Small (X : σ → Prop) : Prop := SmallAbove (@StoneOrdinal.Ordinal e _) X

def Represented (B : σ → Prop) (E : σ → σ → Prop) : Prop :=
  ∃ p I, OrderIso I B E (Below p) EntailmentOrder

def MPAt (σ : Type) [Ty σ] : Prop :=
  ∀ B E, @CBA σ _ B E → Small B → Represented B E

end Classicism.StoneMP

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
#classicism_quote_term Classicism.StoneMP.Represented Classicism.StoneMP.CBA
  Classicism.StoneMP.Embeds Classicism.StoneMP.Smaller Classicism.StoneMP.RepresentsPower
  Classicism.StoneMP.Pow Classicism.StoneMP.PowerClosed Classicism.StoneMP.SmallAbove
  Classicism.StoneMP.Small Classicism.StoneMP.MPAt
