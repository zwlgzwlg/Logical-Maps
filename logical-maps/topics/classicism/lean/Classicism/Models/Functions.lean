import Classicism.Semantics.IdeallyFull
import Classicism.Certified.Schemas

/-!
# Categories of sets and functions

Appendix D builds every model on "a category of sets and functions" with the identity
action for `e` and the finite subsets as the ideal. The one-object models are monoids
acting on `ℕ` (`MonoidModel.lean`); the models with more than one object, which make
principles contingent, need several sets and a choice of which functions between them
are arrows. This module is that construction: objects indexed by a type, each a set, and
a class of functions between them containing the identities and closed under
composition. The action for `e` is the identity action, `W^e = W` and `h^e = h`, and the
model is the ideally full one over it (`Premodel.ideal`, a model by Proposition D.4).

`BF` at the base holds when every arrow out of it agrees, on any finite set, with a
surjection (`bf_of_approx`, from `Premodel.ideal_bf_of_approx`): the paper's argument for
the monoid of all functions on `ℕ`, which it reuses for the two-object model with `BF`
but not `□BF` (`ContingentBarcan.lean`).
-/

namespace Classicism.Meta.Intensional

open CategoryTheory

/-- A category of sets and some of the functions between them: objects indexed by
`Obj`, the object `i` the set `X i`, and the arrows `i → j` the functions `X i → X j`
satisfying `Arr`, which contains the identities and is closed under composition. -/
structure FunCat where
  Obj : Type
  X : Obj → Type
  Arr : ∀ {i j : Obj}, (X i → X j) → Prop
  arr_id : ∀ i, Arr (id : X i → X i)
  arr_comp : ∀ {i j k : Obj} {f : X i → X j} {g : X j → X k}, Arr f → Arr g → Arr (g ∘ f)

namespace FunCat

variable (F : FunCat)

/-- The objects, as the type carrying the category. -/
def Ob : Type := F.Obj

instance : SmallCategory F.Ob where
  Hom i j := {f : F.X i → F.X j // F.Arr f}
  id i := ⟨id, F.arr_id i⟩
  comp f g := ⟨g.1 ∘ f.1, F.arr_comp f.2 g.2⟩

variable {F} in
/-- An arrow, as the function it is. -/
abbrev fn {i j : F.Ob} (f : i ⟶ j) : F.X i → F.X j := (f : {f : F.X i → F.X j // F.Arr f}).1

variable {F} in
/-- A function in the class, as an arrow. -/
abbrev arr {i j : F.Ob} (f : F.X i → F.X j) (hf : F.Arr f) : i ⟶ j := (⟨f, hf⟩ : {f : F.X i → F.X j // F.Arr f})

theorem fn_id (i : F.Ob) : fn (𝟙 i) = id := rfl

theorem fn_comp {i j k : F.Ob} (f : i ⟶ j) (g : j ⟶ k) : fn (f ≫ g) = fn g ∘ fn f := rfl

variable {F} in
theorem hom_ext {i j : F.Ob} {f g : i ⟶ j} (h : fn f = fn g) : f = g := Subtype.ext h

/-- The identity action for `e`: an object's individuals are its members. -/
abbrev De : F.Ob ⥤ Type where
  obj i := F.X i
  map f := TypeCat.ofHom (fn f)

/-- The ideally full model over the category, based at `W₀`, with no constants. -/
noncomputable abbrev model (W₀ : F.Ob) (ne : ∀ i : F.Ob, Nonempty (F.X i)) :
    Premodel Signature.pure F.Ob :=
  Premodel.ideal F.De W₀ ne (fun c => nomatch c)

theorem model_isModel (W₀ : F.Ob) (ne : ∀ i : F.Ob, Nonempty (F.X i)) : (F.model W₀ ne).IsModel :=
  Premodel.ideal_isModel F.De

/-- **`BF` from approximation by surjections**: if every arrow out of the base agrees on
any finite set with a surjective arrow, `BF_σ` holds at the base for every `σ`. -/
theorem bf_of_approx (W₀ : F.Ob) (ne : ∀ i : F.Ob, Nonempty (F.X i))
    (happrox : ∀ {V : F.Ob} (k : W₀ ⟶ V) (N : Set (F.X W₀)), N.Finite →
      ∃ j : W₀ ⟶ V, (∀ x ∈ N, fn k x = fn j x) ∧ Function.Surjective (fn j)) (σ : Ty) :
    (F.model W₀ ne).HoldsSentence (Sentence.bf σ) :=
  Premodel.ideal_bf_of_approx F.De (fun k N hN => happrox k N hN) σ

end FunCat

end Classicism.Meta.Intensional
