import Classicism.Syntax.Blocks

/-!
# Vectorization: a type variable replaced by a list of types

The translation behind the list forms of the map's principles. An **assignment** `θ` sends
each type variable to a list of types. Along it, every type becomes a list of types (a
one-element list except at an assigned variable), every context a context (each variable
of an assigned type becoming a block of variables), and every term a tuple of terms (a
single term except at an assigned variable, where the term, necessarily a variable, becomes
its block). A function from a variable type becomes a function of the block, a quantifier
over it a block of quantifiers, identity at it the conjunction of identities.

There are two translations, equal up to conversion:

- `Term.vecG`, the **generic** translation, compositional in every term former: an
  application becomes `appBlock`, an abstraction `lamBlock`, `∀σ` the block constant
  `allC`. It commutes with renaming and substitution on the nose, which is what the
  proofs need.
- `Term.vec`, the **readable** translation, which treats the quoter's binding forms as
  units, `∀x:σ. φ` becoming `∀x₁ … ∀xₙ. φ'` and `a = b` the conjunction of identities,
  where the generic one leaves a β-redex. The list forms of the map's principles are
  stated through it, and come out as one would write them.

Proved here: the generic translation commutes with renaming and substitution
(`Term.vecG_subst`), preserves conversion (`Term.vecG_conv`, a δ-step becoming the
operation's unfolding over the whole block) and carries a hole to a hole
(`Hole.vecG1_plug`); the readable translation converts to it (`Term.vec_conv_vecG`), and
computes the binding forms as units by `rfl` (`Term.vec1_forall`, `Term.vec1_eq`, …). The
vectorization theorem, that derivability is preserved, is in
`Syntax/VectorizeDerivable.lean`.

The translation of types is reducible, so that a type's list unfolds wherever its outer
form is known, as `rw` needs when it rewrites a translated term.
-/

namespace Classicism.Meta

variable {Sig : Signature}

/-! ### Assignments and the translation of types -/

/-- An assignment of lists of types to type variables. -/
abbrev Assign : Type := Nat → List Ty

namespace Assign

/-- Each variable to itself. -/
def id : Assign := fun i => [.var i]

/-- The variable `i` to `σs`, every other variable to itself. -/
def single (i : Nat) (σs : List Ty) : Assign := fun j => if j = i then σs else [.var j]

/-- The variable `j` to the `j`-th list of `ls`, every variable beyond them to itself. -/
def ofList (ls : List (List Ty)) : Assign := fun j => ls.getD j [.var j]

end Assign

mutual
  /-- The list of types a type becomes. -/
  @[reducible] def Ty.vec (θ : Assign) : Ty → List Ty
    | .e => [.e]
    | .rel ρ => [.rel (RTy.vec θ ρ)]
    | .var i => θ i
  /-- The relational type a relational type becomes. -/
  @[reducible] def RTy.vec (θ : Assign) : RTy → RTy
    | .t => .t
    | .arr σ ρ => Ty.vec θ σ ⇒* RTy.vec θ ρ
end

@[simp] theorem Ty.vec_e (θ : Assign) : Ty.e.vec θ = [.e] := rfl
@[simp] theorem Ty.vec_rel (θ : Assign) (ρ : RTy) : (Ty.rel ρ).vec θ = [.rel (ρ.vec θ)] := rfl
@[simp] theorem Ty.vec_var (θ : Assign) (i : Nat) : (Ty.var i).vec θ = θ i := rfl
@[simp] theorem RTy.vec_t (θ : Assign) : RTy.t.vec θ = .t := rfl
@[simp] theorem RTy.vec_arr (θ : Assign) (σ : Ty) (ρ : RTy) :
    (σ ⇒ ρ).vec θ = σ.vec θ ⇒* ρ.vec θ := rfl

mutual
  /-- A closed type is unchanged. -/
  theorem Ty.vec_closed (θ : Assign) : ∀ {σ : Ty}, σ.Closed → σ.vec θ = [σ]
    | .e, _ => rfl
    | .rel ρ, h => by rw [Ty.vec_rel, RTy.vec_closed θ h]
  /-- A closed relational type is unchanged. -/
  theorem RTy.vec_closed (θ : Assign) : ∀ {ρ : RTy}, ρ.Closed → ρ.vec θ = ρ
    | .t, _ => rfl
    | .arr σ ρ, h => by rw [RTy.vec_arr, Ty.vec_closed θ h.1, RTy.vec_closed θ h.2]
end

/-- Every type of a list is closed. -/
abbrev Ty.AllClosed (σs : List Ty) : Prop := ∀ σ ∈ σs, σ.Closed

theorem Ty.allClosed_singleton {σ : Ty} (h : σ.Closed) : Ty.AllClosed [σ] := by
  simpa [Ty.AllClosed] using h

theorem Ty.AllClosed.head {σ : Ty} {σs : List Ty} (h : Ty.AllClosed (σ :: σs)) : σ.Closed :=
  h σ List.mem_cons_self

theorem Ty.AllClosed.tail {σ : Ty} {σs : List Ty} (h : Ty.AllClosed (σ :: σs)) :
    Ty.AllClosed σs :=
  fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- The context a context becomes: each variable's type replaced by its list, as a block. -/
@[reducible] def Ctx.vec (θ : Assign) : Ctx → Ctx
  | [] => []
  | σ :: Γ => Ctx.block (σ.vec θ) (Ctx.vec θ Γ)

@[simp] theorem Ctx.vec_nil (θ : Assign) : Ctx.vec θ [] = [] := rfl
@[simp] theorem Ctx.vec_cons (θ : Assign) (σ : Ty) (Γ : Ctx) :
    Ctx.vec θ (σ :: Γ) = Ctx.block (σ.vec θ) (Ctx.vec θ Γ) := rfl

/-! ### Variables, and the generic translation of terms -/

/-- The block of variables of a variable's type's list, renamed by `r` after the
weakenings past the blocks of the variables after it, composed into one renaming. -/
def Var.vecRen (θ : Assign) :
    ∀ {Γ Δ : Ctx} {σ : Ty}, Var Γ σ → Ren (Ctx.vec θ Γ) Δ → Terms Sig Δ (σ.vec θ)
  | σ :: Γ, _, _, .zero, r => (Terms.vars (σ.vec θ) (Ctx.vec θ Γ)).rename r
  | τ :: _, _, _, .succ v, r => Var.vecRen θ v (Ren.comp r (Ren.wkBlock (τ.vec θ)))

/-- A variable becomes the block of variables of its type's list, weakened past the blocks
of the variables after it. The weakenings are composed into one renaming before they act
on the block: where the block's list is not known, renaming it twice does not compute to
renaming it once by the composite, and two translations that reach the same variable
across different binders would differ. -/
def Var.vec (θ : Assign) : ∀ {Γ : Ctx} {σ : Ty}, Var Γ σ → Terms Sig (Ctx.vec θ Γ) (σ.vec θ)
  | σ :: Γ, _, .zero => Terms.vars (σ.vec θ) (Ctx.vec θ Γ)
  | τ :: _, _, .succ v => Var.vecRen θ v (Ren.wkBlock (τ.vec θ))

theorem Var.vecRen_eq (θ : Assign) : ∀ {Γ Δ : Ctx} {σ : Ty} (v : Var Γ σ)
    (r : Ren (Ctx.vec θ Γ) Δ), Var.vecRen (Sig := Sig) θ v r = (Var.vec θ v).rename r
  | _ :: _, _, _, .zero, _ => rfl
  | τ :: _, _, _, .succ v, r => by
    show Var.vecRen θ v _ = (Var.vecRen θ v (Ren.wkBlock (τ.vec θ))).rename r
    rw [Var.vecRen_eq θ v, Var.vecRen_eq θ v, Terms.rename_rename]

theorem Var.vec_succ (θ : Assign) {Γ : Ctx} {σ τ : Ty} (v : Var Γ σ) :
    Var.vec (Sig := Sig) θ (Var.succ v : Var (τ :: Γ) σ) = (Var.vec θ v).rename (Ren.wkBlock (τ.vec θ)) :=
  Var.vecRen_eq θ v _

/-- The signature's constants have types the assignment leaves alone (true of every
signature whose constants have closed types, `Ty.vec_closed`). -/
abbrev Signature.VecFixed (Sig : Signature) (θ : Assign) : Prop :=
  ∀ c : Sig.Const, (Sig.typeOf c).vec θ = [Sig.typeOf c]

/-- Retype a tuple along an equation of type lists. -/
def Terms.cast {Γ : Ctx} {σs σs' : List Ty} (h : σs = σs') (as : Terms Sig Γ σs) : Terms Sig Γ σs' :=
  h ▸ as

theorem Terms.subst_cast {Γ Δ : Ctx} (s : Sub Sig Γ Δ) {σs σs' : List Ty} (h : σs = σs')
    (as : Terms Sig Γ σs) : (Terms.cast h as).subst s = Terms.cast h (as.subst s) := by
  subst h; rfl

/-- The generic translation of a term: compositional in every term former. -/
def Term.vecG (θ : Assign) (hc : Sig.VecFixed θ) :
    ∀ {Γ : Ctx} {σ : Ty}, Term Sig Γ σ → Terms Sig (Ctx.vec θ Γ) (σ.vec θ)
  | _, _, .var v => Var.vec θ v
  | _, _, .const c => Terms.cast (hc c).symm (.single (.const c))
  | _, _, .app f a => .single (Term.appBlock (vecG θ hc f).head1 (vecG θ hc a))
  | _, _, .lam (σ := σ) b => .single (Term.lamBlock (σ.vec θ) (vecG θ hc b).head1)
  | _, _, .and => .single .and
  | _, _, .or => .single .or
  | _, _, .not => .single .not
  | _, _, .all σ => .single (Term.allC (σ.vec θ))
  | _, _, .ex σ => .single (Term.exC (σ.vec θ))
  | _, _, .eq σ => .single (Term.eqC (σ.vec θ))
  | _, _, .constR ρ => .single (.constR (ρ.vec θ))
  | _, _, .negR ρ => .single (.negR (ρ.vec θ))
  | _, _, .andR ρ => .single (.andR (ρ.vec θ))
  | _, _, .orR ρ => .single (.orR (ρ.vec θ))
  | _, _, .coextR ρ => .single (.coextR (ρ.vec θ))
  | _, _, .boxR ρ => .single (.boxR (ρ.vec θ))
  | _, _, .boxImpR ρ => .single (.boxImpR (ρ.vec θ))

/-- The generic translation of a term of a relational type, a single term. -/
abbrev Term.vecG1 (θ : Assign) (hc : Sig.VecFixed θ) {Γ : Ctx} {ρ : RTy} (a : Term Sig Γ ρ) :
    Term Sig (Ctx.vec θ Γ) (ρ.vec θ) :=
  (a.vecG θ hc).head1

section
variable (θ : Assign) (hc : Sig.VecFixed θ)

theorem Term.vecG_app {Γ : Ctx} {σ : Ty} {ρ : RTy} (f : Term Sig Γ (σ ⇒ ρ)) (a : Term Sig Γ σ) :
    (Term.app f a).vecG θ hc = .single (Term.appBlock (f.vecG1 θ hc) (a.vecG θ hc)) := rfl

theorem Term.vecG_lam {Γ : Ctx} {σ : Ty} {ρ : RTy} (b : Term Sig (σ :: Γ) ρ) :
    (Term.lam b).vecG θ hc = .single (Term.lamBlock (σ.vec θ) (b.vecG1 θ hc)) := rfl

/-! The propositional connectives are translated as themselves. -/

theorem Term.vecG1_conj {Γ : Ctx} (p q : Formula Sig Γ) :
    (Term.conj p q).vecG1 θ hc = Term.conj (p.vecG1 θ hc) (q.vecG1 θ hc) := rfl
theorem Term.vecG1_disj {Γ : Ctx} (p q : Formula Sig Γ) :
    (Term.disj p q).vecG1 θ hc = Term.disj (p.vecG1 θ hc) (q.vecG1 θ hc) := rfl
theorem Term.vecG1_neg {Γ : Ctx} (p : Formula Sig Γ) :
    (Term.neg p).vecG1 θ hc = Term.neg (p.vecG1 θ hc) := rfl
theorem Term.vecG1_imp {Γ : Ctx} (p q : Formula Sig Γ) :
    (Term.imp p q).vecG1 θ hc = Term.imp (p.vecG1 θ hc) (q.vecG1 θ hc) := rfl

/-! ### Vectorizing a substitution -/

/-- The substitution for the variables after the first. -/
def Sub.tail {Γ Δ : Ctx} {σ : Ty} (s : Sub Sig (σ :: Γ) Δ) : Sub Sig Γ Δ := fun τ v => s τ (.succ v)

/-- A substitution, vectorized: the block of each variable goes to the translation of the
variable's image. -/
def Sub.vec : ∀ {Γ Δ : Ctx}, Sub Sig Γ Δ → Sub Sig (Ctx.vec θ Γ) (Ctx.vec θ Δ)
  | [], _, _ => fun _ v => nomatch v
  | σ :: _, _, s => Sub.consBlock ((s σ .zero).vecG θ hc) (Sub.vec s.tail)

theorem Sub.vec_cons {Γ Δ : Ctx} {σ : Ty} (s : Sub Sig (σ :: Γ) Δ) :
    Sub.vec θ hc s = Sub.consBlock ((s σ .zero).vecG θ hc) (Sub.vec θ hc s.tail) := rfl

/-- On a variable, the vectorized substitution is the translation of the variable's
image. -/
theorem Var.vec_subst : ∀ {Γ Δ : Ctx} {σ : Ty} (v : Var Γ σ) (s : Sub Sig Γ Δ),
    (Var.vec θ v).subst (Sub.vec θ hc s) = (s σ v).vecG θ hc
  | _ :: _, _, _, .zero, s => Terms.vars_subst_consBlock _ _
  | τ :: _, _, _, .succ v, s => by
    rw [Var.vec_succ, Sub.vec_cons, Terms.subst_rename, Sub.compRen_consBlock_wkBlock]
    exact Var.vec_subst v s.tail

/-- If one substitution's images translate to another's, renamed, so do the vectorized
substitutions. -/
theorem Sub.vec_of_rename : ∀ {Γ Δ Δ' : Ctx} (s : Sub Sig Γ Δ) (s' : Sub Sig Γ Δ')
    (r : Ren (Ctx.vec θ Δ) (Ctx.vec θ Δ')),
    (∀ τ v, (s' τ v).vecG θ hc = ((s τ v).vecG θ hc).rename r) →
    Sub.vec θ hc s' = Ren.compSub r (Sub.vec θ hc s)
  | [], _, _, _, _, _, _ => by funext τ v; exact nomatch v
  | σ :: _, _, _, s, s', r, h => by
    rw [Sub.vec_cons, Sub.vec_cons, h σ .zero,
      Sub.vec_of_rename s.tail s'.tail r (fun τ v => h τ (.succ v))]
    exact (Ren.compSub_consBlock r _ _).symm

theorem Sub.vec_id : ∀ {Γ : Ctx}, Sub.vec θ hc (Sub.id : Sub Sig Γ Γ) = Sub.id
  | [] => by funext τ v; exact nomatch v
  | σ :: Γ => by
    rw [Sub.vec_cons]
    have e : Sub.vec θ hc (Sub.tail (Sub.id : Sub Sig (σ :: Γ) _))
        = Ren.compSub (Ren.wkBlock (σ.vec θ)) (Sub.vec θ hc (Sub.id : Sub Sig Γ Γ)) :=
      Sub.vec_of_rename θ hc Sub.id _ _ (fun _ _ => Var.vec_succ θ _)
    rw [e, Sub.vec_id]
    exact Sub.consBlock_vars_wkBlock (σ.vec θ) (Ctx.vec θ Γ)

/-- A renaming lifted under a binder, vectorized: lifted under the block. -/
theorem Sub.vec_lift_ofRen {Γ Δ : Ctx} {σ : Ty} (r : Ren Γ Δ) :
    Sub.vec θ hc (Sub.ofRen (Sig := Sig) (Ren.lift r (σ := σ)))
      = Sub.liftBlock (σ.vec θ) (Sub.vec θ hc (Sub.ofRen r)) := by
  rw [Sub.vec_cons]
  have e : Sub.vec θ hc (Sub.tail (Sub.ofRen (Sig := Sig) (Ren.lift r (σ := σ))))
      = Ren.compSub (Ren.wkBlock (σ.vec θ)) (Sub.vec θ hc (Sub.ofRen r)) :=
    Sub.vec_of_rename θ hc _ _ _ (fun _ _ => Var.vec_succ θ _)
  rw [e]
  exact Sub.consBlock_vars_compSub (σ.vec θ) _

/-- The commutation with substitution, for every substitution in a family closed under
lifting whose lifts vectorize to lifts over the block. Proved once, used twice: first for
renamings, then, with what that gives, for all substitutions. -/
private theorem vecG_subst_of (P : ∀ {Γ Δ : Ctx}, Sub Sig Γ Δ → Prop)
    (hP : ∀ {Γ Δ : Ctx} {σ : Ty} (s : Sub Sig Γ Δ), P s → P (Sub.lift s (σ := σ)))
    (hL : ∀ {Γ Δ : Ctx} {σ : Ty} (s : Sub Sig Γ Δ), P s →
      Sub.vec θ hc (Sub.lift s (σ := σ)) = Sub.liftBlock (σ.vec θ) (Sub.vec θ hc s)) :
    ∀ {Γ Δ : Ctx} {σ : Ty} (a : Term Sig Γ σ) (s : Sub Sig Γ Δ), P s →
      (a.subst s).vecG θ hc = (a.vecG θ hc).subst (Sub.vec θ hc s)
  | _, _, _, .var v, s, _ => (Var.vec_subst θ hc v s).symm
  | _, _, _, .const c, s, _ => by
    show _ = (Terms.cast (hc c).symm (.single (.const c))).subst _
    rw [Terms.subst_cast]; rfl
  | _, _, _, .app f a, s, h => by
    have e := Term.subst_appBlock (Sub.vec θ hc s) (f.vecG1 θ hc) (a.vecG θ hc)
    calc (Term.app (f.subst s) (a.subst s)).vecG θ hc
        = .single (Term.appBlock ((f.subst s).vecG1 θ hc) ((a.subst s).vecG θ hc)) := rfl
      _ = .single (Term.appBlock (((f.vecG θ hc).subst (Sub.vec θ hc s)).head1)
            ((a.vecG θ hc).subst (Sub.vec θ hc s))) := by
          rw [Term.vecG1, vecG_subst_of P hP hL f s h, vecG_subst_of P hP hL a s h]
      _ = .single ((Term.appBlock (f.vecG1 θ hc) (a.vecG θ hc)).subst (Sub.vec θ hc s)) :=
          congrArg Terms.single e.symm
  | _, _, _, .lam (σ := σ) b, s, h => by
    have e := Term.subst_lamBlock (σ.vec θ) (Sub.vec θ hc s) (b.vecG1 θ hc)
    calc ((Term.lam b).subst s).vecG θ hc
        = .single (Term.lamBlock (σ.vec θ) ((b.subst (Sub.lift s)).vecG1 θ hc)) := rfl
      _ = .single (Term.lamBlock (σ.vec θ)
            (((b.vecG θ hc).subst (Sub.liftBlock (σ.vec θ) (Sub.vec θ hc s))).head1)) := by
          rw [Term.vecG1, vecG_subst_of P hP hL b (Sub.lift s) (hP s h), hL s h]
      _ = .single ((Term.lamBlock (σ.vec θ) (b.vecG1 θ hc)).subst (Sub.vec θ hc s)) :=
          congrArg Terms.single e.symm
  | _, _, _, .and, _, _ | _, _, _, .or, _, _ | _, _, _, .not, _, _ => rfl
  | _, _, _, .all σ, s, _ => by
    show Terms.single _ = Terms.single ((Term.allC _).subst _); rw [Term.subst_allC]
  | _, _, _, .ex σ, s, _ => by
    show Terms.single _ = Terms.single ((Term.exC _).subst _); rw [Term.subst_exC]
  | _, _, _, .eq σ, s, _ => by
    show Terms.single _ = Terms.single ((Term.eqC _).subst _); rw [Term.subst_eqC]
  | _, _, _, .constR _, _, _ | _, _, _, .negR _, _, _ | _, _, _, .andR _, _, _
  | _, _, _, .orR _, _, _ | _, _, _, .coextR _, _, _ | _, _, _, .boxR _, _, _
  | _, _, _, .boxImpR _, _, _ => rfl

/-- The translation commutes with renaming. -/
theorem Term.vecG_rename {Γ Δ : Ctx} {σ : Ty} (r : Ren Γ Δ) (a : Term Sig Γ σ) :
    (a.rename r).vecG θ hc = (a.vecG θ hc).subst (Sub.vec θ hc (Sub.ofRen r)) := by
  rw [Term.rename_eq_subst]
  exact vecG_subst_of θ hc (fun s => ∃ r, s = Sub.ofRen r)
    (fun _ ⟨r, e⟩ => ⟨Ren.lift r, e ▸ Sub.lift_ofRen r⟩)
    (fun _ ⟨r, e⟩ => by subst e; rw [Sub.lift_ofRen]; exact Sub.vec_lift_ofRen θ hc r)
    a (Sub.ofRen r) ⟨r, rfl⟩

/-- Weakening past a variable, vectorized: weakening past its block. -/
theorem Sub.vec_ofRen_shift {Γ : Ctx} {σ : Ty} :
    Sub.vec θ hc (Sub.ofRen (Sig := Sig) (Ren.shift (Γ := Γ) (σ := σ)))
      = Sub.ofRen (Ren.wkBlock (σ.vec θ)) := by
  rw [Sub.vec_of_rename θ hc (Sub.id : Sub Sig Γ Γ) (Sub.ofRen (Ren.shift (σ := σ)))
    (Ren.wkBlock (σ.vec θ)) (fun _ v => Var.vec_succ θ v),
    Sub.vec_id]
  rfl

theorem Term.vecG_weaken {Γ : Ctx} {σ τ : Ty} (a : Term Sig Γ σ) :
    (a.weaken (τ := τ)).vecG θ hc = (a.vecG θ hc).rename (Ren.wkBlock (τ.vec θ)) := by
  rw [Term.weaken, Term.vecG_rename, Sub.vec_ofRen_shift, Terms.rename_eq_subst]

/-- A substitution lifted under a binder, vectorized: lifted under the block. -/
theorem Sub.vec_lift {Γ Δ : Ctx} {σ : Ty} (s : Sub Sig Γ Δ) :
    Sub.vec θ hc (Sub.lift s (σ := σ)) = Sub.liftBlock (σ.vec θ) (Sub.vec θ hc s) := by
  rw [Sub.vec_cons]
  have e : Sub.vec θ hc (Sub.tail (Sub.lift s (σ := σ)))
      = Ren.compSub (Ren.wkBlock (σ.vec θ)) (Sub.vec θ hc s) :=
    Sub.vec_of_rename θ hc _ _ _ (fun _ v => Term.vecG_weaken θ hc (s _ v))
  rw [e]
  exact Sub.consBlock_vars_compSub (σ.vec θ) _

/-- **The translation commutes with substitution**, on the nose. -/
theorem Term.vecG_subst {Γ Δ : Ctx} {σ : Ty} (a : Term Sig Γ σ) (s : Sub Sig Γ Δ) :
    (a.subst s).vecG θ hc = (a.vecG θ hc).subst (Sub.vec θ hc s) :=
  vecG_subst_of θ hc (fun _ => True) (fun _ _ => trivial) (fun s _ => Sub.vec_lift θ hc s) a s trivial

theorem Term.vecG_instantiate {Γ : Ctx} {σ τ : Ty} (b : Term Sig (σ :: Γ) τ) (a : Term Sig Γ σ) :
    (b.instantiate a).vecG θ hc = (b.vecG θ hc).subst (Sub.consBlock (a.vecG θ hc) Sub.id) := by
  rw [Term.instantiate, Term.vecG_subst, Sub.vec_cons]
  congr 2
  exact Sub.vec_id θ hc

/-- A sentence placed in a context: its translation, placed in the translated context. -/
theorem Term.vecG1_close {Γ : Ctx} (a : Sentence Sig) :
    (a.close (Γ := Γ)).vecG1 θ hc = (a.vecG1 θ hc).close := by
  rw [Term.vecG1, Term.close, Term.vecG_rename, Terms.head1_subst, Term.close, Term.rename_eq_subst]
  congr 1
  funext τ v
  exact nomatch v

/-! ### Conversion is preserved

A β-step becomes a block β-step, an η-step a block η-step, and a δ-step the unfolding of
the operation over the whole block (`Conv.negR_block` and its kin). -/

/-- An immediate δ-conversion, translated. -/
theorem Term.vecG_delta : ∀ {Γ : Ctx} {σ : Ty} {a b : Term Sig Γ σ},
    a.unfoldR = some b → Terms.Conv (a.vecG θ hc) (b.vecG θ hc)
  | _, _, .constR .t, _, h => by cases h; exact .cons (Conv.delta rfl) .nil
  | _, _, .constR (.arr σ ρ), _, h => by
    cases h; exact .cons (Conv.constR_block (σ.vec θ) (ρ.vec θ)) .nil
  | _, _, .negR .t, _, h => by cases h; exact .cons (Conv.delta rfl) .nil
  | _, _, .negR (.arr σ ρ), _, h => by
    cases h; exact .cons (Conv.negR_block (σ.vec θ) (ρ.vec θ)) .nil
  | _, _, .andR .t, _, h => by cases h; exact .cons (Conv.delta rfl) .nil
  | _, _, .andR (.arr σ ρ), _, h => by
    cases h; exact .cons (Conv.andR_block (σ.vec θ) (ρ.vec θ)) .nil
  | _, _, .orR .t, _, h => by cases h; exact .cons (Conv.delta rfl) .nil
  | _, _, .orR (.arr σ ρ), _, h => by
    cases h; exact .cons (Conv.orR_block (σ.vec θ) (ρ.vec θ)) .nil
  | _, _, .coextR .t, _, h => by cases h; exact .cons (Conv.delta rfl) .nil
  | _, _, .coextR (.arr σ ρ), _, h => by
    cases h
    exact .cons (Conv.trans (Conv.coextR_block (σ.vec θ) (ρ.vec θ))
      (Conv.lam_congr (Conv.lam_congr (Conv.symm (Conv.allC_lamBlock _ _))))) .nil
  | _, _, .boxR .t, _, h => by cases h; exact .cons (Conv.delta rfl) .nil
  | _, _, .boxR (.arr σ ρ), _, h => by
    cases h; exact .cons (Conv.boxR_block (σ.vec θ) (ρ.vec θ)) .nil
  | _, _, .boxImpR .t, _, h => by cases h; exact .cons (Conv.delta rfl) .nil
  | _, _, .boxImpR (.arr σ ρ), _, h => by
    cases h
    exact .cons (Conv.trans (Conv.boxImpR_block (σ.vec θ) (ρ.vec θ))
      (Conv.lam_congr (Conv.lam_congr (Conv.symm (Conv.allC_lamBlock _ _))))) .nil
  | _, _, .var _, _, h | _, _, .const _, _, h | _, _, .app _ _, _, h | _, _, .lam _, _, h
  | _, _, .and, _, h | _, _, .or, _, h | _, _, .not, _, h | _, _, .all _, _, h
  | _, _, .ex _, _, h | _, _, .eq _, _, h => by cases h

/-- A one-step conversion, translated: a conversion of each component. -/
theorem Term.vecG_step : ∀ {Γ : Ctx} {σ : Ty} {a b : Term Sig Γ σ},
    Step BetaEta a b → Terms.Conv (a.vecG θ hc) (b.vecG θ hc)
  | _, _, _, _, .here (.inl (.intro b a)) => by
    rw [Term.vecG_instantiate]
    exact .cons (Conv.appBlock_lamBlock _ _ _) .nil
  | _, _, _, _, .here (.inr (.inl (.intro (σ := σ) f))) => by
    have e : (f.weaken (τ := σ)).vecG1 θ hc = (f.vecG1 θ hc).rename (Ren.wkBlock (σ.vec θ)) := by
      rw [Term.vecG1, Term.vecG_weaken]; rfl
    refine Terms.Conv.of_head1 ?_
    show Term.lamBlock (σ.vec θ) (Term.appBlock ((f.weaken (τ := σ)).vecG1 θ hc)
      (Terms.vars (σ.vec θ) _)) ≡ f.vecG1 θ hc
    rw [e]
    exact Conv.lamBlock_appBlock _ _
  | _, _, _, _, .here (.inr (.inr h)) => Term.vecG_delta θ hc h
  | _, _, _, _, .appL h => .cons (Conv.appBlock_congr (Term.vecG_step h).head1 (Terms.Conv.refl _)) .nil
  | _, _, _, _, .appR h => .cons (Conv.appBlock_congr (Conv.refl _) (Term.vecG_step h)) .nil
  | _, _, _, _, .lam h => .cons (Conv.lamBlock_congr _ (Term.vecG_step h).head1) .nil

/-- **Conversion is preserved.** -/
theorem Term.vecG_conv {Γ : Ctx} {σ : Ty} {a b : Term Sig Γ σ} (h : a ≡ b) :
    Terms.Conv (a.vecG θ hc) (b.vecG θ hc) := by
  induction h with
  | rel h => exact Term.vecG_step θ hc h
  | refl _ => exact Terms.Conv.refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ### Holes

A hole for a formula lies under relational types only: the subterm containing it has a
relational type at every level, since an application and an abstraction always do, and a
term of type `e` or of a type variable with a hole in it would be the hole itself. So a
hole is translated along with its context, as a hole of the same kind. -/

/-- The translation of a hole whose type and whose hole are relational. -/
def Hole.vec : ∀ {Γ Γ' : Ctx} {ρ ρ' : RTy}, Hole Sig Γ (Ty.rel ρ) Γ' (Ty.rel ρ') →
    Hole Sig (Ctx.vec θ Γ) (Ty.rel (ρ.vec θ)) (Ctx.vec θ Γ') (Ty.rel (ρ'.vec θ))
  | _, _, _, _, .hole => .hole
  | _, _, _, _, .appL C b => Hole.appLBlock (Hole.vec C) (b.vecG θ hc)
  | _, _, _, _, .appR (σ := .rel _) f C => .appR (f.vecG1 θ hc) (Hole.vec C)
  | _, _, _, _, .appR (σ := .e) _ C => nomatch C
  | _, _, _, _, .appR (σ := .var _) _ C => nomatch C
  | _, _, _, _, .lam (σ := σ) C => Hole.lamBlock (σ.vec θ) (Hole.vec C)

/-- Filling a hole, translated: the translated hole, filled with the translation. -/
theorem Hole.vecG1_plug : ∀ {Γ Γ' : Ctx} {ρ ρ' : RTy} (C : Hole Sig Γ (Ty.rel ρ) Γ' (Ty.rel ρ'))
    (P : Term Sig Γ' ρ'), (C.plug P).vecG1 θ hc = (C.vec θ hc).plug (P.vecG1 θ hc)
  | _, _, _, _, .hole, _ => by rw [Hole.vec]; rfl
  | _, _, _, _, .appL C b, P => by
    show Term.appBlock ((C.plug P).vecG1 θ hc) (b.vecG θ hc) = _
    rw [Hole.vecG1_plug C P, Hole.vec, Hole.plug_appLBlock]
  | _, _, _, _, .appR (σ := .rel _) f C, P => by
    show Term.app (f.vecG1 θ hc) ((C.plug P).vecG1 θ hc) = _
    rw [Hole.vecG1_plug C P, Hole.vec]; rfl
  | _, _, _, _, .appR (σ := .e) _ C, _ => nomatch C
  | _, _, _, _, .appR (σ := .var _) _ C, _ => nomatch C
  | _, _, _, _, .lam (σ := σ) C, P => by
    show Term.lamBlock (σ.vec θ) ((C.plug P).vecG1 θ hc) = _
    rw [Hole.vecG1_plug C P, Hole.vec, Hole.plug_lamBlock]

end

/-! ### The readable translation

The generic translation of `∀x:σ. φ`, which the quoter writes `all σ (λx. φ)`, is the block
quantifier applied to a block abstraction: a β-redex, where one wants `∀x₁ … ∀xₙ. φ'`. And
the generic translation of `a = b` is the block identity applied to two tuples, where one
wants the conjunction of identities. The readable translation treats these forms as units.

It is computed by one recursion on the term, `Term.rec`, which yields beside each
subterm's translation a **view** of the subterm, recording what an application of it
needs to know: for an abstraction, the body of its translation; for a function that is
translated specially when applied (`∀σ`, `∃σ`, `=σ` and `=σ a`), how. The view is
defined by recursion on the type, so its shape is known wherever the type's outer form
is, which an application's function always has. No step inspects a type, so the
translation computes on terms whose types are Lean variables.

That the readable translation converts to the generic one is proved by a logical
relation on views, `Ty.VecSound`. -/

section
variable (Sig : Signature) (θ : Assign)

mutual
  /-- The view of a term of a type, beside its translation. -/
  def Ty.VecView (Γ : Ctx) : Ty → Type
    | .rel ρ => RTy.VecView Γ ρ
    | .e => PUnit
    | .var _ => PUnit
  /-- The view of a term of a relational type: for a function, the body of its
  translation if that is an abstraction, and its translation applied to an argument,
  given the argument's translation and view, if that is not the generic one. -/
  def RTy.VecView (Γ : Ctx) : RTy → Type
    | .t => PUnit
    | .arr σ ρ =>
      Option (Term Sig (Ctx.block (σ.vec θ) (Ctx.vec θ Γ)) (ρ.vec θ)) ×
      (Terms Sig (Ctx.vec θ Γ) (σ.vec θ) × Ty.VecView Γ σ →
        Option (Term Sig (Ctx.vec θ Γ) (ρ.vec θ) × RTy.VecView Γ ρ))
end

end

section
variable {θ : Assign}

mutual
  /-- The view that records nothing. -/
  def Ty.VecView.none {Γ : Ctx} : ∀ σ : Ty, Ty.VecView Sig θ Γ σ
    | .rel ρ => RTy.VecView.none ρ
    | .e => ⟨⟩
    | .var _ => ⟨⟩
  /-- The view that records nothing. -/
  def RTy.VecView.none {Γ : Ctx} : ∀ ρ : RTy, RTy.VecView Sig θ Γ ρ
    | .t => ⟨⟩
    | .arr _ _ => (Option.none, fun _ => Option.none)
end

end

/-- A term's readable translation, and its view. Through `Term.rec` directly, as
`Term.rename` is, since the kernel evaluates it; and so not compiled, as it is never run. -/
noncomputable def Term.vecData (θ : Assign) (hc : Sig.VecFixed θ) {Γ : Ctx} {σ : Ty} (t : Term Sig Γ σ) :
    Terms Sig (Ctx.vec θ Γ) (σ.vec θ) × Ty.VecView Sig θ Γ σ :=
  Term.rec (motive := fun Γ σ _ => Terms Sig (Ctx.vec θ Γ) (σ.vec θ) × Ty.VecView Sig θ Γ σ)
    (var := fun v => (Var.vec θ v, Ty.VecView.none _))
    (const := fun c => (Terms.cast (hc c).symm (.single (.const c)), Ty.VecView.none _))
    (app := fun {_ _ ρ} _ _ f a =>
      match f.2.2 a with
      | some d => (.single d.1, d.2)
      | Option.none => (.single (Term.appBlock f.1.head1 a.1), RTy.VecView.none ρ))
    (lam := fun {_ σ _} _ b =>
      (.single (Term.lamBlock (σ.vec θ) b.1.head1), (some b.1.head1, fun _ => Option.none)))
    (and := (.single .and, Ty.VecView.none _))
    (or := (.single .or, Ty.VecView.none _))
    (not := (.single .not, Ty.VecView.none _))
    (all := fun σ => (.single (Term.allC (σ.vec θ)), (Option.none,
      fun a => a.2.1.map fun body => (Term.forallBlock (σ.vec θ) body, ⟨⟩))))
    (ex := fun σ => (.single (Term.exC (σ.vec θ)), (Option.none,
      fun a => a.2.1.map fun body => (Term.existsBlock (σ.vec θ) body, ⟨⟩))))
    (eq := fun σ => (.single (Term.eqC (σ.vec θ)), (Option.none,
      fun a => some (Term.appBlock (Term.eqC (σ.vec θ)) a.1, (Option.none,
        fun b => some (Term.eqBlock a.1 b.1, ⟨⟩))))))
    (constR := fun ρ => (.single (.constR (ρ.vec θ)), Ty.VecView.none _))
    (negR := fun ρ => (.single (.negR (ρ.vec θ)), Ty.VecView.none _))
    (andR := fun ρ => (.single (.andR (ρ.vec θ)), Ty.VecView.none _))
    (orR := fun ρ => (.single (.orR (ρ.vec θ)), Ty.VecView.none _))
    (coextR := fun ρ => (.single (.coextR (ρ.vec θ)), Ty.VecView.none _))
    (boxR := fun ρ => (.single (.boxR (ρ.vec θ)), Ty.VecView.none _))
    (boxImpR := fun ρ => (.single (.boxImpR (ρ.vec θ)), Ty.VecView.none _))
    t

/-- **The readable translation** of a term. -/
noncomputable def Term.vec (θ : Assign) (hc : Sig.VecFixed θ) {Γ : Ctx} {σ : Ty} (t : Term Sig Γ σ) :
    Terms Sig (Ctx.vec θ Γ) (σ.vec θ) :=
  (t.vecData θ hc).1

/-- The readable translation of a term of a relational type, a single term. -/
noncomputable abbrev Term.vec1 (θ : Assign) (hc : Sig.VecFixed θ) {Γ : Ctx} {ρ : RTy}
    (a : Term Sig Γ ρ) : Term Sig (Ctx.vec θ Γ) (ρ.vec θ) :=
  (a.vec θ hc).head1

section
variable (θ : Assign) (hc : Sig.VecFixed θ)

/-! The binding forms, as units. -/

theorem Term.vec1_forall {Γ : Ctx} {σ : Ty} (p : Formula Sig (σ :: Γ)) :
    (Term.forall' p).vec1 θ hc = Term.forallBlock (σ.vec θ) (p.vec1 θ hc) := rfl
theorem Term.vec1_exists {Γ : Ctx} {σ : Ty} (p : Formula Sig (σ :: Γ)) :
    (Term.exists' p).vec1 θ hc = Term.existsBlock (σ.vec θ) (p.vec1 θ hc) := rfl
theorem Term.vec1_eq {Γ : Ctx} {σ : Ty} (a b : Term Sig Γ σ) :
    (Term.eq' a b).vec1 θ hc = Term.eqBlock (a.vec θ hc) (b.vec θ hc) := rfl
theorem Term.vec_lam {Γ : Ctx} {σ : Ty} {ρ : RTy} (b : Term Sig (σ :: Γ) ρ) :
    (Term.lam b).vec θ hc = .single (Term.lamBlock (σ.vec θ) (b.vec1 θ hc)) := rfl
theorem Term.vec_var {Γ : Ctx} {σ : Ty} (v : Var Γ σ) :
    (Term.var v : Term Sig Γ σ).vec θ hc = Var.vec θ v := rfl

/-! The propositional connectives, as themselves. -/

theorem Term.vec1_conj {Γ : Ctx} (p q : Formula Sig Γ) :
    (Term.conj p q).vec1 θ hc = Term.conj (p.vec1 θ hc) (q.vec1 θ hc) := rfl
theorem Term.vec1_disj {Γ : Ctx} (p q : Formula Sig Γ) :
    (Term.disj p q).vec1 θ hc = Term.disj (p.vec1 θ hc) (q.vec1 θ hc) := rfl
theorem Term.vec1_neg {Γ : Ctx} (p : Formula Sig Γ) :
    (Term.neg p).vec1 θ hc = Term.neg (p.vec1 θ hc) := rfl
theorem Term.vec1_imp {Γ : Ctx} (p q : Formula Sig Γ) :
    (Term.imp p q).vec1 θ hc = Term.imp (p.vec1 θ hc) (q.vec1 θ hc) := rfl
theorem Term.vec1_iff {Γ : Ctx} (p q : Formula Sig Γ) :
    (Term.iff p q).vec1 θ hc = Term.iff (p.vec1 θ hc) (q.vec1 θ hc) := rfl

/-! ### The readable translation converts to the generic one -/

mutual
  /-- A view is **sound** for a term: what it records of the term's abstraction body and
  of its applications is, up to conversion, what the generic translation gives. -/
  def Ty.VecSound : ∀ (σ : Ty) {Γ : Ctx}, Term Sig Γ σ → Ty.VecView Sig θ Γ σ → Prop
    | .rel ρ, _, t, w => RTy.VecSound ρ t w
    | .e, _, _, _ => True
    | .var _, _, _, _ => True
  /-- Soundness of a view, at a relational type. -/
  def RTy.VecSound : ∀ (ρ : RTy) {Γ : Ctx}, Term Sig Γ ρ → RTy.VecView Sig θ Γ ρ → Prop
    | .t, _, _, _ => True
    | .arr σ ρ, Γ, t, w =>
      (∀ body, w.1 = some body → t.vecG1 θ hc ≡ Term.lamBlock (σ.vec θ) body) ∧
      (∀ (x : Term Sig Γ σ) (dx : Terms Sig (Ctx.vec θ Γ) (σ.vec θ) × Ty.VecView Sig θ Γ σ),
        Terms.Conv dx.1 (x.vecG θ hc) → Ty.VecSound σ x dx.2 →
        ∀ d, w.2 dx = some d → d.1 ≡ (Term.app t x).vecG1 θ hc ∧ RTy.VecSound ρ (Term.app t x) d.2)
end

mutual
  theorem Ty.vecSound_none : ∀ (σ : Ty) {Γ : Ctx} (t : Term Sig Γ σ),
      Ty.VecSound θ hc σ t (Ty.VecView.none σ)
    | .rel ρ, _, t => RTy.vecSound_none ρ t
    | .e, _, _ => trivial
    | .var _, _, _ => trivial
  theorem RTy.vecSound_none : ∀ (ρ : RTy) {Γ : Ctx} (t : Term Sig Γ ρ),
      RTy.VecSound θ hc ρ t (RTy.VecView.none ρ)
    | .t, _, _ => trivial
    | .arr _ _, _, _ => ⟨(fun _ h => nomatch h), (fun _ _ _ _ _ h => nomatch h)⟩
end

/-- The readable translation converts to the generic one, and its views are sound. -/
theorem Term.vecData_sound : ∀ {Γ : Ctx} {σ : Ty} (t : Term Sig Γ σ),
    Terms.Conv (t.vecData θ hc).1 (t.vecG θ hc) ∧ Ty.VecSound θ hc σ t (t.vecData θ hc).2
  | _, _, .var _ => ⟨Terms.Conv.refl _, Ty.vecSound_none θ hc _ _⟩
  | _, _, .const _ => ⟨Terms.Conv.refl _, Ty.vecSound_none θ hc _ _⟩
  | _, _, .app (ρ := ρ) f a => by
    obtain ⟨hf, hfw⟩ := Term.vecData_sound f
    obtain ⟨ha, haw⟩ := Term.vecData_sound a
    show Terms.Conv (match (f.vecData θ hc).2.2 (a.vecData θ hc) with
        | some d => (Terms.single d.1, d.2)
        | Option.none => (Terms.single (Term.appBlock (f.vecData θ hc).1.head1 (a.vecData θ hc).1),
            RTy.VecView.none ρ)).1 _ ∧ RTy.VecSound θ hc ρ _ (match (f.vecData θ hc).2.2 (a.vecData θ hc) with
        | some d => (Terms.single d.1, d.2)
        | Option.none => (Terms.single (Term.appBlock (f.vecData θ hc).1.head1 (a.vecData θ hc).1),
            RTy.VecView.none ρ)).2
    cases h : (f.vecData θ hc).2.2 (a.vecData θ hc) with
    | some d =>
      obtain ⟨h₁, h₂⟩ := hfw.2 a (a.vecData θ hc) ha haw d h
      exact ⟨.cons h₁ .nil, h₂⟩
    | none =>
      exact ⟨.cons (Conv.appBlock_congr hf.head1 ha) .nil, RTy.vecSound_none θ hc ρ _⟩
  | _, _, .lam (σ := σ) b => by
    obtain ⟨hb, _⟩ := Term.vecData_sound b
    refine ⟨.cons (Conv.lamBlock_congr _ hb.head1) .nil, ?_, fun _ _ _ _ _ h => nomatch h⟩
    intro body h
    cases h
    exact Conv.lamBlock_congr _ hb.head1.symm
  | _, _, .and => ⟨Terms.Conv.refl _, Ty.vecSound_none θ hc _ _⟩
  | _, _, .or => ⟨Terms.Conv.refl _, Ty.vecSound_none θ hc _ _⟩
  | _, _, .not => ⟨Terms.Conv.refl _, Ty.vecSound_none θ hc _ _⟩
  | _, _, .all σ => by
    refine ⟨Terms.Conv.refl _, (fun _ h => nomatch h), ?_⟩
    intro x dx hx hxw d h
    obtain ⟨body, hbody, rfl⟩ := Option.map_eq_some_iff.1 h
    refine ⟨?_, trivial⟩
    exact Conv.symm (Conv.trans (Conv.app_congr (Conv.refl _) (hxw.1 body hbody))
      (Conv.allC_lamBlock _ _))
  | _, _, .ex σ => by
    refine ⟨Terms.Conv.refl _, (fun _ h => nomatch h), ?_⟩
    intro x dx hx hxw d h
    obtain ⟨body, hbody, rfl⟩ := Option.map_eq_some_iff.1 h
    refine ⟨?_, trivial⟩
    exact Conv.symm (Conv.trans (Conv.app_congr (Conv.refl _) (hxw.1 body hbody))
      (Conv.exC_lamBlock _ _))
  | _, _, .eq σ => by
    refine ⟨Terms.Conv.refl _, (fun _ h => nomatch h), ?_⟩
    intro x dx hx _ d h
    cases h
    refine ⟨Conv.appBlock_congr (Conv.refl _) hx, (fun _ h => nomatch h), ?_⟩
    intro y dy hy _ d' h'
    cases h'
    refine ⟨?_, trivial⟩
    exact Conv.trans (Conv.eqBlock_congr hx hy) (Conv.symm (Conv.eqC_appBlock _ _ _))
  | _, _, .constR _ => ⟨Terms.Conv.refl _, Ty.vecSound_none θ hc _ _⟩
  | _, _, .negR _ => ⟨Terms.Conv.refl _, Ty.vecSound_none θ hc _ _⟩
  | _, _, .andR _ => ⟨Terms.Conv.refl _, Ty.vecSound_none θ hc _ _⟩
  | _, _, .orR _ => ⟨Terms.Conv.refl _, Ty.vecSound_none θ hc _ _⟩
  | _, _, .coextR _ => ⟨Terms.Conv.refl _, Ty.vecSound_none θ hc _ _⟩
  | _, _, .boxR _ => ⟨Terms.Conv.refl _, Ty.vecSound_none θ hc _ _⟩
  | _, _, .boxImpR _ => ⟨Terms.Conv.refl _, Ty.vecSound_none θ hc _ _⟩

/-- **The readable translation converts to the generic one.** -/
theorem Term.vec_conv_vecG {Γ : Ctx} {σ : Ty} (t : Term Sig Γ σ) :
    Terms.Conv (t.vec θ hc) (t.vecG θ hc) :=
  (Term.vecData_sound θ hc t).1

theorem Term.vec1_conv_vecG1 {Γ : Ctx} {ρ : RTy} (t : Term Sig Γ ρ) :
    t.vec1 θ hc ≡ t.vecG1 θ hc :=
  (Term.vec_conv_vecG θ hc t).head1

end

end Classicism.Meta
