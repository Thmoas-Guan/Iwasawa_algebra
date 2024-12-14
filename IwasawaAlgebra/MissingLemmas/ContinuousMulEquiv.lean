import Mathlib.Topology.Algebra.ContinuousMonoidHom

section

/-!
# Continuous MulEquiv
This section defines the space of continuous isomorphisms between two topological groups.
## Main definitions
-/

universe u v

variable (G : Type u) [TopologicalSpace G] (H : Type v) [TopologicalSpace H]

/-- Define the structure of two-sided continuous isomorphism of additive groups. -/
structure ContinuousAddEquiv [Add G] [Add H] extends AddEquiv G H , Homeomorph G H

/-- Define the structure of two-sided continuous isomorphism of groups. -/
@[to_additive "The type of two-sided continuous isomorphism of additive groups."]
structure ContinuousMulEquiv [Mul G] [Mul H] extends MulEquiv G H , Homeomorph G H

/-- The Homeomorphism induced from a two-sided continuous isomorphism of groups. -/
add_decl_doc ContinuousMulEquiv.toHomeomorph

/-- The Homeomorphism induced from a two-sided continuous isomorphism additive groups. -/
add_decl_doc ContinuousAddEquiv.toHomeomorph

/-- Notation for a `ContinuousMulEquiv`. -/
infixl:25 " ≃ₜ* " => ContinuousMulEquiv

/-- Notation for an `ContinuousAddEquiv`. -/
infixl:25 " ≃ₜ+ " => ContinuousAddEquiv

section

namespace ContinuousMulEquiv

variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] [Mul M] [Mul N]

section coe

@[to_additive]
instance : EquivLike (M ≃ₜ* N) M N where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    congr
    exact MulEquiv.ext_iff.mpr (congrFun h₁)

@[to_additive]
instance : MulEquivClass (M ≃ₜ* N) M N where
  map_mul f := f.map_mul'

@[to_additive] -- shortcut instance that doesn't generate any subgoals
instance : CoeFun (M ≃ₜ* N) fun _ ↦ M → N where
  coe f := f

/-- Two continuous multiplicative isomorphisms agree if they are defined by the
same underlying function. -/
@[to_additive (attr := ext)
  "Two continuous additive isomorphisms agree if they are defined by the same underlying function."]
theorem ext {f g : M ≃ₜ* N} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[to_additive]
protected theorem congr_arg {f : M ≃ₜ* N} {x x' : M} : x = x' → f x = f x' :=
  DFunLike.congr_arg f

@[to_additive]
protected theorem congr_fun {f g : M ≃ₜ* N} (h : f = g) (x : M) : f x = g x :=
  DFunLike.congr_fun h x

@[to_additive (attr := simp)]
theorem coe_mk (f : M ≃* N) (hf1 : Continuous f.toFun) (hf2 : Continuous f.invFun) :
    (mk f hf1 hf2 : M → N) = f := rfl

@[to_additive]
theorem toEquiv_eq_coe (f : M ≃ₜ* N) : f.toEquiv = f :=
  rfl

/-- Makes a continuous multiplicative isomorphism from
a homeomorphism which preserves multiplication. -/
@[to_additive "Makes an continuous additive isomorphism from
a homeomorphism which preserves addition."]
def mk' (f : M ≃ₜ N) (h : ∀ x y, f (x * y) = f x * f y) : M ≃ₜ* N :=
  ⟨⟨f.toEquiv,h⟩, f.continuous_toFun, f.continuous_invFun⟩

end coe

section bijective

@[to_additive]
protected theorem bijective (e : M ≃ₜ* N) : Function.Bijective e :=
  EquivLike.bijective e

@[to_additive]
protected theorem injective (e : M ≃ₜ* N) : Function.Injective e :=
  EquivLike.injective e

@[to_additive]
protected theorem surjective (e : M ≃ₜ* N) : Function.Surjective e :=
  EquivLike.surjective e

-- Porting note (#10618): `simp` can prove this
@[to_additive]
theorem apply_eq_iff_eq (e : M ≃ₜ* N) {x y : M} : e x = e y ↔ x = y :=
  e.injective.eq_iff

end bijective

section refl

variable (M)

/-- The identity map is a continuous multiplicative isomorphism. -/
@[to_additive (attr := refl) "The identity map is a continuous additive isomorphism."]
def refl : M ≃ₜ* M :=
  { MulEquiv.refl _ with
  continuous_toFun := by continuity
  continuous_invFun := by continuity }

@[to_additive]
instance : Inhabited (M ≃ₜ* M) := ⟨ContinuousMulEquiv.refl M⟩

@[to_additive (attr := simp)]
theorem coe_refl : ↑(refl M) = id := rfl

@[to_additive (attr := simp)]
theorem refl_apply (m : M) : refl M m = m := rfl

end refl

section symm

/-- The inverse of a ContinuousMulEquiv. -/
@[to_additive "The inverse of a ContinuousAddEquiv."]
def symm (cme : M ≃ₜ* N) : N ≃ₜ* M :=
  { cme.toMulEquiv.symm with
  continuous_toFun := cme.continuous_invFun
  continuous_invFun := cme.continuous_toFun }

@[to_additive]
theorem invFun_eq_symm {f : M ≃ₜ* N} : f.invFun = f.symm := rfl

@[to_additive (attr := simp)]
theorem equivLike_inv_eq_symm (f : M ≃ₜ* N) : EquivLike.inv f = f.symm := rfl

@[to_additive (attr := simp)]
theorem symm_symm (f : M ≃ₜ* N) : f.symm.symm = f := rfl

/-- `e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`. -/
@[to_additive (attr := simp) "`e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`."]
theorem apply_symm_apply (e : M ≃ₜ* N) (y : N) : e (e.symm y) = y :=
  e.toEquiv.apply_symm_apply y

/-- `e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`. -/
@[to_additive (attr := simp) "`e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`."]
theorem symm_apply_apply (e : M ≃ₜ* N) (x : M) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x

@[to_additive (attr := simp)]
theorem symm_comp_self (e : M ≃ₜ* N) : e.symm ∘ e = id :=
  funext e.symm_apply_apply

@[to_additive (attr := simp)]
theorem self_comp_symm (e : M ≃ₜ* N) : e ∘ e.symm = id :=
  funext e.apply_symm_apply

@[to_additive]
theorem apply_eq_iff_symm_apply (e : M ≃ₜ* N) {x : M} {y : N} : e x = y ↔ x = e.symm y :=
  e.toEquiv.apply_eq_iff_eq_symm_apply

@[to_additive]
theorem symm_apply_eq (e : M ≃ₜ* N) {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq

@[to_additive]
theorem eq_symm_apply (e : M ≃ₜ* N) {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

@[to_additive]
theorem eq_comp_symm {α : Type*} (e : M ≃ₜ* N) (f : N → α) (g : M → α) :
    f = g ∘ e.symm ↔ f ∘ e = g :=
  e.toEquiv.eq_comp_symm f g

@[to_additive]
theorem comp_symm_eq {α : Type*} (e : M ≃ₜ* N) (f : N → α) (g : M → α) :
    g ∘ e.symm = f ↔ g = f ∘ e :=
  e.toEquiv.comp_symm_eq f g

@[to_additive]
theorem eq_symm_comp {α : Type*} (e : M ≃ₜ* N) (f : α → M) (g : α → N) :
    f = e.symm ∘ g ↔ e ∘ f = g :=
  e.toEquiv.eq_symm_comp f g

@[to_additive]
theorem symm_comp_eq {α : Type*} (e : M ≃ₜ* N) (f : α → M) (g : α → N) :
    e.symm ∘ g = f ↔ g = e ∘ f :=
  e.toEquiv.symm_comp_eq f g

end symm

section trans

variable {L : Type*} [Mul L] [TopologicalSpace L]

/-- The composition of two ContinuousMulEquiv. -/
@[to_additive "The composition of two ContinuousAddEquiv."]
def trans (cme1 : M ≃ₜ* N) (cme2 : N ≃ₜ* L) : M ≃ₜ* L :=
  { cme1.toMulEquiv.trans cme2.toMulEquiv with
  continuous_toFun := by convert Continuous.comp cme2.continuous_toFun cme1.continuous_toFun
  continuous_invFun := by convert Continuous.comp cme1.continuous_invFun cme2.continuous_invFun }

@[to_additive (attr := simp)]
theorem coe_trans (e₁ : M ≃ₜ* N) (e₂ : N ≃ₜ* L) : ↑(e₁.trans e₂) = e₂ ∘ e₁ := rfl

@[to_additive (attr := simp)]
theorem trans_apply (e₁ : M ≃ₜ* N) (e₂ : N ≃ₜ* L) (m : M) : e₁.trans e₂ m = e₂ (e₁ m) := rfl

@[to_additive (attr := simp)]
theorem symm_trans_apply (e₁ : M ≃ₜ* N) (e₂ : N ≃ₜ* L) (l : L) :
    (e₁.trans e₂).symm l = e₁.symm (e₂.symm l) := rfl

@[to_additive (attr := simp)]
theorem symm_trans_self (e : M ≃ₜ* N) : e.symm.trans e = refl N :=
  DFunLike.ext _ _ e.apply_symm_apply

@[to_additive (attr := simp)]
theorem self_trans_symm (e : M ≃ₜ* N) : e.trans e.symm = refl M :=
  DFunLike.ext _ _ e.symm_apply_apply

end trans

section unique

/-- The `MulEquiv` between two monoids with a unique element. -/
@[to_additive "The `AddEquiv` between two `AddMonoid`s with a unique element."]
def continuousMulEquivOfUnique {M N} [Unique M] [Unique N] [Mul M] [Mul N]
    [TopologicalSpace M] [TopologicalSpace N] : M ≃ₜ* N :=
  { MulEquiv.mulEquivOfUnique with
  continuous_toFun := by continuity
  continuous_invFun := by continuity }

/-- There is a unique monoid homomorphism between two monoids with a unique element. -/
@[to_additive "There is a unique additive monoid homomorphism between two additive monoids with
  a unique element."]
instance {M N} [Unique M] [Unique N] [Mul M] [Mul N]
    [TopologicalSpace M] [TopologicalSpace N] : Unique (M ≃ₜ* N) where
  default := continuousMulEquivOfUnique
  uniq _ := ext fun _ ↦ Subsingleton.elim _ _

end unique

end ContinuousMulEquiv

end

end
