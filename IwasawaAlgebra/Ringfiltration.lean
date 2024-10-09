/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.CompletePartialOrder
import IwasawaAlgebra.MissingLemmas.TwoSidedIdeal
import Mathlib.Algebra.Category.Ring.Limits

variable {α : Type v} [CanonicallyLinearOrderedAddCommMonoid α]

section definition

variable (R : Type u) [Ring R]

class RingFiltration where
  Fil : α → TwoSidedIdeal R
  top : Fil (0 : α) = ⊤
  intersection_eq  : ∀ i : α, Fil i = ⨅ j < i, Fil j
  inclusion_le : ∀ i j : α,  ((Fil i) * (Fil j)) ≤ Fil (i + j)

end definition

namespace RingFiltration

open CategoryTheory Opposite TwoSidedIdeal

section Completion

variable (R : Type u) [Ring R] (P : RingFiltration R (α := α))


def Intermap :=
  fun (i : α) ↦ (⨅ μ > i, P.Fil μ)

def QuotientMap :=
  fun (x : αᵒᵖ) ↦ ((P.Fil (unop x)).ringCon).Quotient


instance {x : αᵒᵖ} : Ring (QuotientMap R P x) := (P.Fil (unop x)).ringCon.instRingQuotient


def QuotientRingFunc : αᵒᵖ ⥤ RingCat.{u} where
  obj := fun a ↦  RingCat.of (P.QuotientMap R a)
  map := by
    intro x y f
    dsimp only
    apply RingCat.ofHom
    constructor
    · simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe]
      sorry
    · intro a b
      simp only [OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, QuotientMap]
      sorry
    · sorry


variable [Small (P.QuotientRingFunc ⋙ forget RingCat).sections]

noncomputable section
/-- The explicit limit cone in `Ringcat`. -/
def limitCone  :=
  RingCat.limitCone (QuotientRingFunc R P)


/--The completion of a filtered ring is the limit of the quotient rings . -/
def Completion := (limitCone R P).pt


/--The natural ring homomorphism from `Completion R P` to `R`. -/
def CompletionHom : (Completion R P) →+* R where
  toFun := sorry
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/--We say `R` is complete if the natural ring homomorphism `CompletionHom` is isomorpism. -/
def IsComplete : Prop :=
  ∃ f : (Completion R P) ≃+* R, f.toRingHom = CompletionHom R P


end




end Completion
