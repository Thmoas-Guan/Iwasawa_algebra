/-
Copyright (c) 2024 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Category.Ring.Limits
import IwasawaAlgebra.MissingLemmas.TwoSidedIdeal

set_option maxHeartbeats 0
set_option maxRecDepth 1000000000

variable {α : Type v} [CanonicallyLinearOrderedAddCommMonoid α]

section definition

variable (R : Type u) [Ring R]

class RingFiltration where
  Fil : α → TwoSidedIdeal R
--top : Fil (0 : α) = ⊤
  intersection_eq  : ∀ i : α, Fil i = ⨅ j < i, Fil j
  inclusion_le : ∀ i j : α,  (Fil i) * (Fil j) ≤ Fil (i + j)

end definition


namespace RingFiltration

open CategoryTheory TwoSidedIdeal Opposite TwoSidedIdealextra

variable (R : Type u) [Ring R] (P : RingFiltration R (α := α))

theorem top' : ⨅ (j : α) (_ : j < 0), P.Fil j = ⊤ := by
  simp only [not_lt, zero_le, iInf_neg, iInf_top]

theorem top : P.Fil (0 : α) = ⊤ := by
  rw [P.intersection_eq]
  exact top' R P

def Intermap :=
  fun (i : α) ↦ (⨅ μ > i, P.Fil μ)

def QuotientMap :=
  fun (x : αᵒᵖ) ↦ ((P.Fil (Opposite.unop x)).ringCon).Quotient

lemma descending {x y : α} (h : y ≤ x) : P.Fil x ≤ P.Fil y := by
  repeat rw [P.intersection_eq]
  simp only [le_iInf_iff, iInf_le_iff]
  exact fun a ha b hb => hb a (gt_of_ge_of_gt h ha)

lemma opdescending {x y : αᵒᵖ} (f : x ⟶ y) : P.Fil (unop x) ≤ P.Fil (unop y) :=
  descending R P (le_of_op_hom f)

section Completion

instance {x : αᵒᵖ} : Ring (QuotientMap R P x) := (P.Fil (unop x)).ringCon.instRingQuotient

noncomputable def QuotientRingFunc : αᵒᵖ ⥤ RingCat.{u} where
  obj := fun a => RingCat.of (P.QuotientMap R a)
  map := fun f => RingCat.ofHom (Quotient.factor _ _ (opdescending R P f))
/-  intro x y f
    refine RingCat.ofHom ?f
    let I := P.Fil (unop x)
    let J := P.Fil (unop y)
    exact Quotient.factor I J (descending R P (le_of_op_hom f)) -/

  map_id := fun x => Quotient.factorEqid (P.Fil (unop x))

  map_comp := fun f g => Quotient.factorcomp _ _ _ (opdescending R P f) (opdescending R P g)


instance : Small (P.QuotientRingFunc ⋙ forget RingCat).sections := sorry

  --small_lift ↑(QuotientRingFunc R P ⋙ forget RingCat).sections


#check Nat.fib

variable [Small (P.QuotientRingFunc ⋙ forget RingCat).sections]

noncomputable section
/-- The explicit limit cone in `Ringcat`. -/
def limitCone :=
  RingCat.limitCone (QuotientRingFunc R P)


/--The completion of a filtered ring is the limit of the quotient rings . -/
def Completion := (limitCone R P).pt


/--The natural ring homomorphism from `Completion R P` to `R`. -/
def CompletionHom : (Completion R P) →+* R where
  toFun := by
    intro a
    sorry
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/--We say `R` is complete if the natural ring homomorphism `CompletionHom` is isomorpism. -/
def IsComplete : Prop :=
  ∃ f : (Completion R P) ≃+* R, f.toRingHom = CompletionHom R P




end



end Completion
