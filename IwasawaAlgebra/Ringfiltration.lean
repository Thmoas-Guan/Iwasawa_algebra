import Mathlib
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.TwoSidedIdeal.Basic

variable {R : Type u} [Ring R]

open Pointwise

/-
structure RingFiltration {R : Type u} {α : Type v} [Ring R] [CanonicallyOrderedAddCommMonoid α] where
  F : α → TwoSidedIdeal R
  bot : F (0 : α) = R
  intersection_eq  : ∀ i : α, F i = ⨅ j < i, F j
  inclusion_le : ∀ i j : α,  ((F i) * (F j)) ≤ F (i + j)
 -/
