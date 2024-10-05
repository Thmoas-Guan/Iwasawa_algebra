import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.TwoSidedIdeal.Basic
import IwasawaAlgebra.MissingLemmas.TwoSidedIdeal

variable {R : Type u} {α : Type v} [Ring R] [CanonicallyOrderedAddCommMonoid α]

structure RingFiltration where
  F : α → TwoSidedIdeal R
  bot : F (0 : α) = R
  intersection_eq  : ∀ i : α, F i = ⨅ j < i, F j
  inclusion_le : ∀ i j : α,  ((F i) * (F j)) ≤ F (i + j)
