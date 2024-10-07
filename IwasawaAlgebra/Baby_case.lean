import Mathlib

variable (F : Type*) [Field F] (ι : outParam Type*)
  [LinearOrderedCommGroupWithZero ι] [vR : Valued F ι]

open Polynomial

theorem Wierstrass_preperation (f : PowerSeries (Valued.integer F)) (ne : f ≠ 0)
    (π : Valued.integer F) (h : Ideal.span {π} = Valued.maximalIdeal F) : ∃ (m : ℕ),
    ∃ (g : Polynomial (Valued.integer F)), ∃ (h : (PowerSeries (Valued.integer F))ˣ),
    Monic g ∧ (∀ i : ℕ, i < degree g → (coeff g i) ∈ Valued.maximalIdeal F ) ∧
    f = (π ^ m) • g • h := sorry
