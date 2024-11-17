import Mathlib

variable (F : Type*) [Field F] (ι : outParam Type*)
  [LinearOrderedCommGroupWithZero ι] [vR : Valued F ι]

variable (R : Type*) [CommRing R] (m : Ideal R) (hmax : m.IsMaximal)
open Polynomial Valued

theorem Wierstrass_preperation (f : PowerSeries 𝒪[F]) (ne : f ≠ 0)
    (π : 𝒪[F] ) (hyp : Ideal.span {π} = 𝓂[F] ) : ∃ (m : ℕ),
    ∃ (g : Polynomial 𝒪[F] ), ∃ (h : (PowerSeries 𝒪[F])ˣ),
    Monic g ∧ (∀ i : ℕ, i < degree g → (coeff g i) ∈ 𝓂[F]) ∧
    f = (π ^ m) • g • h := sorry

set_option synthInstance.maxHeartbeats 100000 in
lemma h (n : ℕ) (npos : n > 0) (π : 𝒪[F]) (f : PowerSeries (𝒪[F] ⧸ Ideal.span {π ^ n}))
    (ne : ∀(f' : PowerSeries (𝒪[F] ⧸ Ideal.span {π ^ n})), f ≠ (π : (𝒪[F] ⧸ Ideal.span {π ^ n})) • f') :
    ∃ (g : Polynomial (𝒪[F] ⧸ Ideal.span {π ^ n})), ∃ (h : (PowerSeries (𝒪[F] ⧸ Ideal.span {π ^ n}))ˣ),
    Monic g ∧ (∀ i : ℕ, i < degree g → ∃ (coeff' : (𝒪[F] ⧸ Ideal.span {π ^ n})), (coeff g i) = (π : (𝒪[F] ⧸ Ideal.span {π ^ n})) * coeff')
    ∧ f = g • h := by
    induction' n with n ih
    · absurd npos
      exact Nat.not_lt_zero 0
    · by_cases neq0 : n = 0
      · have : ∃ (m : ℕ), (PowerSeries.coeff _ m) f ≠ 0 ∧ (∀ (i : ℕ), i < m → (PowerSeries.coeff _ i) f = 0) := by
          by_contra hcon
          have hall0 (l : ℕ): ∀ (i : ℕ), i < l → (PowerSeries.coeff _ i) f = 0 := by
            induction' l with l ihl
            · intro i hi
              absurd hi
              exact Nat.not_lt_zero i
            · by_cases hcasl0 : (PowerSeries.coeff _ l) f = 0
              · intro i hi
                by_cases hcasl : i = l
                · rw[hcasl]
                  exact hcasl0
                · exact ihl i (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) hcasl)
              · absurd hcon
                use l
          have : ∀ (m : ℕ), (PowerSeries.coeff _ m) f = 0 := by
            intro m
            exact hall0 (m + 1) m (lt_add_one m)
          have : f = 0 := by exact PowerSeries.ext this
          absurd ne
          simp only [ne_eq, not_forall, not_not]
          use 0
          rw[this]
          exact Eq.symm <| DistribMulAction.smul_zero ((Ideal.Quotient.mk (Ideal.span {π ^ (n + 1)})) π)
        sorry
      · have npos' : n > 0 := by exact Nat.zero_lt_of_ne_zero neq0
        --let f' := f ⧸ Ideal.span {π ^ n}
        #check ih npos'
        sorry
-/
