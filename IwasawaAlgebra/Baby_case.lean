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
set_option diagnostics true

--

example (hmax : m.IsMaximal) (f : PowerSeries (R ⧸ m)) (k : ℕ) : 1 = 1 := by
  #check Quotient.out' ((PowerSeries.coeff (R ⧸ m) k) f) ∉ m

lemma hneq0 (hmax : m.IsMaximal) (f : PowerSeries (R ⧸ m))
    (ne : ∃ (k : ℕ), Quotient.out' ((PowerSeries.coeff (R ⧸ m) k) f) ∉ m) :
    ∃ (g : Polynomial (R ⧸ m)), ∃ (h : (PowerSeries (R ⧸ m))ˣ), Monic g ∧
    (∀ i : ℕ, i < degree g → Quotient.out' ((PowerSeries.coeff (R ⧸ m) i) f) ∈ m) ∧ f = g • h := by
    sorry
/-
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
        rcases ne with ⟨k, hne⟩
        absurd hne
        simp only [ne_eq, not_forall, not_not]
        use 0
        rw[this]
        simp only [map_zero, ZeroMemClass.coe_zero]
      rcases this with ⟨t, ⟨ht1, ht2⟩⟩
      let hrg := PowerSeries.mk λ i ↦ (PowerSeries.coeff _ (i + t)) f
      have hhrg (i : ℕ) : (PowerSeries.coeff (R ⧸ m) (i)) hrg = (PowerSeries.coeff (R ⧸ m) (i + t)) f := by exact PowerSeries.coeff_mk i fun i => (PowerSeries.coeff (R ⧸ m) (i + t)) f
      have : f = hrg * PowerSeries.X ^ t := by
        ext k
        by_cases hkt : k < t
        · rw [ht2 k hkt]
          have htk : ¬t <= k := by exact Nat.not_le_of_lt hkt
          have hco0 : (PowerSeries.coeff (R ⧸ m) k) (hrg * PowerSeries.X ^ t) = if t ≤ k then (PowerSeries.coeff (R ⧸ m) (k - t)) hrg else 0 := by exact PowerSeries.coeff_mul_X_pow' hrg t k
          rw [if_neg htk] at hco0
          rw [hco0]
        · have : k >= t := by exact Nat.le_of_not_lt hkt
          have : k = k - t + t := by exact (Nat.sub_eq_iff_eq_add this).mp rfl
          calc
            (PowerSeries.coeff (R ⧸ m) k) f = (PowerSeries.coeff (R ⧸ m) (k - t)) hrg := by rw[hhrg (k - t)]; nth_rw 1 [this]
            _ = (PowerSeries.coeff (R ⧸ m) k) (hrg * PowerSeries.X ^ t) := by rw[←PowerSeries.coeff_mul_X_pow hrg t (k - t)]; nth_rw 2 [this]
      use (Polynomial.X ^ t : Polynomial (R ⧸ m))

      rcases ne with ⟨k, hk⟩
      have hkt : k >= t := by
        by_contra hcon
        absurd hk
        simp only [not_forall₂]
        use (0 : m)
        simp only [not_false_eq_true, ZeroMemClass.coe_zero, map_zero, exists_prop, and_true]
        exact ht2 k (Nat.gt_of_not_le hcon)
      have hunit: IsUnit hrg := by
        apply PowerSeries.isUnit_iff_constantCoeff.mpr
        have : (PowerSeries.constantCoeff (R ⧸ m)) hrg = (PowerSeries.coeff (R ⧸ m) 0) hrg := by
          exact Eq.symm (PowerSeries.coeff_zero_eq_constantCoeff_apply hrg)
        rw[this]
        have : (PowerSeries.coeff (R ⧸ m) (0)) hrg = (PowerSeries.coeff (R ⧸ m) (0 + t)) f := hhrg 0
        rw[this, Nat.zero_add t]
        have : (PowerSeries.coeff (R ⧸ m) t) f ≠ 0 := by exact ht1
        let hField : Field (R ⧸ m) := by
          exact Ideal.Quotient.field m
        apply IsUnit.mk0
        exact this
      use IsUnit.unit hrg
      sorry
-/


lemma hh (n : ℕ) (npos : n > 0) (hmax : m.IsMaximal) (f : PowerSeries (R ⧸ m ^ n))
    (ne : ∃ (k : ℕ), Quotient.out' ((PowerSeries.coeff (R ⧸ (m ^ n)) k) f) ∉ m) :
    ∃ (g : Polynomial (R ⧸ m ^ n)), ∃ (h : (PowerSeries (R ⧸ (m ^ n)))ˣ), Monic g ∧
    (∀ i : ℕ, i < degree g → Quotient.out' ((PowerSeries.coeff (R ⧸ (m ^ n)) i) f) ∈ m) ∧ f = g • h := by
    sorry
    /-
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
          rcases ne with ⟨k, hne⟩
          absurd hne
          simp only [ne_eq, not_forall, not_not]
          use 0
          rw[this]
          simp only [map_zero, ZeroMemClass.coe_zero]
        rcases this with ⟨t, ⟨ht1, ht2⟩⟩
        let hrg := PowerSeries.mk λ i ↦ (PowerSeries.coeff _ (i + t)) f
        have hhrg (i : ℕ) : (PowerSeries.coeff (R ⧸ m ^ (n + 1)) (i)) hrg = (PowerSeries.coeff (R ⧸ m ^ (n + 1)) (i + t)) f := by exact PowerSeries.coeff_mk i fun i => (PowerSeries.coeff (R ⧸ m ^ (n + 1)) (i + t)) f
        have : f = hrg * PowerSeries.X ^ t := by
          ext k
          by_cases hkt : k < t
          · rw [ht2 k hkt]
            have htk : ¬t <= k := by exact Nat.not_le_of_lt hkt
            have hco0 : (PowerSeries.coeff (R ⧸ m ^ (n + 1)) k) (hrg * PowerSeries.X ^ t) = if t ≤ k then (PowerSeries.coeff (R ⧸ m ^ (n + 1)) (k - t)) hrg else 0 := by exact PowerSeries.coeff_mul_X_pow' hrg t k
            rw [if_neg htk] at hco0
            rw [hco0]
          · have : k >= t := by exact Nat.le_of_not_lt hkt
            have : k = k - t + t := by exact (Nat.sub_eq_iff_eq_add this).mp rfl
            calc
              (PowerSeries.coeff (R ⧸ m ^ (n + 1)) k) f = (PowerSeries.coeff (R ⧸ m ^ (n + 1)) (k - t)) hrg := by rw[hhrg (k - t)]; nth_rw 1 [this]
              _ = (PowerSeries.coeff (R ⧸ m ^ (n + 1)) k) (hrg * PowerSeries.X ^ t) := by rw[←PowerSeries.coeff_mul_X_pow hrg t (k - t)]; nth_rw 2 [this]
        use (Polynomial.X ^ t : Polynomial (R ⧸ m ^ (n + 1)))
        have hField : Field (R ⧸ m ^ (n + 1)) := by
          have : m ^ (n + 1) = m := by
            rw [neq0]
            have : 0 + 1 = 1 := by exact rfl
            rw [this, pow_one m]
          rw [this]
          exact Ideal.Quotient.field m
        rcases ne with ⟨k, hk⟩
        have hkt : k >= t := by
          by_contra hcon
          absurd hk
          simp only [not_forall₂]
          use (0 : m)
          simp only [not_false_eq_true, ZeroMemClass.coe_zero, map_zero, exists_prop, and_true]
          exact ht2 k (Nat.gt_of_not_le hcon)
        have : ∃ (hrg' : (PowerSeries (R ⧸ m ^ (n + 1)))), hrg * hrg' = 1 := by sorry
        have hunit: IsUnit hrg := by
          apply PowerSeries.isUnit_iff_constantCoeff.mpr
          have : (PowerSeries.constantCoeff (R ⧸ m ^ (n + 1))) hrg = (PowerSeries.coeff (R ⧸ m ^ (n + 1)) 0) hrg := by
            exact Eq.symm (PowerSeries.coeff_zero_eq_constantCoeff_apply hrg)
          rw[this]
          have : (PowerSeries.coeff (R ⧸ m ^ (n + 1)) (0)) hrg = (PowerSeries.coeff (R ⧸ m ^ (n + 1)) (0 + t)) f := hhrg 0
          rw[this, Nat.zero_add t]
          have : (PowerSeries.coeff (R ⧸ m ^ (n + 1)) t) f ≠ 0 := by exact ht1
          apply IsUnit.mk0
          --exact this
          sorry
        sorry
      · have : n > 0 := by exact Nat.zero_lt_of_ne_zero neq0
        --#check ih Nat.zero_lt_of_ne_zero neq0
        sorry
      -/


/-
set_option synthInstance.maxHeartbeats 50000 in
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
        rcases this with ⟨m, ⟨hm1, hm2⟩⟩
        have : (PowerSeries.X ^ m) ∣ f := by
          sorry
        let h := f / (PowerSeries.X ^ m)
        sorry
      · have npos' : n > 0 := by exact Nat.zero_lt_of_ne_zero neq0
        --let f' := f ⧸ Ideal.span {π ^ n}
        #check ih npos'
        sorry
-/
