import Mathlib

set_option maxHeartbeats 500000

variable {R : Type*} [CommRing R] {m : Ideal R} (hmax : m.IsMaximal)
open Polynomial PowerSeries

lemma ne0 {f : PowerSeries (R ⧸ m ^ n)} (ntriv : ∃ (k : ℕ), (PowerSeries.coeff _ k) f ∉ m.map (Ideal.Quotient.mk (m ^ n))) : f ≠ 0 := by
  rcases ntriv with ⟨k, hk⟩
  have : (PowerSeries.coeff _ k) f ≠ 0 := by
    by_contra h
    exact (h ▸ hk) (Submodule.zero_mem (Ideal.map (Ideal.Quotient.mk (m ^ n)) m))
  exact (ne_of_apply_ne ⇑(PowerSeries.coeff _ k) fun a => this a.symm).symm

lemma hh (n : ℕ) (npos : n > 0) [hmax : m.IsMaximal] (f : PowerSeries (R ⧸ m ^ n))
    (ntriv : ∃ (k : ℕ), (PowerSeries.coeff _ k) f ∉ m.map (Ideal.Quotient.mk (m ^ n))) :
    ∃ (g : Polynomial (R ⧸ m ^ n)), ∃ (h : (R ⧸ m ^ n)⟦X⟧ˣ), Monic g ∧
    (∀ i : ℕ, i < degree g → coeff g i ∈ m.map (Ideal.Quotient.mk (m ^ n))) ∧ f = g * h := by
    induction' n with n ih
    · absurd npos
      exact Nat.not_lt_zero 0
    · by_cases neq0 : n = 0
      · use Polynomial.X ^ f.order.get (order_finite_iff_ne_zero.mpr (ne0 ntriv))
        let max' : (m ^ (n + 1)).IsMaximal := by
          simp [neq0]
          exact hmax
        let hField : Field (R ⧸ m ^ (n + 1)) := Ideal.Quotient.field (m ^ (n + 1))
        let h : (R ⧸ m ^ (n + 1))⟦X⟧ˣ := PowerSeries.Unit_of_divided_by_X_pow_order f
        use h
        constructor
        · apply monic_X_pow
        · simp only [degree_pow, degree_X, nsmul_eq_mul, mul_one, Nat.cast_lt,
          Polynomial.coeff_X_pow]
          constructor
          · intro a ha
            convert (Submodule.zero_mem (Ideal.map (Ideal.Quotient.mk (m ^ (n + 1))) m))
            simp [Nat.ne_of_lt ha]
          · have := PowerSeries.self_eq_X_pow_order_mul_divided_by_X_pow_order (ne0 ntriv)
            rw [PowerSeries.Unit_of_divided_by_X_pow_order_nonzero (ne0 ntriv)]
            convert this.symm
            simp only [Polynomial.coe_pow, Polynomial.coe_X]
      · let hom : (R ⧸ m ^ (n + 1)) →+* (R ⧸ m ^ n) :=
          Ideal.Quotient.lift (m ^ (n + 1)) (Ideal.Quotient.mk (m ^ n))
            (fun a ha ↦ Ideal.Quotient.eq_zero_iff_mem.mpr ((Ideal.pow_le_pow_right (Nat.le_add_right n 1)) ha))
        let f' : PowerSeries (R ⧸ m ^ n) := PowerSeries.map hom f
        have ntriv' : ∃ k, (PowerSeries.coeff (R ⧸ m ^ n) k) f' ∉ Ideal.map (Ideal.Quotient.mk (m ^ n)) m := by
          rcases ntriv with ⟨k, hk⟩
          use k
          simp only [PowerSeries.coeff_map, f', hom]
          /-by_contra h
          absurd hk
          rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ n)) Ideal.Quotient.mk_surjective h with ⟨r, hr, eq⟩
          have : (Ideal.Quotient.mk (m ^ (n + 1))) r ∈ m.map (Ideal.Quotient.mk (m ^ (n + 1))) := by
            exact Ideal.mem_map_of_mem (Ideal.Quotient.mk (m ^ (n + 1))) hr
          convert this-/

          sorry
        rcases ih (Nat.zero_lt_of_ne_zero neq0) f' ntriv' with ⟨g',h', mon, hg, eq⟩
        sorry

section

variable (F : Type*) [Field F] (ι : outParam Type*)
  [LinearOrderedCommGroupWithZero ι] [vR : Valued F ι]
open Valued

theorem Wierstrass_preperation (f : PowerSeries 𝒪[F]) (ne : f ≠ 0)
    (π : 𝒪[F] ) (hyp : Ideal.span {π} = 𝓂[F] ) : ∃ (m : ℕ),
    ∃ (g : Polynomial 𝒪[F] ), ∃ (h : (PowerSeries 𝒪[F])ˣ),
    Monic g ∧ (∀ i : ℕ, i < degree g → (coeff g i) ∈ 𝓂[F]) ∧
    f = (π ^ m) • g • h := sorry

end
