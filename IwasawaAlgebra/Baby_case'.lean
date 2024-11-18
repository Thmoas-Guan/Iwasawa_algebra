import Mathlib

set_option maxHeartbeats 500000

variable {R : Type*} [CommRing R] {m : Ideal R} (hmax : m.IsMaximal)
open Polynomial PowerSeries

section

variable (m)

open Set

lemma map_eq_range (n : ℕ) : m.map (Ideal.Quotient.mk (m ^ n)) = (Ideal.Quotient.mk (m ^ n))'' m := by
  ext x
  exact ⟨fun h ↦ Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ n)) Ideal.Quotient.mk_surjective h,
    fun ⟨r, hr, eq⟩ ↦ eq ▸ (Ideal.mem_map_of_mem _ hr)⟩

def hom (n : ℕ) : (R ⧸ m ^ (n + 1)) →+* (R ⧸ m ^ n) :=
  Ideal.Quotient.lift (m ^ (n + 1)) (Ideal.Quotient.mk (m ^ n))
  (fun _ ha ↦ Ideal.Quotient.eq_zero_iff_mem.mpr ((Ideal.pow_le_pow_right (Nat.le_add_right n 1)) ha))

lemma hom_commute (n : ℕ) : ((hom m n).comp (Ideal.Quotient.mk (m ^ (n + 1)))) = (Ideal.Quotient.mk (m ^ n)) := rfl

end

lemma ne0 {f : PowerSeries (R ⧸ m ^ n)} (ntriv : ∃ (k : ℕ), (PowerSeries.coeff _ k) f ∉ m.map (Ideal.Quotient.mk (m ^ n))) : f ≠ 0 := by
  rcases ntriv with ⟨k, hk⟩
  have : (PowerSeries.coeff _ k) f ≠ 0 := by
    by_contra h
    exact (h ▸ hk) (Submodule.zero_mem (Ideal.map (Ideal.Quotient.mk (m ^ n)) m))
  exact (ne_of_apply_ne ⇑(PowerSeries.coeff _ k) fun a => this a.symm).symm

open Classical

/-
If don't want to open Classical then trie def and lemma below.

noncomputable def ntriv_deg {f : PowerSeries (R ⧸ m ^ n)} (ntriv : ∃ (k : ℕ), (PowerSeries.coeff _ k) f ∉ m.map (Ideal.Quotient.mk (m ^ n))) : ℕ :=
  sInf {k | (PowerSeries.coeff _ k) f ∉ m.map (Ideal.Quotient.mk (m ^ n))}

lemma ntriv_deg_spec {f : PowerSeries (R ⧸ m ^ n)} (ntriv : ∃ (k : ℕ), (PowerSeries.coeff _ k) f ∉ m.map (Ideal.Quotient.mk (m ^ n))) :
    (PowerSeries.coeff _ (ntriv_deg ntriv)) f ∉ m.map (Ideal.Quotient.mk (m ^ n)) ∧ ∀ i < (ntriv_deg ntriv), (PowerSeries.coeff _ i) f ∈ m.map (Ideal.Quotient.mk (m ^ n)) :=
  sorry
-/
set_option linter.unusedTactic false

lemma map_ntriv {f : PowerSeries (R ⧸ m ^ (n + 1))} (ntriv : ∃ (k : ℕ), (PowerSeries.coeff _ k) f ∉ m.map (Ideal.Quotient.mk (m ^ (n + 1)))) :
    ∃ k, (PowerSeries.coeff (R ⧸ m ^ n) k) (PowerSeries.map (hom m n) f) ∉ Ideal.map (Ideal.Quotient.mk (m ^ n)) m := by
  sorry

lemma hh (n : ℕ) (npos : n > 0) [hmax : m.IsMaximal] (f : PowerSeries (R ⧸ m ^ n))
    (ntriv : ∃ (k : ℕ), (PowerSeries.coeff _ k) f ∉ m.map (Ideal.Quotient.mk (m ^ n))) :
    ∃! (g : Polynomial (R ⧸ m ^ n)), ∃ (h : (R ⧸ m ^ n)⟦X⟧ˣ), Monic g ∧ g.degree = Nat.find ntriv ∧
    (∀ i : ℕ, i < degree g → coeff g i ∈ m.map (Ideal.Quotient.mk (m ^ n))) ∧ f = g * h := by
    induction' n with n ih
    · absurd npos
      exact Nat.not_lt_zero 0
    · by_cases neq0 : n = 0
      · use Polynomial.X ^ f.order.get (order_finite_iff_ne_zero.mpr (ne0 ntriv))
        constructor
        · let max' : (m ^ (n + 1)).IsMaximal := by simpa only [neq0, zero_add, pow_one] using hmax
          let hField : Field (R ⧸ m ^ (n + 1)) := Ideal.Quotient.field (m ^ (n + 1))
          use PowerSeries.Unit_of_divided_by_X_pow_order f
          constructor
          · apply monic_X_pow
          · simp only [degree_pow, degree_X, nsmul_eq_mul, mul_one, Nat.cast_lt,
            Polynomial.coeff_X_pow, Nat.cast_inj]
            constructor
            · apply PartENat.get_eq_iff_eq_coe.mpr
              apply order_eq_nat.mpr
              have {x : (R ⧸ m ^ (n + 1))} (hx : x ∈ m.map (Ideal.Quotient.mk (m ^ (n + 1)))): x = 0 := by
                rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ (n + 1))) Ideal.Quotient.mk_surjective hx with ⟨r, hr, eq⟩
                rw [← eq, Ideal.Quotient.eq_zero_iff_mem, neq0, zero_add, pow_one]
                exact hr
              constructor
              · by_contra h
                absurd Nat.find_spec ntriv
                simp only [h, Submodule.zero_mem]
              · intro i hi
                exact this <| Decidable.not_not.mp (Nat.find_min ntriv hi)
            · constructor
              · intro a ha
                convert (Submodule.zero_mem (Ideal.map (Ideal.Quotient.mk (m ^ (n + 1))) m))
                simp [Nat.ne_of_lt ha]
              · rw [PowerSeries.Unit_of_divided_by_X_pow_order_nonzero (ne0 ntriv)]
                convert (PowerSeries.self_eq_X_pow_order_mul_divided_by_X_pow_order (ne0 ntriv)).symm
                simp only [Polynomial.coe_pow, Polynomial.coe_X]
        · rintro g' ⟨h, mon, deg, hg, eq⟩

          --Uniqueness
          sorry
      · let f' : PowerSeries (R ⧸ m ^ n) := PowerSeries.map (hom m n) f
        rcases ih (Nat.zero_lt_of_ne_zero neq0) f' (map_ntriv ntriv) with ⟨g', ⟨h', mon, hg', eq⟩, uniq⟩
        --take arbitrary lift of `f' g' h'`, get `f'' - g'' * h''` coeffs in `m ^ n`,
        --split `h''.inv * (f'' - g'' * h'')` at power `Nat.find ntriv`
        --add the lower part onto `g''` and add the higher part multiplicated by `h''` onto `h''`
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
