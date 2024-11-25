import Mathlib

set_option maxHeartbeats 500000
set_option linter.unusedTactic false

variable {R : Type*} [CommRing R] {m : Ideal R} (hmax : m.IsMaximal)
open Polynomial PowerSeries

theorem PowerSeries.map_surjective {R : Type u} {S : Type v} [Semiring R] [Semiring S] (f : R →+* S) (hf : Function.Surjective ⇑f) :
    Function.Surjective (PowerSeries.map f) := by
  intro g
  use PowerSeries.mk fun k ↦ Function.surjInv hf (PowerSeries.coeff _ k g)
  ext k
  simp only [Function.surjInv, coeff_map, coeff_mk]
  exact Classical.choose_spec (hf ((coeff S k) g))

noncomputable def PowerSeries.lowerpart {R : Type u} [Semiring R] (f : R⟦X⟧) (n : ℕ) : R[X] where
  toFinsupp := {
    support :=
      have : Fintype {i | i < n ∧ PowerSeries.coeff R i f ≠ 0} :=
        Fintype.ofInjective (fun i ↦ (⟨i.1, i.2.1⟩ : Fin n)) (fun i j  hij ↦ Subtype.val_inj.mp <| Fin.mk.inj_iff.mp hij)
      Set.toFinset {i | i < n ∧ PowerSeries.coeff R i f ≠ 0}
    toFun := fun i ↦ if i < n then PowerSeries.coeff R i f else 0
    mem_support_toFun := by simp }

lemma lowerpart_deg_lt {R : Type u} [Semiring R] (f : R⟦X⟧) (n : ℕ) : (PowerSeries.lowerpart f n).degree < n := by
  apply (degree_lt_iff_coeff_zero (f.lowerpart n) n).mpr
  intro m hm
  simp only [lowerpart, ne_eq, Set.coe_setOf, Set.mem_setOf_eq, coeff_ofFinsupp, Finsupp.coe_mk]
  exact if_neg (Nat.not_lt.mpr hm)

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

lemma hom_surjective (n : ℕ) : Function.Surjective (hom m n) := by
  apply Ideal.Quotient.lift_surjective_of_surjective
  exact Ideal.Quotient.mk_surjective

lemma hom_ker (n : ℕ) : RingHom.ker (hom m n) = (m ^ n).map (Ideal.Quotient.mk (m ^ (n + 1))) := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases Ideal.Quotient.mk_surjective x with ⟨r, hr⟩
    rw [← hr] at h ⊢
    simp only [hom, RingHom.mem_ker, Ideal.Quotient.lift_mk, Ideal.Quotient.eq_zero_iff_mem] at h
    exact Ideal.mem_map_of_mem _ h
  · rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ (n + 1))) Ideal.Quotient.mk_surjective h with ⟨r, hr, eq⟩
    simpa only [hom, ← eq, RingHom.mem_ker, Ideal.Quotient.lift_mk, Ideal.Quotient.eq_zero_iff_mem] using hr

lemma hom_preimage {n : ℕ} (npos : n > 0) : m.map (Ideal.Quotient.mk (m ^ (n + 1))) = (hom m n)⁻¹' (m.map (Ideal.Quotient.mk (m ^ n))) := by
  ext x
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ (n + 1))) Ideal.Quotient.mk_surjective h with ⟨r, hr, eq⟩
    simp [hom, ← eq, Submodule.mem_sup_left hr]
  · rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ n)) Ideal.Quotient.mk_surjective h with ⟨r, hr, eq⟩
    rw [← hom_commute] at eq
    have : x - ((Ideal.Quotient.mk (m ^ (n + 1))) r) ∈ (m ^ n).map (Ideal.Quotient.mk (m ^ (n + 1))) := by simp [← hom_ker, ← eq]
    rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ (n + 1))) Ideal.Quotient.mk_surjective this with ⟨s, hs, eq'⟩
    rw [← add_sub_cancel ((Ideal.Quotient.mk (m ^ (n + 1))) r) x, ← eq', ← map_add]
    apply Ideal.mem_map_of_mem
    apply Submodule.add_mem _ hr
    rw [← Nat.sub_add_cancel npos, pow_add, pow_one] at hs
    exact Ideal.mul_le_left (I := m ^ (n - 1)) hs

variable {m} in
lemma IsUnit_of_IsUnit_image {n : ℕ} (npos : n > 0) {a : R ⧸ m ^ (n + 1)} (h : IsUnit ((hom m n) a)) : IsUnit a := by
  rcases isUnit_iff_exists.mp h with ⟨b, hb, _⟩
  rcases hom_surjective m n b with ⟨b', hb'⟩
  rw [← hb', ← map_one (hom m n), ← map_mul] at hb
  apply (RingHom.sub_mem_ker_iff (hom m n)).mpr at hb
  rw [hom_ker m n] at hb
  rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ (n + 1))) Ideal.Quotient.mk_surjective hb with ⟨c, hc, eq⟩
  have : a * (b' * (1 - ((Ideal.Quotient.mk (m ^ (n + 1))) c))) = 1 := by
    calc
      _ = (a * b' - 1) * (1 - ((Ideal.Quotient.mk (m ^ (n + 1))) c)) + (1 - ((Ideal.Quotient.mk (m ^ (n + 1))) c)) := by ring
      _ = 1 := by
        rw [← eq, mul_sub, mul_one, sub_add_sub_cancel', sub_eq_self, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_add]
        apply Ideal.mul_mem_mul hc (Ideal.mul_le_left (I := m ^ (n - 1)) _)
        simpa only [← pow_add, Nat.sub_add_cancel npos] using hc
  exact isUnit_of_mul_eq_one _ _ this

end

lemma ne0 {f : PowerSeries (R ⧸ m ^ n)} (ntriv : ∃ (k : ℕ), (PowerSeries.coeff _ k) f ∉ m.map (Ideal.Quotient.mk (m ^ n))) : f ≠ 0 := by
  rcases ntriv with ⟨k, hk⟩
  have : (PowerSeries.coeff _ k) f ≠ 0 := by
    by_contra h
    exact (h ▸ hk) (Submodule.zero_mem (Ideal.map (Ideal.Quotient.mk (m ^ n)) m))
  exact (ne_of_apply_ne ⇑(PowerSeries.coeff _ k) fun a => this a.symm).symm

open Classical

/-
If don't want to open Classical then try def and lemma below.

noncomputable def ntriv_deg {f : PowerSeries (R ⧸ m ^ n)} (ntriv : ∃ (k : ℕ), (PowerSeries.coeff _ k) f ∉ m.map (Ideal.Quotient.mk (m ^ n))) : ℕ :=
  sInf {k | (PowerSeries.coeff _ k) f ∉ m.map (Ideal.Quotient.mk (m ^ n))}

lemma ntriv_deg_spec {f : PowerSeries (R ⧸ m ^ n)} (ntriv : ∃ (k : ℕ), (PowerSeries.coeff _ k) f ∉ m.map (Ideal.Quotient.mk (m ^ n))) :
    (PowerSeries.coeff _ (ntriv_deg ntriv)) f ∉ m.map (Ideal.Quotient.mk (m ^ n)) ∧ ∀ i < (ntriv_deg ntriv), (PowerSeries.coeff _ i) f ∈ m.map (Ideal.Quotient.mk (m ^ n)) :=
  sorry
-/

lemma map_ntriv {n : ℕ} (npos : n > 0) {f : PowerSeries (R ⧸ m ^ (n + 1))} (ntriv : ∃ (k : ℕ), (PowerSeries.coeff _ k) f ∉ m.map (Ideal.Quotient.mk (m ^ (n + 1)))) :
    ∃ k, (PowerSeries.coeff (R ⧸ m ^ n) k) (PowerSeries.map (hom m n) f) ∉ Ideal.map (Ideal.Quotient.mk (m ^ n)) m := by
  rcases ntriv with ⟨k, hk⟩
  use k
  by_contra h
  absurd hk
  show _ ∈ (_ : Set _)
  rw [hom_preimage m npos]
  exact h

lemma hh (n : ℕ) (npos : n > 0) [hmax : m.IsMaximal] (f : PowerSeries (R ⧸ m ^ n))
    (ntriv : ∃ (k : ℕ), (PowerSeries.coeff _ k) f ∉ m.map (Ideal.Quotient.mk (m ^ n))) :
    ∃! (g : Polynomial (R ⧸ m ^ n)), ∃ (h : (R ⧸ m ^ n)⟦X⟧ˣ), Monic g ∧ g.degree = Nat.find ntriv ∧
    (∀ i : ℕ, i < degree g → coeff g i ∈ m.map (Ideal.Quotient.mk (m ^ n))) ∧ f = g * h := by
    induction' n with n ih
    · absurd npos
      exact Nat.not_lt_zero 0
    · by_cases neq0 : n = 0
      · have {x : (R ⧸ m ^ (n + 1))} (hx : x ∈ m.map (Ideal.Quotient.mk (m ^ (n + 1)))): x = 0 := by
          rcases Ideal.mem_image_of_mem_map_of_surjective (Ideal.Quotient.mk (m ^ (n + 1))) Ideal.Quotient.mk_surjective hx with ⟨r, hr, eq⟩
          rw [← eq, Ideal.Quotient.eq_zero_iff_mem, neq0, zero_add, pow_one]
          exact hr
        have eqfind : f.order.get (order_finite_iff_ne_zero.mpr (ne0 ntriv)) = Nat.find ntriv := by
          apply PartENat.get_eq_iff_eq_coe.mpr (order_eq_nat.mpr _)
          constructor
          · by_contra h
            absurd Nat.find_spec ntriv
            simp only [h, Submodule.zero_mem]
          · exact fun i hi ↦ this <| Decidable.not_not.mp (Nat.find_min ntriv hi)
        use Polynomial.X ^ Nat.find ntriv
        constructor
        · let max' : (m ^ (n + 1)).IsMaximal := by simpa only [neq0, zero_add, pow_one] using hmax
          let hField : Field (R ⧸ m ^ (n + 1)) := Ideal.Quotient.field (m ^ (n + 1))
          use PowerSeries.Unit_of_divided_by_X_pow_order f
          constructor
          · apply monic_X_pow
          · simp only [degree_pow, degree_X, nsmul_eq_mul, mul_one, Nat.cast_lt,
            Polynomial.coeff_X_pow, Nat.cast_inj, eqfind, true_and]
            constructor
            · intro a ha
              convert (Submodule.zero_mem (Ideal.map (Ideal.Quotient.mk (m ^ (n + 1))) m))
              simp [Nat.ne_of_lt ha]
            · rw [PowerSeries.Unit_of_divided_by_X_pow_order_nonzero (ne0 ntriv)]
              convert (PowerSeries.self_eq_X_pow_order_mul_divided_by_X_pow_order (ne0 ntriv)).symm
              simp only [Polynomial.coe_pow, Polynomial.coe_X, eqfind]
        · rintro g' ⟨h, mon, deg, hg', eq⟩
          apply Polynomial.ext
          intro i
          simp only [Polynomial.coeff_X_pow]
          by_cases H' : i = Nat.find ntriv
          · rw [if_pos H', H', ← (natDegree_eq_of_degree_eq_some deg), Polynomial.Monic.coeff_natDegree mon]
          · rcases Nat.lt_or_gt_of_ne H' with gt|lt
            · rw [if_neg (Nat.ne_of_lt gt)]
              exact this ((hg' i) (deg ▸ Nat.cast_lt.mpr gt))
            · rw [if_neg (Nat.ne_of_gt lt)]
              apply Polynomial.coeff_eq_zero_of_degree_lt
              exact deg ▸ (Nat.cast_lt.mpr lt)
      · rcases ih (Nat.zero_lt_of_ne_zero neq0) (PowerSeries.map (hom m n) f) (map_ntriv (Nat.zero_lt_of_ne_zero neq0) ntriv) with ⟨g, ⟨h, mon, deg, hg, eq⟩, uniq⟩
        --take arbitrary lift of `f g h`, get `f' - g' * h'` coeffs in `m ^ n`,
        --need lift monic!!!
        rcases PowerSeries.map_surjective (hom m n) (hom_surjective m n) h.val with ⟨h', hh'⟩
        have : IsUnit h' := by
          apply PowerSeries.isUnit_iff_constantCoeff.mpr
          have := PowerSeries.isUnit_iff_constantCoeff.mp (Units.isUnit h)
          rw [← hh', ← PowerSeries.coeff_zero_eq_constantCoeff_apply] at this
          simp only [PowerSeries.coeff_map, coeff_zero_eq_constantCoeff] at this
          exact IsUnit_of_IsUnit_image (Nat.zero_lt_of_ne_zero neq0) this
        let h'' : (R ⧸ m ^ (n + 1))⟦X⟧ˣ := IsUnit.unit this
        have val : h''.1 = h' := rfl

        /-
        have : (Polynomial.map (hom m n) g') = (PowerSeries.map (hom m n) g') := by
          ext
          simp
        rw [← hg', ← hh', this, ← map_mul, ← val] at eq
        have : (PowerSeries.map (hom m n)) (f - g' * h'') = 0 := by rw [map_sub, sub_eq_zero_of_eq eq]
        --split `h'.inv * (f' - g' * h')` at power `Nat.find ntriv`
        --add the lower part onto `g'` and add the higher part multiplicated by `h'` onto `h'`
        set c : (R ⧸ m ^ (n + 1))⟦X⟧ := h''.inv * (f - g' * h'')
        have map0 : (PowerSeries.map (hom m n)) c = 0 := by rw [map_mul, this, mul_zero]
        let α := PowerSeries.lowerpart c (Nat.find ntriv)
        let γ := (PowerSeries.mk fun i ↦ PowerSeries.coeff (R ⧸ m ^ (n + 1)) (i + (Nat.find ntriv)) c)
        let β := (h'' * γ)
        have hu1 : IsUnit (1 + γ) := by
          apply PowerSeries.isUnit_iff_constantCoeff.mpr
          apply IsUnit_of_IsUnit_image (Nat.zero_lt_of_ne_zero neq0)
          convert isUnit_one
          simp [γ, ← PowerSeries.coeff_map, map0]
        have hu2 : IsUnit (h''.1 * (1 + γ)) := IsUnit.mul (Units.isUnit h'') hu1
        have heq : (α : (R ⧸ m ^ (n + 1))⟦X⟧) + ((PowerSeries.X) ^ (Nat.find ntriv)) * γ = c := by
          ext k
          simp only [lowerpart, ne_eq, Set.coe_setOf, Set.mem_setOf_eq, map_add, Polynomial.coeff_coe, coeff_ofFinsupp, Finsupp.coe_mk, α, PowerSeries.coeff_X_pow_mul', coeff_mk, γ]
          by_cases lt : k < Nat.find ntriv
          · rw [if_pos lt, if_neg (Nat.not_le_of_lt lt), add_zero]
          · rw [if_neg lt, if_pos (Nat.le_of_not_lt lt), zero_add, Nat.sub_add_cancel (Nat.le_of_not_lt lt)]
        have deg'' : g'.degree = Nat.find ntriv := by
          --Polynomial.degree_map_eq_of_leadingCoeff_ne_zero
          sorry
        have deg' : (g' + α).degree = Nat.find ntriv := by
          rw [← deg'']
          apply Polynomial.degree_add_eq_left_of_degree_lt
          rw [deg'']
          sorry
        have : ∀ i : ℕ, i < (g' + α).degree → (g' + α).coeff i ∈ m.map (Ideal.Quotient.mk (m ^ (n + 1))) := by
          sorry
        have : (((g' + α)  : (R ⧸ m ^ (n + 1))⟦X⟧) - ((PowerSeries.X) ^ (Nat.find ntriv))) * γ = 0 := by
          ext
          simp only [PowerSeries.coeff_mul, map_zero]
          apply Finset.sum_eq_zero fun x hx => ?_
          have : (PowerSeries.coeff (R ⧸ m ^ (n + 1)) x.1) (((g' + α)  : (R ⧸ m ^ (n + 1))⟦X⟧) - PowerSeries.X ^ Nat.find ntriv) ∈ m.map (Ideal.Quotient.mk (m ^ (n + 1))) := by
            simp only [map_sub, map_add, Polynomial.coeff_coe]
            have : (hom m n) (α.coeff x.1) = 0 := by
              simp only [lowerpart, Set.coe_setOf, Set.mem_setOf_eq, coeff_ofFinsupp, Finsupp.coe_mk, α]
              by_cases lt : x.1 < Nat.find ntriv
              · rw [if_pos lt, ← PowerSeries.coeff_map, map0]
                rfl
              · rw [if_neg lt, map_zero]
            have : (α.coeff x.1) ∈ (Ideal.map (Ideal.Quotient.mk (m ^ (n + 1))) m : Set _) := by
              rw [hom_preimage m (Nat.zero_lt_of_ne_zero neq0)]
              simp [this]
            have : (g'.coeff x.1 - (PowerSeries.coeff (R ⧸ m ^ (n + 1)) x.1) (PowerSeries.X ^ Nat.find ntriv)) ∈
              Ideal.map (Ideal.Quotient.mk (m ^ (n + 1))) m := by

              sorry
            rw [add_comm (g'.coeff x.1) (α.coeff x.1), add_sub_assoc]
            --hom_preimage m (Nat.zero_lt_of_ne_zero neq0)

            sorry
          sorry
        have : (g' + α) * (h''.1 * (1 + γ)) = f := by
          calc
           _ = (g' : (R ⧸ m ^ (n + 1))⟦X⟧) * h''.1 + h''.1 * ((α : (R ⧸ m ^ (n + 1))⟦X⟧) + ((PowerSeries.X) ^ (Nat.find ntriv)) * γ) + (((g' + α)  : (R ⧸ m ^ (n + 1))⟦X⟧) - ((PowerSeries.X) ^ (Nat.find ntriv))) * γ * h''.1 := by ring
           _ = f := by simp [this, heq, c]
        -/
        sorry

section

variable (F : Type*) [Field F] (ι : outParam Type*) [LinearOrderedCommGroupWithZero ι] [vR : Valued F ι]
open Valued

theorem Wierstrass_preperation (f : PowerSeries 𝒪[F]) (ne : f ≠ 0)
    (π : 𝒪[F] ) (hyp : Ideal.span {π} = 𝓂[F] ) : ∃ (m : ℕ),
    ∃! (g : Polynomial 𝒪[F] ), ∃ (h : (PowerSeries 𝒪[F])ˣ),
    Monic g ∧ (∀ i : ℕ, i < degree g → (coeff g i) ∈ 𝓂[F]) ∧
    f = (π ^ m) • g • h := sorry

end
